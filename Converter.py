#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MSBT Converter for The Legend of Zelda: Tears of the Kingdom
Convert MSBT files to AEON file format and back, with tag processing.
"""

import os
import struct
import re
import yaml
import argparse
import traceback

MSBT_MAGIC = b'MsgStdBn'
BOM_LE = b'\xFF\xFE'
BOM_BE = b'\xFE\xFF'
LBL1_MAGIC = b'LBL1'
ATR1_MAGIC = b'ATR1'
ATO1_MAGIC = b'ATO1'
TSY1_MAGIC = b'TSY1'
TXT2_MAGIC = b'TXT2'
TXTW_MAGIC = b'TXTW'
NLI1_MAGIC = b'NLI1'

DEBUG = False


def log(msg: str, level: str = "INFO") -> None:
    if DEBUG or level != "DEBUG":
        print(f"[{level}] {msg}")


class Validator:
    def __init__(self, filepath: str = ""):
        self.filepath = filepath
        self.errors:   list = []
        self.warnings: list = []

    def error(self, msg: str):
        self.errors.append(msg)

    def warn(self, msg: str):
        self.warnings.append(msg)

    def ok(self) -> bool:
        return len(self.errors) == 0

    def has_issues(self) -> bool:
        return bool(self.errors or self.warnings)

    def print_report(self):
        if self.has_issues():
            print(f"\n[VALIDATION] {self.filepath}")
            for e in self.errors:
                print(f"  [ERROR]   {e}")
            for w in self.warnings:
                print(f"  [WARNING] {w}")


def calc_hash(label: str, n: int) -> int:
    h = 0
    for c in label:
        h = h * 0x492 + ord(c)
    return (h & 0xFFFFFFFF) % n


# ---------------------------------------------------------------------------
# Byte-level hex helpers
#
# UTF-16-LE stream: bytes [lo, hi] → chr(lo | hi<<8)
# We display/store arg bytes in their on-disk (LE) order:
#   chr(0xCD01) → raw bytes [0x01, 0xCD] → hex "01CD"
#
# _chars_to_hex : str of UTF-16 chars → LE-byte hex string (NO "0x" prefix)
# _hex_to_chars : LE-byte hex string  → str of UTF-16 chars
# ---------------------------------------------------------------------------

def _chars_to_hex(chars: str, big_endian: bool = False) -> str:
    out = []
    for c in chars:
        v = ord(c)
        if big_endian:
            out.append(f"{(v >> 8) & 0xFF:02X}{v & 0xFF:02X}")
        else:
            out.append(f"{v & 0xFF:02X}{(v >> 8) & 0xFF:02X}")
    return "".join(out)


def _hex_to_chars(hex_str: str, big_endian: bool = False) -> str:
    # Use slice [2:], not lstrip — lstrip strips all leading '0'/'x' chars.
    hs = hex_str[2:] if hex_str.startswith(("0x", "0X")) else hex_str
    if not hs:
        return ""
    if len(hs) % 2:
        hs = "0" + hs
    bs = bytes.fromhex(hs)
    if len(bs) % 2:
        bs += b'\x00'
    if big_endian:
        return "".join(chr((bs[k] << 8) | bs[k + 1]) for k in range(0, len(bs), 2))
    return "".join(chr(bs[k] | (bs[k + 1] << 8)) for k in range(0, len(bs), 2))



def _escape_nulls(s: str) -> str:
    """Replace runs of null chars with {{0x000000...}} hex tags."""
    result = []
    i = 0
    while i < len(s):
        if s[i] == chr(0):
            j = i
            while j < len(s) and s[j] == chr(0):
                j += 1
            result.append('{{0x' + '00' * (j - i) + '}}')
            i = j
        else:
            result.append(s[i])
            i += 1
    return ''.join(result)


def _unescape_nulls(s: str) -> str:
    """Replace {{0x00...}} hex tags back to null chars."""
    def repl(m):
        hex_str = m.group(1)
        return chr(0) * (len(hex_str) // 2)
    return re.sub(r'\{\{0x((?:00)+)\}\}', repl, s)

class TagDefinitions:
    def __init__(self):
        self.by_group_type: dict = {}
        self.by_name: dict = {}
        self.loaded: bool = False

    def load_from_file(self, filepath: str) -> bool:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                data = yaml.safe_load(f)
            tags = data.get('msbt', {}).get('tags', [])
            for td in tags:
                g, t, n = td.get('group'), td.get('type'), td.get('name')
                if g is not None and t is not None and n:
                    self.by_group_type[(g, t)] = td
                    self.by_name[n] = td
            # log(f"Loaded {len(tags)} tag definitions")
            self.loaded = True
            return True
        except Exception as e:
            log(f"Error loading GCF: {e}", "ERROR")
            return False

    def get(self, group: int, type_id: int):
        return self.by_group_type.get((group, type_id))

    def get_by_name(self, name: str):
        return self.by_name.get(name)


class MSBTFile:
    def __init__(self):
        self.big_endian    = False
        self.version       = 3
        self.encoding      = 'utf-16'
        self.file_size     = 0
        self.has_lbl1      = False
        self.has_atr1      = False
        self.has_ato1      = False
        self.has_tsy1      = False
        self.has_nli1      = False
        self.has_txtw      = False
        self.label_groups  = 0
        self.labels: dict  = {}
        self.label_id_map: dict = {}
        self.texts: dict   = {}
        self.attributes: dict = {}
        self.attribute_has_text: bool = False
        self.original_order: list = []
        self.text_order: list = []
        self.raw_sections: dict = {}
        self.tag_defs      = TagDefinitions()
        self.validator     = Validator()

    @property
    def enc_width(self) -> int:
        return {'utf-8': 1, 'utf-16': 2, 'utf-32': 4}.get(self.encoding, 2)

    def load_tag_definitions(self, fp: str) -> bool:
        return self.tag_defs.load_from_file(fp)

    # ------------------------------------------------------------------
    # MSBT → memory
    # ------------------------------------------------------------------
    def load_from_file(self, filepath: str) -> None:
        with open(filepath, 'rb') as f:
            raw = f.read()
        if raw[:8] != MSBT_MAGIC:
            raise ValueError("Not an MSBT file")
        bom = raw[8:10]
        if   bom == BOM_LE: self.big_endian = False; endian = '<'
        elif bom == BOM_BE: self.big_endian = True;  endian = '>'
        else: raise ValueError(f"Bad BOM: {bom.hex()}")

        self.encoding  = {0: 'utf-8', 1: 'utf-16', 2: 'utf-32'}.get(raw[0x0C], 'utf-16')
        self.version   = raw[0x0D]
        sec_count      = struct.unpack_from(f"{endian}H", raw, 0x0E)[0]
        self.file_size = struct.unpack_from(f"{endian}I", raw, 0x12)[0]

        pos = 0x20
        for _ in range(sec_count):
            if pos + 8 > len(raw): break
            magic    = raw[pos:pos+4]
            sec_size = struct.unpack_from(f"{endian}I", raw, pos+4)[0]
            sec_data = raw[pos+16:pos+16+sec_size]
            self.raw_sections[magic] = sec_data

            if   magic == LBL1_MAGIC: self.has_lbl1 = True;  self._parse_lbl1(sec_data, endian)
            elif magic == TXT2_MAGIC: self.has_txtw = False;  self._parse_txt2(sec_data, endian)
            elif magic == TXTW_MAGIC: self.has_txtw = True;   self._parse_txt2(sec_data, endian)
            elif magic == ATR1_MAGIC: self.has_atr1 = True;   self._parse_atr1(sec_data, endian)
            elif magic == ATO1_MAGIC: self.has_ato1 = True
            elif magic == TSY1_MAGIC: self.has_tsy1 = True
            elif magic == NLI1_MAGIC: self.has_nli1 = True

            pos += 16 + ((sec_size + 15) & ~15)

        for lbl, mid in self.labels.items():
            if mid not in self.label_id_map:
                self.label_id_map[mid] = lbl
                self.original_order.append((lbl, mid))

        self.validator.filepath = filepath
        self._validate_msbt()

    def _validate_msbt(self) -> None:
        v = self.validator
        txt_count = len(self.texts)

        # LBL1 → TXT2 index checks
        for lbl, mid in self.labels.items():
            if mid >= txt_count:
                v.error(f"Label '{lbl}' points to slot {mid}, but TXT2 only has {txt_count} entries")

        # Count mismatch
        lbl_count = len(self.labels)
        if self.has_lbl1 and lbl_count != txt_count:
            v.warn(f"LBL1 has {lbl_count} labels but TXT2 has {txt_count} entries")

        # Broken tags in texts
        for mid, text in self.texts.items():
            i = 0
            while i < len(text):
                if ord(text[i]) in (0x000E, 0x000F):
                    if i + 3 > len(text):
                        lbl_name = self.label_id_map.get(mid, f"slot {mid}")
                        v.warn(f"Broken tag at end of text '{lbl_name}' (0x000E without group/type)")
                        break
                    closing_tag = ord(text[i]) == 0x000F
                    i += 3  # skip tag marker, group, type
                    if not closing_tag and i < len(text):
                        byte_count = ord(text[i]); i += 1
                        char_count = byte_count // self.enc_width
                        if i + char_count > len(text):
                            lbl_name = self.label_id_map.get(mid, f"slot {mid}")
                            v.warn(f"Broken tag args in text '{lbl_name}' (declared {byte_count} arg bytes, but string ends early)")
                        i += char_count
                else:
                    i += 1

    def _parse_lbl1(self, data: bytes, endian: str) -> None:
        if len(data) < 4: return
        n = struct.unpack_from(f"{endian}I", data, 0)[0]
        self.label_groups = n
        groups = [(struct.unpack_from(f"{endian}I", data, 4+i*8)[0],
                   struct.unpack_from(f"{endian}I", data, 8+i*8)[0]) for i in range(n)]
        d: dict = {}
        for cnt, loff in groups:
            p = loff
            for _ in range(cnt):
                if p >= len(data): break
                ll = data[p]; p += 1
                name = data[p:p+ll].decode('utf-8'); p += ll
                idx  = struct.unpack_from(f"{endian}I", data, p)[0]; p += 4
                d[name] = idx
        self.labels = d

    def _parse_txt2(self, data: bytes, endian: str) -> None:
        if len(data) < 4: return
        num  = struct.unpack_from(f"{endian}I", data, 0)[0]
        offs = [struct.unpack_from(f"{endian}I", data, 4+i*4)[0] for i in range(num)]
        if self.encoding == 'utf-16':
            enc = 'utf-16-le' if endian == '<' else 'utf-16-be'
        elif self.encoding == 'utf-32':
            enc = 'utf-32-le' if endian == '<' else 'utf-32-be'
        else:
            enc = 'utf-8'
        txts: dict = {}
        for i in range(num):
            s, e = offs[i], (offs[i+1] if i+1 < num else len(data))
            raw = data[s:e]
            try:
                t = raw.decode(enc)
                if t and t[-1] == '\0': t = t[:-1]
                txts[i] = t
            except UnicodeDecodeError:
                txts[i] = raw.decode('latin1')
        self.texts = txts
        self.text_order = list(range(num))

    def _parse_atr1(self, data: bytes, endian: str) -> None:
        if len(data) < 8: return
        cnt  = struct.unpack_from(f"{endian}I", data, 0)[0]
        size = struct.unpack_from(f"{endian}I", data, 4)[0]
        enc  = 'utf-16-le' if not self.big_endian else 'utf-16-be'
        attrs: dict = {}
        sec_size = len(data)
        attr_length = cnt * 4 + 8
        enc_width = self.enc_width
        has_text = size == 4 and sec_size >= attr_length + cnt * enc_width
        if has_text:
            for i in range(cnt):
                off = struct.unpack_from(f"{endian}I", data, 8+i*4)[0]
                if off == 0 or off > sec_size or off < attr_length:
                    attrs[i] = ""; continue
                end = off
                while end+1 < sec_size and not (data[end] == 0 and data[end+1] == 0):
                    end += 2
                try:    attrs[i] = data[off:end].decode(enc).rstrip('\0')
                except: attrs[i] = "[DECODE ERROR]"
        else:
            for i in range(cnt):
                if size == 0:
                    attrs[i] = ""
                else:
                    s = 8+i*size; e = s+size
                    if e <= sec_size: attrs[i] = data[s:e].hex()
        self.attribute_has_text = has_text
        self.attributes = attrs

    # ------------------------------------------------------------------
    # Tag reading helpers
    # ------------------------------------------------------------------
    def _read_arg_data(self, text: str, i: int):
        """Read arg_size char (always present, 0 for no-arg tags) and return (arg_data, new_i).
        The char value is the BYTE-COUNT of the following argument data."""
        if i >= len(text):
            return "", i
        byte_count = ord(text[i]); i += 1
        char_count = byte_count // self.enc_width
        arg = text[i:i + char_count]
        return arg, i + char_count

    def _decode_args(self, arg_data: str, arg_defs: list) -> dict:
        """Decode arg_data working at raw-byte level.

        Unpack UTF-16 chars to bytes (LE), then read each arg by its byte size:
          str    : 2-byte LE length prefix + char data (2 bytes/char)
          u16/s16: 2 bytes
          u8     : 1 byte  (multiple args pack into same UTF-16 char)
          bool   : 1 byte

        otherArg: emitted only when remaining byte count is EVEN (complete chars).
        Odd remainder = alignment padding (e.g. 0xCD after a lone u8) → dropped.
        """
        if not arg_data:
            return {}
        if not arg_defs:
            # No defined args but data exists — treat all as otherArg (raw hex)
            raw = bytearray()
            w = self.enc_width
            for c in arg_data:
                v = ord(c)
                shifts = range((w-1)*8, -1, -8) if self.big_endian else range(0, w * 8, 8)
                for shift in shifts:
                    raw.append((v >> shift) & 0xFF)
            return {'otherArg': "0x" + raw.hex().upper()}

        # Unpack chars → raw bytes based on encoding width and endianness
        raw = bytearray()
        w = self.enc_width
        for c in arg_data:
            v = ord(c)
            shifts = range((w-1)*8, -1, -8) if self.big_endian else range(0, w * 8, 8)
            for shift in shifts:
                raw.append((v >> shift) & 0xFF)

        result: dict = {}
        pos = 0  # byte position

        for ad in arg_defs:
            if pos >= len(raw): break
            name  = ad.get('name', 'arg')
            dtype = ad.get('dataType', '')

            if dtype == 'str':
                if pos + 2 > len(raw): break
                if self.big_endian:
                    byte_len = (raw[pos] << 8) | raw[pos+1]
                else:
                    byte_len = raw[pos] | (raw[pos+1] << 8)
                pos += 2
                char_len = byte_len // 2
                s = ""
                for _ in range(char_len):
                    if pos + 2 > len(raw): break
                    if self.big_endian:
                        s += chr((raw[pos] << 8) | raw[pos+1])
                    else:
                        s += chr(raw[pos] | (raw[pos+1] << 8))
                    pos += 2
                result[name] = s

            elif dtype in ('u16', 's16'):
                if pos + 2 > len(raw): break
                if self.big_endian:
                    v = (raw[pos] << 8) | raw[pos+1]
                else:
                    v = raw[pos] | (raw[pos+1] << 8)
                pos += 2
                if dtype == 's16' and v & 0x8000:
                    v -= 0x10000
                result[name] = str(v)

            elif dtype == 'u8':
                arr = ad.get('arrayLength', 1)
                value_map = ad.get('valueMap', {})
                if arr > 1:
                    vals = [raw[pos+j] for j in range(min(arr, len(raw)-pos))]
                    result[name] = str(vals); pos += arr
                else:
                    if pos >= len(raw): break
                    v = raw[pos]; pos += 1
                    # Use valueMap if available (e.g. icon type: 12 → "JumpButton0")
                    result[name] = str(value_map.get(v, v))

            elif dtype == 'bool':
                if pos >= len(raw): break
                result[name] = 'true' if raw[pos] else 'false'
                pos += 1

        # Remaining bytes → otherArg only when aligned to enc_width
        remaining = raw[pos:]
        # Skip pure 0xCD padding; include any other remaining bytes as otherArg
        if len(remaining) > 0 and not all(b == 0xCD for b in remaining):
            result['otherArg'] = "0x" + remaining.hex().upper()

        return result

    # ------------------------------------------------------------------
    # binary text → readable YAML text
    # ------------------------------------------------------------------
    def _process_tags(self, text: str) -> str:
        if not self.tag_defs.loaded:
            return self._mark_tags_raw(text)

        out = []; i = 0
        while i < len(text):
            ch = ord(text[i])
            if ch != 0x000E and ch != 0x000F:
                out.append(text[i]); i += 1; continue

            closing = ch == 0x000F
            i += 1
            if i + 2 > len(text):
                out.append(text[i-1:i]); continue

            group   = ord(text[i]); i += 1
            type_id = ord(text[i]); i += 1

            if closing:
                out.append(f"{{{{{group}:{type_id}/}}}}"); continue

            arg_data, i = self._read_arg_data(text, i)

            td = self.tag_defs.get(group, type_id)
            if td:
                name  = td.get('name', f"{group}:{type_id}")
                av    = self._decode_args(arg_data, td.get('arguments', []))
                parts = [f'{k}="{v}"' for k, v in av.items()]
                tag   = "{{" + name + (" " if parts else "") + " ".join(parts) + "}}"
            else:
                if arg_data:
                    tag = f'{{{{{group}:{type_id} arg="0x{_chars_to_hex(arg_data, self.big_endian)}"}}}}'
                else:
                    tag = f"{{{{{group}:{type_id}}}}}"
            out.append(tag)

        return _escape_nulls("".join(out))

    def _mark_tags_raw(self, text: str) -> str:
        out = []; i = 0
        while i < len(text):
            ch = ord(text[i])
            if ch != 0x000E and ch != 0x000F:
                out.append(text[i]); i += 1; continue

            closing = ch == 0x000F
            i += 1
            if i + 2 > len(text):
                out.append(text[i-1:i]); continue

            group   = ord(text[i]); i += 1
            type_id = ord(text[i]); i += 1

            if closing:
                out.append(f"{{{{{group}:{type_id}/}}}}"); continue

            arg_data, i = self._read_arg_data(text, i)

            if arg_data:
                out.append(f'{{{{{group}:{type_id} arg="0x{_chars_to_hex(arg_data, self.big_endian)}"}}}}'  )
            else:
                out.append(f"{{{{{group}:{type_id}}}}}")

        return _escape_nulls("".join(out))

    # ------------------------------------------------------------------
    # readable YAML text → binary text
    # ------------------------------------------------------------------
    def _generate_tags(self, text: str) -> str:
        out = []; last = 0
        for m in re.finditer(r'\{\{([^}]+)\}\}', text):
            out.append(text[last:m.start()])
            b = self._tag_to_binary(m.group(1).strip())
            out.append(b if b is not None else m.group(0))
            last = m.end()
        out.append(text[last:])
        return _unescape_nulls("".join(out))

    @staticmethod
    def _parse_kv(s: str) -> dict:
        result: dict = {}
        for m in re.finditer(r'(\w+)=(?:"([^"]*)"|\'([^\']*)\'|(\S+))', s):
            v = m.group(2) if m.group(2) is not None else \
                m.group(3) if m.group(3) is not None else m.group(4)
            result[m.group(1)] = v
        return result

    def _tag_to_binary(self, tag_content: str):
        parts    = tag_content.split(None, 1)
        tag_name = parts[0]
        kv       = self._parse_kv(parts[1]) if len(parts) > 1 else {}

        td = None
        closing = tag_name.endswith('/')
        if closing: tag_name = tag_name.rstrip('/')
        if ":" in tag_name:
            try:
                g, t = tag_name.split(":", 1)
                group, type_id = int(g), int(t)
            except ValueError:
                log(f"Bad tag: {tag_content}", "WARNING"); return None
        elif self.tag_defs.loaded:
            td = self.tag_defs.get_by_name(tag_name)
            if td is None:
                log(f"Unknown tag: {tag_name}", "WARNING"); return None
            group, type_id = td['group'], td['type']
        else:
            log(f"No defs for: {tag_name}", "WARNING"); return None

        if td is not None:
            arg_data = self._encode_args(kv, td.get('arguments', []))
        else:
            raw = kv.get('arg', '')
            arg_data = _hex_to_chars(raw, self.big_endian) if raw else ""

        if closing:
            return chr(0x000F) + chr(group) + chr(type_id)
        return chr(0x000E) + chr(group) + chr(type_id) + chr(len(arg_data) * self.enc_width) + arg_data

    def _encode_args(self, kv: dict, arg_defs: list) -> str:
        """Encode argument dict to binary UTF-16 char string, working at byte level.

        Type sizes:
          str    : 2-byte LE length prefix + char data (2 bytes/char)
          u16/s16: 2 bytes
          u8     : 1 byte
          bool   : 1 byte
        If total byte count is odd, pad with 0xCD (TotK engine pattern).
        Pack bytes into UTF-16 chars at the end (LE: low byte, high byte).
        """
        raw = bytearray()
        defined: set = set()

        for ad in arg_defs:
            name  = ad.get('name', '')
            dtype = ad.get('dataType', '')
            defined.add(name)
            if name not in kv: continue
            val = kv[name]

            if dtype == 'str':
                byte_len = len(val) * 2
                if self.big_endian:
                    raw.append((byte_len >> 8) & 0xFF)
                    raw.append(byte_len & 0xFF)
                else:
                    raw.append(byte_len & 0xFF)
                    raw.append((byte_len >> 8) & 0xFF)
                for c in val:
                    v = ord(c)
                    if self.big_endian:
                        raw.append((v >> 8) & 0xFF)
                        raw.append(v & 0xFF)
                    else:
                        raw.append(v & 0xFF)
                        raw.append((v >> 8) & 0xFF)

            elif dtype in ('u16', 's16'):
                v = int(val)
                if dtype == 's16' and v < 0: v += 0x10000
                v &= 0xFFFF
                if self.big_endian:
                    raw.append((v >> 8) & 0xFF)
                    raw.append(v & 0xFF)
                else:
                    raw.append(v & 0xFF)
                    raw.append((v >> 8) & 0xFF)

            elif dtype == 'u8':
                arr = ad.get('arrayLength', 1)
                value_map = ad.get('valueMap', {})
                # Reverse valueMap: name → number (for encoding "JumpButton0" → 12)
                reverse_map = {str(v): k for k, v in value_map.items()}
                if arr > 1 and val.startswith('['):
                    try:
                        vs = eval(val)
                        raw.extend(vs[j] if j < len(vs) else 0 for j in range(arr))
                    except:
                        raw.extend(0 for _ in range(arr))
                else:
                    try:
                        # Try reverse valueMap first, then plain int
                        v = reverse_map[val] if val in reverse_map else int(val)
                        raw.append(v & 0xFF)
                    except: raw.append(0)

            elif dtype == 'bool':
                raw.append(1 if val.lower() == 'true' else 0)

        # Extra args not in GCF (e.g. otherArg) — append as raw bytes
        extra = bytearray()
        for name, val in kv.items():
            if name in defined: continue
            if val.startswith(("0x", "0X")):
                hs = val[2:]
                if len(hs) % 2: hs = "0" + hs
                try: extra.extend(bytes.fromhex(hs))
                except: pass

        # If extra data present, append directly; otherwise pad defined args to enc_width
        w = self.enc_width
        if extra:
            raw.extend(extra)
        else:
            while len(raw) % w:
                raw.append(0xCD)

        # Pack bytes into chars of enc_width bytes (pad last char with 0 if needed)
        while len(raw) % w:
            raw.append(0)
        if self.big_endian:
            return "".join(chr(sum(raw[k+j] << ((w-1-j)*8) for j in range(w))) for k in range(0, len(raw), w))
        return "".join(chr(sum(raw[k+j] << (j*8) for j in range(w))) for k in range(0, len(raw), w))

    def _validate_yaml(self, labels: dict, texts: dict, matches, id_map: dict) -> None:
        v = self.validator

        # Duplicate label names
        seen_names: dict = {}
        for i, m in enumerate(matches):
            lbl = m.group(1).strip('\n\r')
            if lbl in seen_names:
                v.error(f"Duplicate label '{lbl}' (entries #{seen_names[lbl]+1} and #{i+1})")
            else:
                seen_names[lbl] = i

        # Duplicate slot IDs (only relevant when has_lbl1=false)
        if not self.has_lbl1:
            seen_ids: dict = {}
            for i, m in enumerate(matches):
                lbl = m.group(1).strip('\n\r')
                mid = id_map[i]
                if mid in seen_ids:
                    v.error(f"ID collision: labels '{seen_ids[mid]}' and '{lbl}' both map to slot {mid}")
                else:
                    seen_ids[mid] = lbl

        # has_lbl1=false but non-Text_N labels present
        if not self.has_lbl1:
            for lbl in labels:
                if not (lbl.startswith("Text_") and lbl[5:].isdigit()):
                    v.warn(f"hasLBL1 is false but label '{lbl}' is not a Text_N name — it won't be stored in the file")

        # Empty texts
        # for i, m in enumerate(matches):
            # text = m.group(3).rstrip('\n') if m.group(3) else ""
            # if not text.strip():
                # lbl = m.group(1).strip('\n\r')
                # v.warn(f"Label '{lbl}' has empty text")

    # ------------------------------------------------------------------
    # memory → MSBT file
    # ------------------------------------------------------------------
    def save_to_file(self, filepath: str) -> None:
        endian = '>' if self.big_endian else '<'
        bom    = BOM_BE if self.big_endian else BOM_LE

        header = bytearray(32)
        header[0:8]  = MSBT_MAGIC
        header[8:10] = bom
        header[0x0C] = {'utf-8': 0, 'utf-16': 1, 'utf-32': 2}.get(self.encoding, 1)
        header[0x0D] = self.version

        sections = []
        if self.has_lbl1:
            sections.append((LBL1_MAGIC, self._build_lbl1(endian)))
        if self.has_atr1:
            d = self._build_atr1(endian)
            if d: sections.append((ATR1_MAGIC, d))
        sections.append((TXTW_MAGIC if self.has_txtw else TXT2_MAGIC, self._build_txt2(endian)))
        for mg, flag in [(ATO1_MAGIC, self.has_ato1),
                         (TSY1_MAGIC, self.has_tsy1),
                         (NLI1_MAGIC, self.has_nli1)]:
            if flag and mg in self.raw_sections:
                sections.append((mg, self.raw_sections[mg]))

        struct.pack_into(f"{endian}H", header, 0x0E, len(sections))

        txt2_magic = TXTW_MAGIC if self.has_txtw else TXT2_MAGIC
        last_tid = self.text_order[-1] if self.text_order else -1
        last_slot_all_zero = last_tid >= 0 and not self.texts.get(last_tid, '').strip(chr(0))

        with open(filepath, 'wb') as f:
            f.write(header); pos = 32
            for mg, sd in sections:
                aligned = (len(sd) + 15) & ~15
                hdr = bytearray(16); hdr[0:4] = mg
                struct.pack_into(f"{endian}I", hdr, 4, len(sd))
                f.write(hdr); pos += 16
                f.write(sd);  pos += len(sd)
                pad = aligned - len(sd)
                if pad: f.write(b'\xAB' * pad); pos += pad
            f.seek(0x12); f.write(struct.pack(f"{endian}I", pos))
        # log(f"Saved: {filepath}")

    def _build_lbl1(self, endian: str) -> bytes:
        _label_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101]
        count = len(self.labels)
        n = next((p for p in _label_primes if count / 2 < p), _label_primes[-1])

        if not self.labels:
            sec = bytearray()
            sec += struct.pack(f"{endian}I", n)
            for _ in range(n):
                sec += struct.pack(f"{endian}I", 0)
                sec += struct.pack(f"{endian}I", 4 + n * 8)
            return sec

        buckets = [[] for _ in range(n)]
        for name, mid in self.labels.items():
            buckets[calc_hash(name, n)].append((name, mid))

        sec = bytearray()
        sec += struct.pack(f"{endian}I", n)
        cur = 4 + n * 8
        offs = []
        for b in buckets:
            offs.append(cur)
            cur += sum(1 + len(nm.encode('utf-8')) + 4 for nm, _ in b)
        for i, b in enumerate(buckets):
            sec += struct.pack(f"{endian}I", len(b))
            sec += struct.pack(f"{endian}I", offs[i])
        for b in buckets:
            for nm, mid in b:
                nb = nm.encode('utf-8')
                sec += bytes([len(nb)]) + nb + struct.pack(f"{endian}I", mid)
        return sec

    def _build_atr1(self, endian: str):
        if not self.has_atr1: return None
        n = (max(self.attributes) + 1) if self.attributes else 0
        sec = bytearray()
        if self.attribute_has_text:
            # String table mode: attributeSize=4, offsets + null-terminated strings
            enc = 'utf-16-le' if not self.big_endian else 'utf-16-be'
            sec += struct.pack(f"{endian}I", n)
            sec += struct.pack(f"{endian}I", 4)
            tbl = len(sec); sec += bytearray(n * 4)
            om: dict = {}; cur = tbl + n * 4
            for i in range(n):
                if i not in self.attributes:
                    om[i] = 0; continue
                a = self.attributes[i]
                om[i] = cur
                b = (a.encode(enc) + b'\x00\x00') if a else b'\x00\x00'
                sec += b; cur += len(b)
            for i in range(n):
                struct.pack_into(f"{endian}I", sec, tbl + i*4, om[i])
        else:
            # Raw bytes mode
            attr_size = 0
            for v in self.attributes.values():
                if v: attr_size = max(attr_size, len(bytes.fromhex(v)))
            sec += struct.pack(f"{endian}I", n)
            sec += struct.pack(f"{endian}I", attr_size)
            for i in range(n):
                raw = bytes.fromhex(self.attributes[i]) if (i in self.attributes and self.attributes[i]) else b''
                sec += raw + b'\x00' * (attr_size - len(raw))
        return sec

    def _build_txt2(self, endian: str) -> bytes:
        if self.encoding == 'utf-16':
            enc = 'utf-16-le' if not self.big_endian else 'utf-16-be'
        elif self.encoding == 'utf-32':
            enc = 'utf-32-le' if not self.big_endian else 'utf-32-be'
        else:
            enc = 'utf-8'
        null = b'\x00\x00' if self.encoding == 'utf-16' else b'\x00'
        n    = max(self.texts) + 1 if self.texts else 0
        if n == 0: return bytearray(4)

        hdr_size = 4 + 4 * n
        sec = bytearray(hdr_size)
        struct.pack_into(f"{endian}I", sec, 0, n)

        order = self.text_order if self.text_order else list(range(n))
        body  = bytearray()
        for pos in range(n):
            struct.pack_into(f"{endian}I", sec, 4 + pos*4, hdr_size + len(body))
            tid = order[pos] if pos < len(order) else -1
            if tid in self.texts:
                # Always append null explicitly — do NOT use endswith() check.
                # Tags like delay15 end with chr(0) (arg_size=0) which encodes
                # to 00 00 in UTF-16-LE and would falsely pass endswith(null).
                body += self._generate_tags(self.texts[tid]).encode(enc) + null
            else:
                body += null
        return sec + body

    # ------------------------------------------------------------------
    # memory → YAML file
    # ------------------------------------------------------------------
    def export_to_yaml(self, filepath: str) -> None:
        lines = []
        lines.append("%%%\n")
        for k, v in [
            ('bigEndian',       str(self.big_endian).lower()),
            ('bigEndianLabels', 'false'),
            ('version',         str(self.version)),
            ('encoding',        self.encoding),
            ('hasNLI1',         str(self.has_nli1).lower()),
            ('hasLBL1',         str(self.has_lbl1).lower()),
            ('labelGroups',     str(self.label_groups)),
            ('hasATR1',         str(self.has_atr1).lower()),
            ('hasATO1',         str(self.has_ato1).lower()),
            ('hasTSY1',         str(self.has_tsy1).lower()),
            ('hasTXTW',         str(self.has_txtw).lower()),
        ]:
            lines.append(f"{k}: {v}\n")
        lines.append("%%%\n\n")

        id2lbl: dict = {}
        for lbl, mid in self.labels.items():
            id2lbl.setdefault(mid, []).append(lbl)

        entries = []
        saved: set = set()
        for mid in self.text_order:
            if mid not in self.texts: continue
            for lbl in id2lbl.get(mid, [f"Text_{mid}"]):
                entry = "---\n"
                entry += f"label: {lbl}\n"
                if self.has_atr1 and mid in self.attributes:
                    key = "attributeText" if self.attribute_has_text else "attribute"
                    entry += f"{key}: {self.attributes[mid]}\n"
                entry += "---\n"
                entry += self._process_tags(self.texts[mid])
                entries.append(entry)
            saved.add(mid)
        for mid, text in sorted(self.texts.items()):
            if mid in saved: continue
            entry = "---\n"
            entry += f"label: Text_{mid}\n"
            if self.has_atr1 and mid in self.attributes:
                key = "attributeText" if self.attribute_has_text else "attribute"
                entry += f"{key}: {self.attributes[mid]}\n"
            entry += "---\n"
            entry += self._process_tags(text)
            entries.append(entry)

        content = "".join(lines) + "\n\n".join(entries) + "\n"

        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)

        # log(f"YAML saved: {filepath}")

    # ------------------------------------------------------------------
    # YAML file → memory
    # ------------------------------------------------------------------
    @classmethod
    def from_yaml(cls, filepath: str, tag_defs_file: str = None) -> 'MSBTFile':
        msbt = cls()
        if tag_defs_file:
            msbt.load_tag_definitions(tag_defs_file)

        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()

        mm = re.search(r'%%%\n(.*?)%%%', content, re.DOTALL)
        if not mm: raise ValueError("No metadata block")

        for line in mm.group(1).strip().split('\n'):
            p = line.strip().split(None, 1)
            if len(p) < 2: continue
            k, v = p[0].rstrip(':'), p[1]
            if   k == 'bigEndian':    msbt.big_endian   = v.lower() == 'true'
            elif k == 'version':      msbt.version      = int(v)
            elif k == 'encoding':     msbt.encoding     = v.strip("'\"")
            elif k == 'hasNLI1':      msbt.has_nli1     = v.lower() == 'true'
            elif k == 'hasLBL1':      msbt.has_lbl1     = v.lower() == 'true'
            elif k == 'labelGroups':  msbt.label_groups = int(v)
            elif k == 'hasATR1':      msbt.has_atr1     = v.lower() == 'true'
            elif k == 'hasATO1':      msbt.has_ato1     = v.lower() == 'true'
            elif k == 'hasTSY1':      msbt.has_tsy1     = v.lower() == 'true'
            elif k == 'hasTXTW':      msbt.has_txtw     = v.lower() == 'true'

        entry_re = re.compile(
            r'---\nlabel: (.*?)(?:\n(?:attributeText|attribute): (.*?))?\n---\n(.*?)(?=\n---\n|\Z)',
            re.DOTALL)
        matches = list(entry_re.finditer(content))

        labels: dict = {}; texts: dict = {}; attrs: dict = {}
        order: list  = []; id_map: dict = {}; next_id = 0

        for i, m in enumerate(matches):
            lbl = m.group(1).strip('\n\r')
            if msbt.has_lbl1:
                mid = next_id; next_id += 1
            else:
                if lbl.startswith("Text_") and lbl[5:].isdigit():
                    mid = int(lbl[5:])
                else:
                    mid = next_id; next_id += 1
            id_map[i] = mid
            labels[lbl] = mid

        msbt.text_order = []
        for i, m in enumerate(matches):
            attr = m.group(2).strip('\n\r') if m.group(2) is not None else None
            text = m.group(3)
            if text.endswith('\n'): text = text[:-1]
            mid  = id_map[i]
            texts[mid] = msbt._generate_tags(text)
            if attr is not None: attrs[mid] = attr
            msbt.text_order.append(mid)

        msbt.labels        = labels
        msbt.texts         = texts
        msbt.attributes    = attrs
        msbt.original_order = order
        msbt.label_id_map  = {mid: lbl for lbl, mid in labels.items()}
        if attrs: msbt.has_atr1 = True
        msbt.attribute_has_text = 'attributeText:' in content

        msbt.validator.filepath = filepath
        msbt._validate_yaml(labels, texts, matches, id_map)
        # log(f"YAML loaded: {len(labels)} labels, {len(texts)} texts")
        return msbt


# ------------------------------------------------------------------
# CLI
# ------------------------------------------------------------------
def main():
    global DEBUG
    p = argparse.ArgumentParser(description="MSBT Converter")
    p.add_argument('files', nargs='*')
    p.add_argument('--output-dir',        '-o')
    p.add_argument('--debug',             '-d', action='store_true')
    p.add_argument('--continue-on-error', '-c', action='store_true')
    p.add_argument('--tag-definitions',   '-t')
    args  = p.parse_args()
    DEBUG = args.debug

    # If no GCF specified, look for TotK.gcf next to the script
    if not args.tag_definitions:
        default_gcf = os.path.join(os.path.dirname(os.path.abspath(__file__)), "TotK.gcf")
        if os.path.isfile(default_gcf):
            args.tag_definitions = default_gcf
            log(f"Using default GCF: {default_gcf}")
        else:
            log("TotK.gcf not found next to script, proceeding without tag definitions", "WARNING")

    for path in args.files:
        if os.path.isdir(path):
            _process_folder(path, args)
        else:
            _process_file(path, args, out_dir=args.output_dir)

def _process_folder(folder: str, args) -> None:
    """Recursively process all .msbt/.yaml files in folder.
    Output goes to <folder>_ (same parent, folder name + underscore),
    preserving the internal directory structure.
    """
    folder    = os.path.abspath(folder)
    out_root  = folder.rstrip('/\\') + '_'
    parent    = os.path.dirname(folder)

    all_validators: list = []

    for dirpath, _, filenames in os.walk(folder):
        for filename in filenames:
            ext = os.path.splitext(filename)[1].lower()
            if ext not in ('.msbt', '.yaml'):
                continue

            src     = os.path.join(dirpath, filename)
            rel_dir = os.path.relpath(dirpath, folder)
            dst_dir = os.path.join(out_root, rel_dir)
            os.makedirs(dst_dir, exist_ok=True)

            v = _process_file(src, args, out_dir=dst_dir)
            if v is not None:
                all_validators.append(v)

    # Summary
    issues = [v for v in all_validators if v.has_issues()]
    if not issues:
        print(f"\n[OK] All files processed without issues ({len(all_validators)} total)")
    else:
        total_errors   = sum(len(v.errors)   for v in issues)
        total_warnings = sum(len(v.warnings) for v in issues)
        print(f"\n{'='*60}")
        print(f"[SUMMARY] {len(issues)}/{len(all_validators)} files had issues  "
              f"({total_errors} errors, {total_warnings} warnings)")
        print('='*60)
        for v in issues:
            short = os.path.basename(v.filepath)
            
            
            
            # e_str = f"{len(v.errors)} error(s)"   if v.errors   else ""
            # w_str = f"{len(v.warnings)} warning(s)" if v.warnings else ""
            # tag   = ", ".join(filter(None, [e_str, w_str]))
            # print(f"  {short}: {tag}")
            msgs = ([f"[E] {e}" for e in v.errors] +
                    [f"[W] {w}" for w in v.warnings])
            print(f"  {short}: {' | '.join(msgs)}")
            
            
            
        print('='*60)

def _process_file(filepath: str, args, out_dir=None) -> 'Validator | None':
    try:
        ext = os.path.splitext(filepath)[1].lower()
        if ext == '.msbt':
            msbt = MSBTFile()
            if args.tag_definitions: msbt.load_tag_definitions(args.tag_definitions)
            msbt.load_from_file(filepath)
            out_name = os.path.splitext(os.path.basename(filepath))[0] + '.yaml'
            out = os.path.join(out_dir, out_name) if out_dir else \
                  os.path.splitext(filepath)[0] + '.yaml'
            msbt.export_to_yaml(out)
            log(f"Created: {out}")
            msbt.validator.print_report()
            return msbt.validator
        elif ext == '.yaml':
            msbt = MSBTFile.from_yaml(filepath, args.tag_definitions)
            out_name = os.path.splitext(os.path.basename(filepath))[0] + '.msbt'
            out = os.path.join(out_dir, out_name) if out_dir else \
                  os.path.splitext(filepath)[0] + '.msbt'
            msbt.save_to_file(out)
            log(f"Created: {out}")
            msbt.validator.print_report()
            return msbt.validator
        else:
            log(f"Unsupported: {filepath}", "WARNING")
            return None
    except Exception as e:
        log(f"Error: {filepath}: {e}", "ERROR")
        if DEBUG: traceback.print_exc()
        v = Validator(filepath)
        v.error(f"Exception: {e}")
        return v

if __name__ == "__main__":
    main()