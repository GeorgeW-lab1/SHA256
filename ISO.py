#!/usr/bin/env python3
"""
SHA-256 Optical Disk Binary Encoder / ISO Maker
------------------------------------------------
Creates:
  - a deterministic binary manifest describing SHA-256's 64-round logic
  - a raw 2048-byte-sector ISO-9660 image containing the manifest and README
  - an optional raw binary track map for optical-disk layout experiments

IMPORTANT:
This is a digital design/metadata encoder, NOT a fabricated optical computer.
The ISO stores a description of the circuit. It does not itself execute SHA-256
optically. Any physical implementation needs a validated optical logic design,
state storage/feedback, thresholding, and exact digital verification.

Usage:
  python sha256_optical_iso_maker.py
  python sha256_optical_iso_maker.py --out sha256_optical.iso
  python sha256_optical_iso_maker.py --out sha256_optical.iso --track-map sha256_tracks.bin
  python sha256_optical_iso_maker.py --verify sha256_optical.iso

The generated ISO is a minimal ISO-9660 Level 1 image with one file:
  /SHA256LOG.BIN
and a README file /README.TXT.
"""

import argparse
import hashlib
import json
import math
import struct
import sys
from pathlib import Path

SECTOR = 2048
PVD_SECTOR = 16
TERM_SECTOR = 17
ROOT_SECTOR = 18
MANIFEST_SECTOR = 19
README_SECTOR = 20

MAGIC = b"SHA256OD"  # SHA-256 Optical Disk manifest
VERSION = 1

ROUND_CONSTANTS = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]

ROUND_OPS = [
    ("SIGMA1_E", "ROTR(e,6) XOR ROTR(e,11) XOR ROTR(e,25)"),
    ("CH_EFG", "((e AND f) XOR ((NOT e) AND g))"),
    ("T1", "(h + SIGMA1_E + CH_EFG + K[t] + W[t]) mod 2^32"),
    ("SIGMA0_A", "ROTR(a,2) XOR ROTR(a,13) XOR ROTR(a,22)"),
    ("MAJ_ABC", "((a AND b) XOR (a AND c) XOR (b AND c))"),
    ("T2", "(SIGMA0_A + MAJ_ABC) mod 2^32"),
    ("UPDATE", "a'=T1+T2; e'=d+T1; shift remaining registers; mod 2^32"),
]

README = """SHA-256 OPTICAL DISK LOGIC MANIFEST
==================================

This ISO contains SHA256LOG.BIN, a binary descriptor for the SHA-256
compression-round logic and its fixed round constants.

This is NOT encryption. SHA-256 is a cryptographic hash function.

The binary manifest describes the algorithm and candidate physical logic blocks.
It does not define a validated photonic layout or guarantee that a passive disk
can compute the hash. A physical implementation must solve optical Boolean
logic, 32-bit carry propagation, state storage/feedback, signal regeneration,
and error-free readout.

Suggested experiment:
1. Decode SHA256LOG.BIN with the accompanying Python encoder.
2. Implement one Boolean gate on an optical bench and verify its truth table.
3. Implement Ch and Maj, then a small adder.
4. Validate one complete SHA-256 round against a software reference.
5. Do not claim optical SHA-256 operation until all outputs match test vectors.

Binary manifest format (little-endian except the ISO itself):
  8 bytes  magic: SHA256OD
  u16      version
  u16      flags (bit 0 = descriptive-only)
  u32      rounds (64)
  u32      block size in bits (512)
  u32      state size in bits (256)
  u32      number of round constants (64)
  64*u32   SHA-256 round constants
  u32      operation record count
  records  u8 name length, u16 formula length, then UTF-8 name + formula
  32 bytes SHA-256 checksum of all preceding manifest bytes

The ISO is a minimal ISO-9660 Level 1 filesystem using 2048-byte sectors.
"""

def u16le(value):
    return struct.pack("<H", value)

def u32le(value):
    return struct.pack("<I", value)

def u16be(value):
    return struct.pack(">H", value)

def u32be(value):
    return struct.pack(">I", value)

def both_endian_16(value):
    return u16le(value) + u16be(value)

def both_endian_32(value):
    return u32le(value) + u32be(value)

def pad_sector(data):
    if len(data) > SECTOR:
        raise ValueError("ISO directory record exceeds one sector")
    return data + b"\x00" * (SECTOR - len(data))

def make_record(name, extent, size, flags=0, is_dir=False):
    if isinstance(name, str):
        name = name.encode("ascii")
    # Directory identifiers '.' and '..' are represented by one-byte 0 and 1.
    name_len = len(name)
    record_len = 33 + name_len + (1 if name_len % 2 == 0 else 0)
    rec = bytearray(record_len)
    rec[0] = record_len
    rec[1] = 0  # extended attribute record length
    rec[2:10] = both_endian_32(extent)
    rec[10:18] = both_endian_32(size)
    rec[18:25] = bytes([126, 10, 28, 0, 0, 0, 0])  # 2026-10-28 UTC-ish date
    rec[25] = flags | (2 if is_dir else 0)
    rec[26] = 0  # file unit size
    rec[27] = 0  # interleave gap size
    rec[28:32] = both_endian_16(1)  # volume sequence number
    rec[32] = name_len
    rec[33:33 + name_len] = name
    return bytes(rec)

def make_manifest():
    payload = bytearray()
    payload += MAGIC
    payload += u16le(VERSION)
    payload += u16le(1)  # descriptive-only
    payload += u32le(64)
    payload += u32le(512)
    payload += u32le(256)
    payload += u32le(len(ROUND_CONSTANTS))
    for constant in ROUND_CONSTANTS:
        payload += u32le(constant)
    payload += u32le(len(ROUND_OPS))
    for name, formula in ROUND_OPS:
        n = name.encode("utf-8")
        f = formula.encode("utf-8")
        payload += bytes([len(n)]) + u16le(len(f)) + n + f
    payload += hashlib.sha256(payload).digest()
    return bytes(payload)

def make_pvd(total_sectors):
    pvd = bytearray(SECTOR)
    pvd[0] = 1
    pvd[1:6] = b"CD001"
    pvd[6] = 1
    pvd[8:40] = b"PYTHON SHA256 OPTICAL DISK".ljust(32, b" ")
    pvd[40:72] = b"SHA256_LOGIC".ljust(32, b" ")
    pvd[80:88] = both_endian_32(total_sectors)
    pvd[120:124] = both_endian_16(1)
    pvd[124:128] = both_endian_16(1)
    pvd[128:132] = both_endian_16(SECTOR)
    pvd[132:140] = both_endian_32(0)  # path table size
    pvd[140:144] = u32le(0)
    pvd[144:148] = u32le(0)
    pvd[148:152] = u32be(0)
    pvd[152:156] = u32be(0)
    root = make_record(b"\x00", ROOT_SECTOR, SECTOR, is_dir=True)
    pvd[156:156 + len(root)] = root
    pvd[813:830] = b"SHA256 LOGIC DISC"
    pvd[881] = 1  # file structure version
    pvd[883:883 + 8] = b"PYSHALOG"
    pvd[883 + 8:883 + 40] = b"PYTHON SHA256 OPTICAL ISO MAKER".ljust(32, b" ")
    pvd[883 + 40:883 + 72] = b"SHA256 Optical Disk".ljust(32, b" ")
    pvd[883 + 72:883 + 80] = b"2026102800000000"
    pvd[883 + 80:883 + 88] = b"2026102800000000"
    pvd[883 + 88:883 + 96] = b"2026102800000000"
    pvd[883 + 96:883 + 104] = b"2026102800000000"
    pvd[881] = 1
    return bytes(pvd)

def make_terminator():
    block = bytearray(SECTOR)
    block[0] = 255
    block[1:6] = b"CD001"
    block[6] = 1
    return bytes(block)

def make_root_dir(manifest_size, readme_size):
    records = bytearray()
    records += make_record(b"\x00", ROOT_SECTOR, SECTOR, is_dir=True)
    records += make_record(b"\x01", ROOT_SECTOR, SECTOR, is_dir=True)
    records += make_record(b"SHA256LOG.BIN;1", MANIFEST_SECTOR, manifest_size)
    records += make_record(b"README.TXT;1", README_SECTOR, readme_size)
    return pad_sector(bytes(records))

def make_iso(manifest, readme):
    manifest_sectors = (len(manifest) + SECTOR - 1) // SECTOR
    readme_sectors = (len(readme) + SECTOR - 1) // SECTOR
    # Place README after the manifest, so it works for variable manifest sizes.
    readme_sector = MANIFEST_SECTOR + manifest_sectors
    total_sectors = readme_sector + readme_sectors
    pvd = bytearray(make_pvd(total_sectors))
    # Root directory uses fixed sector 18; root records refer to actual file extents.
    root = bytearray(SECTOR)
    records = bytearray()
    records += make_record(b"\x00", ROOT_SECTOR, SECTOR, is_dir=True)
    records += make_record(b"\x01", ROOT_SECTOR, SECTOR, is_dir=True)
    records += make_record(b"SHA256LOG.BIN;1", MANIFEST_SECTOR, len(manifest))
    records += make_record(b"README.TXT;1", readme_sector, len(readme))
    root[:] = pad_sector(bytes(records))
    # Patch the PVD's root directory record extent and size (both-endian fields).
    root_record = make_record(b"\x00", ROOT_SECTOR, SECTOR, is_dir=True)
    pvd[156:156 + len(root_record)] = root_record
    image = bytearray(total_sectors * SECTOR)
    image[PVD_SECTOR * SECTOR:(PVD_SECTOR + 1) * SECTOR] = pvd
    image[TERM_SECTOR * SECTOR:(TERM_SECTOR + 1) * SECTOR] = make_terminator()
    image[ROOT_SECTOR * SECTOR:(ROOT_SECTOR + 1) * SECTOR] = root
    image[MANIFEST_SECTOR * SECTOR:MANIFEST_SECTOR * SECTOR + len(manifest)] = manifest
    image[readme_sector * SECTOR:readme_sector * SECTOR + len(readme)] = readme
    return bytes(image)

def make_track_map(track_path, tracks=64, sectors_per_track=128):
    """
    Write a research-only raw binary map:
      header: 8-byte magic, u16 version, u16 tracks, u16 sectors/track
      each sector record: track index, sector index, round index, op index,
                          32-bit tag and 32-byte SHA-256 checksum.
    This is an abstract layout index, not optical mask fabrication data.
    """
    data = bytearray(b"SHATRAK1")
    data += u16le(1) + u16le(tracks) + u16le(sectors_per_track)
    for track in range(tracks):
        for sector in range(sectors_per_track):
            round_index = track % 64
            op_index = sector % len(ROUND_OPS)
            tag = ((track & 0xFFFF) << 16) | (sector & 0xFFFF)
            record = u16le(track) + u16le(sector) + u16le(round_index) + u16le(op_index) + u32le(tag)
            data += record + hashlib.sha256(record).digest()
    Path(track_path).write_bytes(data)
    return len(data)

def verify_iso(path):
    data = Path(path).read_bytes()
    if len(data) % SECTOR:
        raise ValueError("Image size is not a multiple of 2048 bytes")
    if data[PVD_SECTOR * SECTOR + 1: PVD_SECTOR * SECTOR + 6] != b"CD001":
        raise ValueError("Primary Volume Descriptor not found at sector 16")
    if data[TERM_SECTOR * SECTOR] != 255 or data[TERM_SECTOR * SECTOR + 1:TERM_SECTOR * SECTOR + 6] != b"CD001":
        raise ValueError("Volume Descriptor Set Terminator not found")
    # Find the manifest by known sector in this generated format.
    manifest = data[MANIFEST_SECTOR * SECTOR:]
    manifest = manifest[:manifest.find(b"README.TXT") if b"README.TXT" in manifest else len(manifest)]
    if not data[MANIFEST_SECTOR * SECTOR:MANIFEST_SECTOR * SECTOR + 8] == MAGIC:
        raise ValueError("SHA256 manifest magic not found at sector 19")
    # Validate checksum by parsing manifest fields and operation records.
    raw = data[MANIFEST_SECTOR * SECTOR:]
    pos = 8 + 2 + 2 + 4 * 4 + 64 * 4
    op_count = struct.unpack_from("<I", raw, pos)[0]
    pos += 4
    for _ in range(op_count):
        name_len = raw[pos]
        formula_len = struct.unpack_from("<H", raw, pos + 1)[0]
        pos += 3 + name_len + formula_len
    expected = raw[pos:pos + 32]
    actual = hashlib.sha256(raw[:pos]).digest()
    if expected != actual:
        raise ValueError("Manifest checksum failed")
    return {"valid": True, "bytes": len(data), "sectors": len(data) // SECTOR, "manifest_sha256": actual.hex()}

def main():
    parser = argparse.ArgumentParser(description="Create a SHA-256 optical logic descriptor ISO.")
    parser.add_argument("--out", default="sha256_optical_logic.iso", help="Output ISO path")
    parser.add_argument("--track-map", default="", help="Optional output raw track-map binary")
    parser.add_argument("--verify", default="", help="Verify a previously generated ISO")
    args = parser.parse_args()

    if args.verify:
        try:
            print(json.dumps(verify_iso(args.verify), indent=2))
            return 0
        except Exception as exc:
            print("VERIFY FAILED:", exc, file=sys.stderr)
            return 1

    manifest = make_manifest()
    readme = README.encode("utf-8")
    iso = make_iso(manifest, readme)
    Path(args.out).write_bytes(iso)
    print("Created ISO:", Path(args.out).resolve())
    print("ISO bytes:", len(iso))
    print("Manifest bytes:", len(manifest))
    print("Manifest SHA-256:", hashlib.sha256(manifest).hexdigest())
    print("This ISO describes SHA-256 logic; it is not a physical optical processor.")
    if args.track_map:
        size = make_track_map(args.track_map)
        print("Created abstract track map:", Path(args.track_map).resolve())
        print("Track map bytes:", size)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
