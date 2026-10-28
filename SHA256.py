
import argparse
import hashlib
import math
import struct
import time
from pathlib import Path

K = [
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

INITIAL = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
]

MASK = 0xffffffff
SECTOR = 2048
CD_1X = 150 * 1024
BLOCK = 64


def rotr(x, n):
    return ((x >> n) | (x << (32 - n))) & MASK


def compress(state, block):
    w = list(struct.unpack(">16I", block))

    for i in range(16, 64):
        s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3)
        s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10)
        w.append((w[i - 16] + s0 + w[i - 7] + s1) & MASK)

    a, b, c, d, e, f, g, h = state

    for i in range(64):
        s1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
        ch = (e & f) ^ ((~e) & g)
        t1 = (h + s1 + ch + K[i] + w[i]) & MASK

        s0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
        maj = (a & b) ^ (a & c) ^ (b & c)
        t2 = (s0 + maj) & MASK

        a, b, c, d, e, f, g, h = (
            (t1 + t2) & MASK, a, b, c,
            (d + t1) & MASK, e, f, g
        )

    return [(x + y) & MASK for x, y in zip(
        state, [a, b, c, d, e, f, g, h]
    )]


def sha256_trace(data):
    """Compute SHA-256 and return the digest plus per-round trace."""
    original_length = len(data)
    bit_length = original_length * 8

    padded = data + b"\x80"
    padded += b"\x00" * ((56 - len(padded) % 64) % 64)
    padded += struct.pack(">Q", bit_length)

    state = INITIAL.copy()
    trace = []

    for block_index in range(0, len(padded), 64):
        block = padded[block_index:block_index + 64]

        w = list(struct.unpack(">16I", block))
        for i in range(16, 64):
            s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3)
            s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10)
            w.append((w[i - 16] + s0 + w[i - 7] + s1) & MASK)

        working = state.copy()
        a, b, c, d, e, f, g, h = working

        for r in range(64):
            s1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
            ch = (e & f) ^ ((~e) & g)
            t1 = (h + s1 + ch + K[r] + w[r]) & MASK
            s0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
            maj = (a & b) ^ (a & c) ^ (b & c)
            t2 = (s0 + maj) & MASK

            a, b, c, d, e, f, g, h = (
                (t1 + t2) & MASK, a, b, c,
                (d + t1) & MASK, e, f, g
            )

            trace.append({
                "block": block_index // 64,
                "round": r,
                "t1": t1,
                "t2": t2,
                "a": a,
                "e": e,
            })

        state = [(x + y) & MASK for x, y in zip(
            state, [a, b, c, d, e, f, g, h]
        )]

    digest = b"".join(struct.pack(">I", x) for x in state).hex()
    return digest, trace, len(padded) // 64


def simulate(data, disk_path, speed_x, rpm, sectors_per_track):
    disk = Path(disk_path).read_bytes() if disk_path else b""
    disk_sectors = math.ceil(len(disk) / SECTOR) if disk else 0

    digest, trace, blocks = sha256_trace(data)

    # 1x CD speed is 150 KiB/s; sectors are 2048 bytes.
    sectors_per_second = speed_x * CD_1X / SECTOR
    read_seconds = 0.0
    rotational_seconds = 0.0
    sectors_read = 0

    # Simulate one disk-sector read for each SHA-256 round.
    rounds = blocks * 64
    for i in range(rounds):
        read_seconds += SECTOR / (speed_x * CD_1X)

        # Average rotational wait: half a revolution.
        rotational_seconds += 30.0 / rpm
        sectors_read += 1

        if disk_sectors:
            sector_index = i % disk_sectors
            sector_data = disk[sector_index * SECTOR:(sector_index + 1) * SECTOR]
            # The sector is read as simulated input; it does not alter SHA logic.
            _ = sector_data

    # Approximate serialized read model: throughput plus average rotational wait.
    simulated_time = read_seconds + rotational_seconds
    actual_start = time.perf_counter()
    checked_digest = hashlib.sha256(data).hexdigest()
    software_seconds = time.perf_counter() - actual_start

    print("\n=== SHA-256 DISK SIMULATOR ===")
    print(f"Input bytes:             {len(data)}")
    print(f"SHA-256 message blocks:  {blocks}")
    print(f"SHA-256 rounds:          {rounds}")
    print(f"Disk speed:              {speed_x:g}x CD")
    print(f"Disk RPM:                {rpm:g}")
    print(f"Disk image bytes:        {len(disk)}")
    print(f"Disk image sectors:      {disk_sectors}")
    print(f"Simulated sector reads:  {sectors_read}")
    print(f"Read throughput:         {sectors_per_second:.2f} sectors/s")
    print(f"Estimated read time:     {read_seconds:.6f} s")
    print(f"Estimated rotation wait: {rotational_seconds:.6f} s")
    print(f"Estimated disk time:     {simulated_time:.6f} s")
    print(f"Python hashlib time:     {software_seconds:.6f} s")
    print(f"Digest:                  {digest}")
    print(f"Reference digest:        {checked_digest}")
    print(f"Verified:                {digest == checked_digest}")

    print("\nFirst 10 simulated rounds:")
    for item in trace[:10]:
        print(
            f"block={item['block']:03d} round={item['round']:02d} "
            f"T1={item['t1']:08x} T2={item['t2']:08x} "
            f"a={item['a']:08x} e={item['e']:08x}"
        )

DISK_PROFILES = {
    "floppy": {"kind": "rotating", "rpm": 300, "sector": 512, "mbps": 0.06},
    "hdd": {"kind": "rotating", "rpm": 7200, "sector": 512, "mbps": 200},
    "cd": {"kind": "rotating", "rpm": 3600, "sector": 2048, "mbps": 7.8},
    "dvd": {"kind": "rotating", "rpm": 7200, "sector": 2048, "mbps": 22},
    "bluray": {"kind": "rotating", "rpm": 10000, "sector": 2048, "mbps": 50},
    "ssd": {"kind": "solid", "rpm": 0, "sector": 4096, "mbps": 550},
    "nvme": {"kind": "solid", "rpm": 0, "sector": 4096, "mbps": 7000},
    "usb": {"kind": "solid", "rpm": 0, "sector": 4096, "mbps": 100},
    "ramdisk": {"kind": "solid", "rpm": 0, "sector": 4096, "mbps": 20000},
}


def simulate(data, disk_path, speed_x, rpm, sectors_per_track, disk_type):
    profile = DISK_PROFILES[disk_type].copy()
    sector_size = profile["sector"]
    disk = Path(disk_path).read_bytes() if disk_path else b""
    disk_sectors = math.ceil(len(disk) / sector_size) if disk else 0

    digest, trace, blocks = sha256_trace(data)
    rounds = blocks * 64

    # For optical media, speed_x scales the nominal transfer rate.
    # For other media, speed_x also acts as a configurable multiplier.
    transfer_mbps = profile["mbps"] * speed_x
    bytes_per_second = transfer_mbps * 1_000_000 / 8

    read_bytes = rounds * sector_size
    read_seconds = read_bytes / bytes_per_second

    if profile["kind"] == "rotating":
        effective_rpm = rpm if rpm > 0 else profile["rpm"]
        rotation_wait = rounds * 30.0 / effective_rpm
    else:
        effective_rpm = 0
        rotation_wait = 0.0

    # The disk read model is illustrative; SHA-256 is still computed in software.
    simulated_time = read_seconds + rotation_wait

    start = time.perf_counter()
    reference = hashlib.sha256(data).hexdigest()
    software_time = time.perf_counter() - start

    print("\n=== UNIVERSAL DISK SHA-256 SIMULATOR ===")
    print(f"Disk type:              {disk_type}")
    print(f"Storage type:           {profile['kind']}")
    print(f"Input bytes:            {len(data)}")
    print(f"SHA-256 blocks:         {blocks}")
    print(f"SHA-256 rounds:         {rounds}")
    print(f"Sector size:            {sector_size} bytes")
    print(f"Transfer rate:          {transfer_mbps:g} Mbit/s")
    print(f"Disk RPM:               {effective_rpm:g}")
    print(f"Disk image size:        {len(disk)} bytes")
    print(f"Disk image sectors:     {disk_sectors}")
    print(f"Simulated bytes read:   {read_bytes}")
    print(f"Estimated read time:    {read_seconds:.9f} s")
    print(f"Rotational latency:     {rotation_wait:.9f} s")
    print(f"Estimated total time:   {simulated_time:.9f} s")
    print(f"Software hash time:     {software_time:.9f} s")
    print(f"SHA-256:                {digest}")
    print(f"Reference:              {reference}")
    print(f"Verified:               {digest == reference}")

    print("\nFirst 10 SHA-256 rounds:")
    for item in trace[:10]:
        print(
            f"block={item['block']:03d} round={item['round']:02d} "
            f"T1={item['t1']:08x} T2={item['t2']:08x} "
            f"a={item['a']:08x} e={item['e']:08x}"
        )


def main():
    parser = argparse.ArgumentParser(
        description="Simulate SHA-256 with different storage technologies."
    )
    parser.add_argument("--text", default="optical disk sha256 test")
    parser.add_argument("--input", help="File to hash instead of --text")
    parser.add_argument("--disk", help="Optional disk image to read")
    parser.add_argument(
        "--disk-type",
        choices=DISK_PROFILES.keys(),
        default="dvd",
        help="floppy, hdd, cd, dvd, bluray, ssd, nvme, usb, ramdisk",
    )
    parser.add_argument(
        "--speed-x",
        type=float,
        default=1.0,
        help="Transfer-rate multiplier for the selected disk profile",
    )
    parser.add_argument(
        "--rpm",
        type=float,
        default=0,
        help="Override RPM for rotating media; 0 uses profile RPM",
    )
    parser.add_argument("--sectors-per-track", type=int, default=128)
    args = parser.parse_args()

    if args.speed_x <= 0 or args.rpm < 0 or args.sectors_per_track <= 0:
        parser.error("speed-x and sectors-per-track must be positive; rpm cannot be negative")

    data = (
        Path(args.input).read_bytes()
        if args.input
        else args.text.encode("utf-8")
    )

    simulate(
        data,
        args.disk,
        args.speed_x,
        args.rpm,
        args.sectors_per_track,
        args.disk_type,
    )


if __name__ == "__main__":
    main()
