#!/usr/bin/env python3
"""
Magnetic tape computer: write a synthetic logic circuit to tape, read it back,
and run a pipelined SHA-256 solver whose stages ARE that circuit.

TAPE (10 parallel tracks per frame, like 9-track tape plus a clock track)
  tracks 0-7  data byte            track 8  odd parity       track 9  clock
  - Each cell is a magnetic domain: +1 / -1.
  - WRITE: a cell flips only if the write field beats that cell's coercivity
    (Hc ~ N(1, coercivity-sigma)).  Every block is read back and rewritten
    until the magnetization is right (write-verify).
  - READ : each head sees  +-1 + Gaussian noise  and thresholds at 0.
    Re-passes are averaged.  Per-frame parity + a longitudinal parity byte
    (LRC) per block correct a single flipped cell; CRC-32 is the final check.
  - The clock track is written onto the tape: the tape IS the logical clock.
    1 tick = 1 frame time = 1 clock-track pulse.  Loading the circuit costs
    ticks, rewinding costs ticks, and the pipeline then runs on the same ticks.

BLOCKS on tape:  gap | A5 5A | type | len16 | payload | crc32 | lrc
  type 1 CIRCUIT   netlist (word-level gates)
  type 2 CONSTANTS 32-bit table; stage i uses table[i mod len]   (counter & modulus)
  type 3 LABEL     text
  type FF END      end of tape mark

CIRCUIT netlist: inputs (named 32-bit words), gates, named outputs.  Each gate
is 4 bytes (kind, param, a, b); wire index = n_inputs + gate_index.
  LUT  param = 4-bit truth table, index (a_bit<<1 | b_bit), applied bitwise
         AND=1000 OR=1110 XOR=0110 NAND=0111 NOR=0001 XNOR=1001 ANDN(~a&b)=0010
  ADD  param = modulus bits (adds mod 2^param)
  ROTR / SHR  param = amount (pure wiring in hardware)

Commands:
  python magnetic_computer.py write --tape sha.mtape
  python magnetic_computer.py write --tape fa.mtape --asm full_adder.asm
  python magnetic_computer.py dump  --tape sha.mtape --disasm
  python magnetic_computer.py truth --tape fa.mtape
  python magnetic_computer.py run   --tape sha.mtape --lanes 4 --nonces 2000
  python magnetic_computer.py run   --tape sha.mtape --noise 0.8 --damage 1
"""
import argparse
import hashlib
import itertools
import random
import struct
import sys
import zlib
from collections import Counter

MASK = 0xFFFFFFFF
TRACKS = 10
GAP = 6                      # inter-block gap, frames
WIND = 32                    # fast-wind speed: frames per tick
SYNC = bytes([0xA5, 0x5A])
T_CIRCUIT, T_CONST, T_LABEL, T_END = 1, 2, 3, 0xFF
TYPE_NAMES = {T_CIRCUIT: "CIRCUIT", T_CONST: "CONSTANTS", T_LABEL: "LABEL", T_END: "END"}
MAGIC = b"MAGTAPE1"

IV = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
      0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

# Source data for the WRITER only.  The reading side never touches this table.
K_TABLE = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]

# The built-in circuit: one SHA-256 round plus one message-schedule step.
SHA_ROUND_ASM = """
# one pipeline stage = one SHA-256 round + one schedule step
in a b c d e f g h w0 w1 w9 w14 k
# Sigma1(e)
e6   = ROTR e 6
e11  = ROTR e 11
e25  = ROTR e 25
s1x  = LUT XOR e6 e11
S1   = LUT XOR s1x e25
# Ch(e,f,g) = (e & f) ^ (~e & g)
ef   = LUT AND e f
neg  = LUT ANDN e g
CH   = LUT XOR ef neg
# T1 = h + S1 + Ch + k + w0
h1   = ADD h S1 32
h2   = ADD h1 CH 32
h3   = ADD h2 k 32
T1   = ADD h3 w0 32
# Sigma0(a)
a2   = ROTR a 2
a13  = ROTR a 13
a22  = ROTR a 22
s0x  = LUT XOR a2 a13
S0   = LUT XOR s0x a22
# Maj(a,b,c)
ab   = LUT AND a b
ac   = LUT AND a c
bc   = LUT AND b c
mx   = LUT XOR ab ac
MAJ  = LUT XOR mx bc
T2   = ADD S0 MAJ 32
A    = ADD T1 T2 32
E    = ADD d T1 32
# message schedule: W[t+16] = w0 + s0(w1) + w9 + s1(w14)
w1a  = ROTR w1 7
w1b  = ROTR w1 18
w1c  = SHR w1 3
g0x  = LUT XOR w1a w1b
G0   = LUT XOR g0x w1c
w14a = ROTR w14 17
w14b = ROTR w14 19
w14c = SHR w14 10
g1x  = LUT XOR w14a w14b
G1   = LUT XOR g1x w14c
n1   = ADD w0 G0 32
n2   = ADD n1 w9 32
W    = ADD n2 G1 32
out na = A
out nb = a
out nc = b
out nd = c
out ne = E
out nf = e
out ng = f
out nh = g
out nw = W
"""
SHA_IN = ["a", "b", "c", "d", "e", "f", "g", "h", "w0", "w1", "w9", "w14", "k"]
SHA_OUT = ["na", "nb", "nc", "nd", "ne", "nf", "ng", "nh", "nw"]


# ================================================================ circuit
class CircuitError(Exception):
    pass


LUTS = {"AND": 0b1000, "OR": 0b1110, "XOR": 0b0110, "NAND": 0b0111,
        "NOR": 0b0001, "XNOR": 0b1001, "ANDN": 0b0010}
LUT_NAMES = {v: k for k, v in LUTS.items()}
KIND = {"LUT": 1, "ADD": 2, "ROTR": 3, "SHR": 4}
KIND_NAMES = {v: k for k, v in KIND.items()}


class Circuit:
    def __init__(self, inputs, gates, outputs):
        self.inputs, self.gates, self.outputs = inputs, gates, outputs
        self.n_in = len(inputs)
        if self.n_in + len(gates) > 255:
            raise CircuitError("too many wires (max 255)")
        for i, (k, p, a, b) in enumerate(gates):
            lim = self.n_in + i
            if k not in KIND_NAMES or a >= lim or (k in (1, 2) and b >= lim):
                raise CircuitError(f"gate {i}: bad kind or forward reference")
            if (k == 1 and p > 15) or (k == 2 and not 1 <= p <= 32) or (k in (3, 4) and p > 31):
                raise CircuitError(f"gate {i}: bad parameter {p}")
        for name, w in outputs:
            if w >= self.n_in + len(gates):
                raise CircuitError(f"output {name}: no such wire")

    def run(self, vec):
        W = list(vec)
        for kind, p, a, b in self.gates:
            x = W[a]
            if kind == 1:
                y = W[b]
                nx, ny = ~x & MASK, ~y & MASK
                o = 0
                if p & 1: o |= nx & ny
                if p & 2: o |= nx & y
                if p & 4: o |= x & ny
                if p & 8: o |= x & y
                W.append(o)
            elif kind == 2:
                W.append((x + W[b]) & ((1 << p) - 1))
            elif kind == 3:
                W.append(((x >> p) | (x << (32 - p))) & MASK)
            else:
                W.append(x >> p)
        return [W[w] for _, w in self.outputs]

    def encode(self):
        out = bytearray([self.n_in])
        for n in self.inputs:
            nb = n.encode()
            out += bytes([len(nb)]) + nb
        out += struct.pack(">H", len(self.gates))
        for g in self.gates:
            out += bytes(g)
        out.append(len(self.outputs))
        for n, w in self.outputs:
            nb = n.encode()
            out += bytes([len(nb)]) + nb + bytes([w])
        return bytes(out)

    @classmethod
    def decode(cls, raw):
        try:
            pos = 0
            n_in = raw[pos]; pos += 1
            inputs = []
            for _ in range(n_in):
                ln = raw[pos]; inputs.append(raw[pos + 1:pos + 1 + ln].decode()); pos += 1 + ln
            ng = struct.unpack_from(">H", raw, pos)[0]; pos += 2
            gates = [tuple(raw[pos + 4 * i:pos + 4 * i + 4]) for i in range(ng)]
            pos += 4 * ng
            n_out = raw[pos]; pos += 1
            outputs = []
            for _ in range(n_out):
                ln = raw[pos]; name = raw[pos + 1:pos + 1 + ln].decode()
                outputs.append((name, raw[pos + 1 + ln])); pos += 2 + ln
            if pos != len(raw) or any(len(g) != 4 for g in gates):
                raise CircuitError("netlist length mismatch")
        except (IndexError, struct.error, UnicodeDecodeError) as e:
            raise CircuitError(f"netlist unreadable: {e}")
        return cls(inputs, gates, outputs)

    def census(self):
        c = Counter()
        for k, p, a, b in self.gates:
            c[KIND_NAMES[k] if k != 1 else "LUT:" + LUT_NAMES.get(p, format(p, "04b"))] += 1
        return c

    def disasm(self):
        names = list(self.inputs) + [f"w{self.n_in + i}" for i in range(len(self.gates))]
        lines = ["in  " + " ".join(self.inputs)]
        for i, (k, p, a, b) in enumerate(self.gates):
            dst = names[self.n_in + i]
            if k == 1:
                lines.append(f"{dst:>5} = LUT {LUT_NAMES.get(p, format(p, '04b')):<5} {names[a]} {names[b]}")
            elif k == 2:
                lines.append(f"{dst:>5} = ADD {names[a]} {names[b]} mod 2^{p}")
            else:
                lines.append(f"{dst:>5} = {KIND_NAMES[k]} {names[a]} {p}")
        for n, w in self.outputs:
            lines.append(f"out {n} = {names[w]}")
        return "\n".join(lines)


def assemble(text):
    names, inputs, gates, outs = {}, [], [], []
    for lineno, line in enumerate(text.splitlines(), 1):
        t = line.split("#")[0].replace("=", " = ").split()
        if not t:
            continue
        try:
            if t[0] == "in":
                if gates or inputs:
                    raise CircuitError("'in' must come once, first")
                for n in t[1:]:
                    names[n] = len(inputs); inputs.append(n)
            elif t[0] == "out":
                outs.append((t[1], names[t[3]]))
            else:
                dst, op = t[0], t[2]
                if dst in names:
                    raise CircuitError(f"{dst} already defined")
                if op == "LUT":
                    fn = LUTS[t[3]] if t[3] in LUTS else int(t[3], 2)
                    g = (1, fn, names[t[4]], names[t[5]])
                elif op == "ADD":
                    g = (2, int(t[5]) if len(t) > 5 else 32, names[t[3]], names[t[4]])
                elif op in ("ROTR", "SHR"):
                    g = (KIND[op], int(t[4]), names[t[3]], 0)
                else:
                    raise CircuitError(f"unknown op {op}")
                names[dst] = len(inputs) + len(gates)
                gates.append(g)
        except (KeyError, IndexError, ValueError) as e:
            raise CircuitError(f"line {lineno}: {line.strip()!r} ({type(e).__name__} {e})")
    return Circuit(inputs, gates, outs)


# ================================================================ tape medium
class TapeError(Exception):
    pass


class ReadError(TapeError):
    pass


def frame_word(byte, pos):
    par = (bin(byte).count("1") & 1) ^ 1        # odd parity over data+parity
    return byte | (par << 8) | ((pos & 1) << 9)  # clock track alternates


def block_bytes(typ, payload):
    body = bytes([typ]) + len(payload).to_bytes(2, "big") + payload
    seq = SYNC + body + zlib.crc32(body).to_bytes(4, "big")
    lrc = 0
    for b in seq:
        lrc ^= b
    return seq + bytes([lrc])


def save_tape(path, cells):
    with open(path, "wb") as f:
        f.write(MAGIC + struct.pack(">I", len(cells)))
        f.write(b"".join(struct.pack(">H", c) for c in cells))


def load_tape(path):
    raw = open(path, "rb").read()
    if raw[:8] != MAGIC:
        raise TapeError("not a magnetic tape image")
    n = struct.unpack_from(">I", raw, 8)[0]
    return list(struct.unpack_from(">%dH" % n, raw, 12))


class WriteDrive:
    """Write head + transport.  Cells flip only when field >= coercivity."""

    def __init__(self, frames, field, c_sigma, seed):
        self.cells = [0] * frames          # erased tape
        self.pos = 0
        self.field, self.c_sigma = field, c_sigma
        self.rng = random.Random(seed)
        self.ticks = 0
        self.failed_cells = 0              # cells that refused to flip (first try)
        self.rewrites = 0

    def _write_frame(self, pos, byte):
        want, old = frame_word(byte, pos), self.cells[pos]
        new = old
        for t in range(TRACKS):
            if ((want >> t) & 1) != ((old >> t) & 1):
                hc = self.rng.gauss(1.0, self.c_sigma) if self.c_sigma else 1.0
                if self.field >= hc:
                    new ^= 1 << t
        self.cells[pos] = new
        return want

    def write_block(self, typ, payload, attempts=4):
        data = bytes(GAP) + block_bytes(typ, payload)
        start = self.pos
        if start + len(data) > len(self.cells):
            raise TapeError("tape full")
        for attempt in range(attempts):
            wants = [self._write_frame(start + i, b) for i, b in enumerate(data)]
            self.ticks += len(data)
            bad = sum(bin(self.cells[start + i] ^ w).count("1") for i, w in enumerate(wants))
            if attempt == 0:
                self.failed_cells += bad
            if bad == 0:
                self.pos = start + len(data)
                return len(data)
            self.rewrites += 1
            self.ticks += -(-len(data) // WIND)    # rewind to block start
        raise TapeError(f"write-verify failed on {TYPE_NAMES.get(typ, typ)} block "
                        f"after {attempts} attempts (write field too weak?)")


# ================================================================ read head
class Head:
    """A read head: sees +-1 flux plus its own Gaussian noise."""

    def __init__(self, cells, sigma, seed):
        self.cells, self.sigma = cells, sigma
        self.rng = random.Random(seed)
        self.ticks = 0          # frame-passes read
        self.wind = 0           # rewind ticks
        self.frames = 0         # frames touched (for rewind accounting)
        self.clock_errors = 0
        self.fixes = 0

    def read_frame(self, pos, passes):
        if not 0 <= pos < len(self.cells):
            raise ReadError("ran off the tape")
        c = self.cells[pos]
        self.ticks += passes
        self.frames += 1
        v = 0
        for t in range(TRACKS):
            s = 1.0 if (c >> t) & 1 else -1.0
            acc = 0.0
            for _ in range(passes):
                acc += s + (self.rng.gauss(0, self.sigma) if self.sigma else 0)
            if acc > 0:
                v |= 1 << t
        if ((v >> 9) & 1) != (pos & 1):
            self.clock_errors += 1
        return v

    def find_sync(self, pos, passes, limit=64):
        for off in range(limit):
            if (self.read_frame(pos + off, passes) & 0xFF) == SYNC[0] and \
               (self.read_frame(pos + off + 1, passes) & 0xFF) == SYNC[1]:
                return pos + off
        raise ReadError("no sync found")

    def read_block(self, start, passes):
        vals = [self.read_frame(start + i, passes) for i in range(5)]
        ln = ((vals[3] & 0xFF) << 8) | (vals[4] & 0xFF)
        total = 5 + ln + 5
        if ln > 4096 or start + total > len(self.cells):
            raise ReadError("implausible block length")
        vals += [self.read_frame(start + i, passes) for i in range(5, total)]
        data = [v & 0xFF for v in vals]
        par_ok = [(bin(d).count("1") + ((v >> 8) & 1)) & 1 == 1 for d, v in zip(data, vals)]
        lrc = 0
        for d in data[:-1]:
            lrc ^= d
        syn = lrc ^ data[-1]
        bad = [i for i, ok in enumerate(par_ok) if not ok]
        fixes = 0
        if len(bad) == 1:
            i = bad[0]
            if i == total - 1 or syn == 0:
                fixes = 1                          # parity cell / LRC byte hit; data fine
            elif syn & (syn - 1) == 0:
                data[i] ^= syn                     # frame i, bit = syndrome: flip it back
                fixes = 1
        body, crc = bytes(data[2:5 + ln]), bytes(data[5 + ln:9 + ln])
        if bytes(data[:2]) != SYNC or zlib.crc32(body).to_bytes(4, "big") != crc:
            raise ReadError("CRC mismatch")
        self.fixes += fixes
        return data[2], bytes(data[5:5 + ln]), start + total


def load_from_tape(head, max_passes):
    """Scan the tape, return {type: payload}.  Escalates passes per block."""
    pos, blocks, passes_used = 0, {}, {}
    while True:
        passes = 1
        while True:
            mark_frames = head.frames
            try:
                start = head.find_sync(pos, passes)
                typ, payload, end = head.read_block(start, passes)
                break
            except ReadError as e:
                head.wind += -(-(head.frames - mark_frames) // WIND)
                passes *= 2
                if passes > max_passes:
                    raise TapeError(f"block at frame ~{pos} unreadable: {e}")
        passes_used[typ] = passes
        pos = end
        if typ == T_END:
            return blocks, passes_used
        blocks[typ] = payload


# ================================================================ pipeline
def pad(msg):
    p = msg + b"\x80"
    p += b"\x00" * ((56 - len(p) % 64) % 64)
    return p + struct.pack(">Q", len(msg) * 8)


def bind_sha(circ):
    """Wrap the circuit read from tape as a pipeline stage function."""
    if sorted(circ.inputs) != sorted(SHA_IN) or \
       any(n not in [o for o, _ in circ.outputs] for n in SHA_OUT):
        raise CircuitError("circuit does not expose the SHA-256 round interface "
                           "(inputs a..h w0 w1 w9 w14 k; outputs na..nh nw)")
    in_pos = [SHA_IN.index(n) for n in circ.inputs]
    out_names = [o for o, _ in circ.outputs]
    out_pos = [out_names.index(n) for n in SHA_OUT]

    def stage(v, w, k):
        base = list(v) + [w[0], w[1], w[9], w[14], k]
        o = circ.run([base[j] for j in in_pos])
        return tuple(o[j] for j in out_pos[:8]), o[out_pos[8]]
    return stage


def run_pipeline(stage_fn, K, messages):
    """64 stages; stage i = the tape circuit with k = K[i mod len(K)]."""
    n = len(K)
    blocks = [[p[i:i + 64] for i in range(0, len(p), 64)] for p in map(pad, messages)]
    state = [list(IV) for _ in messages]
    nxt, busy = [0] * len(messages), [False] * len(messages)
    digests = [None] * len(messages)
    regs = [None] * 64
    tick = completed = rr = 0
    total = sum(len(b) for b in blocks)

    def advance(job, i):
        v, nw = stage_fn(job["v"], job["w"], K[i % n])
        return {**job, "v": v, "w": job["w"][1:] + [nw]}

    while completed < total:
        for i in range(63, 0, -1):
            regs[i] = advance(regs[i - 1], i) if regs[i - 1] else None
        regs[0] = None
        for off in range(len(messages)):
            m = (rr + off) % len(messages)
            if not busy[m] and nxt[m] < len(blocks[m]):
                w = list(struct.unpack(">16I", blocks[m][nxt[m]]))
                regs[0] = advance({"m": m, "in": tuple(state[m]), "v": tuple(state[m]), "w": w}, 0)
                busy[m] = True
                nxt[m] += 1
                rr = (m + 1) % len(messages)
                break
        if regs[63]:
            j = regs[63]
            m = j["m"]
            state[m] = [(x + y) & MASK for x, y in zip(j["in"], j["v"])]
            busy[m] = False
            completed += 1
            if nxt[m] == len(blocks[m]):
                digests[m] = b"".join(struct.pack(">I", x) for x in state[m]).hex()
            regs[63] = None
        tick += 1
    return digests, tick, total


# ================================================================ commands
def cmd_write(a):
    asm = open(a.asm).read() if a.asm else SHA_ROUND_ASM
    circ = assemble(asm)
    consts = struct.pack(">H", len(K_TABLE)) + b"".join(struct.pack(">I", k) for k in K_TABLE)
    label = (f"MAGTAPE-1 circuit={'custom' if a.asm else 'sha256-round'} "
             f"gates={len(circ.gates)} K-modulus={len(K_TABLE)}").encode()
    payloads = [(T_LABEL, label), (T_CIRCUIT, circ.encode()), (T_END, b"")]
    if not a.no_constants:
        payloads.insert(2, (T_CONST, consts))
    need = sum(GAP + len(block_bytes(t, p)) for t, p in payloads) + 64
    frames = a.frames or need
    if frames < need:
        sys.exit(f"tape too short: need {need} frames")
    drive = WriteDrive(frames, a.write_drive, a.coercivity_sigma, a.seed)
    for t, p in payloads:
        drive.write_block(t, p)
    save_tape(a.tape, drive.cells)
    print("=== TAPE WRITE ===")
    print(f"tape                  : {a.tape} ({frames} frames x {TRACKS} tracks)")
    print(f"write field / Hc      : {a.write_drive} vs N(1.0, {a.coercivity_sigma})")
    for t, p in payloads:
        print(f"  wrote {TYPE_NAMES[t]:<9} {len(p):>5} payload bytes")
    print(f"circuit               : {len(circ.inputs)} inputs, {len(circ.gates)} gates, "
          f"{len(circ.outputs)} outputs")
    print(f"cells that resisted   : {drive.failed_cells} (first attempt)")
    print(f"block rewrites        : {drive.rewrites} (write-verify)")
    print(f"write ticks           : {drive.ticks}")
    return 0


def ideal_scan(path):
    cells = load_tape(path)
    head = Head(cells, 0.0, 0)
    blocks, _ = load_from_tape(head, 1)
    return cells, blocks


def flux_row(word):
    order = [7, 6, 5, 4, 3, 2, 1, 0, 8, 9]       # D7..D0 P CLK
    return " ".join("+" if (word >> t) & 1 else "-" for t in order)


def cmd_dump(a):
    cells, blocks = ideal_scan(a.tape)
    print(f"=== TAPE {a.tape}: {len(cells)} frames x {TRACKS} tracks ===")
    head, pos = Head(cells, 0.0, 0), 0
    while True:
        start = head.find_sync(pos, 1)
        typ, payload, end = head.read_block(start, 1)
        print(f"frames {start:>5}-{end - 1:<5} {TYPE_NAMES.get(typ, hex(typ)):<9} "
              f"{len(payload):>5} bytes  crc ok")
        if typ == T_CIRCUIT and not getattr(a, "_shown", False):
            print("   flux (+/-) of the first frames:   D7 D6 D5 D4 D3 D2 D1 D0  P CLK")
            for i in range(5):
                print(f"   frame {start + i:>5}  byte {cells[start + i] & 0xFF:02x}      "
                      f"{flux_row(cells[start + i])}")
            a._shown = True
        pos = end
        if typ == T_END:
            break
    if T_LABEL in blocks:
        print("label                 :", blocks[T_LABEL].decode())
    if T_CIRCUIT in blocks:
        c = Circuit.decode(blocks[T_CIRCUIT])
        print(f"circuit               : {len(c.inputs)} inputs, {len(c.gates)} gates, "
              f"{len(c.outputs)} outputs")
        print("gate census           :", ", ".join(f"{k} x{v}" for k, v in sorted(c.census().items())))
        if a.disasm:
            print("\n" + c.disasm())
    if T_CONST in blocks:
        n = struct.unpack_from(">H", blocks[T_CONST])[0]
        k0 = struct.unpack_from(">I", blocks[T_CONST], 2)[0]
        print(f"constants             : {n} words (modulus {n}), table[0] = 0x{k0:08x}")
    return 0


def cmd_truth(a):
    _, blocks = ideal_scan(a.tape)
    c = Circuit.decode(blocks[T_CIRCUIT])
    if c.n_in > 4:
        print(f"{c.n_in} inputs: too many for a truth table (limit 4). "
              "Use `dump --disasm` or `run`.")
        return 1
    print("  ".join(c.inputs), "|", "  ".join(n for n, _ in c.outputs))
    for combo in itertools.product([0, 1], repeat=c.n_in):
        o = c.run(list(combo))
        print("  ".join(f"{x:>{len(n)}}" for x, n in zip(combo, c.inputs)), "|",
              "  ".join(f"{v & 1:>{len(n)}}" for v, (n, _) in zip(o, c.outputs)))
    return 0


def cmd_run(a):
    cells = load_tape(a.tape)
    if a.damage:
        r = random.Random(a.seed + 999)
        for _ in range(a.damage):
            cells[r.randrange(len(cells))] ^= 1 << r.randrange(9)   # permanent flux damage
    heads = [Head(cells, a.noise, a.seed + i) for i in range(a.lanes)]
    lanes = []
    for i, h in enumerate(heads):
        try:
            blocks, passes = load_from_tape(h, a.max_passes)
            circ = Circuit.decode(blocks[T_CIRCUIT])
            n = struct.unpack_from(">H", blocks[T_CONST])[0]
            K = list(struct.unpack_from(">%dI" % n, blocks[T_CONST], 2))
            stage = bind_sha(circ)
            lanes.append({"i": i, "ok": True, "h": h, "circ": circ, "K": K,
                          "stage": stage, "passes": passes, "blocks": blocks})
        except (TapeError, CircuitError, KeyError, struct.error) as e:
            lanes.append({"i": i, "ok": False, "h": h, "err": str(e)})
    live = [l for l in lanes if l["ok"]]

    print(f"=== TAPE READ ({a.lanes} read heads on one transport) ===")
    print(f"tape                  : {a.tape}, {len(cells)} frames x {TRACKS} tracks")
    print(f"read noise sigma      : {a.noise} (signal is +-1)   damaged cells: {a.damage}")
    print("head  status  max-passes  ecc-fixes  clock-errs  ticks")
    for l in lanes:
        h = l["h"]
        if l["ok"]:
            print(f"{l['i']:>4}  OK      {max(l['passes'].values()):>10}  {h.fixes:>9}  "
                  f"{h.clock_errors:>10}  {h.ticks + h.wind:>5}")
        else:
            print(f"{l['i']:>4}  DEAD    {l['err']}")
    if not live:
        print("TAPE READ FAILED: no head could load the circuit")
        return 2
    same = all(l["circ"].encode() == live[0]["circ"].encode() and l["K"] == live[0]["K"]
               for l in live)
    c = live[0]["circ"]
    load_ticks = max(l["h"].ticks + l["h"].wind for l in live)   # one shared transport
    print(f"live heads            : {len(live)}/{a.lanes}")
    print(f"circuits+constants identical in all live heads: {same}")
    print(f"circuit loaded        : {len(c.gates)} gates ({', '.join(f'{k} x{v}' for k, v in sorted(c.census().items()))})")
    print(f"counter & modulus     : stage i fetches K[i mod {len(live[0]['K'])}]")
    print(f"tape load ticks       : {load_ticks}")

    label = live[0]["blocks"].get(T_LABEL, b"").decode()
    circ_bytes = live[0]["blocks"][T_CIRCUIT]
    if a.nonces:
        allmsgs = [f"{a.prefix}{n}".encode() for n in range(a.nonces)]
        work = [allmsgs[j::len(live)] for j in range(len(live))]
        wl = f"{a.nonces} independent single-block messages spread over lanes"
    else:
        work = [[circ_bytes] for _ in live]
        wl = f"the circuit block read off the tape ({len(circ_bytes)} bytes), hashed in every lane"

    print(f"\n=== SOLVER LANES (64 stages = the tape circuit, {len(live)} lane(s)) ===")
    print(f"workload              : {wl}")
    print("lane  messages  blocks  ticks  verified")
    tot_blocks = tot_bad = tot_msgs = max_ticks = 0
    first = None
    for l, msgs in zip(live, work):
        if not msgs:
            continue
        digests, ticks, nblocks = run_pipeline(l["stage"], l["K"], msgs)
        bad = sum(d != hashlib.sha256(m).hexdigest() for d, m in zip(digests, msgs))
        print(f"{l['i']:>4}  {len(msgs):>8}  {nblocks:>6}  {ticks:>5}  {len(msgs) - bad}/{len(msgs)}")
        tot_blocks += nblocks; tot_bad += bad; tot_msgs += len(msgs)
        max_ticks = max(max_ticks, ticks)
        first = first or digests[0]

    rate = tot_blocks / max_ticks
    eff = tot_blocks / (load_ticks + max_ticks)
    print("\n=== TOTAL (tape-bound logical clock: 1 tick = 1 clock-track pulse) ===")
    print(f"tape load ticks       : {load_ticks}")
    print(f"compute ticks         : {max_ticks}")
    print(f"total ticks           : {load_ticks + max_ticks}")
    print(f"compute throughput    : {rate:.4f} blocks/tick (iterative would be {1 / 64:.4f})")
    print(f"effective incl. load  : {eff:.4f} blocks/tick")
    print(f"at {a.clock / 1e6:g} MHz frame rate  : {rate * a.clock / 1e6:.3f} MH/s compute, "
          f"{eff * a.clock / 1e6:.3f} MH/s effective")
    print(f"digests verified      : {tot_msgs - tot_bad}/{tot_msgs} match hashlib")
    print("first digest          :", first)
    return 1 if tot_bad else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    w = sub.add_parser("write", help="format a tape and write circuit + constants")
    w.add_argument("--tape", required=True)
    w.add_argument("--asm", help="assembly file for a custom circuit (default: SHA-256 round)")
    w.add_argument("--no-constants", action="store_true")
    w.add_argument("--frames", type=int, default=0, help="tape length (default: just enough)")
    w.add_argument("--write-drive", type=float, default=1.5, help="write field strength")
    w.add_argument("--coercivity-sigma", type=float, default=0.0, help="spread of cell Hc around 1.0")
    w.add_argument("--seed", type=int, default=1)
    w.set_defaults(fn=cmd_write)

    d = sub.add_parser("dump", help="list blocks, flux, and the circuit on a tape")
    d.add_argument("--tape", required=True)
    d.add_argument("--disasm", action="store_true")
    d.set_defaults(fn=cmd_dump)

    t = sub.add_parser("truth", help="read the circuit from tape and print its truth table")
    t.add_argument("--tape", required=True)
    t.set_defaults(fn=cmd_truth)

    r = sub.add_parser("run", help="load the circuit from tape and run pipelined SHA-256")
    r.add_argument("--tape", required=True)
    r.add_argument("--noise", type=float, default=0.0, help="read-head noise sigma (signal is +-1)")
    r.add_argument("--damage", type=int, default=0, help="permanently flip this many random cells")
    r.add_argument("--max-passes", type=int, default=64)
    r.add_argument("--lanes", type=int, default=1, help="read heads / solver pipelines")
    r.add_argument("--nonces", type=int, default=0)
    r.add_argument("--prefix", default="SHA256-")
    r.add_argument("--clock", type=float, default=16, help="tape frame rate, Hz")
    r.add_argument("--seed", type=int, default=1)
    r.set_defaults(fn=cmd_run)

    args = ap.parse_args()
    try:
        return args.fn(args)
    except (TapeError, CircuitError) as e:
        print("ERROR:", e)
        return 2


if __name__ == "__main__":
    sys.exit(main())
