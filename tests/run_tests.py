#!/usr/bin/env python3
"""Tests for the Lean PNG chunk parser and printer.

Four parts.

1. Real PNG files built with Python zlib: an IHDR chunk (the
   width, height, bit depth, and colour type are stated per file
   below), IDAT chunks holding zlib-compressed scanlines, and
   IEND. The Lean tool must accept each file and reprint it byte
   for byte. One file splits its compressed data across two IDAT
   chunks. The IDAT bytes are opaque to the chunk layer; what is
   checked is framing and CRC.

2. Hand-built chunk cases through the same path: a tEXt chunk,
   unknown ancillary chunk types, and the rejected shapes (a bad
   signature, a bad CRC on each kind of chunk, a length that
   overruns the file, a length of 2^31, a type with a digit in it,
   IHDR not first, IHDR with the wrong length, IEND missing, an
   IEND that carries data, bytes after IEND, an empty file).

3. A differential run against a strict Python oracle written in
   this harness from the plan rules, using zlib.crc32 for the CRC:
   random chunk lists written by a Python writer, which the Lean
   tool must accept and reprint byte for byte; mutations of a
   small valid file (a single byte flip at every position, and a
   truncation at every length); and mutations of a larger file at
   sampled positions across the signature, length, type, data,
   and CRC fields. The oracle settles accept or reject, and an
   accepted mutation must reprint to the oracle's reading.

4. Malformed request lines must be answered `error`.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is driven one batch process per chunk of requests, input
written and closed, output drained until the process exits. It
builds the executable first, writes tests/TEST-RESULTS.md, and
exits non-zero if any check fails. It needs Python 3.11 or later.
"""

import argparse
import random
import struct
import subprocess
import sys
import threading
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "png"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 900
BUILD_TIMEOUT = 3600
CHUNK = 200

SEED_DEFAULT = 20261026
SIG = bytes([137, 80, 78, 71, 13, 10, 26, 10])


def codes(data):
    return ",".join(str(b) for b in data)


def request(data):
    return "parse " + codes(data)


def run_tool(lines, timeout=TIMEOUT):
    """Run the tool on a batch of request lines.

    Returns (answers, problem). No right answer is longer than its
    request plus a small constant, so output past twice the input
    plus 64 bytes a line is stopped, not read until memory runs
    out.
    """
    data = "".join(line + "\n" for line in lines)
    raw = data.encode("utf-8")
    limit = 2 * len(raw) + 64 * (len(lines) + 1)
    try:
        proc = subprocess.Popen(
            [str(EXE)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as e:
        return [], f"could not run {EXE}: {e.strerror or e}"
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf, cap):
        while chunk := stream.read1(1 << 16):
            buf += chunk
            if len(buf) > cap:
                proc.kill()
                return

    threads = [
        threading.Thread(target=feed),
        threading.Thread(target=drain, args=(proc.stdout, out, limit)),
        threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20)),
    ]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if len(out) > limit:
        problem = problem or f"more than {limit} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(
            bytes(err).decode("utf-8", "backslashreplace").splitlines()[-3:]
        )
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    if len(answers) != len(lines) and not problem:
        problem = f"tool gave {len(answers)} answers for {len(lines)} requests"
    return answers, problem


def ask_all(lines):
    """Chunked run_tool. Answers align with lines, or None entries."""
    answers = []
    problems = []
    for i in range(0, len(lines), CHUNK):
        chunk = lines[i : i + CHUNK]
        ans, problem = run_tool(chunk)
        if problem:
            problems.append(problem)
            ans = ans + [None] * (len(chunk) - len(ans))
        answers += ans
    return answers, problems


# ---------------------------------------------------------------- the
# PNG builders and the strict oracle, written from the plan rules.


def make_chunk(typ, data):
    return (
        struct.pack(">I", len(data))
        + typ
        + data
        + struct.pack(">I", zlib.crc32(typ + data) & 0xFFFFFFFF)
    )


def ihdr_data(width, height, bit_depth, colour_type):
    return struct.pack(">IIBBBBB", width, height, bit_depth, colour_type, 0, 0, 0)


def is_letter(b):
    return 65 <= b <= 90 or 97 <= b <= 122


def oracle_parse(data):
    """The strict reading of the plan rules. A chunk list of
    (type, data) pairs, or None when the file is rejected."""
    if len(data) < 8 or data[:8] != SIG:
        return None
    i = 8
    chunks = []
    while True:
        if i + 4 > len(data):
            return None
        ln = int.from_bytes(data[i : i + 4], "big")
        if ln >= 2**31:
            return None
        if i + 8 > len(data):
            return None
        typ = data[i + 4 : i + 8]
        if not all(is_letter(b) for b in typ):
            return None
        if i + 8 + ln + 4 > len(data):
            return None
        payload = data[i + 8 : i + 8 + ln]
        crc = int.from_bytes(data[i + 8 + ln : i + 12 + ln], "big")
        if zlib.crc32(typ + payload) & 0xFFFFFFFF != crc:
            return None
        chunks.append((typ, payload))
        i += 12 + ln
        if typ == b"IEND" and ln == 0:
            if i != len(data):
                return None
            break
    if chunks[0][0] != b"IHDR" or len(chunks[0][1]) != 13:
        return None
    return chunks


def oracle_print(chunks):
    out = bytearray(SIG)
    for typ, payload in chunks:
        out += make_chunk(typ, payload)
    return bytes(out)


def oracle_answer(data):
    parsed = oracle_parse(data)
    if parsed is None:
        return "none"
    return "ok:" + codes(oracle_print(parsed))


# ---------------------------------------------------------------- real
# PNG files.


def real_png(width, height, colour_type, rng, split_idat=False, extra=()):
    bpp = {0: 1, 2: 3, 6: 4}[colour_type]
    raw = bytearray()
    for _ in range(height):
        raw.append(0)
        raw += bytes(rng.randrange(0, 256) for _ in range(width * bpp))
    comp = zlib.compress(bytes(raw))
    parts = [SIG, make_chunk(b"IHDR", ihdr_data(width, height, 8, colour_type))]
    for typ, data in extra:
        parts.append(make_chunk(typ, data))
    if split_idat:
        cut = max(1, len(comp) // 2)
        parts.append(make_chunk(b"IDAT", comp[:cut]))
        parts.append(make_chunk(b"IDAT", comp[cut:]))
    else:
        parts.append(make_chunk(b"IDAT", comp))
    parts.append(make_chunk(b"IEND", b""))
    return b"".join(parts)


def run_real(seed):
    rng = random.Random(seed)
    files = [
        ("1x1, bit depth 8, colour type 2 (RGB)", real_png(1, 1, 2, rng)),
        ("4x3, bit depth 8, colour type 6 (RGBA)", real_png(4, 3, 6, rng)),
        (
            "16x16, bit depth 8, colour type 0 (greyscale), IDAT split in two",
            real_png(16, 16, 0, rng, split_idat=True),
        ),
        (
            "7x5, bit depth 8, colour type 2 (RGB), a tEXt chunk before IDAT",
            real_png(7, 5, 2, rng, extra=[(b"tEXt", b"Title\x00A small test")]),
        ),
    ]
    lines = []
    failures = []
    answers, problems = ask_all([request(data) for _, data in files])
    for problem in problems:
        failures.append(f"real files: tool problem: {problem}")
    agree = 0
    for (name, data), ans in zip(files, answers):
        want = "ok:" + codes(data)
        if ans == want:
            agree += 1
        else:
            failures.append(f"real file {name}: want byte for byte reprint, got {ans!r}")
    lines.append(
        f"Real PNG files (zlib built): {agree} of {len(files)} accepted "
        "and reprinted byte for byte"
    )
    for name, data in files:
        lines.append(f"Real PNG file: {name}, {len(data)} bytes")
    return lines, failures


# ---------------------------------------------------------------- hand
# built cases.


def corrupt_crc(chunk_bytes):
    """A chunk with its last CRC byte flipped."""
    b = bytearray(chunk_bytes)
    b[-1] ^= 0xFF
    return bytes(b)


def hand_cases():
    ihdr = make_chunk(b"IHDR", ihdr_data(1, 1, 8, 2))
    idat = make_chunk(b"IDAT", zlib.compress(b"\x00\x01\x02\x03"))
    iend = make_chunk(b"IEND", b"")
    good = SIG + ihdr + idat + iend
    text = make_chunk(b"tEXt", b"Comment\x00Hello, chunk layer")
    cases = [
        # (name, file bytes, accepted?)
        ("a tEXt chunk between IHDR and IDAT", SIG + ihdr + text + idat + iend, True),
        ("an unknown ancillary chunk type, abCD", SIG + ihdr + make_chunk(b"abCD", b"\x00\xff\x10") + idat + iend, True),
        ("an unknown chunk with no data, zzZZ", SIG + ihdr + make_chunk(b"zzZZ", b"") + idat + iend, True),
        ("an IEND chunk with data, mid file, is ordinary", SIG + ihdr + make_chunk(b"IEND", b"\x01\x02") + idat + iend, True),
        ("a bad signature byte", bytes([good[0] ^ 0xFF]) + good[1:], False),
        ("a signature that is only seven bytes", SIG[:7], False),
        ("a bad CRC on IHDR", SIG + corrupt_crc(ihdr) + idat + iend, False),
        ("a bad CRC on IDAT", SIG + ihdr + corrupt_crc(idat) + iend, False),
        ("a bad CRC on IEND", SIG + ihdr + idat + corrupt_crc(iend), False),
        ("a bad CRC on a tEXt chunk", SIG + ihdr + corrupt_crc(text) + idat + iend, False),
        (
            "a length that overruns the file",
            SIG + ihdr + struct.pack(">I", 500) + b"IDAT" + b"short" + b"\x00\x00\x00\x00" + iend,
            False,
        ),
        (
            "a length of 2^31",
            SIG + ihdr + struct.pack(">I", 2**31) + b"IDAT" + iend,
            False,
        ),
        (
            "a type with a digit in it, CRC recomputed",
            SIG + ihdr + make_chunk(b"ID4T", zlib.compress(b"\x00\x01\x02\x03")) + iend,
            False,
        ),
        ("IHDR not first", SIG + idat + ihdr + iend, False),
        (
            "IHDR with 12 data bytes, CRC recomputed",
            SIG + make_chunk(b"IHDR", ihdr_data(1, 1, 8, 2)[:12]) + idat + iend,
            False,
        ),
        ("IEND missing", SIG + ihdr + idat, False),
        ("only the signature", SIG, False),
        ("an IEND that carries data, at the end", SIG + ihdr + idat + make_chunk(b"IEND", b"\x00"), False),
        ("one byte after IEND", good + b"\x00", False),
        ("a whole chunk after IEND", good + text, False),
        ("an empty file", b"", False),
        ("three bytes only", b"\x89PN", False),
    ]
    return cases


def run_hand():
    cases = hand_cases()
    lines = []
    failures = []
    answers, problems = ask_all([request(data) for _, data, _ in cases])
    for problem in problems:
        failures.append(f"hand cases: tool problem: {problem}")
    agree = 0
    for (name, data, accepted), ans in zip(cases, answers):
        want = ("ok:" + codes(data)) if accepted else "none"
        if ans == want:
            agree += 1
        else:
            failures.append(f"hand case {name}: want {want[:60]!r}, got {ans!r}")
    lines.append(f"Hand-built cases: {agree} of {len(cases)} agreements")
    return lines, failures


# ---------------------------------------------------------------- the
# differential runs.

LETTERS = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"


def rand_chunk_list(rng):
    chunks = [(b"IHDR", bytes(rng.randrange(0, 256) for _ in range(13)))]
    for _ in range(rng.randrange(0, 5)):
        typ = bytes(rng.choice(LETTERS) for _ in range(4))
        size = rng.choice([0, 1, 3, 17, 40, 120])
        data = bytes(rng.randrange(0, 256) for _ in range(size))
        if typ == b"IEND" and not data:
            data = b"\x00"
        chunks.append((typ, data))
    chunks.append((b"IEND", b""))
    return chunks


def writer(chunks):
    out = bytearray(SIG)
    for typ, data in chunks:
        out += make_chunk(typ, data)
    return bytes(out)


def run_random(seed, count):
    rng = random.Random(seed + 2)
    docs = [writer(rand_chunk_list(rng)) for _ in range(count)]
    lines = []
    failures = []
    answers, problems = ask_all([request(d) for d in docs])
    for problem in problems:
        failures.append(f"random lists: tool problem: {problem}")
    agree = 0
    for data, ans in zip(docs, answers):
        want = "ok:" + codes(data)
        if ans == want:
            agree += 1
        else:
            failures.append(f"random list: want byte for byte reprint, got {ans!r}")
    lines.append(
        f"Random chunk lists (Python writer, zlib.crc32): {len(docs)} documents, "
        f"{agree} of {len(docs)} accepted and reprinted byte for byte"
    )
    return lines, failures


def mutations_of(data, flip_positions, truncations=True):
    out = []
    if truncations:
        out += [data[:k] for k in range(len(data))]
    for pos in flip_positions:
        b = bytearray(data)
        b[pos] ^= 0xFF
        out.append(bytes(b))
    return out


def run_mutations(seed):
    lines = []
    failures = []
    rng = random.Random(seed + 3)
    small = real_png(3, 2, 2, rng)
    big = real_png(16, 16, 6, rng, extra=[(b"tEXt", b"Note\x00mutation target")])
    small_muts = mutations_of(small, range(len(small)))
    big_positions = sorted(rng.sample(range(len(big)), 300))
    big_muts = mutations_of(big, big_positions, truncations=False)
    inputs = small_muts + big_muts
    wants = [oracle_answer(d) for d in inputs]
    answers, problems = ask_all([request(d) for d in inputs])
    for problem in problems:
        failures.append(f"mutations: tool problem: {problem}")
    agree_small = 0
    for want, ans in zip(wants[: len(small_muts)], answers[: len(small_muts)]):
        if ans == want:
            agree_small += 1
        else:
            failures.append(f"small mutation: want {want[:60]!r}, got {ans!r}")
    agree_big = 0
    for want, ans in zip(wants[len(small_muts) :], answers[len(small_muts) :]):
        if ans == want:
            agree_big += 1
        else:
            failures.append(f"big mutation: want {want[:60]!r}, got {ans!r}")
    lines.append(
        f"Mutations of a {len(small)} byte file (every truncation and every "
        f"single byte flip): {len(small_muts)} inputs, {agree_small} agreements"
    )
    lines.append(
        f"Mutations of a {len(big)} byte file (300 sampled single byte flips): "
        f"{len(big_muts)} inputs, {agree_big} agreements"
    )
    return lines, failures


MALFORMED = [
    "bogus 1",
    "parse 12a",
    "parse 256",
    "parse 999999999",
    "parse 1,,2",
    "parse  97",
    "parse 97 ",
    "PARSE 97",
    "parse -1",
    "parse 0x41",
    "parse 97 98",
    "parse 1.5",
]


def run_malformed():
    lines = []
    failures = []
    answers, problems = ask_all(MALFORMED)
    for problem in problems:
        failures.append(f"malformed: tool problem: {problem}")
    bad_ok = 0
    for line, ans in zip(MALFORMED, answers):
        if ans == "error":
            bad_ok += 1
        else:
            failures.append(f"malformed {line!r}: want error, got {ans!r}")
    lines.append(f"Malformed requests answered error: {bad_ok} of {len(MALFORMED)}")
    # A request with no codes at all is the empty file, which the
    # rules reject: the answer is none, not ok: and not error.
    none_ok = 0
    answers, _ = ask_all(["parse", "parse "])
    for ans in answers:
        if ans == "none":
            none_ok += 1
        else:
            failures.append(f"empty request: want none, got {ans!r}")
    lines.append(f"Requests with no codes answered none: {none_ok} of 2")
    return lines, failures


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=SEED_DEFAULT)
    ap.add_argument("--count", type=int, default=400)
    args = ap.parse_args()

    build = subprocess.run(
        ["lake", "build"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=BUILD_TIMEOUT,
    )
    if build.returncode != 0:
        print(build.stdout)
        print(build.stderr)
        print("lake build failed")
        return 1

    all_lines = []
    all_failures = []
    for part in (
        run_real(args.seed),
        run_hand(),
        run_random(args.seed, args.count),
        run_mutations(args.seed),
        run_malformed(),
    ):
        lines, failures = part
        all_lines += lines
        all_failures += failures

    lean_version = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    ).stdout.strip()

    out = ["# Test results", ""]
    out.append("Written by `tests/run_tests.py`. Rerun it to check these numbers.")
    out.append("")
    out.append(
        f"- Oracle: Python {sys.version.split()[0]} `zlib` (crc32 and compress), "
        "plus a strict reading of the plan rules written in the harness"
    )
    out.append(f"- Lean: {lean_version}")
    out.append(f"- Seed: {args.seed}")
    for line in all_lines:
        out.append(f"- {line}")
    out.append("- Named differences: none")
    out.append(f"- Failures: {len(all_failures)}")
    for failure in all_failures[:50]:
        out.append(f"- FAILURE: {failure}")
    RESULTS.write_text("\n".join(out) + "\n", encoding="utf-8")
    print("\n".join(out))
    return 0 if not all_failures else 1


if __name__ == "__main__":
    sys.exit(main())
