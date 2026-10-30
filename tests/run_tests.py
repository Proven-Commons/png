#!/usr/bin/env python3
"""Tests for the Lean PNG chunk parser and printer.

Seven parts. Parts 1 to 4 are the slice 1 suite, unchanged.
Part 5 is slice 2: the IHDR header read through the `header`
request. Part 6 checks the accepted inputs stated in
Png/Spec.lean. Part 7 compares the header read with libpng, where libpng is
installed.

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

5. The header read (slice 2). The same real files are asked
   through `header`, and their decoded fields are checked. Hand
   built headers cover every colour type with each depth the
   PNG specification allows it. An enumeration crosses colour
   types 0 to 12 and 255 with depths 0, 1, 2, 3, 4, 5, 8, 16,
   and 255, settled by the allowed table written in this
   harness. Mutations (a zero width, a zero height, a width of
   2^31, a height of 2^31, a width of 2^32 - 1, a height of
   2^32 - 1, a compression byte of 1, a filter byte of 1, an
   interlace byte of 2, a first chunk of length 12) must be
   rejected, and a width or height of 2^31 - 1 accepted. A
   second IHDR chunk must be rejected by `header` and read by
   `parse`; an IEND chunk with data is an ordinary chunk at both
   layers. Random well formed headers are built into whole
   files and checked through `header` for their fields and
   through `parse` for a byte for byte reprint.

6. The accepted inputs stated in Png/Spec.lean
   (Png.Spec.reads_real_file_header, a whole file, and
   Png.Spec.reads_header_1920x1080, 13 header bytes, wrapped in
   a file with an all zero image), read from that file. The
   stated header must match the harness's own big endian
   reading of the bytes, the image data must inflate to the
   size that header gives, the tool's `header` answer must be
   the stated header, and so must libpng's, decoding the whole
   file, where libpng is installed.

7. The libpng comparison. tests/libpng_header.c is built
   against the system libpng (skipped, and said so, when there
   is no C compiler or no libpng). Each file is read by libpng
   and by `header`, and the answers must agree field for field,
   or both refuse, except in the named differences listed in
   LIBPNG_NAMED. The files: the real files, the colour type and
   depth grid, every allowed pair with and without Adam7 at
   three sizes (with an all zero image libpng decodes), the
   header rule cases, 150 random well formed headers, and the
   chunk order cases.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is driven one batch process per chunk of requests, input
written and closed, output drained until the process exits. It
builds the executable first, writes tests/TEST-RESULTS.md, and
exits non-zero if any check fails. It needs Python 3.11 or later.
"""

import argparse
import json
import random
import re
import shutil
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


ASKED = [0]


def ask_all(lines):
    """Chunked run_tool. Answers align with lines, or None entries.
    Every request counts toward the record's Inputs."""
    ASKED[0] += len(lines)
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


def real_files(seed):
    rng = random.Random(seed)
    return [
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


def run_real(seed):
    files = real_files(seed)
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


# ---------------------------------------------------------------- the
# header read (slice 2). The strict oracle for this part is the
# allowed table below, written from the PNG specification: a
# colour type allows exactly these bit depths.


ALLOWED = {0: [1, 2, 4, 8, 16], 2: [8, 16], 3: [1, 2, 4, 8], 4: [8, 16], 6: [8, 16]}


def ihdr_full(width, height, bit_depth, colour_type, comp=0, filt=0, interlace=0):
    return struct.pack(
        ">IIBBBBB", width, height, bit_depth, colour_type, comp, filt, interlace
    )


def header_request(data):
    return "header " + codes(data)


def header_line(width, height, bit_depth, colour_type, interlace):
    text = f"{width}x{height} d{bit_depth} t{colour_type} i{interlace}"
    return "ok:" + codes(text.encode("ascii"))


def header_file(ihdr_bytes, idat_data=b"\x00\x01\x02\x03"):
    return (
        SIG
        + make_chunk(b"IHDR", ihdr_bytes)
        + make_chunk(b"IDAT", zlib.compress(idat_data))
        + make_chunk(b"IEND", b"")
    )


def run_real_headers(seed):
    """The real files of part 1, asked through `header`. Their
    (width, height, bit depth, colour type, interlace) are known
    from how they were built."""
    known = [(1, 1, 8, 2, 0), (4, 3, 8, 6, 0), (16, 16, 8, 0, 0), (7, 5, 8, 2, 0)]
    files = real_files(seed)
    lines = []
    failures = []
    answers, problems = ask_all([header_request(data) for _, data in files])
    for problem in problems:
        failures.append(f"real headers: tool problem: {problem}")
    agree = 0
    for (name, _), fields, ans in zip(files, known, answers):
        want = header_line(*fields)
        if ans == want:
            agree += 1
        else:
            failures.append(f"real header {name}: want {want!r}, got {ans!r}")
    lines.append(
        f"Real PNG files through `header`: {agree} of {len(files)} decoded "
        "to the fields they were built with"
    )
    return lines, failures


def run_header_types():
    """One file per allowed (colour type, bit depth) pair, the
    interlace byte alternating, each checked for its fields."""
    cases = []
    for ctype in sorted(ALLOWED):
        for depth in ALLOWED[ctype]:
            interlace = (len(cases) % 2)
            cases.append((3, 2, depth, ctype, interlace))
    lines = []
    failures = []
    answers, problems = ask_all(
        [
            header_request(
                header_file(ihdr_full(w, h, d, t, interlace=i))
            )
            for (w, h, d, t, i) in cases
        ]
    )
    for problem in problems:
        failures.append(f"header types: tool problem: {problem}")
    agree = 0
    for fields, ans in zip(cases, answers):
        want = header_line(*fields)
        if ans == want:
            agree += 1
        else:
            failures.append(f"header type {fields}: want {want!r}, got {ans!r}")
    lines.append(
        f"Hand-built headers, every colour type and allowed depth: "
        f"{agree} of {len(cases)} accepted with their fields"
    )
    return lines, failures


def run_header_grid():
    """The enumeration: colour types 0 to 12 and 255, against
    depths 0, 1, 2, 3, 4, 5, 8, 16, 255. The table settles each."""
    types = list(range(13)) + [255]
    depths = [0, 1, 2, 3, 4, 5, 8, 16, 255]
    cases = [(t, d) for t in types for d in depths]
    lines = []
    failures = []
    answers, problems = ask_all(
        [
            header_request(header_file(ihdr_full(2, 2, d, t)))
            for t, d in cases
        ]
    )
    for problem in problems:
        failures.append(f"header grid: tool problem: {problem}")
    agree = 0
    for (t, d), ans in zip(cases, answers):
        want = header_line(2, 2, d, t, 0) if d in ALLOWED.get(t, []) else "none"
        if ans == want:
            agree += 1
        else:
            failures.append(f"header grid type {t} depth {d}: want {want!r}, got {ans!r}")
    lines.append(
        f"Header enumeration, {len(types)} colour types by {len(depths)} "
        f"depths against the allowed table: {agree} of {len(cases)} agreements"
    )
    return lines, failures


def run_header_mutations():
    """Each of these files is one change away from a valid one,
    and each must be rejected by the header read. The CRCs are
    recomputed, so the rejection is for the header rule itself
    (except the length 12 case, which the chunk layer rejects)."""
    good = ihdr_full(4, 3, 8, 6)
    cases = [
        ("a width of zero", header_file(ihdr_full(0, 3, 8, 6))),
        ("a height of zero", header_file(ihdr_full(4, 0, 8, 6))),
        ("a width of 2^31", header_file(ihdr_full(2**31, 3, 8, 6))),
        ("a height of 2^31", header_file(ihdr_full(4, 2**31, 8, 6))),
        ("a width of 2^32 - 1", header_file(ihdr_full(2**32 - 1, 3, 8, 6))),
        ("a height of 2^32 - 1", header_file(ihdr_full(4, 2**32 - 1, 8, 6))),
        ("a compression byte of 1", header_file(ihdr_full(4, 3, 8, 6, comp=1))),
        ("a filter byte of 1", header_file(ihdr_full(4, 3, 8, 6, filt=1))),
        ("an interlace byte of 2", header_file(ihdr_full(4, 3, 8, 6, interlace=2))),
        (
            "a first chunk of length 12",
            SIG
            + make_chunk(b"IHDR", good[:12])
            + make_chunk(b"IDAT", zlib.compress(b"\x00\x01\x02\x03"))
            + make_chunk(b"IEND", b""),
        ),
    ]
    lines = []
    failures = []
    answers, problems = ask_all([header_request(data) for _, data in cases])
    for problem in problems:
        failures.append(f"header mutations: tool problem: {problem}")
    agree = 0
    for (name, _), ans in zip(cases, answers):
        if ans == "none":
            agree += 1
        else:
            failures.append(f"header mutation {name}: want none, got {ans!r}")
    lines.append(f"Header mutations rejected: {agree} of {len(cases)}")
    return lines, failures


def run_header_chunk_order():
    """Chunk order cases the file level read settles. A second
    IHDR chunk, right after the first or after IDAT, is refused
    by `header` (the PNG specification allows one IHDR chunk),
    while `parse`, the chunk layer, still reads it as an ordinary
    chunk. An IEND chunk that carries data is an ordinary chunk at
    both layers: before IDAT, with a real IEND at the end, the
    file reads; as the last chunk, with no real IEND after it,
    the file is refused."""
    ihdr1 = make_chunk(b"IHDR", ihdr_full(1, 1, 8, 2))
    ihdr2 = make_chunk(b"IHDR", ihdr_full(2, 2, 8, 2))
    idat = make_chunk(b"IDAT", zlib.compress(b"\x00\x00\x00\x00"))
    iend = make_chunk(b"IEND", b"")
    iend_data = make_chunk(b"IEND", b"\x01\x02")
    # (name, file, header answer, chunk layer accepts?)
    cases = [
        ("a second IHDR right after the first", SIG + ihdr1 + ihdr2 + idat + iend, "none", True),
        ("a second IHDR after IDAT", SIG + ihdr1 + idat + ihdr2 + iend, "none", True),
        (
            "an IEND chunk with data before IDAT, a real IEND at the end",
            SIG + ihdr1 + iend_data + idat + iend,
            header_line(1, 1, 8, 2, 0),
            True,
        ),
        ("an IEND chunk with data as the last chunk", SIG + ihdr1 + idat + iend_data, "none", False),
    ]
    lines = []
    failures = []
    answers, problems = ask_all([header_request(data) for _, data, _, _ in cases])
    for problem in problems:
        failures.append(f"chunk order: tool problem: {problem}")
    agree = 0
    for (name, _, want, _), ans in zip(cases, answers):
        if ans == want:
            agree += 1
        else:
            failures.append(f"chunk order {name}, header: want {want!r}, got {ans!r}")
    lines.append(f"Chunk order cases through `header`: {agree} of {len(cases)} agreements")
    answers, problems = ask_all([request(data) for _, data, _, _ in cases])
    for problem in problems:
        failures.append(f"chunk order, parse: tool problem: {problem}")
    agree = 0
    for (name, data, _, chunk_ok), ans in zip(cases, answers):
        want = ("ok:" + codes(data)) if chunk_ok else "none"
        if ans == want:
            agree += 1
        else:
            failures.append(f"chunk order {name}, parse: want {want[:60]!r}, got {ans!r}")
    lines.append(
        f"The same cases through `parse`, the chunk layer: {agree} of {len(cases)} agreements"
    )
    return lines, failures


def run_header_random(seed, count=200):
    """Random well formed headers, built into whole files. Each
    file is checked through `header` for its fields and through
    `parse` for a byte for byte reprint."""
    rng = random.Random(seed + 11)
    cases = []
    for _ in range(count):
        ctype = rng.choice(sorted(ALLOWED))
        depth = rng.choice(ALLOWED[ctype])
        width = rng.choice([1, 2, 17, 640, 65535, rng.randrange(1, 100001)])
        height = rng.choice([1, 3, 42, 480, 65535, rng.randrange(1, 100001)])
        interlace = rng.randrange(0, 2)
        fields = (width, height, depth, ctype, interlace)
        cases.append(
            (fields, header_file(ihdr_full(width, height, depth, ctype, interlace=interlace)))
        )
    lines = []
    failures = []
    answers, problems = ask_all([header_request(data) for _, data in cases])
    for problem in problems:
        failures.append(f"random headers: tool problem: {problem}")
    answers2, problems2 = ask_all([request(data) for _, data in cases])
    for problem in problems2:
        failures.append(f"random headers, parse: tool problem: {problem}")
    agree = 0
    for (fields, _), ans in zip(cases, answers):
        want = header_line(*fields)
        if ans == want:
            agree += 1
        else:
            failures.append(f"random header {fields}: want {want!r}, got {ans!r}")
    lines.append(
        f"Random well formed headers: {agree} of {len(cases)} decoded "
        "to the fields they were built with"
    )
    agree2 = 0
    for (_, data), ans in zip(cases, answers2):
        want = "ok:" + codes(data)
        if ans == want:
            agree2 += 1
        else:
            failures.append(f"random header file: want byte for byte reprint, got {ans!r}")
    lines.append(
        f"Random header files through `parse`: {agree2} of {len(cases)} "
        "reprinted byte for byte"
    )
    return lines, failures


def run_header_bounds():
    """The largest width and height the rules allow, 2^31 - 1, are
    accepted with their fields: the cap is exact on both sides."""
    top = 2**31 - 1
    cases = [(top, 3, 8, 6, 0), (4, top, 8, 6, 0), (top, top, 8, 0, 1)]
    lines = []
    failures = []
    answers, problems = ask_all(
        [header_request(header_file(ihdr_full(w, h, d, t, interlace=i))) for (w, h, d, t, i) in cases]
    )
    for problem in problems:
        failures.append(f"header bounds: tool problem: {problem}")
    agree = 0
    for fields, ans in zip(cases, answers):
        want = header_line(*fields)
        if ans == want:
            agree += 1
        else:
            failures.append(f"header bound {fields}: want {want!r}, got {ans!r}")
    lines.append(f"Headers at the cap, width or height 2^31 - 1, accepted: {agree} of {len(cases)}")
    return lines, failures


# ---------------------------------------------------------------- the
# libpng oracle for the header read. tests/libpng_header.c is built
# against the system libpng, when there is one, and each file below
# is read by libpng and by the Lean tool's `header` request. The
# answers must agree, field for field, except in the named
# differences listed here, each of which is a rule this reader
# leaves out on purpose (SPEC.md says so) or a place libpng is more
# lenient than the PNG specification.

LIBPNG_SRC = ROOT / "tests" / "libpng_header.c"
LIBPNG_EXE = ROOT / ".lake" / "oracle" / "libpng_header"

CHANNELS = {0: 1, 2: 3, 3: 1, 4: 2, 6: 4}
ADAM7 = [(0, 0, 8, 8), (4, 0, 8, 8), (0, 4, 4, 8), (2, 0, 4, 4), (0, 2, 2, 4), (1, 0, 2, 2), (0, 1, 1, 2)]

# Named differences: case name -> (what libpng answers, why).
LIBPNG_NAMED = {
    "indexed colour with no PLTE chunk": (
        "libpng refuses the file (no PLTE before IDAT); this reader accepts it",
        "which chunks must appear between IHDR and IEND is not checked (SPEC.md, Chunks)",
    ),
    "an IEND chunk with data before IDAT, a real IEND at the end": (
        "libpng refuses the file (IEND out of place); this reader accepts it",
        "an IEND chunk that carries data is an ordinary chunk here (SPEC.md, Chunks)",
    ),
    "an IEND chunk with data as the last chunk": (
        "libpng reads the file, with a warning; this reader refuses it",
        "the file has no IEND chunk with empty data, which the PNG specification requires (SPEC.md, Chunks)",
    ),
}


LIBPNG_BUILT = []


def build_libpng():
    """Build the libpng oracle, once per run. Returns (version text,
    None) or (None, the reason it could not be built)."""
    if not LIBPNG_BUILT:
        LIBPNG_BUILT.append(build_libpng_once())
    return LIBPNG_BUILT[0]


def build_libpng_once():
    cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
    if not cc:
        return None, "no C compiler"
    flags = ["-lpng16"]
    if shutil.which("pkg-config"):
        pc = subprocess.run(
            ["pkg-config", "--cflags", "--libs", "libpng"], capture_output=True, text=True
        )
        if pc.returncode == 0 and pc.stdout.split():
            flags = pc.stdout.split()
    LIBPNG_EXE.parent.mkdir(parents=True, exist_ok=True)
    build = subprocess.run(
        [cc, "-O1", "-o", str(LIBPNG_EXE), str(LIBPNG_SRC), *flags],
        capture_output=True,
        text=True,
    )
    if build.returncode != 0:
        tail = " / ".join(build.stderr.strip().splitlines()[-2:])
        return None, f"libpng oracle did not build: {tail}"
    run = subprocess.run([str(LIBPNG_EXE)], input="version\n", capture_output=True, text=True)
    if run.returncode != 0 or not run.stdout.startswith("ok:"):
        return None, "libpng oracle did not run"
    return run.stdout[3:].strip(), None


def ask_libpng(requests):
    run = subprocess.run(
        [str(LIBPNG_EXE)],
        input="".join(r + "\n" for r in requests),
        capture_output=True,
        text=True,
        timeout=TIMEOUT,
    )
    answers = run.stdout.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    if run.returncode != 0 or len(answers) != len(requests):
        return None
    return answers


def raw_image(width, height, depth, colour_type, interlace):
    """Filtered scanlines of an all zero image: a filter byte of 0,
    then zero pixels, for each row of each Adam7 pass when the
    image is interlaced."""
    bits = CHANNELS.get(colour_type, 1) * depth

    def rows(w, h):
        return (b"\x00" * (1 + (w * bits + 7) // 8)) * h

    if interlace != 1:
        return rows(width, height)
    out = b""
    for x0, y0, dx, dy in ADAM7:
        pw = (width - x0 + dx - 1) // dx if width > x0 else 0
        ph = (height - y0 + dy - 1) // dy if height > y0 else 0
        if pw and ph:
            out += rows(pw, ph)
    return out


def oracle_png(width, height, depth, colour_type, interlace=0, comp=0, filt=0, plte=True, raw=None):
    """A whole file whose image data decodes, for colour types and
    depths the table allows: indexed colour gets a one entry PLTE
    chunk, and the IDAT chunk holds an all zero image."""
    if raw is None:
        if colour_type in CHANNELS and depth in ALLOWED.get(colour_type, []):
            raw = raw_image(width, height, depth, colour_type, interlace)
        else:
            raw = b"\x00"
    parts = [SIG, make_chunk(b"IHDR", ihdr_full(width, height, depth, colour_type, comp, filt, interlace))]
    if colour_type == 3 and plte:
        parts.append(make_chunk(b"PLTE", b"\x00\x00\x00"))
    parts.append(make_chunk(b"IDAT", zlib.compress(raw)))
    parts.append(make_chunk(b"IEND", b""))
    return b"".join(parts)


def libpng_cases(seed):
    """(name, mode, file) for the libpng comparison. `full` reads the
    whole file and decodes the image; `info` reads up to IDAT and is
    used where the image would be too large to decode."""
    cases = []
    for name, data in real_files(seed):
        cases.append((f"real file: {name}", "full", data))
    for t in list(range(13)) + [255]:
        for d in [0, 1, 2, 3, 4, 5, 8, 16, 255]:
            cases.append((f"grid: colour type {t}, depth {d}", "full", oracle_png(3, 2, d, t)))
    for t in sorted(ALLOWED):
        for d in ALLOWED[t]:
            for i in (0, 1):
                for w, h in ((1, 1), (3, 2), (9, 9)):
                    cases.append((f"allowed pair: {w}x{h} d{d} t{t} i{i}", "full", oracle_png(w, h, d, t, i)))
    top = 2**31 - 1
    z = b"\x00"  # read up to IDAT only, so the image data is not looked at
    for name, data in [
        ("a width of zero", oracle_png(0, 3, 8, 6, raw=z)),
        ("a height of zero", oracle_png(4, 0, 8, 6, raw=z)),
        ("a width of 2^31", oracle_png(2**31, 3, 8, 6, raw=z)),
        ("a height of 2^31", oracle_png(4, 2**31, 8, 6, raw=z)),
        ("a width of 2^32 - 1", oracle_png(2**32 - 1, 3, 8, 6, raw=z)),
        ("a height of 2^32 - 1", oracle_png(4, 2**32 - 1, 8, 6, raw=z)),
        ("a compression byte of 1", oracle_png(4, 3, 8, 6, comp=1, raw=z)),
        ("a filter byte of 1", oracle_png(4, 3, 8, 6, filt=1, raw=z)),
        ("an interlace byte of 2", oracle_png(4, 3, 8, 6, interlace=2, raw=z)),
        ("a width of 2^31 - 1", oracle_png(top, 3, 8, 6, raw=z)),
        ("a height of 2^31 - 1", oracle_png(4, top, 8, 6, raw=z)),
        ("a width and height of 2^31 - 1, Adam7", oracle_png(top, top, 8, 0, 1, raw=z)),
    ]:
        cases.append((f"header rule: {name}", "info", data))
    for name, cut in [("an IHDR chunk of 12 bytes", 12), ("an IHDR chunk of 14 bytes", 14)]:
        body = (ihdr_full(4, 3, 8, 6) + b"\x00")[:cut]
        data = (
            SIG
            + make_chunk(b"IHDR", body)
            + make_chunk(b"IDAT", zlib.compress(raw_image(4, 3, 8, 6, 0)))
            + make_chunk(b"IEND", b"")
        )
        cases.append((f"header rule: {name}", "info", data))
    rng = random.Random(seed + 13)
    for k in range(150):
        t = rng.choice(sorted(ALLOWED))
        d = rng.choice(ALLOWED[t])
        w, h, i = rng.randrange(1, 40), rng.randrange(1, 40), rng.randrange(0, 2)
        cases.append((f"random: {w}x{h} d{d} t{t} i{i}", "full", oracle_png(w, h, d, t, i)))
    ihdr1 = make_chunk(b"IHDR", ihdr_full(1, 1, 8, 2))
    ihdr2 = make_chunk(b"IHDR", ihdr_full(2, 2, 8, 2))
    idat = make_chunk(b"IDAT", zlib.compress(raw_image(1, 1, 8, 2, 0)))
    iend = make_chunk(b"IEND", b"")
    iend_data = make_chunk(b"IEND", b"\x01\x02")
    cases += [
        ("a second IHDR right after the first", "full", SIG + ihdr1 + ihdr2 + idat + iend),
        ("a second IHDR after IDAT", "full", SIG + ihdr1 + idat + ihdr2 + iend),
        ("an IEND chunk with data before IDAT, a real IEND at the end", "full", SIG + ihdr1 + iend_data + idat + iend),
        ("an IEND chunk with data as the last chunk", "full", SIG + ihdr1 + idat + iend_data),
        ("indexed colour with no PLTE chunk", "full", oracle_png(3, 2, 8, 3, plte=False)),
    ]
    return cases


def lean_header_text(ans):
    """The Lean tool's `header` answer as the same text libpng's
    answer uses: `ok:` and the fields, or `none`."""
    if ans is None or not ans.startswith("ok:"):
        return ans
    try:
        return "ok:" + bytes(int(c) for c in ans[3:].split(",")).decode("ascii")
    except ValueError:
        return ans


def run_libpng(seed):
    """Returns (lines, failures, inputs, named): the record lines,
    the failures, the count of files compared, and the named
    differences met, with their counts."""
    version, why = build_libpng()
    if version is None:
        return [f"libpng header oracle: skipped, {why}"], [], 0, {}
    cases = libpng_cases(seed)
    lp = ask_libpng([f"{mode} {data.hex()}" for _, mode, data in cases])
    if lp is None:
        return [f"libpng header oracle ({version}): did not answer"], ["libpng oracle did not answer"], 0, {}
    lean, problems = ask_all([header_request(data) for _, _, data in cases])
    failures = [f"libpng comparison: tool problem: {p}" for p in problems]
    agree = 0
    named = {}
    for (name, mode, _), want, got in zip(cases, lp, lean):
        theirs = want.split(" warnings:")[0]
        ours = lean_header_text(got)
        same = (theirs.startswith("ok:") and ours == theirs) or (
            theirs.startswith("none:") and ours == "none"
        )
        if same:
            agree += 1
        elif name in LIBPNG_NAMED:
            named[name] = named.get(name, 0) + 1
        else:
            failures.append(f"libpng comparison {name} ({mode}): libpng {want!r}, this reader {ours!r}")
    lines = [
        f"libpng header oracle ({version}, `tests/libpng_header.c`): {len(cases)} files, "
        f"{agree} agreements, {sum(named.values())} named differences"
    ]
    for name in LIBPNG_NAMED:
        if name in [c[0] for c in cases] and name not in named:
            failures.append(f"libpng comparison {name}: the named difference did not occur")
    return lines, failures, len(cases), named


def run_header_malformed():
    lines = []
    failures = []
    bad = ["header 256", "header 12a", "header 97 98"]
    answers, problems = ask_all(bad)
    for problem in problems:
        failures.append(f"header malformed: tool problem: {problem}")
    bad_ok = 0
    for line, ans in zip(bad, answers):
        if ans == "error":
            bad_ok += 1
        else:
            failures.append(f"header malformed {line!r}: want error, got {ans!r}")
    lines.append(f"Malformed header requests answered error: {bad_ok} of {len(bad)}")
    none_ok = 0
    answers, _ = ask_all(["header", "header "])
    for ans in answers:
        if ans == "none":
            none_ok += 1
        else:
            failures.append(f"empty header request: want none, got {ans!r}")
    lines.append(f"Header requests with no codes answered none: {none_ok} of 2")
    return lines, failures


# ---------------------------------------------------------------- the
# accepted inputs stated in Png/Spec.lean. Two statements there give
# an input and the header the reader returns for it:
# Png.Spec.reads_real_file_header (a whole file) and
# Png.Spec.reads_header_1920x1080 (13 header bytes). The bytes and
# the fields are read from Png/Spec.lean itself, so the check is of
# the statements as written, and each is checked three ways: the
# harness's own reading of the bytes (big endian width and height,
# zlib for the CRCs and the image data), the tool's `header` answer,
# and libpng's answer where libpng is installed.

SPEC_LEAN = ROOT / "Png" / "Spec.lean"


def lean_bytes(text):
    return bytes(int(x) for x in text.replace("\n", " ").split(","))


HEADER_FIELDS = ("width", "height", "bitDepth", "colorType", "interlace")


def lean_fields(text):
    """The header a statement gives, written as a structure
    instance with its five fields named, as (width, height, bit
    depth, colour type, interlace)."""
    got = dict(
        (k, int(v)) for k, v in re.findall(r"(\w+)\s*:=\s*([0-9]+)", text)
    )
    if sorted(got) != sorted(HEADER_FIELDS):
        return None
    return tuple(got[k] for k in HEADER_FIELDS)


def spec_examples():
    """(theorem, file, the 13 header bytes, the stated fields), read
    from Png/Spec.lean. The header only statement is wrapped in a
    whole file: its 13 bytes as the IHDR data, an IDAT chunk holding an
    all zero image of that size, and IEND."""
    src = SPEC_LEAN.read_text(encoding="utf-8")
    found = []
    m = re.search(
        r"theorem Png\.Spec\.reads_real_file_header :\s*\(parseFile \(\[([0-9,\s]*)\]\s*"
        r":\s*List UInt8\)\)\.map Prod\.fst =\s*some \{([^}]*)\}",
        src,
    )
    if m and lean_fields(m.group(2)):
        data = lean_bytes(m.group(1))
        found.append(("Png.Spec.reads_real_file_header", data, data[16:29], lean_fields(m.group(2))))
    m = re.search(
        r"theorem Png\.Spec\.reads_header_1920x1080 :\s*parseIhdr \(\[([0-9,\s]*)\]\s*"
        r":\s*List UInt8\) =\s*some \{([^}]*)\}",
        src,
    )
    if m and lean_fields(m.group(2)):
        ihdr = lean_bytes(m.group(1))
        w, h, d, t, i = lean_fields(m.group(2))
        data = (
            SIG
            + make_chunk(b"IHDR", ihdr)
            + make_chunk(b"IDAT", zlib.compress(raw_image(w, h, d, t, i)))
            + make_chunk(b"IEND", b"")
        )
        found.append(("Png.Spec.reads_header_1920x1080", data, ihdr, (w, h, d, t, i)))
    return found


def own_reading(data, ihdr, fields):
    """The harness's own reading of a stated input: None when it
    agrees with the stated fields, else what is wrong."""
    w, h, d, t, i = fields
    if len(ihdr) != 13:
        return f"the header is {len(ihdr)} bytes, not 13"
    got = struct.unpack(">IIBBBBB", ihdr)
    if got != (w, h, d, t, 0, 0, i):
        return f"the 13 bytes read big endian are {got}, not {(w, h, d, t, 0, 0, i)}"
    chunks = oracle_parse(data)
    if chunks is None:
        return "the strict oracle refuses the file"
    if chunks[0] != (b"IHDR", ihdr):
        return "the file's IHDR data is not the stated 13 bytes"
    image = zlib.decompress(b"".join(c for typ, c in chunks if typ == b"IDAT"))
    want = len(raw_image(w, h, d, t, i))
    if len(image) != want:
        return f"the image data inflates to {len(image)} bytes, not {want}"
    return None


def run_spec_examples():
    lines = []
    failures = []
    cases = spec_examples()
    if len(cases) != 2:
        failures.append(
            f"Png/Spec.lean accepted inputs: found {len(cases)} of the 2 statements; "
            "the harness could not read them"
        )
    own_ok = 0
    for name, data, ihdr, fields in cases:
        wrong = own_reading(data, ihdr, fields)
        if wrong is None:
            own_ok += 1
        else:
            failures.append(f"{name}: {wrong}")
    lines.append(
        f"Accepted inputs stated in Png/Spec.lean, read from that file: {own_ok} of "
        f"{len(cases)} agree with the harness's own reading of the bytes"
    )
    answers, problems = ask_all([header_request(data) for _, data, _, _ in cases])
    failures += [f"Png/Spec.lean accepted inputs: tool problem: {p}" for p in problems]
    tool_ok = 0
    for (name, _, _, fields), ans in zip(cases, answers):
        want = header_line(*fields)
        if ans == want:
            tool_ok += 1
        else:
            failures.append(f"{name} through `header`: want {want!r}, got {ans!r}")
    lines.append(
        f"Accepted inputs stated in Png/Spec.lean, through `header`: {tool_ok} of "
        f"{len(cases)} answered with the stated header"
    )
    version, why = build_libpng()
    if version is None:
        lines.append(f"Accepted inputs stated in Png/Spec.lean, through libpng: skipped, {why}")
        return lines, failures
    lp = ask_libpng([f"full {data.hex()}" for _, data, _, _ in cases])
    if lp is None:
        failures.append("Png/Spec.lean accepted inputs: the libpng oracle did not answer")
        return lines, failures
    lp_ok = 0
    for (name, _, _, fields), got in zip(cases, lp):
        w, h, d, t, i = fields
        want = f"ok:{w}x{h} d{d} t{t} i{i}"
        if got.split(" warnings:")[0] == want:
            lp_ok += 1
        else:
            failures.append(f"{name} through libpng: want {want!r}, got {got!r}")
    lines.append(
        f"Accepted inputs stated in Png/Spec.lean, through libpng ({version}), "
        f"decoded in full: {lp_ok} of {len(cases)} read with the stated header"
    )
    return lines, failures


# ---------------------------------------------------------------- the
# axiom check. Png/Proofs/Verify.lean prints `#print axioms` for the
# headline theorems in Png.Proofs and for every theorem
# comparator.json names. Each must have its line, and each may
# depend on these three axioms and no other: a `sorryAx`, or any
# axiom a proof adds of its own, is a failure.

AXIOMS_ALLOWED = ("propext", "Classical.choice", "Quot.sound")

HEADLINE = [
    "Png.Proofs.parse_print",
    "Png.Proofs.parseIhdr_print",
    "Png.Proofs.checkPair_iff",
    "Png.Proofs.parseFile_print",
    "Png.Proofs.parse_sound",
    "Png.Proofs.parseIhdr_sound",
    "Png.Proofs.parseFile_sound",
    "Png.Proofs.print_layout",
    "Png.Proofs.printIhdr_layout",
    "Png.Proofs.isLetter_iff",
    "Png.Proofs.isIEND_iff",
]


def axiom_names():
    """The theorems the axiom check covers: the headline theorems,
    then every theorem comparator.json names."""
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    return HEADLINE + list(config["theorem_names"])


def read_axioms(text):
    """The axioms of each theorem in `#print axioms` output, by
    name. A list may run over several lines."""
    found = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        found[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        found[m.group(1)] = []
    return found


def axiom_failures(found, names):
    failures = []
    for name in names:
        if name not in found:
            failures.append(f"axiom check: no `#print axioms` output for {name}")
            continue
        extra = [a for a in found[name] if a not in AXIOMS_ALLOWED]
        if extra:
            failures.append(
                f"axiom check: {name} depends on {', '.join(extra)}, "
                "beyond propext, Classical.choice, and Quot.sound"
            )
    return failures


def axiom_self_test():
    """The check itself, on planted output: a theorem on sorryAx, one
    on an axiom of its own, and a missing line must each fail, and
    clean output must pass. Returns the failures of the check."""
    names = ["A.clean", "A.none", "A.sorry", "A.own"]
    planted = (
        "'A.clean' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
        "'A.none' does not depend on any axioms\n"
        "'A.sorry' depends on axioms: [propext, sorryAx]\n"
        "'A.own' depends on axioms: [Quot.sound, A.myAxiom]\n"
    )
    got = axiom_failures(read_axioms(planted), names + ["A.missing"])
    want = [
        "axiom check: A.sorry depends on sorryAx, beyond propext, Classical.choice, and Quot.sound",
        "axiom check: A.own depends on A.myAxiom, beyond propext, Classical.choice, and Quot.sound",
        "axiom check: no `#print axioms` output for A.missing",
    ]
    if got != want:
        return [f"axiom check self-test: planted output gave {got!r}"]
    return []


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
        run_real_headers(args.seed),
        run_header_types(),
        run_header_grid(),
        run_header_mutations(),
        run_header_chunk_order(),
        run_header_bounds(),
        run_header_random(args.seed),
        run_header_malformed(),
        run_spec_examples(),
    ):
        lines, failures = part
        all_lines += lines
        all_failures += failures
    # The record's Inputs: every request of the sections above. The
    # libpng comparison below runs only where libpng is installed, so
    # it is counted on its own line, and a run without libpng records
    # the same Inputs.
    inputs = ASKED[0]
    libpng_lines, libpng_failures, libpng_inputs, named = run_libpng(args.seed)
    all_failures += libpng_failures

    lean_version = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    ).stdout.strip()

    # The axiom check: Png/Proofs/Verify.lean prints the axioms of the
    # headline theorems and of every theorem comparator.json names,
    # with `#print axioms`. The names in that output are read, and
    # any axiom beyond the three standard ones is a failure. The
    # output goes into the results file, in the Axiom check section.
    all_failures += axiom_self_test()
    axiom_run = subprocess.run(
        ["lake", "env", "lean", "Png/Proofs/Verify.lean"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=600,
    )
    if axiom_run.returncode != 0:
        all_failures.append(
            f"axiom check: running Png/Proofs/Verify.lean exited {axiom_run.returncode}"
        )
    covered = axiom_names()
    found = read_axioms(axiom_run.stdout)
    all_failures += axiom_failures(found, covered)
    axiom_lines = [
        f"'{name}' depends on axioms: [{', '.join(found[name])}]"
        for name in covered
        if name in found
    ]

    out = ["# Test results", ""]
    out.append("Written by `tests/run_tests.py`. Rerun it to check these numbers.")
    out.append("")
    out.append(
        f"- Oracle: Python {sys.version.split()[0]} `zlib` (crc32 and compress), "
        "plus a strict reading of the plan rules written in the harness; "
        "for the header read, also libpng where it is installed (below)"
    )
    out.append(f"- Lean: {lean_version}")
    out.append(f"- Seed: {args.seed}")
    out.append(f"- Inputs: {inputs}")
    out.append(
        "- Inputs counts every request of the sections below, up to the libpng "
        "comparison, which is counted on its own line"
    )
    for line in all_lines:
        out.append(f"- {line}")
    out.append("")
    out.append("## libpng comparison of the header read")
    out.append("")
    out.append(
        "Each file is read by libpng (`tests/libpng_header.c`, built against the "
        "system libpng, with its default width and height limits raised to "
        "2^31 - 1) and by the tool's `header` request, and the two answers must "
        "agree: the same fields, or both refuse. The files: the real files, the "
        "colour type and depth grid, every allowed pair with and without Adam7 at "
        "three sizes, the header rule cases, 150 random well formed headers, and "
        "the chunk order cases. Whole files are decoded by libpng, image and all, "
        "except for the header rule cases, which libpng reads up to IDAT."
    )
    out.append("")
    for line in libpng_lines:
        out.append(f"- {line}")
    out.append(f"- Named differences: {sum(named.values())}")
    for name, count in named.items():
        what, why = LIBPNG_NAMED[name]
        out.append(f"- Named difference, {name} ({count}): {what}; {why}")
    out.append("")
    out.append("## Axiom check")
    out.append("")
    out.append(
        f"The output of `#print axioms` for the {len(HEADLINE)} headline theorems "
        f"and the {len(covered) - len(HEADLINE)} theorems `comparator.json` names, "
        "from `lake env lean Png/Proofs/Verify.lean`. The harness reads the names, and "
        "fails on any axiom but "
        + ", ".join(f"`{a}`" for a in AXIOMS_ALLOWED)
        + ". A self-test on planted output (a `sorryAx`, an axiom of a proof's own, "
        "a missing line) runs first."
    )
    out.append("")
    for line in axiom_lines:
        out.append(f"- {line}")
    out.append("")
    out.append("## Outcome")
    out.append("")
    out.append(f"- Failures: {len(all_failures)}")
    for failure in all_failures[:50]:
        out.append(f"- FAILURE: {failure}")
    RESULTS.write_text("\n".join(out) + "\n", encoding="utf-8")
    print("\n".join(out))
    return 0 if not all_failures else 1


if __name__ == "__main__":
    sys.exit(main())
