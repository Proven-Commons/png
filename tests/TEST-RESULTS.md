# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.12.3 `zlib` (crc32 and compress), plus a strict reading of the plan rules written in the harness
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261026
- Real PNG files (zlib built): 4 of 4 accepted and reprinted byte for byte
- Real PNG file: 1x1, bit depth 8, colour type 2 (RGB), 69 bytes
- Real PNG file: 4x3, bit depth 8, colour type 6 (RGBA), 119 bytes
- Real PNG file: 16x16, bit depth 8, colour type 0 (greyscale), IDAT split in two, 352 bytes
- Real PNG file: 7x5, bit depth 8, colour type 2 (RGB), a tEXt chunk before IDAT, 208 bytes
- Hand-built cases: 22 of 22 agreements
- Random chunk lists (Python writer, zlib.crc32): 400 documents, 400 of 400 accepted and reprinted byte for byte
- Mutations of a 86 byte file (every truncation and every single byte flip): 172 inputs, 172 agreements
- Mutations of a 1140 byte file (300 sampled single byte flips): 300 inputs, 300 agreements
- Malformed requests answered error: 12 of 12
- Requests with no codes answered none: 2 of 2
- Named differences: none
- Failures: 0

## Axiom check

Recorded on 2026-10-26 against the head of this pull request, on Lean 4.35.0. The line below is the output printed for `Proofs/Verify.lean` during a clean `lake build` (17 jobs).

```text
'Png.Proofs.parse_print' depends on axioms: [propext, Quot.sound]
```

No other axiom is named, and sorryAx is not named.
