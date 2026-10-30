# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `zlib` (crc32 and compress), plus a strict reading of the plan rules written in the harness; for the header read, also libpng where it is installed (below)
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261026
- Inputs: 1485
- Inputs counts every request of the sections below, up to the libpng comparison, which is counted on its own line
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
- Real PNG files through `header`: 4 of 4 decoded to the fields they were built with
- Hand-built headers, every colour type and allowed depth: 15 of 15 accepted with their fields
- Header enumeration, 14 colour types by 9 depths against the allowed table: 126 of 126 agreements
- Header mutations rejected: 10 of 10
- Chunk order cases through `header`: 4 of 4 agreements
- The same cases through `parse`, the chunk layer: 4 of 4 agreements
- Headers at the cap, width or height 2^31 - 1, accepted: 3 of 3
- Random well formed headers: 200 of 200 decoded to the fields they were built with
- Random header files through `parse`: 200 of 200 reprinted byte for byte
- Malformed header requests answered error: 3 of 3
- Header requests with no codes answered none: 2 of 2
- Accepted inputs stated in Png/Spec.lean, read from that file: 2 of 2 agree with the harness's own reading of the bytes
- Accepted inputs stated in Png/Spec.lean, through `header`: 2 of 2 answered with the stated header
- Accepted inputs stated in Png/Spec.lean, through libpng (built 1.6.43, running 1.6.43), decoded in full: 2 of 2 read with the stated header

## libpng comparison of the header read

Each file is read by libpng (`tests/libpng_header.c`, built against the system libpng, with its default width and height limits raised to 2^31 - 1) and by the tool's `header` request, and the two answers must agree: the same fields, or both refuse. The files: the real files, the colour type and depth grid, every allowed pair with and without Adam7 at three sizes, the header rule cases, 150 random well formed headers, and the chunk order cases. Whole files are decoded by libpng, image and all, except for the header rule cases, which libpng reads up to IDAT.

- libpng header oracle (built 1.6.43, running 1.6.43, `tests/libpng_header.c`): 389 files, 386 agreements, 3 named differences
- Named differences: 3
- Named difference, an IEND chunk with data before IDAT, a real IEND at the end (1): libpng refuses the file (IEND out of place); this reader accepts it; an IEND chunk that carries data is an ordinary chunk here (SPEC.md, Chunks)
- Named difference, an IEND chunk with data as the last chunk (1): libpng reads the file, with a warning; this reader refuses it; the file has no IEND chunk with empty data, which the PNG specification requires (SPEC.md, Chunks)
- Named difference, indexed colour with no PLTE chunk (1): libpng refuses the file (no PLTE before IDAT); this reader accepts it; which chunks must appear between IHDR and IEND is not checked (SPEC.md, Chunks)

## Axiom check

The output of `#print axioms` for the 11 headline theorems and the 30 theorems `comparator.json` names, from `lake env lean Png/Proofs/Verify.lean`. The harness reads the names, and fails on any axiom but `propext`, `Classical.choice`, `Quot.sound`. A self-test on planted output (a `sorryAx`, an axiom of a proof's own, a missing line) runs first.

- 'Png.Proofs.parse_print' depends on axioms: [propext, Quot.sound]
- 'Png.Proofs.parseIhdr_print' depends on axioms: [propext, Quot.sound]
- 'Png.Proofs.checkPair_iff' depends on axioms: [propext, Quot.sound]
- 'Png.Proofs.parseFile_print' depends on axioms: [propext, Quot.sound]
- 'Png.Proofs.parse_sound' depends on axioms: [propext, Quot.sound]
- 'Png.Proofs.parseIhdr_sound' depends on axioms: [propext, Quot.sound]
- 'Png.Proofs.parseFile_sound' depends on axioms: [propext, Quot.sound]
- 'Png.Proofs.print_layout' depends on axioms: [propext, Quot.sound]
- 'Png.Proofs.printIhdr_layout' depends on axioms: [propext]
- 'Png.Proofs.isLetter_iff' depends on axioms: [propext]
- 'Png.Proofs.isIEND_iff' depends on axioms: [propext]
- 'Png.Spec.parse_print' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.parseIhdr_print' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.checkPair_iff' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.parseFile_print' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.parse_sound' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.parseIhdr_sound' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.parseFile_sound' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.print_layout' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.printIhdr_layout' depends on axioms: [propext]
- 'Png.Spec.isLetter_iff' depends on axioms: [propext]
- 'Png.Spec.ihdrType_eq' depends on axioms: []
- 'Png.Spec.typeBytes_eq' depends on axioms: []
- 'Png.Spec.isIEND_iff' depends on axioms: [propext]
- 'Png.Spec.reads_real_file_header' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.reads_header_1920x1080' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_bad_signature' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_bad_crc' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_truncated_input' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_first_chunk_length_12' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_zero_width' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_zero_height' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_width_at_cap' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_height_at_cap' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_illegal_depth' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_unknown_colour_type' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_unknown_interlace' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_nonzero_compression' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_nonzero_filter' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_second_ihdr' depends on axioms: [propext, Quot.sound]
- 'Png.Spec.rejects_header_wrong_length' depends on axioms: [propext, Quot.sound]

## Outcome

- Failures: 0
