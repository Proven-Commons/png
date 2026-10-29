# png: a PNG chunk parser and printer, with proved round trips

Status: in-progress

A parser and printer for the chunk layer of PNG files, in Lean,
following the PNG specification. It reads the signature, then
each chunk's length, type, data, and CRC-32 check. Slice 2 adds
a decoder for the IHDR header: the width, height, bit depth,
colour type, and interlace method held in the first chunk's 13
data bytes, checked against the validity rules of the PNG
specification. It does not decode pixels, and it does not
inflate IDAT data. The rules are written out in `SPEC.md`.

The statements a reviewer approves are in `Spec.lean`, with
their proofs in `Proofs/SpecProofs.lean`. No reviewer has
approved them yet, so this project is not called verified.

## How to run it

`lake build` builds the library, the proofs, and the command
line tool. The tool reads one request per line: the word
`parse` or `header`, a space, and the file as comma-separated
decimal byte codes. `parse` answers `ok:` and the byte codes
of the canonical reprint of the parsed chunk list, or `none`
when the file is rejected. `header` reads the file at both
layers, the chunk list and the IHDR header decoded from the
first chunk's data, and answers `ok:` and the codes of a text
line naming the header fields, or `none` when the file is
rejected at either layer. A malformed request answers
`error`.

```
lake build
echo "parse 137,80,78,71,13,10,26,10,0,0,0,13,73,72,68,82,0,0,0,1,0,0,0,1,8,2,0,0,0,144,119,83,222,0,0,0,0,73,69,78,68,174,66,96,130" | .lake/build/bin/png
```

That request is a whole minimal PNG file as byte codes: the
signature, an IHDR chunk for a 1 by 1 image, and IEND. The
answer is `ok:` followed by the same codes, since the file is
valid and reprints byte for byte. A file the parser rejects,
such as the single code `120`, answers `none`. The same file
asked through `header`, with the word `header` in place of
`parse`, answers `ok:49,120,49,32,100,56,32,116,50,32,105,48`:
the codes of the text `1x1 d8 t2 i0`, the decoded header
fields. See `SPEC.md` for the full protocol.

`python3 tests/run_tests.py` rebuilds the tool, runs the real
files, the hand built cases, the differential runs, and the
header sections, and writes the outcome to
`tests/TEST-RESULTS.md`.

## What is proved

Each claim below names the theorem behind it. The theorems
are stated in `Spec.lean` (the challenge file, where they end
in `sorry`) and proved in `Proofs/SpecProofs.lean`, under the
same names. `comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed chunk list gives the list back. | `Spec.parse_print` |
| Reading the printed bytes of a well formed IHDR header gives the header back. | `Spec.parseIhdr_print` |
| The depth checker agrees with the written out table of allowed (colour type, bit depth) pairs on every byte pair. | `Spec.checkPair_iff` |
| Printing a fully well formed document whose first chunk holds the printed header `hd`, and reading it back at both layers, gives back `hd` itself and the document. | `Spec.parseFile_print` |
| A file whose first signature byte is wrong is refused. | `Spec.rejects_bad_signature` |
| A file whose IHDR chunk carries a CRC that does not match its type and data is refused. | `Spec.rejects_bad_crc` |
| A file cut short inside its first chunk is refused. | `Spec.rejects_truncated_input` |
| A file whose first chunk holds 12 data bytes is refused: an IHDR chunk holds 13. | `Spec.rejects_first_chunk_length_12` |
| A file with a width of zero is refused. | `Spec.rejects_zero_width` |
| A file with a height of zero is refused. | `Spec.rejects_zero_height` |
| A file with a width of 2^31 is refused: the width stays below 2^31. | `Spec.rejects_width_at_cap` |
| A file with a height of 2^31 is refused: the height stays below 2^31. | `Spec.rejects_height_at_cap` |
| A file with bit depth 4 on colour type 2 is refused: that colour type allows depths 8 and 16 only. | `Spec.rejects_illegal_depth` |
| A file with colour type 1 is refused: 1 is not a PNG colour type, and allows no bit depth. | `Spec.rejects_unknown_colour_type` |
| A file with an interlace byte of 2 is refused: the byte is 0 or 1. | `Spec.rejects_unknown_interlace` |
| A file with a compression byte of 1 is refused: the only compression method is 0. | `Spec.rejects_nonzero_compression` |
| A file with a filter byte of 1 is refused: the only filter method is 0. | `Spec.rejects_nonzero_filter` |
| The header reader refuses anything but exactly 13 bytes: here a valid header's first 12 bytes. | `Spec.rejects_header_wrong_length` |

A chunk list is well formed when it is a first chunk, then
any middle chunks, then the IEND chunk; the first chunk has
type IHDR and 13 data bytes; no chunk before the last is the
IEND chunk; every chunk type is four ASCII letters; and every
data length is below 2^31. A header is well formed when its
width and height are above zero and below 2^31, its interlace
byte is 0 or 1, and its bit depth is one its colour type
allows. A document is fully well formed with header `hd`
(`WFFull hd doc`) when it is well formed at the chunk layer and
its first chunk's data is the printed form of `hd`, a well
formed header. The header is a parameter of the predicate, so
the file level round trip names the header the read must
return: a reader that answered a fixed header, or swapped the
width and the height, would not meet it.

The headline theorems rest on the proofs in
`Proofs/RoundTrip.lean` and `Proofs/Header.lean`, where they
are `Png.Proofs.parse_print`, `Png.Proofs.parseIhdr_print`,
`Png.Proofs.checkPair_iff`, and `Png.Proofs.parseFile_print`.
Each checks against two of the standard axioms (`propext`,
`Quot.sound`), which a reader can confirm with `#print
axioms`, or by running `lake env lean Proofs/Verify.lean`.
The refusal theorems are single inputs checked in the kernel
with `decide +kernel`.

The definitions are in `Png/Value.lean` (the chunk type, the
printer, and the well formedness rules), `Png/Parse.lean`
(the parser), `Png/Crc32.lean` (the CRC-32), and
`Png/Header.lean` (the IHDR header value, its reader and
printer, and the file level read). The command line tool in
`Main.lean` calls `Png.parse`, `Png.print`, and
`Png.parseFile` directly, the same functions the theorems are
about.

## What is not proved

- That the parser accepts every file the rules in `SPEC.md` allow, and rejects every file they forbid. The round trip does not need either, so neither is proved. The test suite checks that behaviour instead, and the results file records the outcome, including any failure.
- That the CRC-32 here is the standard one. The round trip needs no such fact, since the parser and the printer compute the same function. The differential tests against Python zlib's `crc32` are what tie this function to the standard.
- That the header reader accepts every header the rules in `SPEC.md` allow, and rejects every header they forbid, beyond what the round trip and the table theorem cover. The tests check that behaviour instead: hand built headers for every colour type and allowed depth, the full colour type and depth enumeration against the table, and the rejection cases.
- Anything inside a chunk's data past the IHDR header. The data of every other chunk type is opaque here. IDAT data is not inflated. No pixel is ever decoded.
- Chunk order past the first and last. Which types may appear, how many times, and in what order between IHDR and IEND is not checked. A chunk of type IEND that carries data is read as an ordinary chunk.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in
  `lean-toolchain`), which checks every proof.
- The Lean compiler, with the C compiler and linker shipped
  with it, which turns the proved definitions into the
  program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest
  lists no packages, so there are no library dependencies to
  trust beyond the Lean toolchain itself.
- Lean's core library, including the compiled code it puts
  in place of some definitions the proofs reason about.
- The operating system the program runs on.
- That `SPEC.md` states the reading of the PNG specification
  you intend. The proofs are about the parser, printer, and
  header reader in this repo following each other exactly;
  the fidelity of the spec to the PNG specification is a
  reading, pinned in `SPEC.md` where the PNG specification
  leaves a choice open.
- Python's standard library, including zlib, as the oracle
  in the tests. The results file names the versions used.
- The line handling in `Main.lean` (splitting a request
  line, reading decimal codes). The tests drive it, and no
  proof covers it.
- There are no exceptions to item 4 of the bar: the project
  uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge file
   `Spec.lean` and the proofs in a sandbox and checks that
   each theorem named in `comparator.json` proves exactly
   the statement in the challenge file, uses no axiom but
   the three standard ones, and is accepted by Lean's kernel
   and every other kernel shipped with Lean.
2. `python3 tests/run_tests.py`: the real files, the hand
   built cases, the differential runs against the oracle,
   the mutations, and the header sections, with counts and
   any failures written to `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool build
   clean, and `lake env lean Proofs/Verify.lean` prints the
   axiom list for the headline theorems.
4. Read `SPEC.md` against the PNG specification and check
   the pinned readings are the ones you want.
