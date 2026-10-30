# png: a PNG chunk parser and printer, with proved round trips

Status: in progress. No reviewer has approved the specification yet.

A parser and printer for the chunk layer of PNG files, in Lean,
following the PNG specification. It reads the signature, then
each chunk's length, type, data, and CRC-32 check. Slice 2 adds
a decoder for the IHDR header: the width, height, bit depth,
colour type, and interlace method held in the first chunk's 13
data bytes, checked against the validity rules of the PNG
specification. It does not decode pixels, and it does not
inflate IDAT data. The rules are written out in `SPEC.md`.

The statements a reviewer approves are in `Spec.lean`, over
the definitions in `Spec/Defs.lean`, with their proofs in
`Proofs/SpecProofs.lean`. No reviewer has approved them yet,
so this project is not called verified.

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
header sections, checks the two accepted inputs stated in
`Spec.lean`, compares the header read with libpng where a C
compiler and libpng are installed (`tests/libpng_header.c`),
and writes the outcome to `tests/TEST-RESULTS.md`.

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
| A file the chunk parser accepts is the printed form of the chunk list it returns, and that list is well formed. | `Spec.parse_sound` |
| A header the header reader accepts is well formed, and the bytes it read are its printed form. So a header that breaks any header rule is refused. | `Spec.parseIhdr_sound` |
| A file the file level read accepts is the printed form of the chunk list it returns, and that list is fully well formed with the header the read returns. So a file that breaks any rule of either layer, or holds a second IHDR chunk, is refused. | `Spec.parseFile_sound` |
| The chunk printer writes the eight signature bytes, then each chunk as its data length in four bytes big endian, its four type bytes, its data, and the CRC-32 of its type bytes and data in four bytes big endian. | `Spec.print_layout` |
| The header printer writes the width in four bytes big endian, then the height in four bytes big endian, then the bit depth, the colour type, a compression byte of zero, a filter byte of zero, and the interlace byte. | `Spec.printIhdr_layout` |
| The letter test the chunk rules use holds of the ASCII letters A to Z and a to z, and of no other byte. | `Spec.isLetter_iff` |
| The type bytes required of the first chunk are I, H, D, R. | `Spec.ihdrType_eq` |
| The type bytes the chunk rules compare are a chunk's four type bytes, in the order the printer writes them. | `Spec.typeBytes_eq` |
| The IEND chunk, where reading stops, is a chunk with type bytes I, E, N, D and no data. | `Spec.isIEND_iff` |
| A real 4 by 3 PNG file (an IHDR, an IDAT with zlib compressed pixels, and IEND) is read with its own header: width 4, height 3, bit depth 8, colour type 6, no interlace. | `Spec.reads_real_file_header` |
| The 13 bytes of a 1920 by 1080 header are read as width 1920 and height 1080, bit depth 8, colour type 2, no interlace. | `Spec.reads_header_1920x1080` |
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
| A file with a second IHDR chunk is refused by the file level read: the PNG specification allows one IHDR chunk. | `Spec.rejects_second_ihdr` |
| The header reader refuses anything but exactly 13 bytes: here a valid header's first 12 bytes. | `Spec.rejects_header_wrong_length` |

A chunk list is well formed when it is a first chunk, then
any middle chunks, then the IEND chunk; the first chunk has
type IHDR and 13 data bytes; no chunk before the last is the
IEND chunk; every chunk type is four ASCII letters; and every
data length is below 2^31. A header is well formed when its
width and height are above zero and below 2^31, its interlace
byte is 0 or 1, and its bit depth is one its colour type
allows. A document is fully well formed with header `hd`
(`WFFull hd doc`) when it is well formed at the chunk layer,
its first chunk's data is the printed form of `hd`, a well
formed header, and no chunk after the first has type IHDR.
The header is a parameter of the predicate, so
the file level round trip names the header the read must
return. That holds relative to the printer: the read must
return the header whose `printIhdr` bytes the first chunk
holds. So a reader that answered a fixed header, or swapped the
width and the height while the printer did not, would not meet
it. A change that swapped them in both the printer and the
reader would still meet the round trips. What stops it is
`Spec.printIhdr_layout`, which fixes the bytes the printer
writes (the width first, then the height, each four bytes big
endian), and the two accepted inputs,
`Spec.reads_real_file_header` and `Spec.reads_header_1920x1080`,
whose widths and heights differ.

Each reader is pinned to its rule in both directions. The
round trip says it accepts the printed form of every well
formed value and returns that value; the soundness theorem
says it accepts nothing else. So the chunk parser accepts a
file exactly when the file is `print doc` for a well formed
`doc`, and then returns `doc` (`Spec.parse_print` with
`Spec.parse_sound`); the header reader accepts 13 bytes
exactly when they are `printIhdr h` for a well formed `h`
(`Spec.parseIhdr_print` with `Spec.parseIhdr_sound`); and the
file level read accepts a file exactly when it is `print doc`
for a `doc` fully well formed with header `hd`, and then
returns `hd` and `doc` (`Spec.parseFile_print` with
`Spec.parseFile_sound`). Every rule in these predicates is
therefore a proved rejection rule. The named refusal theorems
in the table are worked examples of those rules, one input
each.

The round trips and the soundness theorems are stated in terms
of the printers. The layout theorems fix what the printers
write: `Spec.print_layout` the chunk layout, and
`Spec.printIhdr_layout` the 13 header bytes. `Spec.isLetter_iff`,
`Spec.ihdrType_eq`, `Spec.typeBytes_eq`, and `Spec.isIEND_iff`
fix the letters and type bytes the rules name. Together with the
round trips and the soundness theorems, they fix which bytes each
reader accepts and what it returns, for every input. The one
function they leave as the code has it is the CRC-32 (see
below).

The headline theorems rest on the proofs in
`Proofs/RoundTrip.lean`, `Proofs/Header.lean`,
`Proofs/Sound.lean`, and `Proofs/Layout.lean`, where they are
`Png.Proofs.parse_print`, `Png.Proofs.parseIhdr_print`,
`Png.Proofs.checkPair_iff`, `Png.Proofs.parseFile_print`,
`Png.Proofs.parse_sound`, `Png.Proofs.parseIhdr_sound`,
`Png.Proofs.parseFile_sound`, `Png.Proofs.print_layout`,
`Png.Proofs.printIhdr_layout`, `Png.Proofs.isLetter_iff`, and
`Png.Proofs.isIEND_iff`. Each checks against at most two of the
standard axioms (`propext`, `Quot.sound`), which a reader can
confirm with `#print axioms`, or by running `lake env lean
Proofs/Verify.lean`; the test harness reads that output for
every theorem `comparator.json` names, and records it.
The refusal theorems and the two accepted inputs are single
inputs checked in the kernel with `decide +kernel`, and
`Spec.ihdrType_eq` and `Spec.typeBytes_eq` hold by definition.
The test harness reads the two accepted inputs from `Spec.lean`
and checks the header each states against its own big endian
reading of the bytes, the tool's `header` answer, and libpng's.

The code is in `Png/Value.lean` (the chunk type and the
printer), `Png/Parse.lean` (the parser), `Png/Crc32.lean` (the
CRC-32), and `Png/Header.lean` (the IHDR header value, its
reader and printer, and the file level read). The well
formedness rules (`Spec.WFChunk`, `Spec.WF`, `Spec.WFHeader`,
`Spec.WFFull`), the written out table of allowed pairs
(`Spec.allowedPairs`), and four bytes big endian
(`Spec.bigEndian4`) give the statements their meaning and no
code uses them, so they are part of the specification, in
`Spec/Defs.lean`, and a change to them voids an approval. The
command line tool in `Main.lean` calls `Png.parse`,
`Png.print`, and `Png.parseFile` directly, the same functions
the theorems are about.

## What is not proved

- That the well formedness rules (`WF`, `WFHeader`, `WFFull`, and the table of allowed pairs) and the byte layout the layout theorems state (`Spec.print_layout`, `Spec.printIhdr_layout`, with `Spec.bigEndian4`) are the PNG specification's. The proofs tie each reader to its rule and each printer to the stated layout exactly, but that the rule and the layout say what the PNG specification says is a reading: `SPEC.md` states it in words, and the tests compare the readers against a strict oracle written in the harness from those rules, and the header read against libpng, file by file, the two accepted inputs of `Spec.lean` among them. Where libpng and this reader differ, the test record names each difference and the rule behind it.
- That the CRC-32 here is the standard one. `Spec.print_layout` states the chunk layout with the code's own CRC-32 function (`Png.Crc32.crc32`), and no theorem says that function is the standard CRC-32. The round trip needs no such fact, since the parser and the printer compute the same function. The differential tests against Python zlib's `crc32` are what tie this function to the standard. Two statements pin it on single inputs: `Spec.reads_real_file_header` holds only if the function gives the three CRCs that zlib wrote into that file, and `Spec.rejects_bad_crc` holds only if it does not give the wrong CRC that its file carries.
- Anything inside a chunk's data past the IHDR header. The data of every other chunk type is opaque here. IDAT data is not inflated. No pixel is ever decoded.
- Chunk order past the first and last, except for IHDR. Which types may appear, how many times, and in what order between IHDR and IEND is not checked, with one exception: the file level read (`header`) refuses a second IHDR chunk. The chunk layer (`parse`) does not, and reads it as an ordinary chunk. So an indexed colour file with no PLTE chunk is accepted, where libpng refuses it.
- A chunk of type IEND that carries data. The PNG specification gives IEND no data, but this reader reads such a chunk as an ordinary chunk, at both layers: the file is accepted when an IEND chunk with no data ends it, and refused when none does. libpng refuses such a chunk when it comes before IDAT, and reads a file that ends in one, with a warning. `SPEC.md` states this reading, and the test record names both differences.

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
  in the tests, and libpng as the oracle for the header read
  where it is installed. The results file names the versions
  used.
- The line handling in `Main.lean` (splitting a request
  line, reading decimal codes) and the text of the `header`
  answer. The tests drive them, and no proof covers them.
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
   the mutations, the header sections, the accepted inputs
   stated in `Spec.lean`, and the libpng comparison of the
   header read, with counts, named
   differences, and any failures written to
   `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool build
   clean, and `lake env lean Proofs/Verify.lean` prints the
   axiom list for the headline theorems and for every theorem
   `comparator.json` names.
4. Read `SPEC.md` against the PNG specification and check
   the pinned readings are the ones you want.
