# png: a PNG chunk parser and printer, with a proved round trip

A PNG chunk parser and printer in Lean. It reads the chunk layer of a PNG file: the signature, then each chunk's length, type, data, and CRC-32 check. Slice 2 adds a decoder for the IHDR header: the width, height, bit depth, colour type, and interlace method held in the first chunk's 13 data bytes, checked against the validity rules of the PNG specification. It does not decode pixels, and it does not inflate IDAT data. The main claims are proved: parsing what the printer wrote returns the same chunk list, reading the printed bytes of a well formed header returns the header, and the bit depth table the checker uses is exactly the table the specification names. The tests run the parser against real PNG files built with Python's zlib and against a strict oracle written from the rules; see `tests/TEST-RESULTS.md` for the counts.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, and no statement file (`Spec.lean`) has been added by a reviewer, so this is not verified.

## What is proved

The definitions are in `Png/Value.lean` (the chunk type, the printer, and the well-formedness rules), `Png/Parse.lean` (the parser), `Png/Crc32.lean` (the CRC-32), and `Png/Header.lean` (the IHDR header value, its reader and printer, and the file level read). The proofs are in `Proofs/RoundTrip.lean` and `Proofs/Header.lean`.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed chunk list gives the list back. | `Png.Proofs.parse_print` |
| Reading back one printed chunk, with any bytes after it, gives the chunk and those bytes untouched. | `Png.Proofs.parseChunk_printChunk` |
| Four bytes printed from a value below 2^32 read back as the value. | `Png.Proofs.u32_be32` |
| Reading the printed bytes of a well formed IHDR header gives the header back. | `Png.Proofs.parseIhdr_print` |
| The depth checker agrees with the written out table of allowed (colour type, bit depth) pairs on every byte pair. | `Png.Proofs.checkPair_iff` |
| Printing a fully well formed document and reading it back at both layers gives the document back, header included. | `Png.Proofs.parseFile_print` |

A chunk list is well formed when it is a first chunk, then any middle chunks, then the IEND chunk; the first chunk has type IHDR and 13 data bytes; no chunk before the last is the IEND chunk; every chunk type is four ASCII letters; and every data length is below 2^31. A header is well formed when its width and height are above zero and below 2^32, its interlace byte is 0 or 1, and its bit depth is one its colour type allows. Each of these theorems checks against two of the standard axioms (`propext`, `Quot.sound`), which a reader can confirm with `#print axioms` on the theorem's name.

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- That the parser accepts every file the rules in `SPEC.md` allow, and rejects every file they forbid. The round trip does not need either, so neither is proved. The test suite checks that behaviour instead, and the results file records the outcome, including any failure.
- That the CRC-32 here is the standard one. The round trip needs no such fact, since the parser and the printer compute the same function. The differential tests against Python zlib's `crc32` are what tie this function to the standard.
- That the header reader accepts every header the rules in `SPEC.md` allow, and rejects every header they forbid, beyond what the round trip and the table theorem cover. The tests check that behaviour instead: hand built headers for every colour type and allowed depth, the full colour type and depth enumeration against the table, and the rejection cases.
- Anything inside a chunk's data past the IHDR header. The data of every other chunk type is opaque here. IDAT data is not inflated. No pixel is ever decoded.
- Chunk order past the first and last. Which types may appear, how many times, and in what order between IHDR and IEND is not checked. A chunk of type IEND that carries data is read as an ordinary chunk.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- Python's standard library, including zlib, as the oracle in the tests. The results file names the versions used.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "parse 137,80,78,71,13,10,26,10,0,0,0,13,73,72,68,82,0,0,0,1,0,0,0,1,8,2,0,0,0,144,119,83,222,0,0,0,0,73,69,78,68,174,66,96,130" | .lake/build/bin/png
```

That request is a whole minimal PNG file as byte codes: the signature, an IHDR chunk for a 1 by 1 image, and IEND. The answer is `ok:` followed by the same codes, since the file is valid and reprints byte for byte. A file the parser rejects, such as the single code `120`, answers `none`. A malformed request answers `error`. The same file asked through `header`, with the word `header` in place of `parse`, answers `ok:49,120,49,32,100,56,32,116,50,32,105,48`: the codes of the text `1x1 d8 t2 i0`, the decoded header fields. See `SPEC.md` for the full protocol.

## Re-check it

Needs Linux, elan, and Python 3.11 or later.

```
lake build
grep -rn "sorry" --include="*.lean" Png Proofs Main.lean Png.lean Proofs.lean
python3 tests/run_tests.py
```

The grep should print nothing: there is no `sorry` anywhere. The test script rebuilds the tool, builds real PNG files with Python zlib, runs hand-built chunk cases, runs the differential tests with a fixed seed, and writes the counts to `tests/TEST-RESULTS.md`.
