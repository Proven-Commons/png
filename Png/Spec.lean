/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and
  `bar.toml` records the SHA-256 it had then. The proofs live in
  `Png.Proofs` (`Png/Proofs/SpecProofs.lean`); `lake comparator`
  checks that each one proves exactly the statement written here.
  The `sorry` below is expected in this file only.

  The statements use the definitions in `Png/Value.lean`,
  `Png/Parse.lean`, `Png/Crc32.lean`, and `Png/Header.lean`, the
  code under proof named in `bar.toml`, and the well formedness
  predicates, the written out table of allowed pairs, and four
  bytes big endian (`Png.Spec.WF`, `Png.Spec.WFHeader`,
  `Png.Spec.WFFull`, `Png.Spec.allowedPairs`,
  `Png.Spec.bigEndian4`, and what they use), which are in
  `Png/Spec/Defs.lean`. That file is part of the specification
  too.
-/

import Png
import Png.Spec.Defs

open Png Png.Spec

/-! ## The round trips and the table

The statements the slice stands on. Each one is the statement of
the proved theorem of the same shape in `Png/Proofs/RoundTrip.lean`
or `Png/Proofs/Header.lean`, over the same well formedness
predicates, `Png.Spec.WF`, `Png.Spec.WFHeader`, and `Png.Spec.WFFull`. -/

/-- Parsing the printed form of a well formed chunk list gives
    the list back. So a printer that wrote nothing, or wrote
    something shorter, fails this statement. -/
theorem Png.Spec.parse_print {doc : Doc} (h : WF doc) :
    parse (print doc) = some doc := sorry

/-- Reading the printed bytes of a well formed IHDR header gives
    the header back. -/
theorem Png.Spec.parseIhdr_print (h : Ihdr) (hwf : WFHeader h) :
    parseIhdr (printIhdr h) = some h := sorry

/-- The depth checker agrees with the written out table of
    allowed (colour type, bit depth) pairs on every byte pair. -/
theorem Png.Spec.checkPair_iff (ct bd : UInt8) :
    checkPair ct bd = true ↔
      (ct.toNat, bd.toNat) ∈ allowedPairs := sorry

/-- Printing a fully well formed document with header `hd` and
    reading it back at both layers gives back that header, `hd`
    itself, and the document. This holds relative to the printer:
    the first chunk's data is `printIhdr hd`. So a reader that
    returned some other header than the one `printIhdr` wrote, a
    fixed one or one with the width and height swapped, fails
    this statement. A change that swapped them in both the
    printer and the reader would still meet it; that change fails
    `Png.Spec.printIhdr_layout`, which fixes the bytes the printer
    writes, and the accepted inputs below. -/
theorem Png.Spec.parseFile_print {hd : Ihdr} {doc : Doc} (h : WFFull hd doc) :
    parseFile (print doc) = some (hd, doc) := sorry

/-! ## What the readers accept

The converse of the round trips: each reader accepts only the
printed form of a well formed value, and returns that value.
With the round trips above, this pins each reader exactly, so
every rule the well formedness predicates state is a rule the
reader keeps when it refuses a file. -/

/-- A file the chunk parser accepts is the printed form of the
    chunk list it returns, and that list is well formed. -/
theorem Png.Spec.parse_sound {bs : List UInt8} {doc : Doc}
    (h : parse bs = some doc) : WF doc ∧ print doc = bs := sorry

/-- A header the header reader accepts is well formed, and the
    bytes it read are that header's printed form. So a width or
    height of zero or of 2^31 or more, a nonzero compression or
    filter byte, an interlace byte above 1, a depth the colour
    type does not allow, and any length but 13 are all refused. -/
theorem Png.Spec.parseIhdr_sound {bs : List UInt8} {h : Ihdr}
    (hp : parseIhdr bs = some h) : WFHeader h ∧ printIhdr h = bs := sorry

/-- A file the file level read accepts, with header `hd` and
    chunk list `doc`, is the printed form of `doc`, and `doc` is
    fully well formed with header `hd`: its first chunk's data is
    the printed form of `hd`, and no later chunk is an IHDR
    chunk. -/
theorem Png.Spec.parseFile_sound {bs : List UInt8} {hd : Ihdr} {doc : Doc}
    (h : parseFile bs = some (hd, doc)) :
    WFFull hd doc ∧ print doc = bs := sorry

/-! ## The byte layout

The round trips and their converses tie each reader to its
printer, but say nothing of the bytes the printer writes: a
printer and a reader that both put the height before the width,
or both wrote lengths least significant byte first, would meet
them. The statements here fix those bytes: the chunk layout, the
13 bytes of the header, the letters a chunk type may use, the
type bytes the rules compare, and the type bytes of IHDR and
IEND. With the round trips and the
converses above, they fix what each reader accepts and returns
for every input: the chunk parser accepts exactly the bytes
`Png.Spec.print_layout` gives for a well formed chunk list, and the
header reader accepts exactly the bytes `Png.Spec.printIhdr_layout`
gives for a well formed header, and returns that header. The one
function they leave as the code has it is the CRC-32. -/

/-- The bytes `print` writes for a chunk list: the eight
    signature bytes, then each chunk in order as its data length
    in four bytes big endian, its four type bytes, its data, and
    the CRC-32 of its type bytes and data in four bytes big
    endian. This is the chunk layout of the PNG specification.
    The CRC-32 is the function in `Png/Crc32.lean`. -/
theorem Png.Spec.print_layout (doc : Doc) :
    print doc = [137, 80, 78, 71, 13, 10, 26, 10] ++
      doc.flatMap (fun c =>
        bigEndian4 c.data.length ++ [c.t1, c.t2, c.t3, c.t4] ++ c.data ++
          bigEndian4 (Crc32.crc32 ([c.t1, c.t2, c.t3, c.t4] ++ c.data)).toNat) := sorry

/-- The 13 bytes `printIhdr` writes for a header, in order: the
    width in four bytes big endian, the height in four bytes big
    endian, the bit depth, the colour type, a compression byte of
    zero, a filter byte of zero, and the interlace byte. This is
    the IHDR layout of the PNG specification. With
    `Png.Spec.parseIhdr_sound`, the width the header reader returns
    is the value of the first four bytes it read, and the height
    the value of the next four. -/
theorem Png.Spec.printIhdr_layout (h : Ihdr) :
    printIhdr h = bigEndian4 h.width ++ bigEndian4 h.height ++
      [h.bitDepth, h.colorType, 0, 0, h.interlace] := sorry

/-- The letter test the chunk rules use (`Png.Spec.WFChunk`, and the
    parser) holds of the ASCII letters, A to Z (65 to 90) and a
    to z (97 to 122), and of no other byte. -/
theorem Png.Spec.isLetter_iff (b : UInt8) :
    isLetter b = true ↔
      (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ (97 ≤ b.toNat ∧ b.toNat ≤ 122) := sorry

/-- The type bytes the chunk rules require of the first chunk
    are I, H, D, R, in ASCII. -/
theorem Png.Spec.ihdrType_eq : ihdrType = [73, 72, 68, 82] := sorry

/-- The type bytes the chunk rules compare with `ihdrType`
    (`Png.Spec.WF`, `Png.Spec.WFFull`, and the readers) are a chunk's four
    type bytes, in the order the chunk printer writes them. -/
theorem Png.Spec.typeBytes_eq (c : Chunk) :
    c.typeBytes = [c.t1, c.t2, c.t3, c.t4] := sorry

/-- The IEND chunk, at which reading stops and which ends a well
    formed chunk list, is a chunk with type bytes I, E, N, D, in
    ASCII, and no data. -/
theorem Png.Spec.isIEND_iff (c : Chunk) :
    isIEND c = true ↔ [c.t1, c.t2, c.t3, c.t4] = [73, 69, 78, 68] ∧ c.data = [] := sorry

/-! ## Accepted inputs

Two inputs the readers accept, with the header each returns. The
width and the height differ in both, so a reader that swapped
them fails each statement. The test harness reads both inputs
from this file and checks the header each statement gives
against its own reading of the bytes, against the tool's `header`
answer, and, where libpng is installed, against libpng's. -/

/-- A real PNG file is read with its own header: 4 by 3, bit
    depth 8, colour type 6 (truecolour with alpha), no interlace.
    The file has an IHDR chunk, an IDAT chunk holding the
    zlib compressed scanlines of random pixels, and IEND. It is
    the 4 by 3 file among the test suite's real files. The test
    harness checks that zlib inflates its IDAT data to three
    scanlines of that width, and has libpng decode it in full. -/
theorem Png.Spec.reads_real_file_header :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 0, 180, 244,
      174, 198, 0, 0, 0, 62, 73, 68, 65, 84, 120, 156, 1, 51, 0, 204,
      255, 0, 248, 207, 45, 4, 205, 181, 169, 174, 98, 138, 255, 174,
      190, 27, 111, 191, 0, 254, 105, 254, 66, 198, 209, 157, 111,
      200, 221, 165, 145, 35, 173, 191, 75, 0, 216, 164, 157, 244,
      188, 239, 173, 101, 28, 78, 104, 79, 114, 243, 122, 31, 237,
      218, 28, 90, 62, 15, 23, 102, 0, 0, 0, 0, 73, 69, 78, 68, 174,
      66, 96, 130] : List UInt8)).map Prod.fst =
      some { width := 4, height := 3, bitDepth := 8, colorType := 6, interlace := 0 } := sorry

/-- The header reader reads the 13 bytes of a 1920 by 1080
    header, bit depth 8, colour type 2 (truecolour), no
    interlace, as width 1920 (the first four bytes, 0, 0, 7, 128)
    and height 1080 (the next four, 0, 0, 4, 56). -/
theorem Png.Spec.reads_header_1920x1080 :
    parseIhdr ([0, 0, 7, 128, 0, 0, 4, 56, 8, 2, 0, 0, 0]
      : List UInt8) =
      some { width := 1920, height := 1080, bitDepth := 8, colorType := 2, interlace := 0 } := sorry

/-! ## Refused inputs

Single inputs the reader refuses, one for each headline rule of
`SPEC.md`. Each input is one of the named rejection cases in the
test harness: the chunk layer cases stand as the harness builds
them for its `parse` requests, and the header cases are whole
files whose CRCs are recomputed, as the harness builds them for
its `header` requests, so the refusal is for the header rule
itself. The differential tests cover these rules on many more
inputs; these statements pin them so a reader of the
specification can check each rule against one concrete case. -/

/-- A file whose first signature byte is wrong is refused. -/
theorem Png.Spec.rejects_bad_signature :
    (parse ([118, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72,
      68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 0, 180, 244, 174,
      198, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file whose IHDR chunk carries a CRC that does not match
    its type and data is refused. -/
theorem Png.Spec.rejects_bad_crc :
    (parse ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72,
      68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 0, 180, 244, 174,
      57, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file cut short inside its first chunk is refused: the
    first twenty bytes of a valid file, and no more. -/
theorem Png.Spec.rejects_truncated_input :
    (parse ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72,
      68, 82, 0, 0, 0, 4] : List UInt8)).isSome = false := sorry

/-- A file whose first chunk holds 12 data bytes is refused: an
    IHDR chunk holds 13. -/
theorem Png.Spec.rejects_first_chunk_length_12 :
    (parse ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 12, 73, 72,
      68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 240, 122, 129,
      218, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a width of zero is refused. -/
theorem Png.Spec.rejects_zero_width :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 0, 0, 0, 0, 3, 8, 6, 0, 0, 0, 189, 31,
      14, 188, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a height of zero is refused. -/
theorem Png.Spec.rejects_zero_height :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 0, 8, 6, 0, 0, 0, 50, 96,
      220, 104, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a width of 2^31 is refused: the width stays
    below 2^31. -/
theorem Png.Spec.rejects_width_at_cap :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 128, 0, 0, 0, 0, 0, 0, 3, 8, 6, 0, 0, 0, 29, 117,
      43, 171, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a height of 2^31 is refused: the height stays
    below 2^31. -/
theorem Png.Spec.rejects_height_at_cap :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 128, 0, 0, 0, 8, 6, 0, 0, 0, 84, 53,
      220, 39, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with bit depth 4 on colour type 2 is refused: that
    colour type allows depths 8 and 16 only. -/
theorem Png.Spec.rejects_illegal_depth :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 4, 2, 0, 0, 0, 254, 102,
      212, 144, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with colour type 1 is refused: 1 is not a PNG colour
    type, and allows no bit depth. -/
theorem Png.Spec.rejects_unknown_colour_type :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 1, 0, 0, 0, 41, 35,
      150, 127, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with an interlace byte of 2 is refused: the byte is
    0 or 1. -/
theorem Png.Spec.rejects_unknown_interlace :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 2, 90, 250,
      207, 234, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a compression byte of 1 is refused: the only
    compression method is 0. -/
theorem Png.Spec.rejects_nonzero_compression :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 1, 0, 0, 181, 54,
      196, 241, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a filter byte of 1 is refused: the only filter
    method is 0. -/
theorem Png.Spec.rejects_nonzero_filter :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 1, 0, 173, 239,
      159, 135, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a second IHDR chunk is refused by the file level
    read: here a 1 by 1 IHDR, then a 2 by 2 IHDR, then IDAT and
    IEND. The PNG specification allows one IHDR chunk. -/
theorem Png.Spec.rejects_second_ihdr :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 1, 0, 0, 0, 1, 8, 2, 0, 0, 0, 144, 119,
      83, 222, 0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 2, 0, 0, 0, 2,
      8, 2, 0, 0, 0, 253, 212, 154, 115, 0, 0, 0, 12, 73, 68, 65, 84,
      120, 156, 99, 96, 96, 96, 0, 0, 0, 4, 0, 1, 246, 23, 56, 85, 0,
      0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- The header reader refuses anything but exactly 13 bytes:
    here a valid header's first 12 bytes. -/
theorem Png.Spec.rejects_header_wrong_length :
    (parseIhdr ([0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0]
      : List UInt8)).isSome = false := sorry
