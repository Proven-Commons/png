/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the SHA-256 it had then. The proofs live in `Proofs`
  (`Proofs/SpecProofs.lean`); `lake comparator` checks that each one
  proves exactly the statement written here. The `sorry` below is
  expected in this file only.

  The statements use only the definitions in `Png/Value.lean`,
  `Png/Parse.lean`, `Png/Crc32.lean`, and `Png/Header.lean`, the
  code under proof named in `bar.toml`. No definition of their own
  is needed, so this project has no `Spec/Defs.lean`.
-/

import Png

open Png

/-! ## The round trips and the table

The statements the slice stands on. Each one is the statement of
the proved theorem of the same shape in `Proofs/RoundTrip.lean`
or `Proofs/Header.lean`, over the same well formedness
predicates, `Png.WF`, `Png.WFHeader`, and `Png.WFFull`. -/

/-- Parsing the printed form of a well formed chunk list gives
    the list back. So a printer that wrote nothing, or wrote
    something shorter, fails this statement. -/
theorem Spec.parse_print {doc : Doc} (h : WF doc) :
    parse (print doc) = some doc := sorry

/-- Reading the printed bytes of a well formed IHDR header gives
    the header back. -/
theorem Spec.parseIhdr_print (h : Ihdr) (hwf : WFHeader h) :
    parseIhdr (printIhdr h) = some h := sorry

/-- The depth checker agrees with the written out table of
    allowed (colour type, bit depth) pairs on every byte pair. -/
theorem Spec.checkPair_iff (ct bd : UInt8) :
    checkPair ct bd = true ↔
      (ct.toNat, bd.toNat) ∈ allowedPairs := sorry

/-- Printing a fully well formed document with header `hd` and
    reading it back at both layers gives back that header, `hd`
    itself, and the document. So a reader that returned some
    other header, a fixed one or one with the width and height
    swapped, fails this statement. -/
theorem Spec.parseFile_print {hd : Ihdr} {doc : Doc} (h : WFFull hd doc) :
    parseFile (print doc) = some (hd, doc) := sorry

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
theorem Spec.rejects_bad_signature :
    (parse ([118, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72,
      68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 0, 180, 244, 174,
      198, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file whose IHDR chunk carries a CRC that does not match
    its type and data is refused. -/
theorem Spec.rejects_bad_crc :
    (parse ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72,
      68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 0, 180, 244, 174,
      57, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file cut short inside its first chunk is refused: the
    first twenty bytes of a valid file, and no more. -/
theorem Spec.rejects_truncated_input :
    (parse ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72,
      68, 82, 0, 0, 0, 4] : List UInt8)).isSome = false := sorry

/-- A file whose first chunk holds 12 data bytes is refused: an
    IHDR chunk holds 13. -/
theorem Spec.rejects_first_chunk_length_12 :
    (parse ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 12, 73, 72,
      68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 240, 122, 129,
      218, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a width of zero is refused. -/
theorem Spec.rejects_zero_width :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 0, 0, 0, 0, 3, 8, 6, 0, 0, 0, 189, 31,
      14, 188, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a height of zero is refused. -/
theorem Spec.rejects_zero_height :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 0, 8, 6, 0, 0, 0, 50, 96,
      220, 104, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a width of 2^31 is refused: the width stays
    below 2^31. -/
theorem Spec.rejects_width_at_cap :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 128, 0, 0, 0, 0, 0, 0, 3, 8, 6, 0, 0, 0, 29, 117,
      43, 171, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a height of 2^31 is refused: the height stays
    below 2^31. -/
theorem Spec.rejects_height_at_cap :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 128, 0, 0, 0, 8, 6, 0, 0, 0, 84, 53,
      220, 39, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with bit depth 4 on colour type 2 is refused: that
    colour type allows depths 8 and 16 only. -/
theorem Spec.rejects_illegal_depth :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 4, 2, 0, 0, 0, 254, 102,
      212, 144, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with colour type 1 is refused: 1 is not a PNG colour
    type, and allows no bit depth. -/
theorem Spec.rejects_unknown_colour_type :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 1, 0, 0, 0, 41, 35,
      150, 127, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with an interlace byte of 2 is refused: the byte is
    0 or 1. -/
theorem Spec.rejects_unknown_interlace :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 2, 90, 250,
      207, 234, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a compression byte of 1 is refused: the only
    compression method is 0. -/
theorem Spec.rejects_nonzero_compression :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 1, 0, 0, 181, 54,
      196, 241, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- A file with a filter byte of 1 is refused: the only filter
    method is 0. -/
theorem Spec.rejects_nonzero_filter :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 1, 0, 173, 239,
      159, 135, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := sorry

/-- The header reader refuses anything but exactly 13 bytes:
    here a valid header's first 12 bytes. -/
theorem Spec.rejects_header_wrong_length :
    (parseIhdr ([0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0]
      : List UInt8)).isSome = false := sorry
