/-
  The definitions the statements in `Spec.lean` use besides the
  code under proof: four bytes big endian (`bigEndian4`), the
  IEND chunk as a value, well formedness at
  the chunk layer (`WFChunk`, `WF`), the written out table of
  allowed (colour type, bit depth) pairs, well formedness of a
  header (`WFHeader`), and full well formedness of a document
  with its header (`WFFull`). They give the statements their
  meaning, and the readers and printers do not use them, so they
  are part of the specification, with `Spec.lean` and `SPEC.md`,
  not of the code (`bar.toml` lists the code). A change here
  changes the spec hash, and so voids an approval.
-/

import Png

namespace Spec

open Png

/-- A number as four bytes, most significant first (big endian):
    its base 256 digits, from the 2^24 place down to the units.
    The PNG specification writes every four byte number this way:
    chunk lengths, CRCs, and the width and height in IHDR. A
    number of 2^32 or more keeps only its lowest four digits;
    the numbers PNG writes are below 2^31. -/
def bigEndian4 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- The IEND chunk itself: type bytes I, E, N, D, in ASCII, and
    no data. The fields are named, so the value does not depend
    on the order in which `Png.Chunk` declares them. -/
def iendChunk : Chunk := { t1 := 73, t2 := 69, t3 := 78, t4 := 68, data := [] }

/-- The per-chunk part of well formedness: each type byte is an
    ASCII letter, and the data length stays below 2^31, as the PNG
    specification bounds chunk lengths. -/
def WFChunk (c : Chunk) : Prop :=
  isLetter c.t1 = true ∧ isLetter c.t2 = true ∧
  isLetter c.t3 = true ∧ isLetter c.t4 = true ∧
  c.data.length < 2147483648

/-- A document is well formed when it is a first chunk, then any
    middle chunks, then the IEND chunk; the first chunk has type
    IHDR and 13 data bytes; no chunk before the last is the IEND
    chunk; and every chunk is a well formed chunk. -/
def WF (doc : Doc) : Prop :=
  ∃ (head : Chunk) (mid : List Chunk),
    doc = head :: mid ++ [iendChunk] ∧
    head.typeBytes = ihdrType ∧ head.data.length = 13 ∧
    (∀ c ∈ doc, WFChunk c) ∧
    (∀ c ∈ head :: mid, isIEND c = false)

/-- The allowed (colour type, bit depth) pairs, written out in
    full, as the PNG specification's table gives them. The
    checker in `Png/Header.lean` is built from a per-type table;
    `Spec.checkPair_iff` says the two agree on every colour type
    byte and every bit depth byte. -/
def allowedPairs : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 4), (0, 8), (0, 16),
   (2, 8), (2, 16),
   (3, 1), (3, 2), (3, 4), (3, 8),
   (4, 8), (4, 16),
   (6, 8), (6, 16)]

/-- A header is well formed when the width and the height are
    above zero and below 2^31, the interlace byte is 0 or 1, and
    the (colour type, bit depth) pair is in the table above. -/
def WFHeader (h : Ihdr) : Prop :=
  0 < h.width ∧ h.width < 2147483648 ∧
  0 < h.height ∧ h.height < 2147483648 ∧
  (h.interlace = 0 ∨ h.interlace = 1) ∧
  (h.colorType.toNat, h.bitDepth.toNat) ∈ allowedPairs

/-- A document is fully well formed, with header `hd`, when it
    is well formed at the chunk layer (as in `WF`), its first
    chunk's data is the printed form of `hd`, `hd` is well
    formed, and no chunk after the first has type IHDR. The
    header is a parameter, not a witness, so a statement over
    `WFFull hd doc` can say which header a reader must return.
    Stated in the shape of `WF`. -/
def WFFull (hd : Ihdr) (doc : Doc) : Prop :=
  ∃ (head : Chunk) (mid : List Chunk),
    doc = head :: mid ++ [iendChunk] ∧
    head.typeBytes = ihdrType ∧ head.data = printIhdr hd ∧
    WFHeader hd ∧
    (∀ c ∈ doc, WFChunk c) ∧
    (∀ c ∈ head :: mid, isIEND c = false) ∧
    (∀ c ∈ mid, c.typeBytes ≠ ihdrType)

end Spec
