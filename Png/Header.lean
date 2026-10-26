/-
  Slice 2: the IHDR header, decoded. Slice 1 reads the chunk
  layer and checks that the first chunk has type IHDR and 13
  data bytes; it does not look inside those bytes. This file
  reads them.

  The 13 bytes hold: the width and the height, four bytes each,
  big endian; then the bit depth, the colour type, the
  compression method, the filter method, and the interlace
  method, one byte each.

  The compression and filter bytes carry no choice in PNG: each
  must be zero. So the header value does not hold them. They are
  checked on reading and written as zero on printing. The
  interlace byte is 0 (no interlace) or 1 (Adam7), and is held.

  A header is accepted only when the width and the height are
  both above zero, the compression and filter bytes are zero,
  the interlace byte is 0 or 1, and the bit depth is one the
  colour type allows. The allowed pairs are the ones the PNG
  specification names:

    colour type 0 (greyscale):        depths 1, 2, 4, 8, 16
    colour type 2 (truecolour):       depths 8, 16
    colour type 3 (indexed colour):   depths 1, 2, 4, 8
    colour type 4 (greyscale, alpha): depths 8, 16
    colour type 6 (truecolour, alpha): depths 8, 16

  Colour types other than 0, 2, 3, 4, 6 are not PNG colour
  types, and allow no depth.
-/

import Png.Parse

namespace Png

/-- The decoded IHDR header: width and height as numbers, the
    bit depth, the colour type, and the interlace method as
    bytes. The compression and filter bytes are not held: each
    is zero in every accepted file, and printing writes zero. -/
structure Ihdr where
  width : Nat
  height : Nat
  bitDepth : UInt8
  colorType : UInt8
  interlace : UInt8
  deriving DecidableEq, Repr

/-- The bit depths a colour type allows, by the colour type's
    number. A number that is not a PNG colour type allows none. -/
def allowedDepths (ct : Nat) : List Nat :=
  if ct = 0 then [1, 2, 4, 8, 16]
  else if ct = 2 then [8, 16]
  else if ct = 3 then [1, 2, 4, 8]
  else if ct = 4 then [8, 16]
  else if ct = 6 then [8, 16]
  else []

/-- Does this depth go with this colour type? The two numbers
    are the byte values. -/
def pairAllowed (ct bd : Nat) : Bool :=
  decide (bd ∈ allowedDepths ct)

/-- The allowed (colour type, bit depth) pairs, written out in
    full. The checker above is built from the per-type table;
    the proof in `Proofs/Header.lean` shows the two agree on
    every colour type byte and every bit depth byte. -/
def allowedPairs : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 4), (0, 8), (0, 16),
   (2, 8), (2, 16),
   (3, 1), (3, 2), (3, 4), (3, 8),
   (4, 8), (4, 16),
   (6, 8), (6, 16)]

/-- Does this bit depth go with this colour type? The two
    arguments are the file's bytes. -/
def checkPair (ct bd : UInt8) : Bool := pairAllowed ct.toNat bd.toNat

/-- A header is well formed when the width and the height are
    above zero and below 2^32, the interlace byte is 0 or 1, and
    the bit depth is one the colour type allows. -/
def WFHeader (h : Ihdr) : Prop :=
  0 < h.width ∧ h.width < 4294967296 ∧
  0 < h.height ∧ h.height < 4294967296 ∧
  (h.interlace = 0 ∨ h.interlace = 1) ∧
  checkPair h.colorType h.bitDepth = true

/-- The 13 IHDR data bytes of a header: width and height big
    endian, then bit depth, colour type, compression zero,
    filter zero, interlace. -/
def printIhdr (h : Ihdr) : List UInt8 :=
  be32 h.width ++ be32 h.height ++ [h.bitDepth, h.colorType, 0, 0, h.interlace]

/-- Read 13 bytes as a header. Anything but exactly 13 bytes is
    rejected, and so is a header that breaks any of the rules at
    the top of this file: a width or height of zero, a nonzero
    compression or filter byte, an interlace byte above 1, or a
    bit depth the colour type does not allow. -/
def parseIhdr (bs : List UInt8) : Option Ihdr :=
  match bs with
  | w1 :: w2 :: w3 :: w4 :: h1 :: h2 :: h3 :: h4 :: bd :: ct :: comp :: filt :: int :: rest =>
    if rest ≠ [] then none
    else if u32 w1 w2 w3 w4 = 0 ∨ u32 h1 h2 h3 h4 = 0 then none
    else if comp ≠ 0 ∨ filt ≠ 0 then none
    else if int > 1 then none
    else if checkPair ct bd then
      some ⟨u32 w1 w2 w3 w4, u32 h1 h2 h3 h4, bd, ct, int⟩
    else none
  | _ => none

/-- The decoded header of a chunk list: the first chunk's data
    read as a header, or `none` when there is no first chunk or
    its data does not read as one. -/
def headerOf (doc : Doc) : Option Ihdr :=
  match doc with
  | c :: _ => parseIhdr c.data
  | [] => none

/-- Read a whole file at both layers: the chunk list of slice 1,
    and the header decoded from the first chunk's data. A file
    whose first chunk is not a valid IHDR, in the slice 2 sense,
    is rejected here even when slice 1 accepts it. -/
def parseFile (bs : List UInt8) : Option (Ihdr × Doc) :=
  match parse bs with
  | some doc => (headerOf doc).map fun h => (h, doc)
  | none => none

/-- A document is fully well formed when it is well formed at
    the chunk layer (the `WF` of slice 1), its first chunk's
    data is the printed form of some header, and that header is
    well formed. Stated with the witnesses out, in the shape of
    `WF`. -/
def WFFull (doc : Doc) : Prop :=
  ∃ (hd : Ihdr) (head : Chunk) (mid : List Chunk),
    doc = head :: mid ++ [iendChunk] ∧
    head.typeBytes = ihdrType ∧ head.data = printIhdr hd ∧
    WFHeader hd ∧
    (∀ c ∈ doc, WFChunk c) ∧
    (∀ c ∈ head :: mid, isIEND c = false)

end Png
