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
  both above zero and below 2^31 (the PNG specification caps
  each of them at 2^31 - 1), the compression and filter bytes are zero,
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

  The file level read also turns a file away when a chunk after
  the first has type IHDR: the PNG specification allows one IHDR
  chunk, and it comes first. The chunk layer of slice 1 does not
  look at this; only the file level read does.

  The written out table of allowed pairs, and well formedness of
  a header and of a whole document, give the statements their
  meaning and no code uses them, so they are part of the
  specification, in `Spec/Defs.lean`.
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

/-- Does this bit depth go with this colour type? The two
    arguments are the file's bytes. -/
def checkPair (ct bd : UInt8) : Bool := pairAllowed ct.toNat bd.toNat

/-- The 13 IHDR data bytes of a header: width and height big
    endian, then bit depth, colour type, compression zero,
    filter zero, interlace. -/
def printIhdr (h : Ihdr) : List UInt8 :=
  be32 h.width ++ be32 h.height ++ [h.bitDepth, h.colorType, 0, 0, h.interlace]

/-- Read 13 bytes as a header. Anything but exactly 13 bytes is
    rejected, and so is a header that breaks any of the rules at
    the top of this file: a width or height of zero or of 2^31
    or more, a nonzero
    compression or filter byte, an interlace byte above 1, or a
    bit depth the colour type does not allow. -/
def parseIhdr (bs : List UInt8) : Option Ihdr :=
  match bs with
  | w1 :: w2 :: w3 :: w4 :: h1 :: h2 :: h3 :: h4 :: bd :: ct :: comp :: filt :: int :: rest =>
    if rest ≠ [] then none
    else if u32 w1 w2 w3 w4 = 0 ∨ u32 h1 h2 h3 h4 = 0 then none
    else if u32 w1 w2 w3 w4 ≥ 2147483648 ∨ u32 h1 h2 h3 h4 ≥ 2147483648 then none
    else if comp ≠ 0 ∨ filt ≠ 0 then none
    else if int > 1 then none
    else if checkPair ct bd then
      some ⟨u32 w1 w2 w3 w4, u32 h1 h2 h3 h4, bd, ct, int⟩
    else none
  | _ => none

/-- Is this chunk an IHDR chunk, by its type bytes? -/
def isIHDR (c : Chunk) : Bool := decide (c.typeBytes = ihdrType)

/-- The decoded header of a chunk list: the first chunk's data
    read as a header. It is `none` when there is no first chunk,
    when any later chunk is also of type IHDR (the PNG
    specification allows one IHDR chunk, and it comes first), or
    when the first chunk's data does not read as a header. -/
def headerOf (doc : Doc) : Option Ihdr :=
  match doc with
  | c :: rest => if rest.any isIHDR then none else parseIhdr c.data
  | [] => none

/-- Read a whole file at both layers: the chunk list of slice 1,
    and the header decoded from the first chunk's data. A file
    whose first chunk is not a valid IHDR, in the slice 2 sense,
    or that holds a second IHDR chunk, is rejected here even when
    slice 1 accepts it. -/
def parseFile (bs : List UInt8) : Option (Ihdr × Doc) :=
  match parse bs with
  | some doc => (headerOf doc).map fun h => (h, doc)
  | none => none

end Png
