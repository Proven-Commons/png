/-
  The PNG chunk data model and the canonical printer. This slice
  reads the chunk layer only: it does not decode pixels, and it
  does not inflate IDAT data.

  A file is the eight byte signature, then a list of chunks. A
  chunk holds a type, which is four bytes, and its data. On the
  wire a chunk is a length (four bytes, big endian, counting the
  data bytes only), the four type bytes, the data, and a CRC-32
  (four bytes, big endian) over the type bytes and the data
  together.

  The printer writes the signature, then each chunk with its
  length, type, data, and a CRC it computes as it goes. Its output
  is the canonical form the tests compare against: a file this
  parser accepts is reprinted byte for byte.
-/

import Png.Crc32

namespace Png

/-- The eight signature bytes every PNG file starts with. -/
def signature : List UInt8 := [137, 80, 78, 71, 13, 10, 26, 10]

/-- One chunk: a type, held as its four bytes, and the data. -/
structure Chunk where
  t1 : UInt8
  t2 : UInt8
  t3 : UInt8
  t4 : UInt8
  data : List UInt8
  deriving DecidableEq, Repr

/-- The type bytes of a chunk, as a list. -/
def Chunk.typeBytes (c : Chunk) : List UInt8 := [c.t1, c.t2, c.t3, c.t4]

/-- A document: a list of chunks. -/
abbrev Doc := List Chunk

/-- A chunk type byte is an ASCII letter, A to Z or a to z. -/
def isLetter (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)

/-- The type bytes of the first chunk of every PNG file. -/
def ihdrType : List UInt8 := [73, 72, 68, 82]

/-- The type bytes of the last chunk of every PNG file. -/
def iendType : List UInt8 := [73, 69, 78, 68]

/-- The IEND chunk itself: type IEND, no data. -/
def iendChunk : Chunk := ⟨73, 69, 78, 68, []⟩

/-- Is this chunk the IEND chunk: type IEND and no data? A chunk
    of type IEND that carries data is an ordinary chunk here. -/
def isIEND (c : Chunk) : Bool :=
  c.typeBytes = iendType && c.data.isEmpty

/-- A value as four bytes, big endian. The value is taken modulo
    2^32; callers only pass values below that. -/
def be32 (n : Nat) : List UInt8 :=
  [ (n / 16777216).toUInt8, (n / 65536).toUInt8, (n / 256).toUInt8, n.toUInt8 ]

/-- The value of four bytes read big endian. -/
def u32 (a b c d : UInt8) : Nat :=
  a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat

/-- The CRC-32 of a chunk's type bytes and data, as it is stored
    in the file. -/
def chunkCrc (c : Chunk) : UInt32 :=
  Crc32.crc32 (c.typeBytes ++ c.data)

/-- One chunk in printed form: its length, its type bytes, its
    data, and its CRC. -/
def printChunk (c : Chunk) : List UInt8 :=
  be32 c.data.length ++ c.typeBytes ++ c.data ++ be32 (chunkCrc c).toNat

/-- A document in printed form: the signature, then the chunks in
    order. -/
def print (doc : Doc) : List UInt8 :=
  signature ++ doc.flatMap printChunk

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

end Png
