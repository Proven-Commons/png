/-
  The PNG chunk parser. It reads a list of bytes and returns the
  chunk list, or `none` when the bytes break any of the rules the
  plan states:

  - The first eight bytes are the PNG signature.
  - Each chunk reads a length (four bytes, big endian, the count
    of data bytes, and below 2^31), a type (four bytes, each an
    ASCII letter), that many data bytes, and a CRC (four bytes,
    big endian) equal to the CRC-32 of the type bytes and the data.
  - A chunk whose length runs past the bytes that remain, or whose
    CRC does not match, turns the whole file away. There is no
    partial read.
  - The first chunk has type IHDR and a data length of 13.
  - Reading stops at the IEND chunk, which must carry no data,
    and no bytes may follow it. Running out of bytes before an
    IEND chunk is a rejection.

  `parseChunks` takes a fuel count, one unit per chunk. The top
  level `parse` passes one more than the length of the input,
  which is always enough, since every chunk takes at least twelve
  bytes. A hostile input is rejected, never looped on.
-/

import Png.Value

namespace Png

/-- Read four bytes as a big endian value, with the rest of the
    input. Fewer than four bytes gives `none`. -/
def get4 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: c :: d :: rest => some (u32 a b c d, rest)
  | _ => none

/-- Read one chunk from the front of the input. Returns the chunk
    and the input after it, or `none` when the chunk is cut short,
    its length is 2^31 or more, a type byte is not an ASCII letter,
    or its CRC does not match. -/
def parseChunk (bs : List UInt8) : Option (Chunk × List UInt8) :=
  match get4 bs with
  | none => none
  | some (len, rest1) =>
    if len ≥ 2147483648 then none
    else
      match rest1 with
      | t1 :: t2 :: t3 :: t4 :: rest2 =>
        if isLetter t1 && isLetter t2 && isLetter t3 && isLetter t4 then
          let data := rest2.take len
          if data.length ≠ len then none
          else
            match get4 (rest2.drop len) with
            | none => none
            | some (crcVal, rest3) =>
              if crcVal = (Crc32.crc32 ([t1, t2, t3, t4] ++ data)).toNat then
                some (⟨t1, t2, t3, t4, data⟩, rest3)
              else none
        else none
      | _ => none

/-- Read chunks until the IEND chunk. The IEND chunk must be the
    last thing in the input: any byte after it is a rejection, and
    so is running out of input before it. -/
def parseChunks : Nat → List UInt8 → Option Doc
  | 0, _ => none
  | fuel + 1, bs =>
    match parseChunk bs with
    | none => none
    | some (c, rest) =>
      if isIEND c then
        if rest = [] then some [c] else none
      else
        match parseChunks fuel rest with
        | none => none
        | some cs => some (c :: cs)

/-- Parse a whole file: the signature, then the chunks, with the
    first chunk checked as IHDR with a data length of 13. -/
def parse (bs : List UInt8) : Option Doc :=
  if bs.take 8 = signature then
    match parseChunks (bs.length + 1) (bs.drop 8) with
    | some (c :: cs) =>
      if c.typeBytes = ihdrType ∧ c.data.length = 13 then some (c :: cs)
      else none
    | _ => none
  else none

end Png
