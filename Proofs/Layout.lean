/-
  The byte layout: the bytes the chunk printer and the header
  printer write, stated with `Spec.bigEndian4`, the four bytes of
  a number most significant first, and the type bytes and the
  letter test the chunk rules use. The round trips and their
  converses tie each reader to its printer; these tie each
  printer to the layout of the PNG specification, so that a
  printer and a reader that agreed on some other layout (the
  height before the width, say) would not meet the statements.

  The code writes four byte numbers with `be32`, which takes each
  byte with `Nat.toUInt8`; `bigEndian4` writes them with
  `UInt8.ofNat` of the base 256 digit. `be32_eq_bigEndian4` says
  the two agree on every number.
-/

import Png
import Spec.Defs

namespace Png.Proofs

open Png Spec

/-- A number's byte is the byte of its last base 256 digit. -/
theorem toUInt8_eq_ofNat_mod (n : Nat) : n.toUInt8 = UInt8.ofNat (n % 256) := by
  apply UInt8.toNat_inj.mp
  simp [Nat.toUInt8]

/-- The code's four bytes big endian are the specification's. -/
theorem be32_eq_bigEndian4 (n : Nat) : be32 n = bigEndian4 n := by
  unfold be32 bigEndian4
  rw [toUInt8_eq_ofNat_mod (n / 16777216), toUInt8_eq_ofNat_mod (n / 65536),
    toUInt8_eq_ofNat_mod (n / 256), toUInt8_eq_ofNat_mod n]

/-- The chunk layout: the signature, then each chunk as its
    length, its four type bytes in order, its data, and its
    CRC-32, the length and the CRC four bytes big endian. -/
theorem print_layout (doc : Doc) :
    print doc = [137, 80, 78, 71, 13, 10, 26, 10] ++
      doc.flatMap (fun c =>
        bigEndian4 c.data.length ++ [c.t1, c.t2, c.t3, c.t4] ++ c.data ++
          bigEndian4 (Crc32.crc32 ([c.t1, c.t2, c.t3, c.t4] ++ c.data)).toNat) := by
  unfold print signature
  congr 1
  apply congrArg (List.flatMap · doc)
  funext c
  simp only [printChunk, chunkCrc, Chunk.typeBytes, be32_eq_bigEndian4]

/-- The IHDR layout: width, height, four bytes big endian each,
    then bit depth, colour type, compression zero, filter zero,
    and interlace. -/
theorem printIhdr_layout (h : Ihdr) :
    printIhdr h = bigEndian4 h.width ++ bigEndian4 h.height ++
      [h.bitDepth, h.colorType, 0, 0, h.interlace] := by
  simp only [printIhdr, be32_eq_bigEndian4]

/-- The letter test: A to Z, or a to z, by the byte's value. -/
theorem isLetter_iff (b : UInt8) :
    isLetter b = true ↔
      (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ (97 ≤ b.toNat ∧ b.toNat ≤ 122) := by
  simp [isLetter, UInt8.le_iff_toNat_le]

/-- The IEND chunk test: type bytes I, E, N, D, and no data. -/
theorem isIEND_iff (c : Chunk) :
    isIEND c = true ↔ [c.t1, c.t2, c.t3, c.t4] = [73, 69, 78, 68] ∧ c.data = [] := by
  unfold isIEND iendType Chunk.typeBytes
  rw [Bool.and_eq_true, List.isEmpty_iff]
  exact and_congr_left fun _ => decide_eq_true_iff

end Png.Proofs
