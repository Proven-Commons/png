/-
  The slice 2 proofs: the IHDR header round trip, the exactness
  of the (colour type, bit depth) table, and the file level
  round trip that joins the header to the chunk layer of
  slice 1.

  The table claim is `pairAllowed_iff`, with its byte form
  `checkPair_iff`: the checker's answer agrees with the written
  out list of allowed pairs for every colour type number and
  every bit depth number. Colour types are bytes and bit depths
  are bytes, so the numbers 0 to 255 are the whole of both, and
  the proof settles the question for all of them: it splits on
  the five colour types the PNG specification names, and in
  each case the two sides come down to the same list of depths;
  for every other colour type number both sides are empty. No
  case is left to computation over the whole grid.

  The header round trip is `parseIhdr_print`, and its converse
  is `parseIhdr_sound`: a header the reader accepts is well
  formed, and the bytes it read are its printed form. The file
  level claim is `parseFile_print`: a fully well formed document
  with header `hd` (chunk layer well formed, first chunk the
  printed form of the well formed header `hd`, no second IHDR)
  prints and reads back whole, and the header the read returns
  is `hd` itself. Its converse, `parseFile_sound`, is in
  `Png/Proofs/Sound.lean`.
-/

import Png
import Png.Spec.Defs
import Png.Proofs.RoundTrip

namespace Png.Proofs

open Png Png.Spec

/-- One step of the header reader, stated for rewriting: 13
    bytes at the front of the input, with whatever follows. -/
theorem parseIhdr_step (w1 w2 w3 w4 h1 h2 h3 h4 bd ct comp filt int : UInt8)
    (rest : List UInt8) :
    parseIhdr (w1 :: w2 :: w3 :: w4 :: h1 :: h2 :: h3 :: h4
      :: bd :: ct :: comp :: filt :: int :: rest) =
      if rest ≠ [] then none
      else if u32 w1 w2 w3 w4 = 0 ∨ u32 h1 h2 h3 h4 = 0 then none
      else if u32 w1 w2 w3 w4 ≥ 2147483648 ∨ u32 h1 h2 h3 h4 ≥ 2147483648 then none
      else if comp ≠ 0 ∨ filt ≠ 0 then none
      else if int > 1 then none
      else if checkPair ct bd then
        some ⟨u32 w1 w2 w3 w4, u32 h1 h2 h3 h4, bd, ct, int⟩
      else none := rfl

/-- The printed form of a header is 13 bytes. -/
theorem printIhdr_length (h : Ihdr) : (printIhdr h).length = 13 := by
  simp [printIhdr, be32]

/-- The table, exactly: a depth goes with a colour type under
    the checker if and only if the pair is in the written out
    list of allowed pairs. Stated for all numbers, so in
    particular for every colour type byte and every bit depth
    byte. -/
theorem pairAllowed_iff : ∀ n m : Nat,
    pairAllowed n m = true ↔ (n, m) ∈ allowedPairs := by
  intro n m
  by_cases h0 : n = 0
  · subst h0
    simp only [pairAllowed, decide_eq_true_eq]
    show m ∈ [1, 2, 4, 8, 16] ↔ (0, m) ∈ allowedPairs
    simp [allowedPairs]
  by_cases h2 : n = 2
  · subst h2
    simp only [pairAllowed, decide_eq_true_eq]
    show m ∈ [8, 16] ↔ (2, m) ∈ allowedPairs
    simp [allowedPairs]
  by_cases h3 : n = 3
  · subst h3
    simp only [pairAllowed, decide_eq_true_eq]
    show m ∈ [1, 2, 4, 8] ↔ (3, m) ∈ allowedPairs
    simp [allowedPairs]
  by_cases h4 : n = 4
  · subst h4
    simp only [pairAllowed, decide_eq_true_eq]
    show m ∈ [8, 16] ↔ (4, m) ∈ allowedPairs
    simp [allowedPairs]
  by_cases h6 : n = 6
  · subst h6
    simp only [pairAllowed, decide_eq_true_eq]
    show m ∈ [8, 16] ↔ (6, m) ∈ allowedPairs
    simp [allowedPairs]
  · have hdep : allowedDepths n = [] := by
      unfold allowedDepths
      rw [ite_eq_right h0, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h6]
    simp only [pairAllowed, decide_eq_true_eq, hdep]
    simp [allowedPairs, h0, h2, h3, h4, h6]

/-- The table, in the byte form the parser uses: the check on
    two bytes holds if and only if the pair of their values is
    in the written out list. -/
theorem checkPair_iff (ct bd : UInt8) :
    checkPair ct bd = true ↔ (ct.toNat, bd.toNat) ∈ allowedPairs :=
  pairAllowed_iff ct.toNat bd.toNat

/-- The header round trip: reading the printed bytes of a well
    formed header gives the header back. -/
theorem parseIhdr_print (h : Ihdr) (hwf : WFHeader h) :
    parseIhdr (printIhdr h) = some h := by
  obtain ⟨w, hh, bd, ct, il⟩ := h
  obtain ⟨hw1, hw2, hh1, hh2, hil, hpair⟩ := hwf
  have hw1' : 0 < w := hw1
  have hh1' : 0 < hh := hh1
  have hw2' : w < 2147483648 := hw2
  have hh2' : hh < 2147483648 := hh2
  have hnl : ¬ (il > 1) := by
    rcases hil with rfl | rfl <;> decide
  have e : printIhdr ⟨w, hh, bd, ct, il⟩ =
      (w / 16777216).toUInt8 :: (w / 65536).toUInt8
      :: (w / 256).toUInt8 :: w.toUInt8
      :: (hh / 16777216).toUInt8 :: (hh / 65536).toUInt8
      :: (hh / 256).toUInt8 :: hh.toUInt8
      :: bd :: ct :: 0 :: 0 :: il :: [] := rfl
  rw [e, parseIhdr_step, u32_be32 w (by omega), u32_be32 hh (by omega)]
  rw [ite_eq_right (by simp : ¬ (([] : List UInt8) ≠ []))]
  rw [ite_eq_right (by omega : ¬ (w = 0 ∨ hh = 0))]
  rw [ite_eq_right (by omega : ¬ (w ≥ 2147483648 ∨ hh ≥ 2147483648))]
  rw [ite_eq_right (by decide : ¬ ((0 : UInt8) ≠ 0 ∨ (0 : UInt8) ≠ 0))]
  rw [ite_eq_right hnl, ite_eq_left ((checkPair_iff ct bd).mpr hpair)]

/-- Four bytes read big endian and printed again are the same
    four bytes. -/
theorem be32_u32 (a b c d : UInt8) : be32 (u32 a b c d) = [a, b, c, d] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  simp only [be32, u32, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> rw [toUInt8_toNat] <;> omega

/-- Four bytes read big endian give a value below 2^32. -/
theorem u32_lt (a b c d : UInt8) : u32 a b c d < 4294967296 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  simp only [u32]
  omega

/-- A byte that is not above 1 is 0 or 1. -/
theorem uint8_le_one {i : UInt8} (h : ¬ i > 1) : i = 0 ∨ i = 1 := by
  have h' : ¬ (1 : UInt8).toNat < i.toNat :=
    fun x => h (UInt8.lt_iff_toNat_lt.mpr x)
  have : i.toNat = 0 ∨ i.toNat = 1 := by simp at h'; omega
  rcases this with e | e
  · left; exact UInt8.toNat_inj.mp (by simpa using e)
  · right; exact UInt8.toNat_inj.mp (by simpa using e)

/-- The header reader is sound: a header it accepts is well
    formed, and the bytes it read are that header's printed form.
    So every rejection rule holds of what it accepts: the width
    and the height are above zero and below 2^31, the interlace
    byte is 0 or 1, the depth is one the colour type allows (by
    `checkPair_iff`, a pair of the written out table), there were
    exactly 13 bytes, and the compression and filter bytes were
    zero, since `printIhdr` writes zero there. -/
theorem parseIhdr_sound {bs : List UInt8} {h : Ihdr}
    (hp : parseIhdr bs = some h) : WFHeader h ∧ printIhdr h = bs := by
  unfold parseIhdr at hp
  split at hp
  · rename_i w1 w2 w3 w4 h1 h2 h3 h4 bd ct comp filt int rest
    split at hp
    · cases hp
    rename_i hr
    split at hp
    · cases hp
    rename_i hz
    split at hp
    · cases hp
    rename_i hb
    split at hp
    · cases hp
    rename_i hc
    split at hp
    · cases hp
    rename_i hi
    split at hp
    · rename_i hpair
      cases hp
      have hr' : rest = [] := Decidable.of_not_not hr
      have hcomp : comp = 0 := Decidable.of_not_not (not_or.mp hc).1
      have hfilt : filt = 0 := Decidable.of_not_not (not_or.mp hc).2
      subst hr' hcomp hfilt
      refine ⟨⟨(by omega : 0 < u32 w1 w2 w3 w4),
        (by omega : u32 w1 w2 w3 w4 < 2147483648),
        (by omega : 0 < u32 h1 h2 h3 h4),
        (by omega : u32 h1 h2 h3 h4 < 2147483648),
        uint8_le_one hi, (checkPair_iff ct bd).mp hpair⟩, ?_⟩
      show be32 (u32 w1 w2 w3 w4) ++ be32 (u32 h1 h2 h3 h4)
        ++ [bd, ct, 0, 0, int] = _
      rw [be32_u32, be32_u32]
      rfl
    · cases hp
  · cases hp

/-- The header reader, exactly: it accepts the bytes `bs` with
    header `h` if and only if `h` is well formed and `bs` is its
    printed form. -/
theorem parseIhdr_iff (bs : List UInt8) (h : Ihdr) :
    parseIhdr bs = some h ↔ WFHeader h ∧ printIhdr h = bs :=
  ⟨parseIhdr_sound, fun ⟨hwf, hp⟩ => hp ▸ parseIhdr_print h hwf⟩

/-- A fully well formed document is well formed at the chunk
    layer. -/
theorem wfFull_wf {hd : Ihdr} {doc : Doc} (h : WFFull hd doc) : WF doc := by
  obtain ⟨head, mid, hdoc, htype, hdata, -, hall, hnot, -⟩ := h
  exact ⟨head, mid, hdoc, htype,
    by rw [hdata]; exact printIhdr_length hd, hall, hnot⟩

/-- The file level round trip: printing a fully well formed
    document with header `hd` and reading the file back at both
    layers gives back `hd` itself and the document. -/
theorem parseFile_print {hd : Ihdr} {doc : Doc} (h : WFFull hd doc) :
    parseFile (print doc) = some (hd, doc) := by
  have hwf : WF doc := wfFull_wf h
  obtain ⟨head, mid, hdoc, htype, hdata, hwfhd, hall, hnot, hone⟩ := h
  have hany : (mid ++ [iendChunk]).any isIHDR = false := by
    rw [List.any_eq_false]
    intro c hc
    rcases List.mem_append.mp hc with hm | hm
    · simpa [isIHDR] using hone c hm
    · rw [List.mem_singleton.mp hm]
      decide
  unfold parseFile
  rw [parse_print hwf]
  show (headerOf doc).map (fun x => (x, doc)) = some (hd, doc)
  rw [hdoc]
  simp [headerOf, hany, hdata, parseIhdr_print hd hwfhd]

end Png.Proofs
