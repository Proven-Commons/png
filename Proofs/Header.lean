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

  The header round trip is `parseIhdr_print`. The file level
  claim is `parseFile_print`: a fully well formed document
  with header `hd` (chunk layer well formed, first chunk the
  printed form of the well formed header `hd`) prints and reads
  back whole, and the header the read returns is `hd` itself.
-/

import Png
import Proofs.RoundTrip

namespace Png.Proofs

open Png

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
  rw [if_neg (by simp : ¬ (([] : List UInt8) ≠ []))]
  rw [if_neg (by omega : ¬ (w = 0 ∨ hh = 0))]
  rw [if_neg (by omega : ¬ (w ≥ 2147483648 ∨ hh ≥ 2147483648))]
  rw [if_neg (by decide : ¬ ((0 : UInt8) ≠ 0 ∨ (0 : UInt8) ≠ 0))]
  rw [if_neg hnl, if_pos hpair]

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
      rw [if_neg h0, if_neg h2, if_neg h3, if_neg h4, if_neg h6]
    simp only [pairAllowed, decide_eq_true_eq, hdep]
    simp [allowedPairs, h0, h2, h3, h4, h6]

/-- The table, in the byte form the parser uses: the check on
    two bytes holds if and only if the pair of their values is
    in the written out list. -/
theorem checkPair_iff (ct bd : UInt8) :
    checkPair ct bd = true ↔ (ct.toNat, bd.toNat) ∈ allowedPairs :=
  pairAllowed_iff ct.toNat bd.toNat

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
