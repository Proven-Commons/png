/-
  Soundness: the converse of the round trips. Whatever the
  readers accept is the printed form of a well formed value, and
  the value they return is that value.

  - `parse_sound`: a file the chunk parser accepts is the printed
    form of the chunk list it returns, and that list is well
    formed (`WF`).
  - `parseFile_sound`: a file the file level read accepts is the
    printed form of the chunk list it returns, and that list is
    fully well formed with the header it returns (`WFFull`).

  With the round trips `parse_print` and `parseFile_print`, each
  reader is pinned exactly (`parse_iff`, `parseFile_iff`): it
  accepts a file if and only if the file is the printed form of a
  well formed value, and then returns that value. So every rule
  the well formedness predicates state is a rejection rule the
  reader keeps: a file that breaks one is refused.

  The steps follow the readers: four bytes read and printed again
  are the same bytes (`be32_u32`, in `Proofs/Header.lean`); one
  chunk the chunk reader accepts is a well formed chunk printed in
  front of the rest of the input; a list of chunks read to IEND is
  the printed list, ending in the IEND chunk; then the signature
  and the IHDR check at the top level, and the header on top.
-/

import Png
import Spec.Defs
import Proofs.RoundTrip
import Proofs.Header

namespace Png.Proofs

open Png Spec

/-- Four bytes the reader takes off the front of the input are
    the printed form of the value it returns, and that value is
    below 2^32. -/
theorem get4_sound {bs : List UInt8} {n : Nat} {r : List UInt8}
    (h : get4 bs = some (n, r)) : n < 4294967296 ∧ be32 n ++ r = bs := by
  unfold get4 at h
  split at h
  · rename_i a b c d rest
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨u32_lt a b c d, by rw [be32_u32]; rfl⟩
  · cases h

/-- One chunk the chunk reader accepts is a well formed chunk,
    and the input was its printed form followed by the rest the
    reader returns. -/
theorem parseChunk_sound {bs : List UInt8} {c : Chunk} {r : List UInt8}
    (h : parseChunk bs = some (c, r)) : WFChunk c ∧ printChunk c ++ r = bs := by
  unfold parseChunk at h
  split at h
  · cases h
  rename_i len rest1 hg
  obtain ⟨_, hbs⟩ := get4_sound hg
  split at h
  · cases h
  rename_i hlen
  split at h
  · rename_i t1 t2 t3 t4 rest2
    split at h
    · rename_i hletters
      dsimp only at h
      split at h
      · cases h
      rename_i hdl
      split at h
      · cases h
      rename_i crcVal rest3 hg2
      split at h
      · rename_i hcrc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨_, hrest2⟩ := get4_sound hg2
        have hl : (rest2.take len).length = len := Decidable.of_not_not hdl
        simp only [Bool.and_eq_true] at hletters
        obtain ⟨⟨⟨l1, l2⟩, l3⟩, l4⟩ := hletters
        refine ⟨⟨l1, l2, l3, l4, ?_⟩, ?_⟩
        · show (rest2.take len).length < 2147483648
          rw [hl]
          exact Nat.lt_of_not_le hlen
        rw [← hbs]
        show be32 (rest2.take len).length ++ [t1, t2, t3, t4] ++ rest2.take len
          ++ be32 (Crc32.crc32 ([t1, t2, t3, t4] ++ rest2.take len)).toNat ++ rest3
          = be32 len ++ (t1 :: t2 :: t3 :: t4 :: rest2)
        rw [hl, ← hcrc, List.append_assoc, List.append_assoc, List.append_assoc,
          hrest2, List.take_append_drop]
        rfl
      · cases h
    · cases h
  · cases h

/-- A chunk the reader takes as the IEND chunk is the IEND
    chunk. -/
theorem isIEND_eq {c : Chunk} (h : isIEND c = true) : c = iendChunk := by
  obtain ⟨t1, t2, t3, t4, data⟩ := c
  simp only [isIEND, Chunk.typeBytes, iendType, Bool.and_eq_true, decide_eq_true_eq,
    List.cons.injEq, and_true, List.isEmpty_iff] at h
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
  rfl

/-- A chunk list the list reader accepts, at any fuel, is the
    printed form of the list, every chunk in it is well formed,
    and it ends in the IEND chunk with no IEND chunk before. -/
theorem parseChunks_sound : ∀ (n : Nat) (bs : List UInt8) (cs : Doc),
    parseChunks n bs = some cs →
    cs.flatMap printChunk = bs ∧ (∀ c ∈ cs, WFChunk c) ∧
    ∃ pre : Doc, cs = pre ++ [iendChunk] ∧ ∀ c ∈ pre, isIEND c = false := by
  intro n
  induction n with
  | zero => intro bs cs h; cases h
  | succ n ih =>
    intro bs cs h
    rw [parseChunks_succ] at h
    split at h
    · cases h
    rename_i c rest hc
    obtain ⟨hwf, hpr⟩ := parseChunk_sound hc
    split at h
    · rename_i hend
      split at h
      · rename_i hrest
        simp only [Option.some.injEq] at h
        subst h hrest
        refine ⟨?_, ?_, [], ?_, ?_⟩
        · simpa using hpr
        · intro x hx
          rw [List.mem_singleton.mp hx]
          exact hwf
        · rw [isIEND_eq hend]
          rfl
        · intro x hx
          cases hx
      · cases h
    · rename_i hnend
      split at h
      · cases h
      rename_i cs' hcs
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hflat, hall, pre, hpre, hnot⟩ := ih rest cs' hcs
      refine ⟨?_, ?_, c :: pre, ?_, ?_⟩
      · rw [List.flatMap_cons, hflat]
        exact hpr
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hwf
        · exact hall x hx
      · rw [hpre]
        rfl
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Bool.eq_false_iff.mpr hnend
        · exact hnot x hx

/-- The chunk parser is sound: a file it accepts is the printed
    form of the chunk list it returns, and that list is well
    formed. -/
theorem parse_sound {bs : List UInt8} {doc : Doc} (h : parse bs = some doc) :
    WF doc ∧ print doc = bs := by
  unfold parse at h
  split at h
  · rename_i hsig
    split at h
    · rename_i c cs hcs
      split at h
      · rename_i hhead
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hflat, hall, pre, hpre, hnot⟩ := parseChunks_sound _ _ _ hcs
        obtain ⟨htype, hlen⟩ := hhead
        have hprint : print (c :: cs) = bs := by
          show signature ++ (c :: cs).flatMap printChunk = bs
          rw [hflat, ← hsig]
          exact List.take_append_drop 8 bs
        cases pre with
        | nil =>
          have hc : c = iendChunk := (List.cons.inj hpre).1
          rw [hc] at htype
          exact absurd htype (by decide)
        | cons head mid =>
          have hpre' : c :: cs = head :: (mid ++ [iendChunk]) := hpre
          have hc : c = head := (List.cons.inj hpre').1
          subst hc
          exact ⟨⟨c, mid, hpre, htype, hlen, hall, hnot⟩, hprint⟩
      · cases h
    · cases h
  · cases h

/-- The chunk parser, exactly: it accepts the file `bs` with the
    chunk list `doc` if and only if `doc` is well formed and `bs`
    is its printed form. -/
theorem parse_iff (bs : List UInt8) (doc : Doc) :
    parse bs = some doc ↔ WF doc ∧ print doc = bs :=
  ⟨parse_sound, fun ⟨hwf, hp⟩ => hp ▸ parse_print hwf⟩

/-- The file level read is sound: a file it accepts, with header
    `hd` and chunk list `doc`, is the printed form of `doc`, and
    `doc` is fully well formed with header `hd`. So the header it
    returns is the one the first chunk's data is the printed form
    of, and no later chunk is an IHDR chunk. -/
theorem parseFile_sound {bs : List UInt8} {hd : Ihdr} {doc : Doc}
    (h : parseFile bs = some (hd, doc)) : WFFull hd doc ∧ print doc = bs := by
  unfold parseFile at h
  split at h
  · rename_i d hd'
    cases hh : headerOf d with
    | none =>
      rw [hh] at h
      cases h
    | some x =>
      rw [hh] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hx, rfl⟩ := h
      rw [hx] at hh
      obtain ⟨hwf, hpr⟩ := parse_sound hd'
      obtain ⟨head, mid, hdoc, htype, -, hall, hnot⟩ := hwf
      rw [hdoc] at hh
      have hh' : (if (mid ++ [iendChunk]).any isIHDR then none
          else parseIhdr head.data) = some hd := hh
      split at hh'
      · cases hh'
      rename_i hany
      obtain ⟨hwfh, hprint⟩ := parseIhdr_sound hh'
      refine ⟨⟨head, mid, hdoc, htype, hprint.symm, hwfh, hall, hnot, ?_⟩, hpr⟩
      intro c hc hct
      apply hany
      rw [List.any_eq_true]
      exact ⟨c, List.mem_append_left _ hc, by simp [isIHDR, hct]⟩
  · cases h

/-- The file level read, exactly: it accepts the file `bs` with
    header `hd` and chunk list `doc` if and only if `doc` is fully
    well formed with header `hd` and `bs` is its printed form. -/
theorem parseFile_iff (bs : List UInt8) (hd : Ihdr) (doc : Doc) :
    parseFile bs = some (hd, doc) ↔ WFFull hd doc ∧ print doc = bs :=
  ⟨parseFile_sound, fun ⟨hwf, hp⟩ => hp ▸ parseFile_print hwf⟩

end Png.Proofs
