/-
  The round trip proof: for every well formed document, parsing
  its printed form gives the same chunk list back.

  The statement proved here is `parse_print`. A matching statement
  in a spec file still has to be added by a reviewer, so this file
  builds on its own, in the same shape as the csv proofs.

  The steps: four printed bytes read back as the value they were
  printed from; one printed chunk reads back as the chunk, with
  whatever follows it untouched; a printed list of chunks ending
  in IEND reads back whole; then the signature and the IHDR check
  at the top level. The CRC needs no lemma here: the parser and
  the printer compute the same function of the same bytes, so the
  check between them closes by computation of the two sides to a
  common value.
-/

import Png
import Png.Spec.Defs

namespace Png.Proofs

open Png Png.Spec

/-- A byte printed from a number reads back as the number modulo
    256. -/
theorem toUInt8_toNat (n : Nat) : (n.toUInt8).toNat = n % 256 := rfl

/-- Four bytes printed from a value below 2^32 read back as the
    value. -/
theorem u32_be32 (n : Nat) (h : n < 4294967296) :
    u32 (n / 16777216).toUInt8 (n / 65536).toUInt8 (n / 256).toUInt8
      n.toUInt8 = n := by
  simp only [u32, toUInt8_toNat]
  omega

/-- Reading four bytes off the front of a printed value and what
    follows it. -/
theorem get4_be32 (n : Nat) (h : n < 4294967296) (r : List UInt8) :
    get4 (be32 n ++ r) = some (n, r) := by
  show get4 ((n / 16777216).toUInt8 :: (n / 65536).toUInt8 ::
    (n / 256).toUInt8 :: n.toUInt8 :: r) = some (n, r)
  show some (u32 (n / 16777216).toUInt8 (n / 65536).toUInt8
    (n / 256).toUInt8 n.toUInt8, r) = some (n, r)
  rw [u32_be32 n h]

/-- The printed length of one chunk: twelve bytes of framing plus
    its data. -/
theorem printChunk_length (c : Chunk) :
    (printChunk c).length = c.data.length + 12 := by
  simp [printChunk, Chunk.typeBytes, be32, List.length_append]

/-- A printed document is at least as long as its chunk count. -/
theorem print_length (doc : Doc) : doc.length ≤ (print doc).length := by
  have h1 : ∀ cs : Doc, cs.length ≤ (cs.flatMap printChunk).length := by
    intro cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have hc := printChunk_length c
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have h2 := h1 doc
  simp only [print, List.length_append]
  omega

/-- One step of the chunk reader, stated for rewriting: a chunk
    whose eight header bytes sit at the front of the input. -/
theorem parseChunk_step (b1 b2 b3 b4 t1 t2 t3 t4 : UInt8)
    (rest : List UInt8) :
    parseChunk (b1 :: b2 :: b3 :: b4 :: t1 :: t2 :: t3 :: t4 :: rest) =
      if u32 b1 b2 b3 b4 ≥ 2147483648 then none
      else if isLetter t1 && isLetter t2 && isLetter t3 && isLetter t4 then
        if (rest.take (u32 b1 b2 b3 b4)).length ≠ u32 b1 b2 b3 b4 then none
        else
          match get4 (rest.drop (u32 b1 b2 b3 b4)) with
          | none => none
          | some (crcVal, rest3) =>
            if crcVal
                = (Crc32.crc32 ([t1, t2, t3, t4]
                    ++ rest.take (u32 b1 b2 b3 b4))).toNat then
              some (⟨t1, t2, t3, t4, rest.take (u32 b1 b2 b3 b4)⟩, rest3)
            else none
      else none := rfl

/-- Reading back one printed chunk: followed by any bytes, the
    reader returns the chunk and those bytes untouched. -/
theorem parseChunk_printChunk (c : Chunk) (r : List UInt8)
    (hwf : WFChunk c) :
    parseChunk (printChunk c ++ r) = some (c, r) := by
  obtain ⟨h1, h2, h3, h4, hlen⟩ := hwf
  have hlen32 : c.data.length < 4294967296 := by omega
  have hcrc32 : (chunkCrc c).toNat < 4294967296 :=
    UInt32.toNat_lt_size _
  have e : printChunk c ++ r
      = (c.data.length / 16777216).toUInt8
        :: (c.data.length / 65536).toUInt8
        :: (c.data.length / 256).toUInt8 :: c.data.length.toUInt8
        :: c.t1 :: c.t2 :: c.t3 :: c.t4
        :: ((c.data ++ be32 (chunkCrc c).toNat) ++ r) := rfl
  rw [e, parseChunk_step, u32_be32 c.data.length hlen32]
  have hge : ¬ c.data.length ≥ 2147483648 := by omega
  rw [ite_eq_right hge]
  have hletters : (isLetter c.t1 && isLetter c.t2 && isLetter c.t3
      && isLetter c.t4) = true := by
    simp [h1, h2, h3, h4]
  rw [ite_eq_left hletters]
  rw [List.append_assoc, List.take_left, List.drop_left,
    get4_be32 _ hcrc32]
  rw [ite_eq_right (by simp : ¬ c.data.length ≠ c.data.length)]
  show (if (chunkCrc c).toNat
      = (Crc32.crc32 ([c.t1, c.t2, c.t3, c.t4] ++ c.data)).toNat
    then some (⟨c.t1, c.t2, c.t3, c.t4, c.data⟩, r)
    else none) = some (c, r)
  rw [ite_eq_left (show (chunkCrc c).toNat
    = (Crc32.crc32 ([c.t1, c.t2, c.t3, c.t4] ++ c.data)).toNat from rfl)]

/-- One step of the chunk list reader, stated for rewriting. -/
theorem parseChunks_succ (n : Nat) (bs : List UInt8) :
    parseChunks (n + 1) bs =
      match parseChunk bs with
      | none => none
      | some (c, rest) =>
        if isIEND c then
          if rest = [] then some [c] else none
        else
          match parseChunks n rest with
          | none => none
          | some cs => some (c :: cs) := rfl

/-- Reading back a printed list of chunks that ends with the
    IEND chunk, at any fuel that covers one more than the count of
    chunks before it. -/
theorem parseChunks_printChunks : ∀ (pre : Doc) (last : Chunk)
    (n : Nat),
    (∀ c ∈ pre, WFChunk c) → (∀ c ∈ pre, isIEND c = false) →
    WFChunk last → isIEND last = true →
    pre.length + 1 ≤ n →
    parseChunks n ((pre ++ [last]).flatMap printChunk)
      = some (pre ++ [last]) := by
  intro pre
  induction pre with
  | nil =>
    intro last n _ _ hwf hlast hlen
    cases n with
    | zero => simp at hlen
    | succ n =>
      have hpc := parseChunk_printChunk last [] hwf
      simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at hpc ⊢
      rw [parseChunks_succ, hpc]
      simp [hlast]
  | cons c pre ih =>
    intro last n hall hnot hwf hlast hlen
    have hc : WFChunk c := hall c (by simp)
    have hcnot : isIEND c = false := hnot c (by simp)
    have hall' : ∀ x ∈ pre, WFChunk x :=
      fun x hx => hall x (List.mem_cons_of_mem c hx)
    have hnot' : ∀ x ∈ pre, isIEND x = false :=
      fun x hx => hnot x (List.mem_cons_of_mem c hx)
    cases n with
    | zero => simp at hlen
    | succ n =>
      have hlen' : pre.length + 1 ≤ n := by
        simp only [List.length_cons] at hlen
        omega
      have hI := ih last n hall' hnot' hwf hlast hlen'
      have hpc := parseChunk_printChunk c
        ((pre ++ [last]).flatMap printChunk) hc
      have hform : ((c :: pre) ++ [last]).flatMap printChunk
          = printChunk c ++ (pre ++ [last]).flatMap printChunk := by
        simp [List.flatMap_cons]
      rw [hform, parseChunks_succ, hpc]
      simp only [hcnot, Bool.false_eq_true, ite_false, hI,
        List.cons_append]

/-- The signature at the front of a printed document. -/
theorem take_signature (doc : Doc) :
    (print doc).take 8 = signature := by
  show (signature ++ doc.flatMap printChunk).take signature.length
    = signature
  exact List.take_left

/-- The bytes after the signature of a printed document. -/
theorem drop_signature (doc : Doc) :
    (print doc).drop 8 = doc.flatMap printChunk := by
  show (signature ++ doc.flatMap printChunk).drop signature.length
    = doc.flatMap printChunk
  exact List.drop_left

/-- The round trip: parsing the printed form of a well formed
    document gives the document back. A document is well formed
    when its first chunk is IHDR with 13 data bytes, its last is
    the IEND chunk, no earlier chunk is the IEND chunk, every
    type is four ASCII letters, and every data length is below
    2^31. -/
theorem parse_print {doc : Doc} (h : WF doc) : parse (print doc) = some doc := by
  obtain ⟨head, mid, hdoc, htype, hlen13, hall, hnot⟩ := h
  have hparse : parseChunks ((print doc).length + 1) (List.drop 8 (print doc))
      = some doc := by
    rw [drop_signature]
    subst hdoc
    have hflen : (head :: mid).length + 1
        ≤ (print (head :: mid ++ [iendChunk])).length + 1 := by
      have h1 := print_length (head :: mid ++ [iendChunk])
      have h2 : (head :: mid ++ [iendChunk]).length
          = (head :: mid).length + 1 := by
        simp
      omega
    have hallpre : ∀ c ∈ head :: mid, WFChunk c := by
      intro c hc
      apply hall
      have hmem : c ∈ (head :: mid) ++ [iendChunk] :=
        List.mem_append_left _ hc
      simpa using hmem
    have hwflast : WFChunk iendChunk := by
      apply hall
      simp
    exact parseChunks_printChunks (head :: mid) iendChunk _
      hallpre hnot hwflast (by decide) hflen
  unfold parse
  rw [take_signature, hparse, hdoc]
  show (if head.typeBytes = ihdrType ∧ head.data.length = 13
    then some (head :: mid ++ [iendChunk])
    else none) = some (head :: mid ++ [iendChunk])
  rw [ite_eq_left ⟨htype, hlen13⟩]

end Png.Proofs
