/-
  Proofs of the statements in `Spec.lean`, under the same names.

  The round trips, the table, the soundness statements, and the
  byte layout are the theorems proved in `Proofs/RoundTrip.lean`,
  `Proofs/Header.lean`, `Proofs/Sound.lean`, and
  `Proofs/Layout.lean`. The accepted and refused inputs are
  single inputs, checked in the kernel with `decide +kernel`:
  no native evaluation, which the bar forbids.
-/

import Png
import Spec.Defs
import Proofs.RoundTrip
import Proofs.Header
import Proofs.Sound
import Proofs.Layout

open Png Spec

theorem Spec.parse_print {doc : Doc} (h : WF doc) :
    parse (print doc) = some doc :=
  Png.Proofs.parse_print h

theorem Spec.parseIhdr_print (h : Ihdr) (hwf : WFHeader h) :
    parseIhdr (printIhdr h) = some h :=
  Png.Proofs.parseIhdr_print h hwf

theorem Spec.checkPair_iff (ct bd : UInt8) :
    checkPair ct bd = true ↔
      (ct.toNat, bd.toNat) ∈ allowedPairs :=
  Png.Proofs.checkPair_iff ct bd

theorem Spec.parseFile_print {hd : Ihdr} {doc : Doc} (h : WFFull hd doc) :
    parseFile (print doc) = some (hd, doc) :=
  Png.Proofs.parseFile_print h


theorem Spec.parse_sound {bs : List UInt8} {doc : Doc}
    (h : parse bs = some doc) : WF doc ∧ print doc = bs :=
  Png.Proofs.parse_sound h

theorem Spec.parseIhdr_sound {bs : List UInt8} {h : Ihdr}
    (hp : parseIhdr bs = some h) : WFHeader h ∧ printIhdr h = bs :=
  Png.Proofs.parseIhdr_sound hp

theorem Spec.parseFile_sound {bs : List UInt8} {hd : Ihdr} {doc : Doc}
    (h : parseFile bs = some (hd, doc)) :
    WFFull hd doc ∧ print doc = bs :=
  Png.Proofs.parseFile_sound h


theorem Spec.print_layout (doc : Doc) :
    print doc = [137, 80, 78, 71, 13, 10, 26, 10] ++
      doc.flatMap (fun c =>
        bigEndian4 c.data.length ++ [c.t1, c.t2, c.t3, c.t4] ++ c.data ++
          bigEndian4 (Crc32.crc32 ([c.t1, c.t2, c.t3, c.t4] ++ c.data)).toNat) :=
  Png.Proofs.print_layout doc

theorem Spec.printIhdr_layout (h : Ihdr) :
    printIhdr h = bigEndian4 h.width ++ bigEndian4 h.height ++
      [h.bitDepth, h.colorType, 0, 0, h.interlace] :=
  Png.Proofs.printIhdr_layout h

theorem Spec.isLetter_iff (b : UInt8) :
    isLetter b = true ↔
      (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ (97 ≤ b.toNat ∧ b.toNat ≤ 122) :=
  Png.Proofs.isLetter_iff b

theorem Spec.ihdrType_eq : ihdrType = [73, 72, 68, 82] := rfl

theorem Spec.isIEND_iff (c : Chunk) :
    isIEND c = true ↔ [c.t1, c.t2, c.t3, c.t4] = [73, 69, 78, 68] ∧ c.data = [] :=
  Png.Proofs.isIEND_iff c


theorem Spec.reads_real_file_header :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 0, 180, 244,
      174, 198, 0, 0, 0, 62, 73, 68, 65, 84, 120, 156, 1, 51, 0, 204,
      255, 0, 248, 207, 45, 4, 205, 181, 169, 174, 98, 138, 255, 174,
      190, 27, 111, 191, 0, 254, 105, 254, 66, 198, 209, 157, 111,
      200, 221, 165, 145, 35, 173, 191, 75, 0, 216, 164, 157, 244,
      188, 239, 173, 101, 28, 78, 104, 79, 114, 243, 122, 31, 237,
      218, 28, 90, 62, 15, 23, 102, 0, 0, 0, 0, 73, 69, 78, 68, 174,
      66, 96, 130] : List UInt8)).map Prod.fst =
      some { width := 4, height := 3, bitDepth := 8, colorType := 6, interlace := 0 } := by
  decide +kernel


theorem Spec.reads_header_1920x1080 :
    parseIhdr ([0, 0, 7, 128, 0, 0, 4, 56, 8, 2, 0, 0, 0]
      : List UInt8) =
      some { width := 1920, height := 1080, bitDepth := 8, colorType := 2, interlace := 0 } := by
  decide +kernel


theorem Spec.rejects_bad_signature :
    (parse ([118, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72,
      68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 0, 180, 244, 174,
      198, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_bad_crc :
    (parse ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72,
      68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 0, 180, 244, 174,
      57, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_truncated_input :
    (parse ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72,
      68, 82, 0, 0, 0, 4] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_first_chunk_length_12 :
    (parse ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 12, 73, 72,
      68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 240, 122, 129,
      218, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_zero_width :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 0, 0, 0, 0, 3, 8, 6, 0, 0, 0, 189, 31,
      14, 188, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_zero_height :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 0, 8, 6, 0, 0, 0, 50, 96,
      220, 104, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_width_at_cap :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 128, 0, 0, 0, 0, 0, 0, 3, 8, 6, 0, 0, 0, 29, 117,
      43, 171, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_height_at_cap :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 128, 0, 0, 0, 8, 6, 0, 0, 0, 84, 53,
      220, 39, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_illegal_depth :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 4, 2, 0, 0, 0, 254, 102,
      212, 144, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_unknown_colour_type :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 1, 0, 0, 0, 41, 35,
      150, 127, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_unknown_interlace :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0, 2, 90, 250,
      207, 234, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_nonzero_compression :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 1, 0, 0, 181, 54,
      196, 241, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_nonzero_filter :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 1, 0, 173, 239,
      159, 135, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_second_ihdr :
    (parseFile ([137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73,
      72, 68, 82, 0, 0, 0, 1, 0, 0, 0, 1, 8, 2, 0, 0, 0, 144, 119,
      83, 222, 0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 2, 0, 0, 0, 2,
      8, 2, 0, 0, 0, 253, 212, 154, 115, 0, 0, 0, 12, 73, 68, 65, 84,
      120, 156, 99, 96, 96, 96, 0, 0, 0, 4, 0, 1, 246, 23, 56, 85, 0,
      0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]
      : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_header_wrong_length :
    (parseIhdr ([0, 0, 0, 4, 0, 0, 0, 3, 8, 6, 0, 0]
      : List UInt8)).isSome = false := by
  decide +kernel
