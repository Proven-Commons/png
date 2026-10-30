/-
  Axiom check. Building this file prints the axioms each proof
  depends on: the headline theorems in `Png.Proofs`, then every
  theorem `comparator.json` names, as proved in
  `Png/Proofs/SpecProofs.lean`. The expected output is only the three
  standard Lean axioms: `propext`, `Classical.choice`,
  `Quot.sound`, or a subset of them. Any other name here breaks
  the verified bar. `tests/run_tests.py` reads this output and
  fails on any other name, or on a theorem with no line.
-/

import Png.Proofs.RoundTrip
import Png.Proofs.Header
import Png.Proofs.Sound
import Png.Proofs.Layout
import Png.Proofs.SpecProofs

#print axioms Png.Proofs.parse_print
#print axioms Png.Proofs.parseIhdr_print
#print axioms Png.Proofs.checkPair_iff
#print axioms Png.Proofs.parseFile_print
#print axioms Png.Proofs.parse_sound
#print axioms Png.Proofs.parseIhdr_sound
#print axioms Png.Proofs.parseFile_sound
#print axioms Png.Proofs.print_layout
#print axioms Png.Proofs.printIhdr_layout
#print axioms Png.Proofs.isLetter_iff
#print axioms Png.Proofs.isIEND_iff

#print axioms Png.Spec.parse_print
#print axioms Png.Spec.parseIhdr_print
#print axioms Png.Spec.checkPair_iff
#print axioms Png.Spec.parseFile_print
#print axioms Png.Spec.parse_sound
#print axioms Png.Spec.parseIhdr_sound
#print axioms Png.Spec.parseFile_sound
#print axioms Png.Spec.print_layout
#print axioms Png.Spec.printIhdr_layout
#print axioms Png.Spec.isLetter_iff
#print axioms Png.Spec.ihdrType_eq
#print axioms Png.Spec.typeBytes_eq
#print axioms Png.Spec.isIEND_iff
#print axioms Png.Spec.reads_real_file_header
#print axioms Png.Spec.reads_header_1920x1080
#print axioms Png.Spec.rejects_bad_signature
#print axioms Png.Spec.rejects_bad_crc
#print axioms Png.Spec.rejects_truncated_input
#print axioms Png.Spec.rejects_first_chunk_length_12
#print axioms Png.Spec.rejects_zero_width
#print axioms Png.Spec.rejects_zero_height
#print axioms Png.Spec.rejects_width_at_cap
#print axioms Png.Spec.rejects_height_at_cap
#print axioms Png.Spec.rejects_illegal_depth
#print axioms Png.Spec.rejects_unknown_colour_type
#print axioms Png.Spec.rejects_unknown_interlace
#print axioms Png.Spec.rejects_nonzero_compression
#print axioms Png.Spec.rejects_nonzero_filter
#print axioms Png.Spec.rejects_second_ihdr
#print axioms Png.Spec.rejects_header_wrong_length
