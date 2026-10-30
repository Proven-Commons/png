/-
  Axiom check. Building this file prints the axioms each proof
  depends on: the headline theorems in `Png.Proofs`, then every
  theorem `comparator.json` names, as proved in
  `Proofs/SpecProofs.lean`. The expected output is only the three
  standard Lean axioms: `propext`, `Classical.choice`,
  `Quot.sound`, or a subset of them. Any other name here breaks
  the verified bar. `tests/run_tests.py` reads this output and
  fails on any other name, or on a theorem with no line.
-/

import Proofs.RoundTrip
import Proofs.Header
import Proofs.Sound
import Proofs.Layout
import Proofs.SpecProofs

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

#print axioms Spec.parse_print
#print axioms Spec.parseIhdr_print
#print axioms Spec.checkPair_iff
#print axioms Spec.parseFile_print
#print axioms Spec.parse_sound
#print axioms Spec.parseIhdr_sound
#print axioms Spec.parseFile_sound
#print axioms Spec.print_layout
#print axioms Spec.printIhdr_layout
#print axioms Spec.isLetter_iff
#print axioms Spec.ihdrType_eq
#print axioms Spec.typeBytes_eq
#print axioms Spec.isIEND_iff
#print axioms Spec.reads_real_file_header
#print axioms Spec.reads_header_1920x1080
#print axioms Spec.rejects_bad_signature
#print axioms Spec.rejects_bad_crc
#print axioms Spec.rejects_truncated_input
#print axioms Spec.rejects_first_chunk_length_12
#print axioms Spec.rejects_zero_width
#print axioms Spec.rejects_zero_height
#print axioms Spec.rejects_width_at_cap
#print axioms Spec.rejects_height_at_cap
#print axioms Spec.rejects_illegal_depth
#print axioms Spec.rejects_unknown_colour_type
#print axioms Spec.rejects_unknown_interlace
#print axioms Spec.rejects_nonzero_compression
#print axioms Spec.rejects_nonzero_filter
#print axioms Spec.rejects_second_ihdr
#print axioms Spec.rejects_header_wrong_length
