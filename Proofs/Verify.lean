/-
  Axiom check for the headline theorem. Building this file prints
  the axioms the proof depends on. The expected output is only the
  three standard Lean axioms: `propext`, `Classical.choice`,
  `Quot.sound`, or a subset of them. Any other name here breaks
  the verified bar.
-/

import Proofs.RoundTrip
import Proofs.Header

#print axioms Png.Proofs.parse_print
#print axioms Png.Proofs.parseIhdr_print
#print axioms Png.Proofs.checkPair_iff
#print axioms Png.Proofs.parseFile_print
