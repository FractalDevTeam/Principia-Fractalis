/-
# Axiom audit for the 143-problem empirical validation framework.

This file uses `#print axioms` to verify that the empirical-validation
capstone theorem `empirical_validation_capstone` depends on zero project
axioms. Only standard kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`) are expected — these are the foundational axioms of Lean 4
itself and ship with the kernel; no PF-specific axiom is permitted in
this dependency chain.
-/

import PF.Empirical.HundredFortyThreeProblems

open PrincipiaTractalis Empirical

#print axioms empirical_validation_capstone
#print axioms universal_fractal_coherence
#print axioms match_canonical_closed_form
#print axioms coherence_highly_significant
#print axioms the143Problems_length
