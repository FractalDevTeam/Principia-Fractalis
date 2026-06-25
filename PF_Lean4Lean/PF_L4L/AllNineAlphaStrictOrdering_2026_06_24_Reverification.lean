/-
# PF_L4L.AllNineAlphaStrictOrdering_2026_06_24_Reverification

Independent Lean4Lean re-elaboration of the 2026-06-24 strict total ordering
on all nine substrate-class α values.

Expected: `[propext, Classical.choice, Quot.sound]` for each.
-/

import PF.AllNineAlphaStrictOrdering_2026_06_24

namespace PF_L4L

def nine_alpha_strict_total_ordering_reverified :=
  @PrincipiaTractalis.AllNineAlphaStrictOrdering.nine_alpha_strict_total_ordering
#print axioms nine_alpha_strict_total_ordering_reverified

def alpha_P_ne_alpha_NP_reverified :=
  @PrincipiaTractalis.AllNineAlphaStrictOrdering.alpha_P_ne_alpha_NP
#print axioms alpha_P_ne_alpha_NP_reverified

def alpha_Poincare_ne_alpha_NS_reverified :=
  @PrincipiaTractalis.AllNineAlphaStrictOrdering.alpha_Poincare_ne_alpha_NS
#print axioms alpha_Poincare_ne_alpha_NS_reverified

def alpha_P_ne_alpha_QG_reverified :=
  @PrincipiaTractalis.AllNineAlphaStrictOrdering.alpha_P_ne_alpha_QG
#print axioms alpha_P_ne_alpha_QG_reverified

end PF_L4L
