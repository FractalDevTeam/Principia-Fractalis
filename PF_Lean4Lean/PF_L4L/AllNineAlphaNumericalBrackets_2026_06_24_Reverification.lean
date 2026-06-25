/-
# PF_L4L.AllNineAlphaNumericalBrackets_2026_06_24_Reverification

Independent Lean4Lean re-elaboration of the 2026-06-24 all-nine
substrate-class α numerical brackets capstone.

Expected axiom report for each: `[propext, Classical.choice, Quot.sound]`.
-/

import PF.AllNineAlphaNumericalBrackets_2026_06_24

namespace PF_L4L

def alpha_P_bracket_reverified :=
  @PrincipiaTractalis.AllNineAlphaNumericalBrackets.alpha_P_bracket
#print axioms alpha_P_bracket_reverified

def alpha_NP_bracket_reverified :=
  @PrincipiaTractalis.AllNineAlphaNumericalBrackets.alpha_NP_bracket
#print axioms alpha_NP_bracket_reverified

def alpha_Hodge_bracket_reverified :=
  @PrincipiaTractalis.AllNineAlphaNumericalBrackets.alpha_Hodge_bracket
#print axioms alpha_Hodge_bracket_reverified

def alpha_BSD_bracket_reverified :=
  @PrincipiaTractalis.AllNineAlphaNumericalBrackets.alpha_BSD_bracket
#print axioms alpha_BSD_bracket_reverified

def alpha_NS_bracket_reverified :=
  @PrincipiaTractalis.AllNineAlphaNumericalBrackets.alpha_NS_bracket
#print axioms alpha_NS_bracket_reverified

def alpha_QG_bracket_reverified :=
  @PrincipiaTractalis.AllNineAlphaNumericalBrackets.alpha_QG_bracket
#print axioms alpha_QG_bracket_reverified

def all_nine_alpha_brackets_capstone_reverified :=
  @PrincipiaTractalis.AllNineAlphaNumericalBrackets.all_nine_alpha_brackets_capstone
#print axioms all_nine_alpha_brackets_capstone_reverified

end PF_L4L
