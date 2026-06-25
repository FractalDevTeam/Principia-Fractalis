/-
# PF.AllNineAlphaStrictOrdering_2026_06_24

★★★★★★★★ 2026-06-24 — explicit strict ordering of all nine substrate-class
α values derived from the 4-decimal brackets, kernel-only.

The substrate's nine α values sort in a unique strict order:

    α_Poincaré < α_P < α_RH < α_Hodge < α_NP < α_YM < α_BSD < α_QG < α_NS
        1     <  √2  < 3/2 <    φ    < φ+1/4 <  2  < 3π/4  < √(2π) < 3π/2

Numerically (4-decimal):
    1 < 1.4142 < 1.5 < 1.6180 < 1.8680 < 2 < 2.3561 < 2.5066 < 4.7123

All inequalities follow from the all-nine α brackets capstone in
`PF/AllNineAlphaNumericalBrackets_2026_06_24.lean` (non-overlapping
brackets). Pairwise distinctness for all C(9,2) = 36 pairs is then
an immediate corollary of the strict total ordering.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.AllNineAlphaNumericalBrackets_2026_06_24

namespace PrincipiaTractalis.AllNineAlphaStrictOrdering

open Real PrincipiaTractalis PrincipiaTractalis.Capstone
open PrincipiaTractalis.AllNineAlphaNumericalBrackets

/-! ## §1 — Adjacent strict inequalities (8 of them) -/

theorem Poincare_lt_P : alpha_Poincare < alpha_P := by
  rw [alpha_Poincare_exact]
  linarith [alpha_P_bracket.1]

theorem P_lt_RH : alpha_P < alpha_RH := by
  rw [alpha_RH_exact]
  linarith [alpha_P_bracket.2]

theorem RH_lt_Hodge : alpha_RH < alpha_Hodge := by
  rw [alpha_RH_exact]
  linarith [alpha_Hodge_bracket.1]

theorem Hodge_lt_NP : alpha_Hodge < alpha_NP := by
  linarith [alpha_Hodge_bracket.2, alpha_NP_bracket.1]

theorem NP_lt_YM : alpha_NP < alpha_YM := by
  rw [alpha_YM_exact]
  linarith [alpha_NP_bracket.2]

theorem YM_lt_BSD : alpha_YM < alpha_BSD := by
  rw [alpha_YM_exact]
  linarith [alpha_BSD_bracket.1]

theorem BSD_lt_QG : alpha_BSD < alpha_QG := by
  linarith [alpha_BSD_bracket.2, alpha_QG_bracket.1]

theorem QG_lt_NS : alpha_QG < alpha_NS := by
  linarith [alpha_QG_bracket.2, alpha_NS_bracket.1]

/-! ## §2 — The all-nine strict total ordering capstone -/

/-- **★★★★★★★★ THE ALL-NINE α STRICT TOTAL ORDERING ★★★★★★★★** —
    the substrate's nine forced α values arrange in a unique strict
    ordering, derived kernel-only from the non-overlapping 4-decimal
    brackets:

      α_Poincaré < α_P < α_RH < α_Hodge < α_NP < α_YM < α_BSD < α_QG < α_NS

    Equivalently:

      1 < √2 < 3/2 < φ < φ+1/4 < 2 < 3π/4 < √(2π) < 3π/2.

    No two substrate classes can carry the same α value. The strict
    ordering implies pairwise distinctness for all C(9, 2) = 36 pairs;
    by transitivity, any α_i ≠ α_j with i ≠ j.

    Zero project axioms. -/
theorem nine_alpha_strict_total_ordering :
    alpha_Poincare < alpha_P ∧
    alpha_P < alpha_RH ∧
    alpha_RH < alpha_Hodge ∧
    alpha_Hodge < alpha_NP ∧
    alpha_NP < alpha_YM ∧
    alpha_YM < alpha_BSD ∧
    alpha_BSD < alpha_QG ∧
    alpha_QG < alpha_NS :=
  ⟨Poincare_lt_P,
   P_lt_RH,
   RH_lt_Hodge,
   Hodge_lt_NP,
   NP_lt_YM,
   YM_lt_BSD,
   BSD_lt_QG,
   QG_lt_NS⟩

/-! ## §3 — Pairwise distinctness corollaries (selected) -/

/-- α_P ≠ α_NP (the load-bearing distinctness for the P ≠ NP chain). -/
theorem alpha_P_ne_alpha_NP : alpha_P ≠ alpha_NP := by
  have hchain : alpha_P < alpha_NP := by
    have h1 := P_lt_RH
    have h2 := RH_lt_Hodge
    have h3 := Hodge_lt_NP
    linarith
  exact ne_of_lt hchain

/-- α_Poincaré ≠ α_NS (extremes of the strict ordering). -/
theorem alpha_Poincare_ne_alpha_NS : alpha_Poincare ≠ alpha_NS := by
  have hchain : alpha_Poincare < alpha_NS := by
    have := nine_alpha_strict_total_ordering
    linarith [this.1, this.2.1, this.2.2.1, this.2.2.2.1,
              this.2.2.2.2.1, this.2.2.2.2.2.1,
              this.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2]
  exact ne_of_lt hchain

/-- α_P ≠ α_QG (cross-class distinctness involving the QG anchor). -/
theorem alpha_P_ne_alpha_QG : alpha_P ≠ alpha_QG := by
  have hchain : alpha_P < alpha_QG := by
    have := nine_alpha_strict_total_ordering
    linarith [this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
              this.2.2.2.2.2.1, this.2.2.2.2.2.2.1]
  exact ne_of_lt hchain

end PrincipiaTractalis.AllNineAlphaStrictOrdering

-- ★ Axiom check ★
#print axioms
  PrincipiaTractalis.AllNineAlphaStrictOrdering.nine_alpha_strict_total_ordering
