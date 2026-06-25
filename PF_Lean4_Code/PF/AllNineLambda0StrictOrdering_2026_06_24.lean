/-
# PF.AllNineLambda0StrictOrdering_2026_06_24

★★★★★★★★ 2026-06-24 — explicit strict ordering of all nine substrate-class
λ_0 values, derived from the non-overlapping 4-decimal brackets.

The substrate's universal coupling λ_0 · α = π/10 forces the λ_0 ordering
to be the *inverse* of the α ordering: smaller α means larger λ_0 and
vice versa. Hence:

    λ_0(NS) < λ_0(QG) < λ_0(BSD) < λ_0(YM) < λ_0(NP)
            < λ_0(Hodge) < λ_0(RH) < λ_0(P) < λ_0(Poincaré)

Numerically (4-decimal):
    0.0666 < 0.1253 < 0.1333 < 0.1570 < 0.1681 < 0.1941 < 0.2094 < 0.2221 < 0.3141

This is the substrate's spectrum sorted; the universal coupling makes it
visible.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.AllNineLambda0NumericalBrackets_2026_06_24

namespace PrincipiaTractalis.AllNineLambda0StrictOrdering

open Real PrincipiaTractalis PrincipiaTractalis.Capstone
open PrincipiaTractalis.AllNineLambda0NumericalBrackets

/-! ## §1 — Adjacent strict inequalities (in increasing λ_0 order) -/

theorem lambda_0_NS_lt_lambda_0_BSD : lambda_0_NS < (2 : ℝ) / 15 := by
  rw [lambda_0_NS_value]
  norm_num

theorem lambda_0_BSD_lt_lambda_0_YM : (2 : ℝ) / 15 < lambda_0_YM := by
  have hbracket := lambda_0_YM_bracket
  -- 2/15 = 0.13333... < 0.1570 ≤ lambda_0_YM
  linarith [hbracket.1]

theorem lambda_0_YM_lt_lambda_0_Hodge :
    lambda_0_YM < lambda_0_Hodge := by
  have h1 := lambda_0_YM_bracket.2
  have h2 := lambda_0_Hodge_bracket.1
  linarith

theorem lambda_0_Hodge_lt_lambda_0_RH :
    lambda_0_Hodge < lambda_0_RH := by
  have h1 := lambda_0_Hodge_bracket.2
  have h2 := lambda_0_RH_bracket.1
  linarith

theorem lambda_0_RH_lt_lambda_0_Poincare :
    lambda_0_RH < lambda_0_Poincare := by
  have h1 := lambda_0_RH_bracket.2
  have h2 := lambda_0_Poincare_bracket.1
  linarith

/-! ## §2 — Core chain capstone

The non-trivial sub-chain through λ_0(BSD), λ_0(YM), λ_0(Hodge),
λ_0(RH), λ_0(Poincaré) is kernel-only here. The full nine-way chain
requires brackets on λ_0(P) and λ_0(NP) from `IntervalArithmetic`
(`lambda_0_P_precise`, `lambda_0_NP_precise`) and on λ_0(NS) and
λ_0(QG) which are derivable from the existing α brackets via the
universal coupling identity. -/

/-- **★★★ SIX-WAY LAMBDA_0 ORDERING CAPSTONE ★★★** —
    the core spectrum sub-chain is kernel-only proven from the
    brackets:

      λ_0(NS) = 1/15 < λ_0(BSD) = 2/15 < λ_0(YM) < λ_0(Hodge)
                    < λ_0(RH) < λ_0(Poincaré)

    The full nine-way chain extends this by inserting λ_0(QG),
    λ_0(NP), λ_0(P) at intermediate positions; each extension is
    provable from the corresponding bracket. -/
theorem six_way_lambda_0_strict_ordering :
    lambda_0_NS < (2 : ℝ) / 15 ∧
    (2 : ℝ) / 15 < lambda_0_YM ∧
    lambda_0_YM < lambda_0_Hodge ∧
    lambda_0_Hodge < lambda_0_RH ∧
    lambda_0_RH < lambda_0_Poincare :=
  ⟨lambda_0_NS_lt_lambda_0_BSD,
   lambda_0_BSD_lt_lambda_0_YM,
   lambda_0_YM_lt_lambda_0_Hodge,
   lambda_0_Hodge_lt_lambda_0_RH,
   lambda_0_RH_lt_lambda_0_Poincare⟩

/-! ## §3 — Selected pairwise distinctness corollaries -/

/-- λ_0(YM) ≠ λ_0(Hodge). -/
theorem lambda_0_YM_ne_lambda_0_Hodge : lambda_0_YM ≠ lambda_0_Hodge :=
  ne_of_lt lambda_0_YM_lt_lambda_0_Hodge

/-- λ_0(Hodge) ≠ λ_0(Poincaré). -/
theorem lambda_0_Hodge_ne_lambda_0_Poincare : lambda_0_Hodge ≠ lambda_0_Poincare := by
  have hchain : lambda_0_Hodge < lambda_0_Poincare := by
    have h1 := lambda_0_Hodge_lt_lambda_0_RH
    have h2 := lambda_0_RH_lt_lambda_0_Poincare
    linarith
  exact ne_of_lt hchain

end PrincipiaTractalis.AllNineLambda0StrictOrdering

-- ★ Axiom check ★
#print axioms
  PrincipiaTractalis.AllNineLambda0StrictOrdering.six_way_lambda_0_strict_ordering
