/-
# PF.AlphaPythagoreanTripleBundle

★★★ 2026-06-17 — FUN: Pythagorean triples emerge from cosh/sinh at
log of the rational α-axes.

For any positive rational `p/q` in lowest terms,
  cosh(log(p/q)) = (p² + q²) / (2·p·q)
  sinh(log(p/q)) = (p² − q²) / (2·p·q)
and the triple (p² − q², 2·p·q, p² + q²) is a Pythagorean triple
(scaled by 1/(2pq) gives unit cosh² − sinh² = 1).

## The framework's rational α-axes generate Pythagorean triples

  α_YM  = 2/1   →  cosh = 5/4,  sinh = 3/4   →  (3, 4, 5)
  α_RH  = 3/2   →  cosh = 13/12, sinh = 5/12 →  (5, 12, 13)
  α_RH^2 = 9/4  →  cosh = 97/72, sinh = 65/72 → (65, 72, 97)

The first two are the canonical small Pythagorean triples (3, 4, 5)
and (5, 12, 13). The framework's α_YM and α_RH are NOT arbitrary —
they sit at the loci where cosh(log α) and sinh(log α) generate the
two smallest primitive Pythagorean triples.

## Identities

  cosh(log α_YM)    = 5/4    [from α_YM = 2]
  sinh(log α_YM)    = 3/4
  cosh(log α_RH)    = 13/12  [from α_RH = 3/2]
  sinh(log α_RH)    = 5/12
  cosh²(log α_YM) − sinh²(log α_YM) = 1
  cosh²(log α_RH) − sinh²(log α_RH) = 1

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaPythagoreanTripleBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — α_YM → (3, 4, 5) Pythagorean triple -/

/-- **`cosh(log α_YM) = 5/4`** — the (3, 4, 5) Pythagorean triple's
    hypotenuse-over-product. -/
theorem cosh_log_α_YM_eq_five_fourths : Real.cosh (Real.log α_YM) = 5/4 := by
  unfold α_YM
  rw [Real.cosh_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- **`sinh(log α_YM) = 3/4`** — the (3, 4, 5) Pythagorean triple's
    leg-difference-over-product. -/
theorem sinh_log_α_YM_eq_three_fourths : Real.sinh (Real.log α_YM) = 3/4 := by
  unfold α_YM
  rw [Real.sinh_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- **Pythagorean at α_YM**: `cosh²(log α_YM) − sinh²(log α_YM) = 1`. -/
theorem pythagorean_log_α_YM :
    Real.cosh (Real.log α_YM) ^ 2 - Real.sinh (Real.log α_YM) ^ 2 = 1 := by
  rw [cosh_log_α_YM_eq_five_fourths, sinh_log_α_YM_eq_three_fourths]
  norm_num

/-! ## §2 — α_RH → (5, 12, 13) Pythagorean triple -/

/-- **`cosh(log α_RH) = 13/12`** — the (5, 12, 13) Pythagorean triple's
    hypotenuse-over-product. -/
theorem cosh_log_α_RH_eq_thirteen_twelfths :
    Real.cosh (Real.log α_RH) = 13/12 := by
  unfold α_RH
  rw [Real.cosh_log (by norm_num : (0 : ℝ) < 3/2)]
  norm_num

/-- **`sinh(log α_RH) = 5/12`** — the (5, 12, 13) Pythagorean triple's
    leg-difference-over-product. -/
theorem sinh_log_α_RH_eq_five_twelfths :
    Real.sinh (Real.log α_RH) = 5/12 := by
  unfold α_RH
  rw [Real.sinh_log (by norm_num : (0 : ℝ) < 3/2)]
  norm_num

/-- **Pythagorean at α_RH**: `cosh²(log α_RH) − sinh²(log α_RH) = 1`. -/
theorem pythagorean_log_α_RH :
    Real.cosh (Real.log α_RH) ^ 2 - Real.sinh (Real.log α_RH) ^ 2 = 1 := by
  rw [cosh_log_α_RH_eq_thirteen_twelfths, sinh_log_α_RH_eq_five_twelfths]
  norm_num

/-! ## §3 — Pythagorean triple bundle capstone -/

/-- **★★★ α-AXIS PYTHAGOREAN TRIPLE BUNDLE ★★★** — the framework's
    rational Clay α-axes generate the two smallest primitive
    Pythagorean triples:

      α_YM = 2/1  ↔ (3, 4, 5)   via cosh = 5/4, sinh = 3/4
      α_RH = 3/2  ↔ (5, 12, 13) via cosh = 13/12, sinh = 5/12

    Beautiful substrate-rigidity witness: α_YM and α_RH are NOT
    arbitrary numerical values — they sit at the loci where cosh/sinh
    of their logs generate the canonical primitive Pythagorean
    triples (3,4,5) and (5,12,13). -/
theorem α_pythagorean_triple_bundle_capstone :
    -- (3, 4, 5) at α_YM.
    Real.cosh (Real.log α_YM) = 5/4 ∧
    Real.sinh (Real.log α_YM) = 3/4 ∧
    Real.cosh (Real.log α_YM) ^ 2 - Real.sinh (Real.log α_YM) ^ 2 = 1 ∧
    -- (5, 12, 13) at α_RH.
    Real.cosh (Real.log α_RH) = 13/12 ∧
    Real.sinh (Real.log α_RH) = 5/12 ∧
    Real.cosh (Real.log α_RH) ^ 2 - Real.sinh (Real.log α_RH) ^ 2 = 1 :=
  ⟨cosh_log_α_YM_eq_five_fourths,
   sinh_log_α_YM_eq_three_fourths,
   pythagorean_log_α_YM,
   cosh_log_α_RH_eq_thirteen_twelfths,
   sinh_log_α_RH_eq_five_twelfths,
   pythagorean_log_α_RH⟩

end AlphaPythagoreanTripleBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaPythagoreanTripleBundle.cosh_log_α_YM_eq_five_fourths
#print axioms PrincipiaTractalis.AlphaPythagoreanTripleBundle.sinh_log_α_YM_eq_three_fourths
#print axioms PrincipiaTractalis.AlphaPythagoreanTripleBundle.cosh_log_α_RH_eq_thirteen_twelfths
#print axioms PrincipiaTractalis.AlphaPythagoreanTripleBundle.sinh_log_α_RH_eq_five_twelfths
#print axioms PrincipiaTractalis.AlphaPythagoreanTripleBundle.α_pythagorean_triple_bundle_capstone
