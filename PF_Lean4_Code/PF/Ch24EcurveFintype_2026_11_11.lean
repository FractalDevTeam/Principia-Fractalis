/-
# PF.Ch24EcurveFintype_2026_11_11

**The group E(ℚ) for Ch24's curve E : y² = x³ + x is literally two elements.**

`Ch24Descent2TorsionRatBridge_2026_10_17` delivered
`Ecurve_rank_eq_zero : Module.rank ℤ Ecurve.toAffine.Point = 0` by proving
`solutions_are_origin`: every rational `(x, y)` on `y² = x³ + x` has `x = 0`
and `y = 0`. The rank follows because every point is then 2-torsion (via
`Ecurve_two_torsion`).

That same `solutions_are_origin` suffices for a strictly stronger structural
fact: **E(ℚ) has exactly two elements**, the identity `0 : Point` and the
unique affine point `(0, 0)`. This file supplies

  * `P0 : Ecurve.toAffine.Point` — the affine 2-torsion point.
  * `point_is_zero_or_P0 : ∀ P, P = 0 ∨ P = P0`.
  * `Fintype Ecurve.toAffine.Point` instance with card = 2.

HONEST SCOPE. A `Fintype` on the Mordell-Weil group of a specific curve.
Nothing about L(E, s), nothing about 2-descent in general. The genuine
machinery that would give `rank = 0 → Finite` for every rank-0 curve on
mathlib's Weierstrass structure (Mordell-Weil finite generation) is not
in mathlib and is NOT built here.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.Ch24Descent2TorsionRatBridge_2026_10_17
import Mathlib.Data.Fintype.Basic

namespace PrincipiaTractalis
namespace Ch24EcurveFintype20261111

open PrincipiaTractalis.Ch24DescentRatBridge20261017
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the unique affine point `(0, 0)` as a `Point` -/

/-- `(0, 0)` is nonsingular on `Ecurve = ⟨0, 0, 0, 1, 0⟩`: the equation at
`(0, 0)` reads `0 = a₆ = 0` and the Y-partial there is `a₃ = 0`; but the
X-partial is `-a₄ = -1 ≠ 0`. -/
theorem P0_nonsingular : Ecurve.toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  refine ⟨rfl, Or.inr ?_⟩
  show (1 : ℚ) ≠ 0
  norm_num

/-- `P0 = (0, 0) ∈ Ecurve(ℚ)`. -/
def P0 : Ecurve.toAffine.Point := Point.some P0_nonsingular

theorem P0_ne_zero : P0 ≠ 0 := by
  intro h
  exact Point.noConfusion h

/-! ## §2 — classification: every `P` is either `0` or `P0` -/

/-- **Every rational point of `Ecurve` is either the identity or `(0, 0)`.**
Proof: cast to the `(x, y)` representation of an affine point; apply
`solutions_are_origin` to force `(x, y) = (0, 0)`; conclude by proof
irrelevance on `Nonsingular`. -/
theorem point_is_zero_or_P0 (P : Ecurve.toAffine.Point) :
    P = 0 ∨ P = P0 := by
  cases P with
  | zero => exact Or.inl rfl
  | some h =>
      rename_i x y
      -- Derive the Rat-level equation y² = x³ + x from Nonsingular/Equation.
      have hEq : y ^ 2 = x ^ 3 + x := by
        have h1 := h.left
        rw [WeierstrassCurve.Affine.equation_iff] at h1
        simp only [Ecurve] at h1
        linarith
      have hxy : x = 0 ∧ y = 0 := solutions_are_origin hEq
      right
      -- The points at (0, 0) are the same up to proof irrelevance of Nonsingular.
      subst hxy.1
      subst hxy.2
      rfl

/-! ## §3 — `Fintype` instance with card = 2 -/

/-- `Ecurve(ℚ) = {0, P0}` as a `Finset`. -/
def ecurveFinset : Finset Ecurve.toAffine.Point := {0, P0}

/-- The `Fintype` instance follows from `point_is_zero_or_P0`. -/
instance : Fintype Ecurve.toAffine.Point where
  elems := ecurveFinset
  complete P := by
    rcases point_is_zero_or_P0 P with hP | hP
    · rw [hP]
      show (0 : Ecurve.toAffine.Point) ∈ ecurveFinset
      simp [ecurveFinset]
    · rw [hP]
      show P0 ∈ ecurveFinset
      simp [ecurveFinset]

/-- **The Mordell-Weil group `Ecurve(ℚ)` is finite.** -/
theorem Ecurve_finite : Finite Ecurve.toAffine.Point := Finite.of_fintype _

/-- **The Mordell-Weil group of `Ecurve` has exactly 2 elements.** -/
theorem Ecurve_card :
    Fintype.card Ecurve.toAffine.Point = 2 := by
  show (ecurveFinset).card = 2
  simp [ecurveFinset, Finset.card_insert_of_notMem, P0_ne_zero.symm]

end Ch24EcurveFintype20261111
end PrincipiaTractalis

#print axioms PrincipiaTractalis.Ch24EcurveFintype20261111.P0_nonsingular
#print axioms PrincipiaTractalis.Ch24EcurveFintype20261111.point_is_zero_or_P0
#print axioms PrincipiaTractalis.Ch24EcurveFintype20261111.Ecurve_finite
#print axioms PrincipiaTractalis.Ch24EcurveFintype20261111.Ecurve_card
