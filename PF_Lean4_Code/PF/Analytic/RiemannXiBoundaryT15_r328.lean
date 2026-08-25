/-
# r328 — T=15 RIEMANN ξ BOUNDARY REDUCTION

★ 2026-08-25.  Reduces the boundary-nonvanishing hypothesis of r327's
  `rectangleZeroCount_riemannXiEntire` on the specific rectangle
  `[0, 1] × [0, 15]` to the two genuinely unresolved horizontal
  obligations (top right half + bottom edge).

## The T = 15 rectangle

  z15 := ⟨0,  0⟩
  w15 := ⟨1, 15⟩

Rectangle: `0 ≤ Re s ≤ 1`, `0 ≤ Im s ≤ 15`.
Border: bottom (Im = 0) ∪ left (Re = 0) ∪ top (Im = 15) ∪ right (Re = 1).

## What this file gives (kernel-clean)

- **Corners.** `riemannXiEntire 0 = 1/2`, `riemannXiEntire 1 = 1/2`.  Direct
  from r325's definition — the polynomial factor `s(s-1)` vanishes at both
  endpoints, killing any `completedRiemannZeta₀` contribution.
- **Right vertical.** `riemannXiEntire ⟨1, t⟩ ≠ 0` for EVERY real `t`.
  Case-split on `t = 0` (corner) vs `t ≠ 0` (mathlib
  `riemannZeta_ne_zero_of_one_le_re` + `Gammaℝ_ne_zero_of_re_pos` +
  `riemannZeta_def_of_ne_zero` + r325's off-pole factorization).
- **Left vertical.** `riemannXiEntire ⟨0, t⟩ ≠ 0` for EVERY real `t`.
  Immediate from the right vertical via r326's `riemannXiEntire_one_sub`.
- **Top edge halving.** If `ξ⟨σ, 15⟩ ≠ 0` for every `σ ∈ [1/2, 1]`, then
  the same holds for every `σ ∈ [0, 1]`.  Direct from r326's
  `riemannXiEntire_reflect_vertical`.
- **Bottom edge — packaged as residual.**  We do NOT smuggle in
  "ζ has no real zeros in `(0, 1)`" (classical via Dirichlet eta but not a
  named theorem in mathlib `v4.24.0-rc1`).  The endpoints `σ = 0` and
  `σ = 1` ARE handled by the corner values; the open interior is the
  residual, exposed as `BottomEdgeZeroFree`.
- **Main boundary reduction.**  Given the top-right-half hypothesis and
  `BottomEdgeZeroFree`, `riemannXiEntire s ≠ 0` for every `s` on the border
  of the T = 15 rectangle — exactly r327's border hypothesis.
- **T = 15 zero-count identity.**  Instantiates r327's
  `rectangleZeroCount_riemannXiEntire_self_contained` at `(z15, w15)`
  under the same two hypotheses.  The finite interior zero set is
  produced automatically from `finite_zeros_rectangle` using
  `riemannXiEntire 0 = 1/2 ≠ 0` as the SW-corner nonvanishing witness.

## Exact remaining numerical obligations after r328

Only two:

  (H_TOP)     `riemannXiEntire ⟨σ, 15⟩ ≠ 0` for `1/2 ≤ σ ≤ 1`.
  (H_BOTTOM)  `riemannXiEntire (σ : ℂ) ≠ 0` for `0 ≤ σ ≤ 1`.

Once both are certified, the total zero-count integer on the T = 15
rectangle equals `∑ ρ, analyticOrderNatAt riemannXiEntire ρ`.  Combined
with r324 (at least one such zero exists in `1 < t < 15`), a total-count
= 1 evaluation would give: no off-line ζ-zeros below `t = 15`.

Zero project axioms; ordinary foundations only.  No `sorry`, no
`native_decide`, no `axiom`, no `Prop := True`.  No `α_RH`,
no `StructuralLaws`, no empirical zero table.

SPDX-License-Identifier: Apache-2.0
-/
import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannXiSymmetries_r326
import PF.Analytic.RiemannXiRectangleCount_r327
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex Set Topology Filter
open scoped ComplexConjugate Interval
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiSymmetries
open PrincipiaTractalis.RiemannXiRectangleCount
open Zeta23.Analytic

noncomputable section

namespace PrincipiaTractalis.RiemannXiBoundaryT15

/-! ## §1 — The T = 15 rectangle -/

/-- South-west corner of the T = 15 rectangle: `s = 0`. -/
def z15 : ℂ := ⟨0, 0⟩

/-- North-east corner of the T = 15 rectangle: `s = 1 + 15 · I`. -/
def w15 : ℂ := ⟨1, 15⟩

lemma z15_re : z15.re = 0 := rfl
lemma z15_im : z15.im = 0 := rfl
lemma w15_re : w15.re = 1 := rfl
lemma w15_im : w15.im = 15 := rfl

lemma z15_re_le_w15_re : z15.re ≤ w15.re := by
  show (0 : ℝ) ≤ 1; linarith

lemma z15_im_le_w15_im : z15.im ≤ w15.im := by
  show (0 : ℝ) ≤ 15; linarith

/-! ## §3 — Corner values `ξ(0) = ξ(1) = 1/2` -/

/-- **`riemannXiEntire_zero_value`** — `ξ(0) = 1/2`.  Since
`s(s - 1) = 0 · (-1) = 0` at `s = 0`, the entire `completedRiemannZeta₀`
factor drops out of the r325 definition. -/
theorem riemannXiEntire_zero_value : riemannXiEntire 0 = 1/2 := by
  unfold riemannXiEntire
  ring

/-- **`riemannXiEntire_one_value`** — `ξ(1) = 1/2`.  Since
`s(s - 1) = 1 · 0 = 0` at `s = 1`, the entire `completedRiemannZeta₀`
factor drops out of the r325 definition. -/
theorem riemannXiEntire_one_value : riemannXiEntire 1 = 1/2 := by
  unfold riemannXiEntire
  ring

/-- `ξ(0) ≠ 0`. -/
theorem riemannXiEntire_zero_ne_zero : riemannXiEntire 0 ≠ 0 := by
  rw [riemannXiEntire_zero_value]; norm_num

/-- `ξ(1) ≠ 0`. -/
theorem riemannXiEntire_one_ne_zero : riemannXiEntire 1 ≠ 0 := by
  rw [riemannXiEntire_one_value]; norm_num

/-! ## §4 — Right vertical `ξ⟨1, t⟩ ≠ 0` for every real `t` -/

/-- The complex point `⟨1, 0⟩` is the real one. -/
lemma mk_one_zero_eq_one : (⟨1, 0⟩ : ℂ) = 1 := by
  apply Complex.ext <;> simp

/-- **`riemannXiEntire_ne_zero_on_re_one`** — the entire ξ does not vanish
anywhere on the vertical line `Re s = 1`.  The `Re s ≥ 1` non-vanishing of
`Complex.riemannZeta` (mathlib's `riemannZeta_ne_zero_of_one_le_re`, which
does not require `s ≠ 1` since the junk value at the pole happens to be
nonzero) plus `Gammaℝ` non-vanishing for `Re s > 0` plus r325's off-pole
factorization gives the general case; the corner `t = 0` is handled by
`riemannXiEntire_one_value`. -/
theorem riemannXiEntire_ne_zero_on_re_one (t : ℝ) :
    riemannXiEntire ⟨1, t⟩ ≠ 0 := by
  by_cases ht : t = 0
  · subst ht
    rw [mk_one_zero_eq_one]
    exact riemannXiEntire_one_ne_zero
  · -- `t ≠ 0` case
    have hs0 : (⟨1, t⟩ : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hs1 : (⟨1, t⟩ : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; exact ht this
    have hRe : (1 : ℝ) ≤ (⟨1, t⟩ : ℂ).re := by
      show (1 : ℝ) ≤ 1; linarith
    have hζ : riemannZeta (⟨1, t⟩ : ℂ) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re hRe
    have hGamma : Gammaℝ (⟨1, t⟩ : ℂ) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      show (0 : ℝ) < 1; linarith
    have hdef := riemannZeta_def_of_ne_zero hs0
    -- `riemannZeta s = completedRiemannZeta s / Gammaℝ s`, so
    -- `completedRiemannZeta s = Gammaℝ s * riemannZeta s`.
    have hΛ_eq : completedRiemannZeta (⟨1, t⟩ : ℂ) =
        Gammaℝ (⟨1, t⟩ : ℂ) * riemannZeta (⟨1, t⟩ : ℂ) := by
      rw [hdef, mul_div_cancel₀ _ hGamma]
    have hΛ : completedRiemannZeta (⟨1, t⟩ : ℂ) ≠ 0 := by
      rw [hΛ_eq]; exact mul_ne_zero hGamma hζ
    -- Assemble via r325 off-pole factorization
    rw [riemannXiEntire_eq_completed hs0 hs1]
    apply div_ne_zero
    · exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hΛ
    · norm_num

/-! ## §5 — Left vertical `ξ⟨0, t⟩ ≠ 0` for every real `t`

Via r326's `riemannXiEntire_one_sub`: `ξ(⟨0, t⟩) = ξ(1 - ⟨0, t⟩) = ξ(⟨1, -t⟩)`,
which is nonzero by the right-vertical theorem at `-t`. -/

/-- `1 - ⟨0, t⟩ = ⟨1, -t⟩` as a complex identity. -/
lemma one_sub_mk_zero (t : ℝ) : (1 : ℂ) - ⟨0, t⟩ = ⟨1, -t⟩ := by
  apply Complex.ext <;> simp

/-- **`riemannXiEntire_ne_zero_on_re_zero`** — the entire ξ does not vanish
anywhere on the vertical line `Re s = 0`.  Direct from the right-vertical
theorem and the r326 functional equation. -/
theorem riemannXiEntire_ne_zero_on_re_zero (t : ℝ) :
    riemannXiEntire ⟨0, t⟩ ≠ 0 := by
  have hFE : riemannXiEntire ⟨0, t⟩ = riemannXiEntire (1 - ⟨0, t⟩) :=
    (riemannXiEntire_one_sub _).symm
  rw [hFE, one_sub_mk_zero]
  exact riemannXiEntire_ne_zero_on_re_one (-t)

/-! ## §6 — Top edge halving (`Im s = 15`, right half → full edge) -/

/-- **`top_edge_nonvanishing_of_right_half`** — if `ξ⟨σ, 15⟩ ≠ 0` for every
`σ ∈ [1/2, 1]`, then the same holds for every `σ ∈ [0, 1]`.

For `σ ∈ [0, 1/2]`, set `σ' := 1 - σ ∈ [1/2, 1]`.  r326's
`riemannXiEntire_reflect_vertical` gives
`ξ⟨1 - σ, 15⟩ = conj (ξ⟨σ, 15⟩)`, and `conj z ≠ 0 ↔ z ≠ 0`, so nonvanishing
at `σ'` transports to `σ`. -/
theorem top_edge_nonvanishing_of_right_half
    (h : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → riemannXiEntire ⟨σ, 15⟩ ≠ 0) :
    ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → riemannXiEntire ⟨σ, 15⟩ ≠ 0 := by
  intro σ h0 h1
  by_cases hσ : (1 : ℝ)/2 ≤ σ
  · exact h σ hσ h1
  · push_neg at hσ
    -- σ ∈ [0, 1/2).  Set σ' := 1 - σ ∈ (1/2, 1].
    have h1' : 1 - σ ≤ 1 := by linarith
    have h1'2 : (1 : ℝ)/2 ≤ 1 - σ := by linarith
    have hσ'_ne : riemannXiEntire ⟨1 - σ, 15⟩ ≠ 0 := h (1 - σ) h1'2 h1'
    -- reflect_vertical: ξ⟨1 - σ, 15⟩ = conj (ξ⟨σ, 15⟩)
    have hReflect : riemannXiEntire ⟨1 - σ, (15 : ℝ)⟩ =
        conj (riemannXiEntire ⟨σ, (15 : ℝ)⟩) :=
      riemannXiEntire_reflect_vertical σ 15
    rw [hReflect] at hσ'_ne
    -- conj z ≠ 0 ↔ z ≠ 0
    exact fun hz => hσ'_ne (by rw [hz]; simp)

/-! ## §7 — Bottom edge as residual

Classically `ξ(σ) > 0` for real `σ ∈ [0, 1]`, since:

  ξ(σ) = -σ(1-σ)/2 · π^(-σ/2) · Γ(σ/2) · ζ(σ)

with `-σ(1-σ) ≤ 0` on `[0, 1]` (vanishing only at endpoints),
`π^(-σ/2) > 0`, `Γ(σ/2) > 0` for `σ > 0`, and `ζ(σ) < 0` for
`σ ∈ (0, 1)` (Dirichlet-eta representation).  The endpoints
`σ = 0, 1` give `ξ = 1/2` (see §3), so `ξ` is positive on the whole
closed interval.

However, `ζ(σ) < 0` on `(0, 1)` is NOT a named theorem in mathlib
`v4.24.0-rc1`, and the directive forbids smuggling it as external
fact.  We therefore package it as the residual predicate below and
require it as a hypothesis. -/

/-- **`BottomEdgeZeroFree`** — the residual nonvanishing condition on the
real interval `[0, 1]`.  The endpoints are already discharged by the
corner values (see `bottom_edge_endpoints_ne_zero` below); the genuine
residual content is the open interior `σ ∈ (0, 1)`. -/
def BottomEdgeZeroFree : Prop :=
  ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → riemannXiEntire (σ : ℂ) ≠ 0

/-- The endpoints of the bottom edge (`σ = 0`, `σ = 1`) do NOT rely on
`BottomEdgeZeroFree`: they are handled by `riemannXiEntire_zero_ne_zero`
and `riemannXiEntire_one_ne_zero`.  Only the open interior `σ ∈ (0, 1)`
is genuinely residual. -/
theorem bottom_edge_endpoints_ne_zero :
    riemannXiEntire ((0 : ℝ) : ℂ) ≠ 0 ∧
    riemannXiEntire ((1 : ℝ) : ℂ) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · show riemannXiEntire (0 : ℂ) ≠ 0
    exact riemannXiEntire_zero_ne_zero
  · show riemannXiEntire (1 : ℂ) ≠ 0
    exact riemannXiEntire_one_ne_zero

/-! ## §8 — Main boundary reduction -/

/-- **`boundary_zero_free_of_top_right_half_and_bottom`** — given
`riemannXiEntire ⟨σ, 15⟩ ≠ 0` for `σ ∈ [1/2, 1]` (the H_TOP residual) and
`BottomEdgeZeroFree` (the H_BOTTOM residual), the entire ξ does not
vanish anywhere on the border of the T = 15 rectangle.

This is exactly the border hypothesis of r327's
`rectangleZeroCount_riemannXiEntire`. -/
theorem boundary_zero_free_of_top_right_half_and_bottom
    (hTop : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → riemannXiEntire ⟨σ, 15⟩ ≠ 0)
    (hBottom : BottomEdgeZeroFree) :
    ∀ s ∈ RectangleBorder z15 w15, riemannXiEntire s ≠ 0 := by
  intro s hs
  -- RectangleBorder z15 w15 =
  --   [[0, 1]] ×ℂ {0} ∪ {0} ×ℂ [[0, 15]] ∪
  --     [[0, 1]] ×ℂ {15} ∪ {1} ×ℂ [[0, 15]]
  simp only [RectangleBorder, z15_re, z15_im, w15_re, w15_im,
             Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff] at hs
  rcases hs with ⟨⟨⟨hRe, hIm⟩ | ⟨hRe, hIm⟩⟩ | ⟨hRe, hIm⟩⟩ | ⟨hRe, hIm⟩
  · -- bottom edge: s.re ∈ [[0, 1]], s.im = 0
    -- Rewrite s = ⟨s.re, 0⟩ = (s.re : ℂ), then apply BottomEdgeZeroFree.
    have hs_form : s = ((s.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hIm
    have h_re : 0 ≤ s.re ∧ s.re ≤ 1 := by
      rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 1)] at hRe
      exact ⟨hRe.1, hRe.2⟩
    rw [hs_form]
    exact hBottom s.re h_re.1 h_re.2
  · -- left edge: s.re = 0, s.im ∈ [[0, 15]]
    have hs_form : s = ⟨0, s.im⟩ := by
      apply Complex.ext
      · simpa using hRe
      · simp
    rw [hs_form]
    exact riemannXiEntire_ne_zero_on_re_zero s.im
  · -- top edge: s.re ∈ [[0, 1]], s.im = 15
    have hs_form : s = ⟨s.re, 15⟩ := by
      apply Complex.ext
      · simp
      · simpa using hIm
    have h_re : 0 ≤ s.re ∧ s.re ≤ 1 := by
      rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 1)] at hRe
      exact ⟨hRe.1, hRe.2⟩
    rw [hs_form]
    exact top_edge_nonvanishing_of_right_half hTop s.re h_re.1 h_re.2
  · -- right edge: s.re = 1, s.im ∈ [[0, 15]]
    have hs_form : s = ⟨1, s.im⟩ := by
      apply Complex.ext
      · simpa using hRe
      · simp
    rw [hs_form]
    exact riemannXiEntire_ne_zero_on_re_one s.im

/-! ## §9 — Instantiating r327 at (z15, w15) -/

/-- The SW corner `z15 = 0` is on `RectangleBorder z15 w15` (it is the
south-west corner point). -/
lemma z15_mem_RectangleBorder : z15 ∈ RectangleBorder z15 w15 :=
  Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))

/-- `ξ(z15) = 1/2 ≠ 0` — the SW corner nonvanishing witness needed by
`finite_zeros_rectangle`. -/
theorem riemannXiEntire_z15_ne_zero : riemannXiEntire z15 ≠ 0 := by
  show riemannXiEntire (⟨0, 0⟩ : ℂ) ≠ 0
  have : (⟨0, 0⟩ : ℂ) = 0 := by apply Complex.ext <;> simp
  rw [this]
  exact riemannXiEntire_zero_ne_zero

/-- **`xi_T15_exact_zero_count_identity`** — the exact zero-count identity
for the classical entire Riemann ξ on the T = 15 rectangle.  Instantiates
r327's `rectangleZeroCount_riemannXiEntire_self_contained` at
`(z15, w15) = (0, 1 + 15 I)` under the two boundary residuals of r328.

Endpoint form:

  `RectangleIntegral' (fun s => logDeriv riemannXiEntire s) z15 w15`
    `= ∑ ρ ∈ Z, (analyticOrderNatAt riemannXiEntire ρ : ℂ)`

where `Z` is the finite set of interior zeros of `riemannXiEntire` inside
the rectangle, produced automatically from `finite_zeros_rectangle` via
the SW-corner nonvanishing witness `riemannXiEntire z15 = 1/2 ≠ 0`.

The `hTop` hypothesis captures ONLY the top half-edge `σ ∈ [1/2, 1]`
(the left half is discharged by r326 symmetry inside
`boundary_zero_free_of_top_right_half_and_bottom`).  The `hBottom`
hypothesis captures the full bottom edge `σ ∈ [0, 1]`, with the
endpoints already provable but the open interior classical-but-unformalized. -/
theorem xi_T15_exact_zero_count_identity
    (hTop : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → riemannXiEntire ⟨σ, 15⟩ ≠ 0)
    (hBottom : BottomEdgeZeroFree) :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) z15 w15
      = ∑ ρ ∈ (finite_zeros_rectangle
              (riemannXiEntire_analyticOnNhd _)
              (rectangleBorder_subset_rectangle z15 w15 z15_mem_RectangleBorder)
              (boundary_zero_free_of_top_right_half_and_bottom hTop hBottom z15
                  z15_mem_RectangleBorder)).toFinset,
          (analyticOrderNatAt riemannXiEntire ρ : ℂ) := by
  exact rectangleZeroCount_riemannXiEntire_self_contained
    z15_re_le_w15_re z15_im_le_w15_im
    (boundary_zero_free_of_top_right_half_and_bottom hTop hBottom)

end PrincipiaTractalis.RiemannXiBoundaryT15

/-! ## §Axiom check — build-time guarantee -/

#print axioms PrincipiaTractalis.RiemannXiBoundaryT15.riemannXiEntire_zero_value
#print axioms PrincipiaTractalis.RiemannXiBoundaryT15.riemannXiEntire_one_value
#print axioms PrincipiaTractalis.RiemannXiBoundaryT15.riemannXiEntire_ne_zero_on_re_one
#print axioms PrincipiaTractalis.RiemannXiBoundaryT15.riemannXiEntire_ne_zero_on_re_zero
#print axioms PrincipiaTractalis.RiemannXiBoundaryT15.top_edge_nonvanishing_of_right_half
#print axioms PrincipiaTractalis.RiemannXiBoundaryT15.bottom_edge_endpoints_ne_zero
#print axioms
  PrincipiaTractalis.RiemannXiBoundaryT15.boundary_zero_free_of_top_right_half_and_bottom
#print axioms PrincipiaTractalis.RiemannXiBoundaryT15.xi_T15_exact_zero_count_identity
