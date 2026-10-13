/-
# r331e — FULL RECTANGLE `[0,1] × [-15, 15]`: BOUNDARY ZERO-FREE + COUNT IDENTITY

★ 2026-09-28 — composes r331b (right edge), r331c (top edge at t = 15),
  r331d (bottom edge at t = -15), and r326 (functional equation → left edge)
  into the full-rectangle boundary-nonvanishing statement, then instantiates
  r327's argument principle on that rectangle. ★

## What this file gives (all kernel-clean)

- **`zF`, `wF`** — the full-rectangle corners: `zF := ⟨0, -15⟩`, `wF := ⟨1, 15⟩`.
- **`full_rectangle_boundary_zero_free`** — `∀ s ∈ RectangleBorder zF wF,
  riemannXiEntire s ≠ 0`.  Unconditional composition of the four edge
  nonvanishing results.
- **`zF_mem_RectangleBorder`** — the SW corner is on the border.
- **`riemannXiEntire_zF_ne_zero`** — `ξ(zF) = ξ⟨0, -15⟩ ≠ 0` (from left-edge
  nonvanishing at `t = -15`), the SW-corner witness needed by
  `finite_zeros_rectangle`.
- **`xi_full_rectangle_zero_count_identity`** — instantiates r327's
  `rectangleZeroCount_riemannXiEntire_self_contained` at `(zF, wF)`.
  Endpoint form:
    `RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF`
      `= ∑ ρ ∈ Z, (analyticOrderNatAt riemannXiEntire ρ : ℂ)`
  where `Z` is the finite set of interior zeros produced automatically by
  `finite_zeros_rectangle`.

## Scope — explicit

* IS: unconditional exact zero-count identity for `riemannXiEntire` on the
  full rectangle `[0,1] × [-15, 15]` in the critical strip.
* IS: kernel-clean, no `sorry`, no `native_decide`, no `axiom`, no
  `Prop := True`.
* NOT: an evaluation of the resulting contour integer.
* NOT: a proof that the multiplicity sum equals the on-line count.
* NOT: a proof that all interior zeros lie on the critical line.
* NOT: `riemannHypothesis_below_15`.  That requires the additional multiplicity-
  to-on-line-count argument, which is not landed here (see
  `codex/GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-09-27.md` Rank-1 note).

The full-rectangle count identity is the natural analog of
`RiemannXiT15Endgame.xi_T15_zero_count_identity_unconditional` (which handles
the top-half rectangle `[0,1] × [0, 15]`).  The full rectangle is symmetric
under `s ↦ conj s` by r326.B; this file makes the boundary-nonvanishing
extension to negative-`t` explicit via r331d.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiRectangleCount_r327
import PF.Analytic.RiemannXiBoundaryT15_r328
import PF.Analytic.RiemannXiTopEdge_r331c
import PF.Analytic.RiemannXiBottomEdgeAtMinus15_r331d

namespace PrincipiaTractalis
namespace FullRectangleBoundaryR331e

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiSymmetries
open PrincipiaTractalis.RiemannXiRectangleCount
open PrincipiaTractalis.RiemannXiBoundaryT15
open PrincipiaTractalis.TopEdgeR331c
open PrincipiaTractalis.BottomEdgeR331d
open Zeta23.Analytic

/-! ## §1 — Full-rectangle corners -/

/-- **SW corner of the full rectangle: `⟨0, -15⟩`.** -/
def zF : ℂ := ⟨0, -15⟩

/-- **NE corner of the full rectangle: `⟨1, 15⟩`.** -/
def wF : ℂ := ⟨1, 15⟩

lemma zF_re : zF.re = 0 := rfl
lemma zF_im : zF.im = -15 := rfl
lemma wF_re : wF.re = 1 := rfl
lemma wF_im : wF.im = 15 := rfl

/-- The full rectangle is well-oriented: real-part low ≤ high. -/
lemma zF_re_le_wF_re : zF.re ≤ wF.re := by
  show (0 : ℝ) ≤ 1; linarith

/-- The full rectangle is well-oriented: imag-part low ≤ high. -/
lemma zF_im_le_wF_im : zF.im ≤ wF.im := by
  show (-15 : ℝ) ≤ 15; linarith

/-! ## §2 — Boundary zero-free on the full rectangle -/

/-- **`full_rectangle_boundary_zero_free`** — `riemannXiEntire` does not vanish
anywhere on the border of the full rectangle `[0,1] × [-15, 15]`.

Composes:
* Bottom edge (`t = -15`, `σ ∈ [0,1]`): r331d's `bottom_edge_ne_zero`.
* Left edge (`σ = 0`, `t ∈ [-15, 15]`): r328's `riemannXiEntire_ne_zero_on_re_zero`.
* Top edge (`t = 15`, `σ ∈ [0,1]`): r331c's `top_edge_ne_zero`.
* Right edge (`σ = 1`, `t ∈ [-15, 15]`): r328's `riemannXiEntire_ne_zero_on_re_one`.

This is the border hypothesis of r327's `rectangleZeroCount_riemannXiEntire`. -/
theorem full_rectangle_boundary_zero_free :
    ∀ s ∈ RectangleBorder zF wF, riemannXiEntire s ≠ 0 := by
  intro s hs
  simp only [RectangleBorder, zF_re, zF_im, wF_re, wF_im,
             Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff] at hs
  rcases hs with ⟨⟨⟨hRe, hIm⟩ | ⟨hRe, hIm⟩⟩ | ⟨hRe, hIm⟩⟩ | ⟨hRe, hIm⟩
  · -- bottom edge: s.re ∈ [[0, 1]], s.im = -15
    have hs_form : s = ⟨s.re, -15⟩ := by
      apply Complex.ext
      · simp
      · simpa using hIm
    have h_re : 0 ≤ s.re ∧ s.re ≤ 1 := by
      rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 1)] at hRe
      exact ⟨hRe.1, hRe.2⟩
    rw [hs_form]
    exact bottom_edge_ne_zero h_re.1 h_re.2
  · -- left edge: s.re = 0, s.im ∈ [[-15, 15]]
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
    exact top_edge_ne_zero h_re.1 h_re.2
  · -- right edge: s.re = 1, s.im ∈ [[-15, 15]]
    have hs_form : s = ⟨1, s.im⟩ := by
      apply Complex.ext
      · simpa using hRe
      · simp
    rw [hs_form]
    exact riemannXiEntire_ne_zero_on_re_one s.im

/-! ## §3 — SW-corner membership + nonvanishing witness -/

/-- The SW corner `zF = ⟨0, -15⟩` is on `RectangleBorder zF wF`. -/
lemma zF_mem_RectangleBorder : zF ∈ RectangleBorder zF wF :=
  Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))

/-- `ξ(zF) = ξ⟨0, -15⟩ ≠ 0` — the SW-corner nonvanishing witness needed by
`finite_zeros_rectangle`.  Direct from `riemannXiEntire_ne_zero_on_re_zero`. -/
theorem riemannXiEntire_zF_ne_zero : riemannXiEntire zF ≠ 0 := by
  show riemannXiEntire (⟨0, -15⟩ : ℂ) ≠ 0
  exact riemannXiEntire_ne_zero_on_re_zero (-15)

/-! ## §4 — The unconditional full-rectangle zero-count identity -/

/-- **★★★ `xi_full_rectangle_zero_count_identity` ★★★** — the exact zero-count
identity for the classical entire Riemann ξ on the full rectangle
`[0,1] × [-15, 15]`, with NO remaining hypotheses.

Instantiates r327's `rectangleZeroCount_riemannXiEntire_self_contained` at
`(zF, wF) = (⟨0, -15⟩, ⟨1, 15⟩)`.  The interior zero set is produced
automatically from `finite_zeros_rectangle` using the SW-corner nonvanishing
witness `ξ(zF) ≠ 0`.

Endpoint form:
    `RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF`
      `= ∑ ρ ∈ Z, (analyticOrderNatAt riemannXiEntire ρ : ℂ)`

**What this does NOT do.** It does not evaluate the contour integral, does not
give a numerical bound on the multiplicity sum, and does not show that all
interior zeros lie on the critical line.  Those are downstream tasks separate
from this landing (see the docstring's Scope section). -/
theorem xi_full_rectangle_zero_count_identity :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF
      = ∑ ρ ∈ (finite_zeros_rectangle
              (riemannXiEntire_analyticOnNhd _)
              (rectangleBorder_subset_rectangle zF wF zF_mem_RectangleBorder)
              (full_rectangle_boundary_zero_free zF
                  zF_mem_RectangleBorder)).toFinset,
          (analyticOrderNatAt riemannXiEntire ρ : ℂ) :=
  rectangleZeroCount_riemannXiEntire_self_contained
    zF_re_le_wF_re zF_im_le_wF_im full_rectangle_boundary_zero_free

/-! ## §5 — Interior zeros of ξ are interior zeros of ζ (open-strip bridge) -/

/-- The open interior of the full rectangle sits in the open critical strip.
For every `s ∈ Rectangle zF wF \ RectangleBorder zF wF`, `0 < s.re < 1`. -/
lemma interior_re_strict {s : ℂ} (hs : s ∈ Rectangle zF wF)
    (hs_border : s ∉ RectangleBorder zF wF) :
    0 < s.re ∧ s.re < 1 := by
  -- Rectangle zF wF = [[0,1]] ×ℂ [[-15, 15]], i.e., s.re ∈ [0,1] and s.im ∈ [-15,15].
  simp only [Rectangle, zF_re, zF_im, wF_re, wF_im, Complex.mem_reProdIm] at hs
  obtain ⟨hRe, hIm⟩ := hs
  rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 1)] at hRe
  -- Exclude the border cases s.re = 0 (left edge) and s.re = 1 (right edge) by hs_border.
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hRe.1 with hRe0 | hRe0
    · -- s.re = 0 would put s on the left edge; contradict hs_border.
      exfalso
      apply hs_border
      right
      rw [Set.uIcc_of_le (by linarith : (-15 : ℝ) ≤ 15)] at hIm
      exact ⟨hRe0.symm, hIm⟩
    · exact hRe0
  · rcases eq_or_lt_of_le hRe.2 with hRe1 | hRe1
    · -- s.re = 1 would put s on the right edge; contradict hs_border.
      exfalso
      apply hs_border
      left; right
      rw [Set.uIcc_of_le (by linarith : (-15 : ℝ) ≤ 15)] at hIm
      exact ⟨hRe1, hIm⟩
    · exact hRe1

/-- **`interior_xi_zero_iff_zeta_zero`** — for every interior point of the full
rectangle, `riemannXiEntire s = 0 ↔ riemannZeta s = 0`.

Direct from `interior_re_strict` + r325's
`riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip`. -/
theorem interior_xi_zero_iff_zeta_zero {s : ℂ} (hs : s ∈ Rectangle zF wF)
    (hs_border : s ∉ RectangleBorder zF wF) :
    riemannXiEntire s = 0 ↔ riemannZeta s = 0 := by
  obtain ⟨hRe0, hRe1⟩ := interior_re_strict hs hs_border
  exact riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip hRe0 hRe1

end FullRectangleBoundaryR331e
end PrincipiaTractalis

/-! ## §6 — Axiom check -/

#print axioms
  PrincipiaTractalis.FullRectangleBoundaryR331e.full_rectangle_boundary_zero_free
#print axioms
  PrincipiaTractalis.FullRectangleBoundaryR331e.riemannXiEntire_zF_ne_zero
#print axioms
  PrincipiaTractalis.FullRectangleBoundaryR331e.xi_full_rectangle_zero_count_identity
#print axioms
  PrincipiaTractalis.FullRectangleBoundaryR331e.interior_xi_zero_iff_zeta_zero
