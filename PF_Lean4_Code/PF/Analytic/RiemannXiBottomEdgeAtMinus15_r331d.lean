/-
# r331d — BOTTOM EDGE: `Re ξ < 0` on the whole segment `σ ∈ [0,1]` at `t = -15`

★ 2026-09-27 — the bottom-edge counterpart to r331c, via one conjugation step ★

## The problem this solves

r331c handled the TOP edge `t = 15` via r331b (right edge) plus the σ-reflection
`riemannXiEntire_reflect_vertical`. The BOTTOM edge `t = -15` closes the
remaining side of the ξ-rectangle in the critical strip
`0 ≤ σ ≤ 1, -15 ≤ t ≤ 15`. The same real-part negativity holds, by a
*different* symmetry — the global conjugation identity from r326.

## The device

`(⟨σ, -15⟩ : ℂ) = conj ⟨σ, 15⟩`, so by `riemannXiEntire_conj` (r326.B),
`ξ⟨σ, -15⟩ = conj (ξ⟨σ, 15⟩)`. Taking real parts:

    (ξ⟨σ, -15⟩).re = (conj ξ⟨σ, 15⟩).re = (ξ⟨σ, 15⟩).re.

The bottom edge inherits the real part of the top edge. r331c's
`top_edge_re_neg_full` therefore transports directly.

## Why this is (also) nearly free

Once r331c ships, the bottom edge is a one-step consequence: apply
`riemannXiEntire_conj` at `s = ⟨σ, 15⟩` and take `Complex.conj_re`. No
new analysis is required.

## What this completes

Together with r331b (right edge, `σ = 1`), r331c (top edge, `t = 15`),
r331d (this file, bottom edge, `t = -15`), and the vertical-reflection
transfer to the left edge via `re_reflect`, the four sides of the
ξ-rectangle `[0,1] × [-15, 15]` are boundary-nonvanishing with a
kernel-certified negative-real-part margin. The argument-principle
threading in r327 consumes this boundary to conclude zero non-trivial
`riemannZeta` zeros off the critical line inside the rectangle.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiTopEdge_r331c
import PF.Analytic.RiemannXiSymmetries_r326

namespace PrincipiaTractalis
namespace BottomEdgeR331d

open PrincipiaTractalis.RiemannXiSymmetries
open PrincipiaTractalis.TopEdgeR331c
open PrincipiaTractalis.RiemannXiEntire
open scoped ComplexConjugate

/-! ## §1 — The complex identity `⟨σ, -15⟩ = conj ⟨σ, 15⟩` -/

/-- **`neg15_eq_conj_15`** — for every real `σ`,
`(σ - 15i : ℂ) = conj (σ + 15i : ℂ)`. -/
lemma neg15_eq_conj_15 (σ : ℝ) :
    (⟨σ, -15⟩ : ℂ) = conj (⟨σ, 15⟩ : ℂ) := by
  apply Complex.ext
  · simp [Complex.conj_re]
  · simp [Complex.conj_im]

/-! ## §2 — Real-part transfer across the conjugation `t ↦ -t` -/

/-- **`re_conj_at_neg_15`** — the real part of ξ at `⟨σ, -15⟩` equals its
real part at `⟨σ, 15⟩`, via `riemannXiEntire_conj` (r326.B) and
`Complex.conj_re`. -/
theorem re_conj_at_neg_15 (σ : ℝ) :
    (riemannXiEntire ⟨σ, -15⟩).re = (riemannXiEntire ⟨σ, 15⟩).re := by
  rw [neg15_eq_conj_15 σ, riemannXiEntire_conj, Complex.conj_re]

/-! ## §3 — r331d bottom-edge theorems -/

/-- **★★★ r331d.BOTTOM — `Re ξ(σ - 15i) < -1/10000` on the FULL segment
`σ ∈ [0,1]` ★★★**

Direct consequence of r331c.`top_edge_re_neg_full` + `re_conj_at_neg_15`. -/
theorem bottom_edge_re_neg_full {σ : ℝ} (h0 : (0:ℝ) ≤ σ) (h1 : σ ≤ 1) :
    (riemannXiEntire ⟨σ, -15⟩).re < -(1/10000 : ℝ) := by
  rw [re_conj_at_neg_15 σ]
  exact top_edge_re_neg_full h0 h1

/-- **r331d.BOTTOM' — the bottom edge avoids the closed right half-plane.**
Stated as the positivity of `-ξ`'s real part, the form the rotated
logarithm branch consumes in r327. -/
theorem bottom_edge_neg_xi_re_pos {σ : ℝ} (h0 : (0:ℝ) ≤ σ) (h1 : σ ≤ 1) :
    (0:ℝ) < (-(riemannXiEntire ⟨σ, -15⟩)).re := by
  have h := bottom_edge_re_neg_full h0 h1
  simp only [Complex.neg_re]
  linarith

/-- **r331d.BOTTOM'' — ξ does not vanish on the bottom edge.**
A number with negative real part is nonzero. -/
theorem bottom_edge_ne_zero {σ : ℝ} (h0 : (0:ℝ) ≤ σ) (h1 : σ ≤ 1) :
    riemannXiEntire ⟨σ, -15⟩ ≠ 0 := by
  intro hz
  have h := bottom_edge_re_neg_full h0 h1
  rw [hz] at h
  simp at h
  linarith

/-! ## §4 — Axiom check -/

#print axioms neg15_eq_conj_15
#print axioms re_conj_at_neg_15
#print axioms bottom_edge_re_neg_full
#print axioms bottom_edge_neg_xi_re_pos
#print axioms bottom_edge_ne_zero

end BottomEdgeR331d
end PrincipiaTractalis
