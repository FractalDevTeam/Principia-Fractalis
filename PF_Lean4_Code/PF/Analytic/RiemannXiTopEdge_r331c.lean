/-
# r331c — TOP EDGE: `Re ξ < 0` on the whole segment `σ ∈ [0,1]` at `t = 15`

★ 2026-09-12 — the top-edge device, and why the obvious one is FALSE ★

## The problem this solves

The right edge of the T=15 rectangle is handled by keeping ξ off the negative
real axis, so the *principal* branch of `log ξ` stays continuous. The read-back
audit of 2026-09-08 showed that device **cannot** be reused on the top edge:

    ξ⟨1/2, 15⟩ = -7.0569795882e-04  +  (-4.8e-45)i        arg = -π exactly

ξ is real on the critical line (Hardy's Ξ), and `t = 15` is past the first zero
at `t ≈ 14.1347`, so the top edge passes **through** the principal branch cut,
exactly at `σ = 1/2`. Any "top edge ∈ slitPlane" lemma is false.

## The device that does work

The same numerics show `Re ξ⟨σ,15⟩ < 0` for **every** `σ ∈ [0,1]` — the top edge
lies in the open LEFT half-plane. So `-ξ` lies in the open right half-plane
there, which is inside `Complex.slitPlane`, and a branch of the logarithm is
available after that rotation.

## Why this is nearly free

r331b already proves the right half: `top15_re_lt_neg_1e4` gives
`Re ξ⟨σ,15⟩ < -1/10000` for `σ ∈ [1/2, 1]`.

r326's `riemannXiEntire_reflect_vertical` gives `ξ⟨1-σ,t⟩ = conj ξ⟨σ,t⟩`, hence
equal real parts. Applying it at `1-σ` turns any `σ ∈ [0,1/2]` into
`1-σ ∈ [1/2,1]`, which is r331b's range.

So the top edge is **r331b plus one reflection**, not new analysis. The
numerical recon confirms the reflection to seven digits:

    σ=0 :  ξ = -8.059477e-04 - 1.661340e-04 i
    σ=1 :  ξ = -8.059477e-04 + 1.661340e-04 i        same Re, conjugate Im

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiTopUnion
import PF.Analytic.RiemannXiSymmetries_r326

namespace PrincipiaTractalis
namespace TopEdgeR331c

open PrincipiaTractalis.RiemannXiSymmetries
open scoped ComplexConjugate

/-- **Reflection transfers the real part across `σ ↦ 1-σ`.** -/
theorem re_reflect (σ t : ℝ) :
    (riemannXiEntire ⟨σ, t⟩).re = (riemannXiEntire ⟨1 - σ, t⟩).re := by
  rw [riemannXiEntire_reflect_vertical σ t, Complex.conj_re]

/-- **★★★ r331c.TOP — `Re ξ(σ + 15i) < -1/10000` on the FULL segment
`σ ∈ [0,1]` ★★★**

r331b gives `[1/2, 1]`; reflection gives `[0, 1/2]`. The top edge therefore
lies in the open left half-plane, and `-ξ` lies in the right half-plane, where a
logarithm branch is available. -/
theorem top_edge_re_neg_full {σ : ℝ} (h0 : (0:ℝ) ≤ σ) (h1 : σ ≤ 1) :
    (riemannXiEntire ⟨σ, 15⟩).re < -(1/10000 : ℝ) := by
  rcases le_or_lt (1/2 : ℝ) σ with hσ | hσ
  · exact RiemannXiTopUnion.top15_re_lt_neg_1e4 hσ h1
  · -- σ < 1/2, so 1 - σ ∈ [1/2, 1]; reflect and apply r331b there.
    have hlo : (1/2 : ℝ) ≤ 1 - σ := by linarith
    have hhi : (1 : ℝ) - σ ≤ 1 := by linarith
    have h := RiemannXiTopUnion.top15_re_lt_neg_1e4 hlo hhi
    rwa [← re_reflect σ 15] at h

/-- **r331c.TOP' — the top edge avoids the closed right half-plane.**
Stated as the positivity of `-ξ`'s real part, which is the form the rotated
logarithm branch consumes. -/
theorem top_edge_neg_xi_re_pos {σ : ℝ} (h0 : (0:ℝ) ≤ σ) (h1 : σ ≤ 1) :
    (0:ℝ) < (-(riemannXiEntire ⟨σ, 15⟩)).re := by
  have h := top_edge_re_neg_full h0 h1
  simp only [Complex.neg_re]
  linarith

/-- **r331c.TOP'' — ξ does not vanish on the top edge.**
Immediate, and worth having separately: a number with negative real part is
nonzero. -/
theorem top_edge_ne_zero {σ : ℝ} (h0 : (0:ℝ) ≤ σ) (h1 : σ ≤ 1) :
    riemannXiEntire ⟨σ, 15⟩ ≠ 0 := by
  intro hz
  have h := top_edge_re_neg_full h0 h1
  rw [hz] at h
  simp at h
  linarith

/-! ## Axiom check -/

#print axioms re_reflect
#print axioms top_edge_re_neg_full
#print axioms top_edge_neg_xi_re_pos
#print axioms top_edge_ne_zero

end TopEdgeR331c
end PrincipiaTractalis
