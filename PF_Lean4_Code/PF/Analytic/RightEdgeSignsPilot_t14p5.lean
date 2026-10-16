/-
# RightEdgeSignsPilot_t14p5 — σ=1 point reduction at t = 29/2  (P6)

The analogue of the (nonexistent-in-repo) pilot reduction, specialised to the
SINGLE point `t = 29/2` (t = 14.5).  Mirrors `R3_box` of
`RightEdgeSignsProof_2026_10_09` but at one point instead of a segment, and feeds
on the certified `Λ₀(1+(29/2)i) = completedRiemannZeta₀(1+(29/2)i)` enclosure the
40-segment midpoint panels + `box0_envelope_le` produce
(`box14p5_re_enclosure` / `box14p5_im_enclosure`).

## Scope (honest)
Formalisation of a CLASSICALLY-KNOWN bounded fact: `Re ξ(1+(29/2)i) < 0` (R3 at
t = 14.5).  NOT the Clay Riemann Hypothesis.  This file is the pure reduction
layer: it carries NO numerics of its own — the single missing numeric input is
the certified `Λ₀` enclosure.  Everything here is `re_xi_edge` (kernel-clean) plus
monotonicity of multiplication by the nonnegative coefficients `(29/2)^2`, `29/2`.

## Margin note (why the full target needs BOTH parts)
`Re ξ(1+(29/2)i) = (1 - (29/2)^2·Re Λ₀ - (29/2)·Im Λ₀)/2`, and `(29/2)^2 = 210.25`.
With `Re Λ₀ ≥ 4737/10⁶` one gets `210.25·Re Λ₀ ≈ 0.99595 < 1`, so the real part
ALONE does not force the sign; the `(29/2)·Im Λ₀` term carries the rest.  Hence the
reduction keeps the Im lower bound as a genuine hypothesis (`re_xi_14p5_neg_of_edge_lb`)
or the full two-sided box (`re_xi_14p5_neg_of_edge_enclosure`).  No single-sided
overclaim.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RightEdgeSignsProof_2026_10_09

set_option autoImplicit false

namespace PrincipiaTractalis
namespace RightEdgeSignsPilot14p5

open Complex
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RightEdgeSignsProof20261009

noncomputable section

/-- **P6 — two-sided box reduction at the point `t = 29/2`.**  Given a certified
enclosure `Re Λ₀(1+(29/2)i) ∈ [reA,reB]`, `Im Λ₀(1+(29/2)i) ∈ [imA,imB]` and the
producer's rational arithmetic obligation `h_arith`, conclude
`Re ξ(1+(29/2)i) < 0`.  The exact point-analogue of `R3_box`. -/
theorem re_xi_14p5_neg_of_edge_enclosure
    {reA reB imA imB : ℝ}
    (h_reA : reA ≤ (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).re)
    (h_reB : (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).re ≤ reB)
    (h_imA : imA ≤ (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).im)
    (h_imB : (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).im ≤ imB)
    (h_arith : ∀ r s : ℝ, reA ≤ r → r ≤ reB → imA ≤ s → s ≤ imB →
        (1 - (29 / 2 : ℝ) ^ 2 * r - (29 / 2 : ℝ) * s) / 2 < 0) :
    (riemannXiEntire (⟨1, 29 / 2⟩ : ℂ)).re < 0 := by
  rw [re_xi_edge (29 / 2)]
  exact h_arith _ _ h_reA h_reB h_imA h_imB

/-- **P6 — lower-bound reduction at the point `t = 29/2`.**  The practical form the
enclosure feeds: certified LOWER bounds `Re Λ₀ ≥ reA`, `Im Λ₀ ≥ imA` and the single
rational key `1 < (29/2)^2·reA + (29/2)·imA` give `Re ξ(1+(29/2)i) < 0`.  Uses only
that `(29/2)^2 ≥ 0` and `29/2 ≥ 0` (both bounds are scaled by nonnegative
coefficients, so the worst corner is the pair of lower bounds). -/
theorem re_xi_14p5_neg_of_edge_lb
    {reA imA : ℝ}
    (h_reA : reA ≤ (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).re)
    (h_imA : imA ≤ (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).im)
    (h_key : (1 : ℝ) < (29 / 2 : ℝ) ^ 2 * reA + (29 / 2 : ℝ) * imA) :
    (riemannXiEntire (⟨1, 29 / 2⟩ : ℂ)).re < 0 := by
  rw [re_xi_edge (29 / 2)]
  have e1 : (29 / 2 : ℝ) ^ 2 * reA
      ≤ (29 / 2 : ℝ) ^ 2 * (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).re :=
    mul_le_mul_of_nonneg_left h_reA (by norm_num)
  have e2 : (29 / 2 : ℝ) * imA
      ≤ (29 / 2 : ℝ) * (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).im :=
    mul_le_mul_of_nonneg_left h_imA (by norm_num)
  linarith

end

#print axioms re_xi_14p5_neg_of_edge_enclosure
#print axioms re_xi_14p5_neg_of_edge_lb

end RightEdgeSignsPilot14p5
end PrincipiaTractalis
