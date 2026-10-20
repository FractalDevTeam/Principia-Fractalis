/-
# PF.Analytic.R1BoxLocalL_2026_10_20

**The generic R1 box, parametric in `(c, r, M)`, carrying the box-local `L₀`.**

Every landed pilot hardcodes `Mc_lb = 1/8`, and `Re ξ(1+ic) ≥ 1/8` fails past
`c = 7.50194`. That constant — not `L`, and not the enclosure — is what pins
the provable march. This module removes it.

## What replaces the two hardcoded constants

| | before | here |
|---|---|---|
| `Mc_lb` | `1/8` (fails past `c = 7.502`) | a parameter `M` |
| `L` | `1` (uniform Gate-2; 193 boxes to reach 13) | `L0 (c − r)` (19 boxes) |

`R1_box_centered_of_lb` needs `L·r < Mc_lb`. With `L₀` that is
`L0 (c − r)·r ≈ 0.0069` at `r = 1/16`, against the old `1·(1/16) = 0.0625`
which had to be beaten by a `Mc_lb` that itself decays like `Re ξ`.

## The producer-facing theorem

`box_of_enclosure` takes **exactly three** hypotheses: the two `Λ₀` upper
bounds the panel chain already produces, and one rational inequality

  `L0 (c − r) · r < (1 − c²·R_ub − c·I_ub) / 2`

whose right side is precisely the best lower bound on `Re ξ(1+ic)` those two
enclosures support. So a per-box emission is: two bounds, one `norm_num`.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-20.
-/

import PF.Analytic.DerivEdgeReLocalL_2026_10_20
import PF.Analytic.CenteredFormBridge_2026_10_13

set_option autoImplicit false

namespace PrincipiaTractalis
namespace R1BoxLocalL20261020

open Complex Real MeasureTheory Set
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.DerivEdgeReLocalL20261020
open scoped Real

noncomputable section

/-! ## §1 — The centre value, for an arbitrary target `M` -/

/-- **`M ≤ Re ξ(1+ic)` for ANY target `M`**, given upper bounds on
`Re Λ₀`, `Im Λ₀` and the corresponding gate inequality.

`Re ξ(1+ic) = (1 − c²·Re Λ₀ − c·Im Λ₀)/2`, so `M ≤ Re ξ` is exactly
`c²·Re Λ₀ + c·Im Λ₀ ≤ 1 − 2M`. The landed pilots are the case `M = 1/8`,
where the right side is `3/4`. -/
theorem hvalue_lb_param {c M R_ub I_ub : ℝ} (hc0 : 0 ≤ c)
    (hR_ub : (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).re ≤ R_ub)
    (hI_ub : (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).im ≤ I_ub)
    (h_gate : c ^ 2 * R_ub + c * I_ub ≤ 1 - 2 * M) :
    M ≤ (riemannXiEntire (⟨1, c⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  set re := (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).re with hre_def
  set im := (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).im with him_def
  have hsq : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
  have h1 : c ^ 2 * re ≤ c ^ 2 * R_ub := mul_le_mul_of_nonneg_left hR_ub hsq
  have h2 : c * im ≤ c * I_ub := mul_le_mul_of_nonneg_left hI_ub hc0
  -- `1 + A - B` parses as `(1 + A) - B`, so `A - B` is not a subterm and a
  -- rewrite cannot fire; linarith normalises the ring expressions itself.
  linarith [h1, h2, h_gate]

/-! ## §2 — The box -/

/-- **The R1 box at `(c, r)` with target `M` and `L := L0 (c − r)`.**

All four of `R1_box_centered_of_lb`'s hypotheses are discharged from the two
`Λ₀` enclosures, the gate inequality, and the margin `L0 (c − r)·r < M`. -/
theorem box_param {c r M R_ub I_ub : ℝ} (hr : 0 ≤ r) (hcr : r < c)
    (hR_ub : (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).re ≤ R_ub)
    (hI_ub : (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).im ≤ I_ub)
    (h_gate : c ^ 2 * R_ub + c * I_ub ≤ 1 - 2 * M)
    (hmargin : L0 (c - r) * r < M) :
    ∀ t ∈ Icc (c - r) (c + r), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re :=
  R1_box_centered_of_lb (c := c) (r := r) (L := L0 (c - r)) (Mc_lb := M)
    hr
    (hvalue_lb_param (by linarith) hR_ub hI_ub h_gate)
    (deriv_edgeRe_le_on_box hr hcr)
    hmargin

/-- **★ THE PRODUCER-FACING FORM ★**

Three hypotheses: the two `Λ₀` upper bounds, and one rational inequality.
The target `M` is taken to be `(1 − c²·R_ub − c·I_ub)/2`, the sharpest lower
bound on `Re ξ(1+ic)` those two enclosures support, so the gate inequality
holds by equality and disappears. -/
theorem box_of_enclosure {c r R_ub I_ub : ℝ} (hr : 0 ≤ r) (hcr : r < c)
    (hR_ub : (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).re ≤ R_ub)
    (hI_ub : (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).im ≤ I_ub)
    (hmargin : L0 (c - r) * r < (1 - c ^ 2 * R_ub - c * I_ub) / 2) :
    ∀ t ∈ Icc (c - r) (c + r), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re :=
  box_param hr hcr hR_ub hI_ub (by linarith) hmargin

/-! ## §3 — The old shape is the special case `M = 1/8` -/

/-- Sanity: the landed pilots' `Mc_lb = 1/8`, `gate ≤ 3/4` shape is exactly
`box_param` at `M = 1/8`, since `1 − 2·(1/8) = 3/4`. Kept so the
generalisation is visibly a generalisation and not a different statement. -/
theorem box_at_one_eighth {c r R_ub I_ub : ℝ} (hr : 0 ≤ r) (hcr : r < c)
    (hR_ub : (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).re ≤ R_ub)
    (hI_ub : (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).im ≤ I_ub)
    (h_gate : c ^ 2 * R_ub + c * I_ub ≤ 3 / 4)
    (hmargin : L0 (c - r) * r < 1 / 8) :
    ∀ t ∈ Icc (c - r) (c + r), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re :=
  box_param hr hcr hR_ub hI_ub (by linarith) hmargin

end

end R1BoxLocalL20261020
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.R1BoxLocalL20261020.hvalue_lb_param
#print axioms PrincipiaTractalis.R1BoxLocalL20261020.box_param
#print axioms PrincipiaTractalis.R1BoxLocalL20261020.box_of_enclosure
#print axioms PrincipiaTractalis.R1BoxLocalL20261020.box_at_one_eighth
