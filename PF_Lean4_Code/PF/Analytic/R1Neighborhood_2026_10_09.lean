/-
# R1Neighborhood_2026_10_09 — R1 upgraded from one point to a positive-length interval

## What this file does, in one paragraph

`PF/Analytic/RightEdgeSignsProof_2026_10_09.lean` proves R1 at the single point
`t = 0` (`R1_at_zero : 0 < (ξ(1)).re`, because `ξ(1) = 1/2`) and states the open
segment fact R1 : `∀ t ∈ [0,13], 0 < (ξ(1+it)).re`. This file upgrades the single
point to a genuine POSITIVE-LENGTH interval, by continuity: there is a `δ > 0` with

    ∀ t ∈ [0, δ],  0 < (riemannXiEntire (1+it)).re.

The map `t ↦ (riemannXiEntire (1+it)).re` is continuous `ℝ → ℝ`
(`riemannXiEntire` is entire — `differentiable_riemannXiEntire`, r325 — composed
with the continuous line `t ↦ ⟨1,t⟩` and `Complex.re`), and is `1/2 > 0` at
`t = 0` (`R1_at_zero_local`, re-proved here directly from the r325 definition:
the polynomial factor `s(s-1)` vanishes at `s = 1`, so `ξ(1) = 1/2` with no zeta
value needed). A continuous real function positive at a point is positive on an
open neighborhood; taking an explicit radius from that neighborhood gives `δ`.

## Honesty notes — scope, stated plainly

* This does **NOT** close R1. R1 needs the WHOLE closed interval `[0,13]`; this
  file proves it only on `[0,δ]` for some `δ > 0` produced by continuity. The
  remaining segment `[δ,13]` is still open and still requires the absent certified
  `t`-boxed `Λ₀` producer (RightEdgeSignsProof_2026_10_09 header, route §9).
* The `∃ δ` is **not** vacuous: `δ` must satisfy the real predicate
  `0 < δ ∧ ∀ t ∈ [0,δ], 0 < Re ξ(1+it)` — a genuine positivity-on-an-interval
  statement. The witness is extracted from an open ball of positive radius around
  a point where the value is `1/2`, so it carries real content (a true sign over a
  set of positive length), not a `True`-equivalent.
* No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. `autoImplicit` off.
* Additive: nothing existing is edited.

## Why not import RightEdgeSignsProof_2026_10_09 for `R1_at_zero`

Measured 2026-10-09: `RightEdgeSignsProof_2026_10_09.olean` does not exist (that
file is itself additive and unbuilt), and building it is out of scope. So the
`t = 0` point value is re-proved here directly from the r325 definition, whose
olean does exist. The statement obtained, `R1_at_zero_local`, is literally the
same proposition as that file's `R1_at_zero`.

## Dependencies (olean measured 2026-10-09 to exist)
* `PF/Analytic/RiemannXiEntire_r325.lean` — `riemannXiEntire`,
  `differentiable_riemannXiEntire`.
* mathlib — `Complex.continuous_re`, `Complex.continuous_ofReal`,
  `Continuous.isOpen_preimage`, `Metric.isOpen_iff`.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen + Claude Opus 4.8.  2026-10-09.
-/

import PF.Analytic.RiemannXiEntire_r325

set_option autoImplicit false

namespace PrincipiaTractalis
namespace R1Neighborhood20261009

open Complex
open PrincipiaTractalis.RiemannXiEntire

noncomputable section

/-! ## §0 — the `t = 0` corner, re-proved from the r325 definition

`ξ(1) = (1·(1-1)·Λ₀(1) + 1)/2 = 1/2`: the polynomial factor `s(s-1)` is `0` at
`s = 1`, so the (unknown) value `Λ₀(1)` is annihilated and the real part is `1/2`.
This is literally the proposition `RightEdgeSignsProof_2026_10_09.R1_at_zero`. -/

/-- `Re ξ(1) = 1/2` exactly (the `t = 0` corner). -/
theorem re_xi_one : (riemannXiEntire (⟨1, 0⟩ : ℂ)).re = 1 / 2 := by
  have h1 : (⟨1, 0⟩ : ℂ) = 1 := by apply Complex.ext <;> simp
  have hval : riemannXiEntire (1 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    unfold riemannXiEntire
    push_cast
    ring
  rw [h1, hval, Complex.ofReal_re]

/-- R1 at the single point `t = 0`: `0 < Re ξ(1)`. -/
theorem R1_at_zero_local : 0 < (riemannXiEntire (⟨1, 0⟩ : ℂ)).re := by
  rw [re_xi_one]; norm_num

/-! ## §1 — the real edge function and its continuity -/

/-- The real-part right-edge function `t ↦ Re ξ(1+it)`. -/
def edgeRe (t : ℝ) : ℝ := (riemannXiEntire (⟨1, t⟩ : ℂ)).re

/-- The line `t ↦ 1 + it` is continuous `ℝ → ℂ`. -/
theorem continuous_edgeLine : Continuous (fun t : ℝ => (⟨1, t⟩ : ℂ)) := by
  have h : (fun t : ℝ => (⟨1, t⟩ : ℂ))
      = fun t : ℝ => Complex.I * (t : ℂ) + 1 := by
    funext t
    apply Complex.ext <;> simp
  rw [h]
  exact (continuous_const.mul Complex.continuous_ofReal).add continuous_const

/-- `t ↦ Re ξ(1+it)` is continuous `ℝ → ℝ`: `riemannXiEntire` is entire
(`differentiable_riemannXiEntire`, hence continuous), composed with the continuous
line `t ↦ ⟨1,t⟩` and `Complex.re`. -/
theorem continuous_edgeRe : Continuous edgeRe := by
  unfold edgeRe
  exact Complex.continuous_re.comp
    (differentiable_riemannXiEntire.continuous.comp continuous_edgeLine)

/-! ## §2 — the neighborhood upgrade -/

/-- **R1 on a neighborhood of `0`.** There is a positive-length interval `[0,δ]`
on which R1 holds: `0 < Re ξ(1+it)`. Proof: the open super-level set
`{t | 0 < edgeRe t}` contains `0` (value `1/2`, `R1_at_zero_local`);
`Metric.isOpen_iff` yields a ball of radius `ε > 0` inside it; take `δ = ε/2`, and
every `t ∈ [0,δ]` lies in that ball.

This does NOT close R1, which needs all of `[0,13]`: the segment `[δ,13]` remains
open. It is a genuine, unconditional upgrade of R1 from the single point `t = 0`
to an interval of positive length. -/
theorem R1_on_neighborhood :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (0 : ℝ) δ,
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  -- The super-level set `{t | 0 < edgeRe t}` is open.
  have hUopen : IsOpen (edgeRe ⁻¹' Set.Ioi (0 : ℝ)) :=
    continuous_edgeRe.isOpen_preimage _ isOpen_Ioi
  -- `0` lies in it, since `edgeRe 0 = Re ξ(1) = 1/2 > 0`.
  have hmem : (0 : ℝ) ∈ edgeRe ⁻¹' Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_preimage, Set.mem_Ioi]
    exact R1_at_zero_local
  -- Extract a ball of positive radius `ε` inside the open set.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen 0 hmem
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t ht
  rw [Set.mem_Icc] at ht
  obtain ⟨ht0, htδ⟩ := ht
  -- Every `t ∈ [0, ε/2]` is within distance `< ε` of `0`.
  have htball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |t - 0| = t := by rw [sub_zero, abs_of_nonneg ht0]
    rw [habs]; linarith
  have hpos := hball htball
  simp only [Set.mem_preimage, Set.mem_Ioi] at hpos
  exact hpos

end

/-! ## §Axiom check -/

#print axioms re_xi_one
#print axioms R1_at_zero_local
#print axioms continuous_edgeLine
#print axioms continuous_edgeRe
#print axioms R1_on_neighborhood

end R1Neighborhood20261009
end PrincipiaTractalis
