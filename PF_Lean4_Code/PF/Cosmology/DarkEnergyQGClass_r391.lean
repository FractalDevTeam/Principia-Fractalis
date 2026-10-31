/-
# r391: dark energy is assigned the QG class — the decision, and what it commits to

★ 2026-10-30 r391 — `α_DE := α_QG = √(2π)`, authorial decision, recorded ★

## The decision

r390 filled the dark-energy α-row, pre-registered all nine candidate classes,
and eliminated four by theorem (any class with `σ > 0` gives a phantom `w`, which
PF's own action derivation forbids). Five survived and r390 deliberately refused
to choose, on the ground that choosing by goodness of fit is fitting.

**The author has chosen the QG class.** This file records that decision and
derives what it commits the framework to.

## The rationale is not a fit — it is already in the book

The choice discriminates, which is what the corpus's own precedent demands: the
graph-isomorphism assignment was *superseded* because its rationale was
"literally true of every NP problem and therefore underdetermined"
(`ProblemClassTriClass_2026_06_22`). This one is true of the QG class and of no
other:

**ch26's master equation already evaluates the resonance kernel at `√(2π)`.** The
boxed cosmological-constant mechanism (ch26:167) is

    Λ_eff(C) = Λ₀ · exp[ −∫_Σ d³x  ch₂(C(x)) · R_f(√(2π), |x|) ]

and `√(2π)` is `α_QG`. It recurs at ch26:179, ch26:423, ch26:483. So the dark
sector in Principia Fractalis was *constructed* at the QG α-value years before
the α-row question was posed; the row makes explicit what the mechanism already
assumed. r229's header records the same reading from the Lean side.

## What the decision commits to

With `α_DE = α_QG = √(2π)` and r390's law `ρ_DE ∝ a^{σ(α_DE)}` read against the
standard parameterisation `ρ_DE ∝ a^{−3(1+w)}`:

* `σ(α_QG) = −0.0387175864…` — **numeric, not a closed form**: `α_QG` is
  irrational so σ has no closed form here (THE MAP §3). Its *sign* is
  kernel-proven (`sigma_alphaQG_lt_zero`, r230), and the sign is what the gate
  needs;
* **`w₀ = −0.9870941379…`** — near-ΛCDM;
* the row passes the non-phantom gate, so it is consistent with PF's action
  derivation, whose window is `w₀ ∈ [−0.99, −0.93]`. `−0.9871` is inside it. Of
  r390's five survivors this is the only one that is.

**And the commitment with teeth.** DE and QG now share one sector, hence one σ.
σ is simultaneously the primordial tilt `n_s − 1` (the QG row, THE MAP §3.1) and
`−3(1 + w₀)` (this row). So the framework now asserts a *hard link* between two
independently measured quantities:

    n_s − 1  =  −3 (1 + w₀)

That is `tilt_w0_link` below. It is the sharpest falsifiable statement the
α-skeleton has produced, because both sides are measured. With ch28's own
`n_s = 0.965 ± 0.004` it reads `w₀ = −0.9883 ± 0.0013`.

## The three things this makes worse, stated because they are the point

1. **It contradicts ch27's own boxed equation of state.** ch27:157ff gives
   `w_DE(z) = −1 + ε(z)(ch₂(z)/0.95)³` with `ε(0) = 0.15`, hence
   `w_DE(0) = −0.85` (its own 2026-10-03 correction remark). The QG row gives
   `−0.9871`. Both cannot be the framework's prediction for the same quantity.
   Recorded, neither withdrawn — the same treatment ch27 already gives its two
   incompatible `H₀` values at ch27:316.
2. **It is in sharp tension with the CPL-based data.** DESI DR2's preferred
   `w₀ ≈ −0.67` sits far from `−0.9871`. The row predicts near-ΛCDM; the data
   fits prefer strong evolution.
3. **It converts THE MAP's one hit into a mixed row.** The QG class previously
   had one observable, the tilt, agreeing at 0.86σ. It now has two, and one σ
   cannot equal both `−0.0351 ± 0.0042` and `−3(1 + w₀)` with `w₀ ≈ −0.67`
   (which would need `σ ≈ −0.99`). So the joint scoreboard goes from
   *one hit, one miss* to *one hit, one miss, and one newly-failing observable on
   the hit's own row* — unless the CPL-based `w₀` determinations are themselves
   wrong, which is a live possibility (the evolving-dark-sector critique holds
   that DESI's apparent evolution is an artifact of assuming constant
   dark-matter mass) but is not something this framework gets to assume.

## What is NOT claimed

Not claimed: a derivation. The classification is a **posit**; `α_QG = √(2π)` is
an ASSERTED postulate (r230's own scope note disclaims deriving it); and "σ is a
scaling exponent" is THE MAP's EMPIRICAL HYPOTHESIS — UNTESTED. Not claimed: that
the row is confirmed — it is currently disfavoured by the CPL fits and
inconsistent with ch27. Not claimed: that ch26's use of `√(2π)` *derives* the
classification; it makes it the non-arbitrary choice, which is a different and
weaker thing. Not claimed: any Millennium discharge, any statement about
physical spacetime, and nothing about `Λ₀`'s magnitude.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-30.
-/
import PF.Cosmology.DarkEnergyAlphaRow_r390
import PF.AlphaQGSigmaNegative_r230

set_option autoImplicit false

open scoped Real

namespace PrincipiaTractalis.Cosmology.DarkEnergyQGClass

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow
open PrincipiaTractalis.AlphaQGSigmaNegative

/-! ## §1 — The assignment -/

/-- **The decision.** Dark energy is assigned the QG class, so
`α_DE = α_QG = √(2π)`. A posit, with ch26:167's kernel argument as its
discriminating rationale. -/
noncomputable def alphaDE : ℝ := Real.sqrt (2 * π)

/-- The dark-energy scaling exponent is the QG sector's σ. -/
noncomputable def sigmaDE : ℝ := sigma alphaDE

/-- The predicted present equation of state. -/
noncomputable def wDE : ℝ := wOfSigma sigmaDE

/-! ## §2 — The row passes the gate

The gate is `σ ≤ 0`, from the action derivation's non-phantom theorem. r230
proves the strict sign, so the assignment is admissible — and strictly so, which
means it predicts genuine evolution rather than a bare `Λ`. -/

theorem sigmaDE_neg : sigmaDE < 0 := sigma_alphaQG_lt_zero

/-- **★★★ r391: the QG assignment is non-phantom ★★★**

Strictly above `−1`, so admissible under the action derivation's theorem and not
a pure cosmological constant. -/
theorem wDE_gt_neg_one : -1 < wDE := by
  have h := sigmaDE_neg
  unfold wDE wOfSigma
  linarith

theorem wDE_nonphantom : -1 ≤ wDE := le_of_lt wDE_gt_neg_one

/-! ## §3 — The commitment: the tilt–`w₀` link

DE and QG share one sector, hence one σ. σ is the primordial tilt `n_s − 1` by
the QG row and `−3(1 + w₀)` by this row, so the two measured quantities are
locked together. -/

/-- **★★★ r391: `n_s − 1 = −3(1 + w₀)` ★★★**

The framework's sharpest falsifiable statement, because both sides are
measured. -/
theorem tilt_w0_link : -3 * (1 + wDE) = sigmaDE := sigma_of_wOfSigma sigmaDE

/-- Read the other way: the tilt fixes `w₀`. -/
theorem w0_of_tilt (tilt : ℝ) (h : sigmaDE = tilt) : wDE = -1 - tilt / 3 := by
  unfold wDE wOfSigma; rw [h]

/-! ## §4 — The conflict with ch27's boxed value, as a conditional

ch27:157ff gives `w_DE(0) = −1 + ε(0) = −0.85`. The QG row's value is below it.
The comparison is stated as an exact conditional on σ; its antecedent holds for
`σ(α_QG) = −0.03872…`, verified numerically at 30 digits (mpmath) and **not**
in-kernel, since a closed form for `σ(α_QG)` does not exist and the tighter cos
bound needed is not among r230's. Labelled accordingly. -/

/-- ch27's own present-day value, from its boxed formula at `ε(0) = 0.15`. -/
noncomputable def wDE_ch27 : ℝ := -85/100

/-- If `σ > −0.45` then the row's `w₀` lies strictly below ch27's `−0.85`. Pure
arithmetic; the antecedent is the numeric input. -/
theorem below_ch27_of_sigma_gt {s : ℝ} (hs : -45/100 < s) :
    wOfSigma s < wDE_ch27 := by
  unfold wOfSigma wDE_ch27
  linarith

/-- ch27's value is itself non-phantom, so the two disagree *within* the
admissible region — this is a disagreement between two PF constructions, not a
violation of the gate. -/
theorem wDE_ch27_nonphantom : -1 < wDE_ch27 := by
  unfold wDE_ch27; norm_num

end PrincipiaTractalis.Cosmology.DarkEnergyQGClass

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.alphaDE
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.sigmaDE_neg
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.wDE_gt_neg_one
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.wDE_nonphantom
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.tilt_w0_link
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.w0_of_tilt
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.below_ch27_of_sigma_gt
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.wDE_ch27_nonphantom

-- Axiom-check coverage completed 2026-10-30 (declarations the in-file check had omitted)
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.sigmaDE
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.wDE
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyQGClass.wDE_ch27
