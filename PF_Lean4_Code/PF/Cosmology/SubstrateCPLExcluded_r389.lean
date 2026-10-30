/-
# r389: the action derivation EXCLUDES the golden-ratio CPL pair

★ 2026-10-30 r389 — the derivation exists, and it refutes the ansatz ★

## The question this answers

"Derive the ratios from the substrate." The answer is that **the derivation has
already been done, and it does not produce the ratios — it excludes them.**

`codex/COSMOLOGY_DE_DERIVATION_2026-10-11.md` derives PF's dark-energy sector
from the ch08 action. Its chain, in brief:

* varying the gauge connection `A` in the action-as-written gives `dφ ∧ F = 0`,
  which forces the magnetic field — hence the Pontryagin source — to vanish for
  any rolling `φ`. So the `Q = 0` branch is **derived, not assumed** (its rev 4);
* on that branch the action reduces to **exponential quintessence with a single
  free parameter `M`**, `V = (Λ₀/κ)e^{−φ/M}`;
* the system is then **fully closed** — the route map's free function `g(t)`
  collapses to a one-parameter family in `M`;
* and `w` is exact: `w = −1 + g/(3H)` (r219) equals the canonical
  `w_φ = (½φ̇² − V)/(½φ̇² + V) ≥ −1` whenever `φ̇² ≥ 0` and `V > 0`, with equality
  iff `φ̇ = 0`.

That last line is the load-bearing one. It is a **theorem**, register A, and it
matches r219's `wEff_ge_neg_one` and ch27:168 ("never phantom"). **PF's derived
dark energy can never cross `w = −1`.** The derived window is
`w₀ ∈ [−0.99, −0.93]` for `M ∈ [0.287, 1] M_Pl`.

The r78 pair is `(w₀, wₐ) = (−φ/2, −1/φ) = (−0.8090, −0.6180)`, which r387 proved
is phantom in the past and r388 showed crosses `w = −1` at `z = 1/√5`. A phantom
crossing is exactly what the derivation forbids. So the two are not merely
different — they are **inconsistent**, and the inconsistency is settled by a
theorem rather than by data.

This file records the arithmetic half: `−φ/2` lies **outside** the derived
window, above its upper end.

## The three-way state of the lane, for the record

All three pairwise comparisons fail. Via `w = −1 + g/(3H)`:

| | `w₀` | `g₀/H₀` | phantom? |
|---|---|---|---|
| r78 ansatz | `−0.8090` | `0.5729` | yes, crosses at `z = 1/√5` |
| action derivation (register A) | `[−0.99, −0.93]` | `[0.030, 0.210]` | **never** (theorem) |
| measured `g` inversion | `[−0.753, −0.650]` | `[0.74, 1.05]` | zero at `z ≈ 0.40` |

* ansatz vs derivation — `w₀` outside the window, and phantom vs a non-phantom
  theorem;
* ansatz vs measurement — `w₀ = −0.8090` is below the measured interval's floor;
* derivation vs measurement — `g₀/H₀` differs by a factor ≈ 3.5.

The third row's "zero at `z ≈ 0.40`" is compatible with the derivation **if it
is a touch rather than a sign change**: a thawing field sits frozen (`φ̇ = 0`,
`g = 0`, `w = −1`) and then thaws, so `g` reaches zero in the past without
changing sign. The route map reads that zero as a *crossing*; the derivation
says it is a *touch*. Those are different claims about the same measured number
and the corpus has not distinguished them.

## What would actually derive the ratios

Nothing available does, and the obstruction is at four independent places, each
already documented:

1. **The α-values are postulates.** THE MAP §3 marks `α_X` **ASSERTED** —
   `α_Hodge = φ` is not derived from the substrate.
2. **There is no dark-energy sector** among the nine α-skeleton rows (Poincaré,
   RH, YM, P, NP, Hodge, BSD, NS, QG). No `α_DE` exists to evaluate.
3. **The dictionary is a posit.** "σ(α_X) is the physical scaling exponent of X"
   is labelled EMPIRICAL HYPOTHESIS — UNTESTED, and names no observable for any
   cosmological quantity.
4. **The functional form is wrong.** The substrate's φ-content is `log₃ φ`, a
   scaling *exponent*; the CPL pair uses **bare** `φ` in `−φ/2` and `−1/φ`. THE
   MAP carries a dated correction for precisely this confusion: an earlier draft
   called σ(1/4), σ(1/5) "the silver / golden ratio" and that **"was wrong — σ is
   log₃ *of* those ratios; the ratio sits inside the log."**

And the near-misses are close enough to be dangerous, so they are recorded here
to be refused rather than rediscovered:

    σ(3/4) = −log₃(1+√2) = −0.80226081…    vs  −φ/2  = −0.80901699…   (0.84% apart)
    σ(1/3) = log 2/log 3  = +0.63092975…    vs  1/φ   = +0.61803399…   (2.09% apart)

Neither is an equality. `σ(3/4) = −φ/2` would require `3^φ = 3 + 2√2`, i.e.
`5.91559… = 5.82843…`, which is false.

## What is NOT claimed

Not claimed: that r78 should be withdrawn, renamed, or relabelled — no
downgrade, and the decision about a postulate's status is the author's. Not
claimed: that the action derivation is right about the world; it is conditional
on the `Q = 0` branch, on the ch08 action as a postulate (register B), and the
`Q ≠ 0` chromo-natural branch is a genuinely different cosmology the corpus
cannot compute. Not claimed: that the measurement settles anything — the three
rows disagree and that is the finding.

No dataset number appears in any statement below. The window endpoints
`−99/100`, `−93/100` are PF's **own derived** values, not measurements.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-30.
-/
import PF.Cosmology.SubstrateCPLCrossing_r388

set_option autoImplicit false

namespace PrincipiaTractalis.Cosmology.SubstrateCPLExcluded

open PrincipiaTractalis.Priority4SubstrateDischarge
open PrincipiaTractalis.Cosmology.SubstrateCPLPhantomCheck
open PrincipiaTractalis.Cosmology.SubstrateCPLCrossing

/-! ## §1 — The ansatz lies outside the derived `w₀` window -/

/-- **★★★ r389: `−φ/2` is above the derived window's upper end ★★★**

The action derivation gives `w₀ ∈ [−0.99, −0.93]`. The r78 ansatz has
`w₀ = −φ/2 ≈ −0.8090`, which exceeds `−0.93`, so it is outside. Needs
`φ < 1.86`; note `φ < 2` is **not** enough, so the bound is derived from
`φ² = φ + 1` rather than taken from mathlib. -/
theorem substrate_w_0_above_derived_window :
    (-93 : ℝ)/100 < substrate_w_0 := by
  -- `φ < 2` is too weak here; the bound needed is `φ < 93/50 = 1.86`.
  have hub : Real.goldenRatio < 93/50 := by
    have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
    have hpos : (0:ℝ) < Real.goldenRatio := Real.goldenRatio_pos
    nlinarith [hsq, hpos]
  unfold substrate_w_0
  linarith

/-- The ansatz is therefore not in the derived window. -/
theorem substrate_w_0_not_mem_derived_window :
    substrate_w_0 ∉ Set.Icc ((-99 : ℝ)/100) ((-93 : ℝ)/100) := by
  intro hmem
  exact absurd hmem.2 (not_le.mpr substrate_w_0_above_derived_window)

/-! ## §2 — The implied `g₀/H₀`, in closed form

r219's bridge at `a = 1` gives `g₀/H₀ = 3(1 + w₀)`. For the ansatz that is
`3(2 − φ)/2`, which is below `3/5` — stated as a rational bound so no dataset
number enters. -/

theorem substrate_g0_over_H0_closed_form :
    3 * (1 + substrate_w_0) = 3 * (2 - Real.goldenRatio) / 2 := by
  unfold substrate_w_0
  ring

theorem substrate_g0_over_H0_lt_three_fifths :
    3 * (1 + substrate_w_0) < 3/5 := by
  have h : (8:ℝ)/5 < Real.goldenRatio := by
    have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
    have hpos : (0:ℝ) < Real.goldenRatio := Real.goldenRatio_pos
    nlinarith [hsq, hpos]
  unfold substrate_w_0
  linarith

/-! ## §3 — The exclusion, bundled

Phantom (r387) and outside the derived window (§1). The derivation's
`w_φ ≥ −1` is a register-A theorem, so a phantom ansatz cannot be its `w`. -/

theorem substrate_cpl_excluded_by_derivation :
    substrate_w_0 + substrate_w_a < -1
      ∧ substrate_w_0 ∉ Set.Icc ((-99 : ℝ)/100) ((-93 : ℝ)/100) :=
  ⟨substrate_early_phantom, substrate_w_0_not_mem_derived_window⟩

end PrincipiaTractalis.Cosmology.SubstrateCPLExcluded

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLExcluded.substrate_w_0_above_derived_window
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLExcluded.substrate_w_0_not_mem_derived_window
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLExcluded.substrate_g0_over_H0_closed_form
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLExcluded.substrate_g0_over_H0_lt_three_fifths
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLExcluded.substrate_cpl_excluded_by_derivation
