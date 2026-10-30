/-
# r387: the substrate CPL ansatz is phantom — and fails r219's own hypothesis

★ 2026-10-29 r387 — two parts of the corpus, checked against each other ★

## Why this file exists

Two results sit in the corpus and had never been evaluated against one another.

**r78** (`PF/Priority4SubstrateDischarge.lean`) supplies the substrate
dark-energy CPL prediction
`(w₀, wₐ) = (-φ/2, -1/φ)`, and `PF.lean`'s own import note describes it as
"sitting inside DESI DR2 90% CI".

**r219** (`PF/EquationOfStateBridge_r219.lean`) proves
`cpl_nonphantom_forces_wa_bound`: if `w(a) = w₀ + wₐ(1-a) ≥ -1` on all of
`(0,1]`, then `wₐ ≥ -1 - w₀`. The same file's `wEff_ge_neg_one_iff` shows that
`-1 ≤ w` is *equivalent* to `0 ≤ g`, so this bound is exactly r187's
monotonicity hypothesis `hg0` expressed in CPL coordinates.

Substituting r78's numbers into r219's bound:

    wₐ      = -1/φ      ≈ -0.6180
    -1 - w₀ = -1 + φ/2  ≈ -0.1910

and `-0.6180 ≥ -0.1910` is **false**, by a margin of `(φ-1)/2 - 1 + 1 ≈ 0.427`.
So the substrate ansatz is phantom in the past — `w₀ + wₐ ≈ -1.427 < -1` — and
therefore **cannot satisfy the hypothesis of r219's own theorem**. That is what
is proved below, three ways: the bound fails, the early-time value is phantom,
and the non-phantom antecedent is refutable outright.

## This is a fork, not a defect in either file

Both results stand. Neither is weakened here, and nothing is renamed or
withdrawn. What is established is that they are **jointly inconsistent with
`g ≥ 0`**, and exactly one of three things must give:

1. **Keep `g ≥ 0`** (r187's hypothesis, and the non-phantom branch). Then the
   golden-ratio CPL ansatz `(-φ/2, -1/φ)` is excluded by r219 — by a theorem of
   the framework's own, not by data.
2. **Keep the ansatz.** Then `g` must change sign somewhere, r187's monotonicity
   hypothesis fails, and r219's `exists_wEff_crossing_of_sign_change` locates the
   crossing where `g` vanishes. The ODE permits this; the monotonicity theorem
   forbids it.
3. **Keep both and drop the identification** of r78's CPL pair with the `w(a)`
   that r219's bridge governs — i.e. treat the golden-ratio pair as a fit
   parameterisation rather than as this model's equation of state.

Which branch to take is a modelling decision about the framework, not a
derivation, and it is not made here. Note that `g = φ̇/M` is *measured* in this
corpus rather than derived, and `g ≥ 0` is an **assumption** — so branch 1 is
not privileged by anything proved.

## What is NOT claimed

Not claimed: that r78 is wrong, that r219 is wrong, or that either should be
withdrawn — see the no-downgrade discipline. Not claimed: anything about
physical spacetime. r219's own scope note applies verbatim here — these are
theorems about the framework's postulated `Λ`-suppression law, and assert nothing
about the real universe.

Not claimed: any statement about DESI. **No dataset number appears in any
statement below**, matching r219's own discipline; the DESI remark in r78's
import note is prose and is not evaluated here, because assessing it needs the
joint `(w₀, wₐ)` covariance, which this corpus does not contain. What *is* shown
is that the ansatz lies on the phantom side of the `w₀ + wₐ = -1` line, which is
a fact about the ansatz alone.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.Priority4SubstrateDischarge
import PF.EquationOfStateBridge_r219

set_option autoImplicit false

namespace PrincipiaTractalis.Cosmology.SubstrateCPLPhantomCheck

open PrincipiaTractalis.Priority4SubstrateDischarge
open PrincipiaTractalis.EquationOfStateBridge

/-! ## §1 — `1/φ = φ - 1`, and a usable lower bound on `φ` -/

lemma one_div_goldenRatio : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
  have hconj : Real.goldenConj = 1 - Real.goldenRatio := by
    have h := Real.goldenRatio_add_goldenConj
    linarith
  rw [one_div, Real.inv_goldenRatio, hconj]
  ring

lemma four_thirds_lt_goldenRatio : (4:ℝ)/3 < Real.goldenRatio := by
  have hpos : (0:ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  nlinarith [hsq, hpos]

/-! ## §2 — The ansatz violates r219's bound -/

/-- **★★★ r387: the substrate CPL pair violates the non-phantom bound ★★★**

`wₐ < -1 - w₀` for the r78 values, so the conclusion of
`cpl_nonphantom_forces_wa_bound` fails on them. -/
theorem substrate_violates_nonphantom_bound :
    substrate_w_a < -1 - substrate_w_0 := by
  unfold substrate_w_a substrate_w_0
  rw [one_div_goldenRatio]
  have := four_thirds_lt_goldenRatio
  linarith

/-- **★ r387: the ansatz is phantom in the early universe ★**

`w₀ + wₐ < -1`, which is the `a → 0` limit of the CPL form. -/
theorem substrate_early_phantom :
    substrate_w_0 + substrate_w_a < -1 := by
  have := substrate_violates_nonphantom_bound
  linarith

/-- **★★★ r387: the substrate ansatz refutes r219's antecedent ★★★**

The non-phantom condition that `cpl_nonphantom_forces_wa_bound` assumes, and
that `wEff_ge_neg_one_iff` identifies with `0 ≤ g`, is **false** for the r78
pair. Proved by contraposition against r219 itself, so the inconsistency is
exhibited through the corpus's own theorem rather than recomputed. -/
theorem substrate_not_nonphantom :
    ¬ (∀ a : ℝ, 0 < a → a ≤ 1 →
        -1 ≤ substrate_w_0 + substrate_w_a * (1 - a)) := by
  intro h
  exact absurd (cpl_nonphantom_forces_wa_bound h)
    (not_le.mpr substrate_violates_nonphantom_bound)

end PrincipiaTractalis.Cosmology.SubstrateCPLPhantomCheck

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLPhantomCheck.one_div_goldenRatio
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLPhantomCheck.four_thirds_lt_goldenRatio
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLPhantomCheck.substrate_violates_nonphantom_bound
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLPhantomCheck.substrate_early_phantom
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLPhantomCheck.substrate_not_nonphantom
