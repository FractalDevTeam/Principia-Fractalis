/-
# The Yang–Mills placeholders, and why this axis cannot be repointed

**Date**: 2026-11-27 (Legion). Companion to the NS repoint of the same day.

The NS axis had four framework Props of the same family. Three are now in good
order:

* `fractalEmergenceNoBlowup` — repointed today to the faithful a-priori
  vorticity bound, with its `Unit` carrier retained and its collapse proved.
* `fractalBSDRankEquality` — already genuine: it quantifies over mathlib's own
  `WeierstrassCurve ℚ`.
* `fractalHodgeCrystallization` — quantifies over a typed ambient, but its
  consequent `HodgeAlgebraicRepresentation` ignores both of its arguments, so
  the emptiness there is in the consequent rather than the carrier. Recorded in
  ch25's verification-status block; not touched here.

The fourth is Yang–Mills, and it is two Props, both free. §1 proves that.

## Why there is no repoint for this axis

NS could be repointed because Fefferman's statement is writable at this pin:
it is a PDE condition on mathlib `SchwartzMap`s, with `fderiv`, `gradient` and
`laplacian` all present. Yang–Mills is not in that position, and the reason is
measured rather than assumed:

* `Mathlib` contains **zero** files mentioning Wightman.
* `Mathlib` contains **zero** files mentioning Osterwalder.
* There is no `Mathlib/QFT` directory.

So the Clay Yang–Mills statement cannot be written faithfully here, and the
corpus is right to keep it parameterised over an external encoding —
`Clay_YangMillsMassGap_Standard (E : StandardYMEncoding)`, which quantifies
over `E.satisfiesClayAxioms` precisely because those axioms are not available
to state. That is a correct design under the constraint, not a defect, and §3
records it so the asymmetry with NS is legible to a referee.

## What this axis does have

Real, and worth citing in place of the placeholders:

* **`PF.YangMills.wilson_reflection_positivity_of_L2_strong`**
  (`PF/YangMills/WilsonRPL2ExtensionCapstone_2026_11_12.lean:44`) — the
  unconditional L² reflection-positivity theorem: for a family of
  strongly-measurable, L²-integrable functions supported on the plus-zero
  half, the θ-crossed Gram matrix over the Wilson Gibbs measure is
  `PosSemidef`. Genuine measure theory on mathlib's `MemLp`,
  `StronglyMeasurable` and `Matrix.PosSemidef`, under the single hypothesis
  `Even L`.
* **`ym_continuum_mass_gap_three_halves`** — inhabits
  `ContinuumMassGapInfDimTypedStatement` with `Δ = 3/2` on an
  infinite-dimensional complete inner-product space. §2 re-exports it, and
  §2 also states plainly what it is not.
* `fractalYMLevel1SpectrumGap` — three genuine arithmetic identities about
  `fractalKernelReal`, and it holds unconditionally.

Nothing upstream is renamed, reworded or deleted.
-/
import PF.MillenniumSixReductions
import PF.YM_ContinuumMassGapInfDimWitness

set_option autoImplicit false

namespace PF.Referee.YangMillsPlaceholderGravestones

open PrincipiaTractalis
open PrincipiaTractalis.MillenniumSix
open PrincipiaTractalis.YM_ContinuumMassGapInfDimWitness

/-! ## §1 — Both Yang–Mills placeholders are free -/

/-- **★ `YangMillsExistenceAndMassGap` is equivalent to `True`.**

    Its body is `∃ Δ_YM : ℝ, 0 < Δ_YM ∧ True`, which `Δ_YM := 1` satisfies.
    Its own docstring calls it "the structural placeholder", and this makes
    that a theorem of the corpus: no discharge of it was ever evidence about a
    quantum Yang–Mills theory or about a mass gap. -/
theorem yangMillsExistenceAndMassGap_collapses :
    YangMillsExistenceAndMassGap ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨1, by norm_num, trivial⟩

/-- **★ `fractalYMLevel1LiftsToContinuum` is equivalent to `True`.**

    Its consequent is `∃ Δ_YM : ℝ, 0 < Δ_YM`, satisfied by `1`, so the
    implication holds whatever its antecedent says. It is empty twice over,
    since `fractalYMLevel1SpectrumGap` is itself proved unconditionally in the
    corpus — so neither half of the implication carries anything. -/
theorem fractalYMLevel1LiftsToContinuum_collapses :
    fractalYMLevel1LiftsToContinuum ↔ True := by
  constructor
  · intro _
    trivial
  · intro _ _
    exact ⟨1, by norm_num⟩

/-- **And so it transports nothing.**

    Assuming `YangMillsExistenceAndMassGap` and concluding any `Q` is the same
    as concluding `Q`. The same instrument used on the NS bridge and on
    `fractalEmergenceNoBlowup`; here it applies to the YM conclusion itself. -/
theorem yangMills_placeholder_transports_nothing (Q : Prop) :
    (YangMillsExistenceAndMassGap → Q) ↔ Q := by
  constructor
  · intro h
    exact h (yangMillsExistenceAndMassGap_collapses.mpr trivial)
  · intro h _
    exact h

/-! ## §2 — The real spectral result, and what it is not -/

/-- **Re-export of the genuine inf-dimensional mass-gap witness.**

    `ContinuumMassGapInfDimTypedStatement` is not vacuous: it asks for a
    complete inner-product space, an operator, a real `Δ` with `0 < Δ`,
    `1 ≤ Δ` and `Δ ≠ 1`, and a nonzero eigenvector with `Hamil v = Δ • v`.
    The corpus inhabits it at `Δ = 3/2` on an infinite-dimensional carrier. -/
theorem continuum_mass_gap_inf_dim_witness :
    ContinuumMassGapInfDimTypedStatement :=
  ym_continuum_mass_gap_three_halves

/-- **What that result is not.**

    It exhibits *an* operator on *a* complete inner-product space with an
    eigenvalue `3/2`. It says nothing about `SU(N)` gauge fields, about the
    Wightman or Osterwalder–Schrader axioms, or about the Clay mass gap — none
    of which can be stated at this pin. So it must not be cited as a Clay
    result, and the placeholder of §1 must not be cited as anything at all.

    Stated as the disjunction rather than a denial, because this file settles
    nothing about Yang–Mills itself. -/
theorem no_verdict_on_clay_yang_mills :
    YangMillsExistenceAndMassGap ∨ ¬ YangMillsExistenceAndMassGap :=
  em YangMillsExistenceAndMassGap

/-! ## §3 — The asymmetry with Navier–Stokes, recorded -/

/-- **Why NS was repointed and YM was not**, as a citable statement rather
    than a remark.

    Both halves are proved here: the YM framework Prop is free, while the NS
    one now carries the open a-priori vorticity bound. The difference is not a
    choice about rigour — it is that Fefferman's statement is expressible over
    mathlib's `SchwartzMap` whereas the Clay Yang–Mills axioms are not
    expressible at all, mathlib having no Wightman or Osterwalder–Schrader
    development. -/
theorem ym_free_while_ns_carries_the_open_estimate :
    (YangMillsExistenceAndMassGap ↔ True)
      ∧ (fractalEmergenceNoBlowup (3 * Real.pi / 2)
          ↔ PF.NavierStokes.FeffermanFaithful.VorticityAPrioriBound) := by
  refine ⟨yangMillsExistenceAndMassGap_collapses, ?_⟩
  constructor
  · intro h
    exact h rfl
  · intro h _
    exact h

end PF.Referee.YangMillsPlaceholderGravestones
