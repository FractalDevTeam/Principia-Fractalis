/-
# r323: LITERAL `Complex.riemannZeta` NONVANISHING AT t = 15 ON THE CRITICAL LINE
        + generic converse `Xi ≠ 0 → riemannZeta ≠ 0` bridge on the critical line

★ 2026-08-24 r323 — an explicit-point ζ nonvanishing theorem plus a reusable
Xi-nonvanishing → ζ-nonvanishing bridge. ★

## Purpose

r315 (`PF/Analytic/XiOnLineZeroT15.lean:338`) proves `0 < Xi 15` where
`Xi t := (completedRiemannZeta ⟨1/2, t⟩).re`
(`PF/Analytic/XiRealWitness.lean:247`).

The existing bridge `xi_zero_at_pos_implies_nonempty`
(`PF/Analytic/XiRealWitness.lean:298`) handles the FORWARD direction only:

    Xi t = 0 → riemannZeta ⟨1/2, t⟩ = 0

This file supplies the CONVERSE direction and, as an immediate corollary,
extracts from r315 the point-wise statement about mathlib's
`Complex.riemannZeta`:

    riemannZeta ⟨1/2, 15⟩ ≠ 0.

## Position in the corpus

PF already contains an unconditional literal `Complex.riemannZeta` theorem:
r120's `positiveOnLineZetaZeroOrdinatesNonempty`
(`PF/Analytic/XiOnLineZero.lean:392`) proves `∃ t > 0, riemannZeta ⟨1/2, t⟩ = 0`
via the Xi(1) < 0, Xi(77/5) > 0 sign change and IVT.  That theorem is the
existence side; r323 supplies a corresponding nonvanishing side at one
specific critical-line ordinate.

Corpus companions:

- r120's `positiveOnLineZetaZeroOrdinatesNonempty`: existence of ≥1
  positive on-line ζ zero.
- r280's `positive_on_line_zeta_zero_ordinates_countable`: the whole set
  of such ordinates is countable.
- r255's `MillenniumRHSubstratePositionCapstone`: conditional reduction
  of full RH to Hardy 1914 + HP-program.
- r315's `Xi_15_pos`: kernel-clean `0 < Xi 15` via r120 architecture at
  t = 15.

r323 is a small explicit-point NONVANISHING landing plus a reusable
generic bridge; not an existence result, not a Millennium landing.

## Scope — explicit

* IS: `riemannZeta ⟨1/2, 15⟩ ≠ 0` — a literal mathlib-`Complex.riemannZeta`
  statement, kernel-verified via the r315 quadrature + Gammaℝ nonvanishing
  bridge.
* IS: generic converse `Xi t ≠ 0 → riemannZeta ⟨1/2, t⟩ ≠ 0`, reusable
  for any future Xi-side nonvanishing certificate (t = 30, t = 100, ...).
* NOT a finite-height RH theorem (would require ruling out
  off-critical-line zeros and enumerating on-line zeros with multiplicity
  in `0 < Im s ≤ 15`; the argument principle / Riemann-von Mangoldt
  infrastructure is absent from mathlib at pin `v4.24.0-rc1`).
* NOT a discharge of the Riemann Hypothesis.
* NOT a proof of Hardy 1914; r120's `positiveOnLineZetaZeroOrdinatesNonempty`
  supplies existence of ≥1 on-line ζ zero.  r323 supplies point-wise
  ABSENCE of a zero at one specific critical-line ordinate.
* NOT dependent on the α-skeleton, I9, r128 StructuralLaws, H_3 identities,
  or T3 spectrum.

## Proof

`Xi t ≠ 0 ⟹ Xi t ≠ 0` is trivial; combined with `Xi_eq` this gives
`(completedRiemannZeta ⟨1/2, t⟩).re ≠ 0`, hence
`completedRiemannZeta ⟨1/2, t⟩ ≠ 0`.  On the critical line, `Re s = 1/2 > 0`,
so `Gammaℝ_ne_zero_of_re_pos` gives `Gammaℝ ⟨1/2, t⟩ ≠ 0`.  Then
`riemannZeta_def_of_ne_zero` (with `critical_point_ne_zero`) rewrites
`riemannZeta ⟨1/2, t⟩ = completedRiemannZeta ⟨1/2, t⟩ / Gammaℝ ⟨1/2, t⟩`,
and `div_ne_zero` closes.

Specialising at `t = 15` with `Xi_15_pos → ne_of_gt` gives r323's headline.

No new axioms.  Kernel-only.

Author: Pablo Cohen + Claude Opus 4.7.  2026-08-24.
-/

import PF.Analytic.XiRealWitness
import PF.Analytic.XiOnLineZeroT15

namespace PrincipiaTractalis.RiemannZetaAt15

open Complex
open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.XiOnLineZeroT15
open PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning

/-! ## §1 — generic converse `Xi ≠ 0 → riemannZeta ≠ 0` on the critical line -/

/-- **`riemannZeta_ne_zero_of_Xi_ne_zero`** — generic converse bridge on the
critical line.

If the real witness `Xi t = (completedRiemannZeta ⟨1/2, t⟩).re` is nonzero,
then `riemannZeta ⟨1/2, t⟩ ≠ 0`.

Proof: `Xi t ≠ 0` forces `(completedRiemannZeta ⟨1/2, t⟩).re ≠ 0`, hence
`completedRiemannZeta ⟨1/2, t⟩ ≠ 0`.  On the critical line
`Re ⟨1/2, t⟩ = 1/2 > 0`, so `Gammaℝ ⟨1/2, t⟩ ≠ 0` by mathlib's
`Gammaℝ_ne_zero_of_re_pos`.  The mathlib identity
`riemannZeta s = completedRiemannZeta s / Gammaℝ s` (for `s ≠ 0`, from
`riemannZeta_def_of_ne_zero`) plus `div_ne_zero` closes the argument.

This is the CONVERSE of the existing forward direction
`xi_zero_at_pos_implies_nonempty` (`PF/Analytic/XiRealWitness.lean:298`). -/
theorem riemannZeta_ne_zero_of_Xi_ne_zero {t : ℝ} (hXi : Xi t ≠ 0) :
    riemannZeta ⟨1/2, t⟩ ≠ 0 := by
  have hΛ_re : (completedRiemannZeta ⟨1/2, t⟩).re ≠ 0 := hXi
  have hΛ : completedRiemannZeta ⟨1/2, t⟩ ≠ 0 := by
    intro h
    apply hΛ_re
    rw [h, Complex.zero_re]
  have hs_ne : (⟨1/2, t⟩ : ℂ) ≠ 0 := critical_point_ne_zero t
  have hGamma : Gammaℝ (⟨1/2, t⟩ : ℂ) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    show (0 : ℝ) < ((⟨1/2, t⟩ : ℂ)).re
    norm_num
  rw [riemannZeta_def_of_ne_zero hs_ne]
  exact div_ne_zero hΛ hGamma

/-! ## §2 — r323 endpoint: LITERAL `riemannZeta ⟨1/2, 15⟩ ≠ 0` -/

/-- **★★★ r323 — LITERAL `Complex.riemannZeta` NONVANISHING AT t = 15. ★★★**

Extracted from r315's `Xi_15_pos : 0 < Xi 15` via the generic converse
bridge `riemannZeta_ne_zero_of_Xi_ne_zero`.

Companion to r120's existence result
`positiveOnLineZetaZeroOrdinatesNonempty` (`PF/Analytic/XiOnLineZero.lean:392`):
r120 gives ∃ positive on-line ζ zero; r323 gives ABSENCE of a zero at one
specific critical-line ordinate.

Scope: point-wise nonvanishing at ONE specific critical-line ordinate.
NOT a finite-height RH theorem.  NOT a Millennium discharge. -/
theorem riemannZeta_ne_zero_at_critical_15 :
    riemannZeta ⟨1/2, 15⟩ ≠ 0 :=
  riemannZeta_ne_zero_of_Xi_ne_zero (ne_of_gt Xi_15_pos)

end PrincipiaTractalis.RiemannZetaAt15

/-! ## §3 — Axiom check -/

#print axioms PrincipiaTractalis.RiemannZetaAt15.riemannZeta_ne_zero_of_Xi_ne_zero
#print axioms PrincipiaTractalis.RiemannZetaAt15.riemannZeta_ne_zero_at_critical_15
