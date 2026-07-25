/-
# PF.Numerics.IntervalSmoke

2026-07-24 — Route B numerics-engine SMOKE TEST (HARDY_SCOPING_2026-07-24 §7,
INTERVAL_SPIKE_2026-07-24 GO-WITH-PORT verdict).

## Goal

Wire-in check for the vendored girving/interval library
(`vendor/interval/`, Apache 2.0, base commit `2eb9470` ported to the
corpus pin lean4 v4.24.0-rc1 / mathlib `eed770a4` — see
`vendor/interval/VENDORING.md`). This library is the certified-numerics
engine for the RH-arc Route B plan: the kernel-checked quadrature
certificate for a sign change of the real critical-line witness
`Xi` (`PF.Analytic.XiRealWitness`), which discharges the Wave 58/59
atomic fact `PositiveOnLineZetaZeroOrdinatesNonempty`.

Two transcendental inequalities are re-certified here end-to-end,
exactly in the pattern the spike validated:

  * `pi_lt_3_15`   : `π < 3.15`
  * `exp_one_gt_2_7` : `2.7 < Real.exp 1`

## Corpus discipline — the `native_decide` ban

Certification is via the `@[approx]` instrumentation (`by approx`) +
the decidable-interval-order bridges `Interval.approx_lt` /
`Interval.approx_le` + KERNEL reduction `decide +kernel` ONLY.

The library's convenience `interval` tactic
(`Interval/Tactic/Interval.lean`) is BANNED in the corpus: it is
documented to use `native_decide` (trust-the-compiler /
`Lean.ofReduceBool`), which breaks the corpus axiom budget. It is NOT
imported here; do not import it from any consumed corpus file.

ZERO project axioms, ZERO sorries; both #print axioms outputs exactly
`[propext, Classical.choice, Quot.sound]`.
-/

import Interval.Interval.Conversion
import Interval.Interval.Exp
import Interval.Interval.Pi
import Interval.Interval.Order
import Interval.Tactic.Approx

namespace PrincipiaTractalis.IntervalSmoke

open scoped Real

/-! ## §1 — Constant comparison: `π < 3.15` -/

/-- Kernel-certified `π < 3.15` via the vendored interval engine:
tight interval enclosure `Interval.pi`, decidable interval `<`
discharged by `decide +kernel` (NO `native_decide`). -/
theorem pi_lt_3_15 : (π : ℝ) < 3.15 := by
  refine Interval.approx_lt Interval.pi ((3.15 : Interval)) π 3.15
    Interval.approx_pi (by approx) ?_
  decide +kernel

/-! ## §2 — One transcendental evaluation: `2.7 < Real.exp 1` -/

/-- Kernel-certified `2.7 < Real.exp 1` via one interval `exp`
evaluation (`exp_series_16`), again discharged by `decide +kernel`
(NO `native_decide`). -/
theorem exp_one_gt_2_7 : (2.7 : ℝ) < Real.exp 1 := by
  refine Interval.approx_lt ((2.7 : Interval)) ((1 : Interval).exp) 2.7 (Real.exp 1)
    (by approx) (Interval.mem_approx_exp (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.IntervalSmoke
