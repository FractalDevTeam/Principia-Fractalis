/-
# `BernoulliExpHasSumAtNegLogNhdsHalf` — Routine `-log z` Composition Discharge

This file SHARPENS the analytic Bernoulli identity
`BernoulliExpHasSumAtNegLogNhdsHalf` (defined in
`JonquieresExpansionEqualsGeomTendstoPartialAtHalfDischarge.lean`) by
factoring out the routine `-log z` composition step.

## What is open vs. closed in this discharge

The full identity `BernoulliExpHasSumAtNegLogNhdsHalf` packages TWO
distinct pieces of mathematics:

1. (TRULY OPEN, hard) — the **analytic** Bernoulli generating-function
   identity:
   ```
   ∀ v with |v| < 2π,  HasSum (fun k ↦ B_k · v^k / k!) (v / (exp v - 1))
   ```
   where the RHS is taken to be `1` at `v = 0` by the removable
   singularity. Mathlib has the formal-power-series shadow
   (`bernoulliPowerSeries_mul_exp_sub_one`) but no analytic lift.

2. (ROUTINE, axiom-free here) — the **composition with `v = -log z`**
   near `z = 1/2`. Since `-log` is continuous at `1/2` and
   `-log(1/2) = log 2` lies inside the disc `|v| < 2π` (in fact
   `log 2 < 1 < 2π`), the preimage of any neighbourhood of `log 2` in
   the disc is a neighbourhood of `1/2`, and the analytic identity
   transports through.

We isolate piece (1) as the new **sharpest open Prop**
`BernoulliExpHasSumOnBallTwoPi`, and discharge piece (2)
unconditionally as
`bernoulliExpHasSumAtNegLogNhdsHalf_of_bernoulliExpHasSumOnBallTwoPi`.

After this file the load-bearing open analytic content is exactly
the **classical analytic Bernoulli identity on the disc of
convergence** — a textbook complex-analysis fact (see e.g.
Apostol *Introduction to Analytic Number Theory*, Ch. 12, or
Whittaker & Watson §7.2) — with no `-log` composition baggage.

## Strategic position

* Before this file: `BernoulliExpHasSumAtNegLogNhdsHalf` is the
  single open analytic Prop on the closure path.
* After this file: `BernoulliExpHasSumOnBallTwoPi` is the new single
  open analytic Prop. It is STRICTLY simpler: a single-variable
  identity on a disc, with no log composition, no `nhds` wrapping
  on the input side.

Stage L25 — `-log` composition discharge of the partial-sum Bernoulli
residual at `nhds (1/2)`.
-/

import PF.Analytic.JonquieresExpansionEqualsGeomTendstoPartialAtHalfDischarge

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology

/-! ## The sharpest open analytic Prop: Bernoulli identity on the disc of convergence -/

/-- **Analytic Bernoulli generating-function identity on the open disc
    `|v| < 2π`** — the classical (and well-known) statement that the
    Taylor series with coefficients `B_k / k!` converges and sums to
    `v / (exp v - 1)` on its disc of convergence.

    At `v = 0` both sides are taken to be `1` (the removable
    singularity); we encode that here by `HasSum.zero`-style
    handling on the RHS via `if v = 0 then 1 else v / (exp v - 1)`,
    so the statement is uniform across all `v ∈ ball 0 (2π)`.

    **Open**: mathlib has the formal-power-series identity
    `bernoulliPowerSeries_mul_exp_sub_one` but no analytic
    `HasSum` lift to the disc of convergence. Discharging this Prop
    is the textbook classical-analysis step of recognising the
    formal series as the Taylor expansion of `v/(exp v - 1)` on the
    disc bounded by the first singularity (`v = ±2πi`). -/
def BernoulliExpHasSumOnBallTwoPi : Prop :=
  ∀ v : ℂ, ‖v‖ < 2 * Real.pi →
    HasSum (fun k : ℕ => (bernoulli k : ℂ) * v ^ k / (k.factorial : ℂ))
      (if v = 0 then 1 else v / (Complex.exp v - 1))

/-! ## Discharge: `-log z` for `z` near `1/2` lands inside the disc -/

/-- `-log` is continuous at `1/2 : ℂ`. -/
lemma continuousAt_neg_log_at_half :
    ContinuousAt (fun z : ℂ => -(Complex.log z)) (1/2 : ℂ) := by
  have h_half_mem : (1/2 : ℂ) ∈ Complex.slitPlane := by
    -- `1/2 : ℂ` has positive real part `1/2 > 0`, hence lies in the slit plane.
    refine Complex.mem_slitPlane_iff.mpr ?_
    left
    show (0 : ℝ) < (1/2 : ℂ).re
    simp
  exact (continuousAt_clog h_half_mem).neg

/-- The complex logarithm of `1/2` is the real number `log 2` cast into ℂ. -/
lemma neg_log_half_eq_log_two :
    -(Complex.log (1/2 : ℂ)) = ((Real.log 2 : ℝ) : ℂ) := by
  have h1 : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
  rw [Real.log_inv]
  push_cast
  ring

/-- The norm of `-log (1/2 : ℂ)` equals `log 2 < 2π` — well inside the
    disc of convergence. -/
lemma norm_neg_log_half_lt_two_pi :
    ‖-(Complex.log (1/2 : ℂ))‖ < 2 * Real.pi := by
  rw [neg_log_half_eq_log_two]
  rw [Complex.norm_real]
  rw [Real.norm_eq_abs]
  have h_log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_of_pos h_log_two_pos]
  -- `log 2 < 1 < 2π`.
  have h_log_two_lt_one : Real.log 2 < 1 := by
    have h_two_lt_e : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) h_two_lt_e
    rwa [Real.log_exp] at this
  have h_pi_gt : (1 : ℝ) < 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  linarith

/-- The `-log` preimage of the open disc `|v| < 2π` is a neighbourhood
    of `1/2`. -/
lemma eventually_norm_neg_log_lt_two_pi :
    ∀ᶠ z in nhds (1/2 : ℂ), ‖-(Complex.log z)‖ < 2 * Real.pi := by
  -- Pull back the open condition through continuity of `-log` at `1/2`.
  have h_cont := continuousAt_neg_log_at_half
  have h_open : IsOpen { v : ℂ | ‖v‖ < 2 * Real.pi } := by
    have : { v : ℂ | ‖v‖ < 2 * Real.pi } = Metric.ball (0 : ℂ) (2 * Real.pi) := by
      ext v
      simp [Metric.mem_ball, dist_zero_right]
    rw [this]
    exact Metric.isOpen_ball
  have h_mem : (-(Complex.log (1/2 : ℂ))) ∈ { v : ℂ | ‖v‖ < 2 * Real.pi } :=
    norm_neg_log_half_lt_two_pi
  have h_target_nhds : { v : ℂ | ‖v‖ < 2 * Real.pi } ∈ nhds (-(Complex.log (1/2 : ℂ))) :=
    h_open.mem_nhds h_mem
  exact h_cont.tendsto.eventually h_target_nhds

/-- For `z` near `1/2`, `z ≠ 1`. -/
private lemma eventually_z_ne_one :
    ∀ᶠ z in nhds (1/2 : ℂ), z ≠ 1 := by
  refine (isOpen_ne).eventually_mem ?_
  norm_num

/-- For `z` near `1/2`, `z ≠ 0`. -/
private lemma eventually_z_ne_zero :
    ∀ᶠ z in nhds (1/2 : ℂ), z ≠ 0 := by
  refine (isOpen_ne).eventually_mem ?_
  norm_num

/-- For `z` near `1/2` (specifically, in the slit plane near `1/2`), the value
    `Complex.exp (-(Complex.log z))` equals `z⁻¹`. -/
private lemma exp_neg_log_eq_inv {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (-(Complex.log z)) = z⁻¹ := by
  rw [Complex.exp_neg, Complex.exp_log hz]

/-- **DISCHARGE**: the disc-of-convergence Bernoulli identity
    `BernoulliExpHasSumOnBallTwoPi` implies the `-log`-composed
    eventual-in-`nhds (1/2)` form `BernoulliExpHasSumAtNegLogNhdsHalf`.

    The proof is pure analytic-function composition:
    `z ↦ -log z` is continuous at `1/2`, its value `-log(1/2) = log 2`
    has norm `< 2π`, so the preimage of the disc `|v| < 2π` under
    `-log` is a nhd of `1/2`. On that preimage,
    `BernoulliExpHasSumOnBallTwoPi v` with `v = -log z` gives the
    desired `HasSum`. The RHS value `v / (exp v - 1)` simplifies to
    `log z · z / (z - 1)` via `exp(-log z) = z⁻¹` (since `z ≠ 0`). -/
theorem bernoulliExpHasSumAtNegLogNhdsHalf_of_bernoulliExpHasSumOnBallTwoPi
    (h : BernoulliExpHasSumOnBallTwoPi) :
    BernoulliExpHasSumAtNegLogNhdsHalf := by
  unfold BernoulliExpHasSumAtNegLogNhdsHalf
  filter_upwards [eventually_norm_neg_log_lt_two_pi,
                  eventually_z_ne_one, eventually_z_ne_zero]
    with z h_norm hz1 hz0
  -- Set v = -log z.
  set v : ℂ := -(Complex.log z) with hv_def
  -- The hypothesis gives HasSum to (if v = 0 then 1 else v/(exp v - 1)).
  have h_v_HasSum := h v h_norm
  -- We need to show v ≠ 0 to drop the `if`.
  have h_log_ne : Complex.log z ≠ 0 := by
    intro hlog
    have : z = 1 := by
      have := Complex.exp_log hz0
      rw [hlog, Complex.exp_zero] at this
      exact this.symm
    exact hz1 this
  have hv_ne_zero : v ≠ 0 := by
    rw [hv_def]; exact neg_ne_zero.mpr h_log_ne
  rw [if_neg hv_ne_zero] at h_v_HasSum
  -- Now h_v_HasSum : HasSum (fun k => B_k · v^k / k!) (v / (exp v - 1))
  -- Goal: HasSum (fun k => B_k · v^k / k!) (log z · z / (z - 1)).
  -- Need to show v / (exp v - 1) = log z · z / (z - 1).
  have h_rhs_eq : v / (Complex.exp v - 1) = Complex.log z * z / (z - 1) := by
    rw [hv_def]
    rw [exp_neg_log_eq_inv hz0]
    -- v / (z⁻¹ - 1) = (-log z) / (z⁻¹ - 1) = (-log z) · z / (1 - z) = log z · z / (z - 1).
    have h_z_inv_minus_one : z⁻¹ - 1 = (1 - z) / z := by
      field_simp
    rw [h_z_inv_minus_one]
    have h_one_minus_z : (1 : ℂ) - z ≠ 0 := by
      intro h0
      have : z = 1 := by linear_combination -h0
      exact hz1 this
    have h_z_minus_one : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    field_simp
    ring
  rw [h_rhs_eq] at h_v_HasSum
  exact h_v_HasSum

/-! ## Composed capstone: through to the Jonquières partial-sum identity -/

/-- **COMPOSED CAPSTONE**: the disc-of-convergence Bernoulli identity
    `BernoulliExpHasSumOnBallTwoPi` ⟹
    `JonquieresExpansionEqualsGeomTendstoPartialAtHalf`. Composes the
    above `-log`-composition discharge with the existing
    `jonquieresExpansionEqualsGeomTendstoPartialAtHalf_of_bernoulli`. -/
theorem jonquieresExpansionEqualsGeomTendstoPartialAtHalf_of_bernoulliOnBall
    (h : BernoulliExpHasSumOnBallTwoPi) :
    JonquieresExpansionEqualsGeomTendstoPartialAtHalf :=
  jonquieresExpansionEqualsGeomTendstoPartialAtHalf_of_bernoulli
    (bernoulliExpHasSumAtNegLogNhdsHalf_of_bernoulliExpHasSumOnBallTwoPi h)

/-- **COMPOSED CAPSTONE 2**: the disc-of-convergence Bernoulli identity
    `BernoulliExpHasSumOnBallTwoPi` ⟹ the classical Jonquières germ
    identity at `(s, z) = (0, 1/2)`. -/
theorem jonquieresIdentityPointGermAtHalf_zero_of_bernoulliOnBall
    (h : BernoulliExpHasSumOnBallTwoPi) :
    JonquieresIdentityPointGermAtHalf 0 :=
  jonquieresIdentityPointGermAtHalf_zero_of_bernoulli
    (bernoulliExpHasSumAtNegLogNhdsHalf_of_bernoulliExpHasSumOnBallTwoPi h)

end PrincipiaTractalis.Analytic.Sheaf

-- Axiom audit: the unconditional discharge depends only on standard mathlib axioms.
section AxiomAudit
open PrincipiaTractalis.Analytic.Sheaf
#guard_msgs(drop info) in
#print axioms bernoulliExpHasSumAtNegLogNhdsHalf_of_bernoulliExpHasSumOnBallTwoPi
end AxiomAudit

/-!
## Manifest

This file delivers (axiom-free, no `sorry`):

* `BernoulliExpHasSumOnBallTwoPi` — the NEW SHARPEST open analytic
  Prop on the closure path. A single-variable disc-of-convergence
  statement with no `-log` composition baggage. Classical
  textbook content (Apostol Ch. 12, Whittaker & Watson §7.2);
  mathlib has its formal-power-series shadow
  (`bernoulliPowerSeries_mul_exp_sub_one`) but no analytic lift.

* `bernoulliExpHasSumAtNegLogNhdsHalf_of_bernoulliExpHasSumOnBallTwoPi`
  — UNCONDITIONAL discharge: the disc-of-convergence Prop ⟹ the
  `-log`-composed nhds-of-`1/2` Prop. Pure analytic-function
  composition.

* `jonquieresExpansionEqualsGeomTendstoPartialAtHalf_of_bernoulliOnBall`
  — composed reduction to the partial-sum form.

* `jonquieresIdentityPointGermAtHalf_zero_of_bernoulliOnBall` —
  composed reduction to the classical germ identity.

After this file the load-bearing open analytic content is exactly
the textbook **analytic Bernoulli identity on the disc of
convergence** — no log composition, no eventually-wrapping,
no Jonquières-specific structure.
-/
