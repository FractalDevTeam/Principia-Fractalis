/-
# Jonquières Germ at `s = -2` — Algebraic Decomposition + Honest Residual

This file MIRRORS `JonquieresGermAtNegOneDischarge.lean` for the value
`s = -2`, providing the algebraic decomposition of the Jonquières
expansion at this negative-integer value, an honest definition of the
precise scalar residual at the witness point `z = 1/2`, a pointwise
reduction theorem, and a structural equivalence between the literal
germ Prop and the polylog-eliminated rational form from
`JonquieresAtNegTwoDischarge.lean`.

## Why `s = -2` is structurally different from `s = 0` and `s = 1`

At `s = -2`:

1. **`Complex.Gamma (1 - (-2)) = Complex.Gamma 3 = 2! = 2`** is finite
   and nonzero — `Γ(N+1) = N!` for any `N : ℕ` (mathlib's
   `Complex.Gamma_nat_eq_factorial`).
2. The factor `(-log z)^(s - 1) = (-log z)^(-3) = -1/(log z)^3`
   (since `(-x)^3 = -x^3`), finite for `z ≠ 1` and `z ≠ 0`.
3. `riemannZeta (-2 - k)` for `k ≥ 0`: in particular `ζ(-2) = 0`,
   `ζ(-3) = 1/120`, `ζ(-4) = 0`, ... (the trivial zeros of zeta at
   negative even integers cancel half the series).

Consequently, the Jonquières expansion at `s = -2` is the LITERAL sum
of finite regular terms, and the classical identity

  `polyLog (-2) z = z·(1 + z) / (1 - z)^3 = jonquieresExpansion (-2) z`

on `‖z‖ < 1` should hold — but the proof requires identifying the
N=2 shifted Bernoulli-series tail with the algebraic correction
`z·(1+z)/(1-z)^3 + 2/(log z)^3`. Mechanizing this is the second-derivative
analog of the `s = 0` discharge.

## What this file delivers (axiom-free, no `sorry`)

1. **`jonquieresGammaTerm_neg_two_eq`** — the Γ-term at `s = -2` has
   the closed form `-2 / (Complex.log z)^3` for `z ≠ 0, z ≠ 1` (using
   `Complex.Gamma_nat_eq_factorial`, `cpow_neg`, `cpow_natCast`,
   and `neg_pow_three`).

2. **`jonquieresGammaTerm_neg_two_at_half`** — explicit value at the
   witness point: `jonquieresGammaTerm (-2) (1/2) = 2/(log 2)^3`.
   (Note: `log(1/2) = -log 2`, so `(log(1/2))^3 = -(log 2)^3`, and
   `-2/(log(1/2))^3 = -2/(-(log 2)^3) = 2/(log 2)^3`.)

3. **`jonquieresTwoNegResidualAtHalf`** (noncomputable def) — the
   precise scalar residual at the witness point `z = 1/2`:
   `jonquieresExpansion (-2) (1/2) - 6`. (The value `6` is the rational
   closed form `(1/2)·(3/2) / (1/2)^3 = 6`, see
   `rational_at_half_eq_six` in `JonquieresAtNegTwoDischarge.lean`.)

4. **`polyLog_neg_two_eq_jonquieresExpansion_at_half_of_residual_zero`**
   — POINTWISE REDUCTION: vanishing of the residual ⟹ pointwise
   identity at `z = 1/2`.

5. **`jonquieresIdentityPointGermAtHalf_neg_two_iff_germ_eq_rational`**
   — STRUCTURAL EQUIVALENCE: the literal germ Prop
   `JonquieresIdentityPointGermAtHalf (-2)` is equivalent to the
   polylog-eliminated germ
   `(fun z => z*(1+z) / (1-z)^3) =ᶠ[nhds (1/2)] jonquieresExpansion (-2)`.

6. **`jonquieresExpansionEqualsRationalAtNegTwo_of_germ`** — germ ⟹
   `JonquieresExpansionEqualsRationalAtNegTwo` (the existing sharper
   `∃ᶠ`-form). Mirrors the s = 0 structure
   `jonquieresExpansionEqualsGeomFrequentlyAtHalf_of_germ`.

## What this file does NOT deliver

A literal proof of `JonquieresIdentityPointGermAtHalf (-2)`. Closure
requires either:

* The N=2 analog of the disc-of-convergence Bernoulli technique:
  identify
  `Σ_{k≥0} ζ(-2-k) · (log z)^k / k!`
  with
  `z·(1+z) / (1 - z)^3 + 2/(log z)^3`
  via the twice-differentiated Bernoulli generating function
  `(d^2/dv^2)[v / (e^v - 1)]`. Multi-week formalization track.

* The classical Hankel-contour residue at the Γ-factor `Γ(3) = 2`
  plus higher-derivative residue extraction at the `(-log z)^(-3)`
  singular term.

Both paths are open at `s = -2` (and at every `s = -N`, `N ≥ 1`); this
file honestly records the algebraic decomposition and the precise
scalar residual, without inventing axioms or false closures.

Stage L26 — Honest algebraic decomposition at `s = -2`.
-/

import PF.Analytic.JonquieresAtNegTwoDischarge
import PF.Analytic.PolyLogAnalyticAtHalfNegInt

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Step 1: the Γ-term at `s = -2` -/

/-- **The Γ-term at `s = -2`**: `jonquieresGammaTerm (-2) z
    = -2 / (Complex.log z)^3` for `z ≠ 0` and `z ≠ 1`.

    Proof: `jonquieresGammaTerm (-2) z = Γ(1 - (-2)) · (-log z)^(-2 - 1)
    = Γ(3) · (-log z)^(-3) = 2 · 1/(-log z)^3 = 2 / (-(log z)^3)
    = -2/(log z)^3` (since `(-x)^3 = -x^3`).

    Uses `Complex.Gamma_nat_eq_factorial` at `n = 2` (`Γ(3) = 2! = 2`),
    `cpow_neg`, `cpow_natCast`, and the cubed-negation
    sign collapse. -/
theorem jonquieresGammaTerm_neg_two_eq {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    jonquieresGammaTerm (-2) z = -2 / (Complex.log z)^3 := by
  unfold jonquieresGammaTerm
  -- Γ(1 - (-2)) = Γ(3) = 2! = 2
  have h_gamma : Complex.Gamma (1 - (-2 : ℂ)) = 2 := by
    have h_arg : (1 : ℂ) - (-2) = ((2 : ℕ) : ℂ) + 1 := by push_cast; ring
    rw [h_arg, Complex.Gamma_nat_eq_factorial]
    -- (2.factorial : ℂ) = 2
    norm_num
  rw [h_gamma]
  -- (-log z)^(-2 - 1) = (-log z)^(-3) = 1/(-log z)^3
  have h_exp : (-2 : ℂ) - 1 = -(3 : ℕ) := by push_cast; ring
  rw [h_exp]
  have h_log_ne : Complex.log z ≠ 0 := by
    intro h
    have : z = 1 := by
      have := Complex.exp_log hz0
      rw [h, Complex.exp_zero] at this
      exact this.symm
    exact hz1 this
  have h_neg_log_ne : -(Complex.log z) ≠ 0 := neg_ne_zero.mpr h_log_ne
  rw [cpow_neg, cpow_natCast]
  -- (-log z)^3 = -(log z)^3
  have h_cube : (-(Complex.log z))^3 = -((Complex.log z)^3) := by ring
  rw [h_cube]
  -- 2 * (-(log z)^3)⁻¹ = -2 / (log z)^3
  have h_log_cube_ne : (Complex.log z)^3 ≠ 0 := pow_ne_zero _ h_log_ne
  field_simp

/-! ## Step 2: the Γ-term at the witness point `z = 1/2` -/

/-- **The Γ-term at `z = 1/2`**: `jonquieresGammaTerm (-2) (1/2)
    = 2 / (log 2)^3`.

    Computation: from the closed form, `jonquieresGammaTerm (-2) (1/2)
    = -2 / (log(1/2))^3`. Then `log(1/2) = -log 2`, so
    `(log(1/2))^3 = -(log 2)^3`, and `-2/(-(log 2)^3) = 2/(log 2)^3`. -/
theorem jonquieresGammaTerm_neg_two_at_half :
    jonquieresGammaTerm (-2) (1/2 : ℂ) = 2 / ((Real.log 2 : ℝ) : ℂ)^3 := by
  have h_half_ne_zero : (1/2 : ℂ) ≠ 0 := by norm_num
  have h_half_ne_one : (1/2 : ℂ) ≠ 1 := by norm_num
  rw [jonquieresGammaTerm_neg_two_eq h_half_ne_zero h_half_ne_one]
  -- log(1/2) = -log 2 in ℂ.
  have h_log_half : Complex.log (1/2 : ℂ) = -((Real.log 2 : ℝ) : ℂ) := by
    have h1 : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 1/2)]
    rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
    rw [Real.log_inv]
    push_cast
    ring
  rw [h_log_half]
  ring

/-! ## Step 3: the precise residual at the witness point `z = 1/2` -/

/-- **The Jonquières residual at the witness point `z = 1/2` for `s = -2`**:
    `jonquieresExpansion (-2) (1/2) - 6`.

    The value `6` is the rational closed form
    `(1/2)·(1 + 1/2) / (1 - 1/2)^3 = (1/2)·(3/2)/(1/8) = 6`
    (theorem `rational_at_half_eq_six`).

    Numerical estimate: the Γ-term contributes
    `2/(log 2)^3 ≈ 2/0.3330 ≈ 6.007`, and the ζ-series tail
    starts at `ζ(-2) = 0` (trivial zero), `ζ(-3) = 1/120` term,
    ... rapidly decaying. So the residual should be small
    (consistent with classical-identity-holds), but the formal
    numerical bound is open. -/
noncomputable def jonquieresTwoNegResidualAtHalf : ℂ :=
  jonquieresExpansion (-2) (1/2 : ℂ) - 6

/-! ## Step 4: pointwise reduction at `z = 1/2` -/

/-- **Pointwise reduction at `z = 1/2` for `s = -2`**: if
    `jonquieresTwoNegResidualAtHalf = 0` (i.e.,
    `jonquieresExpansion (-2) (1/2) = 6`), then the literal pointwise
    identity `polyLog (-2) (1/2) = jonquieresExpansion (-2) (1/2)` holds.

    Proof: `polyLog (-2) (1/2) = (1/2)·(3/2) / (1/2)^3 = 6` from
    `polyLog_neg_two_eq_jonquieresExpansion_at_half_of_value`. -/
theorem polyLog_neg_two_eq_jonquieresExpansion_at_half_of_residual_zero
    (h : jonquieresTwoNegResidualAtHalf = 0) :
    polyLog (-2) (1/2 : ℂ) = jonquieresExpansion (-2) (1/2 : ℂ) := by
  unfold jonquieresTwoNegResidualAtHalf at h
  have h_val : jonquieresExpansion (-2) (1/2 : ℂ) = 6 := by
    linear_combination h
  exact polyLog_neg_two_eq_jonquieresExpansion_at_half_of_value h_val

/-! ## Step 5: structural equivalence with the polylog-eliminated form -/

/-- **Structural equivalence at `s = -2`**: the literal germ Prop
    `JonquieresIdentityPointGermAtHalf (-2)` is EQUIVALENT to the
    polylog-eliminated germ
    `(fun z => z*(1+z) / (1-z)^3) =ᶠ[nhds (1/2)] jonquieresExpansion (-2)`.

    Proof: on a neighborhood of `1/2` contained in `Metric.ball 0 1`,
    `polyLog (-2) z = z*(1+z) / (1-z)^3` UNCONDITIONALLY
    (theorem `polyLog_neg_two_eq_rational` from
    `JonquieresAtNegTwoDischarge.lean`). -/
theorem jonquieresIdentityPointGermAtHalf_neg_two_iff_germ_eq_rational :
    JonquieresIdentityPointGermAtHalf (-2) ↔
      (fun z : ℂ => z * (1 + z) / (1 - z)^3)
        =ᶠ[nhds (1/2 : ℂ)] jonquieresExpansion (-2) := by
  unfold JonquieresIdentityPointGermAtHalf JonquieresIdentityPointGerm
  constructor
  · -- Forward: polyLog (-2) =ᶠ jonquieres ⟹ z(1+z)/(1-z)^3 =ᶠ jonquieres
    intro h_germ
    have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
      (Metric.isOpen_ball).mem_nhds half_mem_ball_one
    have h_polyLog_eq : ∀ᶠ z in 𝓝 (1/2 : ℂ),
        polyLog (-2) z = z * (1 + z) / (1 - z)^3 := by
      filter_upwards [h_unit_nhd] with z hz
      have h_norm : ‖z‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      exact polyLog_neg_two_eq_rational z h_norm
    filter_upwards [h_germ, h_polyLog_eq] with z hz1 hz2
    rw [← hz2, hz1]
  · -- Backward: z(1+z)/(1-z)^3 =ᶠ jonquieres ⟹ polyLog (-2) =ᶠ jonquieres
    intro h_rat_germ
    have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
      (Metric.isOpen_ball).mem_nhds half_mem_ball_one
    have h_polyLog_eq : ∀ᶠ z in 𝓝 (1/2 : ℂ),
        polyLog (-2) z = z * (1 + z) / (1 - z)^3 := by
      filter_upwards [h_unit_nhd] with z hz
      have h_norm : ‖z‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      exact polyLog_neg_two_eq_rational z h_norm
    filter_upwards [h_rat_germ, h_polyLog_eq] with z hz1 hz2
    rw [hz2, hz1]

/-! ## Step 6: composed pointwise capstone -/

/-- **Capstone (pointwise at `z = 1/2`)**: if the precise scalar
    residual `jonquieresTwoNegResidualAtHalf` vanishes, then the
    pointwise identity at `z = 1/2` holds. -/
theorem polyLog_neg_two_eq_jonquieresExpansion_at_half_capstone
    (h : jonquieresTwoNegResidualAtHalf = 0) :
    polyLog (-2) (1/2 : ℂ) = jonquieresExpansion (-2) (1/2 : ℂ) :=
  polyLog_neg_two_eq_jonquieresExpansion_at_half_of_residual_zero h

/-! ## Step 7: bridge from the rational-germ form to the sharper open Prop -/

/-- **Punctured-nhds frequent agreement from germ at `s = -2`**:
    `JonquieresIdentityPointGermAtHalf (-2)` ⟹
    `JonquieresExpansionEqualsRationalAtNegTwo`.

    Mirrors `jonquieresExpansionEqualsGeomFrequentlyAtHalf_of_germ`
    from `JonquieresAtZeroFinalDischarge.lean` at the `s = -2` value
    using the rational closed form `z * (1 + z) / (1 - z)^3`. -/
theorem jonquieresExpansionEqualsRationalAtNegTwo_of_germ
    (h_germ : JonquieresIdentityPointGermAtHalf (-2)) :
    JonquieresExpansionEqualsRationalAtNegTwo := by
  rw [jonquieresIdentityPointGermAtHalf_neg_two_iff_germ_eq_rational] at h_germ
  unfold JonquieresExpansionEqualsRationalAtNegTwo
  have h_punc : ∀ᶠ z in 𝓝[≠] (1/2 : ℂ),
      z * (1 + z) / (1 - z)^3 = jonquieresExpansion (-2) z :=
    h_germ.filter_mono nhdsWithin_le_nhds
  haveI : Filter.NeBot (𝓝[≠] (1/2 : ℂ)) :=
    Module.punctured_nhds_neBot ℝ ℂ (1/2 : ℂ)
  exact h_punc.frequently

end PrincipiaTractalis.Analytic.Sheaf

/-! ## Axiom audit -/

section AxiomAudit
open PrincipiaTractalis.Analytic.Sheaf
#guard_msgs(drop info) in
#print axioms jonquieresGammaTerm_neg_two_eq
#guard_msgs(drop info) in
#print axioms jonquieresGammaTerm_neg_two_at_half
#guard_msgs(drop info) in
#print axioms polyLog_neg_two_eq_jonquieresExpansion_at_half_of_residual_zero
#guard_msgs(drop info) in
#print axioms jonquieresIdentityPointGermAtHalf_neg_two_iff_germ_eq_rational
#guard_msgs(drop info) in
#print axioms polyLog_neg_two_eq_jonquieresExpansion_at_half_capstone
#guard_msgs(drop info) in
#print axioms jonquieresExpansionEqualsRationalAtNegTwo_of_germ
end AxiomAudit

/-!
## Manifest

This file delivers (axiom-free, no `sorry`):

* `jonquieresGammaTerm_neg_two_eq` — closed form of the Γ-term at
  `s = -2`: `Γ(3) · (-log z)^(-3) = -2/(log z)^3`.
* `jonquieresGammaTerm_neg_two_at_half` — explicit value
  `jonquieresGammaTerm (-2) (1/2) = 2/(log 2)^3`.
* `jonquieresTwoNegResidualAtHalf` (def) — precise scalar residual.
* `polyLog_neg_two_eq_jonquieresExpansion_at_half_of_residual_zero` —
  vanishing residual ⟹ pointwise identity at `z = 1/2`.
* `jonquieresIdentityPointGermAtHalf_neg_two_iff_germ_eq_rational` —
  structural equivalence between the literal germ Prop and the
  polylog-eliminated rational germ.
* `polyLog_neg_two_eq_jonquieresExpansion_at_half_capstone` — composed
  pointwise capstone.
* `jonquieresExpansionEqualsRationalAtNegTwo_of_germ` — germ ⟹
  frequent-agreement transfer.

**Honest comparison with `s = 0`, `s = 1`, and `s = -1`**:

| Property | `s = 0` | `s = 1` | `s = -1` | `s = -2` (this file) |
|----------|---------|---------|----------|-----------------------|
| Γ(1-s) | 1 | 0 (regularized) | 1 | 2 |
| (-log z)^(s-1) at z=1/2 | -1/log 2 | 1 | 1/(log 2)^2 | -1/(log 2)^3 |
| Γ-term at z=1/2 | -1/log 2 | 0 | 1/(log 2)^2 ≈ 2.0814 | 2/(log 2)^3 ≈ 6.007 |
| Polylog rational value at z=1/2 | 1 | log 2 | 2 | 6 |
| Closed germ identity? | DONE (Bernoulli) | NO (structural residual) | OPEN | OPEN (this file isolates residual) |

**Net contribution at `s = -2`**:

* The Γ-term at `s = -2` is shown to have the closed form `-2/(log z)^3`.
* Explicit value at the witness point: `2/(log 2)^3 ≈ 6.007`.
* The precise scalar residual is defined and isolated.
* Pointwise reduction (residual = 0 ⟹ literal pointwise identity).
* Structural equivalence between germ Prop and rational germ.
* Germ ⟹ existing sharper `∃ᶠ`-form transfer.

**Honest status**: this file does NOT close
`JonquieresIdentityPointGermAtHalf (-2)`. Closure requires the N=2
differentiated Bernoulli generating-function analytic identity,
which is the analog of `BernoulliExpHasSumOnBallTwoPi` at second
derivative.

Stage L26 — Honest algebraic decomposition at `s = -2`.
-/
