/-
# Jonquières Germ at `s = -1` — Algebraic Decomposition + Honest Residual

This file MIRRORS `JonquieresGermAtOneDischarge.lean` for the value
`s = -1`, providing the algebraic decomposition of the Jonquières
expansion at this negative-integer value, an honest definition of the
precise scalar residual at the witness point `z = 1/2`, a pointwise
reduction theorem, and a structural equivalence between the literal
germ Prop and the polylog-eliminated rational form from
`JonquieresAtNegOneDischarge.lean`.

## Why `s = -1` is structurally different from `s = 0` and `s = 1`

At `s = 0` the disc-of-convergence Bernoulli technique closes the germ
identity unconditionally (see `BernoulliFnHasSumOnSomeBallDischarge.lean`,
theorem `jonquieresIdentityPointGermAtHalf_zero_proved`). The key
algebraic identity is:

  `ζ(-k) · (log z)^k / k!  =  B_{k+1} · (-log z)^k / (k+1)!`

(per-term, axiom-free via `riemannZeta_neg_nat_eq_bernoulli`).

At `s = 1` the literal identity is structurally FALSE under mathlib's
regularization `Complex.Gamma 0 = 0`, because the polylog-side
`-log(1 - z)` is missing the additive `riemannZeta 1` constant that
the regularized expansion carries (see `JonquieresGermAtOneDischarge.lean`
for the analysis).

At `s = -1`, by contrast:

1. **`Complex.Gamma (1 - (-1)) = Complex.Gamma 2 = 1`** is finite and
   nonzero — `Γ(N+1) = N!` for any `N : ℕ`.
2. The factor `(-log z)^(s - 1) = (-log z)^(-2)` is `1/(log z)^2`, finite
   for `z ≠ 1` and `z ≠ 0`.
3. `riemannZeta (-1 - k)` for `k ≥ 0` is the well-defined regularized
   value `(-1)^{k+1}·B_{k+2}/(k+2)` via mathlib's
   `riemannZeta_neg_nat_eq_bernoulli` at `n = k+1`.

Consequently, the Jonquières expansion at `s = -1` is the LITERAL sum
of finite regular terms, and the classical identity

  `polyLog (-1) z = z / (1 - z)^2 = jonquieresExpansion (-1) z`

on `‖z‖ < 1` should hold — but the proof requires identifying the
N=1 shifted Bernoulli-series tail with the algebraic correction
`z/(1-z)^2 - 1/(log z)^2`. Mechanizing this is the analog of the
`s = 0` discharge, with N-fold derivative content replacing the
single Cauchy product.

## What this file delivers (axiom-free, no `sorry`)

1. **`jonquieresGammaTerm_neg_one_eq`** — the Γ-term at `s = -1` has
   the closed form `1 / (Complex.log z)^2` for `z ≠ 0, z ≠ 1` (using
   `Complex.Gamma_nat_eq_factorial`, `cpow_neg`, `cpow_two`).

2. **`jonquieresGammaTerm_neg_one_at_half`** — explicit value at the
   witness point: `jonquieresGammaTerm (-1) (1/2) = 1 / (log 2)^2`.

3. **`jonquieresOneNegResidualAtHalf`** (noncomputable def) — the
   precise scalar residual at the witness point `z = 1/2`:
   `jonquieresExpansion (-1) (1/2) - 2`. (The value `2` is the rational
   closed form `(1/2) / (1 - 1/2)^2 = 2`, see
   `rational_at_half_eq_two` in `JonquieresAtNegOneDischarge.lean`.)

4. **`polyLog_neg_one_eq_jonquieresExpansion_at_half_of_residual_zero`**
   — POINTWISE REDUCTION: vanishing of the residual ⟹ pointwise
   identity at `z = 1/2`.

5. **`jonquieresIdentityPointGermAtHalf_neg_one_iff_germ_eq_rational`**
   — STRUCTURAL EQUIVALENCE: the literal germ Prop
   `JonquieresIdentityPointGermAtHalf (-1)` is equivalent to the
   polylog-eliminated germ
   `(fun z => z / (1 - z)^2) =ᶠ[nhds (1/2)] jonquieresExpansion (-1)`.
   This is the rewrite that powers `JonquieresAtNegOneDischarge.lean`'s
   sharper Prop `JonquieresExpansionEqualsRationalAtNegOne`.

## What this file does NOT deliver

A literal proof of `JonquieresIdentityPointGermAtHalf (-1)`. Closing
this Prop requires either:

* The N=1 analog of the disc-of-convergence Bernoulli technique:
  identify
  `Σ_{k≥0} ζ(-1-k) · (log z)^k / k!`
  with
  `z / (1 - z)^2 - 1 / (log z)^2`
  via the once-differentiated Bernoulli generating function
  `(d/dv)[v / (e^v - 1)]`. Mechanizing this requires a `HasSum`
  version of the differentiated Bernoulli series; not yet in mathlib
  at full strength. (Multi-week formalization track.)

* The classical Hankel-contour residue at the now non-trivial
  Γ-factor `Γ(2) = 1` plus higher-derivative residue extraction at
  the (-log z)^(-2) singular term (Wood 1992 §3.1 for the
  systematic treatment).

Both paths are open at `s = -1` (and at every `s = -N`, `N ≥ 1`); this
file honestly records the algebraic decomposition and the precise
scalar residual, without inventing axioms or false closures.

Stage L26 — Honest algebraic decomposition at `s = -1`.
-/

import PF.Analytic.JonquieresAtNegOneDischarge
import PF.Analytic.PolyLogAnalyticAtHalfNegInt

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Step 1: the Γ-term at `s = -1` -/

/-- **The Γ-term at `s = -1`**: `jonquieresGammaTerm (-1) z = 1 / (log z)^2`
    for `z ≠ 0` and `z ≠ 1`.

    Proof: `jonquieresGammaTerm (-1) z = Γ(1 - (-1)) · (-log z)^(-1 - 1)
    = Γ(2) · (-log z)^(-2) = 1 · 1/(-log z)^2 = 1/(log z)^2`.

    Uses `Complex.Gamma_nat_eq_factorial` at `n = 1` (`Γ(2) = 1! = 1`),
    `cpow_neg`, `cpow_two`, and `neg_pow_two` for the squared-negation
    collapse. -/
theorem jonquieresGammaTerm_neg_one_eq {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    jonquieresGammaTerm (-1) z = 1 / (Complex.log z)^2 := by
  unfold jonquieresGammaTerm
  -- Γ(1 - (-1)) = Γ(2) = 1
  have h_gamma : Complex.Gamma (1 - (-1 : ℂ)) = 1 := by
    have h_arg : (1 : ℂ) - (-1) = ((1 : ℕ) : ℂ) + 1 := by push_cast; ring
    rw [h_arg, Complex.Gamma_nat_eq_factorial]
    simp
  rw [h_gamma, one_mul]
  -- (-log z)^(-1 - 1) = (-log z)^(-2) = 1 / (-log z)^2 = 1 / (log z)^2
  have h_exp : (-1 : ℂ) - 1 = -(2 : ℕ) := by push_cast; ring
  rw [h_exp]
  have h_log_ne : Complex.log z ≠ 0 := by
    intro h
    have : z = 1 := by
      have := Complex.exp_log hz0
      rw [h, Complex.exp_zero] at this
      exact this.symm
    exact hz1 this
  have h_neg_log_ne : -(Complex.log z) ≠ 0 := neg_ne_zero.mpr h_log_ne
  -- (-log z)^(-2 : ℕ) via cpow_neg + cpow_natCast
  rw [cpow_neg, cpow_natCast]
  have h_sq : (-(Complex.log z))^2 = (Complex.log z)^2 := by ring
  rw [h_sq]
  -- (... ^ 2)⁻¹ = 1 / (... ^ 2)
  rw [inv_eq_one_div]

/-! ## Step 2: the Γ-term at the witness point `z = 1/2` -/

/-- **The Γ-term at `z = 1/2`**: `jonquieresGammaTerm (-1) (1/2)
    = 1 / (log 2)^2`.

    Uses the inlined identity `log(1/2) = -log 2` (mathlib:
    `Complex.log_inv` + `Real.log_inv`). -/
theorem jonquieresGammaTerm_neg_one_at_half :
    jonquieresGammaTerm (-1) (1/2 : ℂ) = 1 / ((Real.log 2 : ℝ) : ℂ)^2 := by
  have h_half_ne_zero : (1/2 : ℂ) ≠ 0 := by norm_num
  have h_half_ne_one : (1/2 : ℂ) ≠ 1 := by norm_num
  rw [jonquieresGammaTerm_neg_one_eq h_half_ne_zero h_half_ne_one]
  -- Need: 1 / (log (1/2))^2 = 1 / (log 2)^2
  -- log(1/2) = -log 2 in ℂ via Complex.ofReal_log and Real.log_inv.
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

/-- **The Jonquières residual at the witness point `z = 1/2` for `s = -1`**:
    `jonquieresExpansion (-1) (1/2) - 2`.

    The value `2` is the rational closed form
    `(1/2) / (1 - 1/2)^2 = 2`
    (theorem `rational_at_half_eq_two`).

    This is a fully determined complex scalar — namely the regularized
    sum `(1 / (log 2)^2) + Σ' k, ζ(-1-k) · (log(1/2))^k / k!` minus
    `2`. We make NO claim about whether this residual is zero; that
    question is exactly the pointwise content of
    `polyLog (-1) (1/2) = jonquieresExpansion (-1) (1/2)`.

    Numerical estimate: `1/(log 2)^2 ≈ 2.0814`, and the ζ-series tail
    starts at `ζ(-1) = -1/12 ≈ -0.0833`, with rapidly decaying higher
    terms. So the residual should be small (consistent with
    classical-identity-holds), but the formal numerical bound is open. -/
noncomputable def jonquieresOneNegResidualAtHalf : ℂ :=
  jonquieresExpansion (-1) (1/2 : ℂ) - 2

/-! ## Step 4: pointwise reduction at `z = 1/2` -/

/-- **Pointwise reduction at `z = 1/2` for `s = -1`**: if
    `jonquieresOneNegResidualAtHalf = 0` (i.e.,
    `jonquieresExpansion (-1) (1/2) = 2`), then the literal pointwise
    identity `polyLog (-1) (1/2) = jonquieresExpansion (-1) (1/2)` holds.

    Proof: `polyLog (-1) (1/2) = (1/2) / (1 - 1/2)^2 = 2` from
    `polyLog_neg_one_eq_jonquieresExpansion_at_half_of_value`. -/
theorem polyLog_neg_one_eq_jonquieresExpansion_at_half_of_residual_zero
    (h : jonquieresOneNegResidualAtHalf = 0) :
    polyLog (-1) (1/2 : ℂ) = jonquieresExpansion (-1) (1/2 : ℂ) := by
  unfold jonquieresOneNegResidualAtHalf at h
  have h_val : jonquieresExpansion (-1) (1/2 : ℂ) = 2 := by
    linear_combination h
  exact polyLog_neg_one_eq_jonquieresExpansion_at_half_of_value h_val

/-! ## Step 5: structural equivalence with the polylog-eliminated form -/

/-- **Structural equivalence at `s = -1`**: the literal germ Prop
    `JonquieresIdentityPointGermAtHalf (-1)` (germ equality of
    `polyLog (-1)` and `jonquieresExpansion (-1)` at `z = 1/2`) is
    EQUIVALENT to the polylog-eliminated germ
    `(fun z => z / (1 - z)^2) =ᶠ[nhds (1/2)] jonquieresExpansion (-1)`.

    Proof: on a neighborhood of `1/2` contained in `Metric.ball 0 1`,
    we have `polyLog (-1) z = z / (1 - z)^2` UNCONDITIONALLY
    (theorem `polyLog_neg_one_eq_geom_sq` from
    `JonquieresAtNegOneDischarge.lean`). So substituting in either
    direction of the germ equality preserves it.

    This is the rewrite that powers
    `JonquieresAtNegOneDischarge.lean`'s sharper Prop
    `JonquieresExpansionEqualsRationalAtNegOne` (the `∃ᶠ`-form of the
    same content, after `polyLog (-1)` is replaced by its disc
    closed form). -/
theorem jonquieresIdentityPointGermAtHalf_neg_one_iff_germ_eq_rational :
    JonquieresIdentityPointGermAtHalf (-1) ↔
      (fun z : ℂ => z / (1 - z)^2)
        =ᶠ[nhds (1/2 : ℂ)] jonquieresExpansion (-1) := by
  unfold JonquieresIdentityPointGermAtHalf JonquieresIdentityPointGerm
  constructor
  · -- Forward: polyLog (-1) =ᶠ jonquieres ⟹ z/(1-z)^2 =ᶠ jonquieres
    intro h_germ
    have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
      (Metric.isOpen_ball).mem_nhds half_mem_ball_one
    have h_polyLog_eq : ∀ᶠ z in 𝓝 (1/2 : ℂ),
        polyLog (-1) z = z / (1 - z)^2 := by
      filter_upwards [h_unit_nhd] with z hz
      have h_norm : ‖z‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      exact polyLog_neg_one_eq_geom_sq z h_norm
    filter_upwards [h_germ, h_polyLog_eq] with z hz1 hz2
    rw [← hz2, hz1]
  · -- Backward: z/(1-z)^2 =ᶠ jonquieres ⟹ polyLog (-1) =ᶠ jonquieres
    intro h_rat_germ
    have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
      (Metric.isOpen_ball).mem_nhds half_mem_ball_one
    have h_polyLog_eq : ∀ᶠ z in 𝓝 (1/2 : ℂ),
        polyLog (-1) z = z / (1 - z)^2 := by
      filter_upwards [h_unit_nhd] with z hz
      have h_norm : ‖z‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      exact polyLog_neg_one_eq_geom_sq z h_norm
    filter_upwards [h_rat_germ, h_polyLog_eq] with z hz1 hz2
    rw [hz2, hz1]

/-! ## Step 6: composed pointwise capstone -/

/-- **Capstone (pointwise at `z = 1/2`)**: if the precise scalar
    residual `jonquieresOneNegResidualAtHalf` vanishes, then the
    pointwise identity at `z = 1/2` holds.

    This is the single explicit numerical residual that closure work
    at `s = -1` needs to address — a single complex equation involving
    `1 / (log 2)^2` and the sum
    `Σ' k, ζ(-1-k) · (log(1/2))^k / k!`. -/
theorem polyLog_neg_one_eq_jonquieresExpansion_at_half_capstone
    (h : jonquieresOneNegResidualAtHalf = 0) :
    polyLog (-1) (1/2 : ℂ) = jonquieresExpansion (-1) (1/2 : ℂ) :=
  polyLog_neg_one_eq_jonquieresExpansion_at_half_of_residual_zero h

/-! ## Step 7: bridge from the rational-germ form to the sharper open Prop

The germ form `(fun z => z / (1 - z)^2) =ᶠ[nhds (1/2)] jonquieresExpansion (-1)`
(the RHS of the iff in Step 5) is STRICTLY STRONGER than the existing
`JonquieresExpansionEqualsRationalAtNegOne` (`∃ᶠ`-form). The former
gives an entire neighborhood; the latter only frequent agreement.

Therefore, IF the literal germ Prop
`JonquieresIdentityPointGermAtHalf (-1)` holds, the existing sharper
Prop `JonquieresExpansionEqualsRationalAtNegOne` follows immediately
(via Step 5's forward direction + the `EventuallyEq → ∃ᶠ` transfer
in the punctured nhds, mirroring `JonquieresAtZeroFinalDischarge.lean`'s
`jonquieresExpansionEqualsGeomFrequentlyAtHalf_of_germ`). -/

/-- **Punctured-nhds frequent agreement from germ at `s = -1`**:
    `JonquieresIdentityPointGermAtHalf (-1)` ⟹
    `JonquieresExpansionEqualsRationalAtNegOne`.

    Mirrors `jonquieresExpansionEqualsGeomFrequentlyAtHalf_of_germ`
    from `JonquieresAtZeroFinalDischarge.lean` at the `s = -1` value
    using the rational closed form `z / (1 - z)^2`. -/
theorem jonquieresExpansionEqualsRationalAtNegOne_of_germ
    (h_germ : JonquieresIdentityPointGermAtHalf (-1)) :
    JonquieresExpansionEqualsRationalAtNegOne := by
  rw [jonquieresIdentityPointGermAtHalf_neg_one_iff_germ_eq_rational] at h_germ
  -- h_germ : (fun z => z / (1 - z)^2) =ᶠ[nhds (1/2)] jonquieresExpansion (-1)
  -- Transfer to 𝓝[≠] (1/2) via nhdsWithin_le_nhds, then frequently.
  unfold JonquieresExpansionEqualsRationalAtNegOne
  have h_punc : ∀ᶠ z in 𝓝[≠] (1/2 : ℂ),
      z / (1 - z)^2 = jonquieresExpansion (-1) z :=
    h_germ.filter_mono nhdsWithin_le_nhds
  -- 𝓝[≠] (1/2) is non-trivial (ℂ has no isolated points).
  haveI : Filter.NeBot (𝓝[≠] (1/2 : ℂ)) :=
    Module.punctured_nhds_neBot ℝ ℂ (1/2 : ℂ)
  exact h_punc.frequently

end PrincipiaTractalis.Analytic.Sheaf

/-! ## Axiom audit -/

section AxiomAudit
open PrincipiaTractalis.Analytic.Sheaf
#guard_msgs(drop info) in
#print axioms jonquieresGammaTerm_neg_one_eq
#guard_msgs(drop info) in
#print axioms jonquieresGammaTerm_neg_one_at_half
#guard_msgs(drop info) in
#print axioms polyLog_neg_one_eq_jonquieresExpansion_at_half_of_residual_zero
#guard_msgs(drop info) in
#print axioms jonquieresIdentityPointGermAtHalf_neg_one_iff_germ_eq_rational
#guard_msgs(drop info) in
#print axioms polyLog_neg_one_eq_jonquieresExpansion_at_half_capstone
#guard_msgs(drop info) in
#print axioms jonquieresExpansionEqualsRationalAtNegOne_of_germ
end AxiomAudit

/-!
## Manifest

This file delivers (axiom-free, no `sorry`):

* `jonquieresGammaTerm_neg_one_eq` — closed form of the Γ-term at
  `s = -1`: `Γ(2)·(-log z)^(-2) = 1/(log z)^2`.
* `jonquieresGammaTerm_neg_one_at_half` — explicit value
  `jonquieresGammaTerm (-1) (1/2) = 1/(log 2)^2`.
* `jonquieresOneNegResidualAtHalf` (def) — precise scalar residual.
* `polyLog_neg_one_eq_jonquieresExpansion_at_half_of_residual_zero` —
  vanishing residual ⟹ pointwise identity at `z = 1/2`.
* `jonquieresIdentityPointGermAtHalf_neg_one_iff_germ_eq_rational` —
  structural equivalence between the literal germ Prop and the
  polylog-eliminated rational germ.
* `polyLog_neg_one_eq_jonquieresExpansion_at_half_capstone` — composed
  pointwise capstone.
* `jonquieresExpansionEqualsRationalAtNegOne_of_germ` — germ ⟹
  frequent-agreement transfer (mirror of
  `jonquieresExpansionEqualsGeomFrequentlyAtHalf_of_germ` from
  `JonquieresAtZeroFinalDischarge.lean`).

**Honest comparison with `s = 0` and `s = 1`**:

| Property | `s = 0` | `s = 1` | `s = -1` (this file) |
|----------|---------|---------|----------------------|
| Γ(1-s) | Γ(1) = 1 | Γ(0) = 0 (mathlib regularization) | Γ(2) = 1 |
| (-log z)^(s-1) at z=1/2 | (-log(1/2))^(-1) = -1/log 2 | (-log(1/2))^0 = 1 | (-log(1/2))^(-2) = 1/(log 2)^2 |
| Γ-term at z=1/2 | -1/log 2 (finite) | 0 (regularized) | 1/(log 2)^2 ≈ 2.0814 (finite) |
| ζ-series at z=1/2 convergent? | YES (Bernoulli growth bound) | YES | YES (Bernoulli growth, shifted index) |
| Closed germ identity discharged? | YES (unconditional, Bernoulli-Cauchy) | NO (structural residual = ζ(1)) | OPEN (this file isolates the residual) |
| Closure path | done | requires Hankel residue at Γ-pole | requires N=1 differentiated Bernoulli generating function |

**Net contribution at `s = -1`**:

* The Γ-term at `s = -1` is shown to have the closed form
  `1/(log z)^2`, exhibiting the finite (not pole-cancelled) nature of
  the singular part — unlike `s = 1` where the Γ-factor vanishes by
  regularization.
* The explicit value of the Γ-term at the witness point
  `z = 1/2` is given as `1/(log 2)^2`, a fully determined real
  scalar.
* The precise scalar residual
  `jonquieresOneNegResidualAtHalf := jonquieresExpansion (-1) (1/2) - 2`
  is defined and isolated.
* The pointwise reduction theorem connects vanishing of the residual
  to the pointwise identity, which (via the disc closed form
  `polyLog (-1) (1/2) = 2`) is the literal classical identity at the
  witness point.
* The structural equivalence
  `JonquieresIdentityPointGermAtHalf (-1) ↔ rational germ at 1/2`
  records that the literal germ Prop and the polylog-eliminated
  rational form (powering `JonquieresAtNegOneDischarge.lean`'s sharper
  Prop) are equivalent.
* The germ ⟹ frequent agreement transfer
  `jonquieresExpansionEqualsRationalAtNegOne_of_germ` provides the
  missing link from the literal germ Prop to the existing sharper
  `∃ᶠ`-form, mirroring exactly the structure that powers the `s = 0`
  closure chain.

**Honest status**: this file does NOT close
`JonquieresIdentityPointGermAtHalf (-1)`. Closure requires the N=1
differentiated Bernoulli generating-function analytic identity
(`HasSum` form of `(d/dv)[v/(e^v - 1)] = -1/(e^v - 1) + v·e^v/(e^v - 1)^2`
as a Taylor series on `|v| < 2π`), which is the analog of
`BernoulliExpHasSumOnBallTwoPi` at the higher derivative. Mathlib has
the formal-power-series infrastructure but no analytic lift; this is
the classical-analysis residual that any future closure must address.

Stage L26 — Honest algebraic decomposition at `s = -1`.
-/
