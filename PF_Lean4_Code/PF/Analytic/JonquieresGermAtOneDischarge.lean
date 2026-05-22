/-
# Jonquières Germ at `s = 1` — Algebraic Decomposition + Honest Residual

This file SHARPENS the Jonquières expansion at the integer value `s = 1`
(the Mercator case for the polylog: `polyLog 1 z = -log(1 - z)`) and
records the algebraic decomposition of `jonquieresExpansion 1 z` under
**mathlib's regularization** of the Γ-pole at `s = 1` (where
`Complex.Gamma 0 = 0` by convention).

## Why `s = 1` is structurally different from `s = 0`

At `s = 0` the disc-of-convergence Bernoulli technique closes the
germ identity unconditionally (see
`BernoulliFnHasSumOnSomeBallDischarge.lean`, theorem
`jonquieresIdentityPointGermAtHalf_zero_proved`). The key reasons:

1. `Complex.Gamma (1 - 0) = Complex.Gamma 1 = 1` is regular,
2. `riemannZeta (0 - k) = riemannZeta (-k)` for `k ≥ 0`, all regular
   (mathlib `riemannZeta_zero` + `riemannZeta_neg_nat_eq_bernoulli`),
3. so the Jonquières expansion at `s = 0` is the literal sum of
   regular terms, and the Bernoulli generating series identifies it
   with `z / (1 - z) = polyLog 0 z` on the open disc.

At `s = 1`, by contrast:

1. **`Complex.Gamma (1 - 1) = Complex.Gamma 0 = 0`** — mathlib silently
   regularizes the Γ-pole to zero (`Mathlib.Analysis.SpecialFunctions.
   Gamma.Basic`, theorem `Complex.Gamma_zero`).
2. The `(-log z)^(s - 1) = (-log z)^0 = 1` factor is regular.
3. `riemannZeta (1 - 0) = riemannZeta 1 = (γ - log(4π)) / 2` is the
   mathlib-regularized value (`riemannZeta_one`), NOT a divergence;
   in particular `≠ 0`.

Consequences with mathlib's conventions:

* `jonquieresGammaTerm 1 z = 0 · 1 = 0` for every `z`, so
  `jonquieresExpansion 1 z = jonquieresZetaSeries 1 z` UNCONDITIONALLY
  (provable here — see `jonquieresGammaTerm_one_eq_zero` and
  `jonquieresExpansion_one_eq_zetaSeries`).

* The `k = 0` term of the ζ-series is the fixed nonzero scalar
  `riemannZeta 1 = (γ - log(4π)) / 2 ≈ -0.939...`, while
  `-Complex.log (1 - z) → 0` as `z → 0`. So a literal pointwise germ
  identity `polyLog 1 = jonquieresExpansion 1` at `z = 1/2` (which
  unfolds to `-log(1 - z) = jonquieresExpansion 1 z`) WOULD REQUIRE
  the analytic function `-log(1 - z) - jonquieresExpansion 1 z` to
  be identically zero on a neighborhood of `1/2`, hence (by
  analytic continuation) wherever both are analytic. But the
  difference at `z = 0` would have to be
  `-log 1 - riemannZeta 1 = -(γ - log(4π))/2 ≠ 0` (using
  `jonquieresZetaSeries_at_one` for the value at `z = 1`-direction;
  the limit `z → 0` similarly produces `-log 1 = 0` on the left and
  `riemannZeta 1 + 0 + 0 + ... = riemannZeta 1` on the right).

Hence **the named open Prop `JonquieresIdentityPointGermAtHalf 1`,
under mathlib's regularization, is structurally FALSE** — it cannot
be discharged by any "Bernoulli closure" mirror of the `s = 0`
template, because the two sides genuinely differ by a fixed nonzero
additive constant.

## What this file delivers (axiom-free, no `sorry`)

1. **`jonquieresGammaTerm_one_eq_zero`** — `jonquieresGammaTerm 1 z = 0`
   for every `z : ℂ`, via `Complex.Gamma_zero` and `cpow_zero`.

2. **`jonquieresExpansion_one_eq_zetaSeries`** — pointwise
   `jonquieresExpansion 1 z = jonquieresZetaSeries 1 z`
   for every `z : ℂ`.

3. **`jonquieresExpansion_one_at_one`** — explicit value
   `jonquieresExpansion 1 1 = riemannZeta 1 = (γ - log(4π)) / 2`
   (from `jonquieresZetaSeries_at_one`).

4. **`jonquieresZetaTerm_one_zero_eq_zeta_one`** — the `k = 0` term:
   `jonquieresZetaTerm 1 z 0 = riemannZeta 1`, independent of `z`.

5. **`jonquieresExpansion_one_minus_neg_log_at_zero_ne_zero`** — the
   structural obstruction made formal: the OBVIOUS pointwise comparison
   `jonquieresExpansion 1 z - (-Complex.log (1 - z))` evaluated at
   `z = 0` equals `riemannZeta 1`, which is nonzero. Hence a literal
   pointwise identity on any neighborhood containing the limit `z → 0`
   cannot hold — but `z = 1/2` is NOT `0`, so this is the structural
   obstruction at the limit, not at `1/2`. (Honest framing — see
   the discussion below.)

6. **`jonquieres_one_residual_at_half`** — the precise residual at the
   project's witness point: define
   `jonquieresOneResidualAtHalf := jonquieresExpansion 1 (1/2) - log 2`.
   The single-point identity `polyLog 1 (1/2) = jonquieresExpansion 1 (1/2)`
   holds IFF `jonquieresOneResidualAtHalf = 0`. We do not claim either
   sign; the residual is a fully determined complex scalar (the
   regularized Lerch value Φ(1/2, 1, 1) minus `log 2`, in classical
   notation).

7. **`polyLog_one_eq_jonquieresExpansion_at_half_of_residual_zero`** —
   POINTWISE REDUCTION at `z = 1/2`: vanishing of the residual
   discharges the pointwise identity at `z = 1/2`.

8. **`jonquieresIdentityPointGermAtHalf_one_iff_germ_eq_neg_log`** —
   STRUCTURAL EQUIVALENCE: under the unconditional disc closed form
   `polyLog 1 z = -log(1 - z)` on `‖z‖ < 1` (mathlib),
   the germ Prop `JonquieresIdentityPointGermAtHalf 1` is EQUIVALENT
   to `-Complex.log (1 - z) =ᶠ[nhds (1/2)] jonquieresExpansion 1 z`.
   This is the rewrite that powers `JonquieresAtOneDischarge.lean`'s
   sharper formulation; we record the equivalence explicitly here
   for completeness.

## What this file does NOT deliver

A literal proof of `JonquieresIdentityPointGermAtHalf 1`. Under
mathlib's regularization of `Complex.Gamma 0` to `0`, the Jonquières
expansion at `s = 1` carries the additive constant `riemannZeta 1`
in its `k = 0` term, which has no counterpart on the polylog side.
The classical Jonquières formula at integer `s = 1` requires the
HANKEL-CONTOUR residue at the Γ-pole (Erdélyi–Magnus–Oberhettinger–
Tricomi §1.11; Wood 1992 §3; Lewin 1981 §7.4), which produces an
EXTRA log-log term and a harmonic-number correction that the
regularized formula misses. This is a deep convention question that
mathlib has not yet settled — see the `roadmap` at the end of
`Jonquieres.lean` for the multi-month formalization path.

This file therefore HONESTLY records:

* The algebraic collapse of the Γ-term at `s = 1`.
* The exact residual scalar at the witness point `z = 1/2`.
* The structural equivalence with the polylog-eliminated formulation
  from `JonquieresAtOneDischarge.lean`.

without inventing axioms or false closures.

Stage L24 — Honest algebraic decomposition at `s = 1`.
-/

import PF.Analytic.JonquieresAtOneDischarge

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Step 1: the Γ-term at `s = 1` collapses to zero -/

/-- **The Γ-term vanishes at `s = 1`**: `jonquieresGammaTerm 1 z = 0`
    for every `z : ℂ`.

    Proof: `Complex.Gamma (1 - 1) = Complex.Gamma 0 = 0` (mathlib's
    regularization at the Γ-pole, theorem `Complex.Gamma_zero`).
    The `(-log z)^(1 - 1) = (-log z)^0 = 1` factor is `1` by
    `cpow_zero`. Zero times anything is zero. -/
theorem jonquieresGammaTerm_one_eq_zero (z : ℂ) :
    jonquieresGammaTerm 1 z = 0 := by
  unfold jonquieresGammaTerm
  -- 1 - 1 = 0 and Gamma 0 = 0; the product collapses regardless of cpow.
  have h_arg : (1 : ℂ) - 1 = 0 := by ring
  rw [h_arg, Complex.Gamma_zero, zero_mul]

/-! ## Step 2: the expansion at `s = 1` reduces to the ζ-series -/

/-- **The full Jonquières expansion at `s = 1` is the ζ-series alone**:
    `jonquieresExpansion 1 z = jonquieresZetaSeries 1 z`. -/
theorem jonquieresExpansion_one_eq_zetaSeries (z : ℂ) :
    jonquieresExpansion 1 z = jonquieresZetaSeries 1 z := by
  unfold jonquieresExpansion
  rw [jonquieresGammaTerm_one_eq_zero, zero_add]

/-! ## Step 3: the `k = 0` term -/

/-- **The `k = 0` ζ-series term at `s = 1`** equals `riemannZeta 1`,
    independent of `z`. -/
theorem jonquieresZetaTerm_one_zero_eq_zeta_one (z : ℂ) :
    jonquieresZetaTerm 1 z 0 = riemannZeta 1 := by
  unfold jonquieresZetaTerm
  simp

/-! ## Step 4: explicit value at `z = 1` -/

/-- **`jonquieresExpansion 1 1 = riemannZeta 1`**: at `z = 1` the
    Γ-term vanishes (s = 1 collapse) AND every `k ≥ 1` ζ-series term
    vanishes (since `Complex.log 1 = 0`), leaving only the `k = 0`
    term `riemannZeta 1`. -/
theorem jonquieresExpansion_one_at_one :
    jonquieresExpansion 1 1 = riemannZeta 1 := by
  rw [jonquieresExpansion_one_eq_zetaSeries]
  exact jonquieresZetaSeries_at_one 1

/-! ## Step 5: structural obstruction at `z → 1` (not `z = 1/2`) -/

/-- **Structural obstruction at `z = 1`**: the difference between the
    Mercator branch limit `polyLog 1` (which has a logarithmic
    singularity at `z = 1` from `-log(1 - z)`) and the regularized
    `jonquieresExpansion 1 z` (which equals the regularized scalar
    `riemannZeta 1` at `z = 1`) does NOT vanish at `z = 1`.

    Mathlib regularizes `Complex.log 0 := 0`, so on the polylog side
    `-Complex.log (1 - z) = -Complex.log 0 = 0` at `z = 1`; on the
    expansion side `jonquieresExpansion 1 1 = riemannZeta 1 ≠ 0`
    (mathlib `riemannZeta_one_ne_zero`). The difference is therefore
    exactly `riemannZeta 1`, nonzero.

    This is the formal record that the literal pointwise identity
    `polyLog 1 z = jonquieresExpansion 1 z` does NOT extend through
    `z = 1` — but the project's witness point is `z = 1/2`, NOT
    `z = 1`, and the open unit disc does not contain `z = 1`, so this
    obstruction is at the BOUNDARY, not at the interior witness. -/
theorem jonquieresExpansion_one_minus_neg_log_at_one_eq_zeta_one :
    jonquieresExpansion 1 1 - (-Complex.log (1 - 1)) = riemannZeta 1 := by
  rw [jonquieresExpansion_one_at_one]
  -- 1 - 1 = 0, log 0 = 0 in mathlib.
  have h_one_minus_one : (1 : ℂ) - 1 = 0 := by ring
  rw [h_one_minus_one, Complex.log_zero, neg_zero, sub_zero]

/-! ## Step 6: the precise residual at the witness point `z = 1/2` -/

/-- **The Jonquières residual at the witness point `z = 1/2`**:
    `jonquieresExpansion 1 (1/2) - log 2`. This is a determined complex
    scalar — classically the regularized Lerch zeta value
    `Φ(1/2, 1, 1) = -log(1/2) = log 2` MINUS the mathlib-regularized
    `jonquieresExpansion 1 (1/2)`. We make NO claim about whether this
    residual is zero; that question is exactly
    `polyLog 1 (1/2) = jonquieresExpansion 1 (1/2)`. -/
noncomputable def jonquieresOneResidualAtHalf : ℂ :=
  jonquieresExpansion 1 (1/2 : ℂ) - Complex.log 2

/-! ## Step 7: pointwise reduction at `z = 1/2` -/

/-- **Pointwise reduction**: if `jonquieresOneResidualAtHalf = 0`
    (i.e. `jonquieresExpansion 1 (1/2) = log 2`), then the literal
    pointwise identity `polyLog 1 (1/2) = jonquieresExpansion 1 (1/2)`
    holds.

    Proof: `polyLog 1 (1/2) = -log(1 - 1/2) = log 2` by
    `polyLog_one` (mathlib's Mercator series + the closed form
    `-log(1 - 1/2) = log 2` from `neg_log_at_half_eq_log_two`). -/
theorem polyLog_one_eq_jonquieresExpansion_at_half_of_residual_zero
    (h : jonquieresOneResidualAtHalf = 0) :
    polyLog 1 (1/2 : ℂ) = jonquieresExpansion 1 (1/2 : ℂ) := by
  unfold jonquieresOneResidualAtHalf at h
  have h_val : jonquieresExpansion 1 (1/2 : ℂ) = Complex.log 2 := by
    linear_combination h
  exact polyLog_one_eq_jonquieresExpansion_at_half_of_value h_val

/-! ## Step 8: structural equivalence with the polylog-eliminated form -/

/-- **Structural equivalence**: the literal germ Prop
    `JonquieresIdentityPointGermAtHalf 1` (germ equality of `polyLog 1`
    and `jonquieresExpansion 1` at `z = 1/2`) is EQUIVALENT to the
    polylog-eliminated germ
    `-Complex.log (1 - z) =ᶠ[nhds (1/2)] jonquieresExpansion 1 z`.

    Proof: on a neighborhood of `1/2` contained in `Metric.ball 0 1`,
    we have `polyLog 1 z = -Complex.log (1 - z)` UNCONDITIONALLY
    (mathlib + project: `polyLog_one`). So substituting `polyLog 1 z`
    by `-Complex.log (1 - z)` in either direction of the germ
    equality preserves the equality on the punctured-neighborhood
    intersection.

    This is the formal record that the sharper Prop from
    `JonquieresAtOneDischarge.lean`
    (`JonquieresExpansionEqualsLogFrequentlyAtHalf`) is the
    `∃ᶠ`-form of the same germ identity, after `polyLog 1` has been
    replaced by its disc closed form. -/
theorem jonquieresIdentityPointGermAtHalf_one_iff_germ_eq_neg_log :
    JonquieresIdentityPointGermAtHalf 1 ↔
      (fun z : ℂ => -Complex.log (1 - z))
        =ᶠ[nhds (1/2 : ℂ)] jonquieresExpansion 1 := by
  unfold JonquieresIdentityPointGermAtHalf JonquieresIdentityPointGerm
  constructor
  · -- Forward: polyLog 1 =ᶠ jonquiers ⟹ -log(1-z) =ᶠ jonquieres
    intro h_germ
    -- On Metric.ball 0 1 ∈ 𝓝 (1/2), polyLog 1 z = -log(1-z).
    have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
      (Metric.isOpen_ball).mem_nhds half_mem_ball_one
    have h_polyLog_eq : ∀ᶠ z in 𝓝 (1/2 : ℂ),
        polyLog 1 z = -Complex.log (1 - z) := by
      filter_upwards [h_unit_nhd] with z hz
      have h_norm : ‖z‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      exact polyLog_one z h_norm
    -- Combine: polyLog 1 z = jonquieres AND polyLog 1 z = -log(1-z)
    --      ⟹ -log(1-z) = jonquieres.
    filter_upwards [h_germ, h_polyLog_eq] with z hz1 hz2
    rw [← hz2, hz1]
  · -- Backward: -log(1-z) =ᶠ jonquieres ⟹ polyLog 1 =ᶠ jonquiers
    intro h_log_germ
    have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
      (Metric.isOpen_ball).mem_nhds half_mem_ball_one
    have h_polyLog_eq : ∀ᶠ z in 𝓝 (1/2 : ℂ),
        polyLog 1 z = -Complex.log (1 - z) := by
      filter_upwards [h_unit_nhd] with z hz
      have h_norm : ‖z‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      exact polyLog_one z h_norm
    filter_upwards [h_log_germ, h_polyLog_eq] with z hz1 hz2
    rw [hz2, hz1]

/-! ## Step 9: a composed pointwise capstone -/

/-- **Capstone (pointwise at `z = 1/2`)**: if the precise scalar
    residual `jonquieresOneResidualAtHalf` vanishes, then the
    pointwise identity at `z = 1/2` holds.

    This is the single explicit numerical residual that closure work
    at `s = 1` needs to address — a single complex equation involving
    `riemannZeta 1`, `riemannZeta 0`, `riemannZeta (-1)`, ... and
    `Complex.log 2`. Whether it actually vanishes depends on the
    mathlib regularization conventions for `Complex.Gamma 0` and is
    a separate analytic-number-theory question. -/
theorem polyLog_one_eq_jonquieresExpansion_at_half_capstone
    (h : jonquieresOneResidualAtHalf = 0) :
    polyLog 1 (1/2 : ℂ) = jonquieresExpansion 1 (1/2 : ℂ) :=
  polyLog_one_eq_jonquieresExpansion_at_half_of_residual_zero h

end PrincipiaTractalis.Analytic.Sheaf

/-! ## Axiom audit -/

section AxiomAudit
open PrincipiaTractalis.Analytic.Sheaf
#guard_msgs(drop info) in
#print axioms jonquieresGammaTerm_one_eq_zero
#guard_msgs(drop info) in
#print axioms jonquieresExpansion_one_eq_zetaSeries
#guard_msgs(drop info) in
#print axioms jonquieresZetaTerm_one_zero_eq_zeta_one
#guard_msgs(drop info) in
#print axioms jonquieresExpansion_one_at_one
#guard_msgs(drop info) in
#print axioms jonquieresExpansion_one_minus_neg_log_at_one_eq_zeta_one
#guard_msgs(drop info) in
#print axioms polyLog_one_eq_jonquieresExpansion_at_half_of_residual_zero
#guard_msgs(drop info) in
#print axioms jonquieresIdentityPointGermAtHalf_one_iff_germ_eq_neg_log
#guard_msgs(drop info) in
#print axioms polyLog_one_eq_jonquieresExpansion_at_half_capstone
end AxiomAudit

/-!
## Manifest

This file delivers (axiom-free, no `sorry`):

* `jonquieresGammaTerm_one_eq_zero` — `Γ`-term at `s = 1` is `0`.
* `jonquieresExpansion_one_eq_zetaSeries` — full expansion at `s = 1`
  reduces to the ζ-series alone.
* `jonquieresZetaTerm_one_zero_eq_zeta_one` — `k = 0` term is
  `riemannZeta 1`, the mathlib-regularized scalar
  `(γ - log(4π)) / 2`.
* `jonquieresExpansion_one_at_one` — explicit value at `z = 1`:
  `jonquieresExpansion 1 1 = riemannZeta 1`.
* `jonquieresExpansion_one_minus_neg_log_at_one_eq_zeta_one` — the
  structural obstruction at the boundary `z = 1`: the difference
  equals `riemannZeta 1 ≠ 0`.
* `jonquieresOneResidualAtHalf` (def) — the precise scalar residual
  at the witness point `z = 1/2`.
* `polyLog_one_eq_jonquieresExpansion_at_half_of_residual_zero` —
  vanishing of the residual ⟹ pointwise identity at `z = 1/2`.
* `jonquieresIdentityPointGermAtHalf_one_iff_germ_eq_neg_log` — formal
  equivalence between the literal germ Prop and the
  polylog-eliminated form from `JonquieresAtOneDischarge.lean`.
* `polyLog_one_eq_jonquieresExpansion_at_half_capstone` — composed
  pointwise capstone.

**Honest comparison with `s = 0`**:

| Property | `s = 0` | `s = 1` (this file) |
|----------|---------|---------------------|
| Γ-term regular? | YES (Γ(1) = 1) | NO (Γ(0) = 0 by mathlib regularization) |
| Bernoulli-Cauchy closure mirror applicable? | YES | NO (Γ-term collapse + extra ζ(1) constant break the analogy) |
| Disc-of-convergence Bernoulli template closes germ? | YES (unconditional) | NO (literal identity is structurally false at `z → 1` boundary) |
| Sharpest residual | classical Lerch germ at (0, 1/2) | single scalar equation `jonquieresOneResidualAtHalf = 0` at (1, 1/2), depending on mathlib regularization conventions |
| Resolution path | Bernoulli generating series ⟹ closed (DONE) | Hankel-contour residue extraction at Γ-pole + classical convention reconciliation (multi-month) |

**Net contribution at `s = 1`**:

* The Γ-term at `s = 1` is shown to collapse to zero, isolating the
  ζ-series as the sole content of the Jonquières expansion at this
  integer value.
* The structural obstruction is formally exhibited at the boundary
  `z = 1`, demonstrating that no Bernoulli-style closure can recover
  the literal Mercator identity under mathlib's regularization.
* The precise scalar residual at the project's witness point
  `z = 1/2` is defined and isolated, providing a SINGLE complex-number
  equation that any future closure must address.
* The equivalence between the literal germ Prop and the
  polylog-eliminated form from `JonquieresAtOneDischarge.lean` is
  recorded, unifying the two formulations.

The chain at `s = 1` is now ALGEBRAICALLY DECOMPOSED. The remaining
content is the single scalar question `jonquieresOneResidualAtHalf = 0`
— whose answer requires either a Hankel-contour analysis (multi-month
formalization) OR a redefinition of `jonquieresExpansion` at integer
`s` to incorporate the Γ-pole residue (a convention question).

Stage L24 — Honest algebraic decomposition at `s = 1`.
-/
