/-
# Parametric `alpha_of_class` — Substrate as an Explicit Structure
# (Addresses Problem P3 — `alpha_of_class` opacity)

## Why this file exists

`PF/TuringEncoding/Operators.lean` declares
```
opaque alpha_of_class : Set Language → ℝ
```
with values constrained only by `PolylogEigenvalueConjecture`. The opacity
is honest in the sense that it transparently encodes "this function is
provided to the framework axiomatically," but it does so as an
**opaque declaration** — Lean cannot inspect or restrict the function
beyond what the conjecture pins down.

This file provides the **parametric** version: package the substrate's
α-providing commitment as an explicit `structure`. Every consumer that
needs `alpha_of_class` then takes a `SubstrateAlphaProvider` as input,
making the dependency on the substrate axiom **visible in every theorem
signature**. The values `α_P = √2` and `α_NP = φ + 1/4` then **fall out
as theorems** from the structure's invariants, not as separate axioms.

## What this enables

1. **Cleaner referee experience.** A reviewer reading
   `theorem foo (p : SubstrateAlphaProvider) : ...` sees immediately
   that `foo` depends on the substrate's α-providing commitment. No
   hidden opaque definitions.

2. **Algebraic derivation.** Within this file we prove
   `alpha_P_eq_sqrt2_from_provider` and
   `alpha_NP_eq_phi_plus_quarter_from_provider` — the α-values are
   derived as the unique positive solutions of their respective
   polynomial constraints. Pure algebra, axiom-free.

3. **Migration path forward.** A future refactor pass can replace
   `opaque alpha_of_class` with a parameter-pattern by routing it
   through `SubstrateAlphaProvider` and updating consumers. The
   present file is the structural target of that refactor.

## Integration status

This file is NOT yet imported by `PF.lean` or by any of the existing
P_NP_Complete_Proof / SpectralGap / Operators chain. It is a parallel
structural definition that does not perturb the existing build.

The "0 project axioms / 8360 jobs clean" claim of the canonical library
is preserved. Once verified locally via `lake build`, this file can be
used as the new substrate-α entry point.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import PF.TuringEncoding.Complexity
import PF.IntervalArithmetic

namespace PrincipiaTractalis.TuringEncoding

open PrincipiaTractalis

/-! ## The substrate's α-providing commitment

    Package the substrate's α-providing function together with the
    constraints it must satisfy. This is the framework's substrate
    axiom made explicit (not opaque). -/

/-- The substrate's commitment: a function from language-sets to reals,
    plus the conjecture-form invariants that pin the values on
    `ClassP` and `ClassNP`. -/
structure SubstrateAlphaProvider where
  /-- The substrate's α-providing function. -/
  alpha : Set Language → ℝ
  /-- α at `ClassP` is positive. -/
  alpha_P_pos : 0 < alpha ClassP
  /-- α at `ClassP` squared equals 2 (the substrate's P-axis invariant). -/
  alpha_P_sq : (alpha ClassP) ^ 2 = 2
  /-- α at `ClassNP` is positive. -/
  alpha_NP_pos : 0 < alpha ClassNP
  /-- α at `ClassNP` satisfies the substrate's NP-axis quadratic. -/
  alpha_NP_quadratic :
    16 * (alpha ClassNP) ^ 2 - 24 * (alpha ClassNP) - 11 = 0

namespace SubstrateAlphaProvider

/-! ## Derivation of the canonical α-values from the substrate axioms

    The substrate's α-providing commitment uniquely determines
    `alpha ClassP = √2` and `alpha ClassNP = φ + 1/4`. Pure algebra.
-/

/-- The unique positive solution of `x² = 2` is `√2`.
    Derived from the substrate's P-axis invariants. -/
theorem alpha_P_eq_sqrt2 (p : SubstrateAlphaProvider) :
    p.alpha ClassP = Real.sqrt 2 := by
  have h_sq : (p.alpha ClassP) ^ 2 = 2 := p.alpha_P_sq
  have h_pos : 0 < p.alpha ClassP := p.alpha_P_pos
  -- Take square roots: √(α²) = √2, and √(α²) = |α| = α since α > 0.
  have h_sqrt : Real.sqrt ((p.alpha ClassP) ^ 2) = Real.sqrt 2 := by
    rw [h_sq]
  rw [Real.sqrt_sq h_pos.le] at h_sqrt
  exact h_sqrt

/-- The unique positive root of `16x² − 24x − 11 = 0` is `(3 + 2√5)/4`.
    Algebraic identity: this equals `φ + 1/4` (see next theorem). -/
theorem alpha_NP_eq_canonical_form (p : SubstrateAlphaProvider) :
    p.alpha ClassNP = (3 + 2 * Real.sqrt 5) / 4 := by
  have h_quad : 16 * (p.alpha ClassNP) ^ 2 - 24 * (p.alpha ClassNP) - 11 = 0 :=
    p.alpha_NP_quadratic
  have h_pos : 0 < p.alpha ClassNP := p.alpha_NP_pos
  -- Let x = alpha ClassNP. Then 16x² - 24x - 11 = 0 means
  -- x = (24 ± √(576 + 704))/32 = (24 ± √1280)/32 = (24 ± 16√5)/32 = (3 ± 2√5)/4
  -- Since x > 0 and (3 - 2√5)/4 < 0 (because 2√5 > 4 > 3), we have
  -- x = (3 + 2√5)/4.
  -- We verify by substitution: 16 * ((3+2√5)/4)² - 24 * (3+2√5)/4 - 11
  --   = 16 * (9 + 12√5 + 20)/16 - 6(3+2√5) - 11
  --   = (29 + 12√5) - 18 - 12√5 - 11
  --   = 0 ✓
  -- The proof packages this as: x satisfies the quadratic ∧ x > 0 ∧ the
  -- other root is negative, so x must be the positive root.
  have h_sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := by
    rw [sq, Real.mul_self_sqrt]; norm_num
  -- The positive root candidate
  set y := (3 + 2 * Real.sqrt 5) / 4 with hy_def
  -- Verify y satisfies the quadratic
  have h_y_quad : 16 * y ^ 2 - 24 * y - 11 = 0 := by
    rw [hy_def]
    field_simp
    ring_nf
    -- After expansion: 16 * ((3 + 2√5)/4)² - 24 * (3+2√5)/4 - 11
    --   = 16 * (9 + 12√5 + 4·5)/16 - 6·(3 + 2√5) - 11
    --   = (9 + 12√5 + 20) - 18 - 12√5 - 11
    --   = 0
    nlinarith [h_sqrt5_sq, h_sqrt5_pos]
  -- y > 0
  have h_y_pos : 0 < y := by
    rw [hy_def]
    have : 0 < 3 + 2 * Real.sqrt 5 := by linarith [h_sqrt5_pos]
    linarith
  -- The other root candidate (negative)
  set z := (3 - 2 * Real.sqrt 5) / 4 with hz_def
  have h_sqrt5_gt_two : Real.sqrt 5 > 2 := by
    have : (2 : ℝ) ^ 2 < 5 := by norm_num
    nlinarith [Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num), h_sqrt5_pos]
  have h_z_neg : z < 0 := by
    rw [hz_def]
    have : 3 - 2 * Real.sqrt 5 < 0 := by linarith [h_sqrt5_gt_two]
    linarith
  -- 16(α)² - 24α - 11 = 16(α - y)(α - z) (after factoring)
  -- Since α > 0 and z < 0, we have α ≠ z. Since α satisfies the quadratic,
  -- α = y.
  -- The factorization: 16x² - 24x - 11 = 16(x - y)(x - z)
  -- Check: 16(x - y)(x - z) = 16(x² - (y+z)x + yz)
  --                          = 16x² - 16(y+z)x + 16yz
  -- y + z = ((3+2√5) + (3-2√5))/4 = 6/4 = 3/2
  -- 16(y+z) = 16 · 3/2 = 24 ✓
  -- y · z = (3+2√5)(3-2√5)/16 = (9 - 4·5)/16 = -11/16
  -- 16 · y · z = -11 ✓
  -- So 16x² - 24x - 11 = 16(x - y)(x - z).
  have h_factor : ∀ x : ℝ, 16 * x ^ 2 - 24 * x - 11 = 16 * (x - y) * (x - z) := by
    intro x
    rw [hy_def, hz_def]
    field_simp
    ring_nf
    nlinarith [h_sqrt5_sq]
  -- alpha ClassNP satisfies 16 * (·)² - 24 · - 11 = 0, factored:
  -- 16 * (α - y) * (α - z) = 0
  have h_factored : 16 * (p.alpha ClassNP - y) * (p.alpha ClassNP - z) = 0 := by
    rw [← h_factor]
    exact h_quad
  -- Either α - y = 0 or α - z = 0
  have h_alt : p.alpha ClassNP = y ∨ p.alpha ClassNP = z := by
    rcases mul_eq_zero.mp (by linarith : (p.alpha ClassNP - y) * (p.alpha ClassNP - z) = 0) with h | h
    · left; linarith
    · right; linarith
  -- Eliminate the z case using α > 0 and z < 0
  rcases h_alt with h_eq_y | h_eq_z
  · exact h_eq_y
  · exfalso
    have : p.alpha ClassNP < 0 := h_eq_z ▸ h_z_neg
    linarith [p.alpha_NP_pos]

/-- The substrate's NP-axis α equals the canonical `φ + 1/4`.
    This is the algebraic identity `(3 + 2√5)/4 = (1 + √5)/2 + 1/4`. -/
theorem alpha_NP_eq_phi_plus_quarter (p : SubstrateAlphaProvider) :
    p.alpha ClassNP = phi + 1 / 4 := by
  rw [alpha_NP_eq_canonical_form p]
  unfold phi
  ring

/-! ## Spectral gap value from the parametric substrate

    Given any `SubstrateAlphaProvider`, the spectral gap value
    `π/(10·√2) − π/(10·(φ+1/4))` is determined and equal to the
    canonical `0.0539677287...` (the existing `spectral_gap_value` in
    `PF/SpectralGap.lean` covers the arithmetic certificate). The
    parametric version just connects to the structure. -/

/-- The spectral gap value as a function of the substrate provider.
    Equal to the existing `spectral_gap` because the α-values are
    determined by the substrate's invariants. -/
noncomputable def spectral_gap_from_provider (p : SubstrateAlphaProvider) : ℝ :=
  pi_10 / (p.alpha ClassP) - pi_10 / (p.alpha ClassNP)

/-- The parametric spectral gap is positive, derived from the substrate's
    α-invariants without reference to any opaque function. -/
theorem spectral_gap_from_provider_pos (p : SubstrateAlphaProvider) :
    0 < spectral_gap_from_provider p := by
  unfold spectral_gap_from_provider
  rw [alpha_P_eq_sqrt2 p, alpha_NP_eq_phi_plus_quarter p]
  -- Reduces to: π/(10√2) > π/(10(φ+1/4))
  -- Equivalent to: 1/√2 > 1/(φ+1/4), i.e. √2 < φ + 1/4
  -- This is exactly `phi_plus_quarter_gt_sqrt2` from IntervalArithmetic.
  have h_gt := phi_plus_quarter_gt_sqrt2
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_phi_plus_pos : 0 < phi + 1 / 4 := by
    have : 0 < phi := by unfold phi; positivity
    linarith
  have h_pi_10_pos : 0 < pi_10 := by
    unfold pi_10
    have : 0 < Real.pi := Real.pi_pos
    linarith
  rw [sub_pos]
  apply div_lt_div_of_pos_left h_pi_10_pos _ h_gt
  positivity

/-! ## Summary

    This file replaces the opaque `alpha_of_class` with a parametric
    structure. Every consumer that uses `SubstrateAlphaProvider` makes
    the substrate's α-axiom visible in its signature. The values
    `α_P = √2` and `α_NP = φ + 1/4` are derived from the structure's
    invariants by routine algebra (no `sorry`).

    This addresses Problem P3 (opacity of `alpha_of_class`) in
    `OPEN_PROBLEMS.md`. The next migration step is to route the
    existing `P_NEQ_NP` chain through `SubstrateAlphaProvider`
    instead of through the opaque function. -/

end SubstrateAlphaProvider

end PrincipiaTractalis.TuringEncoding
