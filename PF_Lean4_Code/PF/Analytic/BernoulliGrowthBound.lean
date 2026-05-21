/-
# Bernoulli Growth Bound — Discharge of `BernoulliGrowthBoundResidual`

This file discharges the single named mathlib gap of
`PF/Analytic/JonquieresZetaSeriesSummable.lean`:

  `BernoulliGrowthBoundResidual : ∃ M ≥ 0, ∃ N, ∀ m ≥ N,
       |B_{2m}| ≤ M · (2m)! / (2π)^{2m}`

## Mathematical content

The classical proof goes via the generating function `z/(e^z - 1)` and
its poles at `z = 2πik` (k ≠ 0), giving Cauchy-Hadamard radius `2π`.
That route requires substantial complex analysis machinery (radius of
convergence of `bernoulli'PowerSeries`, identification with the analytic
function `z/(e^z-1)`, contour deformation).

We use a *much shorter* elementary route already available in mathlib:

  **`hasSum_zeta_nat` (Euler 1735)**:  for `k ≥ 1`,
  `Σ_{n} 1/n^(2k) = (-1)^(k+1) · 2^(2k-1) · π^(2k) · B_{2k} / (2k)!`.

Taking absolute values:
  `|B_{2k}| · 2^(2k-1) · π^(2k) / (2k)! = Σ 1/n^(2k) = ζ(2k)`

For `k ≥ 1`, `ζ(2k) ≤ ζ(2) = π²/6` (termwise comparison `1/n^(2k) ≤ 1/n^2`
for `n ≥ 1`, and the `n = 0` summand is `0` by mathlib convention).

Therefore
  `|B_{2k}| ≤ (2k)! · (π²/6) / (2^(2k-1) · π^(2k))
           = (π²/3) · (2k)! / (2π)^(2k)`

So `M = π²/3 ≈ 3.29` and `N = 1` work. Axiom-free.

Stage L4-B — Bernoulli growth bound discharge (unconditional, axiom-free).
-/

import PF.Analytic.JonquieresZetaSeriesSummable
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.PSeries

namespace PrincipiaTractalis.Analytic

open scoped Nat
open Filter Real

/-! ## Step 1: termwise comparison `1/n^(2k) ≤ 1/n^2` for `k ≥ 1` -/

/-- For `n` and `k ≥ 1`, `1/n^(2k) ≤ 1/n^2`. The `n = 0` case is
    handled by mathlib's convention `1/0 = 0`. -/
lemma one_div_nat_pow_two_mul_le_sq {n k : ℕ} (hk : 1 ≤ k) :
    (1 : ℝ) / (n : ℝ) ^ (2 * k) ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    -- n = 0: both sides are 1/0 = 0, since 2k ≥ 2 > 0 and 2 > 0.
    have h2k_pos : 0 < 2 * k := by omega
    simp [Nat.cast_zero, zero_pow h2k_pos.ne', zero_pow (two_ne_zero)]
  -- n ≥ 1: 1/n^(2k) ≤ 1/n^2 since n ≥ 1 means n^2 ≤ n^(2k).
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2k : (2 : ℕ) ≤ 2 * k := by omega
  have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hnpos _
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * k) :=
    pow_le_pow_right₀ hn1 h2k
  exact one_div_le_one_div_of_le hn2_pos hpow

/-! ## Step 2: `ζ(2k) ≤ π²/6` for `k ≥ 1` -/

/-- The sum `Σ 1/n^(2k)` is at most `Σ 1/n^2 = π²/6` for `k ≥ 1`. -/
theorem zeta_two_mul_nat_le_zeta_two {k : ℕ} (hk : 1 ≤ k) :
    ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)
      * bernoulli (2 * k) / (2 * k)!) ≤ Real.pi ^ 2 / 6 := by
  have hLHS : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)
        * bernoulli (2 * k) / (2 * k)!) :=
    hasSum_zeta_nat (by omega : k ≠ 0)
  have hRHS : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
    hasSum_zeta_two
  have hsum_LHS : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * k)) := hLHS.summable
  have hsum_RHS : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hRHS.summable
  have hle : ∀ n : ℕ, (1 : ℝ) / (n : ℝ) ^ (2 * k) ≤ (1 : ℝ) / (n : ℝ) ^ 2 :=
    fun _ => one_div_nat_pow_two_mul_le_sq hk
  have htsum_le : (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (2 * k))
      ≤ (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) :=
    hsum_LHS.tsum_le_tsum hle hsum_RHS
  rw [hLHS.tsum_eq, hRHS.tsum_eq] at htsum_le
  exact htsum_le

/-! ## Step 3: `ζ(2k) ≥ 0` for `k ≥ 1` -/

/-- `Σ 1/n^(2k) ≥ 0` because every term is nonneg. -/
theorem zeta_two_mul_nat_nonneg {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)
      * bernoulli (2 * k) / (2 * k)!) := by
  have hLHS : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)
        * bernoulli (2 * k) / (2 * k)!) :=
    hasSum_zeta_nat (by omega : k ≠ 0)
  have hnn : ∀ n : ℕ, 0 ≤ (1 : ℝ) / (n : ℝ) ^ (2 * k) := by
    intro n
    apply div_nonneg (by norm_num)
    exact pow_nonneg (Nat.cast_nonneg _) _
  rw [← hLHS.tsum_eq]
  exact tsum_nonneg hnn

/-! ## Step 4: rearrange to get `|B_{2k}|` bound -/

/-- The denominator `(2k)!` is positive (in ℝ). -/
lemma factorial_pos_real (k : ℕ) : (0 : ℝ) < ((2 * k)! : ℝ) := by
  exact_mod_cast (Nat.factorial_pos (2 * k))

/-- `2^(2k-1) > 0` in ℝ. -/
lemma two_pow_pos_real (k : ℕ) : (0 : ℝ) < (2 : ℝ) ^ (2 * k - 1) :=
  pow_pos (by norm_num) _

/-- `π^(2k) > 0` in ℝ. -/
lemma pi_pow_pos_real (k : ℕ) : (0 : ℝ) < Real.pi ^ (2 * k) :=
  pow_pos Real.pi_pos _

/-- `(2π)^(2k) > 0` in ℝ. -/
lemma two_pi_pow_pos_real (k : ℕ) : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) :=
  pow_pos (by positivity) _

/-- Key algebraic rewrite: `2^(2k-1) · π^(2k) = (2π)^(2k) / 2` for `k ≥ 1`. -/
lemma two_pow_pi_pow_eq {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) = (2 * Real.pi) ^ (2 * k) / 2 := by
  have hpow : (2 : ℝ) ^ (2 * k - 1) = (2 : ℝ) ^ (2 * k) / 2 := by
    have hsum : 2 * k = (2 * k - 1) + 1 := by omega
    have hexpand : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ (2 * k - 1) * 2 := by
      conv_lhs => rw [hsum, pow_succ]
    rw [hexpand]
    field_simp
  rw [hpow, mul_pow]
  ring

/-- Helper: nonneg of mul-nonneg via positive right factor. -/
private lemma nonneg_of_mul_nonneg_right_pos {x y : ℝ} (h : 0 ≤ x * y) (hy : 0 < y) : 0 ≤ x := by
  rcases le_or_lt 0 x with hx | hx
  · exact hx
  · exfalso
    have : x * y < 0 := mul_neg_of_neg_of_pos hx hy
    linarith

/-- `(-1)^(k+1) · B_{2k} ≥ 0` for `k ≥ 1`: this is the standard sign fact that
    Bernoulli numbers at positive even indices alternate sign such that
    `(-1)^(k+1) B_{2k} > 0` for k ≥ 1.

    We *derive* this from the Euler formula + `ζ(2k) ≥ 0`, without invoking
    any external sign lemma. -/
lemma sign_bernoulli_two_mul {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ ((-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ)) := by
  have hzeta := zeta_two_mul_nat_nonneg hk
  have hfact_pos : (0 : ℝ) < ((2 * k)! : ℝ) := factorial_pos_real k
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * k - 1) := two_pow_pos_real k
  have hpi_pos : (0 : ℝ) < Real.pi ^ (2 * k) := pi_pow_pos_real k
  set A := (-1 : ℝ) ^ (k + 1) with hA
  set B := (2 : ℝ) ^ (2 * k - 1) with hB
  set C := Real.pi ^ (2 * k) with hC
  set D := ((2 * k)! : ℝ) with hD
  set b := (bernoulli (2 * k) : ℝ) with hb
  -- hzeta : 0 ≤ A * B * C * b / D
  have hkey : 0 ≤ A * B * C * b / D := hzeta
  -- Multiply both sides by D > 0
  have hmul : 0 ≤ A * B * C * b := by
    have hcombined := mul_le_mul_of_nonneg_right hkey hfact_pos.le
    rw [zero_mul, div_mul_cancel₀ _ hfact_pos.ne'] at hcombined
    exact hcombined
  -- A * B * C * b = (A * b) * (B * C)
  have hrearr : A * B * C * b = (A * b) * (B * C) := by ring
  rw [hrearr] at hmul
  have hBC_pos : (0 : ℝ) < B * C := mul_pos h2pow_pos hpi_pos
  exact nonneg_of_mul_nonneg_right_pos hmul hBC_pos

/-- The signed Euler formula rewritten as
    `|B_{2k}| · 2^(2k-1) · π^(2k) / (2k)! = ζ(2k)`
    for `k ≥ 1`. -/
theorem abs_bernoulli_two_mul_eq {k : ℕ} (hk : 1 ≤ k) :
    |(bernoulli (2 * k) : ℝ)| * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)
      / ((2 * k)! : ℝ)
    = ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)
        * bernoulli (2 * k) / (2 * k)!) := by
  have hsign := sign_bernoulli_two_mul hk
  -- |(-1)^(k+1)| = 1
  have habs_sign : |((-1 : ℝ) ^ (k + 1))| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  -- |(-1)^(k+1) · B| = (-1)^(k+1) · B (since ≥ 0)
  have habs_prod : |((-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ))|
      = (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) :=
    abs_of_nonneg hsign
  -- |(-1)^(k+1) · B| = |B|
  have habs_split : |((-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ))|
      = |(bernoulli (2 * k) : ℝ)| := by
    rw [abs_mul, habs_sign, one_mul]
  -- Combining: |B| = (-1)^(k+1) · B
  have habs_B : |(bernoulli (2 * k) : ℝ)| =
      (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
    rw [← habs_split, habs_prod]
  rw [habs_B]
  ring

/-! ## Step 5: the explicit Bernoulli bound -/

/-- **The explicit Bernoulli growth bound**: for `k ≥ 1`,
    `|B_{2k}| ≤ (π²/3) · (2k)! / (2π)^(2k)`. -/
theorem bernoulli_growth_bound_explicit {k : ℕ} (hk : 1 ≤ k) :
    |(bernoulli (2 * k) : ℝ)|
      ≤ (Real.pi ^ 2 / 3) * ((2 * k)! : ℝ) / (2 * Real.pi) ^ (2 * k) := by
  -- From: |B_{2k}| · 2^(2k-1) · π^(2k) / (2k)! = ζ(2k) ≤ π²/6.
  have hbound : |(bernoulli (2 * k) : ℝ)| * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)
      / ((2 * k)! : ℝ) ≤ Real.pi ^ 2 / 6 := by
    rw [abs_bernoulli_two_mul_eq hk]
    exact zeta_two_mul_nat_le_zeta_two hk
  have hfact_pos : (0 : ℝ) < ((2 * k)! : ℝ) := factorial_pos_real k
  have h2pi_pow_pos : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) := two_pi_pow_pos_real k
  -- Clear the denominator (2k)! :
  have hbound' : |(bernoulli (2 * k) : ℝ)| * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)
      ≤ (Real.pi ^ 2 / 6) * ((2 * k)! : ℝ) :=
    (div_le_iff₀ hfact_pos).mp hbound
  -- Use 2^(2k-1) · π^(2k) = (2π)^(2k) / 2.
  rw [show (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) = (2 * Real.pi) ^ (2 * k) / 2
       from two_pow_pi_pow_eq hk] at hbound'
  -- Rearrange: |B| · ((2π)^(2k) / 2) = |B| · (2π)^(2k) / 2
  have hreshape : |(bernoulli (2 * k) : ℝ)| * ((2 * Real.pi) ^ (2 * k) / 2)
      = |(bernoulli (2 * k) : ℝ)| * (2 * Real.pi) ^ (2 * k) / 2 := by ring
  rw [hreshape] at hbound'
  -- Multiply both sides by 2.
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hbound'' : |(bernoulli (2 * k) : ℝ)| * (2 * Real.pi) ^ (2 * k)
      ≤ (Real.pi ^ 2 / 6) * ((2 * k)! : ℝ) * 2 :=
    (div_le_iff₀ h2pos).mp hbound'
  have hsimp : (Real.pi ^ 2 / 6) * ((2 * k)! : ℝ) * 2
      = (Real.pi ^ 2 / 3) * ((2 * k)! : ℝ) := by ring
  rw [hsimp] at hbound''
  -- Divide both sides by (2π)^(2k) > 0.
  exact (le_div_iff₀ h2pi_pow_pos).mpr hbound''

/-! ## Step 6: discharge of the residual -/

/-- **MAIN THEOREM: Discharge of `BernoulliGrowthBoundResidual`.**

    With `M = π²/3` and `N = 1`, the bound
    `|B_{2m}| ≤ M · (2m)! / (2π)^{2m}` holds for all `m ≥ 1`.

    This eliminates the named mathlib gap from the Jonquières
    summability chain. The argument is elementary: Euler's formula
    `ζ(2k) = (-1)^(k+1) · 2^(2k-1) · π^(2k) · B_{2k} / (2k)!`
    combined with `ζ(2k) ≤ ζ(2) = π²/6` for `k ≥ 1`. -/
theorem bernoulliGrowthBoundResidual_proved : BernoulliGrowthBoundResidual := by
  refine ⟨Real.pi ^ 2 / 3, ?_, 1, ?_⟩
  · -- π²/3 ≥ 0
    positivity
  · intro m hm
    have hm1 : 1 ≤ m := hm
    -- Convert from ‖·‖ (Real norm) to |·| (absolute value).
    rw [Real.norm_eq_abs]
    -- The Prop uses `Nat.factorial (2 * m)` (no scoped `!`).
    -- Our explicit theorem uses `(2 * m)!` which unfolds to the same.
    have hbound := bernoulli_growth_bound_explicit hm1
    -- Show definitional equality: (2 * m)! = Nat.factorial (2 * m).
    convert hbound using 2

/-! ## Capstone: chain Bernoulli discharge with the bridge

    Once `BernoulliGrowthBoundResidual` is proved unconditionally,
    `jonquieresZetaSummable_from_residual` reduces to needing ONLY the
    `JonquieresZetaSummableFromBernoulliBridge` (functional-equation
    interpolation), which is a separate analytic content. -/

/-- **Capstone**: under only the bridge Prop, the ζ-series is summable in
    the full convergence region — the Bernoulli growth side is now
    discharged unconditionally. -/
theorem jonquieresZetaSummable_from_bridge_only
    {s z : ℂ}
    (h_bridge : JonquieresZetaSummableFromBernoulliBridge s z)
    (hz : ‖Complex.log z‖ < 2 * Real.pi) :
    jonquieresZetaSummable s z :=
  jonquieresZetaSummable_from_residual h_bridge bernoulliGrowthBoundResidual_proved hz

/-! ## Architecture summary

**This file establishes (axiom-free, no sorry)**:
* `one_div_nat_pow_two_mul_le_sq` — termwise comparison `1/n^(2k) ≤ 1/n^2`.
* `zeta_two_mul_nat_le_zeta_two` — `ζ(2k) ≤ π²/6` for `k ≥ 1` (via tsum comparison).
* `zeta_two_mul_nat_nonneg` — `ζ(2k) ≥ 0` for `k ≥ 1`.
* `sign_bernoulli_two_mul` — `(-1)^(k+1) · B_{2k} ≥ 0` (derived, no axiom).
* `abs_bernoulli_two_mul_eq` — exact rearrangement of Euler's formula.
* `bernoulli_growth_bound_explicit` — `|B_{2k}| ≤ (π²/3) · (2k)!/(2π)^(2k)` for k ≥ 1.
* `bernoulliGrowthBoundResidual_proved` — the named Prop, with M = π²/3, N = 1.
* `jonquieresZetaSummable_from_bridge_only` — chain capstone: only the
  functional-equation bridge remains.

**Residual gap now reduced from TWO to ONE**:
* ~~`BernoulliGrowthBoundResidual`~~ — **DISCHARGED HERE**.
* `JonquieresZetaSummableFromBernoulliBridge` — still open: the
  functional-equation interpolation from Bernoulli growth to `ζ(s - k)`
  for non-integer s. This piece involves Γ/sine factors and is a
  separate multi-page formalization.

**Key elementary insight**: the Bernoulli growth bound is NOT a deep
result requiring radius-of-convergence machinery. Euler's formula for
`ζ(2k)` combined with the trivial bound `ζ(2k) ≤ ζ(2)` already gives a
fully explicit, sharp-up-to-constants bound `|B_{2k}| ≤ (π²/3) · (2k)!/(2π)^{2k}`.
The asymptotic `|B_{2m}| ~ 2 · (2m)!/(2π)^{2m}` is the sharp constant
(this elementary bound has constant `π²/3 ≈ 3.29`, off by factor ~1.65).
-/

end PrincipiaTractalis.Analytic
