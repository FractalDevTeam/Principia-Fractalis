/-
# PF.Analytic.OmegaDerivGeometricBounds_2026_10_18

**Geometric decay bounds for `ω′` and `ω″`** — stage 2 of the Tier-3 first
brick (`codex/TIER3_PREFLIGHT_2026-10-18.md`), the crux of the Route-2
majorant.

For `x ≥ 1`:

  `|ω′(x)| ≤ 2π · exp(−πx)`        `ω″(x) ≤ 4π² · exp(−πx)`

These are the two facts that make an explicit majorant for `F₊″` possible, and
hence make `IntegrableOn (deriv (deriv F_plus)) (Ioi 0)` reachable **without**
the convexity sign lemma (Route 1), whose first-order analogue
`deriv_F_plus_nonpos_on_Ioi` needed the whole `crossTerm` apparatus.

### The mechanism

Each term carries `exp(−π(n+1)²x)`, and the whole difficulty is extracting a
clean `exp(−πx)` from it while the polynomial prefactor `(n+1)^k` is summed
away. For `x ≥ 1`,

  `π(n+1)²x ≥ πx + πn`    (since `(n+1)² ≥ 1 + n` and `x ≥ 1`),

so `exp(−π(n+1)²x) ≤ exp(−πx)·exp(−πn)`, and with the elementary
`(n+1)² ≤ 4ⁿ` and `(n+1)⁴ ≤ 16ⁿ` each series collapses to a **geometric** one
of ratio `4e^{−π} ≤ 4/23` resp. `16e^{−π} ≤ 16/23`:

  `∑ (4/23)ⁿ = 23/19 ≤ 2`        `∑ (16/23)ⁿ = 23/7 ≤ 4`

which is where the constants `2π` and `4π²` come from. Both ratios are `< 1`
only because `e^{−π} ≤ 1/23` — the house constant — so nothing new is assumed.

**Sharpness, for the record:** the true constants are
`∑ m²e^{−π(m²−1)} = 1.00032…` and `∑ m⁴e^{−π(m²−1)} = 1.00129…`, so `2` and `4`
are loose by about 2× and 4×. That is deliberate: the geometric route costs a
few lines and the slack is free, since the majorant only has to be *integrable*.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-18.
-/
import PF.Analytic.OmegaSecondDerivative_2026_10_18
import PF.Analytic.Lambda0TightestBoundsMellin_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace OmegaDerivGeometricBounds20261018

open Real MeasureTheory Set Topology
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaSecondDerivative20261018
open PrincipiaTractalis.Lambda0TightestBoundsMellin20261014

noncomputable section

/-! ## §1 — Elementary polynomial-vs-geometric bounds. -/

/-- `(n+1)² ≤ 4ⁿ` over `ℝ`, by induction. -/
lemma sq_succ_le_four_pow (n : ℕ) : ((n : ℝ) + 1) ^ 2 ≤ 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hstep : (((k : ℝ) + 1) + 1) ^ 2 ≤ 4 * (((k : ℝ) + 1) ^ 2) := by nlinarith [hk]
      have h4 : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by ring
      have : (((k + 1 : ℕ) : ℝ) + 1) ^ 2 = (((k : ℝ) + 1) + 1) ^ 2 := by push_cast; ring
      rw [this, h4]
      nlinarith [ih, hstep]

/-- `(n+1)⁴ ≤ 16ⁿ` over `ℝ`, by induction. -/
lemma pow_four_succ_le_sixteen_pow (n : ℕ) : ((n : ℝ) + 1) ^ 4 ≤ 16 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hbase : ((k : ℝ) + 1) + 1 ≤ 2 * ((k : ℝ) + 1) := by linarith
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1) + 1) hbase 4
      have hstep : (((k : ℝ) + 1) + 1) ^ 4 ≤ 16 * (((k : ℝ) + 1) ^ 4) := by
        calc (((k : ℝ) + 1) + 1) ^ 4 ≤ (2 * ((k : ℝ) + 1)) ^ 4 := hpow
          _ = 16 * (((k : ℝ) + 1) ^ 4) := by ring
      have h16 : (16 : ℝ) ^ (k + 1) = 16 * 16 ^ k := by ring
      have hcast : (((k + 1 : ℕ) : ℝ) + 1) ^ 4 = (((k : ℝ) + 1) + 1) ^ 4 := by push_cast; ring
      rw [hcast, h16]
      nlinarith [ih, hstep]

/-- For `x ≥ 1`, the exponent splits: `πx + πn ≤ π(n+1)²x`. -/
lemma pi_mul_sq_mul_ge {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    π * x + π * (n : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 * x := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq : (0 : ℝ) ≤ (n : ℝ) ^ 2 + 2 * (n : ℝ) := by positivity
  have h1 : (n : ℝ) ^ 2 + 2 * (n : ℝ) ≤ x * ((n : ℝ) ^ 2 + 2 * (n : ℝ)) := by
    nlinarith [hq, hx]
  have h3 : (n : ℝ) ≤ x * ((n : ℝ) ^ 2 + 2 * (n : ℝ)) := by
    nlinarith [h1, hn, sq_nonneg ((n : ℝ))]
  have h2 : ((n : ℝ) + 1) ^ 2 * x = x + x * ((n : ℝ) ^ 2 + 2 * (n : ℝ)) := by ring
  calc π * x + π * (n : ℝ) = π * (x + (n : ℝ)) := by ring
    _ ≤ π * (x + x * ((n : ℝ) ^ 2 + 2 * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hπ.le
        linarith
    _ = π * (((n : ℝ) + 1) ^ 2 * x) := by rw [← h2]
    _ = π * ((n : ℝ) + 1) ^ 2 * x := by ring

/-- `exp(−π) ≤ 1/23`, from the house constant. -/
lemma exp_neg_pi_le_inv_23 : Real.exp (-π) ≤ 1 / 23 :=
  exp_neg_pi_le_one_twentythird

lemma four_exp_neg_pi_lt_one : 4 * Real.exp (-π) < 1 := by
  have h := exp_neg_pi_le_inv_23; nlinarith [h]

lemma sixteen_exp_neg_pi_lt_one : 16 * Real.exp (-π) < 1 := by
  have h := exp_neg_pi_le_inv_23; nlinarith [h]

/-! ## §2 — The `ω′` bound. -/

/-- Termwise bound feeding the geometric series, order 1. -/
lemma omega'_term_le_geom {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
      ≤ π * Real.exp (-π * x) * (4 * Real.exp (-π)) ^ n := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hexp : Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
      ≤ Real.exp (-π * x) * Real.exp (-π * (n : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := pi_mul_sq_mul_ge hx n
    linarith
  have hpoly := sq_succ_le_four_pow n
  have hgeom : (4 * Real.exp (-π)) ^ n = (4 : ℝ) ^ n * Real.exp (-π * (n : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [hgeom]
  have he1 : (0 : ℝ) < Real.exp (-π * x) := Real.exp_pos _
  have he2 : (0 : ℝ) < Real.exp (-π * (n : ℝ)) := Real.exp_pos _
  calc π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
      ≤ π * ((n : ℝ) + 1) ^ 2 * (Real.exp (-π * x) * Real.exp (-π * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ π * (4 : ℝ) ^ n * (Real.exp (-π * x) * Real.exp (-π * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left hpoly hπ.le
    _ = π * Real.exp (-π * x) * ((4 : ℝ) ^ n * Real.exp (-π * (n : ℝ))) := by ring

/-- **★ `|ω′(x)| ≤ 2π·exp(−πx)` for `x ≥ 1` ★** -/
theorem abs_omega'_le {x : ℝ} (hx : 1 ≤ x) :
    |omega' x| ≤ 2 * π * Real.exp (-π * x) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hr0 : (0 : ℝ) ≤ 4 * Real.exp (-π) := by positivity
  have hr1 : 4 * Real.exp (-π) < 1 := four_exp_neg_pi_lt_one
  -- the positive series
  have hsummable_pos : Summable fun n : ℕ =>
      π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := by
    have hδ : (0 : ℝ) < x / 2 := by positivity
    have hlt : x / 2 < x := by linarith
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_omega_term_deriv_bound hδ)
    have h_mono : Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
        ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * (x / 2)) := by
      apply Real.exp_le_exp.mpr
      have hterm_nn : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
      nlinarith [hterm_nn, hlt]
    exact mul_le_mul_of_nonneg_left h_mono (by positivity)
  have hsummable_geom : Summable fun n : ℕ =>
      π * Real.exp (-π * x) * (4 * Real.exp (-π)) ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  -- |omega'| is that positive series
  have hneg : omega' x = -∑' n : ℕ,
      π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := by
    unfold omega'
    rw [← tsum_neg]
    congr 1
    ext n
    ring
  have hpos_nn : (0 : ℝ) ≤ ∑' n : ℕ,
      π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) :=
    tsum_nonneg fun n => by positivity
  rw [hneg, abs_neg, abs_of_nonneg hpos_nn]
  -- compare the two series and evaluate the geometric one
  have hcmp := Summable.tsum_le_tsum (fun n => omega'_term_le_geom hx n) hsummable_pos hsummable_geom
  have heval : (∑' n : ℕ, π * Real.exp (-π * x) * (4 * Real.exp (-π)) ^ n)
      = π * Real.exp (-π * x) * (1 - 4 * Real.exp (-π))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [heval] at hcmp
  have hinv : (1 - 4 * Real.exp (-π))⁻¹ ≤ 2 := by
    have h23 := exp_neg_pi_le_inv_23
    have hden : (0 : ℝ) < 1 - 4 * Real.exp (-π) := by linarith
    rw [inv_le_comm₀ hden (by norm_num : (0:ℝ) < 2)]
    nlinarith [h23, Real.exp_pos (-π)]
  have hpref : (0 : ℝ) ≤ π * Real.exp (-π * x) := by positivity
  nlinarith [hcmp, hinv, hpref]

/-! ## §3 — The `ω″` bound. -/

/-- Termwise bound feeding the geometric series, order 2. -/
lemma omega''_term_le_geom {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
      ≤ π ^ 2 * Real.exp (-π * x) * (16 * Real.exp (-π)) ^ n := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hexp : Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
      ≤ Real.exp (-π * x) * Real.exp (-π * (n : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := pi_mul_sq_mul_ge hx n
    linarith
  have hpoly := pow_four_succ_le_sixteen_pow n
  have hgeom : (16 * Real.exp (-π)) ^ n = (16 : ℝ) ^ n * Real.exp (-π * (n : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [hgeom]
  have hsq : (π * ((n : ℝ) + 1) ^ 2) ^ 2 = π ^ 2 * ((n : ℝ) + 1) ^ 4 := by ring
  rw [hsq]
  calc π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
      ≤ π ^ 2 * ((n : ℝ) + 1) ^ 4 * (Real.exp (-π * x) * Real.exp (-π * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ π ^ 2 * (16 : ℝ) ^ n * (Real.exp (-π * x) * Real.exp (-π * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = π ^ 2 * Real.exp (-π * x) * ((16 : ℝ) ^ n * Real.exp (-π * (n : ℝ))) := by ring

/-- **★ `ω″(x) ≤ 4π²·exp(−πx)` for `x ≥ 1` ★** -/
theorem omega''_le {x : ℝ} (hx : 1 ≤ x) :
    omega'' x ≤ 4 * π ^ 2 * Real.exp (-π * x) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hr0 : (0 : ℝ) ≤ 16 * Real.exp (-π) := by positivity
  have hr1 : 16 * Real.exp (-π) < 1 := sixteen_exp_neg_pi_lt_one
  have hsummable_pos : Summable fun n : ℕ =>
      (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := by
    have hδ : (0 : ℝ) < x / 2 := by positivity
    have hlt : x / 2 < x := by linarith
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_omega'_term_deriv_bound hδ)
    have h_mono : Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
        ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * (x / 2)) := by
      apply Real.exp_le_exp.mpr
      have hterm_nn : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
      nlinarith [hterm_nn, hlt]
    exact mul_le_mul_of_nonneg_left h_mono (by positivity)
  have hsummable_geom : Summable fun n : ℕ =>
      π ^ 2 * Real.exp (-π * x) * (16 * Real.exp (-π)) ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hcmp := Summable.tsum_le_tsum (fun n => omega''_term_le_geom hx n) hsummable_pos hsummable_geom
  have heval : (∑' n : ℕ, π ^ 2 * Real.exp (-π * x) * (16 * Real.exp (-π)) ^ n)
      = π ^ 2 * Real.exp (-π * x) * (1 - 16 * Real.exp (-π))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [heval] at hcmp
  have hinv : (1 - 16 * Real.exp (-π))⁻¹ ≤ 4 := by
    have h23 := exp_neg_pi_le_inv_23
    have hden : (0 : ℝ) < 1 - 16 * Real.exp (-π) := by linarith
    rw [inv_le_comm₀ hden (by norm_num : (0:ℝ) < 4)]
    nlinarith [h23, Real.exp_pos (-π)]
  have hpref : (0 : ℝ) ≤ π ^ 2 * Real.exp (-π * x) := by positivity
  unfold omega''
  nlinarith [hcmp, hinv, hpref]

end

end OmegaDerivGeometricBounds20261018
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.OmegaDerivGeometricBounds20261018.sq_succ_le_four_pow
#print axioms PrincipiaTractalis.OmegaDerivGeometricBounds20261018.pow_four_succ_le_sixteen_pow
#print axioms PrincipiaTractalis.OmegaDerivGeometricBounds20261018.pi_mul_sq_mul_ge
#print axioms PrincipiaTractalis.OmegaDerivGeometricBounds20261018.exp_neg_pi_le_inv_23
#print axioms PrincipiaTractalis.OmegaDerivGeometricBounds20261018.omega'_term_le_geom
#print axioms PrincipiaTractalis.OmegaDerivGeometricBounds20261018.abs_omega'_le
#print axioms PrincipiaTractalis.OmegaDerivGeometricBounds20261018.omega''_term_le_geom
#print axioms PrincipiaTractalis.OmegaDerivGeometricBounds20261018.omega''_le
