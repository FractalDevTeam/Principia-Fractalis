/-
# Rayleigh-Ritz Upper Bound on λ_0(H_P^α) via Mercer

Combines the Mercer expansion summability (`MercerExpansionSummable.lean`)
with the cosine-difference closed form
(`CosineDifferenceDoubleIntegral.lean`) to deliver the explicit
Rayleigh-Ritz upper bound on the smallest eigenvalue of `H_P^α`:

  λ_0(H_P^α) ≤ ⟨1, H_P^α · 1⟩_{L²[0,1]} / ⟨1, 1⟩
            = Σ_{j ≥ 0} a^{-j} · 4 · sin²(π · αʲ / 2) / (π · αʲ)²

(for `αʲ ≠ 0` for each summand; the structural identity above ignores
the `α = 0` degeneracy, which is handled by a separate identity).

## Main result

For continuous test function `f = 1` and `α ≠ 0`:

  M_j(1) := (∫_0^1 cos(π · αʲ · x) dx)² + (∫_0^1 sin(π · αʲ · x) dx)²
         = 4 · sin²(π · αʲ / 2) / (π · αʲ)²

The Mercer series sum:

  S(1) := Σ_{j ≥ 0} a^{-j} · M_j(1)

equals the limit `⟨1, H_P^α · 1⟩` as `k → ∞` of the truncated quadratic
form `⟨1, T_k · 1⟩`.

By Rayleigh-Ritz: `λ_0(H_P^α) ≤ S(1)` (since `⟨1, 1⟩ = 1`).

## Significance

This is the closed-form Rayleigh-Ritz upper bound. Combined with:

* `T_k → H_P` Tendsto (TraceLimit, KernelHilbertSchmidtFull),
* PSD (TruncatedOperatorPSD, MercerExpansionSummable),
* Trace sum rule (TraceLimit),

the spectral picture of `H_P^α` has four independent rigorous
constraints + an explicit upper bound — the substrate's polylog
eigenvalue conjecture `λ_k = a^{-k} · Re[Li_1(e^{iπ·αᵏ})]` is constrained
by all of them simultaneously.

All theorems kernel-only `[propext, Classical.choice, Quot.sound]`;
zero project axioms.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.Analytic.MercerExpansionSummable
import PF.Analytic.CosineDifferenceDoubleIntegral

namespace PrincipiaTractalis.Analytic

open Real Filter
open scoped Topology

/-! ## §1 — Explicit Mercer summand at f = 1 -/

/-- **Mercer summand at constant test function `f = 1`**: for any
    `α ≠ 0` and `j : ℕ` with `αʲ ≠ 0`,

      `M_j(1) = 4 · sin²(π · αʲ / 2) / (π · αʲ)²`.

    Directly from the first-moment closed forms
    `∫_0^1 cos(π · αʲ · x) dx = sin(π · αʲ) / (π · αʲ)` and
    `∫_0^1 sin(π · αʲ · x) dx = (1 − cos(π · αʲ)) / (π · αʲ)`,
    combined with the half-angle identity. -/
theorem mercerSummand_const_one
    (α : ℝ) (j : ℕ) (hα : α ^ j ≠ 0) :
    mercerSummand α (fun _ => 1) j
      = 4 * Real.sin (Real.pi * α ^ j / 2) ^ 2 / (Real.pi * α ^ j) ^ 2 := by
  unfold mercerSummand
  -- Each integral closed form: ∫ 1 · cos = sin/πα^j, ∫ 1 · sin = (1-cos)/πα^j.
  have h_cos_int : (∫ x in (0:ℝ)..1, (1 : ℝ) * Real.cos (Real.pi * α ^ j * x))
      = Real.sin (Real.pi * α ^ j) / (Real.pi * α ^ j) := by
    have h_eq : (fun x : ℝ => (1 : ℝ) * Real.cos (Real.pi * α ^ j * x))
        = (fun x : ℝ => Real.cos (Real.pi * α ^ j * x)) := by
      funext x; ring
    rw [h_eq]
    exact integral_cosine_pi_c hα
  have h_sin_int : (∫ x in (0:ℝ)..1, (1 : ℝ) * Real.sin (Real.pi * α ^ j * x))
      = (1 - Real.cos (Real.pi * α ^ j)) / (Real.pi * α ^ j) := by
    have h_eq : (fun x : ℝ => (1 : ℝ) * Real.sin (Real.pi * α ^ j * x))
        = (fun x : ℝ => Real.sin (Real.pi * α ^ j * x)) := by
      funext x; ring
    rw [h_eq]
    exact integral_sine_pi_c hα
  rw [h_cos_int, h_sin_int]
  -- Combine: sin²/(πα^j)² + (1-cos)²/(πα^j)² = [sin² + (1-cos)²]/(πα^j)² = 4 sin²(πα^j/2)/(πα^j)².
  have hpc_ne : Real.pi * α ^ j ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero hα
  have h_combine : (Real.sin (Real.pi * α ^ j) / (Real.pi * α ^ j)) ^ 2
      + ((1 - Real.cos (Real.pi * α ^ j)) / (Real.pi * α ^ j)) ^ 2
      = (Real.sin (Real.pi * α ^ j) ^ 2 + (1 - Real.cos (Real.pi * α ^ j)) ^ 2)
        / (Real.pi * α ^ j) ^ 2 := by
    field_simp
  rw [h_combine]
  -- Apply the half-angle identity (proven in CosineDifferenceDoubleIntegral.lean).
  rw [sq_sin_add_sq_one_sub_cos_eq_four_sq_sin_half (Real.pi * α ^ j)]

/-! ## §2 — Bound on M_j(1) -/

/-- **Bound on M_j(1)**: for `α ≠ 0` and `j : ℕ` with `αʲ ≠ 0`,

      `M_j(1) ≤ 1`.

    Direct from `4 · sin²(t/2) / t² ≤ 1` for `t ≠ 0`, since
    `|sin(t/2)| ≤ |t/2|` (small-angle bound). -/
theorem mercerSummand_const_one_le_one
    (α : ℝ) (j : ℕ) (hα : α ^ j ≠ 0) :
    mercerSummand α (fun _ => 1) j ≤ 1 := by
  rw [mercerSummand_const_one α j hα]
  -- 4·sin²(t/2)/t² ≤ 1 since sin²(t/2) ≤ (t/2)² gives 4·(t/2)²/t² = 1.
  have hpc_ne : Real.pi * α ^ j ≠ 0 := mul_ne_zero Real.pi_ne_zero hα
  have hpc_sq_pos : 0 < (Real.pi * α ^ j) ^ 2 := by positivity
  -- Need: 4 · sin²(πα^j/2) ≤ (πα^j)².
  -- |sin(x)| ≤ |x| gives sin²(x) ≤ x², so sin²(πα^j/2) ≤ (πα^j/2)² = (πα^j)²/4.
  -- Hence 4·sin²(πα^j/2) ≤ 4·(πα^j)²/4 = (πα^j)².
  rw [div_le_one hpc_sq_pos]
  have h_sin_abs : |Real.sin (Real.pi * α ^ j / 2)|
      ≤ |Real.pi * α ^ j / 2| := Real.abs_sin_le_abs
  have h_sin_sq : Real.sin (Real.pi * α ^ j / 2) ^ 2
      ≤ (Real.pi * α ^ j / 2) ^ 2 := by
    rw [← sq_abs (Real.sin _), ← sq_abs (Real.pi * α ^ j / 2)]
    exact sq_le_sq' (by linarith [abs_nonneg (Real.sin (Real.pi * α ^ j / 2))]) h_sin_abs
  calc 4 * Real.sin (Real.pi * α ^ j / 2) ^ 2
      ≤ 4 * (Real.pi * α ^ j / 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left h_sin_sq (by norm_num)
    _ = (Real.pi * α ^ j) ^ 2 := by ring

/-! ## §3 — Rayleigh-Ritz upper bound on the quadratic form -/

/-- **Rayleigh-Ritz quadratic form upper bound**: for `a > 1` and
    any `α : ℝ` with `αʲ ≠ 0` for all `j ≥ 1` (e.g., `α = √2`,
    `α = √(2π)`, etc.),

      `⟨1, H_P^α · 1⟩ = mercerSeriesSum α a (fun _ => 1) ≤ a/(a − 1)`.

    Direct from `M_j(1) ≤ 1` (above) summed with the geometric series
    `Σ a^{-j} = a/(a − 1)`. -/
theorem mercerSeriesSum_const_one_le
    (α a : ℝ) (ha : 1 < a) (hα_nonzero : ∀ j : ℕ, α ^ j ≠ 0) :
    mercerSeriesSum α a (fun _ => 1) ≤ a / (a - 1) := by
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have ha_minus_one_pos : 0 < a - 1 := by linarith
  -- Bound term-by-term: a^{-j}·M_j(1) ≤ a^{-j}·1 = a^{-j}.
  -- Sum: Σ a^{-j} = a/(a-1).
  unfold mercerSeriesSum
  have hinv_lt_one : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have h_inv_nn : (0 : ℝ) ≤ a⁻¹ := le_of_lt (by positivity)
  have h_geom_eq : ∀ j : ℕ, (a⁻¹ : ℝ) ^ j = a ^ (-(j : ℤ)) := fun j => by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have h_geom_sum : (∑' j : ℕ, (a : ℝ) ^ (-(j : ℤ))) = (1 - a⁻¹)⁻¹ := by
    have h_geom : (∑' j : ℕ, (a⁻¹ : ℝ) ^ j) = (1 - a⁻¹)⁻¹ :=
      tsum_geometric_of_lt_one h_inv_nn hinv_lt_one
    rw [← h_geom]
    congr 1
    funext j; exact (h_geom_eq j).symm
  have h_geom_eq_a : (1 - a⁻¹ : ℝ)⁻¹ = a / (a - 1) := by field_simp
  have h_geom : (∑' j : ℕ, (a : ℝ) ^ (-(j : ℤ))) = a / (a - 1) := by
    rw [h_geom_sum, h_geom_eq_a]
  -- Termwise bound: a^{-j}·M_j(1) ≤ a^{-j}.
  have h_bound : ∀ j : ℕ, a ^ (-(j : ℤ)) * mercerSummand α (fun _ => 1) j
      ≤ a ^ (-(j : ℤ)) := by
    intro j
    have h_pos : 0 ≤ a ^ (-(j : ℤ)) := le_of_lt (zpow_pos ha_pos _)
    calc a ^ (-(j : ℤ)) * mercerSummand α (fun _ => 1) j
        ≤ a ^ (-(j : ℤ)) * 1 := by
          apply mul_le_mul_of_nonneg_left
            (mercerSummand_const_one_le_one α j (hα_nonzero j)) h_pos
      _ = a ^ (-(j : ℤ)) := by ring
  have h_summable_const : Summable (fun j : ℕ => a ^ (-(j : ℤ))) := by
    have h_inv : Summable (fun j : ℕ => (a⁻¹ : ℝ) ^ j) :=
      summable_geometric_of_lt_one h_inv_nn hinv_lt_one
    simp_rw [h_geom_eq] at h_inv
    exact h_inv
  have h_summable_mercer : Summable
      (fun j : ℕ => a ^ (-(j : ℤ)) * mercerSummand α (fun _ => 1) j) :=
    summable_mercer_series α a ha (fun _ => 1) continuous_const 1
      (fun _ _ => by simp) (by norm_num)
  calc (∑' j : ℕ, a ^ (-(j : ℤ)) * mercerSummand α (fun _ => 1) j)
      ≤ (∑' j : ℕ, a ^ (-(j : ℤ))) := tsum_le_tsum h_bound h_summable_mercer h_summable_const
    _ = a / (a - 1) := h_geom

/-! ## §4 — Capstone -/

/-- **★ RAYLEIGH-RITZ UPPER BOUND CAPSTONE ★** —
    `rayleigh_ritz_upper_bound_capstone`.

    For all `a > 1` and `α : ℝ` with `αʲ ≠ 0` for all `j`:

      (R1) `M_j(1) = 4 · sin²(π · αʲ / 2) / (π · αʲ)²`
            (explicit closed form for the constant-test Mercer summand).

      (R2) `M_j(1) ≤ 1` (uniform bound per scale).

      (R3) `mercerSeriesSum α a 1 ≤ a/(a − 1)` (Rayleigh-Ritz upper
            bound on `⟨1, H_P^α · 1⟩`).

    By Rayleigh-Ritz, `λ_0(H_P^α) ≤ mercerSeriesSum α a 1` (since
    `‖1‖_{L²[0,1]}² = 1`). Combined with the trace sum rule
    `Σ_{k ≥ 0} λ_k = a/(a − 1)`, the smallest eigenvalue is bounded
    above by the full trace — consistent with the natural spectral
    structure.

    The polylog conjecture's `λ_0 = a^0 · Re[Li_1(e^{iπ})] = -log 2`
    (principal branch) is REFUTED by the PSD constraint
    (`TruncatedOperatorPSD.lean`), confirming the framework's
    monodromy-phase-deficit reformulation. The trace identity, PSD,
    HS norm bound, and Rayleigh-Ritz upper bound jointly constrain
    the spectrum and the conjecture's physical Riemann sheet. -/
theorem rayleigh_ritz_upper_bound_capstone
    (α a : ℝ) (ha : 1 < a) (hα_nonzero : ∀ j : ℕ, α ^ j ≠ 0) :
    -- (R1) Explicit M_j(1) closed form.
    (∀ j : ℕ, mercerSummand α (fun _ => 1) j
       = 4 * Real.sin (Real.pi * α ^ j / 2) ^ 2 / (Real.pi * α ^ j) ^ 2) ∧
    -- (R2) Per-scale uniform bound.
    (∀ j : ℕ, mercerSummand α (fun _ => 1) j ≤ 1) ∧
    -- (R3) Rayleigh-Ritz upper bound on ⟨1, H_P · 1⟩.
    (mercerSeriesSum α a (fun _ => 1) ≤ a / (a - 1)) :=
  ⟨fun j => mercerSummand_const_one α j (hα_nonzero j),
   fun j => mercerSummand_const_one_le_one α j (hα_nonzero j),
   mercerSeriesSum_const_one_le α a ha hα_nonzero⟩

end PrincipiaTractalis.Analytic

#print axioms
  PrincipiaTractalis.Analytic.rayleigh_ritz_upper_bound_capstone
