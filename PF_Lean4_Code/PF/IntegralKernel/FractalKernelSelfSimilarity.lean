/-
# Fractal Kernel Self-Similarity Identity

The fractal kernel `V_α(x, y) = Σ a^(-n) cos(π · α^n · d(x,y))` from Ch 21
Definition 4.2 has a structural SELF-SIMILARITY under rescaling the
distance argument by `α`:

  **K_α(t/α) = (1/a) · K_α(t) + cos(π·t/α)**

where `K_α(t) := Σ_{n=0}^∞ a^(-n) cos(πα^n t)` is the kernel viewed
as a function of the scalar distance `t`.

## Why this matters for the polylog conjecture

The framework's load-bearing conjecture is `λ_0(H_α) = π/(10·α)` — the
ground-state eigenvalue is INVERSELY PROPORTIONAL to α. For that to be
a theorem about the operator family, the operator must have a structural
property that *forces* this 1/α dependence. The self-similarity identity
above IS that structure:

  * When we rescale distances by `1/α` (i.e., `t → t/α`), the kernel
    contracts by `1/a` AND picks up a residual `cos(π·t/α)` term.
  * The 1/α frequency scaling on the residual is exactly what drives
    the ground-state eigenvalue to scale as 1/α.

This file is the FIRST STEP in attacking `PolylogEigenvalueConjecture`
from first principles: rather than treating the closed form as
opaque, derive it from the structural self-similarity of H_α.

## Status

Axiom-free at the Lean level. Strictly algebraic — uses only the
geometric-series convergence (already proved in `FractalKernel.lean`)
and the index-shift identity for absolutely summable series.

Stage L4 — operator self-similarity infrastructure.
-/

import PF.IntegralKernel.FractalKernel

namespace PrincipiaTractalis.IntegralKernel

open Real

/-! ## Distance-only form of the fractal kernel -/

/-- The fractal kernel summand at depth `n` as a pure function of the
    distance argument `t : ℝ`. Equal to `fractalKernelTerm α a z n` whenever
    `t = dist z.1 z.2`. -/
noncomputable def fractalKernelDistTerm (α a : ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  a ^ (-(n : ℤ)) * Real.cos (Real.pi * α ^ n * t)

/-- The fractal kernel as a function of the scalar distance `t`. -/
noncomputable def fractalKernelDist (α a : ℝ) (t : ℝ) : ℝ :=
  ∑' n, fractalKernelDistTerm α a t n

/-! ## Bridge to the (K × K)-valued kernel -/

/-- Termwise: the (K×K)-valued summand factors through the distance. -/
theorem fractalKernelTerm_eq_fractalKernelDistTerm
    {K : Type*} [PseudoMetricSpace K] (α a : ℝ) (z : K × K) (n : ℕ) :
    fractalKernelTerm α a z n =
      fractalKernelDistTerm α a (dist z.1 z.2) n := by
  unfold fractalKernelTerm fractalKernelDistTerm
  rfl

/-- Total: the (K×K)-valued real kernel factors through the distance. -/
theorem fractalKernelReal_eq_fractalKernelDist
    {K : Type*} [PseudoMetricSpace K] (α a : ℝ) (z : K × K) :
    fractalKernelReal α a z = fractalKernelDist α a (dist z.1 z.2) := by
  unfold fractalKernelReal fractalKernelDist
  exact tsum_congr (fun n => fractalKernelTerm_eq_fractalKernelDistTerm α a z n)

/-! ## Summability of the distance-only form -/

/-- Termwise bound: `|fractalKernelDistTerm α a t n| ≤ (1/a)^n` when `a > 0`. -/
theorem abs_fractalKernelDistTerm_le (α : ℝ) {a : ℝ} (ha : 0 < a) (t : ℝ)
    (n : ℕ) :
    |fractalKernelDistTerm α a t n| ≤ (1 / a) ^ n := by
  unfold fractalKernelDistTerm
  have h_pow_pos : (0 : ℝ) < a ^ (-(n : ℤ)) := zpow_pos ha _
  rw [abs_mul, abs_of_pos h_pow_pos]
  calc a ^ (-(n : ℤ)) * |Real.cos (Real.pi * α ^ n * t)|
      ≤ a ^ (-(n : ℤ)) * 1 := by
        apply mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) h_pow_pos.le
    _ = a ^ (-(n : ℤ)) := mul_one _
    _ = (1 / a) ^ n := by
        rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- Summability of the distance-form summands. -/
theorem summable_fractalKernelDistTerm (α : ℝ) {a : ℝ} (ha : 1 < a) (t : ℝ) :
    Summable (fractalKernelDistTerm α a t) := by
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have h_inv_lt_one : 1 / a < 1 := (div_lt_one ha_pos).mpr ha
  have h_inv_nn : 0 ≤ 1 / a := div_nonneg zero_le_one ha_pos.le
  apply Summable.of_norm_bounded (g := fun n => (1 / a) ^ n)
  · exact summable_geometric_of_lt_one h_inv_nn h_inv_lt_one
  · intro n
    exact abs_fractalKernelDistTerm_le α ha_pos t n

/-! ## The self-similarity identity

The substantive content: shifting the distance by `1/α` rearranges the
series so that all terms shift down one in index, exposing a single
"residual" term and an attenuated copy of the original. -/

/-- **Index-shift identity** (the key intermediate step). For any `α > 0`
    and `t : ℝ` and `n : ℕ`:

      `fractalKernelDistTerm α a (t/α) (n+1) = (1/a) · fractalKernelDistTerm α a t n`.

    Because: `a^(-(n+1)) · cos(π·α^(n+1)·t/α) = (1/a)·a^(-n)·cos(π·α^n·t)`. -/
theorem fractalKernelDistTerm_succ_at_scaled
    {α a : ℝ} (hα : α ≠ 0) (ha : a ≠ 0) (t : ℝ) (n : ℕ) :
    fractalKernelDistTerm α a (t/α) (n+1) =
      (1/a) * fractalKernelDistTerm α a t n := by
  unfold fractalKernelDistTerm
  -- LHS: a^(-(n+1)) · cos(π · α^(n+1) · (t/α))
  -- RHS: (1/a) · a^(-n) · cos(π · α^n · t)
  have h_pow_succ : α ^ (n + 1) * (t / α) = α ^ n * t := by
    rw [pow_succ]
    field_simp
  have h_pi_arg :
      Real.pi * α ^ (n + 1) * (t / α) = Real.pi * α ^ n * t := by
    calc Real.pi * α ^ (n + 1) * (t / α)
        = Real.pi * (α ^ (n + 1) * (t / α)) := by ring
      _ = Real.pi * (α ^ n * t) := by rw [h_pow_succ]
      _ = Real.pi * α ^ n * t := by ring
  rw [h_pi_arg]
  -- Now: a^(-(n+1)) · cos(...) = (1/a) · a^(-n) · cos(...)
  -- Reduces to a^(-(n+1)) = (1/a) · a^(-n)
  have h_a_pow :
      (a : ℝ) ^ (-((n+1 : ℕ) : ℤ)) = (1/a) * a ^ (-(n : ℤ)) := by
    push_cast
    rw [show -((n : ℤ) + 1) = (-(n : ℤ)) + (-1) from by ring]
    rw [zpow_add₀ ha, zpow_neg_one, one_div]
    ring
  rw [h_a_pow]
  ring

/-- **THE FRACTAL KERNEL SELF-SIMILARITY IDENTITY**

      `K_α(t/α) = (1/a) · K_α(t) + cos(π·t/α)`

    where `K_α(t) = Σ_{n=0}^∞ a^(-n) cos(πα^n t)` is the kernel viewed
    as a function of scalar distance.

    Proof: split off the `n=0` term on the LHS (which is exactly the
    residual `cos(π·t/α)`), then apply the index-shift identity to
    rewrite `Σ_{n≥1} ...(t/α)... = (1/a)·Σ_{m≥0} ...(t)...`.

    This is the structural identity that explains why the conjectured
    closed form `λ_0(H_α) = π/(10·α)` is inversely proportional to `α`:
    rescaling distance by `1/α` contracts the kernel by `1/a` plus a
    residual at frequency `π/α`. -/
theorem fractalKernelDist_self_similar
    {α a : ℝ} (hα : α ≠ 0) (ha : 1 < a) (t : ℝ) :
    fractalKernelDist α a (t / α) =
      (1 / a) * fractalKernelDist α a t + Real.cos (Real.pi * t / α) := by
  unfold fractalKernelDist
  -- Split the LHS tsum over Nat into (n=0) + (n=k+1 for k≥0).
  have h_sum_lhs : Summable (fractalKernelDistTerm α a (t / α)) :=
    summable_fractalKernelDistTerm α ha (t / α)
  have h_sum_rhs : Summable (fractalKernelDistTerm α a t) :=
    summable_fractalKernelDistTerm α ha t
  -- tsum split: ∑' n, f n = f 0 + ∑' n, f (n+1)
  rw [Summable.tsum_eq_zero_add h_sum_lhs]
  -- Now: f 0 + ∑' k, f (k+1) = (1/a)·tsum + cos(π·t/α)
  -- f 0 = a^0 · cos(π·α^0·(t/α)) = 1 · cos(π·t/α) = cos(π·t/α)
  have h_term_zero :
      fractalKernelDistTerm α a (t / α) 0 = Real.cos (Real.pi * t / α) := by
    unfold fractalKernelDistTerm
    simp
    congr 1
    ring
  rw [h_term_zero]
  -- ∑' k, fractalKernelDistTerm α a (t/α) (k+1) = (1/a) · ∑' n, fractalKernelDistTerm α a t n
  -- By the index-shift identity, each term shifts: (k+1)-th term at t/α equals (1/a) times k-th term at t.
  have h_shift_tsum :
      ∑' k : ℕ, fractalKernelDistTerm α a (t / α) (k + 1) =
        (1 / a) * ∑' n : ℕ, fractalKernelDistTerm α a t n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    have ha_ne : a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
    exact fractalKernelDistTerm_succ_at_scaled hα ha_ne t k
  rw [h_shift_tsum]
  ring

/-! ## Application: kernel on (K × K) under rescaling

For a normed space `K` where scaling is defined, the (K × K)-valued
kernel inherits self-similarity. We don't formalize this here at full
generality, but the distance-form theorem above is the key analytic
content. -/

/-- **Specialization at α = √2 (the P-class value).** The self-similarity
    identity at the manuscript's canonical α value, ready to be combined
    with the truncated generating function content to constrain
    eigenvalues. -/
theorem fractalKernelDist_self_similar_at_sqrt_two
    {a : ℝ} (ha : 1 < a) (t : ℝ) :
    fractalKernelDist (Real.sqrt 2) a (t / Real.sqrt 2) =
      (1 / a) * fractalKernelDist (Real.sqrt 2) a t +
        Real.cos (Real.pi * t / Real.sqrt 2) := by
  have hα : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))
  exact fractalKernelDist_self_similar hα ha t

end PrincipiaTractalis.IntegralKernel
