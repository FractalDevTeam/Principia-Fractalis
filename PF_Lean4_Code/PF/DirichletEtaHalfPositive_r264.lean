/-
# r264: DIRICHLET ETA AT `s = 1/2` IS POSITIVE.

★ 2026-08-13 r264 — first brick on the Dirichlet-eta path toward
discharging Route B numerical fact (a): `(riemannZeta (1/2 : ℂ)).re < 0`.

Classically, `η(s) = Σ_{n=1}^∞ (-1)^{n+1}/n^s` and
`ζ(s) = η(s) / (1 - 2^{1-s})`. At `s = 1/2`,
`ζ(1/2) = η(1/2) / (1 - √2)`. Since `1 - √2 < 0` and `η(1/2) > 0`,
`ζ(1/2) < 0`. r264 delivers the standalone real positivity
`0 < η(1/2)` as the first brick; downstream bricks connect it to
mathlib's `Complex.riemannZeta`.

## What r264 adds

- `dirichletEtaHalfPartial N : ℝ`:
  `∑ i ∈ Finset.range N, (-1)^i / √(i+1)`
  — the natural indexing that gives `1 - 1/√2 + 1/√3 - 1/√4 + …`.

- `dirichletEtaHalfPartial_tendsto`:
  `∃ l : ℝ, Tendsto dirichletEtaHalfPartial atTop (𝓝 l)`
  via mathlib's `Antitone.tendsto_alternating_series_of_tendsto_zero`
  on the antitone sequence `n ↦ 1/√(n+1)` with limit `0`.

- `dirichletEtaHalf_pos`:
  for every limit point `l` of the partial sums,
  `0 < 1 - 1/√2 ≤ l`. Uses mathlib's
  `Antitone.alternating_series_le_tendsto` at `k = 1`.

## Route B substrate value

r264 is the first algebraic brick on the Dirichlet-eta route to
Route B fact (a). Subsequent bricks connect this positivity to
mathlib's `Complex.riemannZeta` via the identity
`η(s) = (1 - 2^{1-s}) · ζ(s)` — mathlib currently lacks Dirichlet
eta entirely.

## Scope

* NOT novel — Dirichlet eta positivity at `1/2` is elementary
  alternating-series analysis.
* NOT a Millennium discharge.
* IS the first brick on a mathlib-adjacent formalization of Dirichlet
  eta, oriented toward Route B fact (a).

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

open scoped Real

namespace PrincipiaTractalis.DirichletEtaHalfPositive

open Filter Topology Real Finset

/-! ## §1 Definition of the partial-sum function. -/

/-- **`dirichletEtaHalfPartial`** — the `N`-th partial sum of the
alternating Dirichlet eta series at `s = 1/2`:
`∑ i ∈ Finset.range N, (-1)^i / √(i+1)`. Equivalent to
`1 - 1/√2 + 1/√3 - … ± 1/√N`. -/
noncomputable def dirichletEtaHalfPartial (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, (-1)^i / Real.sqrt (i + 1)

/-! ## §2 The reciprocal-sqrt sequence is antitone and tends to zero. -/

/-- **`inv_sqrt_succ_antitone`** — the sequence `n ↦ 1/√(n+1)` is
antitone (nonincreasing). -/
theorem inv_sqrt_succ_antitone :
    Antitone (fun n : ℕ => 1 / Real.sqrt (n + 1)) := by
  intro n m hnm
  simp only [one_div]
  apply inv_anti₀
  · exact Real.sqrt_pos.mpr (by positivity)
  · apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.add_le_add_right hnm 1

/-- **`sqrt_succ_tendsto_atTop`** — `√(n+1) → ∞` as `n → ∞`. -/
theorem sqrt_succ_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.sqrt (n + 1)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  refine ⟨Nat.ceil (M * M) + 1, ?_⟩
  intro n hn
  have h1 : (M * M : ℝ) ≤ (Nat.ceil (M * M) : ℝ) := Nat.le_ceil _
  have h2 : (Nat.ceil (M * M) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have : (Nat.ceil (M * M) + 1 : ℕ) ≤ n := hn
    have hcast : ((Nat.ceil (M * M) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    push_cast at hcast
    linarith
  have h3 : M * M ≤ (n : ℝ) + 1 := by linarith
  have h4 : Real.sqrt (M * M) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt h3
  have h5 : Real.sqrt (M * M) = |M| := by
    rw [show M * M = M^2 by ring, Real.sqrt_sq_eq_abs]
  rw [h5] at h4
  exact le_trans (le_abs_self M) h4

/-- **`inv_sqrt_succ_tendsto_zero`** — `1/√(n+1) → 0` as `n → ∞`.
Via `√(n+1) → ∞` and `Filter.Tendsto.inv_tendsto_atTop`. -/
theorem inv_sqrt_succ_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / Real.sqrt (n + 1)) atTop (𝓝 0) := by
  have h := sqrt_succ_tendsto_atTop.inv_tendsto_atTop
  convert h using 1
  funext n
  simp [one_div]

/-! ## §3 The partial-sum limit exists. -/

/-- Rewrite the partial sum in the alternating-series canonical form
`∑ i, (-1)^i * f i`. -/
private lemma dirichletEtaHalfPartial_eq (N : ℕ) :
    dirichletEtaHalfPartial N =
      ∑ i ∈ Finset.range N, (-1)^i * (1 / Real.sqrt (i + 1)) := by
  unfold dirichletEtaHalfPartial
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **`dirichletEtaHalfPartial_tendsto`** — the partial-sum sequence
of `η(1/2)` converges. -/
theorem dirichletEtaHalfPartial_tendsto :
    ∃ l : ℝ, Tendsto dirichletEtaHalfPartial atTop (𝓝 l) := by
  have h_eq : dirichletEtaHalfPartial =
      fun N => ∑ i ∈ Finset.range N, (-1)^i * (1 / Real.sqrt (i + 1)) := by
    funext N; exact dirichletEtaHalfPartial_eq N
  rw [h_eq]
  exact Antitone.tendsto_alternating_series_of_tendsto_zero
    inv_sqrt_succ_antitone inv_sqrt_succ_tendsto_zero

/-! ## §4 Positivity of the limit. -/

/-- **`sqrt_two_gt_one`** — helper: `1 < √2`. -/
private lemma sqrt_two_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  have h : (1 : ℝ) < 2 := by norm_num
  have : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) h
  rwa [Real.sqrt_one] at this

/-- **`one_minus_inv_sqrt_two_pos`** — helper: `0 < 1 - 1/√2`. -/
private lemma one_minus_inv_sqrt_two_pos : (0 : ℝ) < 1 - 1 / Real.sqrt 2 := by
  have h1 : (1 : ℝ) < Real.sqrt 2 := sqrt_two_gt_one
  have h2 : (1 : ℝ) / Real.sqrt 2 < 1 := by
    rw [div_lt_one (by linarith)]
    exact h1
  linarith

/-- **`dirichletEtaHalf_pos`** — every limit point `l` of the
partial-sum sequence for `η(1/2)` satisfies `0 < l`. -/
theorem dirichletEtaHalf_pos :
    ∀ l : ℝ, Tendsto dirichletEtaHalfPartial atTop (𝓝 l) → 0 < l := by
  intro l hl
  have h_eq : dirichletEtaHalfPartial =
      fun N => ∑ i ∈ Finset.range N, (-1)^i * (1 / Real.sqrt (i + 1)) := by
    funext N; exact dirichletEtaHalfPartial_eq N
  rw [h_eq] at hl
  have h_bound := Antitone.alternating_series_le_tendsto hl
    inv_sqrt_succ_antitone 1
  -- unfold ∑ i in range 2, (-1)^i * (1/√(i+1)) = 1/√1 - 1/√2 = 1 - 1/√2
  have h_sum_eq : ∑ i ∈ Finset.range 2, (-1)^i * (1 / Real.sqrt (i + 1))
      = 1 - 1 / Real.sqrt 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    -- After rw, the goal is:
    -- (-1)^0 * (1/√((0:ℕ)+1)) + (-1)^1 * (1/√((1:ℕ)+1)) = 1 - 1/√2
    have e0 : Real.sqrt (((0 : ℕ) : ℝ) + 1) = 1 := by
      norm_num
    have e1 : Real.sqrt (((1 : ℕ) : ℝ) + 1) = Real.sqrt 2 := by norm_num
    rw [e0, e1]
    ring
  rw [h_sum_eq] at h_bound
  linarith [one_minus_inv_sqrt_two_pos]

/-! ## §5 Axiom check. -/

#print axioms PrincipiaTractalis.DirichletEtaHalfPositive.inv_sqrt_succ_antitone
#print axioms PrincipiaTractalis.DirichletEtaHalfPositive.sqrt_succ_tendsto_atTop
#print axioms PrincipiaTractalis.DirichletEtaHalfPositive.inv_sqrt_succ_tendsto_zero
#print axioms PrincipiaTractalis.DirichletEtaHalfPositive.dirichletEtaHalfPartial_tendsto
#print axioms PrincipiaTractalis.DirichletEtaHalfPositive.dirichletEtaHalf_pos

end PrincipiaTractalis.DirichletEtaHalfPositive
