/-
# r276: DIRICHLET ETA — CONDITIONAL CONVERGENCE ON THE REAL AXIS (0, ∞).

★ 2026-08-16 r276 — attacks the r275 refined-residual chain by
formalising ingredient (2) of the r271 Dirichlet 1858 residual on
the REAL AXIS. Delivers `CauchySeq` of the complex LSeries partial
sums for the alternating Dirichlet eta at every complex `s = (σ : ℂ)`
with `σ : ℝ` and `0 < σ`.

## The r275 four-ingredient design

Per r275's docstring, full Dirichlet 1858 identity requires:

1. Abel's theorem on real power series (r275 — done).
2. Abscissa of *conditional* convergence for η on `0 < re s`.
3. `Differentiable ℂ` analytic continuation of η to `0 < re s`.
4. Identity theorem matching that continuation with `(1 − 2^(1−s)) · ζ(s)`.

r276 attacks ingredient (2) on the **real ray** `{s : ℂ | Im s = 0 ∧ 0 < Re s}`.
Mathlib's antitone Dirichlet test
`Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` applies
directly to the real reciprocal-power sequence `n ↦ 1/(n+1)^σ` and
the bounded-partial-sums alternator `n ↦ (-1)^n`.

The GENERAL complex extension (`s : ℂ` with `Im s ≠ 0` and `0 < Re s`)
requires a Dirichlet-test variant for complex-valued twisting factors
`1/(n+1)^(it)` and is named as a strictly-smaller REFINED residual
`DirichletEta_ConditionalConvergence_ComplexOffReal`.

## What r276 adds

Real infrastructure:

- `inv_natCast_add_one_rpow_antitone {σ : ℝ} (hσ : 0 < σ)`:
  `Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ σ)`.

- `inv_natCast_add_one_rpow_tendsto_zero {σ : ℝ} (hσ : 0 < σ)`:
  `Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ σ) atTop (𝓝 0)`.

- `dirichletEta_real_partial_cauchy {σ : ℝ} (hσ : 0 < σ)`:
  **UNCONDITIONAL.** `CauchySeq` of the REAL alternating partial sums
  `∑ i ∈ Finset.range N, (-1)^i · (1 / ((i : ℝ) + 1)^σ)`.
  Via mathlib's antitone Dirichlet test.

LSeries bridge:

- `lseries_partialSum_succ_eq_real_cast {σ : ℝ} (hσ : 0 < σ) (N : ℕ)`:
  `∑ n ∈ range (N+1), LSeries.term dirichletEtaCoeff (σ : ℂ) n
    = (((∑ i ∈ range N, (-1)^i / ((i : ℝ) + 1)^σ) : ℝ) : ℂ)`.
  Off-by-one index alignment (the LSeries term at `n = 0` vanishes).

- `dirichletEta_lseries_partial_cauchy_real {σ : ℝ} (hσ : 0 < σ)`:
  **UNCONDITIONAL.** `CauchySeq` of the complex LSeries partial sums
  `fun N => ∑ n ∈ range N, LSeries.term dirichletEtaCoeff (σ : ℂ) n`.

Named residual (refined named published-mathematics claim):

- `DirichletEta_ConditionalConvergence_ComplexOffReal : Prop` —
  the analogous CauchySeq statement for every `s : ℂ` with
  `Im s ≠ 0 ∧ 0 < Re s`. Classical result of Dirichlet 1858 on the
  general abscissa of conditional convergence for alternating
  Dirichlet series; requires a complex-valued Dirichlet-test variant
  outside mathlib's current infrastructure.

- `dirichletEta_lseries_partial_cauchy_via_named
      (h_off : DirichletEta_ConditionalConvergence_ComplexOffReal)
      {s : ℂ} (hs : 0 < s.re) : CauchySeq (…)` —
  composes the real case (r276) with the refined complex-off-real
  residual to conclude the FULL abscissa of conditional convergence
  on `0 < re s`.

## Net residual movement

Before r276:
- Ingredient (2) was bundled entirely inside r275's refined residual
  `Dirichlet1858_PowerSeriesLimit_EqualsProductForm` (or, more
  strictly, in the ingredient list of r271's design analysis).

After r276:
- The REAL AXIS portion of ingredient (2) is UNCONDITIONAL Lean.
- The remaining complex-off-real portion is a strictly-smaller,
  precisely-stated refined residual
  `DirichletEta_ConditionalConvergence_ComplexOffReal`.

At `s = 1/2` — the specific point required by r271 — the residual
is fully discharged (real axis case); this is a strict generalization
of r265's antitone Leibniz argument, which handled only `s = 1/2` via
`Real.sqrt`. r276 lifts the same argument to every real `σ > 0`.

## Framework-first position

Route B's mathlib-native front on RH remains conditional on the r275
refined residual (which concerns a specific power-series boundary
identity, not conditional convergence per se). r276 tightens the
CLASSICAL-INGREDIENT layer: the abscissa result — one of four historical
Dirichlet 1858 ingredients — is now formal on the real ray, with the
complex-off-real portion named as a strictly-smaller residual.

## Scope

* NOT novel — direct application of mathlib's antitone Dirichlet test
  + cast bridge to the complex LSeries.
* NOT a Millennium discharge.
* IS a genuine formal step on ingredient (2) of the Dirichlet 1858
  residual, together with a strictly-smaller named residual for the
  complex-off-real extension.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True` in the
UNCONDITIONAL theorems (the `DirichletEta_ConditionalConvergence_ComplexOffReal`
Prop is a genuine, precisely-stated named-published-mathematics residual).
Kernel-only.
-/

import PF.DirichletEtaComplex_r267
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open Filter Topology Finset

namespace PrincipiaTractalis.DirichletEtaConditionalConvergenceReal

open PrincipiaTractalis.DirichletEtaComplex

/-! ## §1 Real antitone + tends-to-zero for `n ↦ 1/(n+1)^σ`. -/

/-- **`inv_natCast_add_one_rpow_antitone`** — the real sequence
`n ↦ 1/(n+1)^σ` is antitone for `σ > 0`. -/
theorem inv_natCast_add_one_rpow_antitone {σ : ℝ} (hσ : 0 < σ) :
    Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ σ) := by
  intro n m hnm
  simp only [one_div]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  apply inv_anti₀
  · exact Real.rpow_pos_of_pos hn σ
  · apply Real.rpow_le_rpow hn.le _ hσ.le
    exact_mod_cast Nat.add_le_add_right hnm 1

/-- **`inv_natCast_add_one_rpow_tendsto_zero`** — the real sequence
`1/(n+1)^σ → 0` as `n → ∞`, for `σ > 0`. -/
theorem inv_natCast_add_one_rpow_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ σ) atTop (𝓝 0) := by
  -- Compose: (n : ℕ) ↦ ((n : ℝ) + 1) ↦ ((n : ℝ) + 1)^σ ↦ 1/((n : ℝ) + 1)^σ.
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ σ) atTop atTop :=
    (tendsto_rpow_atTop hσ).comp h1
  have h3 : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ σ)⁻¹) atTop (𝓝 0) :=
    h2.inv_tendsto_atTop
  simpa [one_div] using h3

/-! ## §2 Real Cauchy convergence of the alternating partial sums. -/

/-- **`dirichletEta_real_partial_cauchy`** — UNCONDITIONAL. The real
alternating partial sums `∑ i ∈ range N, (-1)^i · (1 / (i+1)^σ)` form
a Cauchy sequence for every `σ > 0`.

Direct application of mathlib's
`Antitone.cauchySeq_alternating_series_of_tendsto_zero`. -/
theorem dirichletEta_real_partial_cauchy {σ : ℝ} (hσ : 0 < σ) :
    CauchySeq
      (fun N : ℕ =>
        ∑ i ∈ Finset.range N, (-1 : ℝ)^i * (1 / ((i : ℝ) + 1) ^ σ)) :=
  (inv_natCast_add_one_rpow_antitone hσ).cauchySeq_alternating_series_of_tendsto_zero
    (inv_natCast_add_one_rpow_tendsto_zero hσ)

/-! ## §3 LSeries-term evaluation at a real `s`. -/

/-- Evaluate `LSeries.term dirichletEtaCoeff (σ : ℂ) n` at `n = k + 1`
(i.e., strictly positive index) as a cast from `ℝ`. -/
private lemma lseries_term_succ_eq_real_cast {σ : ℝ} (k : ℕ) :
    LSeries.term dirichletEtaCoeff ((σ : ℝ) : ℂ) (k + 1)
      = ((((-1 : ℝ)^k * (1 / ((k : ℝ) + 1) ^ σ) : ℝ)) : ℂ) := by
  have hk : (k + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero k
  rw [LSeries.term_of_ne_zero hk]
  unfold dirichletEtaCoeff
  rw [if_neg hk]
  -- LHS: (-1 : ℂ)^((k+1)+1) / ((k+1 : ℕ) : ℂ)^((σ : ℝ) : ℂ)
  -- Step 1: (-1)^((k+1)+1) = (-1)^k (as complex, via period-2).
  have hpow : ((-1 : ℂ))^((k + 1) + 1) = ((((-1 : ℝ)^k : ℝ)) : ℂ) := by
    have h1 : ((-1 : ℂ))^((k + 1) + 1) = ((-1 : ℂ))^k * ((-1 : ℂ))^2 := by
      ring
    have h2 : ((-1 : ℂ))^2 = 1 := by norm_num
    rw [h1, h2, mul_one]
    push_cast
    ring
  rw [hpow]
  -- Step 2: convert ((k+1 : ℕ) : ℂ)^((σ : ℝ) : ℂ) into a real cast.
  have hk1R : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have hkC : ((k + 1 : ℕ) : ℂ) ^ ((σ : ℝ) : ℂ)
      = ((((k + 1 : ℕ) : ℝ) ^ σ : ℝ) : ℂ) := by
    have : (((k + 1 : ℕ) : ℝ) : ℂ) ^ ((σ : ℝ) : ℂ)
        = ((((k + 1 : ℕ) : ℝ) ^ σ : ℝ) : ℂ) :=
      (Complex.ofReal_cpow hk1R σ).symm
    have hcast : ((k + 1 : ℕ) : ℂ) = (((k + 1 : ℕ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast]; exact this
  rw [hkC]
  push_cast
  ring

/-! ## §4 LSeries partial sum equals cast of real alternating sum
    (with an off-by-one index shift). -/

/-- **`lseries_partialSum_succ_eq_real_cast`** — the LSeries partial
sum at real `s = (σ : ℂ)` over indices `range (N + 1)` equals the
cast of the real alternating partial sum over indices `range N`.

The off-by-one shift is because the LSeries term at `n = 0` vanishes,
while the real alternating series starts at `i = 0` with a nonzero
value `1/1^σ`. -/
theorem lseries_partialSum_succ_eq_real_cast {σ : ℝ} (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
        LSeries.term dirichletEtaCoeff ((σ : ℝ) : ℂ) n
      = (((∑ i ∈ Finset.range N,
              (-1 : ℝ)^i * (1 / ((i : ℝ) + 1) ^ σ)) : ℝ) : ℂ) := by
  induction N with
  | zero =>
    -- LHS = LSeries.term ... 0 = 0. RHS = cast of empty sum = 0.
    simp [LSeries.term]
  | succ N ih =>
    -- LHS = (sum over range (N+1)) + LSeries.term ... (N+1)
    -- RHS = cast of (sum over range N + (-1)^N * (1/(N+1)^σ))
    rw [Finset.sum_range_succ (n := N + 1),
        Finset.sum_range_succ (f := fun i => (-1 : ℝ)^i * (1 / ((i : ℝ) + 1) ^ σ))
                              (n := N),
        ih]
    -- Goal: cast(sum) + LSeries.term ... (N+1) = cast(sum + (-1)^N * (1/(N+1)^σ))
    rw [lseries_term_succ_eq_real_cast N]
    push_cast
    ring

/-! ## §5 Complex LSeries CauchySeq via cast + shift. -/

/-- **`dirichletEta_lseries_partial_cauchy_real`** — UNCONDITIONAL.
`CauchySeq` of the complex LSeries partial sums for `dirichletEta`
at every real `s = (σ : ℂ)` with `σ > 0`. -/
theorem dirichletEta_lseries_partial_cauchy_real {σ : ℝ} (hσ : 0 < σ) :
    CauchySeq
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          LSeries.term dirichletEtaCoeff ((σ : ℝ) : ℂ) n) := by
  -- Strategy: the sequence indexed by (N+1) equals a shift of the real cast;
  -- Cauchy-ness is preserved by shifting.
  have h_real_cauchy : CauchySeq
      (fun N : ℕ =>
        ∑ i ∈ Finset.range N, (-1 : ℝ)^i * (1 / ((i : ℝ) + 1) ^ σ)) :=
    dirichletEta_real_partial_cauchy hσ
  -- Cast to ℂ: Complex.ofReal is an isometry, hence uniformly continuous.
  have h_cast_cauchy : CauchySeq
      (fun N : ℕ =>
        ((((∑ i ∈ Finset.range N,
              (-1 : ℝ)^i * (1 / ((i : ℝ) + 1) ^ σ)) : ℝ)) : ℂ)) :=
    Complex.isometry_ofReal.uniformContinuous.comp_cauchySeq h_real_cauchy
  -- Rewrite via lseries_partialSum_succ_eq_real_cast pointwise.
  have h_pointwise : ∀ N : ℕ,
      (((∑ i ∈ Finset.range N,
            (-1 : ℝ)^i * (1 / ((i : ℝ) + 1) ^ σ) : ℝ)) : ℂ)
        = ∑ n ∈ Finset.range (N + 1),
            LSeries.term dirichletEtaCoeff ((σ : ℝ) : ℂ) n := by
    intro N
    exact (lseries_partialSum_succ_eq_real_cast N).symm
  have h_shift_cauchy : CauchySeq
      (fun N : ℕ =>
        ∑ n ∈ Finset.range (N + 1),
          LSeries.term dirichletEtaCoeff ((σ : ℝ) : ℂ) n) := by
    have h_eq : (fun N : ℕ =>
        ((((∑ i ∈ Finset.range N,
              (-1 : ℝ)^i * (1 / ((i : ℝ) + 1) ^ σ)) : ℝ)) : ℂ))
      = (fun N : ℕ =>
        ∑ n ∈ Finset.range (N + 1),
          LSeries.term dirichletEtaCoeff ((σ : ℝ) : ℂ) n) :=
      funext h_pointwise
    rw [← h_eq]; exact h_cast_cauchy
  -- Cauchy under shift by 1 ⇔ Cauchy of the original.
  exact (cauchySeq_shift 1).mp h_shift_cauchy

/-! ## §6 Existence of the complex limit at real `s = (σ : ℂ)`. -/

/-- **`dirichletEta_lseries_partial_hasLimit_real`** — UNCONDITIONAL.
There EXISTS a complex number to which the LSeries partial sums
converge at every real `s = (σ : ℂ)` with `σ > 0`. -/
theorem dirichletEta_lseries_partial_hasLimit_real {σ : ℝ} (hσ : 0 < σ) :
    ∃ L : ℂ, Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          LSeries.term dirichletEtaCoeff ((σ : ℝ) : ℂ) n)
      atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (dirichletEta_lseries_partial_cauchy_real hσ)

/-! ## §7 The refined named published-mathematics residual. -/

/-- **`DirichletEta_ConditionalConvergence_ComplexOffReal`** — REFINED
named published-mathematics residual, strictly smaller than the full
ingredient (2) of the r271 Dirichlet 1858 residual.

Asserts `CauchySeq` for the complex LSeries partial sums at every
`s : ℂ` with `Im s ≠ 0 ∧ 0 < Re s`. The classical result of Dirichlet
1858 for the abscissa of conditional convergence of alternating
Dirichlet series — standard reference: Titchmarsh, *The Theory of
Functions*, 2nd ed. 1939, §9.11; Hardy & Riesz, *The General Theory
of Dirichlet's Series*, 1915, Ch. II. Requires a complex-valued
Dirichlet-test variant (summation by parts + complex-power difference
bounds) outside mathlib's current infrastructure.

Together with `dirichletEta_lseries_partial_cauchy_real` (the real-ray
case, r276-unconditional), this discharges the FULL ingredient (2)
of the r271 four-ingredient design. -/
def DirichletEta_ConditionalConvergence_ComplexOffReal : Prop :=
  ∀ ⦃s : ℂ⦄, s.im ≠ 0 → 0 < s.re →
    CauchySeq (fun N : ℕ =>
      ∑ n ∈ Finset.range N, LSeries.term dirichletEtaCoeff s n)

/-! ## §8 Composition: real-ray (r276) + named residual ⟹ full ingredient (2). -/

/-- **`dirichletEta_lseries_partial_cauchy_via_named`** — under the
named refined residual `DirichletEta_ConditionalConvergence_ComplexOffReal`,
the complex LSeries partial sums for `dirichletEta` are Cauchy at
EVERY complex `s` with `0 < Re s`. Composes:

- r276's unconditional real-ray case for `Im s = 0`.
- The named refined residual for `Im s ≠ 0`. -/
theorem dirichletEta_lseries_partial_cauchy_via_named
    (h_off : DirichletEta_ConditionalConvergence_ComplexOffReal)
    {s : ℂ} (hs : 0 < s.re) :
    CauchySeq (fun N : ℕ =>
      ∑ n ∈ Finset.range N, LSeries.term dirichletEtaCoeff s n) := by
  by_cases him : s.im = 0
  · -- Real-ray case: rewrite s as ((s.re : ℝ) : ℂ) using him.
    have hs_eq : s = ((s.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [him]
    rw [hs_eq]
    exact dirichletEta_lseries_partial_cauchy_real hs
  · exact h_off him hs

/-! ## §9 Axiom check. -/

#print axioms
  PrincipiaTractalis.DirichletEtaConditionalConvergenceReal.dirichletEta_real_partial_cauchy
#print axioms
  PrincipiaTractalis.DirichletEtaConditionalConvergenceReal.dirichletEta_lseries_partial_cauchy_real
#print axioms
  PrincipiaTractalis.DirichletEtaConditionalConvergenceReal.dirichletEta_lseries_partial_hasLimit_real
#print axioms
  PrincipiaTractalis.DirichletEtaConditionalConvergenceReal.dirichletEta_lseries_partial_cauchy_via_named

end PrincipiaTractalis.DirichletEtaConditionalConvergenceReal
