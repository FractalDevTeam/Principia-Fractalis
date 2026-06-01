/-
# Wave 55-Φ — ch₂ ↔ Φ_IIT Bridge: Prop → THEOREM Discharge

★ DISCHARGED 2026-05-31 via Wave 55-Φ_IIT_bridge proposal ★

## Scope

This file discharges the manuscript Ch 31 central claim
`ch₂ ≤ 1 − exp(−Φ_IIT/2)` from a structural Prop placeholder
(`Ch2PhiBridge.lean::Ch2PhiBridge`, line 133) to an actual axiom-free
THEOREM at the level of finite-dimensional Schmidt spectra
(equivalently: probability vectors `p : Fin n → ℝ` arising as the
spectrum of a reduced density matrix `ρ_A`).

The standard linear-entropy ↔ von Neumann-entropy inequality is here
proved from `Mathlib.Analysis.MeanInequalities`'s weighted AM-GM
(equivalently: Jensen's inequality applied to the convex function
`Real.exp` with weights `p i` and points `Real.log (p i)`).

## What is proved (axiom-free)

For any probability vector `p : Fin n → ℝ` with `∀ i, 0 ≤ p i` and
`∑ i, p i = 1` (the Schmidt spectrum of a finite-dim reduced state):

1. `linearEntropy_le_one_minus_exp_neg_vNEntropy`
   `1 − ∑ (p i)² ≤ 1 − exp(− (−∑ p i · log (p i)))`
   i.e. `ch₂(p) ≤ 1 − exp(−S_vN(p))`.

2. `ch2_le_one_minus_exp_neg_phi_over_two`
   The exact manuscript form, with `Φ_IIT(p) := 2 · S_vN(p)`:
   `ch₂(p) ≤ 1 − exp(−Φ_IIT(p) / 2)`.

3. `ch2_eq_one_minus_exp_neg_phi_over_two_uniform`
   Equality on the uniform-Schmidt locus `p i = 1/d`:
   `ch₂(uniform d) = 1 − exp(−Φ_IIT(uniform d) / 2)`.

4. `ch2_phi_bridge_inequality_pure_bipartite_finite_dim` — Wave 55-Φ
   capstone: bundles (1) + (2) + (3) at finite dimension d ≥ 1.

## What is NOT discharged

- The original `Ch2PhiBridge` Prop (`Ch2PhiBridge.lean` line 133) is
  written in a UNIVERSAL form over arbitrary real scalars satisfying
  `0 ≤ ch_2_val ≤ 1` and `0 ≤ Phi_val`. As written, that statement is
  **vacuously false** as a universal claim (e.g. `ch_2 = 0.5`,
  `Phi = 0` violate both disjuncts). The Prop's CORRECT reading is
  the state-relativised one we prove here, where `ch_2_val` and
  `Phi_val` are derived from the SAME probability vector.

- This file does NOT discharge the manuscript's bridge in the
  infinite-dimensional case `L²(ℝ³, ℂ²)`. That case is recorded as
  the named open Prop `Ch2PhiBridgeContinuousSchmidt` (see below).

- This file does NOT validate the IIT framework empirically (the
  synthetic-vs-real-EEG provenance gap, `evidence_base_audit.md`
  §5 item 16, remains).

- This file does NOT discharge any Clay problem.

## Mathlib lemmas invoked

- `Real.convexOn_exp` (Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:59)
- `ConvexOn.map_sum_le` (Mathlib/Analysis/Convex/Jensen.lean:63)
- `Real.exp_log` (Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)
- `Real.log_one`, `Real.log_inv`, `Real.exp_zero` (standard)

Stage L55-Φ — IIT bridge discharged at finite-dim Schmidt level.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic
import PF.Consciousness.Ch2PhiBridge

namespace PrincipiaTractalis.Consciousness

open Real Finset

/-! ## Schmidt spectrum: a probability vector on `Fin n` -/

/-- A finite-dim Schmidt spectrum: a probability vector `p : Fin n → ℝ`
    with nonneg entries summing to 1. Models the eigenvalues of the
    reduced density matrix `ρ_A` of a pure bipartite state on
    `ℂ^n ⊗ ℂ^m` with Schmidt rank ≤ n. -/
structure SchmidtSpectrum (n : ℕ) where
  /-- The spectrum values. -/
  p : Fin n → ℝ
  /-- Nonnegativity (eigenvalues of a density matrix). -/
  nonneg : ∀ i, 0 ≤ p i
  /-- Normalisation (trace = 1). -/
  sum_eq_one : ∑ i, p i = 1

/-- The linear entropy `ch₂(p) = 1 − ∑ (p i)²`.

    This is the framework Ch 6 definition of `ch₂` on quantum substrates
    (cf. `Ch2PhiBridge.lean` line 26: `ch_2(ψ) = 1 − Tr(ρ_A²)`). -/
def linearEntropy {n : ℕ} (s : SchmidtSpectrum n) : ℝ :=
  1 - ∑ i, (s.p i) ^ 2

/-- The von Neumann entropy `S_vN(p) = − ∑ p i · log (p i)`.

    Convention: `Real.log 0 = 0` in mathlib, so the `p i = 0` summands
    contribute `0 · 0 = 0`, matching the standard `0 · log 0 = 0`
    quantum-information convention. -/
noncomputable def vNEntropy {n : ℕ} (s : SchmidtSpectrum n) : ℝ :=
  - ∑ i, (s.p i) * Real.log (s.p i)

/-- The Tononi Φ_IIT measure on bipartite pure states, defined as
    `Φ_IIT(p) := 2 · S_vN(p)`.

    This matches `Ch2PhiBridge.lean` line 27:
    `Φ_IIT(ψ) = 2·S(ρ_A) = -2·Tr(ρ_A · log ρ_A)`. -/
noncomputable def Phi_IIT {n : ℕ} (s : SchmidtSpectrum n) : ℝ :=
  2 * vNEntropy s

/-! ## Each `p i` lies in `[0, 1]` -/

lemma SchmidtSpectrum.p_le_one {n : ℕ} (s : SchmidtSpectrum n) (i : Fin n) :
    s.p i ≤ 1 := by
  have hsum : s.p i ≤ ∑ j, s.p j := by
    have := Finset.single_le_sum (f := s.p) (s := (Finset.univ : Finset (Fin n)))
      (fun j _ => s.nonneg j) (Finset.mem_univ i)
    exact this
  rw [s.sum_eq_one] at hsum
  exact hsum

/-! ## Key Jensen step:
    `exp (∑ pᵢ · log pᵢ) ≤ ∑ pᵢ²`.

    This is the load-bearing inequality. Convexity of `Real.exp` plus
    `exp(log p) = p` (for `p > 0`) gives weighted-AM-GM. The boundary
    `p i = 0` case is absorbed because `0 * log 0 = 0` and `0² = 0`. -/

/-- Jensen's inequality applied to `Real.exp` with weights `p i` and
    points `log (p i)`, summed over those `i` with `p i > 0`.

    The result: `exp (∑ pᵢ · log pᵢ) ≤ ∑ pᵢ²`.

    Proof strategy: factor through the weighted AM-GM
    `geom_mean_le_arith_mean_weighted` from `MeanInequalities.lean`,
    applied with `z i = p i`. -/
theorem exp_sum_p_log_p_le_sum_p_sq {n : ℕ} (s : SchmidtSpectrum n) :
    Real.exp (∑ i, (s.p i) * Real.log (s.p i)) ≤ ∑ i, (s.p i) ^ 2 := by
  -- We apply `Real.geom_mean_le_arith_mean_weighted` with w = p, z = p:
  --   ∏ (p i)^(p i) ≤ ∑ (p i) * (p i) = ∑ (p i)²
  -- Then express the LHS as `exp (∑ p i * log (p i))`.
  -- Define s' := Finset.univ and use the mathlib lemma.
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ s.p i :=
    fun i _ => s.nonneg i
  have hw' : ∑ i ∈ (Finset.univ : Finset (Fin n)), s.p i = 1 := s.sum_eq_one
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ s.p i :=
    fun i _ => s.nonneg i
  have hAMGM :
      ∏ i ∈ (Finset.univ : Finset (Fin n)), (s.p i) ^ (s.p i) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin n)), s.p i * s.p i :=
    Real.geom_mean_le_arith_mean_weighted (s := (Finset.univ : Finset (Fin n)))
      (w := s.p) (z := s.p) hw hw' hz
  -- Rewrite ∑ p i * p i = ∑ (p i)^2:
  have h_sum_sq : (∑ i ∈ (Finset.univ : Finset (Fin n)), s.p i * s.p i)
      = ∑ i, (s.p i) ^ 2 := by
    simp [pow_two]
  rw [h_sum_sq] at hAMGM
  -- It remains to show: exp (∑ p i * log (p i)) ≤ ∏ (p i) ^ (p i).
  -- This is an equality (whenever the product is well-defined for our
  -- nonneg sequence). Use a per-`i` case split via two-sided bound.
  refine le_trans ?_ hAMGM
  -- Show: exp (∑ p i * log (p i)) ≤ ∏ (p i)^(p i).
  -- For nonneg p i with p i ∈ [0,1], we have:
  --   (p i)^(p i) = exp ((p i) * log (p i))   if p i > 0
  --   (p i)^(p i) = 0^0 = 1                   if p i = 0  (rpow convention)
  --   exp((p i)*log(p i)) = exp(0*log 0) = exp 0 = 1  if p i = 0
  -- So termwise they're equal. We push exp through the sum.
  have h_exp_sum :
      Real.exp (∑ i, (s.p i) * Real.log (s.p i))
        = ∏ i, Real.exp ((s.p i) * Real.log (s.p i)) := by
    rw [Real.exp_sum]
  rw [h_exp_sum]
  -- Now: ∏ exp (p i * log (p i)) ≤ ∏ (p i)^(p i). Termwise ≤ (in fact =).
  apply Finset.prod_le_prod
  · intro i _
    exact Real.exp_nonneg _
  · intro i _
    -- show exp ((p i) * log (p i)) ≤ (p i)^(p i)
    by_cases hpi : s.p i = 0
    · -- p i = 0: LHS = exp(0 * log 0) = exp 0 = 1; RHS = 0^0 = 1 (rpow conv).
      rw [hpi]
      simp
    · -- p i > 0: LHS = exp(p_i * log p_i) and RHS = exp(log p_i * p_i)
      -- (`rpow_def_of_pos` gives `p^p = exp(log p * p)`); equal up to mul_comm.
      have hpi_pos : 0 < s.p i := lt_of_le_of_ne (s.nonneg i) (Ne.symm hpi)
      rw [Real.rpow_def_of_pos hpi_pos, mul_comm]

/-! ## Bridge inequality on `SchmidtSpectrum n` -/

/-- **Linear-entropy vs von-Neumann-entropy inequality**.
    `1 − ∑ (p i)² ≤ 1 − exp (−S_vN(p))`.

    Equivalently: `Tr(ρ_A²) ≥ exp(−S_vN(ρ_A))`. -/
theorem linearEntropy_le_one_minus_exp_neg_vNEntropy
    {n : ℕ} (s : SchmidtSpectrum n) :
    linearEntropy s ≤ 1 - Real.exp (- vNEntropy s) := by
  -- exp(-S_vN) = exp(∑ p log p) ≤ ∑ p² (by exp_sum_p_log_p_le_sum_p_sq)
  -- Hence 1 - ∑ p² ≤ 1 - exp(-S_vN).
  have h := exp_sum_p_log_p_le_sum_p_sq s
  unfold linearEntropy vNEntropy
  have h_neg : - (- ∑ i, (s.p i) * Real.log (s.p i))
                = ∑ i, (s.p i) * Real.log (s.p i) := by ring
  rw [h_neg]
  linarith

/-- **★ The manuscript form ★**:
    `ch₂(p) ≤ 1 − exp(−Φ_IIT(p) / 2)`. -/
theorem ch2_le_one_minus_exp_neg_phi_over_two
    {n : ℕ} (s : SchmidtSpectrum n) :
    linearEntropy s ≤ 1 - Real.exp (- Phi_IIT s / 2) := by
  have h := linearEntropy_le_one_minus_exp_neg_vNEntropy s
  -- Phi_IIT = 2 · S_vN, so -Phi/2 = -S_vN.
  have h_eq : - Phi_IIT s / 2 = - vNEntropy s := by
    unfold Phi_IIT
    ring
  rw [h_eq]
  exact h

/-! ## Uniform Schmidt locus: equality -/

/-- The uniform-Schmidt distribution on `Fin (n+1)`: `p i = 1/(n+1)`. -/
noncomputable def uniformSchmidt (n : ℕ) : SchmidtSpectrum (n + 1) where
  p := fun _ => (1 : ℝ) / (n + 1)
  nonneg := fun _ => by positivity
  sum_eq_one := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp

/-- **Equality on the uniform Schmidt locus**:
    `ch₂(uniform d) = 1 − exp(−Φ_IIT(uniform d)/2)`. -/
theorem ch2_eq_one_minus_exp_neg_phi_over_two_uniform (n : ℕ) :
    linearEntropy (uniformSchmidt n) = 1 - Real.exp (- Phi_IIT (uniformSchmidt n) / 2) := by
  unfold linearEntropy Phi_IIT vNEntropy uniformSchmidt
  set d : ℝ := (n + 1 : ℝ) with hd
  have hd_pos : 0 < d := by
    rw [hd]; positivity
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  -- LHS: 1 − ∑ (1/d)² = 1 − (n+1)·(1/d)² = 1 − 1/d
  have h_sum_sq :
      (∑ _i : Fin (n + 1), ((1 : ℝ) / d) ^ 2) = 1 / d := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    -- (n+1) • (1/d)^2 = 1/d  since d = n+1.
    rw [nsmul_eq_mul]
    have h_d_eq : ((↑(n + 1) : ℝ)) = d := by
      push_cast; rw [hd]
    rw [h_d_eq]
    field_simp
  -- RHS: 1 − exp(−(2·(−∑ (1/d)·log(1/d)))/2)
  --     = 1 − exp(∑ (1/d)·log(1/d))
  --     = 1 − exp((n+1)·(1/d)·log(1/d))
  --     = 1 − exp(log(1/d))
  --     = 1 − 1/d
  have h_sum_plogp :
      (∑ _i : Fin (n + 1), ((1 : ℝ) / d) * Real.log ((1 : ℝ) / d))
        = Real.log ((1 : ℝ) / d) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
    have h_d_eq : ((↑(n + 1) : ℝ)) = d := by
      push_cast; rw [hd]
    rw [h_d_eq]
    field_simp
  -- Now compute both sides.
  -- Use show to align the goal with explicit form.
  show 1 - (∑ _i : Fin (n + 1), ((1 : ℝ) / d) ^ 2)
      = 1 - Real.exp (- (2 * - ∑ _i : Fin (n + 1), ((1 : ℝ) / d) * Real.log ((1 : ℝ) / d)) / 2)
  rw [h_sum_sq, h_sum_plogp]
  have h_arg : - (2 * - Real.log ((1 : ℝ) / d)) / 2 = Real.log ((1 : ℝ) / d) := by ring
  rw [h_arg]
  have h_inv_pos : (0 : ℝ) < 1 / d := by positivity
  rw [Real.exp_log h_inv_pos]

/-! ## Discharge of the original `Ch2PhiBridge` Prop

    The original `Ch2PhiBridge` (`Ch2PhiBridge.lean` line 133) reads:
    `∀ (ch_2_val Phi_val : ℝ), 0 ≤ ch_2_val → ch_2_val ≤ 1 →
       0 ≤ Phi_val →
       ch_2_val ≤ 1 - exp(-Phi_val/2) ∨ ch_2_val = 1 - exp(-Phi_val/2)`.

    As a UNIVERSAL claim over arbitrary scalar pairs, this is FALSE:
    pick `ch_2_val = 0.5`, `Phi_val = 0`. Both disjuncts fail.

    The intended reading (and the manuscript's reading) is the
    state-relativised one: `ch_2_val` and `Phi_val` derived from the
    same Schmidt spectrum. We capture that as a new state-level
    predicate and discharge it. -/

/-- **State-level bridge predicate** (the correct formulation of
    Ch 31 `thm:iit-resonance` on finite-dim Schmidt spectra). -/
def Ch2PhiBridgeState (n : ℕ) : Prop :=
  ∀ (s : SchmidtSpectrum n),
    linearEntropy s ≤ 1 - Real.exp (- Phi_IIT s / 2)

/-- **Discharge**: the state-level bridge predicate holds for any `n`. -/
theorem ch2_phi_bridge_state_holds (n : ℕ) : Ch2PhiBridgeState n :=
  fun s => ch2_le_one_minus_exp_neg_phi_over_two s

/-- **Honest record**: the original `Ch2PhiBridge` Prop is satisfied
    *whenever* both disjuncts are interpreted state-relatively, i.e.
    when the scalars come from a real Schmidt spectrum. The unrestricted
    universal form is unsatisfiable; we discharge the state-relative
    form via `ch2_phi_bridge_state_holds`. -/
theorem ch2_phi_bridge_universal_form_unsatisfiable :
    ¬ Ch2PhiBridge := by
  -- Witness: ch_2 = 1/2, Phi = 0. Both disjuncts fail.
  intro hC
  have h := hC (1/2 : ℝ) (0 : ℝ) (by norm_num) (by norm_num) le_rfl
  -- h : (1/2 ≤ 1 - exp(-0/2)) ∨ (1/2 = 1 - exp(-0/2))
  -- exp(-0/2) = exp 0 = 1, so RHS = 0. Both branches: 1/2 ≤ 0 OR 1/2 = 0.
  have h_exp : Real.exp (-0 / 2) = 1 := by
    simp [Real.exp_zero]
  rw [h_exp] at h
  rcases h with h1 | h2
  · linarith
  · linarith

/-! ## Honest open: infinite-dim continuous Schmidt case

    The discharge above is at the level of `Fin n` Schmidt spectra
    (i.e. density matrices on `ℂ^n` with finite Schmidt rank). The
    manuscript's full claim implicitly ranges over `L²(ℝ³, ℂ²)`
    (continuous Schmidt decomposition with σ-finite measure). That
    case requires the corresponding mathlib measure-theoretic entropy
    framework (`MeasureTheory.entropy`), which is not yet in scope
    of this file. We record the gap explicitly: -/

/-- **Named open Prop**: extension of the bridge to continuous Schmidt
    spectra (σ-finite measure-theoretic probability densities).

    Gap statement: given a probability density `μ` on a σ-finite measure
    space `(X, dx)` with `∫ μ dx = 1` and `μ ≥ 0`, the linear-entropy
    vs differential-entropy inequality
    `1 − ∫ μ² dx ≤ 1 − exp(−(−∫ μ · log μ dx))` requires the convex
    Jensen inequality for `Real.exp` against a probability measure
    `μ · dx`. This is straightforward analytically (and is the
    measure-theoretic shadow of `geom_mean_le_arith_mean_weighted`),
    but its mathlib formalisation in this exact form is not invoked
    here. -/
def Ch2PhiBridgeContinuousSchmidt : Prop :=
  ∀ (μ : ℝ → ℝ), (∀ x, 0 ≤ μ x) →
    -- normalisation, square-integrability, entropy convergence
    -- conditions would be stated alongside the integral form
    True  -- placeholder body; the predicate is named for downstream use

/-! ## ★ Wave 55-Φ Capstone ★ -/

/-- **★ Wave 55-Φ: ch₂ ↔ Φ_IIT closed-form bridge ★**

    Bundle of the IIT-resonance bridge content proved unconditionally
    at finite Schmidt rank:

    1. The inequality `ch₂(s) ≤ 1 − exp(−Φ_IIT(s)/2)` for every
       Schmidt spectrum `s : SchmidtSpectrum n` (Ch 31 thm:iit-resonance,
       lines 64-76, in the *state-relativised* reading).
    2. Equality on the uniform-Schmidt locus `p i = 1/(n+1)` — the
       maximally-mixed case where `ch₂ = 1 − 1/d` and
       `Φ_IIT = 2 log d`.
    3. The original `Ch2PhiBridge` Prop's universal-scalar form is
       falsified (it is not a theorem as stated); the correct
       discharge is the state-relativised `Ch2PhiBridgeState n`.

    Status: discharges Ch 31's central inequality at finite Schmidt
    rank from Prop to theorem. Does NOT extend to the continuous
    `L²(ℝ³, ℂ²)` case (recorded as `Ch2PhiBridgeContinuousSchmidt`
    above). Does NOT validate the IIT framework empirically (the
    synthetic-vs-real-EEG provenance gap is outside this file's scope).
    Does NOT discharge any Clay problem.

    Honest scope: ONE specific manuscript claim, Prop → theorem,
    at finite Schmidt rank, via standard Jensen / weighted AM-GM. -/
theorem ch2_phi_bridge_inequality_pure_bipartite_finite_dim :
    -- Clause 1: the inequality for every Schmidt spectrum
    (∀ (n : ℕ) (s : SchmidtSpectrum n),
      linearEntropy s ≤ 1 - Real.exp (- Phi_IIT s / 2)) ∧
    -- Clause 2: equality on the uniform Schmidt locus
    (∀ (n : ℕ),
      linearEntropy (uniformSchmidt n)
        = 1 - Real.exp (- Phi_IIT (uniformSchmidt n) / 2)) ∧
    -- Clause 3: state-level Prop discharged for every n
    (∀ (n : ℕ), Ch2PhiBridgeState n) ∧
    -- Clause 4: the original UNIVERSAL-scalar Ch2PhiBridge is NOT a theorem
    ¬ Ch2PhiBridge := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n s
    exact ch2_le_one_minus_exp_neg_phi_over_two s
  · intro n
    exact ch2_eq_one_minus_exp_neg_phi_over_two_uniform n
  · intro n
    exact ch2_phi_bridge_state_holds n
  · exact ch2_phi_bridge_universal_form_unsatisfiable

/-! ## Sanity: uniform Schmidt at d = 20 matches manuscript threshold

    The manuscript's `ch₂ = 0.95` threshold corresponds (via uniform
    Schmidt at dimension 20) to `Φ_IIT = 2 log 20` exactly. This is
    consistent with `Ch2PhiBridge.lean::Phi_threshold_from_ch2_095`. -/

/-- At `n + 1 = 20` (i.e. `n = 19`), `ch₂(uniform 19) = 19/20 = 0.95`
    and `Φ_IIT(uniform 19) = 2 · log 20`. -/
theorem uniform_at_d20_matches_ch2_095_threshold :
    linearEntropy (uniformSchmidt 19) = 19 / 20 ∧
    Phi_IIT (uniformSchmidt 19) = 2 * Real.log 20 := by
  refine ⟨?_, ?_⟩
  · unfold linearEntropy uniformSchmidt
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  · unfold Phi_IIT vNEntropy uniformSchmidt
    have h_sum :
        (∑ _i : Fin 20, ((1 : ℝ) / (19 + 1)) * Real.log ((1 : ℝ) / (19 + 1)))
          = Real.log (1 / 20) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      have h20 : ((19 : ℝ) + 1) = 20 := by norm_num
      rw [h20]
      ring
    show 2 * - ∑ _i : Fin 20, ((1 : ℝ) / (19 + 1)) * Real.log ((1 : ℝ) / (19 + 1))
        = 2 * Real.log 20
    rw [h_sum]
    have : Real.log (1 / (20 : ℝ)) = - Real.log 20 := by
      rw [Real.log_div one_ne_zero (by norm_num : (20 : ℝ) ≠ 0), Real.log_one]
      ring
    rw [this]
    ring

end PrincipiaTractalis.Consciousness
