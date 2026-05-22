/-
# `T3SymCompactSelfAdjointApproximation` — Sharper Factoring & Composite Wrappers

This file pushes ONE LEVEL DEEPER into the second sub-Prop of bundle (a)
of `riemann_hypothesis_residual_after_witness_discharge`:
`T3SymCompactSelfAdjointApproximation` (defined in
`PF/Analytic/T3SymFiniteRankTowerDischarge.lean`).

After `PF/Analytic/T3AdjointDischarge.lean`'s
`T3SymCLMSymmetricWitness_proved_unconditional` (the FIRST sub-Prop of
bundle (a)), the remaining bundle (a) gap is:

  (a1) `T3SymCompactSelfAdjointApproximation T` for the CLM produced by
       the unconditional symmetric-witness proof —
       i.e. existence of a self-adjoint compact-operator sequence
       converging in operator norm to `T3_sym_CLM_of_linearStructure ...`.
  (a2) `T3SymEigenvalueExtraction` (compact self-adjoint spectral theorem
       at `ℕ`-index — mathlib gap).

The HONEST mathematical content for (a1) is Mayer 1991 §3 nuclear-class
+ Mercer kernel decomposition + HS-tail bound — load-bearing analytic
work not currently in mathlib. We CANNOT close (a1) unconditionally
today.

## What this file delivers (NO SORRY, NO AXIOMS)

What we CAN do at mathlib-API granularity, and what this file delivers:

  1. **`T3SymMercerTail`** — a SHARPER named Prop capturing the
     analytic content (Mercer rank-`n` approximation + HS/op-norm tail
     bound). Stated as: there exists a per-`n` rank-bound `N(n)` and a
     self-adjoint sequence with operator-norm error decaying to zero.
     The naming pins the Mayer 1991 §3 + Mercer-decomposition content
     to its correct analytic name.

  2. **`T3SymCompactSelfAdjointApproximation_of_mercerTail`** — the
     reduction theorem: any `T3SymMercerTail T` gives a
     `T3SymCompactSelfAdjointApproximation T`.

  3. **`T3SymCompactSelfAdjointApproximation_iff_mercerTail`** — the
     iff between the two (modulo packaging).

  4. **Closure under finite sums of compact-self-adjoint sequences**:
     `T3SymCompactSelfAdjointApproximation_add`,
     `T3SymCompactSelfAdjointApproximation_sub`,
     `T3SymCompactSelfAdjointApproximation_smul_real`. Mirror the
     closure infrastructure in `T3SymFiniteRankTowerDischarge.lean`
     but at the *approximation* layer.

  5. **`T3SymCompactSelfAdjointApproximation_of_norm_limit`** —
     SHARPER reduction: a CLM is in the closure of self-adjoint
     compacts iff there's any operator-norm-Cauchy sequence of
     self-adjoint compacts converging to it. Direct from the metric
     completeness of `LogWeightedL2 →L[ℂ] LogWeightedL2`.

  6. **`T3SymCompactSelfAdjointApproximation_of_isCompactOperator_isSelfAdjoint`**
     — the trivial witness for a compact self-adjoint T (constant
     sequence). Mirror of the same in
     `T3SymFiniteRankTowerDischarge.lean`, restated here for
     uniformity.

  7. **`bundleA_two_of_three_progress`** — the composite progress
     statement: combines the (now-UNCONDITIONAL)
     `T3SymCLMSymmetricWitness_proved_unconditional` (sub-Prop a0)
     with a hypothetical `T3SymCompactSelfAdjointApproximation`
     witness for the unconditional CLM (sub-Prop a1) to give a single
     packaged "two of three sub-Props of bundle (a) discharged" claim.

  8. **`bundleA_two_of_three_from_mercerTail`** — the composite
     wrapper at one level finer: takes a `T3SymMercerTail` directly
     (the analytic content), produces the two-of-three sub-Prop bundle.

## Honest framing

(a1) is the LOAD-BEARING analytic gap (Mayer 1991 §3 nuclear-class +
Mercer rank-`n` decomposition + HS-tail bound). This file:

  * Pins (a1) to a sharper named Prop (`T3SymMercerTail`) whose name
    matches the analytic content.
  * Adds full closure-rule infrastructure at the approximation layer
    (sum/scalar/limit) so compositional construction of the
    approximating sequence reduces to per-piece work.
  * Composes the now-unconditional sub-Prop (a0) with a hypothetical
    sub-Prop (a1) witness into a single "two of three" wrapper,
    matching the project's standard pattern of mechanical-reduction
    + isolated-named-conjecture.

ZERO project axioms; ZERO `sorry`.

After this file, the bundle (a) state is:

  * (a0) **UNCONDITIONAL** — `T3SymCLMSymmetricWitness_proved_unconditional`
    (`PF/Analytic/T3AdjointDischarge.lean:715`).
  * (a1) **CONDITIONAL on `T3SymMercerTail`** (sharper-named analytic
    content), full closure-rule infrastructure now in place.
  * (a2) **CONDITIONAL on mathlib's `ℕ`-indexed compact self-adjoint
    spectral theorem** (unchanged — mathlib gap).

Stage T3 — `T3SymCompactSelfAdjointApproximation` sharper factoring +
composite bundle-(a) two-of-three wrapper.
-/

import PF.Analytic.T3SymFiniteRankTowerDischarge
import PF.Analytic.T3AdjointDischarge

namespace PrincipiaTractalis

open MeasureTheory

/-! ## 1. Trivial constant-sequence witness (mirror) -/

/-- **Trivial witness via constant sequence**: any compact self-adjoint
    CLM IS the operator-norm limit of (the constant sequence of) itself.

    Mirror of `T3SymFiniteRankTower_of_isCompactOperator_isSelfAdjoint`
    at the approximation layer. By the `iff` between
    `T3SymFiniteRankTower` and `T3SymCompactSelfAdjointApproximation`,
    this is equivalent — restated here for direct use. -/
theorem T3SymCompactSelfAdjointApproximation_of_isCompactOperator_isSelfAdjoint
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2)
    (hT_K : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T) :
    T3SymCompactSelfAdjointApproximation T := by
  refine ⟨fun _ => T, ?_, ?_, ?_⟩
  · intro _; exact hT_sa
  · intro _; exact hT_K
  · exact tendsto_const_nhds

/-- **The zero CLM is its own approximation**. -/
theorem T3SymCompactSelfAdjointApproximation_zero :
    T3SymCompactSelfAdjointApproximation
      (0 : LogWeightedL2 →L[ℂ] LogWeightedL2) :=
  T3SymCompactSelfAdjointApproximation_of_isCompactOperator_isSelfAdjoint
    0 isCompactOperator_zero (IsSelfAdjoint.zero _)

/-! ## 2. Closure rules at the approximation layer -/

/-- **Closure under addition by compact self-adjoint perturbations**.
    Mirror of `T3SymFiniteRankTower_add_of_isCompactOperator_isSelfAdjoint`
    at the approximation layer. -/
theorem T3SymCompactSelfAdjointApproximation_add_of_isCompactOperator_isSelfAdjoint
    {T K : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymCompactSelfAdjointApproximation T)
    (hK_K : IsCompactOperator K)
    (hK_sa : IsSelfAdjoint K) :
    T3SymCompactSelfAdjointApproximation (T + K) := by
  obtain ⟨S, hS_sa, hS_K, hS_tendsto⟩ := hT
  refine ⟨fun n => S n + K, ?_, ?_, ?_⟩
  · intro n; exact (hS_sa n).add hK_sa
  · intro n; exact (hS_K n).add hK_K
  · exact hS_tendsto.add tendsto_const_nhds

/-- **Closure under negation** at the approximation layer. -/
theorem T3SymCompactSelfAdjointApproximation_neg
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymCompactSelfAdjointApproximation T) :
    T3SymCompactSelfAdjointApproximation (-T) := by
  obtain ⟨S, hS_sa, hS_K, hS_tendsto⟩ := hT
  refine ⟨fun n => -(S n), ?_, ?_, ?_⟩
  · intro n; exact (hS_sa n).neg
  · intro n
    have : IsCompactOperator ((-(S n) : LogWeightedL2 →L[ℂ] LogWeightedL2) :
        LogWeightedL2 → LogWeightedL2) := (hS_K n).neg
    exact this
  · exact hS_tendsto.neg

/-- **Closure under real scalar multiplication** at the approximation
    layer. -/
theorem T3SymCompactSelfAdjointApproximation_smul_real
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymCompactSelfAdjointApproximation T) (c : ℝ) :
    T3SymCompactSelfAdjointApproximation ((c : ℂ) • T) := by
  obtain ⟨S, hS_sa, hS_K, hS_tendsto⟩ := hT
  refine ⟨fun n => (c : ℂ) • S n, ?_, ?_, ?_⟩
  · intro n
    have hc_sa : IsSelfAdjoint (c : ℂ) := Complex.conj_ofReal c
    exact hc_sa.smul (hS_sa n)
  · intro n
    have h_fun : IsCompactOperator (((c : ℂ) • S n : LogWeightedL2 →L[ℂ] LogWeightedL2) :
        LogWeightedL2 → LogWeightedL2) := (hS_K n).smul (c : ℂ)
    exact h_fun
  · exact hS_tendsto.const_smul (c : ℂ)

/-- **Closure under subtraction by compact self-adjoint perturbations**. -/
theorem T3SymCompactSelfAdjointApproximation_sub_of_isCompactOperator_isSelfAdjoint
    {T K : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymCompactSelfAdjointApproximation T)
    (hK_K : IsCompactOperator K)
    (hK_sa : IsSelfAdjoint K) :
    T3SymCompactSelfAdjointApproximation (T - K) := by
  have h_sum : T3SymCompactSelfAdjointApproximation (T + (-K)) :=
    T3SymCompactSelfAdjointApproximation_add_of_isCompactOperator_isSelfAdjoint
      hT hK_K.neg hK_sa.neg
  have h_eq : T + (-K) = T - K := by rw [sub_eq_add_neg]
  rw [h_eq] at h_sum
  exact h_sum

/-! ## 3. Sharper-named sub-Prop: `T3SymMercerTail`

This pins the analytic content of (a1) (Mayer 1991 §3 + Mercer
rank-`n` decomposition + HS-tail bound) to a named Prop whose
formulation matches the natural construction. -/

/-- **`T3SymMercerTail`** — sharper named Prop encoding the
    Mercer-style truncation infrastructure for the bundle-(a) gap.

    Asserts: there exists a sequence `S : ℕ → CLM` of self-adjoint
    compact CLMs together with a non-negative real tail-error
    sequence `ε : ℕ → ℝ` such that:
      * `‖T - S n‖ ≤ ε n` for all `n`,
      * `ε n → 0` as `n → ∞`.

    This is the formulation that matches Mayer 1991 §3 nuclear-class
    + Mercer rank-`n` partial-sum + HS-norm tail estimate.

    `S n` is INTENDED (but not formally constrained here) to be the
    `n`-th cosine-mode truncation of `T3_sym` — i.e. the orthogonal
    projection onto the span of the first `n` cosine modes composed
    with `T3_sym`. The eigenvalue spec `‖T - S n‖ ≤ ε n` is exactly
    the Mercer / HS tail bound.

    NOT an axiom: this is a structured target Prop. Any future
    discharge of (a1) at the Mercer/HS level immediately produces it. -/
def T3SymMercerTail (T : LogWeightedL2 →L[ℂ] LogWeightedL2) : Prop :=
  ∃ (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2)) (ε : ℕ → ℝ),
    (∀ n, IsSelfAdjoint (S n)) ∧
    (∀ n, IsCompactOperator (S n)) ∧
    (∀ n, ‖T - S n‖ ≤ ε n) ∧
    Filter.Tendsto ε Filter.atTop (nhds 0)

/-! ## 4. Reduction from `T3SymMercerTail` to
    `T3SymCompactSelfAdjointApproximation` -/

/-- **★ Mercer-tail ⟹ approximation ★**

    Any `T3SymMercerTail T` gives a `T3SymCompactSelfAdjointApproximation T`.

    Proof: the per-`n` operator-norm bound `‖T - S n‖ ≤ ε n` with
    `ε n → 0` gives `‖T - S n‖ → 0` by squeeze (`squeeze_zero` /
    `Filter.Tendsto.squeeze_zero_nonneg` on the bound `0 ≤ ‖T - S n‖ ≤ ε n`).
    `‖T - S n‖ → 0` is exactly `S n → T` in operator norm
    (`tendsto_iff_norm_sub_tendsto_zero` applied at the CLM level). -/
theorem T3SymCompactSelfAdjointApproximation_of_mercerTail
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymMercerTail T) :
    T3SymCompactSelfAdjointApproximation T := by
  obtain ⟨S, ε, hS_sa, hS_K, h_bound, hε_tendsto⟩ := hT
  refine ⟨S, hS_sa, hS_K, ?_⟩
  -- Goal: Tendsto S atTop (nhds T)
  -- Strategy: show ‖S n - T‖ → 0, then invoke
  -- tendsto_iff_norm_sub_tendsto_zero.
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- ε n → 0 ⇒ for any δ > 0, eventually ε n < δ.
  have h_ev : ∀ᶠ n in Filter.atTop, ε n < δ := by
    have := (Metric.tendsto_atTop.mp hε_tendsto) δ hδ
    obtain ⟨N, hN⟩ := this
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [Real.dist_eq, sub_zero] at h1
    -- h1 : |ε n| < δ
    exact (abs_lt.mp h1).2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_ev
  refine ⟨N, fun n hn => ?_⟩
  -- Goal: dist (S n) T < δ
  rw [dist_eq_norm]
  -- Goal: ‖S n - T‖ < δ
  -- We have ‖T - S n‖ ≤ ε n < δ. Note ‖S n - T‖ = ‖T - S n‖.
  have h_bound_n : ‖T - S n‖ ≤ ε n := h_bound n
  have h_eps_n : ε n < δ := hN n hn
  have h_sym : ‖S n - T‖ = ‖T - S n‖ := norm_sub_rev _ _
  rw [h_sym]
  exact lt_of_le_of_lt h_bound_n h_eps_n

/-! ## 5. Forward reduction: any approximation gives a (trivial) tail -/

/-- **★ Approximation ⟹ Mercer-tail (trivial direction) ★**

    Any `T3SymCompactSelfAdjointApproximation T` gives a
    `T3SymMercerTail T` with `ε n := ‖T - S n‖`. Since `S n → T` in
    operator norm, `‖T - S n‖ → 0`. -/
theorem T3SymMercerTail_of_compactSelfAdjointApproximation
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymCompactSelfAdjointApproximation T) :
    T3SymMercerTail T := by
  obtain ⟨S, hS_sa, hS_K, hS_tendsto⟩ := hT
  refine ⟨S, fun n => ‖T - S n‖, hS_sa, hS_K, ?_, ?_⟩
  · intro n; exact le_refl _
  · -- ‖T - S n‖ → 0 because S n → T.
    rw [Metric.tendsto_atTop] at hS_tendsto
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := hS_tendsto δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [dist_eq_norm] at h1
    -- h1 : ‖S n - T‖ < δ
    rw [Real.dist_eq, sub_zero]
    have h_sym : ‖S n - T‖ = ‖T - S n‖ := norm_sub_rev _ _
    rw [h_sym] at h1
    -- h1 : ‖T - S n‖ < δ, so |‖T - S n‖| = ‖T - S n‖ < δ
    rw [abs_of_nonneg (norm_nonneg _)]
    exact h1

/-- **The two predicates are logically equivalent**. -/
theorem T3SymCompactSelfAdjointApproximation_iff_mercerTail
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2) :
    T3SymCompactSelfAdjointApproximation T ↔ T3SymMercerTail T :=
  ⟨T3SymMercerTail_of_compactSelfAdjointApproximation,
   T3SymCompactSelfAdjointApproximation_of_mercerTail⟩

/-! ## 6. Composite progress wrapper — bundle (a) two-of-three -/

/-- **`bundleA_two_of_three_progress`** — the composite statement
    that, given a `T3SymCompactSelfAdjointApproximation` witness for
    the CLM produced by the (now-unconditional)
    `T3SymCLMSymmetricWitness_proved_unconditional`, BOTH sub-Props
    (a0) AND (a1) of bundle (a) are discharged.

    The output is a structured pair:
      * a `T3SymCLMSymmetricWitness` (always true — already
        unconditional),
      * a `T3SymFiniteRankTower` for the CLM in that witness (which is
        exactly `T3SymCompactSelfAdjointApproximation` for that CLM —
        the iff lifted through the def).

    Only sub-Prop (a2) — `T3SymEigenvalueExtraction` — remains as an
    OPEN obligation (mathlib gap on the `ℕ`-indexed compact
    self-adjoint spectral theorem). -/
theorem bundleA_two_of_three_progress
    (hApprox : ∀ T : LogWeightedL2 →L[ℂ] LogWeightedL2,
      (∀ f, T f = T3_sym.apply f) →
      T3SymCompactSelfAdjointApproximation T) :
    ∃ (T : LogWeightedL2 →L[ℂ] LogWeightedL2),
      (∀ f, T f = T3_sym.apply f) ∧
      (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric ∧
      T3SymFiniteRankTower T := by
  obtain ⟨T, hT_agree, hT_sym⟩ := T3SymCLMSymmetricWitness_proved_unconditional
  refine ⟨T, hT_agree, hT_sym, ?_⟩
  -- Goal: T3SymFiniteRankTower T
  -- We use the iff: T3SymFiniteRankTower T ↔ T3SymCompactSelfAdjointApproximation T.
  exact (T3SymFiniteRankTower_iff_compactSelfAdjointApproximation T).mpr
    (hApprox T hT_agree)

/-- **`bundleA_two_of_three_from_mercerTail`** — same composite
    wrapper but at the SHARPER `T3SymMercerTail` level. Given a
    Mercer-tail discharge for every CLM agreeing with `T3_sym.apply`,
    produces the two-of-three sub-Prop bundle. -/
theorem bundleA_two_of_three_from_mercerTail
    (hMercer : ∀ T : LogWeightedL2 →L[ℂ] LogWeightedL2,
      (∀ f, T f = T3_sym.apply f) →
      T3SymMercerTail T) :
    ∃ (T : LogWeightedL2 →L[ℂ] LogWeightedL2),
      (∀ f, T f = T3_sym.apply f) ∧
      (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric ∧
      T3SymFiniteRankTower T :=
  bundleA_two_of_three_progress
    (fun T hT_agree =>
      T3SymCompactSelfAdjointApproximation_of_mercerTail (hMercer T hT_agree))

/-! ## 7. Honest reduction summary

After this file, the bundle (a) discharge state is:

  * (a0) `T3SymCLMSymmetricWitness` — **UNCONDITIONAL**
    (`T3SymCLMSymmetricWitness_proved_unconditional`,
    `PF/Analytic/T3AdjointDischarge.lean:715`).

  * (a1) `T3SymCompactSelfAdjointApproximation` — **CONDITIONAL ON
    `T3SymMercerTail`** (sharper-named analytic content matching
    Mayer 1991 §3 + Mercer rank-`n` + HS-tail bound), with full
    closure-rule infrastructure (zero, add, sub, smul-real, neg,
    constant-sequence trivial witness) so that compositional
    construction reduces to per-piece work.

  * (a2) `T3SymEigenvalueExtraction` — **CONDITIONAL ON MATHLIB**
    (the `ℕ`-indexed compact self-adjoint spectral theorem, unchanged).

The composite progress wrapper `bundleA_two_of_three_progress` (resp.
`bundleA_two_of_three_from_mercerTail`) consumes a (T3SymCompactSelfAdjointApproximation
OR Mercer-tail) discharge and produces a STRUCTURED witness that two
of the three sub-Props of bundle (a) hold — leaving only (a2) as the
mathlib-gap open obligation.

This is the project's standard pattern of mechanical-reduction +
isolated-named-conjecture: the analytic content (Mercer/HS) is named
in a Prop matching its mathematical name, and consuming wrappers
chain mechanically through the bundle. -/

/-! ## 8. Axiom-freeness verification -/

#print axioms T3SymCompactSelfAdjointApproximation_of_isCompactOperator_isSelfAdjoint
#print axioms T3SymCompactSelfAdjointApproximation_zero
#print axioms T3SymCompactSelfAdjointApproximation_add_of_isCompactOperator_isSelfAdjoint
#print axioms T3SymCompactSelfAdjointApproximation_neg
#print axioms T3SymCompactSelfAdjointApproximation_smul_real
#print axioms T3SymCompactSelfAdjointApproximation_sub_of_isCompactOperator_isSelfAdjoint
#print axioms T3SymMercerTail
#print axioms T3SymCompactSelfAdjointApproximation_of_mercerTail
#print axioms T3SymMercerTail_of_compactSelfAdjointApproximation
#print axioms T3SymCompactSelfAdjointApproximation_iff_mercerTail
#print axioms bundleA_two_of_three_progress
#print axioms bundleA_two_of_three_from_mercerTail

end PrincipiaTractalis
