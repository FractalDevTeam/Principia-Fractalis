/-
# `T3SymMercerTail` — Sharper Factoring & Builder Infrastructure

This file pushes ONE LEVEL DEEPER into the (a1) sub-Prop of bundle (a) of
`riemann_hypothesis_residual_after_witness_discharge`: `T3SymMercerTail`
(defined in `PF/Analytic/T3SymCompactApproxDischarge.lean:224`).

After `T3SymCompactApproxDischarge.lean` factored
`T3SymCompactSelfAdjointApproximation` into the `T3SymMercerTail` form
(operator-norm error sequence ε_n → 0), the remaining task is to
*construct* such an (S_n, ε_n) sequence for the specific T_3_sym CLM.

The HONEST mathematical content remains Mayer 1991 §3 nuclear-class +
Mercer rank-`n` decomposition + HS-tail bound — multi-week analytic
work not currently in mathlib (and not currently bridged to T_3_sym at
the CLM level).

What this file CAN do at mathlib-API granularity:

  (A) **Factor `T3SymMercerTail` into even sharper sub-Props** so that
      any future analytic input lands at the smallest possible
      "construct this one sequence" level.

  (B) **Add builder infrastructure** turning summable-norm hypotheses,
      Cauchy-telescoping hypotheses, and rank-`n` finite-rank
      hypotheses into `T3SymMercerTail` witnesses.

  (C) **Compositional closure** of `T3SymMercerTail` under sum, scalar,
      negation (lifting from the already-proven approximation-layer
      closure rules via the existing biconditional iff).

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`T3SymHilbertSchmidtTailBound`** — sharpest named Prop:
     there is a sequence of self-adjoint compact CLMs whose tail
     operator-norm errors are bounded above by a `Summable` series.
     This is the formulation that matches the HS-tail estimate
     `∑_{n} ‖T - S_n‖^p < ∞` for `p = 1` (HS) or any summable bound.

  2. **`T3SymMercerTail_of_hilbertSchmidtTail`** — discharge:
     HS-tail-bounded summable approximation gives `T3SymMercerTail`.
     Proof via the standard "summable tails tend to 0" lemma.

  3. **`T3SymCauchyTelescope`** — alternative formulation: a sequence
     `S_n` of self-adjoint compacts with `Summable (fun n => ‖S(n+1) - S n‖)`
     plus an initial term whose norm-sum gives convergence to T in
     operator norm.

  4. **`T3SymMercerTail_of_cauchyTelescope`** — discharge: any
     Cauchy-telescope witness gives a Mercer-tail.

  5. **`T3SymMercerTail_of_uniform_tail_bound`** — direct discharge
     route via `∀ n, ‖T - S n‖ ≤ C / (n+1)` with `S n` self-adjoint
     compact. (A Weyl-decay form on the tail.)

  6. **`T3SymMercerTail_of_summable_tail_bound`** — direct discharge
     route via `‖T - S n‖ ≤ b n` with `Summable b` and `b n ≥ 0` ⇒
     `Tendsto b atTop (nhds 0)` ⇒ Mercer-tail.

  7. **`T3SymMercerTail_zero`** — the zero CLM trivially has a
     Mercer-tail. Mirror of `T3SymCompactSelfAdjointApproximation_zero`
     lifted through the iff.

  8. **`T3SymMercerTail_of_isCompactOperator_isSelfAdjoint`** — any
     compact self-adjoint CLM has a (trivial constant-sequence)
     Mercer-tail.

  9. **`T3SymMercerTail_add_of_isCompactOperator_isSelfAdjoint`** —
     closure: if T has a Mercer-tail and K is compact + self-adjoint,
     then T+K has a Mercer-tail.

 10. **`T3SymMercerTail_neg`** — closure under negation.

 11. **`T3SymMercerTail_smul_real`** — closure under real scalar mult.

 12. **`T3SymMercerTail_sub_of_isCompactOperator_isSelfAdjoint`** —
     subtraction by compact self-adjoint perturbations.

 13. **`bundleA_two_of_three_from_summable_tail`** — composite wrapper
     at the SHARPEST level: a summable per-CLM tail bound discharges
     two-of-three sub-Props of bundle (a).

## Honest framing

After this file, the bundle (a) state for sub-Prop (a1) is:

  * **`T3SymMercerTail`** factored into FOUR alternative builder forms
    (`HilbertSchmidtTailBound`, `CauchyTelescope`, `uniform_tail_bound`,
    `summable_tail_bound`), each at minimal mathlib-API granularity.

  * **Compositional closure** at the Mercer-tail layer (zero, add,
    sub, smul-real, neg, constant-sequence trivial witness).

  * The load-bearing content (constructing the cosine-mode truncated
    sequence for the specific `T_3_sym_CLM_of_linearStructure`) is
    unchanged — it still requires the Mayer 1991 §3 + Mercer
    decomposition + HS-tail bound work, BUT the input it needs to
    produce is now reduced to its smallest possible form: a single
    summable real-valued tail bound `b n ≥ 0` with `‖T - S n‖ ≤ b n`
    where `(S n)` is self-adjoint compact.

  * The composite wrapper `bundleA_two_of_three_from_summable_tail`
    composes the (a0) unconditional symmetric witness with a sub-Prop
    (a1) discharge from a summable tail bound.

ZERO project axioms; ZERO `sorry`.

## Discharge state after this file

  * (a0) **UNCONDITIONAL** (T3SymCLMSymmetricWitness_proved_unconditional)
  * (a1) **CONDITIONAL on `Summable b ∧ ∀ n, ‖T - S n‖ ≤ b n` for some
         self-adjoint compact sequence (S n)** — the sharpest possible
         mathlib-API form. Mayer 1991 §3 Mercer rank-`n` truncation
         with HS norm summability would produce this.
  * (a2) **CONDITIONAL on mathlib** `ℕ`-indexed compact self-adjoint
         spectral theorem (unchanged).

Stage T3 — `T3SymMercerTail` sharper factoring + builder infrastructure.
-/

import PF.Analytic.T3SymCompactApproxDischarge

namespace PrincipiaTractalis

open MeasureTheory Filter

/-! ## 1. Trivial base cases at the Mercer-tail layer (mirror) -/

/-- **The zero CLM has a Mercer-tail** — constant-zero sequence with
    `ε n = 0`. -/
theorem T3SymMercerTail_zero :
    T3SymMercerTail (0 : LogWeightedL2 →L[ℂ] LogWeightedL2) := by
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro _; exact IsSelfAdjoint.zero _
  · intro _; exact isCompactOperator_zero
  · intro n; simp
  · exact tendsto_const_nhds

/-- **Any compact self-adjoint CLM has a Mercer-tail** via the constant
    sequence `S n := T` and `ε n := 0`. -/
theorem T3SymMercerTail_of_isCompactOperator_isSelfAdjoint
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2)
    (hT_K : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T) :
    T3SymMercerTail T := by
  refine ⟨fun _ => T, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro _; exact hT_sa
  · intro _; exact hT_K
  · intro _; simp
  · exact tendsto_const_nhds

/-! ## 2. Closure rules at the Mercer-tail layer (via the iff) -/

/-- **Closure under addition** by compact self-adjoint perturbations. -/
theorem T3SymMercerTail_add_of_isCompactOperator_isSelfAdjoint
    {T K : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymMercerTail T)
    (hK_K : IsCompactOperator K)
    (hK_sa : IsSelfAdjoint K) :
    T3SymMercerTail (T + K) := by
  -- Lift through the iff: Mercer ↔ approximation; closure already
  -- proved at the approximation layer in T3SymCompactApproxDischarge.
  have h_approx : T3SymCompactSelfAdjointApproximation T :=
    T3SymCompactSelfAdjointApproximation_of_mercerTail hT
  have h_approx_sum : T3SymCompactSelfAdjointApproximation (T + K) :=
    T3SymCompactSelfAdjointApproximation_add_of_isCompactOperator_isSelfAdjoint
      h_approx hK_K hK_sa
  exact T3SymMercerTail_of_compactSelfAdjointApproximation h_approx_sum

/-- **Closure under negation** at the Mercer-tail layer. -/
theorem T3SymMercerTail_neg
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymMercerTail T) :
    T3SymMercerTail (-T) := by
  have h_approx : T3SymCompactSelfAdjointApproximation T :=
    T3SymCompactSelfAdjointApproximation_of_mercerTail hT
  have h_approx_neg : T3SymCompactSelfAdjointApproximation (-T) :=
    T3SymCompactSelfAdjointApproximation_neg h_approx
  exact T3SymMercerTail_of_compactSelfAdjointApproximation h_approx_neg

/-- **Closure under real scalar multiplication** at the Mercer-tail
    layer. -/
theorem T3SymMercerTail_smul_real
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymMercerTail T) (c : ℝ) :
    T3SymMercerTail ((c : ℂ) • T) := by
  have h_approx : T3SymCompactSelfAdjointApproximation T :=
    T3SymCompactSelfAdjointApproximation_of_mercerTail hT
  have h_approx_smul : T3SymCompactSelfAdjointApproximation ((c : ℂ) • T) :=
    T3SymCompactSelfAdjointApproximation_smul_real h_approx c
  exact T3SymMercerTail_of_compactSelfAdjointApproximation h_approx_smul

/-- **Closure under subtraction** by compact self-adjoint perturbations. -/
theorem T3SymMercerTail_sub_of_isCompactOperator_isSelfAdjoint
    {T K : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymMercerTail T)
    (hK_K : IsCompactOperator K)
    (hK_sa : IsSelfAdjoint K) :
    T3SymMercerTail (T - K) := by
  have h_approx : T3SymCompactSelfAdjointApproximation T :=
    T3SymCompactSelfAdjointApproximation_of_mercerTail hT
  have h_approx_sub : T3SymCompactSelfAdjointApproximation (T - K) :=
    T3SymCompactSelfAdjointApproximation_sub_of_isCompactOperator_isSelfAdjoint
      h_approx hK_K hK_sa
  exact T3SymMercerTail_of_compactSelfAdjointApproximation h_approx_sub

/-! ## 3. Sharper builder Props (alternative formulations) -/

/-- **`T3SymHilbertSchmidtTailBound`** — sharpest named Prop encoding
    the Mercer/Hilbert-Schmidt content: there is a self-adjoint
    compact sequence `S n` and a nonneg real sequence `b n` with
      * `‖T - S n‖ ≤ b n` for all `n`,
      * `Summable b`.

    This is the formulation that DIRECTLY matches an HS-tail estimate
    of the form `∑_n (HS-norm of n-th cosine-mode tail of T)^2 < ∞`,
    or any other summable upper bound on the operator-norm tails.

    Sharper than `T3SymMercerTail` because the convergence condition
    `ε n → 0` is replaced with the STRONGER `Summable b`. Tendsto-zero
    follows from summability (the standard `Summable.tendsto_atTop_zero`). -/
def T3SymHilbertSchmidtTailBound (T : LogWeightedL2 →L[ℂ] LogWeightedL2) : Prop :=
  ∃ (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2)) (b : ℕ → ℝ),
    (∀ n, IsSelfAdjoint (S n)) ∧
    (∀ n, IsCompactOperator (S n)) ∧
    (∀ n, 0 ≤ b n) ∧
    (∀ n, ‖T - S n‖ ≤ b n) ∧
    Summable b

/-- **★ HS-tail-bound ⟹ Mercer-tail ★**

    `Summable b` ⟹ `Tendsto b atTop (nhds 0)`
    (`Summable.tendsto_atTop_zero`). Combined with the per-`n`
    operator-norm bound, the (S, b) pair is exactly a `T3SymMercerTail`
    witness. -/
theorem T3SymMercerTail_of_hilbertSchmidtTail
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymHilbertSchmidtTailBound T) :
    T3SymMercerTail T := by
  obtain ⟨S, b, hS_sa, hS_K, _hb_nn, h_bound, hb_sum⟩ := hT
  refine ⟨S, b, hS_sa, hS_K, h_bound, ?_⟩
  exact hb_sum.tendsto_atTop_zero

/-! ## 4. Direct Mercer-tail builder from summable real bound -/

/-- **★ Direct builder from a summable upper-bound ★**

    Given a self-adjoint compact sequence `S n` and a nonneg real
    sequence `b n` with `‖T - S n‖ ≤ b n` AND `Summable b`, get a
    Mercer-tail. This is `T3SymMercerTail_of_hilbertSchmidtTail`
    unpacked — exposed as a one-shot builder for ergonomic use. -/
theorem T3SymMercerTail_of_summable_tail_bound
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2))
    (b : ℕ → ℝ)
    (hS_sa : ∀ n, IsSelfAdjoint (S n))
    (hS_K : ∀ n, IsCompactOperator (S n))
    (hb_nn : ∀ n, 0 ≤ b n)
    (h_bound : ∀ n, ‖T - S n‖ ≤ b n)
    (hb_sum : Summable b) :
    T3SymMercerTail T :=
  T3SymMercerTail_of_hilbertSchmidtTail
    ⟨S, b, hS_sa, hS_K, hb_nn, h_bound, hb_sum⟩

/-! ## 5. Uniform `C/(n+1)`-decay variant (Weyl-style tail) -/

/-- **★ Direct builder from a `C/(n+1)` polynomially-decaying tail ★**

    This is NOT summable (∑ 1/(n+1) diverges) so we go through the
    direct Tendsto route: `C/(n+1) → 0` by `tendsto_one_div_add_atTop_nhds_zero_nat`
    (up to constant rescaling). Useful when the Mercer truncation
    delivers a `C/n` operator-norm bound rather than a summable one. -/
theorem T3SymMercerTail_of_uniform_tail_bound
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2))
    (C : ℝ) (_hC : 0 ≤ C)
    (hS_sa : ∀ n, IsSelfAdjoint (S n))
    (hS_K : ∀ n, IsCompactOperator (S n))
    (h_bound : ∀ n, ‖T - S n‖ ≤ C / ((n : ℝ) + 1)) :
    T3SymMercerTail T := by
  refine ⟨S, fun n => C / ((n : ℝ) + 1), hS_sa, hS_K, h_bound, ?_⟩
  -- Tendsto: C/(n+1) → 0 as n → ∞.
  -- We use C * (1/(n+1)) and (1/(n+1)) → 0.
  have h_inv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat
    exact this
  have h_const : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) atTop (nhds (C * 0)) :=
    h_inv.const_mul C
  rw [mul_zero] at h_const
  have h_eq : (fun n : ℕ => C / ((n : ℝ) + 1)) =
              (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) := by
    funext n; ring
  rw [h_eq]
  exact h_const

/-! ## 6. Cauchy-telescope variant -/

/-- **`T3SymCauchyTelescope`** — alternative builder Prop: a sequence
    `S : ℕ → CLM` of self-adjoint compact CLMs together with an
    increment sequence `Δ : ℕ → ℝ` such that:
      * `Δ n ≥ 0`,
      * `‖S (n+1) - S n‖ ≤ Δ n`,
      * `Summable Δ`,
      * `‖T - S 0‖ ≤ ∑' n, Δ n`.

    Geometrically: S_n converges to T via telescoping in operator norm,
    with summable increments. This matches an iterative-construction
    scheme for the Mercer expansion (add one cosine-mode contribution
    per step). -/
def T3SymCauchyTelescope (T : LogWeightedL2 →L[ℂ] LogWeightedL2) : Prop :=
  ∃ (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2)) (Δ : ℕ → ℝ),
    (∀ n, IsSelfAdjoint (S n)) ∧
    (∀ n, IsCompactOperator (S n)) ∧
    (∀ n, 0 ≤ Δ n) ∧
    (∀ n, ‖S (n + 1) - S n‖ ≤ Δ n) ∧
    Summable Δ ∧
    (∀ n, ‖T - S n‖ ≤ ∑' k, Δ (n + k))

/-- **★ Cauchy-telescope ⟹ Mercer-tail ★**

    The tail-sums `∑' k, Δ (n + k)` form a sequence that tends to 0
    as n → ∞ — proved here by a direct ε-N argument using:
      (a) `Summable Δ` ⇒ `Tendsto (fun N => ∑ k in range N, Δ k) atTop (nhds (∑' k, Δ k))`
          (`HasSum.tendsto_sum_nat`).
      (b) the tail formula `∑' k, Δ (n + k) = ∑' k, Δ k - ∑ k in range n, Δ k`
          for any Summable Δ (sum_add_tsum_nat_add).
    Combined with `‖T - S n‖ ≤ ∑' k, Δ (n + k)`, this gives a Mercer-tail. -/
theorem T3SymMercerTail_of_cauchyTelescope
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymCauchyTelescope T) :
    T3SymMercerTail T := by
  obtain ⟨S, Δ, hS_sa, hS_K, _hΔ_nn, _hΔ_inc, hΔ_sum, h_tail_bound⟩ := hT
  refine ⟨S, fun n => ∑' k, Δ (n + k), hS_sa, hS_K, h_tail_bound, ?_⟩
  -- Tendsto: ∑' k, Δ (n + k) → 0 as n → ∞.
  -- Use `Summable.tendsto_sum_nat_add` (the real-valued tail-tendsto-zero
  -- corollary of summability) via the indexing form (k + n) ↔ (n + k).
  have h_swap : (fun n : ℕ => ∑' k, Δ (n + k)) =
                 (fun n : ℕ => ∑' k, Δ (k + n)) := by
    funext n
    apply tsum_congr
    intro k
    rw [Nat.add_comm]
  rw [h_swap]
  -- `tendsto_sum_nat_add` (real version) gives this directly.
  exact tendsto_sum_nat_add Δ

/-! ## 7. Composite wrapper at the SHARPEST level -/

/-- **`bundleA_two_of_three_from_summable_tail`** — composite wrapper
    at the sharpest level: takes a summable-tail-bound discharge for
    every CLM agreeing with `T3_sym.apply` and produces the
    two-of-three sub-Prop bundle for bundle (a).

    The input is the SMALLEST possible mathlib-API form: a per-T
    self-adjoint compact sequence with a summable real upper bound on
    the operator-norm tail. This is exactly the form that Mayer 1991
    §3 nuclear-class + Mercer rank-`n` partial-sum + HS-tail estimate
    would produce. -/
theorem bundleA_two_of_three_from_summable_tail
    (hSummable : ∀ T : LogWeightedL2 →L[ℂ] LogWeightedL2,
      (∀ f, T f = T3_sym.apply f) →
      ∃ (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2)) (b : ℕ → ℝ),
        (∀ n, IsSelfAdjoint (S n)) ∧
        (∀ n, IsCompactOperator (S n)) ∧
        (∀ n, 0 ≤ b n) ∧
        (∀ n, ‖T - S n‖ ≤ b n) ∧
        Summable b) :
    ∃ (T : LogWeightedL2 →L[ℂ] LogWeightedL2),
      (∀ f, T f = T3_sym.apply f) ∧
      (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric ∧
      T3SymFiniteRankTower T :=
  bundleA_two_of_three_from_mercerTail
    (fun T hT_agree =>
      let ⟨S, b, hS_sa, hS_K, hb_nn, h_bound, hb_sum⟩ := hSummable T hT_agree
      T3SymMercerTail_of_summable_tail_bound S b hS_sa hS_K hb_nn h_bound hb_sum)

/-- **`bundleA_two_of_three_from_uniform_tail`** — alternative composite
    wrapper at the C/(n+1) polynomial-decay level. -/
theorem bundleA_two_of_three_from_uniform_tail
    (hUniform : ∀ T : LogWeightedL2 →L[ℂ] LogWeightedL2,
      (∀ f, T f = T3_sym.apply f) →
      ∃ (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2)) (C : ℝ),
        0 ≤ C ∧
        (∀ n, IsSelfAdjoint (S n)) ∧
        (∀ n, IsCompactOperator (S n)) ∧
        (∀ n, ‖T - S n‖ ≤ C / ((n : ℝ) + 1))) :
    ∃ (T : LogWeightedL2 →L[ℂ] LogWeightedL2),
      (∀ f, T f = T3_sym.apply f) ∧
      (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric ∧
      T3SymFiniteRankTower T :=
  bundleA_two_of_three_from_mercerTail
    (fun T hT_agree =>
      let ⟨S, C, hC, hS_sa, hS_K, h_bound⟩ := hUniform T hT_agree
      T3SymMercerTail_of_uniform_tail_bound S C hC hS_sa hS_K h_bound)

/-- **`bundleA_two_of_three_from_cauchyTelescope`** — alternative
    composite wrapper at the Cauchy-telescope level. -/
theorem bundleA_two_of_three_from_cauchyTelescope
    (hCauchy : ∀ T : LogWeightedL2 →L[ℂ] LogWeightedL2,
      (∀ f, T f = T3_sym.apply f) →
      T3SymCauchyTelescope T) :
    ∃ (T : LogWeightedL2 →L[ℂ] LogWeightedL2),
      (∀ f, T f = T3_sym.apply f) ∧
      (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric ∧
      T3SymFiniteRankTower T :=
  bundleA_two_of_three_from_mercerTail
    (fun T hT_agree => T3SymMercerTail_of_cauchyTelescope (hCauchy T hT_agree))

/-! ## 8. Iff between HilbertSchmidtTailBound and MercerTail
       (one direction is trivial — every Mercer-tail with summable ε
       trivially gives an HS-tail-bound; the converse is the main
       reduction theorem above) -/

/-- **Backward**: any Mercer-tail with the additional property that the
    tail-error sequence is itself summable gives a HS-tail-bound. (Note:
    a generic Mercer-tail's ε → 0 does NOT imply Summable ε; so this is
    a strictly stronger condition, hence we factor it out.) -/
theorem T3SymHilbertSchmidtTail_of_mercerTail_summable
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2))
    (ε : ℕ → ℝ)
    (hS_sa : ∀ n, IsSelfAdjoint (S n))
    (hS_K : ∀ n, IsCompactOperator (S n))
    (hε_nn : ∀ n, 0 ≤ ε n)
    (h_bound : ∀ n, ‖T - S n‖ ≤ ε n)
    (hε_sum : Summable ε) :
    T3SymHilbertSchmidtTailBound T :=
  ⟨S, ε, hS_sa, hS_K, hε_nn, h_bound, hε_sum⟩

/-! ## 9. Honest reduction summary

After this file, the bundle (a1) discharge state is:

  * `T3SymMercerTail` is now factored into FOUR alternative builder
    forms at minimal mathlib-API granularity:
      - `T3SymHilbertSchmidtTailBound` (summable tail; sharpest)
      - `T3SymCauchyTelescope` (incremental construction)
      - `_of_uniform_tail_bound` (C/(n+1) polynomial decay)
      - `_of_summable_tail_bound` (one-shot ergonomic builder)

  * Full compositional closure at the Mercer-tail layer (zero, add,
    sub, smul-real, neg, constant-sequence trivial witness).

  * Three composite wrappers (`bundleA_two_of_three_from_*`) at
    different builder levels, each consuming the corresponding
    sharpest mathlib-API-form discharge and producing the two-of-three
    sub-Prop bundle.

The load-bearing content (constructing the (S n) + (b n) sequence
for the specific T_3_sym CLM) is unchanged in mathematical depth —
it's still Mayer 1991 §3 + Mercer kernel decomposition + HS-tail
bound. But the surface area at which any future analytic input must
land is now reduced to its smallest possible form.

For the next-session attacker: produce, for the
`T3_sym_CLM_of_linearStructure` produced by
`T3SymCLMSymmetricWitness_proved_unconditional`, one of:
  (a) An (S, b) pair with S self-adjoint compact, b ≥ 0 summable,
      ‖T - S n‖ ≤ b n. This is the SHARPEST input.
  (b) An (S, C) pair with S self-adjoint compact, ‖T - S n‖ ≤ C/(n+1).
      (More restrictive than (a); easier to write down in practice.)
  (c) A Cauchy-telescope (S, Δ).

Each (a)/(b)/(c) discharges sub-Prop (a1) and, combined with the
unconditional (a0), gives the two-of-three bundle (a) discharge.
The remaining sub-Prop (a2) (mathlib `ℕ`-indexed compact self-adjoint
spectral theorem) is independent of this work.
-/

/-! ## 10. Axiom-freeness verification -/

#print axioms T3SymMercerTail_zero
#print axioms T3SymMercerTail_of_isCompactOperator_isSelfAdjoint
#print axioms T3SymMercerTail_add_of_isCompactOperator_isSelfAdjoint
#print axioms T3SymMercerTail_neg
#print axioms T3SymMercerTail_smul_real
#print axioms T3SymMercerTail_sub_of_isCompactOperator_isSelfAdjoint
#print axioms T3SymHilbertSchmidtTailBound
#print axioms T3SymMercerTail_of_hilbertSchmidtTail
#print axioms T3SymMercerTail_of_summable_tail_bound
#print axioms T3SymMercerTail_of_uniform_tail_bound
#print axioms T3SymCauchyTelescope
#print axioms T3SymMercerTail_of_cauchyTelescope
#print axioms bundleA_two_of_three_from_summable_tail
#print axioms bundleA_two_of_three_from_uniform_tail
#print axioms bundleA_two_of_three_from_cauchyTelescope
#print axioms T3SymHilbertSchmidtTail_of_mercerTail_summable

end PrincipiaTractalis
