/-
# `T3SymFiniteRankTower` Discharge — Constructive Tower Witnesses

This file pushes one level deeper into bundle (a) of
`PF/Analytic/T3SymCompactWitness.lean` by providing **constructive
witnesses** of the `T3SymFiniteRankTower T` predicate in the cases where
the load-bearing analytic content is already in place, plus a
**reduction-to-named-Prop** layer factoring the general case into a
sharper sub-Prop at mathlib-API granularity.

## Why this file exists

`T3SymFiniteRankTower T` (`PF/Analytic/T3SymCompactWitness.lean:163`)
existentially asserts a sequence of self-adjoint compact CLMs converging
to `T` in operator norm. The general case — that the specific CLM built
from `T3_sym.apply` via `T3SymLinearStructure` admits such a tower — is
the load-bearing **analytic** content (Mayer 1991 §3 holomorphic-extension
+ Grothendieck nuclear-class argument; not currently in mathlib).

But the **bookkeeping side** of the predicate is fully attackable today:

  * The **zero** CLM trivially admits the tower (constant-zero sequence).
  * Any **compact self-adjoint** CLM trivially admits the tower
    (constant-`T` sequence).
  * Any CLM that is the **operator-norm limit of self-adjoint compact
    CLMs** admits the tower (direct repackaging).
  * The predicate is **stable under compact self-adjoint perturbations**
    (if `T` has a tower and `K` is compact self-adjoint, then `T + K` has
    a tower).
  * The predicate is **stable under real scalar multiplication** (if `T`
    has a tower and `c : ℝ`, then `(c : ℂ) • T` has a tower).

These convert the obligation "show `T3SymFiniteRankTower T`" into the
**sharper** obligation "show `T` is the operator-norm limit of
self-adjoint compact CLMs" — which is exactly the mathlib-API level at
which the spectral-truncation / Mercer-decomposition / Hilbert-Schmidt
argument lives.

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`T3SymFiniteRankTower_zero`** — the zero CLM admits the tower
     (constant zero sequence).
  2. **`T3SymFiniteRankTower_of_isCompactOperator_isSelfAdjoint`** — any
     compact self-adjoint CLM admits the tower (constant `T` sequence).
  3. **`T3SymCompactSelfAdjointApproximation`** — sharper named sub-Prop:
     "`T` is the operator-norm limit of self-adjoint compact CLMs".
  4. **`T3SymFiniteRankTower_of_compactSelfAdjointApproximation`** —
     direct extraction: any `T3SymCompactSelfAdjointApproximation` is a
     `T3SymFiniteRankTower`.
  5. **`T3SymCompactSelfAdjointApproximation_of_T3SymFiniteRankTower`** —
     the converse: any `T3SymFiniteRankTower` IS a
     `T3SymCompactSelfAdjointApproximation`. The two predicates are
     **logically equivalent** at the definitional level.
  6. **`T3SymFiniteRankTower_iff_compactSelfAdjointApproximation`** —
     the named iff.
  7. **`T3SymFiniteRankTower_add_of_isCompactOperator_isSelfAdjoint`** —
     stability under compact self-adjoint perturbations.
  8. **`T3SymFiniteRankTower_smul_real`** — stability under real scalar
     multiplication.
  9. **`T3SymFiniteRankTower_neg`** — stability under negation.

## Honest framing

This file does NOT prove `T3SymFiniteRankTower` for the specific CLM
that wraps `T3_sym.apply` — that requires identifying the constructed
CLM as the operator-norm limit of self-adjoint compact CLMs, which is
the load-bearing analytic content (Mayer 1991 nuclear-class theory).

What this file DOES deliver:

  (a) The constructive **base cases** (zero, compact self-adjoint) and
      **closure rules** (sum, real scalar, negation), bringing the
      `T3SymFiniteRankTower` predicate down to mathlib's basic
      arithmetic on `IsCompactOperator` + `IsSelfAdjoint`.
  (b) A formal **iff-equivalence** between `T3SymFiniteRankTower` and
      the sharper-named `T3SymCompactSelfAdjointApproximation`, making
      the load-bearing gap explicit in a name that matches the analytic
      content (T is the closure of compact self-adjoints).
  (c) Mechanical reduction: any future construction yielding a
      self-adjoint compact approximating sequence for the
      `T3_sym`-CLM discharges `T3SymFiniteRankTower` without further
      work.

ZERO project axioms; ZERO `sorry`.

Stage T3 — `T3SymFiniteRankTower` constructive witnesses + iff-reduction.
-/

import PF.Analytic.T3SymCompactWitness

namespace PrincipiaTractalis

open MeasureTheory

/-! ## 1. Trivial base cases -/

/-- **The zero CLM admits a finite-rank tower** — constant-zero sequence.

    Each `S n = 0` is self-adjoint (`IsSelfAdjoint.zero`) and compact
    (`isCompactOperator_zero`), and the constant sequence trivially
    converges to `0`. -/
theorem T3SymFiniteRankTower_zero :
    T3SymFiniteRankTower (0 : LogWeightedL2 →L[ℂ] LogWeightedL2) := by
  refine ⟨fun _ => 0, ?_, ?_, ?_⟩
  · intro _; exact IsSelfAdjoint.zero _
  · intro _; exact isCompactOperator_zero
  · exact tendsto_const_nhds

/-- **Any compact self-adjoint CLM admits a finite-rank tower** —
    constant-`T` sequence.

    The constant sequence `fun _ => T` trivially converges to `T`, and
    each term is self-adjoint + compact by the hypotheses. -/
theorem T3SymFiniteRankTower_of_isCompactOperator_isSelfAdjoint
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2)
    (hT_K : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T) :
    T3SymFiniteRankTower T := by
  refine ⟨fun _ => T, ?_, ?_, ?_⟩
  · intro _; exact hT_sa
  · intro _; exact hT_K
  · exact tendsto_const_nhds

/-! ## 2. The sharper named sub-Prop and its iff-reduction -/

/-- **`T3SymCompactSelfAdjointApproximation`** — the sharper named
    sub-Prop: `T` is the operator-norm limit of self-adjoint compact
    CLMs.

    This is logically equivalent to `T3SymFiniteRankTower` (see the
    `iff` theorem below), but its name accurately reflects the
    analytic content of the gap: the construction of a *spectrally
    truncated* approximating sequence for `T3_sym`, which is the
    Mercer-decomposition / Hilbert-Schmidt / nuclear-class content.

    Provenance (when supplied): the Mayer 1991 §3 nuclear-class
    decomposition of the holomorphic extension of `T_3`, or any
    explicit Mercer eigendecomposition of `T3_sym`, would produce such
    an approximating sequence. -/
def T3SymCompactSelfAdjointApproximation
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2) : Prop :=
  ∃ (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2)),
    (∀ n, IsSelfAdjoint (S n)) ∧
    (∀ n, IsCompactOperator (S n)) ∧
    Filter.Tendsto S Filter.atTop (nhds T)

/-- **Forward extraction**: any `T3SymCompactSelfAdjointApproximation`
    gives a `T3SymFiniteRankTower`. Definitionally identical. -/
theorem T3SymFiniteRankTower_of_compactSelfAdjointApproximation
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (h : T3SymCompactSelfAdjointApproximation T) :
    T3SymFiniteRankTower T := h

/-- **Backward extraction**: any `T3SymFiniteRankTower` gives a
    `T3SymCompactSelfAdjointApproximation`. Definitionally identical. -/
theorem T3SymCompactSelfAdjointApproximation_of_T3SymFiniteRankTower
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (h : T3SymFiniteRankTower T) :
    T3SymCompactSelfAdjointApproximation T := h

/-- **The named iff**: `T3SymFiniteRankTower` and
    `T3SymCompactSelfAdjointApproximation` are logically equivalent.

    This factors the bundle (a) compactness gap into a named Prop whose
    name matches the analytic content of the construction (T is the
    closure of compact self-adjoints). -/
theorem T3SymFiniteRankTower_iff_compactSelfAdjointApproximation
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2) :
    T3SymFiniteRankTower T ↔ T3SymCompactSelfAdjointApproximation T :=
  Iff.rfl

/-! ## 3. Closure rules: sum, scalar, negation

These let the user **build up** towers compositionally. If the
T3_sym-CLM is the sum of a piece for which the tower is known
constructively (e.g. a finite-rank truncation) plus a compact
self-adjoint remainder, then the tower lifts to the sum.
-/

/-- **Closure under compact self-adjoint perturbations**: if `T` admits
    a tower and `K` is compact + self-adjoint, then `T + K` admits a
    tower.

    Proof: take `S' n := S n + K` where `(S n)` is `T`'s tower. Each
    `S' n` is self-adjoint + compact (closure under addition), and
    `S n + K → T + K` as `n → ∞`. -/
theorem T3SymFiniteRankTower_add_of_isCompactOperator_isSelfAdjoint
    {T K : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymFiniteRankTower T)
    (hK_K : IsCompactOperator K)
    (hK_sa : IsSelfAdjoint K) :
    T3SymFiniteRankTower (T + K) := by
  obtain ⟨S, hS_sa, hS_K, hS_tendsto⟩ := hT
  refine ⟨fun n => S n + K, ?_, ?_, ?_⟩
  · intro n; exact (hS_sa n).add hK_sa
  · intro n; exact (hS_K n).add hK_K
  · -- S n + K → T + K
    exact hS_tendsto.add tendsto_const_nhds

/-- **Closure under negation**: if `T` admits a tower, so does `-T`.

    Proof: take `S' n := -(S n)`. Each is self-adjoint
    (`IsSelfAdjoint.neg`) and compact (`IsCompactOperator.neg`), and
    `-(S n) → -T`. -/
theorem T3SymFiniteRankTower_neg
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymFiniteRankTower T) :
    T3SymFiniteRankTower (-T) := by
  obtain ⟨S, hS_sa, hS_K, hS_tendsto⟩ := hT
  refine ⟨fun n => -(S n), ?_, ?_, ?_⟩
  · intro n; exact (hS_sa n).neg
  · intro n
    -- IsCompactOperator.neg applied at the CLM level
    have : IsCompactOperator ((-(S n) : LogWeightedL2 →L[ℂ] LogWeightedL2) :
        LogWeightedL2 → LogWeightedL2) := (hS_K n).neg
    exact this
  · exact hS_tendsto.neg

/-- **Closure under real scalar multiplication**: if `T` admits a tower
    and `c : ℝ`, then `(c : ℂ) • T` admits a tower.

    Proof: take `S' n := (c : ℂ) • S n`. Each is self-adjoint (real
    scalars preserve self-adjointness on a complex space because
    `star (c : ℂ) = c` when `c : ℝ`) and compact (`IsCompactOperator.smul`),
    and `(c : ℂ) • S n → (c : ℂ) • T` by continuity of scalar
    multiplication. -/
theorem T3SymFiniteRankTower_smul_real
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hT : T3SymFiniteRankTower T) (c : ℝ) :
    T3SymFiniteRankTower ((c : ℂ) • T) := by
  obtain ⟨S, hS_sa, hS_K, hS_tendsto⟩ := hT
  refine ⟨fun n => (c : ℂ) • S n, ?_, ?_, ?_⟩
  · intro n
    -- For a real scalar c, (c : ℂ) is self-adjoint in ℂ (star = id on ℝ),
    -- and a self-adjoint scalar times a self-adjoint CLM stays
    -- self-adjoint. We avoid the algebraic detour by direct calc on
    -- the star (= adjoint) of the smul CLM.
    have hc_sa : IsSelfAdjoint (c : ℂ) := Complex.conj_ofReal c
    exact hc_sa.smul (hS_sa n)
  · intro n
    -- IsCompactOperator.smul for the underlying-function form.
    have h_fun : IsCompactOperator (((c : ℂ) • S n : LogWeightedL2 →L[ℂ] LogWeightedL2) :
        LogWeightedL2 → LogWeightedL2) := (hS_K n).smul (c : ℂ)
    exact h_fun
  · -- (c : ℂ) • S n → (c : ℂ) • T by continuity of scalar mult.
    exact hS_tendsto.const_smul (c : ℂ)

/-! ## 4. Concrete progress summary

After this file, the state of `T3SymFiniteRankTower` is:

  * **Trivial base cases proven**: zero CLM, any compact self-adjoint
    CLM (each gets a tower for free).
  * **Closure rules proven**: stability under sum-with-compact-SA,
    negation, real-scalar multiplication.
  * **Sharper named Prop introduced**:
    `T3SymCompactSelfAdjointApproximation`, with a definitional `iff`
    to `T3SymFiniteRankTower`. Its name matches the analytic content
    of the missing input (T is the operator-norm closure of
    self-adjoint compacts).
  * **Reduction to mathlib API**: to discharge `T3SymFiniteRankTower T`
    for the `T3_sym`-CLM, it suffices to exhibit ANY sequence of
    self-adjoint compact CLMs converging to T in operator norm.

The load-bearing analytic content (existence of such a sequence for the
specific `T3_sym`-CLM) is unchanged — it remains the operator-side gap
documented in `T3SymCompactWitness.lean`. But the *bookkeeping side* is
now fully discharged, and the named sub-Prop pins the gap to its
correct analytic name.

## What still needs to land for the full discharge of bundle (a)

  1. A concrete approximating sequence `S n` (n-th cosine-mode
     truncation or n-th Mercer partial sum) for the
     `T3_sym_CLM_of_linearStructure` from
     `PF/Analytic/T3SymCLMConstruction.lean`. This is the
     `T3SymCompactSelfAdjointApproximation` content.
  2. An operator-norm convergence estimate for `S n → T3_sym_CLM`
     (Hilbert-Schmidt tail bound on `T3_sym - S n`).
  3. The mathlib `ℕ`-indexed compact self-adjoint spectral theorem
     (still missing in the pinned mathlib).

Items 1, 2 together = `T3SymCompactSelfAdjointApproximation`.
Item 3 = `T3SymEigenvalueExtraction`. Both remain as named Props at
mathlib-API granularity.
-/

/-! ## 5. Axiom-freeness verification -/

#print axioms T3SymFiniteRankTower_zero
#print axioms T3SymFiniteRankTower_of_isCompactOperator_isSelfAdjoint
#print axioms T3SymCompactSelfAdjointApproximation
#print axioms T3SymFiniteRankTower_of_compactSelfAdjointApproximation
#print axioms T3SymCompactSelfAdjointApproximation_of_T3SymFiniteRankTower
#print axioms T3SymFiniteRankTower_iff_compactSelfAdjointApproximation
#print axioms T3SymFiniteRankTower_add_of_isCompactOperator_isSelfAdjoint
#print axioms T3SymFiniteRankTower_neg
#print axioms T3SymFiniteRankTower_smul_real

end PrincipiaTractalis
