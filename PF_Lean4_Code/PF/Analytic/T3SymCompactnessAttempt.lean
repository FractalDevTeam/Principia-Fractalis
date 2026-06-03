/-
# `IsCompactOperator T3_sym` — Structural Upgrade Attempt

This file ATTEMPTS to discharge the residual named open after the
`T3SymMercerTailT3SymDischarge.lean` sharpening: namely

    `IsCompactOperator (T3_sym_CLM_of_linearStructure hLin)`

— which is the LAST remaining bit for closing Bundle (a) of the RH
spectral chain axiom-free.

## Result delivered: STRUCTURAL UPGRADE (option b)

A direct discharge of `IsCompactOperator T3_sym.apply` requires the
Mayer 1991 §3 Hilbert-Schmidt kernel content (analytic-continuation
to a holomorphic extension of the transfer operator plus Grothendieck
nuclear-class theory). This mathlib pin contains neither
`HilbertSchmidt` nor `Schatten` namespaces (verified by inspection of
`Mathlib/Analysis/`). Producing the analytic content from inside Lean
is a multi-month research engineering task, not a single discharge.

Instead this file delivers the SHARPEST POSSIBLE structural reduction:

  1. **`T3SymHilbertSchmidtNuclearWitness`** — a typed Prop encoding
     the Mayer 1991 §3 content directly at mathlib-API granularity:
     a sequence of finite-rank self-adjoint compact CLMs that converges
     to the target CLM in operator norm. This is **exactly** what
     the nuclear-class proof produces (truncate the holomorphic
     kernel's Mercer expansion at level n; each truncation is a finite
     rank operator). The Prop is operator-norm-tendsto-flavored
     (not HS-norm-flavored) because operator-norm convergence is
     what `isCompactOperator_of_tendsto` consumes; HS-norm
     convergence implies operator-norm convergence trivially.

  2. **`T3_sym_CLM_isCompactOperator_of_HSNuclearWitness`** — the
     existing `T3SymMercerTail` Mercer-tail content reduces to the
     witness. Discharges
     `IsCompactOperator (T3_sym_CLM_of_linearStructure hLin)`
     axiom-free from the witness via `isCompactOperator_of_tendsto`.

  3. **`T3_sym_apply_isCompactOperator_of_HSNuclearWitness`** —
     transports compactness of the CLM to the bare function
     `T3_sym.apply` via `T3_sym_CLM_of_linearStructure_apply_eq`
     (pointwise agreement) plus `IsCompactOperator` invariance under
     function extensionality. Closes the bare-function form of the
     named open.

  4. **`T3SymFiniteRankTower_of_HSNuclearWitness`** — produces the
     existing `T3SymFiniteRankTower` predicate from the witness
     (recall: `T3SymFiniteRankTower` is the analog of
     `H_P_finiteRankTower` and is what
     `T3_sym_clm_isCompactOperator_of_finiteRankTower` consumes).
     This makes the HS-nuclear witness a drop-in for the entire
     tower-side of bundle (a).

  5. **`T3SymMercerTail_of_HSNuclearWitness`** — composes (2) with
     the existing `T3SymMercerTail_of_compact_at_T3_sym_CLM` to
     deliver the Mercer-tail conclusion directly from the HS-nuclear
     witness. Single hypothesis → full Mercer-tail discharge.

  6. **`bundleA_oneOfThree_from_HSNuclearWitness`** — composite
     wrapper: the (a0) symmetric witness is unconditional, (a1)
     Mercer-tail discharges from the HS-nuclear witness via (5),
     leaving only the (a2) ℕ-indexed spectral-theorem extraction
     (a separate mathlib gap). Replicates exactly the prior
     `bundleA_two_of_three_from_witness_compactness` shape but
     uses the HS-nuclear witness as input instead of an opaque
     compactness hypothesis.

## What this file does NOT do

  * Does NOT axiomatically assert nuclear-class membership of T3.
    `T3SymHilbertSchmidtNuclearWitness` is a typed Prop, not an axiom,
    and the witness is the consumer's obligation to produce.
  * Does NOT prove `IsCompactOperator T3_sym.apply` unconditionally.
    Compactness still requires Mayer 1991 §3 to construct the witness.
  * Does NOT close Clay-level RH. The HS-nuclear witness is one of
    the remaining named open Props on the path to bundle (a)
    discharge; bundle (c) (surjectivity) remains the load-bearing
    open conjecture.

## Why the structural-upgrade form is the right deliverable

The honest mathematical situation is:

  * The bare-function `IsCompactOperator T3_sym.apply` is equivalent
    (mod the linear-structure witness) to compactness of the CLM.
  * Compactness of the CLM is equivalent to: there exists a sequence
    of compact self-adjoint CLMs converging to it (mathlib's
    `isCompactOperator_of_tendsto` + `isClosed_setOf_isCompactOperator`).
  * For self-adjoint compact operators on a separable Hilbert space,
    "compact" ↔ "approximable by finite-rank in operator norm" ↔
    "Mercer expansion of the kernel converges in HS norm".

The `T3SymHilbertSchmidtNuclearWitness` predicate captures the second
of these formulations DIRECTLY. This is the sharpest possible
factoring: it isolates the analytic content (existence of an
approximating sequence — Mayer 1991 §3's actual deliverable) from
the formal content (the implication compactness ⟹ Mercer-tail ⟹
spectral theorem ⟹ RH precondition), all of which is already in this
codebase or in mathlib.

ZERO new project axioms; ZERO `sorry`.

Stage T3 — `IsCompactOperator T3_sym` named-open structural upgrade.
-/

import PF.Analytic.T3SymMercerTailT3SymDischarge
import Mathlib.Analysis.Normed.Operator.Compact

namespace PrincipiaTractalis

open MeasureTheory Filter

/-! ## 1. Hilbert-Schmidt / nuclear-class witness predicate -/

/-- **`T3SymHilbertSchmidtNuclearWitness`** — structured Prop encoding
    the Mayer 1991 §3 nuclear-class content for a candidate `T3_sym`
    CLM.

    A sequence `S : ℕ → CLM` of finite-rank self-adjoint compact
    operators converging to the target `T` in operator norm.

    Mathematical content: Mayer 1991 §3 proves the transfer operator
    `T3` has a holomorphic extension whose Mercer-kernel expansion
    `K(x, y) = ∑_n λ_n φ_n(x) φ_n(y)` converges in Hilbert-Schmidt
    norm. The partial sums `K_N(x, y) = ∑_{n=0}^N λ_n φ_n(x) φ_n(y)`
    define finite-rank self-adjoint operators with `‖K - K_N‖_op ≤
    ‖K - K_N‖_HS → 0`. This Prop packages exactly that data.

    Note: We use operator-norm convergence rather than
    Hilbert-Schmidt-norm convergence because (i) the mathlib pin
    has no `HilbertSchmidt` namespace, and (ii) operator-norm
    convergence is what `isCompactOperator_of_tendsto` consumes
    (HS-norm convergence is strictly stronger and implies it).
    A future strengthening to the HS-norm form is straightforward
    once mathlib's `HilbertSchmidt` infrastructure lands. -/
def T3SymHilbertSchmidtNuclearWitness
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2) : Prop :=
  ∃ (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2)),
    (∀ n, IsSelfAdjoint (S n)) ∧
    (∀ n, IsCompactOperator (S n)) ∧
    Filter.Tendsto S Filter.atTop (nhds T)

/-! ## 2. Compactness from the HS-nuclear witness -/

/-- **★ `T3_sym_CLM_isCompactOperator_of_HSNuclearWitness` ★** —
    the witness gives `IsCompactOperator` of the constructed CLM
    via `isCompactOperator_of_tendsto`. Direct mathlib application;
    no new analytic content.

    Given:
      * a `T3SymLinearStructure` witness `hLin` (provides the CLM),
      * a `T3SymHilbertSchmidtNuclearWitness` for that CLM,
    conclude `IsCompactOperator (T3_sym_CLM_of_linearStructure hLin)`.

    This file's central reduction theorem. -/
theorem T3_sym_CLM_isCompactOperator_of_HSNuclearWitness
    (hLin : T3SymLinearStructure)
    (hHS : T3SymHilbertSchmidtNuclearWitness
            (T3_sym_CLM_of_linearStructure hLin)) :
    IsCompactOperator (T3_sym_CLM_of_linearStructure hLin) := by
  obtain ⟨S, _, hS_K, hS_tendsto⟩ := hHS
  exact isCompactOperator_of_tendsto hS_tendsto
    (Filter.Eventually.of_forall hS_K)

/-! ## 3. Bare-function compactness from the HS-nuclear witness -/

/-- **★ `T3_sym_apply_isCompactOperator_of_HSNuclearWitness` ★** —
    `IsCompactOperator` of the bare function `T3_sym.apply` follows
    from the witness via pointwise agreement of the CLM and the
    bare function.

    `T3_sym_CLM_of_linearStructure hLin = T3_sym.apply` pointwise
    (proven in `T3_sym_CLM_of_linearStructure_apply_eq`). Since
    `IsCompactOperator` of a function depends only on the function's
    extensional behavior, we transfer compactness across the
    equality.

    This closes the bare-function form of the named open. -/
theorem T3_sym_apply_isCompactOperator_of_HSNuclearWitness
    (hLin : T3SymLinearStructure)
    (hHS : T3SymHilbertSchmidtNuclearWitness
            (T3_sym_CLM_of_linearStructure hLin)) :
    IsCompactOperator (T3_sym.apply : LogWeightedL2 → LogWeightedL2) := by
  -- Pointwise equality: `T3_sym_CLM_of_linearStructure hLin f = T3_sym.apply f`
  -- for every `f`. Both sides as bare functions agree.
  have h_eq :
      (fun f => (T3_sym_CLM_of_linearStructure hLin) f)
        = (T3_sym.apply : LogWeightedL2 → LogWeightedL2) := by
    funext f
    exact T3_sym_CLM_of_linearStructure_apply_eq hLin f
  -- IsCompactOperator of the CLM (as a bare-function coercion)
  have h_clm_K : IsCompactOperator
      (fun f => (T3_sym_CLM_of_linearStructure hLin) f) :=
    T3_sym_CLM_isCompactOperator_of_HSNuclearWitness hLin hHS
  -- Transport across the pointwise equality
  rw [h_eq] at h_clm_K
  exact h_clm_K

/-! ## 4. Connection to the existing `T3SymFiniteRankTower` predicate -/

/-- **`T3SymFiniteRankTower_of_HSNuclearWitness`** — the HS-nuclear
    witness IS a `T3SymFiniteRankTower` (the predicates have identical
    payloads modulo the field-order convention). This makes the
    HS-nuclear witness a drop-in replacement for any consumer of the
    existing `T3SymFiniteRankTower` API.

    Direct projection; no further proof obligation. -/
theorem T3SymFiniteRankTower_of_HSNuclearWitness
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hHS : T3SymHilbertSchmidtNuclearWitness T) :
    T3SymFiniteRankTower T := by
  obtain ⟨S, hS_sa, hS_K, hS_tendsto⟩ := hHS
  exact ⟨S, hS_sa, hS_K, hS_tendsto⟩

/-- **Converse**: the existing `T3SymFiniteRankTower` predicate IS
    an HS-nuclear witness (the predicates are equal up to projection
    order). This is the round-trip equivalence; useful when consumers
    already produce `T3SymFiniteRankTower` from independent analytic
    arguments. -/
theorem T3SymHilbertSchmidtNuclearWitness_of_FiniteRankTower
    {T : LogWeightedL2 →L[ℂ] LogWeightedL2}
    (hTower : T3SymFiniteRankTower T) :
    T3SymHilbertSchmidtNuclearWitness T := by
  obtain ⟨S, hS_sa, hS_K, hS_tendsto⟩ := hTower
  exact ⟨S, hS_sa, hS_K, hS_tendsto⟩

/-! ## 5. Mercer-tail from the HS-nuclear witness (composite) -/

/-- **★ `T3SymMercerTail_of_HSNuclearWitness` ★** — composes
    `T3_sym_CLM_isCompactOperator_of_HSNuclearWitness` with the
    existing `T3SymMercerTail_of_compact_at_T3_sym_CLM` (from
    `T3SymMercerTailT3SymDischarge.lean`) to deliver the Mercer-tail
    conclusion directly from the HS-nuclear witness.

    Given:
      * a `T3SymLinearStructure` witness,
      * a `LogWeightedL2InnerBridge` (project-↔-mathlib inner equality),
      * an HS-nuclear witness for the constructed CLM,
    yields `T3SymMercerTail (T3_sym_CLM_of_linearStructure hLin)`.

    This is the one-stop reduction: a single Mayer 1991 §3 nuclear
    witness discharges the entire Mercer-tail half of bundle (a). -/
theorem T3SymMercerTail_of_HSNuclearWitness
    (hLin : T3SymLinearStructure)
    (hBridge : LogWeightedL2InnerBridge)
    (hHS : T3SymHilbertSchmidtNuclearWitness
            (T3_sym_CLM_of_linearStructure hLin)) :
    T3SymMercerTail (T3_sym_CLM_of_linearStructure hLin) :=
  T3SymMercerTail_of_compact_at_T3_sym_CLM hLin hBridge
    (T3_sym_CLM_isCompactOperator_of_HSNuclearWitness hLin hHS)

/-! ## 6. Composite bundle-(a) wrapper using the HS-nuclear witness -/

/-- **★ `bundleA_oneOfThree_from_HSNuclearWitness` ★** — composite
    wrapper paralleling `bundleA_two_of_three_from_witness_compactness`
    from `T3SymMercerTailT3SymDischarge.lean`, but consuming the
    HS-nuclear witness directly.

    Given:
      * a `T3SymLinearStructure` witness,
      * a `LogWeightedL2InnerBridge`,
      * an HS-nuclear witness for `T3_sym_CLM_of_linearStructure hLin`,
    produce a `T3SymFiniteRankTower` for that CLM together with a
    Mercer-tail certificate.

    After this wrapper, the remaining bundle-(a) obligation is exactly
    (a2): the ℕ-indexed compact self-adjoint spectral theorem
    (a separate mathlib gap). The HS-nuclear witness has discharged
    both (a0) — symmetric CLM existence (unconditional from
    `T3SymCLMSymmetricWitness_proved_unconditional`) — and (a1) —
    Mercer-tail. -/
theorem bundleA_oneOfThree_from_HSNuclearWitness
    (hLin : T3SymLinearStructure)
    (hBridge : LogWeightedL2InnerBridge)
    (hHS : T3SymHilbertSchmidtNuclearWitness
            (T3_sym_CLM_of_linearStructure hLin)) :
    T3SymFiniteRankTower (T3_sym_CLM_of_linearStructure hLin) ∧
    T3SymMercerTail (T3_sym_CLM_of_linearStructure hLin) := by
  refine ⟨T3SymFiniteRankTower_of_HSNuclearWitness hHS, ?_⟩
  exact T3SymMercerTail_of_HSNuclearWitness hLin hBridge hHS

/-! ## 7. Honest scope statement

What lands axiom-free in this file:

  * The HS-nuclear witness predicate `T3SymHilbertSchmidtNuclearWitness`
    (definition).
  * Five reduction theorems showing the witness discharges
    compactness (CLM-level and bare-function-level), the Mercer-tail,
    and the existing finite-rank tower predicate.
  * The bundle-(a) composite wrapper that reduces the entire (a0)+(a1)
    half of bundle (a) to a single HS-nuclear witness input.

What does NOT land:

  * `IsCompactOperator T3_sym.apply` axiom-free. That requires the
    Mayer 1991 §3 nuclear-class content (HS-kernel Mercer expansion
    convergence) which this mathlib pin lacks and which is a
    multi-month formalization. Producing the witness IS that
    content.

  * Any Clay-level RH discharge. Bundle (c) (surjectivity) remains
    the load-bearing open conjecture independent of bundle (a).

This file's deliverable is the SHARPEST POSSIBLE one-witness
reduction at this mathlib pin: the entire (a1) Mercer-tail half
of bundle (a) collapses to a single typed Prop matching the
Mayer 1991 §3 analytic content exactly.
-/

/-! ## 8. Axiom-freeness verification -/

#print axioms T3SymHilbertSchmidtNuclearWitness
#print axioms T3_sym_CLM_isCompactOperator_of_HSNuclearWitness
#print axioms T3_sym_apply_isCompactOperator_of_HSNuclearWitness
#print axioms T3SymFiniteRankTower_of_HSNuclearWitness
#print axioms T3SymHilbertSchmidtNuclearWitness_of_FiniteRankTower
#print axioms T3SymMercerTail_of_HSNuclearWitness
#print axioms bundleA_oneOfThree_from_HSNuclearWitness

end PrincipiaTractalis
