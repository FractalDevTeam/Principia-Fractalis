/-
# Yang-Mills Canonical Kernel — STRICT Operator-Monotone Cluster-Fix
  SHARP partial elimination: 1 strictly-realisable pairing,
                             3 STRUCTURALLY REFUTED pairings.

## Strategic context (2026-05-30, Wave 31 SHARPENING)

This file SHARPENS the Wave 31 operator-monotone narrow-out
(`PF.YangMillsCanonicalOperatorMonotoneKernel`) by replacing the
operator-monotone (non-decreasing) hypothesis with the STRICT
operator-monotone (strictly increasing) hypothesis — the natural
strengthening to the next level of the structural constraint
hierarchy:

    positivity → monotone → STRICT MONOTONE → operator-monotone
                                            → STRICT operator-monotone

Under strict operator-monotonicity (every operator-monotone function
that is moreover strictly increasing on its interval of definition),
the Wave 24 cluster-fix family on `M_cluster` (eigenvalues
`{1/2, 3/2}`) yields a SHARPER partial-elimination than Wave 31:

  ┌──────────────────┬──────────────────────────────────────────┐
  │ pairing          │ STRICT-monotone verdict                   │
  ├──────────────────┼──────────────────────────────────────────┤
  │ (1/2, 3/2) ptwse │ STRICTLY REALISABLE (identity, β = 1)    │
  │ (1/2, 1/2) coll- │ NEWLY REFUTED — needs f(1/2)=f(3/2)=1/2  │
  │ (3/2, 3/2) coll+ │ NEWLY REFUTED — needs f(1/2)=f(3/2)=3/2  │
  │ (3/2, 1/2) cross │ STRUCTURALLY REFUTED (anti-monotone)      │
  └──────────────────┴──────────────────────────────────────────┘

The two collapses, which were DEGENERATELY realisable under operator-
monotonicity (via constant functions), are now STRUCTURALLY REFUTED:
strict monotonicity forbids equal images at distinct arguments, so no
strictly monotone function can send both `1/2` and `3/2` to the same
target. Combined with the Wave 31 cross-swap refutation (which we
import and reuse), exactly ONE of the four pairings — the pointwise
identity — survives under strict operator-monotonicity.

## Honest scope

This is a STRUCTURAL SHARPENING of Wave 31, not a discharge of the
Yang–Mills mass-gap problem. The single surviving pairing (pointwise)
is realised by the IDENTITY map `f(x) = x` — a STRUCTURALLY TRIVIAL
operator. The result establishes the strict operator-monotone class
as the SHARPEST partial-elimination axis currently achievable at the
operator-monotonicity level: exactly one of four cluster pairings
survives, and the survivor's witness is structurally trivial.

## Mathematical core

The key observation is a one-line lemma about strictly increasing
functions on ℝ:

    f STRICTLY MONOTONE  ∧  a ≠ b  ⟹  f(a) ≠ f(b)

Applied to `a = 1/2`, `b = 3/2`, with target value `c ∈ {1/2, 3/2}`:

    f(1/2) = c  ∧  f(3/2) = c  ⟹  f(1/2) = f(3/2)  ⟹  (with strict)
                                                       1/2 = 3/2  →  ⊥

This is `StrictMono.injective` from Mathlib applied to a literal
cluster collision.

## What this file proves (all axiom-free)

  1. `strict_mono_cannot_collapse_low_on_cluster`: no strictly
     monotone `f : ℝ → ℝ` realises the collapse-low pairing
     `f(1/2) = 1/2 ∧ f(3/2) = 1/2`.
  2. `strict_mono_cannot_collapse_high_on_cluster`: same for
     collapse-high `f(1/2) = 3/2 ∧ f(3/2) = 3/2`.
  3. `strict_mono_cannot_cross_swap_on_cluster`: cross-swap is
     refuted at strict-monotone level too (re-derived from Wave 31's
     more general `Monotone` lemma after upgrading
     `StrictMono → Monotone`).
  4. POINTWISE pointwise positive witness (identity, strictly monotone).
  5. STRICT operator-monotone capstone
     `ym_canonical_strict_monotone_realises_cluster_fix_only_at_pointwise`:
     pointwise IN, all three other pairings STRUCTURALLY REFUTED.

ZERO project axioms; `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem.

Author: Pablo Cohen (with assistance). 2026-05-30 Wave 31 SHARPENING
(strict operator-monotone counterpart to the operator-monotone /
Loewner narrow-out of `PF.YangMillsCanonicalOperatorMonotoneKernel`).
-/

import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import PF.YangMillsCanonicalOperatorMonotoneKernel

namespace PrincipiaTractalis

/-! ## Part 1 — Generic strict-monotone refutation lemmas
    (inherited by the STRICT operator-monotone class).

A strictly monotone function `f : ℝ → ℝ` is injective on ℝ: if
`f(a) = f(b)` for `a ≠ b` then `f` could not be strictly increasing.
Applied to the cluster collisions `(1/2, 1/2)` and `(3/2, 3/2)` — both
of which demand `f(1/2) = f(3/2)` — this refutes both collapse
pairings IMMEDIATELY.

These lemmas are stated in their full `StrictMono`-generic form, so
the conclusions apply to the entire STRICT operator-monotone class
(every strictly-increasing operator-monotone function on ℝ — strict
operator-monotone is a strict subclass of operator-monotone, hence
of monotone non-decreasing). -/

/-- **STRUCTURAL: no strictly-monotone function realises the
    collapse-low pairing** (axiom-free).

    If `f : ℝ → ℝ` is strictly monotone, then `f` cannot send BOTH
    `1/2 ↦ 1/2` and `3/2 ↦ 1/2`: this would force
    `f(1/2) = f(3/2) = 1/2`, contradicting injectivity of `f` on the
    distinct arguments `1/2 ≠ 3/2`.

    Since every STRICT operator-monotone function is strictly
    monotone, this REFUTES the collapse-low Wave 24 cluster-fix
    pairing for the entire strict operator-monotone class. -/
theorem strict_mono_cannot_collapse_low_on_cluster
    (f : ℝ → ℝ) (hf : StrictMono f) :
    ¬ (f (1/2) = 1/2 ∧ f (3/2) = 1/2) := by
  intro ⟨h_half, h_three_halves⟩
  -- From the two equations, both images equal 1/2.
  have h_eq : f (1/2) = f (3/2) := by rw [h_half, h_three_halves]
  -- Strict monotonicity is injective; but 1/2 ≠ 3/2.
  have h_inj : (1/2 : ℝ) = 3/2 := hf.injective h_eq
  linarith

/-- **STRUCTURAL: no strictly-monotone function realises the
    collapse-high pairing** (axiom-free).

    Symmetric to the collapse-low case: if `f : ℝ → ℝ` is strictly
    monotone, then `f` cannot send BOTH `1/2 ↦ 3/2` and `3/2 ↦ 3/2`,
    by injectivity on the distinct arguments `1/2 ≠ 3/2`. -/
theorem strict_mono_cannot_collapse_high_on_cluster
    (f : ℝ → ℝ) (hf : StrictMono f) :
    ¬ (f (1/2) = 3/2 ∧ f (3/2) = 3/2) := by
  intro ⟨h_half, h_three_halves⟩
  have h_eq : f (1/2) = f (3/2) := by rw [h_half, h_three_halves]
  have h_inj : (1/2 : ℝ) = 3/2 := hf.injective h_eq
  linarith

/-- **STRUCTURAL: no strictly-monotone function realises the
    cross-swap pairing** (axiom-free).

    Re-derived from the Wave 31 `Monotone`-generic refutation
    `monotone_nondec_cannot_cross_swap_on_cluster` by promoting the
    `StrictMono` hypothesis to `Monotone` via `StrictMono.monotone`. -/
theorem strict_mono_cannot_cross_swap_on_cluster
    (f : ℝ → ℝ) (hf : StrictMono f) :
    ¬ (f (1/2) = 3/2 ∧ f (3/2) = 1/2) :=
  monotone_nondec_cannot_cross_swap_on_cluster f hf.monotone

/-! ## Part 2 — The pointwise pairing remains realisable
    (the unique survivor under strict operator-monotonicity).

The identity `f(x) = x` is the canonical example of a strictly
monotone (and a fortiori operator-monotone) function on ℝ. It maps
`1/2 ↦ 1/2` and `3/2 ↦ 3/2`, realising the pointwise Wave 24 cluster
pairing.

The witness is structurally trivial — the IDENTITY map. This honest
scope is documented explicitly: strict operator-monotonicity admits
exactly ONE Wave 24 cluster pairing, and the realising operator is
the identity. -/

/-- **The identity function on ℝ is strictly monotone** (axiom-free). -/
theorem id_real_strict_mono : StrictMono (fun x : ℝ => x) := by
  intro x y hxy; exact hxy

/-- **Identity pointwise witness — lower image** (axiom-free):
    `(fun x => x) (1/2) = 1/2`. -/
theorem id_pointwise_at_half : (fun x : ℝ => x) (1/2) = 1/2 := rfl

/-- **Identity pointwise witness — upper image** (axiom-free):
    `(fun x => x) (3/2) = 3/2`. -/
theorem id_pointwise_at_three_halves : (fun x : ℝ => x) (3/2) = 3/2 := rfl

/-- **JOINT WITNESS: identity realises the pointwise pairing**
    (axiom-free). -/
theorem id_realises_pointwise :
    (fun x : ℝ => x) (1/2) = 1/2 ∧ (fun x : ℝ => x) (3/2) = 3/2 :=
  ⟨id_pointwise_at_half, id_pointwise_at_three_halves⟩

/-! ## Part 3 — Application to the linear sub-family
    `linearMonotoneMap α β` with `β > 0`.

Under STRICT operator-monotonicity the constraint `β ≥ 0` from
Wave 31 sharpens to `β > 0` (a constant function with `β = 0` is
NOT strictly monotone). With `β > 0` the linear map
`f(x) = α + β·x` is strictly monotone on ℝ, and the structural
refutations of Part 1 apply. -/

/-- **Linear maps with `β > 0` are strictly monotone** (axiom-free). -/
theorem linearMonotoneMap_strict_mono (alpha beta : ℝ) (hβ : 0 < beta) :
    StrictMono (linearMonotoneMap alpha beta) := by
  intro x y hxy
  unfold linearMonotoneMap
  have : beta * x < beta * y := (mul_lt_mul_left hβ).mpr hxy
  linarith

/-- **STRUCTURAL: no `linearMonotoneMap α β` with `β > 0` realises the
    collapse-low pairing** (axiom-free). -/
theorem linearMonotone_strict_cannot_collapse_low
    (alpha beta : ℝ) (hβ : 0 < beta) :
    ¬ (linearMonotoneMap alpha beta (1/2) = 1/2 ∧
       linearMonotoneMap alpha beta (3/2) = 1/2) :=
  strict_mono_cannot_collapse_low_on_cluster
    (linearMonotoneMap alpha beta) (linearMonotoneMap_strict_mono alpha beta hβ)

/-- **STRUCTURAL: no `linearMonotoneMap α β` with `β > 0` realises the
    collapse-high pairing** (axiom-free). -/
theorem linearMonotone_strict_cannot_collapse_high
    (alpha beta : ℝ) (hβ : 0 < beta) :
    ¬ (linearMonotoneMap alpha beta (1/2) = 3/2 ∧
       linearMonotoneMap alpha beta (3/2) = 3/2) :=
  strict_mono_cannot_collapse_high_on_cluster
    (linearMonotoneMap alpha beta) (linearMonotoneMap_strict_mono alpha beta hβ)

/-- **STRUCTURAL: no `linearMonotoneMap α β` with `β > 0` realises the
    cross-swap pairing** (axiom-free). -/
theorem linearMonotone_strict_cannot_cross_swap
    (alpha beta : ℝ) (hβ : 0 < beta) :
    ¬ (linearMonotoneMap alpha beta (1/2) = 3/2 ∧
       linearMonotoneMap alpha beta (3/2) = 1/2) :=
  strict_mono_cannot_cross_swap_on_cluster
    (linearMonotoneMap alpha beta) (linearMonotoneMap_strict_mono alpha beta hβ)

/-! ## Part 4 — Strategic capstone: SHARP partial elimination.

Strict operator-monotonicity yields the SHARPEST partial-elimination
result in the YM canonical-operator program: exactly ONE of the four
Wave 24 cluster pairings (the pointwise pairing, realised by the
identity) survives; the other three are structurally REFUTED.

  ┌──────────────────┬──────────────────────────────────────────┐
  │ pairing          │ STRICT operator-monotone verdict          │
  ├──────────────────┼──────────────────────────────────────────┤
  │ (1/2, 3/2) ptwse │ STRICTLY REALISABLE (identity, β = 1)    │
  │ (1/2, 1/2) coll- │ STRUCTURALLY REFUTED (injectivity)        │
  │ (3/2, 3/2) coll+ │ STRUCTURALLY REFUTED (injectivity)        │
  │ (3/2, 1/2) cross │ STRUCTURALLY REFUTED (anti-monotone)      │
  └──────────────────┴──────────────────────────────────────────┘

Combined with Wave 31 (which had the cross-swap refuted but admitted
both collapses degenerately), this completes the partial-elimination
axis at the monotonicity level. -/

/-- **★★★ STRICT operator-monotone canonical-construction yields the
    SHARP Wave 24 cluster-fix verdict — strategic capstone**
    (axiom-free).

    The STRICT operator-monotone class (every operator-monotone
    function that is moreover strictly increasing on its interval of
    definition), instantiated as the linear sub-family
    `f(x) = α + β·x` with `β > 0`, realises the Wave 24 cluster-fix
    pairings as follows:

      (1/2, 3/2) POINTWISE   : STRICTLY realisable — the IDENTITY
                               `f(x) = x` is a strict-monotone
                               witness sending `1/2 ↦ 1/2` and
                               `3/2 ↦ 3/2`.
      (1/2, 1/2) COLLAPSE-LO : STRUCTURALLY REFUTED — strict
                               monotonicity is injective, but the
                               collapse demands `f(1/2) = f(3/2)`
                               on the distinct cluster centres
                               `1/2 ≠ 3/2`.
      (3/2, 3/2) COLLAPSE-HI : STRUCTURALLY REFUTED — same
                               injectivity argument.
      (3/2, 1/2) CROSS-SWAP  : STRUCTURALLY REFUTED — strict
                               monotonicity is monotone non-
                               decreasing, contradicting the
                               anti-monotone cross-swap demand
                               (inherited from Wave 31).

    OUTCOME (Wave 31 SHARPENING): strict operator-monotonicity refutes
    THREE of the four Wave 24 cluster pairings — only the pointwise
    pairing survives, and its witness is structurally trivial (the
    identity). This is the SHARPEST partial-elimination result
    currently achievable at the operator-monotonicity level.

    Strategic context: combined with Wave 31, this completes the
    partial-elimination axis for monotonicity-based operator-level
    constraints. The constraint hierarchy

        positivity → monotone → STRICT monotone
                              → operator-monotone
                              → STRICT operator-monotone

    has been traversed; the sharpest narrow-out is THREE of four
    pairings refuted, ONE pointwise pairing surviving via identity.

    Honest scope: this does NOT discharge the Yang–Mills mass-gap
    problem. The pointwise pairing's surviving realisation is the
    identity map — structurally trivial. The result is a STRUCTURAL
    SHARPENING of Wave 31, not a Millennium-level result. The
    Loewner / Nevanlinna–Herglotz representation underlying the
    operator-monotone class is invoked only at the level of
    monotonicity (the basic Loewner property); the strict version
    is the natural strengthening to the next level of the structural
    constraint hierarchy. -/
theorem ym_canonical_strict_monotone_realises_cluster_fix_only_at_pointwise :
    -- (a) Pointwise pairing (1/2, 3/2) strictly realisable by the
    --     identity (strict-monotone witness).
    ((fun x : ℝ => x) (1/2) = 1/2 ∧ (fun x : ℝ => x) (3/2) = 3/2) ∧
    -- (b) STRUCTURAL (generic strict-monotone form): no strictly-
    --     monotone `f : ℝ → ℝ` realises the collapse-low pairing.
    (∀ f : ℝ → ℝ, StrictMono f →
       ¬ (f (1/2) = 1/2 ∧ f (3/2) = 1/2)) ∧
    -- (c) STRUCTURAL (generic strict-monotone form): no strictly-
    --     monotone `f : ℝ → ℝ` realises the collapse-high pairing.
    (∀ f : ℝ → ℝ, StrictMono f →
       ¬ (f (1/2) = 3/2 ∧ f (3/2) = 3/2)) ∧
    -- (d) STRUCTURAL (generic strict-monotone form): no strictly-
    --     monotone `f : ℝ → ℝ` realises the cross-swap pairing
    --     (inherited from Wave 31 via StrictMono.monotone).
    (∀ f : ℝ → ℝ, StrictMono f →
       ¬ (f (1/2) = 3/2 ∧ f (3/2) = 1/2)) ∧
    -- (e) STRUCTURAL refutations specialised to the linear sub-family
    --     with `β > 0` (strict operator-monotone canonical form):
    --     all three non-pointwise pairings are refuted.
    (∀ alpha beta : ℝ, 0 < beta →
       ¬ (linearMonotoneMap alpha beta (1/2) = 1/2 ∧
          linearMonotoneMap alpha beta (3/2) = 1/2)) ∧
    (∀ alpha beta : ℝ, 0 < beta →
       ¬ (linearMonotoneMap alpha beta (1/2) = 3/2 ∧
          linearMonotoneMap alpha beta (3/2) = 3/2)) ∧
    (∀ alpha beta : ℝ, 0 < beta →
       ¬ (linearMonotoneMap alpha beta (1/2) = 3/2 ∧
          linearMonotoneMap alpha beta (3/2) = 1/2)) ∧
    -- (f) The pointwise witness is itself strictly monotone (the
    --     identity is the canonical strict-monotone operator).
    StrictMono (fun x : ℝ => x) :=
  ⟨id_realises_pointwise,
   strict_mono_cannot_collapse_low_on_cluster,
   strict_mono_cannot_collapse_high_on_cluster,
   strict_mono_cannot_cross_swap_on_cluster,
   linearMonotone_strict_cannot_collapse_low,
   linearMonotone_strict_cannot_collapse_high,
   linearMonotone_strict_cannot_cross_swap,
   id_real_strict_mono⟩

/-! ## Part 5 — Axiom-freeness verification -/

#print axioms strict_mono_cannot_collapse_low_on_cluster
#print axioms strict_mono_cannot_collapse_high_on_cluster
#print axioms strict_mono_cannot_cross_swap_on_cluster
#print axioms id_real_strict_mono
#print axioms id_pointwise_at_half
#print axioms id_pointwise_at_three_halves
#print axioms id_realises_pointwise
#print axioms linearMonotoneMap_strict_mono
#print axioms linearMonotone_strict_cannot_collapse_low
#print axioms linearMonotone_strict_cannot_collapse_high
#print axioms linearMonotone_strict_cannot_cross_swap
#print axioms ym_canonical_strict_monotone_realises_cluster_fix_only_at_pointwise

end PrincipiaTractalis
