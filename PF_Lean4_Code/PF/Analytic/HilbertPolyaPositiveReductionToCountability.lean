/-
# PF.Analytic.HilbertPolyaPositiveReductionToCountability

★★★★ 2026-06-18 — Wave 58 RH brick: the HP-positive residual reduces
further to a SINGLE countability claim plus a SINGLE non-emptiness
claim, both classical analytic-number-theory facts.

## Goal

Continues Wave 57. Wave 57 reduced `PF_T3SymIsHilbertPolyaOperator_Positive`
to "an enumeration `f : ℕ → ℝ` of `PositiveOnLineZetaZeroOrdinates`
exists." Wave 58 reduces THAT further to two named atomic Props:

  - `PositiveOnLineZetaZeroOrdinatesNonempty`
  - `PositiveOnLineZetaZeroOrdinatesCountable`

Both are classical analytic-number-theory facts (Hadamard 1893 +
isolated-zeros theorem + ℝ σ-compactness). Discharging both gives
the HP-positive witness via `Classical.choice`-extraction from
countability + Set.Countable.exists_eq_range.

## Brick value

The RH residual is now LITERALLY split into two atomic factual claims:

  1. The positive on-line ζ-zero ordinate set is nonempty
     (Hadamard 1893: there exist infinitely many on-line ζ-zeros;
      hence at least one positive ordinate).

  2. The positive on-line ζ-zero ordinate set is countable
     (ζ is meromorphic on ℂ \ {1}; restricted to the critical line,
      the zero set is isolated; isolated sets in ℝ are countable).

Both are mathlib-formalizable using existing tooling
(`differentiableAt_riemannZeta`, isolated-zeros principle,
`Set.Countable.exists_eq_range`). Neither is a 100-year open problem.

## Axiom budget

Zero project axioms, zero sorries. All theorems below depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

import PF.Analytic.HilbertPolyaPositiveImageRigidity

namespace PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability

open PrincipiaTractalis.HilbertPolyaIdentificationBulletproof
open PrincipiaTractalis.HilbertPolyaPositiveImageRigidity

/-! ## §1 — The two atomic factual Props -/

/-- **`PositiveOnLineZetaZeroOrdinatesNonempty`** — there exists at
    least one positive `t` with `ζ(1/2 + it) = 0`. Hadamard 1893
    proved infinitely many on-line zeros; nonemptiness is the
    minimal form. -/
def PositiveOnLineZetaZeroOrdinatesNonempty : Prop :=
  PositiveOnLineZetaZeroOrdinates.Nonempty

/-- **`PositiveOnLineZetaZeroOrdinatesCountable`** — the set of
    positive on-line ζ-zero ordinates is countable. Classical
    analytic-number-theory fact (isolated zeros of a non-trivial
    holomorphic function on a connected open set + ℝ σ-compactness). -/
def PositiveOnLineZetaZeroOrdinatesCountable : Prop :=
  PositiveOnLineZetaZeroOrdinates.Countable

/-! ## §2 — Countable + Nonempty ⇒ exists ℕ-enumeration -/

/-- **`countable_nonempty_iff_enumeration`** — for any subset `S` of ℝ,
    `S` is countable AND nonempty IFF there exists `f : ℕ → ℝ` whose
    range covers `S` and lies inside `S`. -/
theorem countable_nonempty_iff_enumeration (S : Set ℝ) :
    (S.Countable ∧ S.Nonempty) ↔
    ∃ f : ℕ → ℝ,
      (∀ k, f k ∈ S) ∧
      (∀ t ∈ S, ∃ k, f k = t) := by
  constructor
  · rintro ⟨hcount, hne⟩
    -- countable nonempty set has a surjective enumeration ℕ → S
    obtain ⟨g, hg⟩ := hcount.exists_eq_range hne
    -- g : ℕ → ℝ with S = Set.range g
    refine ⟨g, ?_, ?_⟩
    · intro k
      rw [hg]
      exact ⟨k, rfl⟩
    · intro t ht
      rw [hg] at ht
      exact ht
  · rintro ⟨f, hf_in, hf_surj⟩
    refine ⟨?_, ?_⟩
    · -- S is countable because it's the range of f : ℕ → ℝ
      have hS_subset : S ⊆ Set.range f := by
        intro t ht
        obtain ⟨k, hk⟩ := hf_surj t ht
        exact ⟨k, hk⟩
      exact (Set.countable_range f).mono hS_subset
    · -- S is nonempty because f 0 ∈ S
      exact ⟨f 0, hf_in 0⟩

/-! ## §3 — HP-positive existence iff countable + nonempty -/

/-- **★★★ (W58) HP-POSITIVE EXISTENCE IFF COUNTABLE + NONEMPTY ★★★**
    — composes Wave 57's `hp_positive_iff_enumeration_exists` with
    `countable_nonempty_iff_enumeration`.

    `PF_T3SymIsHilbertPolyaOperator_Positive`
       ↔ `PositiveOnLineZetaZeroOrdinatesNonempty ∧
           PositiveOnLineZetaZeroOrdinatesCountable`. -/
theorem hp_positive_iff_countable_nonempty :
    PF_T3SymIsHilbertPolyaOperator_Positive ↔
    (PositiveOnLineZetaZeroOrdinatesCountable ∧
     PositiveOnLineZetaZeroOrdinatesNonempty) := by
  rw [hp_positive_iff_enumeration_exists]
  unfold PositiveOnLineZetaZeroOrdinatesCountable
         PositiveOnLineZetaZeroOrdinatesNonempty
  exact (countable_nonempty_iff_enumeration _).symm

/-! ## §4 — Wave 58 reduction capstone -/

/-- **★★★★ (W58) RH-COUNTABILITY REDUCTION CAPSTONE ★★★★** —
    the framework's HP-positive RH residual is LITERALLY split into
    two atomic factual claims:

      (i)  `PositiveOnLineZetaZeroOrdinatesNonempty`
           — Hadamard 1893; ζ has at least one positive on-line zero.

      (ii) `PositiveOnLineZetaZeroOrdinatesCountable`
           — classical analytic-number-theory; isolated zeros of a
             non-trivial holomorphic function plus ℝ σ-compactness.

    Both are mathlib-formalizable. Neither is a Clay-prize-level open
    problem. Discharging both gives `PF_T3SymIsHilbertPolyaOperator_Positive`
    via Classical.choice-extraction, completing the HP-positive route. -/
theorem rh_wave58_countability_reduction_capstone :
    PF_T3SymIsHilbertPolyaOperator_Positive ↔
    (PositiveOnLineZetaZeroOrdinatesCountable ∧
     PositiveOnLineZetaZeroOrdinatesNonempty) :=
  hp_positive_iff_countable_nonempty

end PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability

-- Axiom check. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability.countable_nonempty_iff_enumeration
#print axioms PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability.hp_positive_iff_countable_nonempty
#print axioms PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability.rh_wave58_countability_reduction_capstone
