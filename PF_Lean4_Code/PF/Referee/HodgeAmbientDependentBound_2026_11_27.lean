/-
# Hodge: the constant predicate, and the strengthening its own docstring asked for

**Date**: 2026-11-27 (Legion). Third of the four-Prop family; see the NS repoint
and the Yang–Mills gravestones of the same day.

`HodgeAlgebraicRepresentation (_H : HodgeAmbient) (_class_idx : ℕ)` takes an
ambient and a class index and uses **neither** — both binders are underscored.
Its three conjuncts are

* `∃ σ, sigma_c_arithmetic ≤ σ ∧ sigma_c_arithmetic + epsilon_quantum ≤ σ`,
  and since `epsilon_quantum := sigma_c - sigma_c_arithmetic` this is just
  `∃ σ, 6/π² ≤ σ ∧ 19/20 ≤ σ`;
* `∃ rank_bound : ℕ, rank_bound ≤ 20`;
* `∃ lam : ℝ, lam = π/(10φ)`.

Each is satisfiable outright, so the predicate is the **same proposition for
every variety and every Hodge class**. §1 proves that by `rfl` and derives the
collapse of `fractalHodgeCrystallization` from it.

## The repair was already specified — by us

The predicate's own docstring says:

> The `_H`/`_class_idx` arguments are not yet used in the body but are
> preserved in the signature so future strengthening (e.g. **rank-bound
> depending on `H.betti`**, σ-bound depending on `H.p`) can drop in without
> touching `hodge_via_fractal_resonance`.

`HodgeAmbient` is not a `Unit`: it carries `dim`, `p` and `betti` with
`p_le_dim` and `betti_pos`. So the proposed strengthening is expressible today,
and §2 does it: `HodgeRankBoundOnAmbient H := H.betti ≤ 20`, the Hankel rank
bound tied to the ambient exactly as suggested.

**And it has teeth, from content this corpus already proved.**
`Ch20Ch25NumericObstructions.k3_betti_decomposition` gives `1 + 20 + 1 = 22`
for a K3 surface, and `22 ≤ 20` is false. So the strengthened bound
*separates ambients*: it holds for a small one and fails for K3. That is the
first Hodge framework predicate in this corpus that can tell two varieties
apart, and it is why the strengthening is worth having rather than cosmetic.

§2 deliberately stops there. The σ-bound "depending on `H.p`" is **not** added,
because every form of it I could write is satisfied by `σ := 19/20`
independently of `p` — adding it would re-create the defect this file exists to
remove. One genuine conjunct beats three free ones.

## What this is not

Not a step toward Clay Hodge, and this axis cannot have one at this pin.
Measured in `Mathlib`: **0** files for `ChowGroup`, **0** for `AlgebraicCycle`,
**0** for `ComplexManifold`, and a single file mentioning Hodge. Algebraic
cycles cannot be written down, so the Clay statement cannot either —
ch25 says as much, and §3 records the measurement.

What §2 strengthens is the *framework* predicate, over the framework's own
typed ambient. Nothing upstream is renamed or deleted;
`HodgeAlgebraicRepresentation` keeps its name and its clients, and the
strengthened predicate is offered alongside rather than substituted in.
-/
import PF.MillenniumSixReductions
import PF.Ch20Ch25NumericObstructions

set_option autoImplicit false

namespace PF.Referee.HodgeAmbientDependentBound

open PrincipiaTractalis
open PrincipiaTractalis.MillenniumSix

/-! ## §1 — The predicate is constant -/

/-- **★ The same proposition for every ambient and every class index.**

    Proved by `rfl`: neither argument occurs in the body, so no instance of
    this predicate can distinguish one variety from another, or one Hodge
    class from another. -/
theorem hodgeAlgebraicRepresentation_is_constant
    (H H' : HodgeAmbient) (i j : ℕ) :
    HodgeAlgebraicRepresentation H i = HodgeAlgebraicRepresentation H' j := rfl

/-- **★ And it is equivalent to `True`.**

    Witnesses: `σ := 1`, `rank_bound := 0`, `lam := π/(10φ)`. The second
    conjunct of the body reduces to `19/20 ≤ σ` because
    `epsilon_quantum := sigma_c - sigma_c_arithmetic`. -/
theorem hodgeAlgebraicRepresentation_collapses (H : HodgeAmbient) (i : ℕ) :
    HodgeAlgebraicRepresentation H i ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨⟨1, ?_, ?_⟩, ⟨0, Nat.zero_le 20⟩, ⟨Real.pi / (10 * phi), rfl⟩⟩
    · have h : sigma_c_arithmetic = 6 / Real.pi ^ 2 := rfl
      rw [h, div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three, Real.pi_pos]
    · have h : sigma_c_arithmetic + epsilon_quantum = sigma_c := by
        unfold epsilon_quantum
        ring
      rw [h]
      unfold sigma_c
      norm_num

/-- **So the Ch 25 framework hypothesis collapses too.** -/
theorem fractalHodgeCrystallization_collapses (α : ℝ) :
    fractalHodgeCrystallization α ↔ True := by
  constructor
  · intro _
    trivial
  · intro _ _ H i
    exact (hodgeAlgebraicRepresentation_collapses H i).mpr trivial

/-! ## §2 — The strengthening the docstring proposed, with teeth -/

/-- **The Hankel rank bound, tied to the ambient** — the docstring's own
    suggestion, "rank-bound depending on `H.betti`", written down.

    Unlike `∃ rank_bound : ℕ, rank_bound ≤ 20`, this constrains the ambient
    rather than asserting the existence of a small number. -/
def HodgeRankBoundOnAmbient (H : HodgeAmbient) : Prop := H.betti ≤ 20

/-- A K3 surface as a `HodgeAmbient`: complex dimension `2`, `p = 1`, and
    second Betti number `22` — the corpus's own decomposition
    `1 + 20 + 1 = 22` from `Ch20Ch25NumericObstructions`. -/
def k3Ambient : HodgeAmbient where
  dim := 2
  p := 1
  betti := 22
  p_le_dim := by decide
  betti_pos := by decide

/-- A small ambient, for contrast: `dim = 3`, `p = 1`, `betti = 4`. -/
def smallAmbient : HodgeAmbient where
  dim := 3
  p := 1
  betti := 4
  p_le_dim := by decide
  betti_pos := by decide

/-- The K3 Betti number really is the corpus's `1 + 20 + 1`. -/
theorem k3Ambient_betti_eq : k3Ambient.betti = 1 + 20 + 1 := by decide

/-- **★ The bound holds for the small ambient.** -/
theorem rankBound_holds_smallAmbient : HodgeRankBoundOnAmbient smallAmbient := by
  unfold HodgeRankBoundOnAmbient
  decide

/-- **★★ And it FAILS for K3** — `22 ≤ 20` is false.

    This is the teeth. The strengthened predicate distinguishes two genuine
    ambients, which the constant predicate of §1 provably cannot do. -/
theorem rankBound_fails_k3Ambient : ¬ HodgeRankBoundOnAmbient k3Ambient := by
  unfold HodgeRankBoundOnAmbient
  decide

/-- **★★ So the strengthening is not vacuous, stated as the separation.**

    One ambient satisfies it and another does not. By
    `hodgeAlgebraicRepresentation_is_constant` no such pair exists for the
    original predicate, so this is a strict gain in discriminating power. -/
theorem strengthened_bound_separates_ambients :
    HodgeRankBoundOnAmbient smallAmbient ∧ ¬ HodgeRankBoundOnAmbient k3Ambient :=
  ⟨rankBound_holds_smallAmbient, rankBound_fails_k3Ambient⟩

/-- **The contrast, as one citable statement.**

    The original predicate cannot separate any two ambients; the strengthened
    bound separates these two. -/
theorem constant_predicate_cannot_separate_but_bound_can :
    (HodgeAlgebraicRepresentation smallAmbient 0
      = HodgeAlgebraicRepresentation k3Ambient 0)
    ∧ (HodgeRankBoundOnAmbient smallAmbient
        ∧ ¬ HodgeRankBoundOnAmbient k3Ambient) :=
  ⟨hodgeAlgebraicRepresentation_is_constant _ _ _ _,
   strengthened_bound_separates_ambients⟩

/-! ## §3 — The non-claim -/

/-- **This settles nothing about the Hodge conjecture.**

    `HodgeRankBoundOnAmbient` is a condition on the framework's typed
    ambient, not a statement about algebraic cycles on a complex projective
    variety — which cannot be written at this pin, mathlib having no Chow
    groups, no algebraic cycles and no complex manifolds. Recorded as the
    disjunction so §2 reads as a strengthening of a framework predicate and
    nothing more. -/
theorem no_verdict_on_hodge (H : HodgeAmbient) :
    HodgeRankBoundOnAmbient H ∨ ¬ HodgeRankBoundOnAmbient H :=
  em (HodgeRankBoundOnAmbient H)

end PF.Referee.HodgeAmbientDependentBound
