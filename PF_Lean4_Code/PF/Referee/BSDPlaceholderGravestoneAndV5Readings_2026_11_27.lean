/-
# BSD: the capstone's conjunct is `True`, and the V5 tower it never reaches

**Date**: 2026-11-27 (Legion). Fourth and last of the four-Prop family; see the
NS repoint, the Yang–Mills gravestones and the Hodge ambient-dependent bound of
the same day.

## The measurement

`BSD_equality_holds (_E : WeierstrassCurve ℚ) : Prop := True` — a genuine
quantifier over mathlib's real curve type, with a body that uses neither the
curve nor anything else. So `BSDConjecture := ∀ E, BSD_equality_holds E` is
`∀ E, True`, and that is the conjunct
`six_millennium_problems_via_fractal_resonance` delivers at
`MillenniumSixReductions:1310`.

This was never hidden. Twenty-plus docstrings across the BSD files say
`BSD_equality_holds := True` in exactly those words, and four of them say
"**NOT** a discharge of the universal `BSDConjecture` Prop". The prose
disclosure is thorough and predates this file.

What was missing is the kernel statement. Measured in the corpus before
writing a line: **no** declaration anywhere proves `BSDConjecture ↔ True`, and
**no** declaration mentions both a V5 object and `BSD_equality_holds`. §1
supplies the first; the rest of this file addresses the second.

## The two disconnected worlds

`PF/Referee/BSDCapstoneTypedBridgeV5.lean` is 508 lines of real content:
`manuscriptRankV5` is a twenty-branch case split over `WeierstrassCurve ℚ`
returning the literature's rank for twenty named curves, with per-curve Heegner
points verified on-curve and explicit discriminants. It routes to Clay through
`StandardClayStatements.Clay_BSD_Standard PF_BSDEncodingV5`.

`BSDConjecture` in `MillenniumSixReductions` routes nowhere, because it is
`True`. The capstone conjoins the second and never mentions the first. That gap
is the finding, and it is why BSD — the axis with the most genuine arithmetic in
this corpus — presents the weakest conjunct in the capstone.

## What V5's rank equality actually says

`PF_BSD_V5_refereeScope` conjunct (H1) is "V5 substrate equality is provable
axiom-free". It is, and its own docstring is candid about why: `algebraicRankV5`
and `analyticRankV5` are *both defined as* `manuscriptRankV5`, so the equality
is `rfl`. §2 states that sharply — the two projections are **one function**, so
the equality compares a function with itself and carries no arithmetic. A
referee will reach this in one `unfold`; better that the corpus says it first.

## Where V5's content really is, and the teeth

In the *readings*, not the equality. And the readings are discriminating, which
§3 proves: `manuscriptRankV5 E_rank_zero = 0` and
`manuscriptRankV5 E_rank_one = 1`, so the V5 projection **separates two curves
that `BSD_equality_holds` identifies** — the latter being literally the same
proposition on both. The separation is real arithmetic over mathlib's own type:
`E_rank_zero = ⟨0,0,0,-1,0⟩` is LMFDB `32.a3` with `Δ = 64`, and
`E_rank_one = ⟨0,0,1,-1,0⟩` is LMFDB `37.a1` with `Δ = 37`, both already proved
in `BSDGaloisPairConcordance`.

Reaching the rank-1 branch needs the five disequalities that guard it, so §3
proves them: `E_rank_one` differs from each of the five rank-0 curves ahead of
it in a single Weierstrass coefficient.

**A docstring repair comes with it.** `v5_E_91a1_surfaced` is documented as
"V5 projects to `1`", but its *statement* is only
`∃ cert : RankCertificateTyped E_91a1, cert.r = 1` — existence of a certificate,
not a value of `manuscriptRankV5`. None of the three `v5_*_surfaced` theorems
state the projection they are described as making. `rankV5_E_rank_one` is the
first theorem in the corpus that states a `manuscriptRankV5` value at a
positive rank, so the claim now exists in the kernel for one curve. The other
nineteen branches are reachable the same way and are left for the per-curve
files, where the coefficients live.

## What this is not

Not a step toward Clay BSD, and the blocker is measured, not guessed: mathlib
has **no** elliptic-curve L-function — 0 files for `hasseWeil`, nothing for
`L_E` in `LSeries/`. The analytic rank cannot be *defined*, so the order of
vanishing of `L_E` at `s = 1` cannot be written down, so the Clay equality
cannot be stated. `analyticRankV5` is named for the quantity it stands in for,
not computed from an L-function, and that is the whole reason (H1) is `rfl`.

Nothing upstream is renamed, weakened or deleted. `BSD_equality_holds` keeps
its name and all of its clients; `bsd_via_fractal_resonance` and the capstone
are untouched. §4 bundles the four facts a referee needs into one theorem.
-/
import PF.MillenniumSixReductions
import PF.Referee.BSDCapstoneTypedBridgeV5

set_option autoImplicit false

namespace PF.Referee.BSDPlaceholderGravestone

open PrincipiaTractalis
open PrincipiaTractalis.MillenniumSix
open PrincipiaTractalis.BSDGaloisPairConcordance
open PrincipiaTractalis.BSD_MultiCMRankZeroBatch
open PF.Referee.BSDCapstoneTypedBridgeV5

/-! ## §1 — The gravestone

The placeholder, the conjecture it builds and the hypothesis that is supposed
to imply it all collapse. Each proof is the shortest one available, which is
the point: there is nothing to discharge.
-/

/-- **★ The same proposition for every curve.**

    Proved by `rfl`: the curve argument is underscored and does not occur in
    the body, so no instance of this predicate can tell two elliptic curves
    apart. -/
theorem bsd_equality_holds_is_constant (E E' : WeierstrassCurve ℚ) :
    BSD_equality_holds E = BSD_equality_holds E' := rfl

/-- The placeholder is `True` at every curve. -/
theorem bsd_equality_holds_collapses (E : WeierstrassCurve ℚ) :
    BSD_equality_holds E ↔ True := Iff.rfl

/-- **★ The capstone's BSD conjunct is `True`.**

    `BSDConjecture := ∀ E, BSD_equality_holds E`, and the body is constantly
    `True`, so the universal quantifier over `WeierstrassCurve ℚ` — genuine as
    a quantifier — ranges over a predicate with no content. -/
theorem bsdConjecture_collapses : BSDConjecture ↔ True :=
  ⟨fun _ => trivial, fun _ _ => trivial⟩

/-- The Ch 24 load-bearing hypothesis collapses too: its body is
    `α = 3π/4 → ∀ E, True`. -/
theorem fractalBSDRankEquality_collapses (α : ℝ) :
    fractalBSDRankEquality α ↔ True :=
  ⟨fun _ => trivial, fun _ _ _ => trivial⟩

/-- **The α-dependence transports nothing.** The hypothesis holds at every
    real `α`, so `α = 3π/4` — the manuscript's BSD resonance value — is not a
    constraint the Lean statement can feel. -/
theorem fractalBSDRankEquality_independent_of_alpha (α α' : ℝ) :
    fractalBSDRankEquality α ↔ fractalBSDRankEquality α' :=
  (fractalBSDRankEquality_collapses α).trans
    (fractalBSDRankEquality_collapses α').symm

/-- The conclusion of `bsd_via_fractal_resonance` is provable with no
    hypothesis at all. -/
theorem bsdConjecture_holds_without_hypothesis : BSDConjecture :=
  fun _E => trivial

/-- **★ The reduction's hypothesis is dead.** `bsd_via_fractal_resonance`
    takes `fractalBSDRankEquality (alpha_at_enum .BSD)` and concludes
    `BSDConjecture`; both sides are `True`, so the implication is the identity
    on a trivial proposition and the hypothesis is never load-bearing. -/
theorem bsd_reduction_transports_nothing :
    BSDConjecture ∧ (fractalBSDRankEquality (3 * Real.pi / 4) ↔ True) :=
  ⟨bsdConjecture_holds_without_hypothesis, fractalBSDRankEquality_collapses _⟩

/-! ## §2 — V5's rank equality is one function compared with itself -/

/-- **★ The two V5 projections are the same function.**

    `algebraicRankV5 := manuscriptRankV5` and
    `analyticRankV5 := manuscriptRankV5`, so this is `rfl` at the level of
    functions — strictly sharper than the pointwise
    `algebraicRankV5_eq_analyticRankV5`, and it makes explicit why that
    theorem is free. The rank equality is not evidence about elliptic curves;
    it is evidence that one definition was used twice. -/
theorem rankV5_projections_are_one_function :
    algebraicRankV5 = analyticRankV5 := rfl

/-- Restated as the referee will want it: V5's (H1) conjunct follows from
    §2 alone, with no arithmetic input. -/
theorem v5_rank_equality_is_free :
    (algebraicRankV5 = analyticRankV5) ∧
    (∀ E : WeierstrassCurve ℚ, algebraicRankV5 E = analyticRankV5 E) :=
  ⟨rankV5_projections_are_one_function, fun _ => rfl⟩

/-! ## §3 — The readings, and the teeth

The five disequalities guarding the rank-1 branch of `manuscriptRankV5`. Each
is settled by a single Weierstrass coefficient, listed in the docstring so the
reader can check it against LMFDB without opening another file.
-/

/-- `E_rank_one = ⟨0,0,1,-1,0⟩` vs `E_rank_zero = ⟨0,0,0,-1,0⟩`: `a₃`. -/
theorem E_rank_one_ne_E_rank_zero : E_rank_one ≠ E_rank_zero := by
  intro h
  have ha : (E_rank_one.a₃ : ℚ) = E_rank_zero.a₃ := by rw [h]
  simp [E_rank_one, E_rank_zero] at ha

/-- `E_rank_one = ⟨0,0,1,-1,0⟩` vs `E_36a1 = ⟨0,0,0,0,1⟩`: `a₃`. -/
theorem E_rank_one_ne_E_36a1 : E_rank_one ≠ E_36a1 := by
  intro h
  have ha : (E_rank_one.a₃ : ℚ) = E_36a1.a₃ := by rw [h]
  simp [E_rank_one, E_36a1] at ha

/-- `E_rank_one = ⟨0,0,1,-1,0⟩` vs `E_49a1 = ⟨1,-1,0,-2,-1⟩`: `a₁`. -/
theorem E_rank_one_ne_E_49a1 : E_rank_one ≠ E_49a1 := by
  intro h
  have ha : (E_rank_one.a₁ : ℚ) = E_49a1.a₁ := by rw [h]
  simp [E_rank_one, E_49a1] at ha

/-- `E_rank_one = ⟨0,0,1,-1,0⟩` vs `E_121b1 = ⟨0,-1,1,-7,10⟩`: `a₂`. -/
theorem E_rank_one_ne_E_121b1 : E_rank_one ≠ E_121b1 := by
  intro h
  have ha : (E_rank_one.a₂ : ℚ) = E_121b1.a₂ := by rw [h]
  simp [E_rank_one, E_121b1] at ha

/-- `E_rank_one = ⟨0,0,1,-1,0⟩` vs `E_144a1 = ⟨0,0,0,0,-27⟩`: `a₃`. -/
theorem E_rank_one_ne_E_144a1 : E_rank_one ≠ E_144a1 := by
  intro h
  have ha : (E_rank_one.a₃ : ℚ) = E_144a1.a₃ := by rw [h]
  simp [E_rank_one, E_144a1] at ha

/-- **V5 reads `0` at `E_rank_zero`** (LMFDB `32.a3`, Coates–Wiles 1977).
    The first branch of the case split, so this is immediate. -/
theorem rankV5_E_rank_zero : manuscriptRankV5 E_rank_zero = 0 := by
  unfold manuscriptRankV5
  rw [if_pos rfl]

/-- **★ V5 reads `1` at `E_rank_one`** (LMFDB `37.a1`, Gross–Zagier 1986 +
    Kolyvagin 1990).

    The first theorem in this corpus stating a `manuscriptRankV5` value at a
    positive rank. Reaching the branch requires stepping past the five
    rank-0 curves ahead of it, which is what §3's disequalities are for. -/
theorem rankV5_E_rank_one : manuscriptRankV5 E_rank_one = 1 := by
  unfold manuscriptRankV5
  rw [if_neg E_rank_one_ne_E_rank_zero, if_neg E_rank_one_ne_E_36a1,
      if_neg E_rank_one_ne_E_49a1, if_neg E_rank_one_ne_E_121b1,
      if_neg E_rank_one_ne_E_144a1, if_pos rfl]

/-- **★ The V5 reading separates two curves.** `0 ≠ 1`. -/
theorem rankV5_separates_rank_zero_from_rank_one :
    manuscriptRankV5 E_rank_zero ≠ manuscriptRankV5 E_rank_one := by
  rw [rankV5_E_rank_zero, rankV5_E_rank_one]
  norm_num

/-- The two curves really are distinct objects, derived from the readings
    rather than assumed — a function cannot take two values at one argument.
    (`BSDGaloisPairConcordance.E_rank_zero_ne_E_rank_one_via_Δ` proves the same
    thing from `Δ = 64` vs `Δ = 37`; this route needs no discriminant.) -/
theorem E_rank_zero_ne_E_rank_one : E_rank_zero ≠ E_rank_one := fun h =>
  rankV5_separates_rank_zero_from_rank_one (congrArg manuscriptRankV5 h)

/-- **★★ THE TEETH ★★**

    `BSD_equality_holds` is the *same proposition* at `E_rank_zero` and
    `E_rank_one` — a rank-0 CM curve and a rank-1 Heegner curve, with
    different discriminants and different Mordell–Weil ranks in the
    literature. The V5 projection tells them apart; the placeholder cannot.

    This is the precise sense in which the capstone's BSD conjunct is weaker
    than the arithmetic the corpus already owns. -/
theorem placeholder_identifies_what_rankV5_separates :
    (BSD_equality_holds E_rank_zero ↔ BSD_equality_holds E_rank_one) ∧
    manuscriptRankV5 E_rank_zero ≠ manuscriptRankV5 E_rank_one :=
  ⟨Iff.rfl, rankV5_separates_rank_zero_from_rank_one⟩

/-! ## §4 — The disclosure a referee needs, in one theorem -/

/-- **★★★ The BSD axis, stated honestly in the kernel ★★★**

    Four machine-checked facts, in the order a referee will want them:

    1. the capstone's BSD conjunct is `True`;
    2. V5's rank equality is one function compared with itself, so it is free;
    3. V5's *readings* nevertheless separate a rank-0 from a rank-1 curve —
       this is where the genuine arithmetic lives;
    4. off the twenty discharged curves the reading is `0`, so the residual is
       every other curve in `WeierstrassCurve ℚ`.

    Read together: BSD has real, axiom-free, curve-specific arithmetic, and it
    is **not** connected to the Millennium capstone, whose BSD slot is
    trivial. Conjunct 4 is `v5_residual_is_zero_on_undischarged`, re-exported
    here so the scope statement is self-contained. -/
theorem bsd_axis_scope_disclosure :
    (BSDConjecture ↔ True) ∧
    (algebraicRankV5 = analyticRankV5) ∧
    (manuscriptRankV5 E_rank_zero ≠ manuscriptRankV5 E_rank_one) ∧
    (∀ E : WeierstrassCurve ℚ, ¬ isV5Discharged E → manuscriptRankV5 E = 0) :=
  ⟨bsdConjecture_collapses,
   rankV5_projections_are_one_function,
   rankV5_separates_rank_zero_from_rank_one,
   v5_residual_is_zero_on_undischarged⟩

#check @bsd_equality_holds_is_constant
#check @bsdConjecture_collapses
#check @rankV5_projections_are_one_function
#check @rankV5_E_rank_one
#check @placeholder_identifies_what_rankV5_separates
#check @bsd_axis_scope_disclosure

#print axioms bsd_equality_holds_is_constant
#print axioms bsdConjecture_collapses
#print axioms fractalBSDRankEquality_collapses
#print axioms fractalBSDRankEquality_independent_of_alpha
#print axioms bsd_reduction_transports_nothing
#print axioms rankV5_projections_are_one_function
#print axioms rankV5_E_rank_zero
#print axioms rankV5_E_rank_one
#print axioms rankV5_separates_rank_zero_from_rank_one
#print axioms placeholder_identifies_what_rankV5_separates
#print axioms bsd_axis_scope_disclosure

end PF.Referee.BSDPlaceholderGravestone
