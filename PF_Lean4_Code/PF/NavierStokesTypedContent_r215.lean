/-
# r215: what the corpus's typed Navier–Stokes predicate actually contains.

★ 2026-08-08 r215 — an ADDITIVE, kernel-visible disclosure. Nothing is deleted,
weakened, or renamed. The point is to put the truth in the kernel, so that
anyone who cites the NS layer upstream finds this file's theorems next to it. ★

## What this file is

`PF/NavierStokes/Wave58TimeGlobalExistenceUpgrade.lean` (lines 108–160) defines
a typed predicate `NS_Solution u u0` on `u : 𝓢(ℝ⁴, ℝ³)` as the conjunction of
four named clauses, and then

    NS3DTimeGlobalSmoothSolution u0 : Prop := ∃ u, NS_Solution u u0 .

Its docstring at `Wave58TimeGlobalExistenceUpgrade.lean:167` asserts that this
is "REAL PDE EXISTENCE CONTENT (NOT `True`)". That claim is accurate in exactly
one narrow sense: the Prop is not literally `True`. It is not PDE content.

This file computes, in the kernel, what the predicate is.

## The four clauses, at source

    initialDataMatch u u0         : ∀ x, u (time-0 slice at x) = u0.velocity x
    divergenceFreePreserved _u u0 : u0.isDivFree        -- `u` is UNDERSCORE-DISCARDED
    forwardTimeDomain u           : ∀ y, ∃ z, u y = z   -- true for ANY function
    smoothness u                  : ∃ M, 0 ≤ M ∧ ∀ y, ‖u y‖ ≤ M   -- BOUNDEDNESS

* **`NS_Solution` contains NO time derivative, NO convective term `u·∇u`, NO
  pressure, NO Laplacian, and NO viscosity.** It is therefore not the
  Navier–Stokes equation, and no theorem about it is a theorem about
  Navier–Stokes.
* Two of the four clauses (`forwardTimeDomain`, `smoothness`) hold for **every**
  `u` — this is proved by the corpus itself, at
  `PF/NavierStokes/FujitaKato1964LocalExistenceDischarge.lean:196` and `:203`.
  §1 below re-exports those two lemmas and records that each clause is
  equivalent to `True`.
* A third clause, `divergenceFreePreserved`, does not mention `u` at all: its
  first argument is discarded. Despite the name "PRESERVATION" it constrains no
  solution; it is a property of the initial datum alone (§2).
* The clause named `smoothness` is a pointwise-boundedness statement. No
  derivative of `u` occurs in it (§1, `smoothness_unfold`).

## The main disclosure (§3)

    NS_Solution u u0  ↔  initialDataMatch u u0 ∧ u0.isDivFree

    NS3DTimeGlobalSmoothSolution u0
      ↔  u0.isDivFree ∧ ∃ u : 𝓢(ℝ⁴, ℝ³), initialDataMatch u u0

So the entire typed "time-global smooth solution" existential is equivalent to
the conjunction of

  (a) the initial datum being divergence-free (a hypothesis, not a conclusion),
  (b) a **Schwartz extension question on ℝ⁴**: is there a Schwartz map whose
      time-zero slice is `u0.velocity`?

Neither (a) nor (b) has anything to do with Navier–Stokes. (b) is an elementary
question about the Schwartz space, unrelated to any PDE.

§3 also records three collapses that follow from the same reading:

* `FujitaKatoLocalExistenceHypothesis` and
  `Wave58TimeGlobalExistenceClauseStrengthened` are the **same Prop**
  (`Iff.rfl`). The "conditional discharge"
  `wave58_strengthened_clause_under_fujita_kato`
  (`Wave58TimeGlobalExistenceUpgrade.lean:230`) is therefore the identity map:
  its hypothesis is its conclusion.
* `FujitaKatoLocalSolution u0 T` discards `T` (`…Discharge.lean:155`), so
  "local existence on horizon `T`" and "time-global existence" are the same
  Prop, for every `T`, including `T ≤ 0`.
* `LinearisedNSLocalSolution` is *defined* as `FujitaKatoLocalSolution`
  (`…Discharge.lean:252`), so the linearised and full statements are the same
  Prop — consistent with the fact that no nonlinearity appears anywhere.
* `FujitaKato1964ExplicitTimeBound` / `FujitaKato1964Theorem` (`…:294`, `:344`)
  are equivalent to the hypothesis above; the `∃ T, 0 < T ∧ …` wrapper carries
  no information, because the body does not depend on `T`.

## What is NOT claimed here (§4)

The extension question (b) is **not** trivial and this file does not pretend to
settle it. A map that is constant in `t` is not Schwartz on ℝ⁴ (no decay in the
time direction), so `u0.velocity ∘ (spatial projection)` is not a witness.

What §4 proves is the zero case: the zero Schwartz map matches the zero datum,
and more generally matches any datum whose velocity field is zero. For a
GENERAL divergence-free Schwartz datum the question is **left open here**.

For the record, and clearly labelled as prose rather than as a proved statement:
the extension is expected to hold by tensoring with a Gaussian in time,
`u(t, x) := e^{-t²} · u0.velocity x`, which is Schwartz on ℝ⁴. Formalizing that
needs a tensor-product / product-domain construction for `SchwartzMap`, which
mathlib does not have at the pin `eed770a434957369c6262aa3fb1d6426419016d4`
(`Mathlib/Analysis/Distribution/SchwartzSpace.lean` has no such API). So the
question is *elementary but unformalized*. It is not attempted here, and nothing
below depends on it.

## Be fair to what is real

The 31-file layer `PF/NavierStokes/FujitaKato1964/` contains genuine
mathematics — Sobolev seminorms via Fourier, heat-semigroup operators, Gaussian
derivative bounds, the Leray projector, Schwartz multiplication, integrability
of Sobolev integrands. It has **zero `sorry`** and **zero `: True`** definitions
(the single `True` in that directory is a documented placeholder conjunct inside
`BilinearScaffold.PicardFixedPointProp`, see P2/§6 below). The defect this file
discloses is localized to two places:

  1. the bilinear map `bilinearOp`, which is literally `fun _u _v => 0`
     (`PF/NavierStokes/FujitaKato1964BilinearEstimate.lean:59`), and
  2. the `NS_Solution` predicate itself.

It is NOT a defect of that layer as a whole.

## Clay scope

Nothing in this file, and nothing in the layer it audits, bears on the Clay
Navier–Stokes problem. That problem remains entirely untouched. This file
reduces the distance to it by zero.

## Cross-reference

`codex/AUDIT_RESPONSE_2026-08-06.md` §4.1 ("The Navier–Stokes bilinear
operator — read at source").

## Discipline

Zero `sorry`, zero `axiom`, zero `native_decide`, zero `Prop := True`, zero new
existentials of the author's own. Every theorem below is checked by
`#print axioms` in §7; all are ⊆ `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (audit stone r215)
Date: 2026-08-08
-/

import PF.NavierStokes.Wave58TimeGlobalExistenceUpgrade
import PF.NavierStokes.FujitaKato1964LocalExistenceDischarge
import PF.NavierStokes.FujitaKato1964BilinearEstimate
import PF.NavierStokes.FujitaKato1964.BilinearScaffold

set_option autoImplicit false

namespace PrincipiaTractalis.NavierStokesTypedContent

open PF.NavierStokes.NSPDETypedUpgrade
open PF.NavierStokes.Wave58TimeGlobalExistenceUpgrade
open PF.NavierStokes.FujitaKato1964LocalExistenceDischarge

/-- Abbreviation for the corpus's typed spacetime solution carrier:
    4-dimensional (1 time + 3 space) vector-valued Schwartz maps. -/
abbrev Spacetime4 : Type := SchwartzMap (Fin 4 → ℝ) (Fin 3 → ℝ)

/-! ## §1 — The two clauses that are free

`forwardTimeDomain` and `smoothness` hold for EVERY `u`. This is not a new
observation: the corpus proves it itself, at
`PF/NavierStokes/FujitaKato1964LocalExistenceDischarge.lean:196`
(`forwardTimeDomain_any`) and `:203` (`smoothness_any`). The two theorems below
are re-exports of those corpus lemmas, restated here so that this disclosure is
self-contained. The `_iff_true` corollaries make the emptiness explicit: each
clause is logically equivalent to `True`, even though neither is *defined* as
`True`.
-/

/-- **`forwardTimeDomain` holds for every `u`.** Re-export of the corpus's own
    `FujitaKato1964LocalExistenceDischarge.forwardTimeDomain_any`. The clause
    reads `∀ y, ∃ z, u y = z`, which is true of any function whatsoever. -/
theorem forwardTimeDomain_trivial (u : Spacetime4) : forwardTimeDomain u :=
  forwardTimeDomain_any u

/-- **`forwardTimeDomain` is equivalent to `True`.** It carries no information
    about `u`, about time, or about a domain of definition. -/
theorem forwardTimeDomain_iff_true (u : Spacetime4) :
    forwardTimeDomain u ↔ True :=
  ⟨fun _ => trivial, fun _ => forwardTimeDomain_trivial u⟩

/-- **The clause named `smoothness` unfolds to pointwise BOUNDEDNESS.** No
    derivative of `u` occurs in it. Stated as `Iff.rfl` so the kernel, not the
    prose, certifies the content. -/
theorem smoothness_unfold (u : Spacetime4) :
    smoothness u ↔ ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Fin 4 → ℝ, ‖u y‖ ≤ M :=
  Iff.rfl

/-- **The clause named `smoothness` holds for every `u`.** Re-export of the
    corpus's own `FujitaKato1964LocalExistenceDischarge.smoothness_any`, which
    discharges it from `SchwartzMap.norm_le_seminorm`. Every Schwartz map is
    bounded, so the clause selects no `u`. -/
theorem smoothness_is_boundedness_holds_for_all (u : Spacetime4) : smoothness u :=
  smoothness_any u

/-- **`smoothness` is equivalent to `True`.** -/
theorem smoothness_iff_true (u : Spacetime4) : smoothness u ↔ True :=
  ⟨fun _ => trivial, fun _ => smoothness_is_boundedness_holds_for_all u⟩

/-! ## §2 — The clause that does not see the solution

`divergenceFreePreserved` is declared as

    def divergenceFreePreserved (_u : 𝓢(ℝ⁴,ℝ³)) (u0 : NS3DSchwartzInitialData)
      : Prop := u0.isDivFree

with the solution argument underscore-discarded
(`Wave58TimeGlobalExistenceUpgrade.lean` §1, clause (b)).
-/

/-- **The clause named "divergence-free PRESERVATION" constrains no solution.**
    For any two candidate solutions `u` and `v` — however different — the clause
    is the same Prop. It is a property of the initial datum alone, and asserts
    nothing about preservation, about time, or about divergence of `u`. -/
theorem divergenceFreePreserved_independent_of_solution
    (u v : Spacetime4) (u0 : NS3DSchwartzInitialData) :
    divergenceFreePreserved u u0 ↔ divergenceFreePreserved v u0 :=
  Iff.rfl

/-- **The clause is exactly the initial datum's own `isDivFree` field.** -/
theorem divergenceFreePreserved_is_initial_datum_property
    (u : Spacetime4) (u0 : NS3DSchwartzInitialData) :
    divergenceFreePreserved u u0 ↔ u0.isDivFree :=
  Iff.rfl

/-! ## §3 — THE MAIN DISCLOSURE: the predicate collapses to two clauses -/

/-- **★★★ `NS_Solution` collapses to two clauses.**

    Of the four conjuncts, two are free (§1) and so drop out; the third does not
    mention `u` (§2) and is exactly `u0.isDivFree`. What remains is the
    time-zero matching clause plus a hypothesis on the datum:

        NS_Solution u u0 ↔ initialDataMatch u u0 ∧ u0.isDivFree

    There is no time derivative, no `u·∇u`, no pressure, no Laplacian and no
    viscosity on either side. -/
theorem NS_Solution_iff (u : Spacetime4) (u0 : NS3DSchwartzInitialData) :
    NS_Solution u u0 ↔ (initialDataMatch u u0 ∧ u0.isDivFree) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, forwardTimeDomain_trivial u,
      smoothness_is_boundedness_holds_for_all u⟩

/-- **★★★ The typed "time-global smooth solution" existential, computed.**

        NS3DTimeGlobalSmoothSolution u0
          ↔ u0.isDivFree ∧ ∃ u : 𝓢(ℝ⁴,ℝ³), initialDataMatch u u0

    Read the right-hand side. It is (a) a hypothesis about the initial datum,
    conjoined with (b) the question: *does `u0.velocity` extend to a Schwartz
    map on ℝ⁴ whose time-zero slice it is?* That is a question about the
    Schwartz space. It is not the Navier–Stokes problem, nor any part of it.

    Consequently every upstream statement of the form "NS-3D smoothness holds at
    the substrate level" that unfolds to `NS3DTimeGlobalSmoothSolution` is a
    statement about Schwartz extension, not about fluids. See §5. -/
theorem NS3DTimeGlobalSmoothSolution_iff (u0 : NS3DSchwartzInitialData) :
    NS3DTimeGlobalSmoothSolution u0
      ↔ (u0.isDivFree ∧ ∃ u : Spacetime4, initialDataMatch u u0) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hmatch, hdiv⟩ := (NS_Solution_iff u u0).mp hu
    exact ⟨hdiv, u, hmatch⟩
  · rintro ⟨hdiv, u, hmatch⟩
    exact ⟨u, (NS_Solution_iff u u0).mpr ⟨hmatch, hdiv⟩⟩

/-! ### §3b — Three further collapses, same cause

These are `Iff.rfl`s. They are recorded because each one has a name in the
corpus that suggests strictly more content than the Prop carries.
-/

/-- **The Fujita–Kato "hypothesis" and the "strengthened clause" are the same
    Prop.** `FujitaKatoLocalExistenceHypothesis`
    (`Wave58TimeGlobalExistenceUpgrade.lean` §4) and
    `Wave58TimeGlobalExistenceClauseStrengthened` (§3 there) unfold to the same
    thing, so the "conditional discharge"
    `wave58_strengthened_clause_under_fujita_kato` at `:230` is the identity
    function: it assumes precisely what it concludes. The theorem is true; it is
    just not a reduction. -/
theorem fujitaKatoHypothesis_iff_strengthenedClause :
    FujitaKatoLocalExistenceHypothesis
      ↔ Wave58TimeGlobalExistenceClauseStrengthened :=
  Iff.rfl

/-- **"Local existence on horizon `T`" does not depend on `T`.**
    `FujitaKatoLocalSolution` (`…LocalExistenceDischarge.lean:155`) discards its
    horizon argument, so it is the same Prop as the time-global existential for
    every real `T` — including `T = 0` and `T < 0`. The local-vs-global
    distinction, which is the entire content of the Clay problem, is absent from
    the encoding. -/
theorem fujitaKatoLocalSolution_iff_timeGlobal
    (u0 : NS3DSchwartzInitialData) (T : ℝ) :
    FujitaKatoLocalSolution u0 T ↔ NS3DTimeGlobalSmoothSolution u0 :=
  Iff.rfl

/-- **The "linearised" statement is the full statement.**
    `LinearisedNSLocalSolution` is *defined* to be `FujitaKatoLocalSolution`
    (`…LocalExistenceDischarge.lean:252`). Dropping the convective nonlinearity
    changes nothing, because no nonlinearity ever entered. -/
theorem linearisedNS_iff_fullNS (u0 : NS3DSchwartzInitialData) (T : ℝ) :
    LinearisedNSLocalSolution u0 T ↔ FujitaKatoLocalSolution u0 T :=
  Iff.rfl

/-- **The "explicit time bound" carries no time information.**
    `FujitaKato1964Theorem` (`…LocalExistenceDischarge.lean:294`) and
    `FujitaKato1964ExplicitTimeBound` (`:344`) wrap the body in
    `∃ T : ℝ, 0 < T ∧ …`, but the body is independent of `T`, so the wrapper is
    removable and the whole Prop is equivalent to
    `FujitaKatoLocalExistenceHypothesis`. -/
theorem fujitaKato1964Theorem_iff_hypothesis :
    FujitaKato1964Theorem ↔ FujitaKatoLocalExistenceHypothesis := by
  constructor
  · intro h u0 hu
    obtain ⟨_T, _hT, hsol⟩ := h u0 hu
    exact hsol
  · intro h u0 hu
    exact ⟨1, by norm_num, h u0 hu⟩

/-! ## §4 — Non-vacuity of the remaining content, without overclaiming

The residual content isolated in §3 is the Schwartz extension question

    ∃ u : 𝓢(ℝ⁴, ℝ³), initialDataMatch u u0 .

**This file does not settle that question for a general datum, and does not
claim to.** In particular the obvious candidate fails: a map constant in the
time variable has no decay in `t` and so is not Schwartz on ℝ⁴, hence
`u0.velocity ∘ (spatial projection)` is not a witness. (Mathlib's
`SchwartzMap.compCLM` cannot be used to build one either: it requires a
growth-from-below condition on the precomposed map, which a coordinate
projection does not satisfy.)

What is proved below is the zero case, and the mild generalization to any datum
with vanishing velocity field. The general case is discussed in the file header
and is left open.
-/

/-- **The zero Schwartz map matches the zero datum.** Re-export of the corpus's
    own `FujitaKato1964LocalExistenceDischarge.initialDataMatch_zero`; both
    sides reduce through `SchwartzMap.zero_apply`. This is the witness that
    makes the residual §3(b) content non-vacuous at one point of the datum
    space — and only at that point. -/
theorem initialDataMatch_zero_witness :
    initialDataMatch (0 : Spacetime4)
      PF.NavierStokes.NSPDETypedUpgrade.NS3DSchwartzInitialData.zero :=
  initialDataMatch_zero

/-- **Any datum with vanishing velocity field is matched by the zero map.**
    Slight generalization of `initialDataMatch_zero_witness`: the `divFree`
    field of `u0` plays no role. -/
theorem initialDataMatch_of_velocity_eq_zero
    (u0 : NS3DSchwartzInitialData) (h : u0.velocity = 0) :
    initialDataMatch (0 : Spacetime4) u0 := by
  intro x
  show (0 : Spacetime4) _ = u0.velocity x
  rw [SchwartzMap.zero_apply, h]
  show (0 : Fin 3 → ℝ) = (0 : SchwartzMap (Fin 3 → ℝ) (Fin 3 → ℝ)) x
  rw [SchwartzMap.zero_apply]

/-- **At a vanishing-velocity datum, the whole typed existential reduces to the
    datum's own `isDivFree` field.** Combining §3 with the witness above: for
    such data the "time-global smooth solution" Prop is exactly the hypothesis
    that was assumed, and nothing more. -/
theorem NS3DTimeGlobalSmoothSolution_iff_isDivFree_of_velocity_eq_zero
    (u0 : NS3DSchwartzInitialData) (h : u0.velocity = 0) :
    NS3DTimeGlobalSmoothSolution u0 ↔ u0.isDivFree := by
  rw [NS3DTimeGlobalSmoothSolution_iff]
  exact ⟨fun hh => hh.1,
    fun hdiv => ⟨hdiv, (0 : Spacetime4), initialDataMatch_of_velocity_eq_zero u0 h⟩⟩

/-! ## §5 — The upstream citation

`PF/Referee/PrincipiaFractalisSubstrateTheorem.lean:167-172` declares the
substrate consequence field

    NS_via_substrate :
      PrincipiaTractalis.CrossMillenniumSharedInvariants.α_NS =
        2 * PrincipiaTractalis.CrossMillenniumSharedInvariants.α_BSD ∧
      ∃ u : SchwartzMap (Fin 4 → ℝ) (Fin 3 → ℝ),
        PF.NavierStokes.Wave58TimeGlobalExistenceUpgrade.NS_Solution u
          PF.NavierStokes.NSPDETypedUpgrade.NS3DSchwartzInitialData.zero

and it is discharged at `:404`. The Referee file is not imported here (it sits
at the top of the import graph and pulling it in would invert the dependency
direction), so the second conjunct is restated verbatim below as a statement
about the underlying Prop.

The theorem records what that conjunct amounts to: the existential is witnessed
by the identically-zero field at the identically-zero datum. By §3 it is
equivalent to `NS3DSchwartzInitialData.zero.isDivFree`, whose `divFree` field is
declared as `True` at `PF/NavierStokes/NSPDETypedUpgrade.lean:222`. The first
conjunct of `NS_via_substrate` is a numerical identity between two `α` constants
and says nothing about any PDE.
-/

/-- **★★ The `NS_via_substrate` existential, witnessed.** Verbatim second
    conjunct of `PFSubstrateConsequences.NS_via_substrate`
    (`PF/Referee/PrincipiaFractalisSubstrateTheorem.lean:168-172`), discharged
    by the zero field. The witness is the zero map at the zero datum: this is
    what the substrate-level "NS-3D smoothness discharge" contains. -/
theorem NS_via_substrate_existential_witnessed_by_zero :
    ∃ u : SchwartzMap (Fin 4 → ℝ) (Fin 3 → ℝ),
      NS_Solution u
        PF.NavierStokes.NSPDETypedUpgrade.NS3DSchwartzInitialData.zero :=
  ⟨(0 : Spacetime4), ns_solution_zero⟩

/-- **The same existential, read through §3.** It is equivalent to the zero
    datum's own `isDivFree` field — i.e. to `True` (`NSPDETypedUpgrade.lean:222`
    sets `NS3DSchwartzInitialData.zero.divFree := True`). -/
theorem NS_via_substrate_existential_iff_zero_isDivFree :
    NS3DTimeGlobalSmoothSolution
        PF.NavierStokes.NSPDETypedUpgrade.NS3DSchwartzInitialData.zero
      ↔ PF.NavierStokes.NSPDETypedUpgrade.NS3DSchwartzInitialData.zero.isDivFree :=
  NS3DTimeGlobalSmoothSolution_iff_isDivFree_of_velocity_eq_zero _ rfl

/-! ## §6 — P2: the bilinear side

The convective nonlinearity is the entire difficulty of Navier–Stokes. In the
Fujita–Kato layer it is the zero map:

    PF/NavierStokes/FujitaKato1964BilinearEstimate.lean:59
      noncomputable def bilinearOp (_u _v : VectorField3) : VectorField3 := 0

Both arguments are underscore-discarded. Every conclusion of that layer that is
stated in terms of `bilinearOp` — the pointwise bilinear bound, the
`Ḣ^{1/2}` bound, the small-data contraction constant — therefore holds *because*
the operator is identically zero, and is independent of the convective term. The
two theorems below record this in the kernel.

Separately, `PF/NavierStokes/FujitaKato1964/BilinearScaffold.lean:229` defines

    PicardFixedPointProp B : Prop :=
      BilinearBoundProp B → ∀ u₀ ε, SmallDataInH12Sq ε u₀ →
        ∃ u : TimeFieldR3C, u 0 = u₀ ∧ True

with a literal `∧ True` in the conclusion — the mild-equation statement itself
is the placeholder, as that file's own docstring says. It is discharged at `:246`
by the constant time-field `fun _ => u₀`. So the Picard fixed-point Prop asserts
that a constant-in-time field matches its own initial datum, which it does.
-/

/-- **The convective nonlinearity is absent: `bilinearOp` is identically zero.**
    Re-export of the corpus's own
    `FujitaKato1964BilinearEstimate.bilinearOp_substrate_zero`. Consequence: no
    conclusion of the Fujita–Kato bilinear layer distinguishes the true
    convective term `ℙ(u·∇v)` from zero. -/
theorem bilinearOp_identically_zero
    (u v : PF.NavierStokes.FujitaKato1964BilinearEstimate.VectorField3)
    (x : Fin 3 → ℝ) :
    (PF.NavierStokes.FujitaKato1964BilinearEstimate.bilinearOp u v) x = 0 :=
  PF.NavierStokes.FujitaKato1964BilinearEstimate.bilinearOp_substrate_zero u v x

/-- **The Picard fixed-point Prop, unfolded, contains a literal `∧ True`.**
    Stated as `Iff.rfl` so the placeholder is visible to the kernel rather than
    only to a reader of `BilinearScaffold.lean:229`. -/
theorem picardFixedPointProp_conclusion_contains_true
    (B : PF.NavierStokes.FujitaKato1964.BilinearScaffold.BilinearMildOperator) :
    PF.NavierStokes.FujitaKato1964.BilinearScaffold.PicardFixedPointProp B
      ↔ (PF.NavierStokes.FujitaKato1964.BilinearScaffold.BilinearBoundProp B →
          ∀ (u₀ : PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier.VectorSchwartz3C)
            (ε : ℝ),
            PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier.SmallDataInH12Sq ε u₀ →
            ∃ u : PF.NavierStokes.FujitaKato1964.BilinearScaffold.TimeFieldR3C,
              u 0 = u₀ ∧ True) :=
  Iff.rfl

/-- **★★ `fujitaKato_conclusions_hold_at_zero_bilinear`** — the Fujita–Kato
    layer's bilinear conclusions are independent of the convective
    nonlinearity, because that nonlinearity is the zero map.

    Conjunct 1: `bilinearOp` is identically zero on all inputs
    (`FujitaKato1964BilinearEstimate.lean:69`), so every estimate downstream of
    it is an estimate on `0`.

    Conjunct 2: `PicardFixedPointProp` holds for `trivialBilinear`, the
    identically-zero mild bilinear (`BilinearScaffold.lean:246`) — and by the
    previous theorem its conclusion's mild-equation content is a literal
    `True`. -/
theorem fujitaKato_conclusions_hold_at_zero_bilinear :
    (∀ (u v : PF.NavierStokes.FujitaKato1964BilinearEstimate.VectorField3)
       (x : Fin 3 → ℝ),
        (PF.NavierStokes.FujitaKato1964BilinearEstimate.bilinearOp u v) x = 0)
    ∧ PF.NavierStokes.FujitaKato1964.BilinearScaffold.PicardFixedPointProp
        PF.NavierStokes.FujitaKato1964.BilinearScaffold.trivialBilinear :=
  ⟨bilinearOp_identically_zero,
   PF.NavierStokes.FujitaKato1964.BilinearScaffold.trivialBilinear_satisfies_picard⟩

/-! ## §7 — Capstone and axiom audit -/

/-- **Disclosure bundle for the typed NS predicate.** Each field is one of the
    facts proved above. No field asserts more than the corresponding theorem. -/
structure TypedNSContentDisclosure : Prop where
  /-- `forwardTimeDomain` is equivalent to `True` for every `u`. -/
  forward_time_domain_free : ∀ u : Spacetime4, forwardTimeDomain u ↔ True
  /-- The clause named `smoothness` is equivalent to `True` for every `u`. -/
  smoothness_free : ∀ u : Spacetime4, smoothness u ↔ True
  /-- `divergenceFreePreserved` does not depend on the candidate solution. -/
  div_free_clause_blind :
    ∀ (u v : Spacetime4) (u0 : NS3DSchwartzInitialData),
      divergenceFreePreserved u u0 ↔ divergenceFreePreserved v u0
  /-- `NS_Solution` collapses to time-zero matching plus the datum hypothesis. -/
  ns_solution_collapse :
    ∀ (u : Spacetime4) (u0 : NS3DSchwartzInitialData),
      NS_Solution u u0 ↔ (initialDataMatch u u0 ∧ u0.isDivFree)
  /-- The typed time-global existential is divergence-freeness of the datum
      conjoined with a Schwartz extension question on ℝ⁴. -/
  time_global_collapse :
    ∀ u0 : NS3DSchwartzInitialData,
      NS3DTimeGlobalSmoothSolution u0
        ↔ (u0.isDivFree ∧ ∃ u : Spacetime4, initialDataMatch u u0)
  /-- The Fujita–Kato "hypothesis" is the same Prop as the "strengthened
      clause" it is supposed to imply. -/
  hypothesis_is_conclusion :
    FujitaKatoLocalExistenceHypothesis
      ↔ Wave58TimeGlobalExistenceClauseStrengthened
  /-- "Local on horizon `T`" is the same Prop as "time-global", for every `T`. -/
  horizon_carries_nothing :
    ∀ (u0 : NS3DSchwartzInitialData) (T : ℝ),
      FujitaKatoLocalSolution u0 T ↔ NS3DTimeGlobalSmoothSolution u0
  /-- The upstream `NS_via_substrate` existential is witnessed by the zero
      field at the zero datum. -/
  substrate_witness_is_zero :
    ∃ u : Spacetime4,
      NS_Solution u
        PF.NavierStokes.NSPDETypedUpgrade.NS3DSchwartzInitialData.zero
  /-- The convective nonlinearity is the zero map. -/
  bilinear_is_zero :
    ∀ (u v : PF.NavierStokes.FujitaKato1964BilinearEstimate.VectorField3)
      (x : Fin 3 → ℝ),
      (PF.NavierStokes.FujitaKato1964BilinearEstimate.bilinearOp u v) x = 0

/-- **★★★ r215 capstone — the typed NS predicate, disclosed.**

    Every field is discharged by a theorem proved above. What the bundle records
    is a reading, not a refutation: each cited corpus theorem is true. The point
    is that the Props they are about do not contain Navier–Stokes.

    Explicitly NOT claimed: that the Schwartz extension question isolated in
    `time_global_collapse` is trivial (see §4), and anything at all about the
    Clay Navier–Stokes problem. -/
theorem r215_typed_ns_content_disclosure : TypedNSContentDisclosure :=
  { forward_time_domain_free := forwardTimeDomain_iff_true
    smoothness_free := smoothness_iff_true
    div_free_clause_blind := divergenceFreePreserved_independent_of_solution
    ns_solution_collapse := NS_Solution_iff
    time_global_collapse := NS3DTimeGlobalSmoothSolution_iff
    hypothesis_is_conclusion := fujitaKatoHypothesis_iff_strengthenedClause
    horizon_carries_nothing := fujitaKatoLocalSolution_iff_timeGlobal
    substrate_witness_is_zero := NS_via_substrate_existential_witnessed_by_zero
    bilinear_is_zero := bilinearOp_identically_zero }

/-! ### Axiom audit — every theorem in this file

House rule: an axiom claim that `lake build` does not re-run is not a verified
claim. Every name below must print a subset of
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms forwardTimeDomain_trivial
#print axioms forwardTimeDomain_iff_true
#print axioms smoothness_unfold
#print axioms smoothness_is_boundedness_holds_for_all
#print axioms smoothness_iff_true
#print axioms divergenceFreePreserved_independent_of_solution
#print axioms divergenceFreePreserved_is_initial_datum_property
#print axioms NS_Solution_iff
#print axioms NS3DTimeGlobalSmoothSolution_iff
#print axioms fujitaKatoHypothesis_iff_strengthenedClause
#print axioms fujitaKatoLocalSolution_iff_timeGlobal
#print axioms linearisedNS_iff_fullNS
#print axioms fujitaKato1964Theorem_iff_hypothesis
#print axioms initialDataMatch_zero_witness
#print axioms initialDataMatch_of_velocity_eq_zero
#print axioms NS3DTimeGlobalSmoothSolution_iff_isDivFree_of_velocity_eq_zero
#print axioms NS_via_substrate_existential_witnessed_by_zero
#print axioms NS_via_substrate_existential_iff_zero_isDivFree
#print axioms bilinearOp_identically_zero
#print axioms picardFixedPointProp_conclusion_contains_true
#print axioms fujitaKato_conclusions_hold_at_zero_bilinear
#print axioms r215_typed_ns_content_disclosure

end PrincipiaTractalis.NavierStokesTypedContent
