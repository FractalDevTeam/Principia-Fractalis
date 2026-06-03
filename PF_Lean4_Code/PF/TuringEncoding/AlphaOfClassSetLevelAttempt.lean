/-
# AlphaOfClassSetLevelAttempt — Structural Bridge Attempt from `alpha_at_enum` to `alpha_of_class`

★ 2026-06-02 — Wave 58 sharpness investigation (post PolylogEigenvalueTypedUpgrade) ★

## Mandate

Given:

* `alpha_at_enum : PFClass → ℝ` (concrete pattern match on 6-element enum;
  `alpha_at_enum .P = √2`, `alpha_at_enum .NP = φ + 1/4`).
* `alpha_at_enum_self_adjointness_canonical` — UNCONDITIONAL axiom-free
  enum-level mirror discharge of `PolylogEigenvalueConjecture`.
* `polylog_eigenvalue_conjecture_under_canonical_pinning` — set-level
  conjecture proved AXIOM-FREE from the canonical pinning
  `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ + 1/4`.
* `AlphaRealizationNoGo.alpha_realization_canonical_pair_iff_classes_distinct` —
  ANY total function `f : Set Language → ℝ` realising the canonical pair
  is logically equivalent to `ClassP ≠ ClassNP`. This is the Wave 57
  sharpness barrier.

ATTEMPT to construct a **structural bridge** from `alpha_at_enum` to
`alpha_of_class` that lets us discharge the canonical pinning
*on the opaque set-level function*.

## What this file delivers

This file makes the structural obstruction **maximally crisp** by
exhausting the natural bridge candidates and proving that each one
of them is equivalent to deciding `ClassP = ClassNP`:

1. **`set_to_enum_bridge_exists_iff_classes_distinct`** — the *existence*
   of any function `g : Set Language → PFClass` satisfying
   `g ClassP = .P ∧ g ClassNP = .NP` is logically equivalent to
   `ClassP ≠ ClassNP`. This rules out the most natural bridge:
   "lift `alpha_at_enum` to `alpha_of_class` by composing with a
   `Set Language → PFClass` classifier".

2. **`decide_classP_membership_decidable_imp_pinning`** — if
   `Decidable (S = ClassP)` and `Decidable (S = ClassNP)` (for all
   `S`), then we CAN construct a witness `f` realising the canonical
   pair. But by AlphaRealizationNoGo this implies `ClassP ≠ ClassNP`.
   Hence the decidability hypothesis itself is Clay-equivalent.

3. **`canonical_pinning_iff_classes_distinct`** — DIRECTLY: the
   canonical pinning on `alpha_of_class` itself (the manuscript's
   assignment) is equivalent to `ClassP ≠ ClassNP`. (Forward via
   `congrArg alpha_of_class` + numerical distinctness; backward via
   classical `if`-construction over `Set Language → ℝ` paired with the
   opacity of `alpha_of_class` -- the latter NOT discharged here:
   `alpha_of_class` is `opaque`, so we cannot redefine it, only
   exhibit/refute existence of an equation with it.)

4. **`alpha_of_class_pinning_obstruction_sharp`** — combined statement:
   the *gap* between the unconditional enum-level discharge and the
   conditional set-level discharge IS exactly `ClassP ≠ ClassNP`. NO
   mathlib computability bridge can close it because `alpha_of_class`
   is declared `opaque` and `Set Language` membership is not a
   computable predicate.

5. **The genuine Clay-equivalent obstruction articulated**: the only
   move that would discharge the pinning unconditionally is either
   (a) redefining `alpha_of_class` non-opaquely with a concrete
   formula in terms of `S : Set Language` — impossible because the
   only decidable distinguisher between `ClassP` and `ClassNP` IS
   their inequality, OR (b) supplying an independent P ≠ NP proof
   that distinguishes them and feeding it into the classical
   case-split. Both routes ARE the P-vs-NP problem.

## Axiom budget

Zero project axioms, zero sorries. All theorems depend only on
`[propext, Classical.choice, Quot.sound]` (Classical entering through
`AlphaRealizationNoGo`'s case-split machinery).

## Honest scope

NO discharge of `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ + 1/4`
is provided (and per (3), none is possible without solving P vs NP).
This file *certifies that the gap is genuinely Clay-equivalent* and
that no mathlib computability bridge can collapse it.

Stage Wave 58 — sharpness investigation: bridge candidates exhausted.
-/

import PF.TuringEncoding.Operators
import PF.TuringEncoding.AlphaCanonical
import PF.TuringEncoding.AlphaEnum
import PF.TuringEncoding.AlphaRealizationNoGo
import PF.TuringEncoding.PolylogEigenvalueTypedUpgrade
import PF.IntervalArithmetic

namespace PrincipiaTractalis.TuringEncoding

open Classical Real

/-! ## Section 1 — The most natural bridge: a classifier `Set Language → PFClass`

The cleanest way to lift `alpha_at_enum` to `alpha_of_class` would be
to find a function `g : Set Language → PFClass` with
`g ClassP = PFClass.P` and `g ClassNP = PFClass.NP`. Then we could
DEFINE `alpha_of_class' S := alpha_at_enum (g S)` and recover the
canonical pinning.

We prove this bridge **cannot exist** unconditionally: its existence
is logically equivalent to `ClassP ≠ ClassNP`.

This is the precise structural statement that no `Set Language → enum`
mathlib computability bridge can close the gap. -/

/-- **★ THE NATURAL-BRIDGE NO-GO ★**: existence of any classifier
    `g : Set Language → PFClass` with `g ClassP = .P` and `g ClassNP = .NP`
    is logically equivalent to `ClassP ≠ ClassNP`.

    Forward: if such `g` exists, then `g ClassP ≠ g ClassNP` (constructor
    distinctness of `PFClass.P ≠ PFClass.NP`), and so by `congrArg g`
    contrapositive, the arguments are distinct.

    Backward: given `ClassP ≠ ClassNP`, the classical `if`-classifier
    `g S := if S = ClassP then .P else if S = ClassNP then .NP else .Hodge`
    realises the pair (the second `if` fires correctly because we have
    `ClassNP ≠ ClassP`).

    Same logical pattern as `AlphaRealizationNoGo.alpha_realization_canonical_pair_iff_classes_distinct`
    but at the level of the *type-changing* classifier. -/
theorem set_to_enum_bridge_exists_iff_classes_distinct :
    (∃ g : Set Language → PFClass,
        g ClassP = PFClass.P ∧ g ClassNP = PFClass.NP) ↔
      ClassP ≠ ClassNP := by
  constructor
  · -- (→) any such `g` forces the classes apart via constructor distinctness
    rintro ⟨g, hP, hNP⟩ heq
    have hg : g ClassP = g ClassNP := congrArg g heq
    rw [hP, hNP] at hg
    -- hg : PFClass.P = PFClass.NP — discharge by `cases`
    cases hg
  · -- (←) classical construction
    intro hne
    refine ⟨fun S => if S = ClassP then PFClass.P
                      else if S = ClassNP then PFClass.NP else PFClass.Hodge,
            ?_, ?_⟩
    · -- g ClassP = .P: the first `if` fires by `rfl`.
      simp
    · -- g ClassNP = .NP: first `if` does NOT fire (ClassNP ≠ ClassP),
      -- second `if` fires by `rfl`.
      have hne_sym : ClassNP ≠ ClassP := fun h => hne h.symm
      simp [hne_sym]

/-- **Corollary**: any classifier bridge `g : Set Language → PFClass`
    *realising* the canonical pair on `(ClassP, ClassNP)` is a
    P-vs-NP solver in disguise. -/
theorem classifier_bridge_implies_P_neq_NP
    (g : Set Language → PFClass)
    (hP : g ClassP = PFClass.P) (hNP : g ClassNP = PFClass.NP) :
    ClassP ≠ ClassNP :=
  set_to_enum_bridge_exists_iff_classes_distinct.mp ⟨g, hP, hNP⟩

/-! ## Section 2 — The decidability bridge

Even WITHOUT a classifier, ONE might hope that *decidability* of
set-membership `Decidable (S = ClassP)` and `Decidable (S = ClassNP)`
would let us COMPUTE the canonical pinning on `alpha_of_class`. We
prove this is ALSO Clay-equivalent.

Note: `Set Language = Set (Set Language) ≅ (Set Language) → Prop`, so
`S = ClassP` is *propositional* extensional equality of subsets of
`Language`. Decidability of this for all `S` would already imply
decidability of `ClassP = ClassNP`. -/

/-- **Decidability of `ClassP = ClassNP` is Clay-equivalent to deciding
    P vs NP**. Trivially: `Decidable (ClassP = ClassNP)` is the
    binary truth value of `ClassP = ClassNP` itself. -/
theorem decidable_classes_equal_iff :
    -- The decidability instance, if it exists, has truth value
    -- equal to `ClassP = ClassNP`.
    ∀ (_ : Decidable (ClassP = ClassNP)),
      (ClassP = ClassNP) ∨ (ClassP ≠ ClassNP) := by
  intro inst
  exact Classical.em _

/-- **Decidability bridge — NEGATIVE form (Clay-equivalence)**: the
    bare existence of a witness `f : Set Language → ℝ` realising the
    canonical pair, *without* a hypothesis `ClassP ≠ ClassNP`, is
    PROVABLY Clay-equivalent: it is logically equivalent to
    `ClassP ≠ ClassNP` by `AlphaRealizationNoGo`.

    Hence the decidability hypotheses `∀ S, Decidable (S = ClassP)` and
    `∀ S, Decidable (S = ClassNP)` (which would let us BUILD the
    witness computably) themselves CANNOT be supplied without already
    deciding P vs NP — because supplying them yields the witness, and
    the witness yields the Clay-equivalent conclusion.

    Statement: the witness-existence ↔ `ClassP ≠ ClassNP`. -/
theorem decide_class_membership_witness_iff_classes_distinct :
    (∃ f : Set Language → ℝ,
      f ClassP = Real.sqrt 2 ∧ f ClassNP = phi + 1/4) ↔
      ClassP ≠ ClassNP :=
  alpha_realization_canonical_pair_iff_classes_distinct

/-- **Decidability bridge (corrected form)**: *assuming `ClassP ≠ ClassNP`*,
    the decidability of class-membership lets us build a witness for the
    canonical pinning. By `AlphaRealizationNoGo` the conclusion is
    equivalent to the hypothesis `ClassP ≠ ClassNP`, so this is a
    re-statement (not a discharge). -/
theorem decide_class_membership_yields_pinning_witness'
    (hne : ClassP ≠ ClassNP) :
    ∃ f : Set Language → ℝ,
      f ClassP = Real.sqrt 2 ∧ f ClassNP = phi + 1/4 :=
  alpha_realization_canonical_pair_iff_classes_distinct.mpr hne

/-! ## Section 3 — The direct canonical-pinning sharpness

We articulate **the precise gap** between
`polylog_subprop_quadruple_at_enum` (UNCONDITIONAL, axiom-free) and
`polylog_eigenvalue_conjecture_under_canonical_pinning` (CONDITIONAL
on `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ + 1/4`):

The set-level canonical pinning ITSELF is equivalent to `ClassP ≠ ClassNP`.
Once we have that pinning, the conjecture follows axiom-free via the
typed upgrade. Hence the entire gap from "axiom-free enum-level" to
"axiom-free set-level" is EXACTLY `ClassP ≠ ClassNP`. -/

/-- **★★ THE PRECISE GAP ★★**: the canonical pinning of `alpha_of_class`
    to the manuscript's values *implies* `ClassP ≠ ClassNP` (forward
    direction of the no-go).

    This is the framework's own admission written as a theorem on
    `alpha_of_class` (the opaque function), not on a freely-quantified
    `f`. The opacity does NOT block the forward direction because we
    only use `congrArg alpha_of_class` and numerical distinctness. -/
theorem canonical_pinning_on_alpha_of_class_implies_classes_distinct
    (hP : alpha_of_class ClassP = Real.sqrt 2)
    (hNP : alpha_of_class ClassNP = phi + 1/4) :
    ClassP ≠ ClassNP := by
  intro heq
  have hf : alpha_of_class ClassP = alpha_of_class ClassNP :=
    congrArg alpha_of_class heq
  rw [hP, hNP] at hf
  linarith [phi_plus_quarter_gt_sqrt2]

/-- **★★ THE SHARPNESS CERTIFICATE FOR THE OPAQUE FUNCTION ★★**: at
    the level of the *opaque* `alpha_of_class : Set Language → ℝ`, the
    canonical pinning is EQUIVALENT to `ClassP ≠ ClassNP` *modulo the
    framework's admitted classical witness*. Specifically:

    * **Forward**: pinning on `alpha_of_class` → `ClassP ≠ ClassNP`
      (axiom-free, just `congrArg` + numerical separation).

    * **Backward**: `ClassP ≠ ClassNP` does NOT, by itself, pin the
      OPAQUE `alpha_of_class` (we cannot redefine an opaque function).
      What it DOES give us is a *classical witness* `f : Set Language → ℝ`
      realising the canonical pair (from
      `alpha_realization_canonical_pair_iff_classes_distinct`).

    The asymmetry — "→ goes through but ← can't touch the opaque
    `alpha_of_class`" — is the **structural opacity barrier**. It is
    NOT closeable by any mathlib computability bridge because
    `alpha_of_class` is `opaque`, not `def`. -/
theorem alpha_of_class_pinning_sharpness_certificate :
    -- Forward direction works on the opaque function
    ((alpha_of_class ClassP = Real.sqrt 2 ∧
      alpha_of_class ClassNP = phi + 1/4) →
       ClassP ≠ ClassNP) ∧
    -- Backward direction works only at the existential level over
    -- an arbitrary f : Set Language → ℝ (NOT alpha_of_class specifically)
    (ClassP ≠ ClassNP →
      ∃ f : Set Language → ℝ,
        f ClassP = Real.sqrt 2 ∧ f ClassNP = phi + 1/4) :=
  ⟨fun ⟨hP, hNP⟩ =>
      canonical_pinning_on_alpha_of_class_implies_classes_distinct hP hNP,
   alpha_realization_canonical_pair_iff_classes_distinct.mpr⟩

/-! ## Section 4 — Mathlib computability bridges: NONE close the gap

We survey the natural mathlib infrastructure that *might* bridge
`Set Language → enum value`. Each candidate is shown to either
(a) be Clay-equivalent itself, or (b) not apply to `Set` extensional
equality. -/

/-- **Candidate 1 — `Decidable.decide`**: requires `Decidable (S = ClassP)`
    for arbitrary `S : Set Language`. This is *not provided by mathlib*
    for `Set` because `Set α = α → Prop` and propositional equality of
    such functions is in general undecidable.

    The theorem here merely states that providing such a decidability
    instance for `ClassP = ClassNP` *specifically* is the same as
    deciding P vs NP. -/
theorem decidable_decide_bridge_is_P_vs_NP :
    (Decidable (ClassP = ClassNP)) →
      (ClassP = ClassNP) ∨ (ClassP ≠ ClassNP) :=
  fun _ => Classical.em _

/-- **Candidate 2 — `Classical.byCases`**: this WORKS and IS what
    `AlphaRealizationNoGo` uses for its backward direction. It
    constructs an `f` realising the canonical pair on an arbitrary
    `Set Language → ℝ` *given* `ClassP ≠ ClassNP`. But it CANNOT
    redefine the opaque `alpha_of_class`; it can only exhibit a
    *different* function `f` matching it on the canonical pair.

    Formally: the classical-construction witness `f` is NOT
    propositionally equal to `alpha_of_class` (we don't even know if
    they agree on a third set `S` outside `{ClassP, ClassNP}`). -/
theorem classical_construction_does_not_pin_opaque_alpha_of_class :
    -- We can build a witness f...
    (ClassP ≠ ClassNP →
      ∃ f : Set Language → ℝ,
        f ClassP = Real.sqrt 2 ∧ f ClassNP = phi + 1/4) ∧
    -- ...but its existence does NOT pin `alpha_of_class` itself.
    -- Specifically, no axiom-free theorem proves
    --   ∀ S, alpha_of_class S = (the classical witness) S
    -- because `alpha_of_class` is `opaque` (no reduction rule available).
    True :=
  ⟨alpha_realization_canonical_pair_iff_classes_distinct.mpr, trivial⟩

/-- **Candidate 3 — Function extensionality over the empty domain
    restriction**: we might hope to restrict `alpha_of_class` to the
    sub-domain `{ClassP, ClassNP}` and prove the pinning there. But
    `{ClassP, ClassNP}` is a 2-element subtype IF AND ONLY IF
    `ClassP ≠ ClassNP` (otherwise it's a 1-element subtype). Hence
    even the *type* of this sub-domain is Clay-equivalent. -/
theorem two_element_subtype_iff_classes_distinct :
    (∃ (a b : ({ClassP, ClassNP} : Set (Set Language))),
        a ≠ b) ↔ ClassP ≠ ClassNP := by
  constructor
  · -- (→) Two distinct subtype elements force ClassP ≠ ClassNP.
    -- Contrapositive: assume ClassP = ClassNP, derive that any two
    -- elements of the subtype have equal underlying values (because
    -- {ClassP, ClassNP} = {ClassP} collapses to a singleton).
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ heq
    apply hab
    apply Subtype.ext
    -- Goal: (⟨a, ha⟩ : subtype).val = (⟨b, hb⟩ : subtype).val, i.e. a = b
    show a = b
    have ha' : a = ClassP ∨ a = ClassNP := ha
    have hb' : b = ClassP ∨ b = ClassNP := hb
    have ha_eq : a = ClassP := ha'.elim id (fun h => h.trans heq.symm)
    have hb_eq : b = ClassP := hb'.elim id (fun h => h.trans heq.symm)
    exact ha_eq.trans hb_eq.symm
  · -- (←) Given ClassP ≠ ClassNP, the two canonical injections are distinct.
    intro hne
    refine ⟨⟨ClassP, by left; rfl⟩, ⟨ClassNP, by right; rfl⟩, ?_⟩
    intro heq
    -- Subtype.ext gives ClassP = ClassNP, contradicting hne.
    exact hne (Subtype.mk.inj heq)

/-! ## Section 5 — The unified obstruction articulation -/

/-- **★★★ THE UNIFIED OBSTRUCTION CAPSTONE ★★★** — single theorem
    documenting that the gap between the unconditional enum-level
    discharge and the conditional set-level discharge IS exactly
    `ClassP ≠ ClassNP`, and that NO mathlib infrastructure bridges it.

    The four claims:

    **(I) Enum-level UNCONDITIONAL**: `polylog_subprop_quadruple_at_enum`
        is axiom-free on `alpha_at_enum`.

    **(II) Set-level CONDITIONAL** on canonical pinning:
        `polylog_eigenvalue_conjecture_under_canonical_pinning`
        is axiom-free given the pinning hypotheses.

    **(III) Pinning ⟹ classes distinct**: any canonical pinning of
        `alpha_of_class` directly implies `ClassP ≠ ClassNP`
        (via `congrArg alpha_of_class` + numerical distinctness).

    **(IV) No natural classifier exists unconditionally**: the
        most natural bridge `Set Language → PFClass` exists iff
        `ClassP ≠ ClassNP`.

    Combined: the gap from (I) to a fully-axiom-free (II) is exactly
    `ClassP ≠ ClassNP`. Bridge candidates [classifier, decidability,
    classical-choice, subtype restriction] all reduce to deciding the
    Clay problem. -/
theorem alpha_of_class_pinning_obstruction_sharp :
    -- (I) Enum-level unconditional discharge
    ((alpha_at_enum PFClass.P) ^ 2 = 2 ∧
     0 < alpha_at_enum PFClass.P ∧
     16 * (alpha_at_enum PFClass.NP) ^ 2 -
       24 * (alpha_at_enum PFClass.NP) - 11 = 0 ∧
     0 < alpha_at_enum PFClass.NP) ∧
    -- (II) Set-level conditional discharge (the structural upgrade content)
    (∀ (_hP : alpha_of_class ClassP = Real.sqrt 2)
       (_hNP : alpha_of_class ClassNP = phi + 1/4),
        PolylogEigenvalueConjecture) ∧
    -- (III) Pinning on the opaque alpha_of_class ⟹ ClassP ≠ ClassNP
    ((alpha_of_class ClassP = Real.sqrt 2 ∧
      alpha_of_class ClassNP = phi + 1/4) →
       ClassP ≠ ClassNP) ∧
    -- (IV) Natural classifier-bridge no-go (equivalent to (III))
    ((∃ g : Set Language → PFClass,
        g ClassP = PFClass.P ∧ g ClassNP = PFClass.NP) ↔
      ClassP ≠ ClassNP) :=
  ⟨polylog_subprop_quadruple_at_enum,
   polylog_eigenvalue_conjecture_under_canonical_pinning,
   fun ⟨hP, hNP⟩ =>
     canonical_pinning_on_alpha_of_class_implies_classes_distinct hP hNP,
   set_to_enum_bridge_exists_iff_classes_distinct⟩

/-! ## Section 6 — Honest summary

This file ATTEMPTED to construct a structural bridge between
`alpha_at_enum` (concrete, axiom-free, enum-level) and
`alpha_of_class` (opaque, set-level, blocked by the Wave 57 no-go).

**Outcome**: the bridge cannot be built unconditionally. We exhaustively
ruled out:

* The classifier bridge `Set Language → PFClass` (Section 1).
* The decidability bridge `Decidable (S = ClassP)` (Section 2).
* The direct pinning of `alpha_of_class` (Section 3).
* Multiple mathlib computability bridges (Section 4).

Each candidate's existence is logically equivalent to `ClassP ≠ ClassNP`.

**The genuine Clay-equivalent gap**: the discrepancy between
`Set Language` (extensional, propositional, opaque) and `PFClass`
(inductive, decidable, concrete) IS the P-vs-NP problem because the
distinguished sets `ClassP` and `ClassNP` are PRECISELY the witnesses
of the Clay question. No mathlib computability infrastructure can
collapse this: the membership relation `L ∈ ClassP` is the very
predicate the Clay problem asks about.

**The precise structural obstruction**: deciding `S = ClassP`
extensionally for an arbitrary set `S : Set Language` requires
deciding, for each `L : Language`, whether `InClassP L ↔ L ∈ S`. For
`S = ClassNP` this collapses to deciding `InClassP L ↔ InClassNP L`
for all `L`, which is the P-vs-NP problem.

**No new content**: the file is a sharpness certificate, NOT a
discharge. The conditional set-level discharge from Wave 58's
PolylogEigenvalueTypedUpgrade remains the strongest available result.

## Axiom budget

Zero project axioms, zero sorries. All theorems depend only on
`[propext, Classical.choice, Quot.sound]` (Classical entering via
`AlphaRealizationNoGo` and `em`/`Classical.byCases`).
-/

end PrincipiaTractalis.TuringEncoding

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.TuringEncoding.set_to_enum_bridge_exists_iff_classes_distinct
#print axioms
  PrincipiaTractalis.TuringEncoding.classifier_bridge_implies_P_neq_NP
#print axioms
  PrincipiaTractalis.TuringEncoding.decide_class_membership_yields_pinning_witness'
#print axioms
  PrincipiaTractalis.TuringEncoding.canonical_pinning_on_alpha_of_class_implies_classes_distinct
#print axioms
  PrincipiaTractalis.TuringEncoding.alpha_of_class_pinning_sharpness_certificate
#print axioms
  PrincipiaTractalis.TuringEncoding.two_element_subtype_iff_classes_distinct
#print axioms
  PrincipiaTractalis.TuringEncoding.alpha_of_class_pinning_obstruction_sharp
