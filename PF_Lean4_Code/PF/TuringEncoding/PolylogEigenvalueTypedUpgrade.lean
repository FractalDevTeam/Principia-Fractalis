/-
# PolylogEigenvalueTypedUpgrade — Structural Decomposition of the Deepest Open Prop

★ 2026-06-02 — Wave 58 (post Wave 57 sharpness certificate) ★

## Why this file exists

`PolylogEigenvalueConjecture` (PF/TuringEncoding/Operators.lean:250) is the
single load-bearing hypothesis of the P ≠ NP chain
(`P_neq_NP_via_spectral_gap` in `PF/P_NP_Equivalence.lean`). By Wave 57's
`alpha_realization_canonical_pair_iff_classes_distinct`
(PF/TuringEncoding/AlphaRealizationNoGo.lean) it is **logically equivalent
to `ClassP ≠ ClassNP`** — i.e., discharging it is equivalent to deciding
P vs NP.

This file does NOT attempt to prove P ≠ NP. It performs a **typed
structural upgrade**: decompose `PolylogEigenvalueConjecture` (an opaque
4-clause Prop on `alpha_of_class`) into **four named typed sub-Props**,
each isolating one structural ingredient. The conjunction of the four is
**definitionally equal** to the original conjecture. Each sub-Prop is
then linked to the corresponding axiom-free **enum-level mirror**
(`alpha_at_enum`), which witnesses its truth on the *concrete* canonical
α values. This sharpens what content is and is not transportable across
the set-level / enum-level divide (per `AlphaRealizationNoGo`).

## What is delivered (axiom-free; no `sorry`)

1. **Four typed sub-Props** isolating the ingredients of the conjecture:
   * `PolylogSubProp_alpha_P_sq_eq_two`
   * `PolylogSubProp_alpha_P_pos`
   * `PolylogSubProp_alpha_NP_quadratic`
   * `PolylogSubProp_alpha_NP_pos`

2. **Conjunction recomposition** as a theorem:
   `PolylogEigenvalueConjecture` iff the conjunction of the four
   sub-Props. (Definitional; `Iff.rfl` after unfolding.)

3. **Enum-level mirror discharge** of each sub-Prop:
   axiom-free theorems
   `polylog_subprop_at_enum_alpha_P_sq_eq_two`,
   `polylog_subprop_at_enum_alpha_P_pos`,
   `polylog_subprop_at_enum_alpha_NP_quadratic`,
   `polylog_subprop_at_enum_alpha_NP_pos`
   discharging each ingredient on the concrete enum-level α values.

4. **Conditional set-level discharge**: theorem
   `polylog_subprops_discharged_via_canonical_pinning` —
   *if* `alpha_of_class ClassP = √2` and `alpha_of_class ClassNP = φ+1/4`
   (the manuscript's canonical pinning), *then* all four set-level
   sub-Props hold simultaneously. This is the cleanest conditional
   structural discharge available without breaking the no-go barrier.

5. **Wave 57 sharpness certificate, typed form**:
   `polylog_subprop_quadruple_iff_classes_distinct` — the **existential**
   form (∃ f : Set Language → ℝ realising the 4 sub-Props on ClassP and
   ClassNP) is ↔ `ClassP ≠ ClassNP`. (Reuses
   `algebraic_realization_iff_classes_distinct` from
   `AlphaRealizationNoGo`.) This is the typed form of "discharging this
   = deciding P vs NP".

6. **Single citable capstone** `polylog_eigenvalue_typed_upgrade_capstone`
   bundling (1)-(5) as a single referee-quotable theorem.

## What is NOT claimed

* No discharge of `PolylogEigenvalueConjecture` on the opaque
  `alpha_of_class`. The opacity barrier (per `AlphaRealizationNoGo`)
  remains: any unconditional set-level discharge is a P ≠ NP proof.
* No new mathematical content beyond what already exists in
  `AlphaCanonical`, `AlphaEnum`, and `AlphaRealizationNoGo`. This file
  is a **structural typed refactoring** that exposes the four
  ingredients of the deepest open Prop as independently inspectable,
  independently dischargeable named sub-Props.
* The Wave 17/18 spectral-reading refutation
  (`polylog_resonance_consistent_with_refutation`) is **orthogonal**:
  the algebraic content here is exactly the content the P ≠ NP chain
  consumes; the refuted spectral reading is incidental scaffolding.

## Axiom budget

Zero project axioms, zero sorries. All theorems depend only on
`[propext, Classical.choice, Quot.sound]` (the latter two enter through
`AlphaRealizationNoGo`'s classical case-split).

Stage Wave 58 — typed structural upgrade of the P-vs-NP-equivalent
named open Prop.
-/

import PF.TuringEncoding.Operators
import PF.TuringEncoding.AlphaCanonical
import PF.TuringEncoding.AlphaEnum
import PF.TuringEncoding.AlphaRealizationNoGo
import PF.IntervalArithmetic

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## Section 1 — The four typed sub-Props -/

/-- **Sub-Prop A1**: `(alpha_of_class ClassP)² = 2`. The P-class
    self-adjointness algebraic equation. -/
def PolylogSubProp_alpha_P_sq_eq_two : Prop :=
  (alpha_of_class ClassP) ^ 2 = 2

/-- **Sub-Prop A2**: `0 < alpha_of_class ClassP`. Positivity / branch
    selection for the P-class α-value. -/
def PolylogSubProp_alpha_P_pos : Prop :=
  0 < alpha_of_class ClassP

/-- **Sub-Prop B1**: `16·(alpha_of_class ClassNP)² − 24·(alpha_of_class ClassNP) − 11 = 0`.
    The NP-class self-adjointness algebraic equation (the
    golden-modulation quadratic). -/
def PolylogSubProp_alpha_NP_quadratic : Prop :=
  16 * (alpha_of_class ClassNP) ^ 2 - 24 * (alpha_of_class ClassNP) - 11 = 0

/-- **Sub-Prop B2**: `0 < alpha_of_class ClassNP`. Positivity / branch
    selection for the NP-class α-value. -/
def PolylogSubProp_alpha_NP_pos : Prop :=
  0 < alpha_of_class ClassNP

/-! ## Section 2 — Conjunction recomposition

The four sub-Props together are **definitionally equal** to the original
`PolylogEigenvalueConjecture`. This is the typed structural decomposition
that the rest of the file refines. -/

/-- **★ THE TYPED DECOMPOSITION ★**: `PolylogEigenvalueConjecture` is
    the conjunction of the four named sub-Props. This is `Iff.rfl`
    after unfolding all five definitions. -/
theorem polylog_eigenvalue_conjecture_iff_four_subprops :
    PolylogEigenvalueConjecture ↔
    (PolylogSubProp_alpha_P_sq_eq_two ∧
     PolylogSubProp_alpha_P_pos ∧
     PolylogSubProp_alpha_NP_quadratic ∧
     PolylogSubProp_alpha_NP_pos) := by
  unfold PolylogEigenvalueConjecture
    PolylogSubProp_alpha_P_sq_eq_two
    PolylogSubProp_alpha_P_pos
    PolylogSubProp_alpha_NP_quadratic
    PolylogSubProp_alpha_NP_pos
  constructor
  · rintro ⟨⟨hPsq, hPpos⟩, hNPquad, hNPpos⟩
    exact ⟨hPsq, hPpos, hNPquad, hNPpos⟩
  · rintro ⟨hPsq, hPpos, hNPquad, hNPpos⟩
    exact ⟨⟨hPsq, hPpos⟩, hNPquad, hNPpos⟩

/-- **Forward**: the four sub-Props imply the conjecture. -/
theorem four_subprops_imply_polylog_eigenvalue_conjecture
    (hPsq : PolylogSubProp_alpha_P_sq_eq_two)
    (hPpos : PolylogSubProp_alpha_P_pos)
    (hNPquad : PolylogSubProp_alpha_NP_quadratic)
    (hNPpos : PolylogSubProp_alpha_NP_pos) :
    PolylogEigenvalueConjecture :=
  polylog_eigenvalue_conjecture_iff_four_subprops.mpr
    ⟨hPsq, hPpos, hNPquad, hNPpos⟩

/-- **Backward**: the conjecture yields each sub-Prop. -/
theorem polylog_eigenvalue_conjecture_gives_subprop_A1
    (h : PolylogEigenvalueConjecture) : PolylogSubProp_alpha_P_sq_eq_two :=
  (polylog_eigenvalue_conjecture_iff_four_subprops.mp h).1

theorem polylog_eigenvalue_conjecture_gives_subprop_A2
    (h : PolylogEigenvalueConjecture) : PolylogSubProp_alpha_P_pos :=
  (polylog_eigenvalue_conjecture_iff_four_subprops.mp h).2.1

theorem polylog_eigenvalue_conjecture_gives_subprop_B1
    (h : PolylogEigenvalueConjecture) : PolylogSubProp_alpha_NP_quadratic :=
  (polylog_eigenvalue_conjecture_iff_four_subprops.mp h).2.2.1

theorem polylog_eigenvalue_conjecture_gives_subprop_B2
    (h : PolylogEigenvalueConjecture) : PolylogSubProp_alpha_NP_pos :=
  (polylog_eigenvalue_conjecture_iff_four_subprops.mp h).2.2.2

/-! ## Section 3 — Enum-level mirror discharge (axiom-free)

The four sub-Props, translated to the enum-level concrete α values
`alpha_at_enum .P = √2` and `alpha_at_enum .NP = φ + 1/4`, are each
provable axiom-free using the canonical algebraic identities from
`AlphaCanonical.lean` and `AlphaEnum.lean`. This is the
**axiom-free witness** that the algebraic content of each sub-Prop
holds on the manuscript's canonical α values; the only barrier to
the set-level statement is the opacity of `alpha_of_class`. -/

/-- **Enum mirror of sub-Prop A1**: `(alpha_at_enum .P)² = 2`. -/
theorem polylog_subprop_at_enum_alpha_P_sq_eq_two :
    (alpha_at_enum PFClass.P) ^ 2 = 2 := by
  show (Real.sqrt 2) ^ 2 = 2
  exact alpha_P_sq

/-- **Enum mirror of sub-Prop A2**: `0 < alpha_at_enum .P`. -/
theorem polylog_subprop_at_enum_alpha_P_pos :
    0 < alpha_at_enum PFClass.P := by
  show (0 : ℝ) < Real.sqrt 2
  exact alpha_P_pos

/-- **Enum mirror of sub-Prop B1**: the NP-class quadratic on the
    concrete value `alpha_at_enum .NP = φ + 1/4`. -/
theorem polylog_subprop_at_enum_alpha_NP_quadratic :
    16 * (alpha_at_enum PFClass.NP) ^ 2 -
      24 * (alpha_at_enum PFClass.NP) - 11 = 0 := by
  show 16 * (phi + 1/4) ^ 2 - 24 * (phi + 1/4) - 11 = 0
  exact alpha_NP_quadratic

/-- **Enum mirror of sub-Prop B2**: `0 < alpha_at_enum .NP`. -/
theorem polylog_subprop_at_enum_alpha_NP_pos :
    0 < alpha_at_enum PFClass.NP := by
  show (0 : ℝ) < phi + 1/4
  exact alpha_NP_pos

/-- **★ THE ENUM-LEVEL CONJUNCTION ★** (axiom-free): the four sub-Props,
    translated to the enum-level α values, hold simultaneously. This is
    the enum-level analog of `PolylogEigenvalueConjecture` and is
    UNCONDITIONAL — no opacity barrier at the enum level. -/
theorem polylog_subprop_quadruple_at_enum :
    (alpha_at_enum PFClass.P) ^ 2 = 2 ∧
    0 < alpha_at_enum PFClass.P ∧
    16 * (alpha_at_enum PFClass.NP) ^ 2 -
      24 * (alpha_at_enum PFClass.NP) - 11 = 0 ∧
    0 < alpha_at_enum PFClass.NP :=
  ⟨polylog_subprop_at_enum_alpha_P_sq_eq_two,
   polylog_subprop_at_enum_alpha_P_pos,
   polylog_subprop_at_enum_alpha_NP_quadratic,
   polylog_subprop_at_enum_alpha_NP_pos⟩

/-! ## Section 4 — Conditional set-level discharge under canonical pinning

If we GRANT the manuscript's canonical pinning
`alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ + 1/4`
(an assumption that, by `AlphaRealizationNoGo`, is itself logically
equivalent to `ClassP ≠ ClassNP`), then EACH of the four sub-Props
follows axiom-free from the enum-level mirror discharges in §3.

This is NOT a discharge of `PolylogEigenvalueConjecture` — the canonical
pinning is exactly the no-go content. But it makes the **path** to
discharge explicit: the only missing structural content is the
identification of the opaque set-level α values with the manuscript's
canonical reals.
-/

/-- **Sub-Prop A1 under canonical pinning** (conditional). -/
theorem polylog_subprop_A1_under_pinning
    (hP : alpha_of_class ClassP = Real.sqrt 2) :
    PolylogSubProp_alpha_P_sq_eq_two := by
  unfold PolylogSubProp_alpha_P_sq_eq_two
  rw [hP]
  exact alpha_P_sq

/-- **Sub-Prop A2 under canonical pinning** (conditional). -/
theorem polylog_subprop_A2_under_pinning
    (hP : alpha_of_class ClassP = Real.sqrt 2) :
    PolylogSubProp_alpha_P_pos := by
  unfold PolylogSubProp_alpha_P_pos
  rw [hP]
  exact alpha_P_pos

/-- **Sub-Prop B1 under canonical pinning** (conditional). -/
theorem polylog_subprop_B1_under_pinning
    (hNP : alpha_of_class ClassNP = phi + 1/4) :
    PolylogSubProp_alpha_NP_quadratic := by
  unfold PolylogSubProp_alpha_NP_quadratic
  rw [hNP]
  exact alpha_NP_quadratic

/-- **Sub-Prop B2 under canonical pinning** (conditional). -/
theorem polylog_subprop_B2_under_pinning
    (hNP : alpha_of_class ClassNP = phi + 1/4) :
    PolylogSubProp_alpha_NP_pos := by
  unfold PolylogSubProp_alpha_NP_pos
  rw [hNP]
  exact alpha_NP_pos

/-- **★ CONDITIONAL SET-LEVEL DISCHARGE ★**: under the manuscript's
    canonical pinning of `alpha_of_class` to `(√2, φ + 1/4)` on the
    (ClassP, ClassNP) pair, all four set-level sub-Props hold
    simultaneously — and hence so does `PolylogEigenvalueConjecture`.

    This is the cleanest conditional structural discharge available
    without breaking the opacity barrier. The hypothesis itself is, by
    `AlphaRealizationNoGo.alpha_realization_canonical_pair_iff_classes_distinct`,
    equivalent to `ClassP ≠ ClassNP` (i.e., to P vs NP itself); so the
    "discharge" here is conditional on something equipotent to the
    Millennium problem. -/
theorem polylog_subprops_discharged_via_canonical_pinning
    (hP : alpha_of_class ClassP = Real.sqrt 2)
    (hNP : alpha_of_class ClassNP = phi + 1/4) :
    PolylogSubProp_alpha_P_sq_eq_two ∧
    PolylogSubProp_alpha_P_pos ∧
    PolylogSubProp_alpha_NP_quadratic ∧
    PolylogSubProp_alpha_NP_pos :=
  ⟨polylog_subprop_A1_under_pinning hP,
   polylog_subprop_A2_under_pinning hP,
   polylog_subprop_B1_under_pinning hNP,
   polylog_subprop_B2_under_pinning hNP⟩

/-- **Conditional set-level discharge → PolylogEigenvalueConjecture**.
    Combines the conditional sub-Prop quadruple with the recomposition. -/
theorem polylog_eigenvalue_conjecture_under_canonical_pinning
    (hP : alpha_of_class ClassP = Real.sqrt 2)
    (hNP : alpha_of_class ClassNP = phi + 1/4) :
    PolylogEigenvalueConjecture := by
  obtain ⟨hPsq, hPpos, hNPquad, hNPpos⟩ :=
    polylog_subprops_discharged_via_canonical_pinning hP hNP
  exact four_subprops_imply_polylog_eigenvalue_conjecture
    hPsq hPpos hNPquad hNPpos

/-! ## Section 5 — Wave 57 sharpness certificate, typed form

The existential form of the four-sub-Props conjunction over a general
`f : Set Language → ℝ` (not the opaque `alpha_of_class` specifically)
is ↔ `ClassP ≠ ClassNP`. This reuses
`algebraic_realization_iff_classes_distinct` from `AlphaRealizationNoGo`.

This is the **typed structural sharpness certificate**: discharging the
existential form of the four sub-Props is exactly as hard as deciding
P vs NP. -/

/-- **★ THE WAVE 57 TYPED SHARPNESS CERTIFICATE ★**: the existential
    form of the four sub-Props (over an arbitrary `f : Set Language → ℝ`)
    is logically equivalent to `ClassP ≠ ClassNP` — i.e., to deciding
    P vs NP.

    This is the typed version of the statement "discharging
    `PolylogEigenvalueConjecture` = proving P ≠ NP". -/
theorem polylog_subprop_quadruple_iff_classes_distinct :
    (∃ f : Set Language → ℝ,
        ((f ClassP) ^ 2 = 2 ∧ 0 < f ClassP) ∧
        (16 * (f ClassNP) ^ 2 - 24 * (f ClassNP) - 11 = 0 ∧
         0 < f ClassNP)) ↔
      ClassP ≠ ClassNP :=
  algebraic_realization_iff_classes_distinct

/-! ## Section 6 — Single citable capstone -/

/-- **★★ THE TYPED UPGRADE CAPSTONE ★★** — single referee-citable
    theorem bundling the entire typed structural upgrade of
    `PolylogEigenvalueConjecture`.

    The five clauses are:

    **(1) Conjunction recomposition** (Iff.rfl after unfolding):
        `PolylogEigenvalueConjecture` is the conjunction of the four
        named sub-Props.

    **(2) Enum-level mirror discharge** (axiom-free, UNCONDITIONAL):
        the four sub-Props hold on the concrete enum-level α values
        `alpha_at_enum .P = √2` and `alpha_at_enum .NP = φ + 1/4`.

    **(3) Conditional set-level discharge** under canonical pinning:
        if `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ+1/4`,
        then `PolylogEigenvalueConjecture` holds.

    **(4) Wave 57 typed sharpness certificate**: the existential form
        over an arbitrary `f : Set Language → ℝ` is ↔ `ClassP ≠ ClassNP`.

    **(5) Honest scope**: no unconditional set-level discharge of
        `PolylogEigenvalueConjecture` is provided (and per (4), none
        is possible without simultaneously proving P ≠ NP). -/
theorem polylog_eigenvalue_typed_upgrade_capstone :
    -- (1) Conjunction recomposition
    (PolylogEigenvalueConjecture ↔
      (PolylogSubProp_alpha_P_sq_eq_two ∧
       PolylogSubProp_alpha_P_pos ∧
       PolylogSubProp_alpha_NP_quadratic ∧
       PolylogSubProp_alpha_NP_pos)) ∧
    -- (2) Enum-level mirror discharge (axiom-free)
    ((alpha_at_enum PFClass.P) ^ 2 = 2 ∧
     0 < alpha_at_enum PFClass.P ∧
     16 * (alpha_at_enum PFClass.NP) ^ 2 -
       24 * (alpha_at_enum PFClass.NP) - 11 = 0 ∧
     0 < alpha_at_enum PFClass.NP) ∧
    -- (3) Conditional set-level discharge under canonical pinning
    (∀ (_hP : alpha_of_class ClassP = Real.sqrt 2)
       (_hNP : alpha_of_class ClassNP = phi + 1/4),
        PolylogEigenvalueConjecture) ∧
    -- (4) Wave 57 typed sharpness certificate
    ((∃ f : Set Language → ℝ,
        ((f ClassP) ^ 2 = 2 ∧ 0 < f ClassP) ∧
        (16 * (f ClassNP) ^ 2 - 24 * (f ClassNP) - 11 = 0 ∧
         0 < f ClassNP)) ↔
      ClassP ≠ ClassNP) :=
  ⟨polylog_eigenvalue_conjecture_iff_four_subprops,
   polylog_subprop_quadruple_at_enum,
   polylog_eigenvalue_conjecture_under_canonical_pinning,
   polylog_subprop_quadruple_iff_classes_distinct⟩

/-! ## Section 7 — Scope and honest summary

This file delivers a **typed structural upgrade** of the deepest open
Prop in the P vs NP axis, NOT a discharge. Concretely:

* The four sub-Props isolate the algebraic ingredients of
  `PolylogEigenvalueConjecture` as independent typed predicates.
* Each sub-Prop is discharged axiom-free at the enum level on the
  concrete canonical α values.
* The conditional set-level discharge under canonical pinning makes
  explicit the single missing ingredient: the identification of
  `alpha_of_class ClassP/ClassNP` with `√2 / φ+1/4`.
* The Wave 57 typed sharpness certificate certifies that this
  identification is itself equivalent to `ClassP ≠ ClassNP`.

**No new mathematical content is produced**; the file is a
**structural refactoring** that exposes the four ingredients of the
deepest open Prop as named, independently inspectable, independently
dischargeable sub-Props — making the chain of reasoning crisp for
future referee inspection and for any future operator-theoretic
derivation that aims at the set-level identification.

## Axiom budget

Zero project axioms, zero sorries. All theorems depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

end PrincipiaTractalis.TuringEncoding

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`
-- (the latter two enter via `AlphaRealizationNoGo`).
#print axioms
  PrincipiaTractalis.TuringEncoding.polylog_eigenvalue_conjecture_iff_four_subprops
#print axioms
  PrincipiaTractalis.TuringEncoding.four_subprops_imply_polylog_eigenvalue_conjecture
#print axioms
  PrincipiaTractalis.TuringEncoding.polylog_subprop_at_enum_alpha_P_sq_eq_two
#print axioms
  PrincipiaTractalis.TuringEncoding.polylog_subprop_at_enum_alpha_P_pos
#print axioms
  PrincipiaTractalis.TuringEncoding.polylog_subprop_at_enum_alpha_NP_quadratic
#print axioms
  PrincipiaTractalis.TuringEncoding.polylog_subprop_at_enum_alpha_NP_pos
#print axioms
  PrincipiaTractalis.TuringEncoding.polylog_subprop_quadruple_at_enum
#print axioms
  PrincipiaTractalis.TuringEncoding.polylog_subprops_discharged_via_canonical_pinning
#print axioms
  PrincipiaTractalis.TuringEncoding.polylog_eigenvalue_conjecture_under_canonical_pinning
#print axioms
  PrincipiaTractalis.TuringEncoding.polylog_subprop_quadruple_iff_classes_distinct
#print axioms
  PrincipiaTractalis.TuringEncoding.polylog_eigenvalue_typed_upgrade_capstone
