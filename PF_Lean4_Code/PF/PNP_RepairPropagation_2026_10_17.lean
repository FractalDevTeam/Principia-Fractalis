/-
# PF.PNP_RepairPropagation_2026_10_17

**Propagating the 2026-10-08 carrier repair.**

`InClassPRepair_2026_10_08.lean` proved that the legacy `InClassP`
specification is defective (`ClassP = {∅, univ}`) and supplied honest
replacements `InClassP_Step` / `InClassNP_Step` over a real machine model. That
file was then left unused by everything downstream. This file propagates it.

## What is new here (§2, §3): the vacuity is DEMONSTRATED, not asserted

The repair file proved `legacy_ClassP_ne_ClassNP : ClassP ≠ ClassNP`
unconditionally. That is a *theorem*, so **every downstream result taking
`ClassP ≠ ClassNP` as a hypothesis is discharged for free.** Two consequences,
both one-liners, both previously unstated:

* **§2** — `P_neq_NP_def`, the repo's own "P ≠ NP" Prop
  (`P_NP_Complete_Proof.lean:83`), **holds unconditionally**. Composing
  `P_neq_NP_def_of_classes_distinct` with the defect gives it with no
  hypothesis at all. So that Prop carries no complexity content.

* **§3** — `PvsNP_via_Hodge_disc5_Bridge_Open`, recorded in
  `GRAND_PROBLEM_DEPENDENCY_GRAPH` as **"NAMED OPEN"**, is **a theorem**. It is
  provably equivalent to `ClassP ≠ ClassNP`
  (`open_bridge_iff_classes_distinct`), and that is proved. So the α-web's
  P-vs-NP bridge is not an open problem awaiting discharge; it is a consequence
  of the specification defect.

**Neither of these is a new mathematical result. Both are statements the tree
already entailed and had not drawn.** That is precisely the propagation that
was owed.

## The honest side (§4)

Over the `_Step` carriers: `P ⊆ NP` survives (it is proved in the repair file,
without the rigged invariance clause), the carriers are non-degenerate, and the
question is **left open on purpose**. `step_question_iff` certifies that the two
natural formulations of the honest question agree, so anyone working on it is
working on one statement rather than two.

## Triage of the legacy claims

| legacy claim | status when re-pointed at `_Step` |
|---|---|
| `ClassP ⊆ ClassNP` | **SURVIVES** — `ClassP_Step_subset_ClassNP_Step` |
| `ClassP ≠ ClassNP` | **WAS VACUOUS** — a one-line consequence of the defect (§1) |
| `P_neq_NP_def` | **WAS VACUOUS** — unconditional (§2) |
| `PvsNP_via_Hodge_disc5_Bridge_Open` | **WAS VACUOUS** — a theorem, not open (§3) |
| the question itself | **OPEN** — `PvsNP_Step`, undischarged here and everywhere |

## α-web (the item checked, not assumed)

The `_Step` definitions quantify only over `TM`, `ℕ → ℕ` bounds and
`BinString` — **no real-valued parameter occurs in either**, so no
α-realisation can hide in the re-pointed statements. The α-realisation
`∃ f, f ClassP = √2 ∧ f ClassNP = φ + ¼` attaches to the **legacy** carriers
only, and §3 shows what that attachment is worth there.

## Scope note

A full textual re-pointing is **75 files and 1,914 references** — not a
mechanical edit, and not attempted here. This file instead makes the honest
status *citable in one place*, so that no file needs rewriting for the
correction to be available, and records the triage above.

Three-axiom bar: `[propext, Classical.choice, Quot.sound]`. No `sorry`,
no `axiom`, no `native_decide`.

Author: Pablo Cohen + Claude Opus 5. 2026-10-17.
-/
import PF.TuringEncoding.InClassPRepair_2026_10_08
import PF.EmpiricalPostulateDischarge
import PF.PNP_WitnessExistenceScaffold

namespace PrincipiaTractalis.PNPRepairPropagation20261017

open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.TuringEncoding.Repair20261008

/-! ## §1 — the defect, cited -/

/-- The legacy classes are provably distinct, with no hypothesis.
Restated here so downstream files can cite one name. -/
theorem legacy_classes_distinct : ClassP ≠ ClassNP :=
  legacy_ClassP_ne_ClassNP

/-! ## §2 — the repo's own `P ≠ NP` Prop is unconditional -/

/-- **`P_neq_NP_def` holds unconditionally.**

Composing `EmpiricalPostulateDischarge.P_neq_NP_def_of_classes_distinct` with
the specification defect discharges the repo's "P ≠ NP" Prop with no hypothesis
whatsoever. It therefore carries no complexity content: it is a consequence of
the trailing-input clause in `InClassP`, not of anything about computation. -/
theorem legacy_P_neq_NP_def_unconditional : P_neq_NP_def :=
  EmpiricalPostulateDischarge.P_neq_NP_def_of_classes_distinct legacy_classes_distinct

/-! ## §3 — the "NAMED OPEN" α-bridge is a theorem -/

/-- **`PvsNP_via_Hodge_disc5_Bridge_Open` is not open.**

It is provably equivalent to `ClassP ≠ ClassNP`, and that is a theorem, so the
bridge Prop is discharged. Recorded as `NAMED OPEN` in the dependency graph;
it is a one-line consequence of the specification defect. -/
theorem alpha_bridge_is_discharged :
    PNP_Wave56CrossGaloisLockAttempt.PvsNP_via_Hodge_disc5_Bridge_Open :=
  (PNP_WitnessExistenceScaffold.open_bridge_iff_classes_distinct).mpr
    legacy_classes_distinct

/-! ## §4 — the honest carriers -/

/-- The honest "P = NP" Prop, over the `_Step` carriers. -/
def P_equals_NP_Step : Prop := ∀ L : Language, InClassNP_Step L → InClassP_Step L

/-- The honest "P ≠ NP" Prop. **Left open deliberately: nothing in this
development discharges it, in either direction.** -/
def P_neq_NP_Step : Prop := ¬ P_equals_NP_Step

/-- `P ⊆ NP` **survives** the re-pointing: it is proved over the honest
carriers without any context-invariance clause. -/
theorem step_P_subset_NP : ClassP_Step ⊆ ClassNP_Step :=
  ClassP_Step_subset_ClassNP_Step

/-- The two natural formulations of the honest question agree. This is what
makes `PvsNP_Step` a single well-posed target rather than two. -/
theorem step_question_iff : P_equals_NP_Step ↔ PvsNP_Step := by
  constructor
  · intro h
    exact Set.Subset.antisymm step_P_subset_NP (fun L hL => h L hL)
  · intro h L hL
    have : ClassNP_Step ⊆ ClassP_Step := by rw [h]
    exact this hL

/-- The honest carriers are **non-degenerate** in exactly the way the legacy
ones failed: `ClassP_Step` contains a language that is neither `∅` nor `univ`,
whereas `ClassP = {∅, univ}`. -/
theorem step_nondegenerate :
    ∃ L : Language, L ∈ ClassP_Step ∧ L ≠ (∅ : Language) ∧ L ≠ (Set.univ : Language) :=
  ⟨Lfirst, Lfirst_mem_ClassP_Step, Lfirst_ne_empty, Lfirst_ne_univ⟩

/-- The repair is not a relabelling: the honest class differs from the
defective one. -/
theorem carriers_differ : ClassP ≠ ClassP_Step :=
  legacy_ClassP_ne_ClassP_Step

/-! ## §5 — the status, as one citable conjunction -/

/-- **The honest status of the P-vs-NP axis in this development.**

Everything true is here; the question itself is absent, because it is open. -/
theorem pnp_honest_status :
    -- the legacy carriers are degenerate, so their `P ≠ NP` is content-free
    ClassP ≠ ClassNP ∧
    P_neq_NP_def ∧
    PNP_Wave56CrossGaloisLockAttempt.PvsNP_via_Hodge_disc5_Bridge_Open ∧
    -- the honest carriers are different, non-degenerate, and satisfy `P ⊆ NP`
    ClassP ≠ ClassP_Step ∧
    (∃ L : Language, L ∈ ClassP_Step ∧ L ≠ (∅ : Language) ∧ L ≠ (Set.univ : Language)) ∧
    ClassP_Step ⊆ ClassNP_Step ∧
    -- and the honest question is a single well-posed statement
    (P_equals_NP_Step ↔ PvsNP_Step) :=
  ⟨legacy_classes_distinct, legacy_P_neq_NP_def_unconditional,
   alpha_bridge_is_discharged, carriers_differ, step_nondegenerate,
   step_P_subset_NP, step_question_iff⟩

end PrincipiaTractalis.PNPRepairPropagation20261017

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.PNPRepairPropagation20261017.legacy_classes_distinct
#print axioms PrincipiaTractalis.PNPRepairPropagation20261017.legacy_P_neq_NP_def_unconditional
#print axioms PrincipiaTractalis.PNPRepairPropagation20261017.alpha_bridge_is_discharged
#print axioms PrincipiaTractalis.PNPRepairPropagation20261017.step_P_subset_NP
#print axioms PrincipiaTractalis.PNPRepairPropagation20261017.step_question_iff
#print axioms PrincipiaTractalis.PNPRepairPropagation20261017.step_nondegenerate
#print axioms PrincipiaTractalis.PNPRepairPropagation20261017.carriers_differ
#print axioms PrincipiaTractalis.PNPRepairPropagation20261017.pnp_honest_status
