# P-vs-NP repair propagation: the vacuity is now DEMONSTRATED, and the ledger's "NAMED OPEN" α-bridge is a theorem

**Date:** 2026-10-17 (Legion, build on Acer). Audit + build.
`PF/PNP_RepairPropagation_2026_10_17.lean`, 168 lines, EXIT 0, three-axiom bar,
no `sorry`. Labels FACT / MEASURED / JUDGEMENT.

**Two new theorems, both one-liners, both previously unstated — and neither is
new mathematics. Both are statements the tree already entailed and had not
drawn.** That is exactly the propagation that was owed.

1. **`legacy_P_neq_NP_def_unconditional : P_neq_NP_def`** — the repo's own
   "P ≠ NP" Prop holds **with no hypothesis at all**.
2. **`alpha_bridge_is_discharged : PvsNP_via_Hodge_disc5_Bridge_Open`** — the
   Prop that `GRAND_PROBLEM_DEPENDENCY_GRAPH` records as **"NAMED OPEN"** is a
   **theorem**. **The ledger entry is wrong and should be corrected.**

---

## 1. Inventory — and the scope correction. MEASURED

A full textual re-pointing is **not** mechanical:

| measure | count |
|---|---|
| files referencing `ClassP`/`ClassNP` | **75** |
| total references | **1,914** |
| claim-bearing lines (`ClassP ≠/= ClassNP`, `PvsNP_Question`) | **371** |

**JUDGEMENT: "re-point everything" is the wrong unit of work**, and I am
reporting that rather than beginning a 75-file refactor that would need a real
decision at each of the α-web files, the six `UnifiedClayClosure*` files and the
five Wave capstones. Most of the 1,914 are docstrings and incidental mentions;
the load-bearing claims are few, and they are listed in §3.

**What was done instead** — the proportionate form of "repair, not disclosure":
make the honest status **citable in one place**, so the correction is available
to every file without any file being rewritten, and record the triage. One
168-line file replaces a 75-file edit.

## 2. The mechanism: the defect discharges hypotheses. FACT

`InClassPRepair_2026_10_08.lean:524` proves
**`legacy_ClassP_ne_ClassNP : ClassP ≠ ClassNP`** unconditionally — because
the trailing clause `(∀ x c, M.accepts (x ++ c) ↔ M.accepts x)` at `x := []`
forces `accepts` constant, giving `ClassP = {∅, univ}`.

> **Since that is a theorem, every downstream result taking `ClassP ≠ ClassNP`
> as a hypothesis is discharged for free — so its conclusion is unconditional,
> and carries no complexity content.**

That single observation is what propagates, and it propagates automatically.
Two instances follow.

### 2a. `P_neq_NP_def` is unconditional — MEASURED

`EmpiricalPostulateDischarge.lean:201` proves
`P_neq_NP_def_of_classes_distinct : ClassP ≠ ClassNP → P_neq_NP_def`, where
`P_neq_NP_def := ¬ P_equals_NP_def` and
`P_equals_NP_def := ∀ L, InClassNP L → InClassP L`
(`P_NP_Complete_Proof.lean:79,83`).

Composing with the defect:

```lean
theorem legacy_P_neq_NP_def_unconditional : P_neq_NP_def :=
  EmpiricalPostulateDischarge.P_neq_NP_def_of_classes_distinct legacy_classes_distinct
```

**The repo's "P ≠ NP" Prop is a consequence of the trailing-input clause in
`InClassP`, not of anything about computation.**

### 2b. The "NAMED OPEN" α-bridge is a theorem — MEASURED, and it corrects the ledger

`PNP_WitnessExistenceScaffold.lean:109` proves
`open_bridge_iff_classes_distinct : PvsNP_via_Hodge_disc5_Bridge_Open ↔ ClassP ≠ ClassNP`,
which itself reduces to Wave 41B's
`alpha_realization_canonical_pair_iff_classes_distinct`. So:

```lean
theorem alpha_bridge_is_discharged :
    PNP_Wave56CrossGaloisLockAttempt.PvsNP_via_Hodge_disc5_Bridge_Open :=
  (PNP_WitnessExistenceScaffold.open_bridge_iff_classes_distinct).mpr
    legacy_classes_distinct
```

**`GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-08-23.md:42,116` records this Prop as
"FULL-STRENGTH RESIDUAL (named open Prop `PvsNP_via_Hodge_disc5_Bridge_Open`)"
and "**NAMED OPEN**". It is not open.** It is discharged by the specification
defect, in one line, and has been discharge-able since 2026-10-08.

**JUDGEMENT: this is the sharpest consequence of the propagation and the one
with a ledger correction attached.** The α-web's P-vs-NP bridge was being
carried as the axis's open frontier; it is a theorem about a degenerate
carrier. Both dependency-graph entries need updating. (Pablo-gated only if the
graph is treated as published text; otherwise it is a codex correction.)

## 3. Triage of the legacy claims

| legacy claim | status when re-pointed at `_Step` |
|---|---|
| `ClassP ⊆ ClassNP` | **SURVIVES** — `ClassP_Step_subset_ClassNP_Step`, proved without the rigged invariance clause |
| `ClassP ≠ ClassNP` | **WAS VACUOUS** — one-line consequence of the defect |
| `P_neq_NP_def` | **WAS VACUOUS** — unconditional (§2a) |
| `PvsNP_via_Hodge_disc5_Bridge_Open` | **WAS VACUOUS** — a theorem, not open (§2b) |
| every result with hypothesis `ClassP ≠ ClassNP` | **UNCONDITIONAL, hence content-free** — the hypothesis is free |
| the question itself | **OPEN** — `PvsNP_Step`, undischarged here and everywhere |

## 4. The honest side, landed

```lean
def P_equals_NP_Step : Prop := ∀ L : Language, InClassNP_Step L → InClassP_Step L
def P_neq_NP_Step : Prop := ¬ P_equals_NP_Step
```

* **`step_P_subset_NP : ClassP_Step ⊆ ClassNP_Step`** — `P ⊆ NP` survives.
* **`step_question_iff : P_equals_NP_Step ↔ PvsNP_Step`** — the two natural
  formulations of the honest question agree, so it is **one** well-posed target
  rather than two. (Axioms `[propext, Quot.sound]` only.)
* **`step_nondegenerate`** — `ClassP_Step` contains a language that is neither
  `∅` nor `univ`, which is exactly what `ClassP = {∅, univ}` failed.
* **`carriers_differ : ClassP ≠ ClassP_Step`** — the repair is not a relabelling.
* **`pnp_honest_status`** — all of the above as one citable conjunction.
  **The question itself is absent from it, because it is open.**

## 5. The α-web check — performed, not assumed. FACT

`InClassP_Step` and `InClassNP_Step` quantify only over `TM`, `ℕ → ℕ` bounds and
`BinString`. **No real-valued parameter occurs in either**, so no α-realisation
can hide in the re-pointed statements — the α-web is bypassed structurally, not
by convention. The realisation `∃ f, f ClassP = √2 ∧ f ClassNP = φ + ¼` attaches
to the **legacy** carriers only, and §2b shows what that attachment is worth
there: it is satisfied automatically.

## 6. What this does and does not buy

**Buys:** honest P and NP; `P ⊆ NP` proved; non-degeneracy; a single well-posed
honest question; and — the substantive part — **two kernel-checked
demonstrations that the legacy P≠NP claims are vacuous**, replacing an argument
about definitions with theorems.

**Does not buy:** anything about P vs NP. `P_neq_NP_Step` is undischarged in
both directions and nothing here bears on it. **The honest statement is: we now
have honest P and NP, `P ⊆ NP`, and the question is open.** The parked spectral
bridge stays parked and is untouched.

**OPEN / owed:** the two `GRAND_PROBLEM_DEPENDENCY_GRAPH` entries calling the
α-bridge "NAMED OPEN" are now provably wrong and should be corrected; the 75-file
textual re-pointing remains undone by choice (§1), with the honest status citable
instead; and I inventoried by `grep` over declaration-bearing lines, so the 371
figure counts claim-bearing *lines*, not distinct theorems — the distinct
load-bearing claims are the five rows of §3.

---

## Label summary

* **FACT (read from source):** the defect clause and `legacy_ClassP_ne_ClassNP`;
  `P_neq_NP_def_of_classes_distinct` and the `P_neq_NP_def` definition site;
  `open_bridge_iff_classes_distinct`; the dependency-graph "NAMED OPEN" entries;
  that the `_Step` definitions contain no real-valued parameter.
* **MEASURED (this session):** 75 files / 1,914 references / 371 claim-bearing
  lines; `EXIT 0` and the three-axiom bar on all seven new theorems.
* **JUDGEMENT (mine):** that "re-point everything" is the wrong unit of work and
  a citable status file is the proportionate repair; that §2b is the sharpest
  consequence and carries a ledger correction.
* **NOT established:** anything about `PvsNP_Step`; that the remaining 70-odd
  files contain no further load-bearing claim (I triaged the claim-bearing lines,
  not all 1,914 references).
