# CLOSURE AUDIT — the whole corpus, 2026-11-26

**Question.** `lake build PFClosure` compiles PF.lean's transitive imports. Everything
outside that closure is never compiled by any gate. After finding nine ungated
PF/KMS modules (`db81af85`), the question was: how much else is out there, and
does any of it matter?

**Answer, measured.** The ungated mass is compute, as `FINISH_LINE_2026-11-24`
said. But **66 hand-written modules declaring theorems were ungated**, including
the entire referee-facing Clay-axis statement family. 63 are now gated; one
genuine defect was isolated.

---

## 1. The numbers

| | |
|---|---|
| `.lean` modules under `PF/` | **10,879** |
| inside the closure, before | 1,702 |
| **outside** | **9,178** |
| of those, bulk generated families | **9,108 (99.2%)** |
| of those, hand-written, declaring theorems | **66** |
| **inside the closure, after** | **1,765** |
| aggregate `PFClosure` | **5,589 jobs, rc=0** (was 5,519) |

The bulk families, by population:

```
3749  PF.Analytic.FourierPanels          166  PF.Analytic.PilotBoxes
 763  PF.Numerics                         87  PF.Analytic
 239  PF.Analytic.RiemannXiBox0Panels    21 x ~228  RiemannXiBox{1xx,2,900}Panels
```

These are auto-generated interval-arithmetic panels. They gate nothing and are
*supposed* to be outside — building them is the compute budget, not a soundness
question.

### How the discriminator was chosen, and two wrong tries

Classifying by **filename** is the naming-sweep trap this corpus has been bitten
by. Classifying by **size uniformity** also failed: FourierPanels contains
`Assemble` files of 8,361 lines beside `Seg` files of 338, so a variance test
cleared 3,749 generated modules as "hand-written". What works is **directory
population** — a directory with dozens of ungated siblings is a bulk family;
PF/KMS had 22 files total. Threshold 40, and the split is unambiguous.

A third error worth recording: the first run of the audit reported `inside: 0`.
`PF.lean` sits *beside* the `PF/` directory, so walking `PF/` never read it and
the closure seeded empty. Caught because the number was impossible; the script
now carries a plausibility assert.

---

## 2. What was ungated, and why it mattered

All 66 **build individually** (65 built, 0 failed; one is the excluded module
below). They include:

* **the entire referee-facing Clay-axis family** — `Referee.StandardNS3DSubstrateStatement`,
  `StandardRHSubstrateStatement`, `StandardYM…`, `StandardPvsNP…`, `StandardHodge…`,
  and the five `*CapstoneTypedBridgeSubstrate` modules. These are the files a
  referee reads first, and no gate covered them.
* **recent spine work** — `Consciousness.SpacetimeEmergenceUpgrade_2026_11_24`,
  `Substrate.UnbiasedObserverIsUnique_2026_11_24`,
  `Substrate.UnbiasedObserverLosesInformation_2026_11_24`,
  `Cosmology.VortexHelicityParityOdd_2026_11_23`.
* **`PF.LogWeightedIntegral`** — 70 theorems, 2,269 lines, zero importers.
* three `Referee` disclosure files, including `HodgeMarkerAndAnchorDisclosure_2026_11_23`.

**An ungated module is not evidence of anything.** The globs omission
(`project_globs_hid_false_theorems_2026-11-22`) found three provably FALSE
theorems plus a nonexistent tactic inside never-compiled modules, all with 0
axioms and 0 `sorry`, so every grep-based gate reported them clean.

---

## 3. The defect the aggregate build found

Building each module **alone is not sufficient**. A module can compile in
isolation and still be unable to coexist in one environment. Only the aggregate
target finds that, and it did:

```
import PF.AxiomElimination_Definitions failed, environment already contains
'PrincipiaTractalis.TMConfig.rec' from PF.TuringEncoding
```

`PrincipiaTractalis.TMConfig` is declared in **four** places:

```
PF/TuringEncoding/Basic.lean:58              PF/AxiomElimination_Definitions.lean:92
PF/TuringEncoding.lean:78                    PF/Referee/AxiomEliminationDefinitionsRefutation…:68  (deliberate mirror)
```

The Referee mirror is intentional and in its own namespace — the refutation file
says it duplicates rather than imports "precisely because that module does not
compile". **That has changed:** `AxiomElimination_Definitions` builds today, and
`by_decidability_instances` now appears in it only inside comments (lines 241,
629) documenting the problem. So it was repaired since 2026-11-22. What remains
is purely the redeclaration.

**Repair, not yet done:** have `AxiomElimination_Definitions` use
`TuringEncoding`'s `TMConfig` rather than declaring its own, then gate it. That
also un-blocks the two Referee files that import it. Deliberately left as a
focused follow-up rather than bundled into a batch gating — editing a file whose
line numbers a refutation document cites deserves its own pass.

**Excluded at first, with cause recorded:** `AxiomElimination_Definitions`,
and the two `Referee` files alongside it. **63 of 66 gated** at that point.

### RESOLVED 2026-11-27 (`bf4871fe`) — 66 of 66 gated

Repaired by **nesting, not merging**, because the two structures are different
types and substituting either would have changed what `encodeConfig` encodes.
`PF.TuringEncoding` is the incumbent and keeps the bare name; the newcomer's
declarations moved to `namespace PrincipiaTractalis.AxiomElimination`. Nothing
renamed, line count unchanged, zero importers so no call site moved, and the
namespace structure was verified to be a single open/close pair before editing.

Kernel check rather than inference — both types now coexist, with distinct
alphabets:

```lean
example (c : PrincipiaTractalis.TMConfig) : List (Fin 3) := c.tape
example (c : PrincipiaTractalis.AxiomElimination.TMConfig) : List (Fin 2) := c.tape
```

**What gating it brings in, checked first.** The refutation proved two of that
module's theorems FALSE, so gating both needed to know what they say *now*. They
were repaired honestly on 2026-11-22/23: both are **conditional restatements**
with explicit `hTape`/`hSmall` hypotheses whose docstrings state outright that
the unconditional form is FALSE and refuted at `⟨1,0,[]⟩`; `encodeConfig_tape_eq`
has a real proof; and **Section 5 discloses the restatements' own near-vacuity
in the kernel** — "very nearly unsatisfiable, so neither restatement yet carries
the complexity content the original (false) statements were reaching for", with
`conditional_restatements_coverage_disclosed` stating the nat version is vacuous
outright. So the closure holds the restatements *and* their own disclosure. On
the record here so it is not rediscovered later as a defect.

The refutation's three docstring citations were repointed to the nested path, and
its removal condition — "when it is repaired, these should be replaced by imports
of the originals" — is now **MET**. That swap is left as a separate decision,
since it would make the refutation depend on the module it refutes.

| final state | |
|---|---|
| closure | **1,768 modules** |
| of the 66 audited, still ungated | **0** |
| aggregate `PFClosure` | **5,593 jobs, rc=0** |

---

## 4. Verification

| check | result |
|---|---|
| each of the 66 built alone | 65 pass, 0 fail |
| aggregate `PFClosure` after gating | **5,589 jobs, rc=0** |
| closure | 1,702 → **1,765** |
| `sorryAx` across the aggregate build | **0** |
| six Referee Clay-axis statements, imported together | clean, all on `[propext, Classical.choice, Quot.sound]` |

Wired by positional insert into PF.lean, never a `>>` append — PF.lean ends with
a doc block and appending has broken it twice.

---

## 5. Recorded, not chased

**116 declarations print "does not depend on any axioms"** in the aggregate
build. That phrase is the all-True-anchor signature. Some are legitimate —
`BrocardProblemFrameworkAttack.brown_4_5` is decidable arithmetic and genuinely
needs no axioms. Others deserve a look, because a Prop that mentions ℝ cannot be
axiom-free:

```
PF.Analytic.RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19.rh_framework_standard_substrate_position
PF.NavierStokes.Fefferman2000_LiteralClayNS3D_Statement_2026_06_19.literal_clay_NS_substrate_bridge_substrate_position
PF.Referee.BookClaimLedger.standard_fermat_at_pf_encoding_iff
```

This is a **pre-existing population**, not a consequence of gating, and the
~478 `True` declarations are already self-disclosed — `project_toe_capstone_verified_2026-11-22`
says not to re-litigate those. Named here so it is on the record with its
measurement.
