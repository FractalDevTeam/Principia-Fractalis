# O-CIRC restatement campaign, 2026-11-04 — the 17 closed conclusions now mention `u`

**Decision.** `OCIRC_RESWEEP_2026-11-03.md` closed with one item that was not
mine to settle: **17** theorems named `unified_minimal_forces_*` whose
minimal-rigidity hypothesis was DEAD, because each concluded a *closed*
sentence — about the framework's global α-constants, or about a derived
physical constant. No proof of a closed sentence can consume a hypothesis
about `u`, so the prescribed 2026-10-01 repair could not reach them. The two
available moves were **restate** (a material change to content) or **rename**
(a downgrade).

Pablo, 2026-11-04: **restate them so the conclusion mentions `u`.** This
document is what that produced, and what it could not reach.

**Result in one line.** 13 of the 17 restated, **DEAD = 0** on every one of
them; over the full closure the family's DEAD findings fall **39 → 11** and
clean rises **73 → 87**; `lake build PF` exit 0 over **5,265 jobs** with
**0 errors, 0 `sorryAx`, 0 `ofReduceBool`**; 4 declined on measured grounds,
with the corpus's own prior adjudication quoted rather than my judgement
substituted. Every DEAD finding that remains anywhere in the closure is either
a known auditor bug or a deliberate decline — **none is a theorem that could be
honestly repaired** (§4).

---

## 1. The device, and why it is not a relabelling

Two devices, both the author's own.

**(A) The α-bridge — 8 theorems.** New module
`PF/Referee/MinimalRigidityForcesAlphaSkeletonBridge.lean` proves that under
substrate-rigidity `u`'s *own* α-fields **are** the framework's global
α-constants:

```
u.sector1.a_RH = α_RH    u.sector1.a_YM = α_YM     u.sector1.a_BSD = α_BSD
u.sector1.a_NS = α_NS    u.sector2.a_P  = α_P      u.sector2.a_Hodge = α_Hodge
u.sector2.a_NP = α_NP    u.sector2.a_QG = α_QG
```

Each component is `unified_alpha_skeleton_forced_by_minimal_invariants`
composed with the definitional value of the global constant. A theorem that
asserted `P(α_Hodge, α_QG, …)` is then restated as
`P(u.sector2.a_Hodge, u.sector2.a_QG, …)` — **the same mathematical content,
now predicated of the substrate assignment** — and proved by rewriting along
the bridge and applying the original unconditional theorem. The statement
transformation is a mechanical token substitution, which is the point: it is
auditable line by line, and **395** α-occurrences were substituted.

**(B) The forced α-expression — 5 theorems.** For the empirical predictions
there is no α in the statement to substitute, because the constants are built
from `Real.pi`, `0.95`, `67.4`, `14.134725`, `197.2`. Here the device is the
one the author already used in
`MinimalRigidityForcesCrossDomainExperimentalWins.lean` §1–§2: **replace the
numeral by the α-expression minimal rigidity forces it to equal.**

| numeral | substrate expression | corpus theorem relied on |
|---|---|---|
| `10` in `π/10` | `u.sector1.a_YM * α_HN` | `unified_minimal_forces_H3_coxeter_number_eq_a_YM_mul_a_HN` |
| `2` in `(2·t₁·Λ_QCD)/π` | `u.sector1.a_YM` | skeleton conjunct 3 |

**Why this is strictly stronger than what it replaced.** The restated
conclusions are **false for a general assignment** — take `a_Hodge = 1` and
`a_Hodge^2 = a_Hodge + 1` fails; take `a_YM` large and the glueball bracket
fails. So `hM` is load-bearing in the strongest available sense: remove it and
the theorem is not merely unproved, it is false. That is exactly what makes
the name `unified_minimal_forces_…` true of the statement it labels, which is
what the auditor was objecting to. **Nothing was renamed and nothing was
withdrawn**; the unconditional global-constant forms remain proved in
`PF/CrossMillenniumMoreInvariants.lean` and
`PF/FrameworkExperimentalWinsCapstone.lean`.

---

## 2. The 13 restated

### Group A — bridge substitution (8)

| theorem | α-occurrences | axes |
|---|---|---|
| `unified_minimal_forces_moment_sum_hierarchy_sharp` | 104 | 9 |
| `unified_minimal_forces_scalar_fingerprint_bundle` | 89 | 9 |
| `unified_minimal_forces_α_skeleton_master_capstone` | 67 | 9 |
| `unified_minimal_forces_tower_of_power` | 56 | 4 |
| `unified_minimal_forces_sharp_bracket_saturation` | 36 | 9 |
| `unified_minimal_forces_elementary_product` | 21 | 7 |
| `unified_minimal_forces_α_Hodge_power_brackets` | 14 | 1 |
| `unified_minimal_forces_fundamental_constants_extracted` | 8 | 4 |

The last of these reads, after restatement:

```lean
    Real.pi = u.sector2.a_QG ^ 2 / u.sector1.a_YM ∧
    Real.sqrt 2 = u.sector2.a_P ∧
    PrincipiaTractalis.phi = u.sector2.a_Hodge ∧ …
```

— π, √2 and φ extracted from the substrate's own axes, which is what the
file's title claimed all along and now actually says.

**One of these is only partly restated, and `CLEAN` must not be over-read.**
`unified_minimal_forces_sharp_bracket_saturation` is an 8-clause bundle. Only
clauses **(S7) Σα** and **(S8) Σα²** mention `u` after restatement; (S1)–(S6)
— XENON, Hubble, M₁, the IBM Galois-pair gap, the Λ_eff exponent product and
the P discriminant — remain brackets on closed constants, inherited from the
unconditional theorems that prove them. The auditor now reports the theorem
CLEAN, and that is literally correct: `hM` *is* consumed, via (S7)–(S8). But
six of its eight clauses are still closed sentences, one of them the Λ_eff
product this document declines in §3. The honest reading is: the bundle's
hypothesis is load-bearing, not that every clause in it is substrate-derived.

### Group B — forced α-expression (5)

| theorem | restated conclusion |
|---|---|
| `unified_minimal_forces_XENON_bracket` | `1.298 < 1 + (π/(a_YM·α_HN))·0.95 < 1.299` |
| `unified_minimal_forces_Hubble_bracket` | `74 < 67.4·√(1 + (π/(a_YM·α_HN))·0.95·0.7) < 75` |
| `unified_minimal_forces_M_1_glueball_bracket` | `1774 < t₁·Λ_QCD/(π/a_YM) < 1775` |
| `unified_minimal_forces_M1_glueball_closed_form` | `M_1 = (a_YM·t₁·Λ_QCD)/π` |
| `unified_minimal_forces_M1_glueball_bracket` | `1770 < (a_YM·t₁·Λ_QCD)/π < 1780` |

One new lemma was needed and written:
`unified_minimal_forces_XENON_prediction_parametric`, the sibling of the two
the author already had for Hubble and M_1.

### Carried along (4 composing capstones)

`tower_of_power_substrate_capstone`,
`experimental_wins_substrate_capstone`, `M1_glueball_substrate_capstone`,
`substrate_rigidity_end_to_end_meta_capstone` — restated to match the
components they bundle. Their proofs are unchanged; only their statements
moved.

---

## 3. The 4 DECLINED, on measured grounds

These are **not** restatable without manufacturing substrate content that the
corpus itself says is absent. Declining them is the same judgement as the
2026-11-03 decline of `W_entropy_ceilings_at_all_clay_axes`: routing them
would turn the auditor green without making minimal rigidity do one unit of
work.

**`unified_minimal_forces_IBM_nine_way_bound`.** Its conclusion is
`nineWayJointMatchProbabilityBound eps9_hardware ≤ 1/10^15`, and
`nineWayJointMatchProbabilityBound ε = (2ε/1.7)^9`
(`PF/IBMHardware9WayEvidence.lean:237,240`). The bound depends on the hardware
precision `ε` and the search-window width `1.7 = 2.6 − 0.9` — **no α-value
appears in it at all**, and the nine forced values are irrelevant to it
because *any* nine fixed targets give the same random-match probability. The
theorem's own docstring already says so: *"the IBM hardware precision and
search range are independent of the substrate hypothesis."* Only the exponent
`9` connects to the skeleton, and it is a count of axes, not an α.

**The three `Lambda_eff_exponent_product` theorems.**
`Lambda_eff_exponent_product := N_78pi * consciousness_threshold_capstone *
Rf_QG_unit_modulus_capstone` (`PF/Cosmology/LambdaEffParameterFreeCapstone.lean:93`),
whose factors are the numerals `78π`, `0.95`, `1.1875`. No α occurs. The `QG`
in `Rf_QG_unit_modulus_capstone` is provenance in a *name*: the value is
`1.1875` and `capstone_step3_Rf_QG_modulus` is proved by `rfl`.

Decisive, and it is the corpus's own adjudication, not mine —
`PF/Priority4SubstrateDischarge.lean:129–130`:

> `78π · (19/20) · (19/16) = 276.44`. The two remaining factors
> (c_2 = 19/20 **RETRACTED**, R_f modulus 19/16 **declared not derived**)

Substituting `19/16 = |R_f(u.sector2.a_QG, 1)|` would require proving an
identity the corpus has recorded as *declared, not derived*, and `19/20` was
**retracted** (`03b05e15`, 2026-11-02). Dressing a retracted and an
undeclared constant as substrate-forced is the precise failure mode this
whole programme exists to prevent. **These three remain flagged, and they
should.** Their 8 DEAD findings are the honest residue of this sweep.

---

## 4. The full-closure sweep, before and after

Re-run with the same four patterns as `OCIRC_RESWEEP_2026-11-03.md`, over
`import PF` — the whole closure, so the numbers are directly comparable.
`lake build PF`: **exit 0, 5,265 jobs, 0 errors, 0 `sorryAx`, 0 `ofReduceBool`,
0 `native_decide` axioms.**

| pattern | 2026-11-03 | 2026-11-04 |
|---|---|---|
| `unified_minimal_forces` | targets 93, clean 73, **DEAD 39** | targets 95, clean **87**, **DEAD 11** |
| `lambda_eff_exponent` | 3 targets, 0 clean, DEAD 6 | unchanged — declined, §3 |
| `literal_clay` | 1 target, CONTAINED 2 | unchanged — recorded 2026-11-03 |
| `fujitaKato1964Theorem_substrate` | 1 target, clean | unchanged |

`targets` rose 93 → 95 because this campaign added two theorems (the bridge and
the XENON parametric sibling), both CLEAN.

**The important part is not that DEAD fell from 39 to 11. It is what the 11
are.** Across the whole closure, every remaining DEAD finding now sits in one of
exactly six declarations, and not one of them is a theorem that could be
honestly repaired:

| declaration | DEAD | why it is still here |
|---|---|---|
| `unified_minimal_forces_universal_fractal_coherence` | 3 | **instrument bug** — the `forallTelescope` artifact diagnosed 2026-11-03; not a corpus defect |
| `unified_minimal_forces_IBM_nine_way_bound` | 2 | declined, §3 — no α occurs in the bound |
| `unified_minimal_forces_lambda_eff_exponent_product_rational` | 2 | declined, §3 |
| `unified_minimal_forces_lambda_eff_exponent_product_bracket` | 2 | declined, §3 |
| `lambda_eff_exponent_product_substrate_capstone` | 2 | declined, §3 |
| `unified_minimal_forces_W_entropy_ceilings_at_all_clay_axes` | 2 | declined 2026-11-03 — routing it would be ceremony |

(The raw totals double-count: the two `lambda_eff` theorems match both patterns,
so the 11 + 6 printed by the sweep are **13 distinct findings**, as listed.)

So the honest statement of where this class stands: **zero remaining DEAD
findings come from a theorem whose statement could be repaired.** Three are an
auditor bug with a known-wrong obvious fix; ten are deliberate declines with
the corpus's own evidence quoted. That is the floor this instrument can reach
without either fixing the auditor or changing what the declined theorems claim.

## 5. Gates

```
lake build (8 modules + manifest)   exit 0, 3,618 jobs, 0 errors, 0 sorryAx
#print axioms, every new/changed declaration
                                    [propext, Classical.choice, Quot.sound]
unused simp arguments in touched files                                     0
```

`#audit_premises` over all 23 affected declarations:

| | count |
|---|---|
| CLEAN | **16** |
| DEAD on a restated theorem | **0** |
| CONTAINED, declared (§6) | 5 |
| DEAD, all in the 4 declined | 8 |

**Negative control, kernel-checked on every build.**
`bridge_conclusion_fails_without_rigidity` exhibits an assignment (every axis
`0`) for which the bridge's `a_Hodge` component is **false**, since
`α_Hodge = φ ≠ 0`. The bridge therefore cannot be proved without consuming the
rigidity hypotheses. It is a theorem in the file, not a comment, so it is
re-checked by the kernel rather than trusted.

**Manifest.** The bridge is registered in `PF.lean` (imports 1,253 → 1,254).
A module outside `PF.lean` is not re-verified by `lake build`, so an
unregistered bridge would sit outside the gate it exists to serve.

---

## 6. ⚠ What the restatement CREATED, stated plainly

Restating in terms of `u` had a consequence that must not be buried: two
clauses, once predicated of `u`, are **literally fields of the hypothesis**.

```
u.sector2.a_Hodge ^ 2 = u.sector2.a_Hodge + 1   is  hM.sector2_minimal.inv_Hodge_quad
u.sector2.a_QG ^ 2 = 2 * Real.pi                is  hM.sector2_minimal.inv_QG_sq_two_pi
```

Under the old global-constant statements these were substantive facts about
`φ` and `√(2π)`. Under the new ones they are hypotheses, and the auditor
reports CONTAINED on `α_skeleton_master_capstone` (2), `tower_of_power` (1)
and `substrate_rigidity_end_to_end_meta_capstone` (2). **Those reports are
correct.**

They are kept rather than deleted because the clauses are true and these
bundles are cited elsewhere as complete layer enumerations; dropping two of
nine squares would shrink published content to quiet an instrument. A
`DECLARED REDUNDANCY` note now sits at the top of each of the three files.

**Removal condition** — this note is a declaration, not a resolution. Either
(a) the bundles are re-cut so each layer states only what is *downstream* of
the invariants, with the invariant clauses cited separately, or (b)
`#audit_premises` grows a `DECLARED` verdict so a deliberate re-statement is
distinguishable from an accidental one. Until one lands, the 5 CONTAINED
stand on the record.

One CONTAINED was **repaired** rather than declared: the bridge's first draft
carried a `u.sector1.a_Poincare = α_Poincare` conjunct, which is definitionally
the `h_P` hypothesis. The auditor flagged it, correctly; the conjunct was
removed and callers derive the Poincaré axis in one line from `h_P`. The
bridge now audits CLEAN.

---

## 7. Instrument limits, carried forward unchanged

Both limits recorded in `OCIRC_RESWEEP_2026-11-03.md` are still live and
neither was touched by this campaign:

1. **`VACUOUS = 0` has never meant anything.** `isTrivialProp` tests
   `isConstOf True` and nothing else, so proved-vacuous clauses are invisible
   to it.
2. **The `TestProblem` finding is a `forallTelescope` artifact**, and the
   obvious `Prop` filter is the wrong fix — it would also stop auditing
   `u : UnifiedAlphaAssignment`, the carrier of the finding class this whole
   campaign addressed.
