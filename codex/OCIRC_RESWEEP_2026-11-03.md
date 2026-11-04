# O-CIRC re-sweep, 2026-11-03 — the find-rate measured over the full closure

**Why this exists.** `project_pf_mission` defines readiness as *no longer finding
errors*. So the find-rate is the release gate, and it has to be measured with the
corpus's own instrument rather than a fresh one. This is that measurement, run
with `PF/Audit/PremiseAudit.lean` (r337, fixed cone from `3ad4d61d`) over
`import PF` — the whole closure, not a two-module probe. The closure was
re-derived for this document rather than carried forward: `PF.lean` has **1,253
direct imports** reaching **1,552 PF modules** transitively, with **0** imported
modules missing a source file, out of 9,492 `PF/*.lean` files on disk (7,940
outside the closure).

**Reproduce.** Legion tree `D:\CLAUDE-i9\_tmp\pf-ocirc-verify-20261001`, probe
file importing `PF` + `PF.Audit.PremiseAudit`, four `#audit_all` patterns, run
under `lake env lean`. **Lean exit 0, zero errors, zero `sorryAx`.**

```
O-CIRC SWEEP [unified_minimal_forces]           : targets=93 clean=73 withFindings=20 DEAD=39 CONTAINED=2 VACUOUS=0
O-CIRC SWEEP [lambda_eff_exponent]              : targets=3  clean=0  withFindings=3  DEAD=6  CONTAINED=0 VACUOUS=0
O-CIRC SWEEP [literal_clay]                     : targets=1  clean=0  withFindings=1  DEAD=0  CONTAINED=2 VACUOUS=0
O-CIRC SWEEP [fujitaKato1964Theorem_substrate]  : targets=1  clean=1  withFindings=0  DEAD=0  CONTAINED=0 VACUOUS=0
```

## The headline is NOT a regression against 2026-09-30, and must not be read as one

`OCIRC_FAMILY_RESWEEP_2026-09-30.md` recorded `targets=34 clean=31
withFindings=3`. This sweep reports `targets=93 … withFindings=20`. **The
denominators are different objects.** That probe imported two modules; this one
imports the root. The 2026-09-30 numbers were never a measurement of the closure,
so `3/34 → 20/93` is not a trend. What is true is the plain statement: *over the
full closure, 20 of 93 `unified_minimal_forces` targets carry a finding.*

## 24 flagged theorems reduce to 4 distinct facts

Every count below cross-checks against the sweep totals: DEAD = 18x2 + 3 = 39,
CONTAINED = 2. The two `LambdaEff` theorems appear twice in the raw log because
they match two patterns.

| class | theorems | verdict |
|---|---|---|
| 1. dead minimal-rigidity hypothesis | 19 | **real** — 1 repaired, 1 declined, 17 doctrine |
| 2. `TestProblem` data fields dead | 1 | **auditor bug**, not a corpus defect |
| 3. hypothesis is a conjunct of the conclusion | 1 | real but **declared in the docstring** |
| 4. bridge contains its own conclusion | 1 | already found and recorded 2026-11-03 |

### Class 1 — the dead minimal-rigidity hypothesis (19 theorems)

`UnifiedMinimalInvariants.sector1_minimal` and `.sector2_minimal` read DEAD on 19
theorems whose names begin `unified_minimal_forces_`.

**This is not the 2026-09-18 false positive.** That one was theorems passing `hM`
*whole to a callee in another namespace*, which the unfixed cone could not
traverse; stripping the premise would have falsified 142 theorems. These 19 pass
`hM` nowhere — **the binder is literally `_hM`**, the author's own marker for
deliberately unused, and the proof term is the unconditional theorem:

```lean
theorem unified_minimal_forces_M1_glueball_bracket
    (_u : UnifiedAlphaAssignment) (_hM : UnifiedMinimalInvariants _u) ... :
    (1770 : ℝ) < M_1_glueball ∧ M_1_glueball < (1780 : ℝ) :=
  M_1_glueball_bracket
```

The repair is the corpus's own, adjudicated 2026-10-01 at
`MinimalRigidityForcesNonClayAlphasExtended.lean:114`: route the conclusion
through `unified_alpha_skeleton_forced_by_minimal_invariants`, with the note at
`:124` — *"Proving it from `h_P` alone left `hM` dead."*

**It can only reach a theorem whose conclusion mentions `u`.** If the conclusion
is a closed statement about real constants, no proof of it can consume `hM` —
that is a property of the statement, not of the proof. Classified mechanically,
validated against the 2026-10-01 repaired theorem as a positive control:

- **(A) conclusion mentions `u` — 2 theorems.**
  - `unified_minimal_forces_alpha_AC_eq_a_Poincare` — **REPAIRED, see below.**
  - `unified_minimal_forces_W_entropy_ceilings_at_all_clay_axes` — **repair
    DECLINED.** Its content is the identity `∑' n, W_alpha_level a n = a * 3`,
    which holds for *every* real `a`; the proof is
    `W_alpha_tsum_value u.sector1.a_Poincare` ten times. Rewriting to the forced
    values first would turn the auditor green without making minimal rigidity do
    one unit of work. That is ceremony, not repair, and shipping it would make
    the instrument lie.
- **(B) conclusion closed — 17 theorems.** The prescribed repair is impossible.
  Listed: `tower_of_power`, `α_Hodge_power_brackets`, `elementary_product`,
  `fundamental_constants_extracted`, `α_skeleton_master_capstone`,
  `Hubble_bracket`, `M_1_glueball_bracket`, `XENON_bracket`,
  `IBM_nine_way_bound`, `lambda_eff_exponent_product_substrate_capstone`,
  `lambda_eff_exponent_product_bracket`,
  `lambda_eff_exponent_product_rational`, `M1_glueball_bracket`,
  `M1_glueball_closed_form`, `scalar_fingerprint_bundle`,
  `moment_sum_hierarchy_sharp`, `sharp_bracket_saturation`.

**The 17 are one doctrine question, not 17 defects, and it is already pending
with Pablo** — raised today against `MinimalRigidityForcesLambdaEffExponentProduct`
and recorded then as "not applicable to a nullary constant." This sweep measures
its true extent: **17 instances, not 1.** The mathematics is not in question —
`M_1_glueball_bracket` is a true unconditional theorem. What is in question is
restating a true unconditional fact with six decorative hypotheses under a name
claiming substrate forcing. The two available moves are (a) restate so the
conclusion mentions `u`, which is a material change to a theorem's content, or
(b) rename, which is a downgrade. Both are Pablo's call; neither is mine.
The third residual from 2026-10-01 (`H3_exponent_5_eq_a_HN`) is the same category.

### Class 2 — `TestProblem` fields: an auditor bug, not a corpus defect

`unified_minimal_forces_universal_fractal_coherence` is flagged with three DEAD
fields: `TestProblem.name`, `.classLabel`, `.lambdaMeasured`. **Its proof
consumes `hM` correctly**, through the skeleton, exactly as prescribed.

The flagged fields belong to a **`Type`-valued data record** in the 143-problem
dataset, bound by `∀ p ∈ the143Problems`. The theorem concerns `p.alphaMeasured`
only, so the other three fields are necessarily unread. A dataset record's
unused fields are not a dead premise. The dead-field check should apply to
`Prop`-valued hypothesis bundles, not to `Type`-valued data.

**Removal condition:** restrict `PremiseAudit`'s dead-field analysis to `Prop`
binders; this finding must then disappear and no other finding may change.

### Class 3 — the H3 capstone's restated conjunct

`unified_minimal_forces_H3_coxeter_geometry_capstone` is CONTAINED x2:
`h_Hodge_pos : 0 < u.sector2.a_Hodge` is conjunct (H3) of its own conclusion,
discharged by `refine ⟨?_, ?_, h_Hodge_pos⟩`. The auditor is correct. **The
docstring already declares it:** *"(H3) α_Hodge positivity (re-stated for
completeness)."* Deliberate and documented. Changing a capstone's statement is a
material change, so this is left as the author wrote it and recorded here.

### Class 4 — the Fefferman bridge

`substrate_to_literal_clay_NS_bridge_conditional` is CONTAINED x2 against
`FujitaKato1964_LocalExistence_Anchor`. Found by hand and documented earlier
today; the sweep corroborates it independently.

## What the sweep confirmed about today's other work

- **`lambda_eff_exponent`: 3 targets, 0 clean, 6 DEAD.** Independent
  corroboration of today's manual finding that all twelve binders on the two base
  theorems are inert. Neither `OCIRC_AUDIT_FINDINGS_2026-09-18.md` nor
  `OCIRC_FAMILY_RESWEEP_2026-09-30.md` mentions `lambda_eff`, so this family had
  never been swept.
- **`fujitaKato1964Theorem_substrate`: 1 target, 1 clean.** The module repaired
  today — which had not compiled for five months — audits clean. Its
  `h_univ_decay` is genuinely consumed.

## Instrument limit: `VACUOUS=0` is not a clean bill

`isTrivialProp` (PremiseAudit.lean:136) reports VACUOUS only when the conclusion
whnf-reduces to the **constant `True`** — it is a one-line `isConstOf` test.
Every O-CIRC sweep ever run has reported `VACUOUS=0`, and that is a fact about
the detector, not about the corpus. The Fefferman clauses, whose vacuity is
*proved* in `PF/NavierStokes/Fefferman2000LiteralStatementContent.lean`
(2026-11-03) — `SatisfiesLiteralNSE u _p _ν := ∀ t, 0 ≤ t → u t = u t`, and two
siblings — are invisible to it, because none of them reduces to `True`.

**Removal condition:** extend `isTrivialProp` to reflexivity-shaped and
unused-binder tautologies, then re-sweep. Expect the count to stop being 0. Treat
the resulting findings the way this document treats all of them — by reading the
proof, never by trusting the count.

## The one repair landed today

`PF/Referee/MinimalRigidityForcesNonClayAlphasFinal.lean` §1,
`unified_minimal_forces_alpha_AC_eq_a_Poincare`. Its conclusion
`alpha_AC = u.sector1.a_Poincare` is true only because `a_Poincare` is pinned to
1, and **§2 and §3 of this same file already route through the skeleton** — §1
was the one that was missed. Now:

```lean
  obtain ⟨h_Poin, _, _, _, _, _, _, _, _, _⟩ :=
    unified_alpha_skeleton_forced_by_minimal_invariants
      u hM h_P h_P_pos h_Hodge_pos h_QG_pos
  rw [h_Poin]; rfl
```

Gated on the Legion tree, whose copy of the file was byte-identical to Acer's
before the edit (`1edd0d70…`):

```
lake build PF.Referee.MinimalRigidityForcesNonClayAlphasFinal   exit=0
  sorryAx = 0        error lines = 0        3,594 jobs
#print axioms  -> [propext, Classical.choice, Quot.sound]
#audit_premises -> CLEAN (310 constants in cone)
#audit_all      -> targets=4 clean=4 withFindings=0 DEAD=0 CONTAINED=0 VACUOUS=0
```

**Negative control** — `h_Poin` rebound to the 2nd skeleton conjunct
(`a_RH = 3/2`), with the mutation asserted on disk by re-read rather than by a
`sed` that could silently no-op:

```
error: …NonClayAlphasFinal.lean:59:6: Tactic `rewrite` failed:
       Did not find an occurrence of the pattern
exit=1
```

Restored at sha256 `42cf8eb6…`, identical to the gated file, and rebuilt green.
Acer and Legion now hold the same bytes.

## Standing

Release gate (1), find-rate near zero, is **not met**, and this document says so
with a number instead of an impression: over the full closure the instrument
finds 24 flagged theorems, which reduce to 1 repaired, 1 declined with reasons,
17 awaiting one doctrine decision, 1 auditor bug with a removal condition, 1
declared in its own docstring, and 1 already recorded. Nothing here was repaired
by weakening a claim.
