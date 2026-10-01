# O-CIRC re-sweep with the fixed cone — `MinimalRigidityForces*`, 2026-09-30

**Headline: the family is clean. The "35 of 35 with findings, 0 clean" result was a
measurement artifact inside r337's own auditor, not a defect in the corpus.**

| | 2026-09-18 (buggy cone) | 2026-09-30 (fixed cone) |
|---|---|---|
| targets | 35 | **40** |
| CLEAN | 0 | **37** |
| with findings | 35 | **3** |
| DEAD lines | 70 | **6** |
| CONTAINED lines | 15 | **0** |
| VACUOUS lines | 0 | 0 |

A second probe over the `unified_minimal_forces` target set, same run:
`targets=34 clean=31 withFindings=3 DEAD=6 CONTAINED=0 VACUOUS=0`.

## Why the first number was wrong

`PremiseAudit.isProjectStruct` already accepted all three roots, but `cone` was
handed only `#[nsPrefix]`, whose default is `` `PrincipiaTractalis ``. The Referee
callees live under `` `PF. ``. So when the auditor walked a `PF.Referee.*` theorem it
saw the callee as a constant and **never traversed into it** — it never observed the
projections the callee consumes, and reported the passed-whole hypothesis fields DEAD.

Any hypothesis passed whole to a callee in the other namespace looked dead.

Demonstrated on a single theorem, `unified_minimal_forces_alpha_NS_Kolmogorov_bridge_parametric`:

| traversal prefix | result |
|---|---|
| `` `PrincipiaTractalis `` (old default) | DEAD = 2, clean = 0 |
| `` `PF `` | DEAD = 0, clean = 1 |

Same theorem, same proof. Only the prefix differs.

Fix: `auditPrefixes = #[nsPrefix, `PrincipiaTractalis, `PF]`, applied at both call
sites (`auditDecl`, `elabAuditPremises`). Commit `3ad4d61d`.

## What the hypotheses actually do

`unified_alpha_skeleton_forced_by_minimal_invariants` consumes both fields:

```
sector1_forces_a_YM_eq_two u hM h_P
framework_alpha_unique_under_perelman_anchor_minimal u.sector1 hM.sector1_minimal h_P
sector2_minimal_rigidity_capstone u.sector2 u.sector1.a_YM hM.sector2_minimal h_YM
```

The instruction the bad finding generated was to strip the
`UnifiedMinimalInvariants` premise from 142 theorems across 51 files. **That edit
would have turned 142 true theorems into false ones** — the nine α-values are not
forced without the invariants. The edit was stopped before it was applied.

`PF.Referee.MinimalRigidityForcesAlphaArchitecturalIdentities` now gates PRISTINE,
exit 0.

## The 3 residual targets

These still report `UnifiedMinimalInvariants.sector1_minimal` and `sector2_minimal`
DEAD under the fixed cone:

- `PF.Referee.MinimalRigidityForcesNonClayAlphasExtended.unified_minimal_forces_alpha_LonelyRunner_eq_a_Poincare`
- `PF.Referee.MinimalRigidityForcesH3CombinatorialStructure.unified_minimal_forces_H3_exponent_1_eq_a_Poincare`
- `PF.Referee.MinimalRigidityForcesH3CombinatorialStructure.unified_minimal_forces_H3_exponent_5_eq_a_HN`

They are open repair candidates, **not** yet confirmed defects. The lesson of this
document is that a DEAD report must be read against the traversal before it is acted
on: check by hand whether each of these three passes the hypothesis whole into a
further namespace the cone still does not reach. Only then consider a repair, and a
repair here means supplying the missing consumption step, never stripping a binder.

## What this does NOT correct

The corpus-wide headline — **213 capstones, 99 CLEAN, 114 with findings** — was
measured with the buggy cone and is therefore suspect in the same direction:
pass-through hypotheses were over-reported as DEAD, so the true clean count is
higher than 99. The same applies to the full-sweep totals DEAD = 432 and
CONTAINED = 138.

Those numbers have been annotated in place rather than guessed at. **Retirement
condition:** run the full 213-target sweep with the fixed cone, replace the totals,
and delete the annotations. That run needs Lean compute and is queued behind the live
`RiemannXiBottomEdgeAtMinus15_r331d` panel build on Acer — starting it now would
contend for the same RAM (one panel worker measured 4.4 GB RSS, panels peak near 9 GB)
and kill a build that is two days into a ~6.5-day job.

## Documents corrected in this pass

- `codex/PF_STATE_STATEMENT_2026-09-29.md` §7
- `codex/STATUS_SNAPSHOT_EXTERNAL_REVIEW_2026-09-29.md`
- `codex/GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-09-27.md` (two places + corpus totals)
- `codex/GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-09-29.md` (two places)
- `codex/BOOK_VS_CODE_PARITY_2026-09-29.md`
- `codex/OCIRC_AUDIT_FINDINGS_2026-09-18.md` — Finding 2 marked WITHDRAWN; the dated
  table is retained as the record of what the auditor reported that day, not as the
  state of the corpus
- `Principia_Fractalis_master_folder/frontmatter/version_history.tex` — the gate
  paragraph, the O-CIRC sweep paragraph, and the 114 count

## Provenance

- Corrected measurement: `/tmp/sweep337.log` on Acer, written 2026-09-30 16:18 by
  `probe_sweep337.lean` against `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE`.
- Cone fix and its in-situ validation: commit `3ad4d61d`.
- Original finding: commits `9c1c2351`, `ebe9c8af`;
  `codex/OCIRC_AUDIT_FINDINGS_2026-09-18.md` Finding 2.
- No Lean source was modified in this pass. Documentation only.
