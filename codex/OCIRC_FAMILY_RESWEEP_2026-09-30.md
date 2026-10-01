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

## The 3 residual targets — hand-checked 2026-10-01, all three real

Checked the way this document says a DEAD report must be checked: by reading the
proof, not by trusting the count. Each proof is two tactics long, so the reading is
exhaustive rather than a sample. **All three findings are correct.** There is no
callee for the cone to fail to traverse — there is no callee at all.

| theorem | proof | what it consumes |
|---|---|---|
| `…NonClayAlphasExtended.unified_minimal_forces_alpha_LonelyRunner_eq_a_Poincare` | `rw [h_P]; rfl` | `h_P` only |
| `…H3CombinatorialStructure.unified_minimal_forces_H3_exponent_1_eq_a_Poincare` | `rw [h_P]; norm_num` | `h_P` only |
| `…H3CombinatorialStructure.unified_minimal_forces_H3_exponent_5_eq_a_HN` | `show (5 : ℝ) = (5 : ℝ); rfl` | **nothing** |

The conclusions hold definitionally: `alpha_LonelyRunner := 1` in
`PF/NumberTheory/LonelyRunnerFrameworkAttack.lean`, and
`def alpha_HN : ℝ := 5` at `PF/NumberTheory/HadwigerNelsonFrameworkAttack.lean:136`.
So `((5 : ℕ) : ℝ) = alpha_HN` is `5 = 5`, and all six of its hypotheses — not only the
two minimality fields — are inert.

**The contrast inside the same two files is what makes this a finding rather than a
suspicion.** Their siblings do consume `hM`, through the skeleton, and the fixed cone
reports them clean:

```
obtain ⟨_, h_RH, _, …⟩ := unified_alpha_skeleton_forced_by_minimal_invariants
                               u hM h_P h_P_pos h_Hodge_pos h_QG_pos
```

`unified_alpha_skeleton_forced_by_minimal_invariants` is invoked 7 times in
`MinimalRigidityForcesNonClayAlphasExtended.lean` and 3 times in
`MinimalRigidityForcesH3CombinatorialStructure.lean`. The auditor marks those targets
clean and these three dead, in the same files, under the same traversal. It is
discriminating correctly.

### What the defect actually is, and what repair means here

These three are not false theorems. They are **true statements whose names claim more
than their proofs do**: `unified_minimal_forces_X` asserts that minimal rigidity
forces X, while the proof obtains X from `h_P` plus a definitional unfolding. Same
shape as the r301 finding — valid theorem, carries none of the information its name
advertises.

Repair is therefore neither stripping the binder nor renaming the theorem. Stripping
`hM` would yield a stronger theorem with a false name; renaming downward is a
downgrade. The repair is to **route the conclusion through the forced skeleton**, as
the siblings already do, so that minimal rigidity is what establishes the result and
the name becomes accurate.

For the first two that is a mechanical change: `obtain` the skeleton from `hM` and
take the `a_Poincare` component instead of rewriting with `h_P`.

The third does not admit that repair as stated. `((5 : ℕ) : ℝ) = alpha_HN` is a
definitional identity; no hypothesis can be made load-bearing in it without changing
the statement. The open question underneath is whether `α_HN = 5` is **forced** by the
skeleton or merely **defined** as 5 — and the neighbouring
`unified_minimal_forces_H3_exponent_sum_eq_a_RH_mul_a_YM_mul_a_HN` routes `h_RH` and
`h_YM` through the skeleton but still supplies the 5 definitionally, which suggests
defined. Settling that is substrate-level work on the α-cascade, not an edit to this
theorem, and it is the same question §12.3 of the state statement raises about the
Perelman anchor: a named value that is supplied rather than derived.

No Lean source was edited in this pass. These three are now recorded as confirmed
findings with a named repair shape, not as counts.

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

### Legion cannot substitute — checked 2026-10-01, NEGATIVE

Worth ruling out explicitly, because Legion does hold a fixed-cone
`PremiseAudit.olean` (built 2026-09-30 14:59) and looks at first glance like spare
capacity. It is not. `#audit_all` selects its targets from `env.constants`, so the
target set is exactly what the probe imports, and Legion's tree at
`D:\CLAUDE-i9\_tmp\pf-ch08-bianchi-bookkeeping-20260926\PF_Lean4_Code` is a partial
snapshot:

- 1,318 oleans of the corpus's ~4,380;
- 439 of the 536 capstone-bearing modules have oleans, so the sweep would silently
  audit a subset and report a target count that is not comparable to 213;
- **1 of the 40 `MinimalRigidityForces*` modules** is built, so it cannot even
  reproduce the family figure above;
- no `PF/Audit/` source directory at all — the audit olean was dropped in, not built
  from the tree.

Making Legion capable means rebuilding its tree, which is days of its own RAM on
Pablo's interactive machine. Available, not free, and not taken unilaterally. Do not
re-derive this; the full re-sweep waits for Acer.

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
