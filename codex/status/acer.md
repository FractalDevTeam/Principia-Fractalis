# ACER — session status

**Owner:** Acer session (Linux server 192.168.0.94, Opus 4.7, 1M ctx).
**Lane:** YM Fubini discharge → unconditional `wilson_reflection_positivity`.
**Pinned by:** `codex/INSTRUCTIONS_FOR_EVERY_AI_2026-10-21.md` §2 ACER.

## Current task (in flight)

**Steps 5 and 6 of the Fubini discharge memo** — Pablo direct order,
2026-10-21.

- Step 5: Φ construction. Needs a *second* glue (Λ_+ vs rest) parallel to the Λ_- glue already landed at `c5080d4b`; equivalently a nested `piEquivPiSubtypeProd` applied with an `isPlusLink` predicate. Then Φ is a partial Bochner integral over the Λ_+ component.
- Step 6: final Fubini apply + Haar-inversion change-of-variable → `wilson_reflection_positivity` with empty hypothesis list.
- Flock discipline (§1): every `lake build` on this machine takes `flock -x /tmp/pf_lean_build.lock` before invoking lake. March builds and YM builds share the same lock. Dual builds OOM at 15 GB.

## Last landed commit (origin/master)

`4e5bbb10` — action/Boltzmann symmetry on glued sector configs
(`WilsonSectorGlueAction_2026_10_21.lean`, 4 decls, three-axiom bar).

## Six-step mapping (where we are)

| # | Scope | Status | Commit |
|---|---|---|---|
| 1 | Λ_- Pi inv-invariance | LANDED | `42d6ad7a` + `5ad9b21a` |
| 1b | θ̂ factorization + measure-preserving | LANDED | `2d1a840e` + `5fd31285` |
| 1c | Change-of-variable identities under θ̂ | LANDED (off-plan — gives Hermiticity directly) | `9a8f1ddd` |
| 2 | `gaugeFieldGlue` + restriction identities + measurability | LANDED | `c5080d4b` |
| 3 | Action/Boltzmann symmetry on glue (X-independence form; weaker than memo's `S_- glue = S_+ glue ∘ θ`) | LANDED | `4e5bbb10` |
| 4 | `supportedOnPlusZero_glue` + `_factor_eq` | LANDED | `c5080d4b` |
| 5 | Φ construction (needs Λ_+ second glue) | IN FLIGHT | — |
| 6 | Final Fubini apply, headline empty-hypothesis | IN FLIGHT | — |

Acceptance target (§2.3): `wilson_reflection_positivity` with empty
hypothesis list, kernel-clean, three-axiom bar.

## Crossings / files other sessions may read-touch

- `PF/YangMills/*` is my lane. No concurrent writer expected.
- `PF/TransferOperator.lean` was named in the §0B asymmetry study — not touched by me.
- `/tmp/pf_lean_build.lock` is SHARED with Legion's march runner (`codex/march_box.sh`). Legion's `5c48f698` note confirms the shared-flock contract.

## Conflict I detected on first-run (2026-10-21)

The §0B asymmetry study question (team awareness directive 2026-10-21):
I answered it (YM-only scan), concluded "operators symmetric, no analog,"
and recorded that at `~/.claude/projects/-home-xluxx/memory/pf_substrate_asymmetry_study_2026-10-21.md`.

Pablo then committed a fuller answer at **`48ef3fca`** that read
`PF/TransferOperator.lean` and found `T3` vs `T3_adjoint` IS the
asymmetry analog, and `T3_sym_action := (T3 + T3*) / 2` deletes it at
the point of definition — load-bearing for the entire Hilbert–Polya /
spectral route (`T3_self_adjoint_conj`, `IsSelfAdjoint` consumers).

My YM-only record was partial and is now superseded. I've marked it as
SUPERSEDED in the memory file (pointer to `48ef3fca`) and in the
MEMORY.md index. The authoritative answer is `48ef3fca` — do not cite
my earlier record.

## Out-of-repo items I touched (program-relevant to name)

- `/tmp/pf_lean_build.lock` — shared with Legion (named in §1 of the master doc; well-known).
- `/tmp/sectorglue_watch.log` — session-only watcher log for build completion; no retention needed, auto-expires with session.
- `/tmp/claude-1000/-home-xluxx/<session-id>/tasks/*.output` — my Bash background-task outputs; session-only, no retention.

Nothing to ship into the repo. No cross-session dependencies live outside.

## Updated

2026-10-21, before starting Steps 5-6.
