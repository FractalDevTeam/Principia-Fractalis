# ACER — session status

**Owner:** Acer session (Linux server 192.168.0.94, Opus 4.7, 1M ctx).
**Lane:** YM Fubini discharge → unconditional `wilson_reflection_positivity`.
**Pinned by:** `codex/INSTRUCTIONS_FOR_EVERY_AI_2026-10-21.md` §2 ACER.

## Current task (in flight)

**Full Step 6 — EMPTY hypothesis list acceptance.** Specialisation
landed at `52a1cd3e` but still takes `hΦ_integrable` + `hFubini` as
parameters. Rio's acceptance is empty hypothesis list + exact
`[propext, Classical.choice, Quot.sound]` axiom output pasted here
verbatim. Pushing through:

* Refined-sector scaffold landed (`52a1cd3e`): `WilsonSectorPlaquetteZero_2026_10_21.lean`.
* NEXT: prove `plaquetteSectorRefined (θ_p p) = (plaquetteSectorRefined p).reflect` + the pointwise `wilsonActionMinusR (θU) = wilsonActionPlusR U` on top of this scaffold.
* THEN: Λ_- restriction of `timeReflectionGaugeField_measurePreserving`; Fubini identity assembly; integrability via bounded-F ⇒ bounded-Φ; empty-hypothesis headline.

## Last landed commit (origin/master)

`cc1fe60c` — explicit `Φ` for Wilson RP Fubini discharge (step 5).
Prior landings this session: `7bb5572e` (Λ_+ glue), `4e5bbb10`
(glue action symmetry), `c5080d4b` (Λ_- glue + supportedOnPlusZero factor-eq).

## Six-step mapping — current state

| # | Scope | Status | Commit |
|---|---|---|---|
| 1 | Λ_- Pi inv-invariance + θ̂ measure-preserving | LANDED | `42d6ad7a` `5ad9b21a` `2d1a840e` `5fd31285` `9a8f1ddd` |
| 2 | Λ_- glue + restriction + measurability | LANDED | `c5080d4b` |
| 3 | Action/Boltzmann symmetry on glue (X-independence) | LANDED | `4e5bbb10` |
| 4 | `supportedOnPlusZero_glue` + `_factor_eq` | LANDED | `c5080d4b` |
| 5a | Λ_+ side glue (parallel to Λ_-) | LANDED | `7bb5572e` |
| 5b | `wilsonReducedPhi` definition + `restrictNonPlus` + invariance | LANDED | `cc1fe60c` |
| 6a | `wilson_reflection_positivity_withReducedPhi` specialisation | BUILD-PENDING (ComplexOrder fix in flight) | — |
| 6b | `hΦ_integrable` discharge | IN FLIGHT | — |
| 6c | `hFubini` discharge (sector action reflection + Λ_- change of variable) | IN FLIGHT | — |

Acceptance target (§2.3): `wilson_reflection_positivity` with empty
hypothesis list, kernel-clean, three-axiom bar.

## Remaining Fubini identity proof — structural payload

~600 LOC across 4 new files, detailed in the progress memory. Short
list:

1. `WilsonSectorMinusMeasurePreserving_2026_10_21.lean` — restrict the
   full-field `timeReflectionGaugeField_measurePreserving` to the Λ_-
   subtype using `measurePreserving_piCongrLeft` for the sector-swap
   bijection + per-link `condInv_minus`. ~100 LOC.
2. `WilsonSectorActionReflection_2026_10_21.lean` — sector action
   reflection identity on INTEGRALS (not pointwise; boundary plaquettes
   require sum-level handling via `wilsonActionDensity_timeReflection`
   + `timeReflectionPlaquette_bijective`). ~250 LOC.
3. `WilsonReducedPhiIntegrable_2026_10_21.lean` — bounded F ⇒ bounded Φ
   ⇒ integrable `|Φ|²` on wilsonBaseMeasure (probability measure, finite).
   ~100 LOC.
4. `WilsonRPFubiniApplyUnconditional_2026_10_21.lean` — the final Fubini
   identity assembly. Combines pieces 1-3 + landed Boltzmann factorisation.
   ~150 LOC.

Each file three-axiom bar individually.

## Crossings / files other sessions may read-touch

- `PF/YangMills/*` is my lane. No concurrent writer expected.
- `PF/TransferOperator.lean` was named in the §0B asymmetry study (`48ef3fca`) — not touched by me.
- `/tmp/pf_lean_build.lock` is SHARED with Legion's march runner (`codex/march_box.sh`). Legion's `5c48f698` note confirms shared-flock contract.

## Current flock contention

Legion's march_box.sh on c=10, box 25 (D=1 band edge per §0, LEGION task 1 — producer pipeline repair / D=2 standup should be prioritised to unblock Legion). My Step 6 rebuild (PID 1708656) waiting ~26+ min — unusually long box.

## Out-of-repo items I touched (program-relevant to name)

- `/tmp/pf_lean_build.lock` — shared with Legion (named in §1).
- `/tmp/sectorglue_watch.log` — session-only, no retention.
- `/tmp/claude-1000/-home-xluxx/<session-id>/tasks/*.output` — session-only.

Nothing to ship into repo.

## Conflicts I detected

My §0B asymmetry answer (YM-only, recorded in local memory) is
SUPERSEDED by **Legion's** commit `48ef3fca` reading
`PF/TransferOperator.lean`. Correction 2026-10-21 evening: commit
`48ef3fca` is Legion's, not Pablo's — board accuracy is the value.
Already flagged; marked SUPERSEDED in my memory file.

## Updated

2026-10-21, after Steps 2-5 landings; before Step 6 full Fubini apply.
