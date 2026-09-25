# r331c/d CAMPAIGN — HARNESS DESIGN AND FLT-METHOD ADOPTION

**Date:** 2026-09-08. Input: `codex/FLT_LESSONS_FOR_PF_2026-09-08.md`.
Directive §9 requires every auxiliary campaign to carry a **ceiling, a stopping
condition, and a named reusable deliverable**. Those are §5 below.

---

## 1. THE DECISIVE DATA POINT

The FLT run's first attempt **failed** — agents lost project state and stopped
collaborating; failed runs contributed ~7% of final lines. The fix was the
harness, **not a better model**. And the method transfers down: Vinogradov's
Three Primes Theorem in **3 days on 3 personal Max plans**; a 151K-line mission
on **2 consumer subscriptions (~$400)**.

That is our exact configuration. The datacenter bought *scale*, not *method*.

## 2. VERDICT ON THE CARD-DAG PATTERN FOR OUR SCALE

**Adopt, with one significant simplification.**

| property | FLT/Prove2Me | r331c/d | fit |
|---|---|---|---|
| statements | 29,511 cards | est. **40–120** | **massive over-capacity** |
| coordination | DB + web platform + search API | 2 machines, 1 human | **too heavy as-built** |
| the actual need | cross-session state, no monolithic rebuild | identical | **exact match** |

**What we adopt:**

- **Card schema (§1).** One file per statement (`:= by sorry`), one per proof,
  type-match enforced by script. Our per-module serialization already gestures at
  this; go per-lemma.
- **Sketch imports (§2).** A proof may import *unproved* cards. This matters
  **more** at our scale, not less: it lets the whole r331c skeleton be committed
  top-down today without paying compile cost for unfinished leaves. Status
  propagates up on completion.
- **Per-card isolated compilation (§3).** Compile each proof against
  statement-only interfaces. Chained full build **once per milestone**, not
  continuously. This is the trick a two-laptop budget needs most — and note our
  C1 rebuild is currently ~5 days of wall-clock precisely because it is monolithic.
- **DAG as shared memory (§4).** The single highest-value item for this project
  specifically: state lives in the DAG, not in a session's context. Every session
  starts by reading it and ends by updating it. This directly addresses the
  session-reset problem that has cost us real time.

**What we do NOT adopt:**

- The web platform, the search API, the DB triggers. At 40–120 statements a
  **JSON file plus a ~50-line propagation script** is the whole system. Building
  Prove2Me's infrastructure for our card count would cost more than the campaign.
- Duplication tolerance (40% duplicate statements, per-file heartbeat overrides).
  Affordable only with their compute; on two laptops it sinks build times.
- Agent-swarm parallelism at "dozens" scale. **Role-split, not count-split**:
  machine A runs prover sessions on open leaves; machine B runs the
  reviewer/disprover plus the serialized builds.

**Estimated build cost: 1–2 days.** Highest-confidence transfer in the document,
because it is the one thing their evidence isolates as decisive.

## 3. THE ORDERING CHANGE THAT MATTERS MOST

Their §5: statements are reviewed **before** anyone attempts a proof, and
*reviewers who computed beat reviewers who argued*. Concrete catches: a false K1
found on Day 9 with the corrected subtree proved 2h40m later; a "model
domination" lemma killed by a **computed counterexample** on Day 11 before any
proof was written against it.

**We have just reproduced this result.** Today's read-back audit
(`codex/READBACK_AUDIT_2026-09-08.md`) found a vacuity hole in
`re_xi_lower_bound_from_edge` — no `t_lo ≤ t_hi`, so the theorem was provable
with `m = 10^100` while asserting nothing — **before any proof work, before
elaboration, with zero consumers.** Cost to fix: one hypothesis. Cost had it been
found after a campaign of green certificates covering zero t-measure:
the campaign.

**Binding rule for r331c/d:** no card enters the prove queue until (a) an
independent read-back matches intent (gate §H) and (b) a **numerical** stress
test has failed to break it. We already own the numerics machinery — the box
certificate generators — and it repurposes directly: evaluate the integrand at
sampled heights, check the enclosure at random points in the box.

## 4. TOP-5 ADOPTION ASSESSMENT

| # | item | verdict | why |
|---|---|---|---|
| 1 | **Card schema + sketch-DAG + propagation** | **ADOPT** | The decisive difference between their failed and successful runs. Fixes cross-session state loss and monolithic rebuilds, both of which have cost us directly. 1–2 days |
| 2 | **Disprove-before-prove with computed checks** | **ADOPT — highest priority** | Already validated on our own corpus today. False statements are the most expensive token sink on a small budget. ~½ day; numerics harness already exists |
| 3 | **Read-back audit of the core** | **ADOPTED — done today** | Gate §H added and mandatory; first run complete on five statements; one defect fixed, one framing corrected |
| 4 | **comparator + nanoda + Buzzard-grep endgame** | **ADOPT, deferred to r331c/d endgame** | Free, external, third-party-replayable. The comparator step specifically closes the "restricted intermediate definitions weaken the final statement" hole — which is *precisely* the r331c risk, since its enclosure structures are project-local. Also adopt their **claiming discipline**: "proved in-pipeline, pending recheck" until all layers pass |
| 5 | **Milestone-driven book pipeline + search-before-submit** | **DEFER** | Correct, but the book queue is not the controlling objective (directive §1). Adopt the NL-description header now — it is free and makes the library searchable later |

**Also adopting from §9, at zero cost** (prompting patterns, no compute):
numerically verify before formalizing; prefer assembly of already-proved modules
over new theory; if stuck 30 minutes, propose an equivalent restatement on served
ground rather than grinding; for any "hard" dependency, probe whether our
*specific* object gives a shortcut the general theorem does not.

**Explicitly rejected:** brute-forcing hard walls by parallel attempt-spam. We
cannot afford it, and §9's route-switching plus the disprove-first gate is the
substitute their own data supports.

## 5. DIRECTIVE §9 COMPLIANCE — ceiling, stopping condition, deliverable

| field | value |
|---|---|
| **Ceiling** | 3 weeks wall-clock, or the harness build exceeding 3 days, whichever first |
| **Stopping condition** | Auto-pause and escalate to Pablo if: the ceiling is hit; **or** a milestone statement fails read-back twice; **or** the t-ranged reparameterisation of the quadrature machinery is shown infeasible (that is the known architectural blocker — r331a's structures are σ-ranged at fixed t, and r331c needs the transpose) |
| **Named reusable deliverable** | The card-DAG harness itself (schema + propagation + type-match script), reusable by r331d and the book queue; **plus** the t-ranged enclosure machinery, which is the piece r331a lacks |
| **Claim ladder** (§9) | box → boundary → count → evaluated count → finite-height RH. **No rung may be promoted as evidence for global RH or for unification absent a formal dependency** |

## 6. SEQUENCING

1. Harness build (1–2 days) — schema, propagation, type-match script.
2. Statement freeze: write the full r331c skeleton as sketches, top-down.
3. **Gate §H read-back on every milestone statement** + numerical stress. No
   proof work before this passes.
4. Farm the interior. Role-split across the two machines.
5. Milestone chained builds; endgame per §4 item 4.

**Step 3 precedes step 4. That ordering is the whole lesson.**

---

*Plan only — no campaign started, no build slot taken. Both machines remain on
C1. Public HEAD `96c71da7`. NO PUSH.*
