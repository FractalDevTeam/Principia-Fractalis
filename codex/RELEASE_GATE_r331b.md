# r331b RELEASE GATE — checkable, box by box

Status: **STAGED 2026-08-31.** Nothing here is satisfied yet. NO PUSH until every
mandatory item is checked and Pablo signs off. Public HEAD must remain `96c71da7`
until then.

This file exists so that when the math lands, the release decision is mechanical:
every item is a yes/no with a named command or artifact, not a judgement call.

---

## A. MATH — the chain must be complete and unconditional

| # | item | check | status |
|---|---|---|---|
| A1 | All 18 boxes' panels kernel-green | `scripts/emit_top_union.py --root . --check-only` reports 18/18 | ☐ |
| A2 | All 18 boxes have a bridge + capstone | same command, all rows `CLOSED` | ☐ |
| A3 | Cover gate passes | same command: contiguous, no gap/overlap, measure exactly 1/2 | ☐ |
| A4 | `RiemannXiTopUnion` elaborates FULL (not partial) | file contains `theorem top15_re_lt_neg_1e4 ` and `H_TOP_discharged` | ☐ |
| A5 | `RiemannXiT15Endgame` elaborates | `lake build PF.Analytic.RiemannXiT15Endgame` RC=0 | ☐ |
| A6 | Count identity has NO hypotheses | `xi_T15_zero_count_identity_unconditional` takes no arguments | ☐ |
| A7 | No `sorry` anywhere in the r331b chain | `grep -rn "sorry" PF/Analytic/RiemannXiBox*Bridge*.lean PF/Analytic/RiemannXiTopUnion*.lean PF/Analytic/RiemannXiT15Endgame.lean` empty | ☐ |
| A8 | No `native_decide` in the chain | same grep for `native_decide` empty | ☐ |

**A6 is the one that matters most.** If the final theorem still takes an argument,
the box campaign has not discharged anything and the release is not a release.

---

## B. AXIOM AUDIT — complete list, every file

Every audit must show exactly `[propext, Classical.choice, Quot.sound]`.
Lean wraps long axiom lists across lines — grep for the *absence* of `sorryAx` and
`ofReduceBool` in the audit file's own output, do not pattern-match the happy list.

| # | audit target | status |
|---|---|---|
| B1 | `RiemannXiBox0BridgeAudit` (31/31 endpoints) | ☐ |
| B2 | `RiemannXiBox2BridgeAudit` (19/19) | ☑ **2026-08-31, clean** |
| B3 | `RiemannXiBox100BridgeAudit` | ☐ |
| B4 | `RiemannXiBox102..116BridgeAudit` (15 files) | ☐ |
| B5 | `RiemannXiTopUnionAudit` | ☐ |
| B6 | `RiemannXiT15Endgame` `#print axioms` (3 checks) | ☐ |
| B7 | `RiemannXiBoundaryT15_r328` axiom checks | ☐ |
| B8 | `RiemannXiBottomEdgeUnconditional_r329b` axiom checks | ☐ |
| B9 | `RiemannXiRectangleCount_r327` axiom checks | ☐ |
| B10 | `RiemannXiThetaBoxEnclosure_r331a` axiom checks | ☐ |

---

## C. FULL BUILD GREEN

| # | item | check | status |
|---|---|---|---|
| C1 | Clean full build from scratch | `lake build` from a clean `.lake/build` RC=0 | ☐ |
| C2 | Zero `error:` in the build log | `grep -c "^error:"` = 0 | ☐ |
| C3 | Build reproducible on a second machine | Acer and Legion both green on the same commit | ☐ |
| C4 | `lean-toolchain` and `lake-manifest.json` pinned and committed | `git status --porcelain` clean for both | ☐ |

C1 is expensive (days). Plan it deliberately; do not skip it on the grounds that
incremental builds were green.

---

## D. PROVENANCE — everything that produced a certificate must be committed

The r331b certificates are machine-generated. A reader must be able to regenerate
every one of them from committed inputs. Untracked generators are a release blocker.

| # | item | check | status |
|---|---|---|---|
| D1 | `scripts/emit_box_segment.py` committed | box-parametric panel generator | ☐ |
| D2 | `scripts/emit_stage2_segment.py` committed | box-0 panel generator | ☐ |
| D3 | `scripts/emit_box_bridge.py` committed | bridge generator | ☐ |
| D4 | `scripts/emit_top_union.py` committed | union generator | ☐ |
| D5 | `scripts/opt40tight.py` committed | the 40-segment OPT partition | ☐ |
| D6 | `scripts/strip_queue.sh` committed | build+closure driver | ☐ |
| D7 | **Gate-B manifest committed into the repo** | currently only at `/tmp/strip_manifest_v2.json` — **must move into `scripts/` or `codex/` and be committed** | ☐ |
| D8 | `manifest_v2.py` (the manifest generator) committed | currently only at `/tmp/manifest_v2.py` | ☐ |
| D9 | All 18 boxes' panel sources committed | `PF/Analytic/RiemannXiBox*Panels/**` currently UNTRACKED | ☐ |
| D10 | All 18 boxes' M certificates committed | `PF/Numerics/Box*Seg*M.lean` | ☐ |
| D11 | All 18 bridges + audits committed | `PF/Analytic/RiemannXiBox*Bridge*.lean` | ☐ |
| D12 | Regeneration is byte-reproducible | re-run each generator, `git diff` empty | ☐ |

**D7/D8 are live risks right now.** The manifest that defines the entire partition
lives in `/tmp` on the Acer. A reboot loses it. Copy it into the repo before anything
else in this section.

---

## E. MHI OVERRIDE TABLE — must be documented

Each segment carries an `MHI` (the `2·Σ B_n` majorant with its slack factor) chosen by
the generator. Any segment where the value was overridden, tightened, or hand-adjusted
away from the default rule must be listed with its justification.

| # | item | status |
|---|---|---|
| E1 | Table of every segment whose MHI differs from the default `2·Σ B_n × 1.0005` rule | ☐ |
| E2 | For each, the reason and who decided it | ☐ |
| E3 | Confirmation that no override *loosens* a bound without a compensating check | ☐ |
| E4 | The Seg17 Stage-1 reference exception (`L=3/2, U=25/16, n=23`, skipped by default in `emit_stage2_segment.py`) documented | ☐ |

---

## F. DOCUMENTATION HONESTY — the item this project has failed before

Per the standing finding that in-code docs are honest while the README overstates,
this section is mandatory, not cosmetic.

| # | item | status |
|---|---|---|
| F1 | README claims match what is actually proved — no "axiom-free" phrasing that implies more than "no project axioms beyond the mathlib three" | ☐ |
| F2 | Every undischarged named conjecture still in the repo is listed as undischarged | ☐ |
| F3 | r330 is described as a superseded ALTERNATIVE route that still carries an unproven `hTaylor` hypothesis — never as part of the proved chain | ☐ |
| F4 | `KatoRellichInput` (proved false by its own file) is not cited anywhere as support | ☐ |
| F5 | Stale docstrings in touched files updated (esp. r328 §7 "classical-but-unformalized" bottom edge — now discharged by r329b) | ☐ |
| F6 | `DISPATCH_OWNERSHIP.md` build-lock notice removed or marked historical | ☐ |
| F7 | Progress notes accurate: box counts, timings, what closed when | ☐ |
| F8 | The r331b result is scoped correctly: this is the **T = 15 rectangle count identity**, NOT the Riemann Hypothesis | ☐ |
| F9 | Margin reporting follows the ledger convention: xi-space margin is the headline; Lambda-space ~1e-13 values labelled as the internal enclosure check | ☐ |

**F8 is the one to be most careful about.** The chain proves an exact zero-count
identity on one rectangle. Any release text implying more is the failure mode this
project has already been audited for.

---

## G. RELEASE MECHANICS

| # | item | status |
|---|---|---|
| G1 | Working tree clean, everything intended is tracked | ☐ |
| G2 | Commit message states exactly what is proved and what is not | ☐ |
| G3 | CHANGELOG entry | ☐ |
| G4 | Pablo has reviewed the endgame chain live (the referee step) | ☐ |
| G5 | Explicit go-ahead to push | ☐ |

---

## SIGN-OFF

Release requires: all of A, B, C, D, F mandatory; E documented; G1–G5.

Nothing in this file authorises a push. `NO PUSH` stands until G5.

---

## B0 — MANDATORY: every audit reads `#print axioms` output, never RC

**A zero exit code does not mean a theorem was proved.**

On 2026-09-05 the first build of `RiemannXiT15Endgame` returned RC=1 — and its audit
line read:

    'PrincipiaTractalis.RiemannXiT15Endgame.xi_T15_zero_count_identity_unconditional'
      depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

`finite_zeros_rectangle` lives in namespace `Zeta23.Analytic`
(`RectangleArgumentPrinciple_r327.lean:51-52`). r328 (line 73) and r329b (line 83)
both open it; the endgame module did not. The name elaborated to a metavariable and
**Lean admitted the goal with a sorry**. Had the module carried no `#print axioms`
check, this would have surfaced only as "build failed" — with no indication that a
load-bearing theorem had been silently admitted rather than proved.

Therefore, for **every load-bearing theorem** in the release:

1. Its module MUST contain a `#print axioms <fully.qualified.name>` line, or an
   `...Audit.lean` companion module MUST.
2. The audit verdict MUST be read from that output, filtered to lines attributed to
   **that module's own file path** — the build log also carries `#print axioms` output
   from every other project file it touched, and Lean wraps long axiom lists across
   lines.
3. Judge cleanliness by the **absence of `sorryAx` and `ofReduceBool`** in the
   unwrapped output, not by pattern-matching the expected happy list (wrapping breaks
   naive matches).
4. RC=0 alone is NEVER sufficient evidence and MUST NOT be recorded as an audit result.

For a theorem claimed to be unconditional, additionally run

    #check @<fully.qualified.name>

The `@` form shows every binder, implicits included. A genuinely unconditional theorem
shows **no binders at all**. Reading the source for absent hypotheses is not
equivalent — elaboration can introduce them.
