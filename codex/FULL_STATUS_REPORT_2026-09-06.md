# FULL STATUS REPORT — r331b

Regenerated from the filesystem on **2026-09-07** on branch `r331b-provenance`
(HEAD `c84fe366`). Supersedes any earlier copy. Every claim below is either a
command result recorded in this session or a citation to a committed file; nothing
is carried forward on memory.

Public HEAD remains `96c71da7`. **NO PUSH.**

---

## 1. PROJECT STATE

### 1.1 The endpoint — verbatim

`PF/Analytic/RiemannXiT15Endgame.lean:87`, copied exactly:

```lean
theorem xi_T15_zero_count_identity_unconditional :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) z15 w15
      = ∑ ρ ∈ (finite_zeros_rectangle
              (riemannXiEntire_analyticOnNhd _)
              (rectangleBorder_subset_rectangle z15 w15 z15_mem_RectangleBorder)
              (boundary_zero_free_of_top_right_half H_TOP z15
                  z15_mem_RectangleBorder)).toFinset,
          (analyticOrderNatAt riemannXiEntire ρ : ℂ) :=
  xi_T15_exact_zero_count_identity_top_only H_TOP
```

Recorded axiom audit (`codex/DISPATCH_RESULTS_2026-08-30.md`, 2026-09-05):

    PrincipiaTractalis.RiemannXiT15Endgame.H_TOP
      depends on axioms: [propext, Classical.choice, Quot.sound]
    PrincipiaTractalis.RiemannXiT15Endgame.boundary_zero_free_T15
      depends on axioms: [propext, Classical.choice, Quot.sound]
    PrincipiaTractalis.RiemannXiT15Endgame.xi_T15_zero_count_identity_unconditional
      depends on axioms: [propext, Classical.choice, Quot.sound]

`sorryAx` / `ofReduceBool` occurrences in that module's audit output: **0**.
`#check @xi_T15_zero_count_identity_unconditional` returned a type with **no
binders at all** — the unconditionality is Lean's verdict, not a reading of the
source. Build: RC=0, 95.48 s, peak 8.95 GB.

**What it is:** the exact zero-count identity for the classical entire Riemann ξ
on the single rectangle `z15 = 0` to `w15 = 1 + 15i`, i.e. `[0,1] × [0,15]`. The
rectangle contour integral of `logDeriv riemannXiEntire` equals the sum of
`analyticOrderNatAt` over the finitely many interior zeros.

**What it is not:** the Riemann Hypothesis. One rectangle, one identity. Any
release text implying more is the failure mode this project has already been
audited for (gate item F8).

### 1.2 Kernel three

Every clean audit in this chain shows exactly `[propext, Classical.choice,
Quot.sound]` — mathlib's three, no project axioms. "Axiom-free" is the wrong
phrase and must not appear in release text (gate item F1).

### 1.3 The 18-box partition and its margins

Cover gate re-run from the filesystem on 2026-09-07:
`python3 scripts/emit_top_union.py --root . --check-only` →
**PASS — contiguous, no gap, no overlap, measure exactly 1/2; capstones 18/18
closed.**

Headline figure is the **ξ-space margin** against the `-1/10000` top-edge target
(convention set 2026-08-31). Values below are read from each committed
`RiemannXiBox<K>Bridge.lean`, not from logs.

| box | σ interval | p1 | headline ξ margin | audit |
|---|---|---|---|---|
| Box0 | [1/2, 9/16] | 25/32 | *not recorded in headline convention* (see note) | 31 endpoints, hand-written |
| Box100 | [9/16, 5/8] | 13/16 | **+1.694871e-04** | 19/19 clean |
| Box2 | [5/8, 11/16] | 27/32 | **+2.839068e-05** | 19/19 clean |
| Box102 | [11/16, 23/32] | 55/64 | **+1.465594e-04** | 19/19 clean |
| Box103 | [23/32, 3/4] | 7/8 | **+1.143581e-04** | 19 |
| Box104 | [3/4, 25/32] | 57/64 | **+8.275513e-05** | 19 |
| Box105 | [25/32, 13/16] | 29/32 | **+5.215431e-05** | 19 clean |
| Box106 | [13/16, 27/32] | 59/64 | **+2.211191e-05** ← weakest | 19 clean |
| Box107 | [27/32, 55/64] | 119/128 | **+2.004865e-04** | 19 clean |
| Box108 | [55/64, 7/8] | 15/16 | **+1.950668e-04** | 19 clean |
| Box109 | [7/8, 57/64] | 121/128 | **+1.898919e-04** | 19 clean |
| Box110 | [57/64, 29/32] | 61/64 | **+1.849170e-04** | 19 clean |
| Box111 | [29/32, 59/64] | 123/128 | **+1.801967e-04** | 19 clean |
| Box112 | [59/64, 15/16] | 31/32 | **+1.755556e-04** | 19 |
| Box113 | [15/16, 61/64] | 125/128 | **+1.710598e-04** | 19 |
| Box114 | [61/64, 31/32] | 63/64 | **+1.668577e-04** | 19 |
| Box115 | [31/32, 63/64] | 127/128 | **+1.627947e-04** | 19 |
| Box116 | [63/64, 1] | 1 | **+1.588177e-04** | 19 clean |

**Weakest box is Box106** (strip 6, `[13/16, 27/32]`) at `+2.211191e-05`, with
Box2 next at `+2.839068e-05`. Those two are the margin floor for the whole union;
any future tightening effort belongs there.

Note on Box0: its bridge is hand-written and predates the 2026-08-31 headline
convention, so no `xi margin ~` line exists in its source. Its recorded figures
are Λ-space: `RE_MARGIN_pos = +1.087524e-06`, `IM_LO_MARGIN_pos = +6.264311e-05`,
`IM_HI_MARGIN_pos = +2.589050e-05`. Its capstone `top15_box0_re_lt_neg_1e4` is
unconditional over `σ ∈ [1/2, 9/16]`.
**Open item:** compute and record Box0's ξ-space margin so the table is uniform.

Box index → manifest strip: `Box(100+k) = strip k`, **except strip 1, built under
the name `Box2`**. There is no Box101. Box106 is strip 6 by decode
(`p1 = 59/64 → σ_hi = 27/32`), which is the weakest strip — do not infer the strip
from the directory name.

The Λ-space margins reported per box (~1e-13) are the **internal enclosure check**,
not the headline. They reflect the 1e-12 outward rounding of the declared box
bounds, not tightness (gate item F9).

### 1.4 Union

`PF/Analytic/RiemannXiTopUnion.lean` contains `theorem top15_re_lt_neg_1e4`
(FULL — not the `_partial` form) and `H_TOP_discharged`, and references all 18
`Box<K>Bridge` modules.

---

## 2. EVIDENCE STANDARD

This is the section that has repeatedly saved the project from recording a false
result. It is mandatory, not advisory.

**A zero exit code does not mean a theorem was proved.** On 2026-09-05 the first
build of `RiemannXiT15Endgame` returned RC=1 while its audit line read

    xi_T15_zero_count_identity_unconditional depends on axioms:
      [propext, sorryAx, Classical.choice, Quot.sound]

`finite_zeros_rectangle`, `RectangleIntegral'` and
`rectangleBorder_subset_rectangle` live in namespace `Zeta23.Analytic`
(`RectangleArgumentPrinciple_r327.lean:51-52`). r328 (line 73) and r329b (line 83)
open it; the staged endgame module did not. The name elaborated to a metavariable
and **Lean admitted the goal with a sorry**. Without the in-module `#print axioms`
check this would have surfaced only as "build failed", with no sign that a
load-bearing theorem had been silently admitted.

Therefore, for every load-bearing theorem:

1. Its module MUST carry `#print axioms <fully.qualified.name>`, or an `...Audit`
   companion MUST.
2. The verdict MUST be read from that output, filtered to lines attributed to that
   module's own file path — the build log also carries `#print axioms` output from
   every other file it touched, and Lean wraps long axiom lists across lines.
3. Judge by the **absence of `sorryAx` and `ofReduceBool`** in the unwrapped
   output, never by pattern-matching the expected happy list. Wrapping breaks
   naive matches.
4. **RC=0 alone is NEVER sufficient evidence and MUST NOT be recorded as an audit
   result.**
5. For a theorem claimed unconditional, additionally run `#check @<name>`. The `@`
   form shows every binder including implicits; a genuinely unconditional theorem
   shows **no binders at all**. Reading the source for absent hypotheses is not
   equivalent — elaboration can introduce them.

### 2.1 Two grep-shaped failures on record

Both were false readings produced by a grep matching its own surrounding prose.
They are recorded because the pattern will recur.

- **The restart count.** A status report claimed one post-fix supervisor restart
  on the Acer. There were **zero**. The count came from `grep`ping for `restart`,
  which matched the string inside `max_restarts=6` in the supervisor's own start
  banner. Corrected in `e2181eda`.
- **Gate items A7/A8.** The gate specifies a bare `grep -rn "sorry"` /
  `native_decide` over the chain. Run literally on 2026-09-07 it returns 18 hits —
  every one of them line 10 of a `Box<K>BridgeAudit.lean` module docstring reading
  *"No project axioms. No sorry. No native_decide."* The check matches its own
  documentation. Re-run excluding block comments: **A7 clean, A8 clean.**
  The gate's stated command is defective and is listed as an open item.

---

## 3. RELEASE GATE — ITEM BY ITEM

Status column is what the **filesystem shows on 2026-09-07**. It is evidence, not
sign-off; the checkboxes in `codex/RELEASE_GATE_r331b.md` are Pablo's to tick.
Several are demonstrably satisfied and still show ☐ there — the gate file is stale
with respect to the evidence.

### A. MATH

| # | item | evidence 2026-09-07 |
|---|---|---|
| A1 | 18 boxes' panels kernel-green | **PASS** — `emit_top_union.py --check-only`: 18/18 |
| A2 | all 18 have bridge + capstone | **PASS** — all 18 rows `CLOSED` |
| A3 | cover gate | **PASS** — contiguous, no gap/overlap, measure exactly 1/2 |
| A4 | `RiemannXiTopUnion` FULL | **PASS** — contains `theorem top15_re_lt_neg_1e4` and `H_TOP_discharged`; no `_partial` |
| A5 | `RiemannXiT15Endgame` elaborates | **PASS** — RC=0, 95.48 s, 2026-09-05 |
| A6 | count identity has NO hypotheses | **PASS** — `#check @…` shows no binders at all |
| A7 | no `sorry` in the chain | **PASS on a correct grep**; the gate's literal command yields 18 false positives (§2.1) |
| A8 | no `native_decide` | **PASS** — clean on both the literal and the corrected grep |

A6 is the item that matters most and it holds.

### B. AXIOM AUDIT

| # | target | status |
|---|---|---|
| B1 | `RiemannXiBox0BridgeAudit` (31/31) | ☐ **not re-run**; and see §6.4 — box 0's bridge was skipped by the current C1 pass |
| B2 | `RiemannXiBox2BridgeAudit` (19/19) | ☑ 2026-08-31, clean |
| B3 | `RiemannXiBox100BridgeAudit` | recorded 19/19 clean in the dispatch ledger; not re-run this session |
| B4 | `Box102..116BridgeAudit` (15 files) | recorded 19 each; 105, 106, 107, 108, 109, 110, 111, 116 explicitly "clean"; 102, 103, 104, 112, 113, 114, 115 recorded as `audit 19` without the clean tag — **verify before sign-off** |
| B5 | `RiemannXiTopUnionAudit` | recorded clean at the 4-box partial (2026-09-02); **not re-audited at FULL** |
| B6 | `RiemannXiT15Endgame` `#print axioms` (3 checks) | ☑ 2026-09-05, all three the mathlib three |
| B7 | `RiemannXiBoundaryT15_r328` | ☐ |
| B8 | `RiemannXiBottomEdgeUnconditional_r329b` | ☐ |
| B9 | `RiemannXiRectangleCount_r327` | ☐ |
| B10 | `RiemannXiThetaBoxEnclosure_r331a` | ☐ |

**B5 is the sharpest open math item.** The union audit was clean over a four-box
prefix. The full 18-box case split has not been axiom-audited. That is exactly the
scaffold whose branching the partial run did not exercise.

### C. FULL BUILD GREEN

| # | item | status |
|---|---|---|
| C1 | clean full build from scratch | **IN PROGRESS**, A1-scoped (see §4). Acer 1/9 boxes; Legion 0/9 boxes but near box 108 completion |
| C2 | zero `error:` in build log | pending C1 |
| C3 | reproducible on a second machine | partially evidenced: 106–111 built on Legion and re-audited on the Acer production tree |
| C4 | `lean-toolchain` + `lake-manifest.json` pinned and committed | ☐ verify `git status --porcelain` at sign-off |

### D. PROVENANCE — **now materially better than the gate file records**

| # | item | status 2026-09-07 |
|---|---|---|
| D1 | `emit_box_segment.py` | **TRACKED** |
| D2 | `emit_stage2_segment.py` | **TRACKED** |
| D3 | `emit_box_bridge.py` | **TRACKED** |
| D4 | `emit_top_union.py` | **TRACKED** |
| D5 | `opt40tight.py` | **TRACKED** |
| D6 | `strip_queue.sh` | **TRACKED** |
| D7 | Gate-B manifest committed | **RESOLVED** — `PF_Lean4_Code/scripts/manifests/strip_manifest_v2.json` |
| D8 | `manifest_v2.py` committed | **TRACKED** |
| D9 | 18 boxes' panel sources committed | **RESOLVED** — 4115 files tracked |
| D10 | 18 boxes' M certificates committed | **RESOLVED** — 720 files tracked |
| D11 | 18 bridges + audits committed | **RESOLVED** — 36 files tracked |
| D12 | regeneration byte-reproducible | ☐ **not attempted** — the one D item still fully open |

The gate file's warning that "D7/D8 are live risks right now" and that panel
sources are "currently UNTRACKED" is **out of date**. Correct that text.
D12 is the remaining provenance obligation and it is not small: it means re-running
every generator and getting an empty `git diff`.

### E. MHI OVERRIDE TABLE

`codex/MHI_OVERRIDE_TABLE.md` and `MHI_OVERRIDE_TABLE_FULL.md` exist (2026-09-05).
E1–E4 need a read-through against the gate's four questions; not done this session.

### F. DOCUMENTATION HONESTY

All nine open. F8 (scope: this is the T=15 rectangle count identity, **not** RH)
and F1 (no "axiom-free" phrasing) are the two that decide whether the release text
is honest. F6 (`DISPATCH_OWNERSHIP.md` build-lock notice) is a one-line fix.

### G. RELEASE MECHANICS

All open. G5 — explicit go-ahead to push — does not exist and nothing in this
report authorises one.

---

## 4. SCOPE DISCIPLINE

### 4.1 What C1 covers, and on what grounds

C1 rebuilds **the r331b chain only**: 4835 generated files (4115 panel modules +
720 M certificates), the box-parametric core, the §8 envelope,
`RiemannXiThetaRealFormAndBoxes_r331b`, all 18 bridges and their audits,
`RiemannXiTopUnion` + audit, `RiemannXiT15Endgame`, and every other file this
branch adds or modifies relative to `96c71da7`. The set is defined mechanically:

    git diff --name-only 96c71da7..HEAD

The pre-r331b corpus is excluded because it is **tracked and unmodified at public
HEAD `96c71da7`** — already the published built state — and the threat model for
this gate is our own generation pipeline: the emitters, the manifest, the bridge
and union assembly. Code we did not write and did not change is a dependency, in
the same category as mathlib.

### 4.2 The RAM-wall claim is withdrawn

Commit `1e17f246` asserted a pre-r331b module exceeds available RAM, citing three
OOM kills at 13 GB cap, 14.5 GB cap, and no cap. **That inference was wrong and is
withdrawn** (`e2181eda`).

All three runs used a driver issuing **one `lake build` per box**, so a single lake
process elaborated ~280 modules in sequence and accumulated memory until the kernel
killed it — reliably near the five-minute mark regardless of the cgroup setting,
which is precisely why removing the cap changed nothing. The campaign's discipline
is **one lake invocation per module**, each process exiting and releasing memory.
That discipline was not carried into the rebuild driver. With it restored the same
tree builds at normal figures (~210 s, ~10.4 GB for a heavy panel).

What is actually known: **no pre-r331b module has been shown to exceed available
RAM**, and the full-tree rebuild has not been attempted with correct per-target
serialization, so the question is open rather than settled. The one independent
data point — the first smoke build — ran at `nproc=4` and fanned out in parallel,
which alone explains an OOM and proves nothing about any single module.

**C1's scope restriction therefore does not rest on a hardware limit.** It rests
only on the scope argument in §4.1, which is independent of memory and is the one
to cite.

### 4.3 Release-text consequence

Do not claim "builds clean from scratch" unqualified. The accurate claim is:
**every artifact this release contributes rebuilds from committed source on stock
hardware, against a pinned, unmodified dependency base.**

---

## 5. ROADMAP

**Immediate (blocks the gate):**

1. Finish the A1-scoped C1 rebuild on both halves.
2. Fix the box-0 bridge skip (§6.4) and rebuild box 0's bridge + audit — B1 and C1
   coverage both depend on it.
3. Audit `RiemannXiTopUnionAudit` at FULL, 18 boxes (B5).
4. Re-audit the seven boxes recorded as `audit 19` without a clean tag (B4).
5. D12: re-run every generator, require an empty `git diff`.

**Then:**

6. B7–B10: axiom audits on r327, r328, r329b, r331a.
7. E1–E4: MHI override table walked against the gate's four questions.
8. F1–F9: documentation honesty pass, F8 and F1 first.
9. G1–G4, then Pablo referees the endgame chain live.

**Not on this path:** `r331c` (stage C0 staged at `c84fe366`,
`codex/R331C_STAGING_PLAN.md`) is a t-ranged enclosure skeleton. It is the next
mathematical arc, not a release blocker, and must not be allowed to consume the
gate walk.

---

## 6. INFRASTRUCTURE INCIDENT LOG

### 6.1 OOM restart loop — 2026-09-06 08:18 to 08:54 (RESOLVED)

`pf-c1` was OOM-killed **six times** in 36 minutes under `c1_rebuild.sh`
(peak 13.3 G memory + 2.8 G swap on a 15 G machine). Cause is §4.2: one `lake
build` per box. Resolved by replacing the driver with `a1_v2.sh` (per-module
invocation) at 19:07:58. **Zero OOM kills since** — verified by
`journalctl --user -u pf-c1 --since "2026-09-06 19:00"`.

### 6.2 Idle incidents (the reason supervisors are policy)

Three separate incidents: a worker that finished and was never chained (~9 h), and
a C1 unit OOM-killed while its sibling half had never been launched at all (~15 h).
The machines sat idle and nothing reported it. Standing policy: **no build unit
runs unsupervised**; every long-running unit is paired with a supervisor that
detects death and *resumes*, with a capped retry count and a refusal to restart on
a genuine build failure as opposed to a kill. A watcher that only reports is
insufficient.

### 6.3 The phantom restart (RESOLVED)

See §2.1. Zero real restarts on either machine since the per-target driver landed.
The Legion's supervisor log was trimmed to the current generation so the sentinel
reads truth; the original is kept as `.pre-a1v2.bak`.

### 6.4 Box 0 bridge skipped — 2026-09-07 04:42 — **OPEN**

Ledger line, verbatim:

    | box 0 | BRIDGE GEN FAILED (panels green) | | xluxx-Nitro-AN515-58 | 2026-09-07T04:42:28-04:00 |

This reads as a failure. It is not one. `/tmp/r331b_logs/bridge_gen_0.log`
contains exactly one line:

    REFUSED: box 0 has a hand-written, kernel-green bridge. It is the reference
    for this generator, not a target.

That refusal is correct and by design (`emit_box_bridge.py` refuses box 0 so it
cannot overwrite the reference). **But `a1_v2.sh` treats a by-design refusal
identically to a generator crash**: it logs `BRIDGE GEN FAILED` and `continue`s to
the next box — skipping the bridge *build* as well as the generation.

Two consequences, both real:

1. **A C1 coverage gap.** Box 0's panels rebuilt (40/40 green, 574 min) but
   `RiemannXiBox0Bridge` and `RiemannXiBox0BridgeAudit` did **not**. Both are
   tracked source; neither has a rebuilt `.olean` in the rebuild tree. C1 is not
   complete for box 0 as it stands.
2. **A false ledger line**, of exactly the kind §2.1 catalogues.

Fix: on `REFUSED`, skip generation but still build the existing bridge and audit,
and record `bridge pre-existing (reference), rebuilt` rather than `FAILED`.
Nothing green needs redoing — the panels stand.

### 6.5 Throughput

Box 0 took **574 min** for 40/40 segments. At that rate nine boxes per machine is
roughly 3.5 days per half. Both halves run 9 boxes, not 108: Acer
`{0, 100, 2, 102, 103, 104, 105, 106, 107}`, Legion `{108…116}` — 18 total.

### 6.6 Current run state — 2026-09-07 07:34 EDT

| | Acer (`xluxx-Nitro-AN515-58`) | Legion (WSL Ubuntu) |
|---|---|---|
| driver | `a1_v2.sh` | `a1_v2.sh` |
| supervisor | `pf-c1-sup` (systemd **user** unit) | `c1_supervisor.sh --system` as a plain process — **no systemd**; WSL has no user bus (`Failed to connect to bus`) |
| boxes | `0 100 2 102 103 104 105 106 107` | `108 … 116` |
| progress | box 0 done; **box 100 in progress**, `Seg07P5` | **box 108 in progress**, `Seg38P1` (38/40) |
| elapsed on current target | 2 m 44 s, 108% CPU, 9.76 GB RSS | 1 m 50 s, 108% CPU, 8.02 GB RSS |
| driver uptime | 12 h 27 m | 12 h 05 m |
| ledger | 2 lines | **0 bytes** — no box completed yet |
| verdict | **ADVANCING** | **ADVANCING** |

The Legion's supervision is weaker than the Acer's: it is a script, not a systemd
unit, so it does not survive a WSL VM restart. Worth noting, not urgent while it
is alive.

---

## 7. OPEN ITEMS BY OWNER

### Orchestrator (automatable, no judgement call)

| # | item | ref |
|---|---|---|
| O1 | Patch `a1_v2.sh`: on `REFUSED`, build the pre-existing bridge + audit instead of skipping | §6.4 |
| O2 | Rebuild `RiemannXiBox0Bridge` + `…BridgeAudit` in the rebuild tree; closes B1 and the C1 gap | §6.4 |
| O3 | Correct the false `BRIDGE GEN FAILED` ledger line for box 0 | §6.4 |
| O4 | Fix the gate's A7/A8 grep so it excludes block comments | §2.1 |
| O5 | Update gate section D: D1–D11 are resolved; delete the "live risks"/"UNTRACKED" text | §3 D |
| O6 | Compute and record Box0's ξ-space margin | §1.3 |
| O7 | Re-audit `RiemannXiTopUnionAudit` at FULL 18 boxes | B5 |
| O8 | Re-audit the seven boxes tagged `audit 19` without `clean` | B4 |
| O9 | Promote the Legion supervisor to a durable unit or document the gap | §6.6 |

### Pablo (judgement, sign-off, or referee)

| # | item | ref |
|---|---|---|
| P1 | Referee the endgame chain live | G4 |
| P2 | Decide D12 scope: full byte-reproducibility re-run of every generator | D12 |
| P3 | Walk E1–E4 against the MHI override table | E |
| P4 | Approve the F-section release text, F8 and F1 first | F |
| P5 | G5 — the push decision. Nothing else authorises it | G |
| P6 | Decide whether r331c stage C0 proceeds in parallel with the gate walk or waits | §5 |

### Blocked / not started

| # | item | blocker |
|---|---|---|
| X1 | D12 byte-reproducibility | needs C1 complete first |
| X2 | B7–B10 (r327/r328/r329b/r331a audits) | none — simply not started |
| X3 | C2 error-count check | needs C1 complete |

---

*Regenerated 2026-09-07 from branch `r331b-provenance` @ `c84fe366`.
Public HEAD `96c71da7`. NO PUSH.*
