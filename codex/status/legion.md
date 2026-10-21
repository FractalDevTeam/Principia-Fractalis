# LEGION — status

**Updated:** 2026-10-21 18:2x · **Owner:** Legion session (march ownership, pipeline, research)

## Current task

§2 LEGION items 1–2 are **done**; item 3 (D=2 band on the repaired producer) is
**blocked on two decisions that are Pablo's**, below. The D=1 band is running
unattended and is the only build I have in flight.

## Last landed

| commit | what |
|---|---|
| `5c48f698` | lock contention no longer stops the band (shared flock with YM) |
| `48ef3fca` | §0B study answer: the asymmetry analog exists and is deleted by construction |
| `2089b8b5` | march priced against the deployed criterion; `march_schedule.txt` (36 rows) |
| `b2c3a26c` | Legion native-build standup; panel modules need 7 GB not 12 |
| `ab2a4586` | **§2 task 1** producer pipeline repair + input drift guard |
| `89a5fdb1` | `ω(1) ≤ 1/22`, `L0_le_rat`, `box_of_enclosure_rat` |

§2 task-by-task: **1** done (`ab2a4586`, 9/9 md5). **2** and **5** were already
done by Acer on the same instruction set — I verified rather than duplicated
(see that commit body). **3** done: landed c=7 regenerates **16/16
byte-identical** from the repo producer. **4** done: D=2 box emitted at c=81/8,
Seg01 pack built, **not landed** — evidence in `codex/data/`.

## In flight

* **D=1 band**, `codex/march_run.sh` under `nohup setsid` on Acer. 24 boxes
  landed, frontier **9.8125**, building **c=39/4**. Hard-stops at c = 10.0625
  per §0.7. Its untracked `_c39_4_` files in `PF/Analytic/` are the in-flight
  box — **`commit_box.sh` will add them; no other session should.**
* Nothing else of mine is building. The Legion-side native builds are finished.

## §0.7 is now superseded by evidence, and that is my doing to report

§0.7 says the deployed producer is `/tmp/prod/gen_box.py` with no density
machinery, and the repo producer cannot run from the tree. **Both halves are
fixed as of `ab2a4586`:** the nine inputs are committed at
`codex/gen/`, `codex/addons/` and `codex/R1_c27_4_…UNCONDITIONAL_2026_10_19.lean`,
the repo producer runs from the tree, and `march_box.sh` points at it (Acer's
edit). The producer now also refuses to start if any input drifts.

§0.7's other clause — "the march hard-stops at c=10 until the pipeline is
repaired" — I have **not** overridden. The band still stops at the D=1 band
edge, because going past it needs the decisions below.

## Two decisions for Pablo, blocking §2 item 3

1. **`--extend-midpoint` on or off for D ≥ 2.** Measured: with the default
   boundary the march **does not reach 13 under any safety factor** (stops at
   12.906250). Extending it is free — same tier, same M-bound proof,
   byte-identical at D = 1 — and takes 397.8 h → **225.3 h**. It changes every
   emitted box past the band edge, so I have not turned it on.
2. **The safety factor.** §0.8 is right that the deployed march applies none.
   That is currently true by default rather than by decision: at the default
   boundary, requiring 1.25× makes 13 unreachable. With the extension it costs
   62 h (287.5 vs 225.3). This is a claim-strength call.

## Lanes I would cross — flagged before starting, per §1

* `codex/march_box.sh` — **Acer owns it** (Acer pointed it at the repo producer
  and added `check_march_axioms.py`). I propose **two** changes and have made
  **neither**: align its `flock -n` to a blocking `flock -w` to match Acer's own
  `-x` convention (see Conflicts below), and add `-M 7000` to its
  `lake env lean` calls. Measured basis: panel
  modules build fine capped (54/54 and 4/4 declarations on the bar), the band
  currently runs at **12.3 GB of 15**, and the cap costs ~16% on range modules
  and **nothing** on midpoint (449 s capped vs ~461 s uncapped). Acer's call.
* `PF/Analytic/TransferOperator.lean` — three docstrings (1244, 3050, 3854) call
  `T3_self_adjoint_conj` an `axiom`; the file has **zero** axioms and it is a
  proved theorem (line 3545). Not edited: that module is inside the march's
  dependency closure, so touching it mid-band invalidates oleans the running
  band depends on. For whoever holds the file, after the band.

## Outside the repo — everything the program depends on that is not committed

Shipped in this update: `codex/data/rss_peaks_2026-10-21.log` (100 measured
per-module peak-RSS samples — the evidence for the 7 GB cap),
`codex/data/d2_c81_8_seg01_evidence_2026-10-21.txt` (task-4 axiom output),
`codex/legion_build10.sh` (the Legion native serial capped builder).

Named, not shipped:

| lives at | what it is | if lost |
|---|---|---|
| `/tmp/d2test/` on Acer, 26 files | the emitted D=2 box at c=81/8 (task 4) | regenerate: `cd codex && python3 gen_box.py --c 81/8 --r 1/16 --density 2 --out <dir>` |
| `PF/Analytic/FourierPanels/{CoreDefs,Seg01Range,Seg01Midpoint}_c81_8_*.lean` | the 3 task-4 sources, installed untracked so Lean could resolve module paths | regenerate as above; **deliberately not landed** |
| `/tmp/prod/` on Acer | the **superseded** pre-repair producer; `march_box.sh` keeps it as a commented emergency fallback | its `gen_box.py` has **no density machinery** — do not re-point at it without re-reading §0.7 |
| `/tmp/prodD/`, `/tmp/prodR/` on Acer | new-vs-reference producer copies used for the D=1 byte-identity test | regenerable from git history |
| `/tmp/march_*` logs, `/tmp/d2seg01_*`, `/tmp/sched2.log`, `/tmp/closure.txt` | band and build logs; the 428-module closure used for the staleness check | evidence only; conclusions are in the commit bodies |
| `D:\CLAUDE-i9\_tmp\pf-ocirc-verify-20261001\PF_Lean4_Code` on Legion | **the second build host.** Current PF sources + packages junction + 1732 cached oleans + the 13 modules I built natively | not shippable (build cache). Recipe is in my memory note `infrastructure_legion_lean_verify_tree`; manifest md5 matches Acer's `ce569bf7…` |
| `D:\CLAUDE-i9\_tmp\legion_*.log`, `lb_*.log` | native-build evidence (rc, timings, axiom output) | the conclusions are in `b2c3a26c` |
| Legion session scratchpad (`…\Temp\claude\…\scratchpad\`) | `patch_*.py` producer patch scripts, `ref/` pre-density producer snapshot, commit-message drafts | historical; the producer itself is committed, so none is load-bearing |

**Legion is a build host, not just an analysis seat.** It builds march modules
natively with identical evidence to Acer (same declaration counts, same axiom
set). It is **not** currently taking band boxes: with `-M 7000` it can, but the
split needs decision 1 above and Acer's agreement on `march_box.sh`.

## Conflicts with other sessions

**Read `codex/status/acer.md` (upstream `23532902`). No conflict.** Acer's lane
is `PF/YangMills/*` and its in-flight work is Steps 5–6 of the Fubini discharge;
mine is the march, the producer and the Legion build host. No shared files, and
nothing I was about to start is in flight there.

(I had written "I am the first to write a status file" — wrong. My session-start
`git pull` predated Acer's push by minutes. Corrected here rather than left
standing, because the board is only useful if it is accurate about itself.)

**Two corrections to acer.md, raised rather than edited** — it is Acer's file:

1. **`48ef3fca` is Legion's commit, not Pablo's.** acer.md records "Pablo then
   committed a fuller answer at 48ef3fca". That was this session, answering the
   §0B study question. It matters only for routing: follow-ups on the asymmetry
   result come here, not to Pablo.
2. **Acer's flock convention and `march_box.sh`'s disagree, and that is the
   whole contention bug.** acer.md states Acer takes `flock -x` — blocking,
   exclusive wait. `march_box.sh` takes `flock -n` — fail immediately. So when
   Acer legitimately held the lock at 17:08:51, the march read contention as
   failure and stopped. My `5c48f698` makes `march_run.sh` retry, which works
   but is a patch at the wrong layer. **The clean fix is to align
   `march_box.sh` to a blocking `flock -w`, matching Acer's own convention** —
   then the contention class disappears instead of being caught. `march_box.sh`
   is Acer's file; I have not touched it.
