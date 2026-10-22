# LEGION — status

**Updated:** 2026-10-21 23:xx · **Owner:** Legion session (march ownership, pipeline, research)

## Current task

**The D=2+ band is running on the decided configuration.** Pablo 2026-10-21:
`--extend-midpoint` ON, safety 1.25x. Enforced in the producer gate, not only
in the schedule. First D=2 box landed; `march_run_schedule.sh` is walking the
remaining 39 rows unattended.

## Last landed

| commit | what |
|---|---|
| `69638902` | commit the per-segment M tier in `scripts/` — 26 boxes depended on an **uncommitted** file |
| `bd2b33bf` | **the two staged fixes**: blocking `flock -w 7200` + `-M 7000` in `march_box.sh` |
| `8af253eb` | **final band box c = 10** — 25 decls on the bar, frontier 10.0625 |
| `02ba49c8` | correction: r177/r178 **do** universalise the group-law link; my cost claim was wrong |
| `9260ab5f` | **BSD item 1** — universal non-torsion step + validation against E43a1's capstone |

## D=1 band — done

**26 boxes, contiguous `[5.9375, 10.0625]` in t.** Every box kernel-clean with
its own `#print axioms` output on `[propext, Classical.choice, Quot.sound]`,
each committed before the next started. Final box `8af253eb`, 25 declarations.

The lock fix earned itself twice: the band hit contention again at c = 10 and
**retried instead of stopping**, one box short of target.

## In flight

* **D>=2 band**, `codex/march_run_schedule.sh` under `nohup setsid`, driving
  `codex/march_schedule.txt` (40 rows). Row 1 (c = 81/8) landed; now on row 2
  (c = 41/4, r = 1/16, D = 2). Holds the shared flock per box via
  `march_box.sh`'s blocking `flock -w`.
* Priced total **287.5 h (12.0 days)**, 2284 panel modules.

## The decided configuration, and what enforcing it required

| | |
|---|---|
| schedule | 40 boxes, 2284 modules, 287.5 h, 10.0625 -> 13 |
| producer gate | `1.25x * Q*r < Mc_lb` on the **proof's** majorant scale |
| `march_box.sh` | takes a density arg; passes `--extend-midpoint --safety 1.25` |

Two things §0.8 flagged are now actually true in the deployed path: the gate
compares on **Q** (the `omega(1) <= 1/22` majorant the proof carries, ~5% larger
than the tight `L0` it used to compare against), and the safety factor is
**applied** rather than existing only for `--pick-r`. Verified both ways —
`--safety 10` at a 3.89x centre refuses and emits 0 pilots, while reporting that
the bare criterion still passes, so a margin decision can never read as a
mathematical failure.

D defaults to 1 in `march_box.sh`, so re-running any landed box stays
byte-identical (`--extend-midpoint` is a no-op at D=1).

## The D=2 test found a real bug — `d78a7771`

`emit_assemble` had **`Seg03Range` hardcoded** for the two integrability
lemmas. Correct for every box ever built, because at D=1 segments 3–6 are
range-brick. With extend-ON at D=2, sub-segments 1–5 are midpoint and the range
modules start at 6, so the assemble failed on an unknown identifier. The density
refactor parameterised `MID_SEGS`/`RANGE_SEGS` but left that literal.

**The axiom gate caught the consequence independently** — the two headline
enclosure theorems came back carrying `sorryAx` from Lean's error recovery, so
the exact-set check would have refused the box even if the exit code had been
missed.

Fixed to `min(RANGE_SEGS \ MID_SEGS)` with an assertion that one exists. D=1
regeneration is **18/18 byte-identical**, so the landed band cannot be
perturbed; only the assemble changed, so the rebuild was 3 modules not 1.8 h.

Worth noting why building beat inspecting: this was the first D>=2 **assemble**
ever compiled. The earlier D=8 check read the emitted text's `linarith`
structure, and task 4 built only the Seg01 pack. A structural check on generated
text cannot find an unknown identifier.

## BSD — item 1 landed, items 2+3 next

**Item 1, `9260ab5f`:** `PF/NonTorsionFromOrbit_2026_10_21.lean`. Six curve
files each defined their own `X : E.toAffine.Point → ℚ` and re-proved the same
argument; it is now one universal lemma, 5 declarations, 0 errors, on the bar.
**Validated, not merely compiled:** `NonTorsionFromOrbitCheck_2026_10_21.lean`
re-derives E43a1's landed capstone through it, borrowing only the
curve-specific inputs and specifically *not* E43a1's `X`/`X_pts`/`P_nonTorsion`,
which would make the test circular.

**Evidence layer (§0.9):** both built on the **Legion** native tree under
`lean -M 7000`. **Acer has not built them** — the band held the shared flock.
Acer confirmation pending, not claimed. Now that the band is done this can run.

**Item 2+3 feasibility, Lean-evaluated** against the repo's own r174/r175/r177
definitions at `b₂,b₄,b₆,b₈ = 0,2,1,−1`:

| | |
|---|---|
| `Disc` | **−91** (matches the file and an independent recompute) |
| `CU` / `CL` / `kappa` | 9 / 24388 / **24388** |
| `4b₈` vs `b₂b₆ − b₄²` | **−4 = −4** → r177's `hrel` holds |
| threshold | `x(16P)` naive height **6088653225047446** ≫ 24388, fires at n=4 — same index E43a1 uses |

I have now been wrong twice on this cost (spec said ~35 L, I said ~150–250 L).
**I will report the measured figure when it is written rather than estimate a
third time.** What remains per-curve: `hrel`/`Disc` (both `decide`), `y ≠ negY`,
the doubling chain with explicit x-values, and the flag.

**Target, restated:** `1 ≤ Module.rank` — a *lower* bound. Not an exact rank.
`rank = 0` is false for all four gap curves, and an exact rank needs the
2-Selmer upper bound on a curve with rational 2-torsion.

## Blocked on Pablo

Nothing. Both decisions landed 2026-10-21 and are in force.

## A reproducibility hazard found and closed — `69638902`

`PF_Lean4_Code/scripts/gen_fourier_panels_c27_4_midpoint.py` had **uncommitted**
changes (the per-segment `M_for_seg` tier replacing `M_VALUE = Fraction(24)`),
not mine — they predate this session. Measured md5s: working tree and my
committed `codex/gen/` copy both `ae5ddfa1…`; **git HEAD held the old
`1b60400a…`**. So the version all 26 landed boxes were generated with lived in
exactly two places: one uncommitted file, and the duplicate I happened to commit
during the `ab2a4586` repair. A `git checkout -- scripts/` would have reverted
the canonical copy, my drift guard would have fired correctly, and the next
session would have had to diagnose it. Now committed. The range generator was
**not** diverged (all three copies `d6099e42…`).

## Lanes / do-not-touch

* `PF/Analytic/TransferOperator.lean` — three docstrings call a proved theorem
  an `axiom`. **Rio: leave it alone** until the march passes it. Untouched.
* `codex/status/acer.md` — the `48ef3fca` attribution is Acer's to fix.
* `Principia_Fractalis_master_folder/chapters/ch07_*.tex`, `ch24_*.tex` have
  uncommitted edits — **BOOK WORK's lane**, not touched.

## Outside the repo

Shipped earlier: `codex/data/rss_peaks_2026-10-21.log`,
`codex/data/d2_c81_8_seg01_evidence_2026-10-21.txt`, `codex/legion_build10.sh`.
Unchanged and still named: `/tmp/d2test/` (one command to regenerate), the three
untracked `_c81_8_` sources (deliberately not landed), superseded `/tmp/prod`
and its no-density hazard, `/tmp/prodD`, `/tmp/prodR`, band logs, and the Legion
verify tree at `D:\CLAUDE-i9\_tmp\pf-ocirc-verify-20261001\` (1732-olean cache,
not shippable; recipe in memory note `infrastructure_legion_lean_verify_tree`).

**New:** the Legion tree now also holds the two BSD modules and the 13 natively
built oleans; the BSD falsification script and the 91a1 constant probe live only
in the Legion scratchpad — named, trivially rewritten, results recorded above.

## Conflicts

None. Acer is in `PF/YangMills/*` on Fubini Steps 5–6.
