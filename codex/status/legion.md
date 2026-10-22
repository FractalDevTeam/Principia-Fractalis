# LEGION — status

**Updated:** 2026-10-21 late evening · **Owner:** Legion session (march ownership, pipeline, research)

## Current task

**D=1 band is COMPLETE.** Both staged script fixes applied and pushed. BSD
item 1 (the universal non-torsion step) is landed and validated. Next: BSD
items 2+3 for 91a1, whose feasibility constants are now Lean-verified.

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

Nothing building. No locks held by me.

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

**`--extend-midpoint` on/off, and safety 1.25× vs 1.0×.** Rio recommends extend
ON + 1.25×. Measured: default boundary **does not reach 13 under any safety
factor** (stops 12.906250); extend+1.0× = 225.3 h, extend+1.25× = 287.5 h,
default+1.0× = 397.8 h. **No D=2 boxes emitted until these land.**

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
