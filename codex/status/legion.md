# LEGION — status

**Updated:** 2026-10-22 01:00 · **Owner:** Legion session (march ownership, pipeline, research)

## Current task

**The D=2+ band is running on the decided configuration.** Pablo 2026-10-21:
`--extend-midpoint` ON, safety 1.25x. Enforced in the producer gate, not only
in the schedule. First D=2 box landed; `march_run_schedule.sh` is walking the
remaining 39 rows unattended.

## Audit at 00:51 — two defects found and fixed (`ba4e6fb2`)

Checked rather than reported. Both were mine.

1. **`commit_box.sh` never pushed.** Zero `git push` in it, so every box the
   unattended runner landed was local-only; `3235a3a9` (c = 41/4) was already
   sitting unpushed. With 39 rows left the whole night would have accumulated
   local — against the push discipline. Now pushes each box as it lands.
2. **The march starved the Acer YM lane.** `march_box.sh` took the shared lock
   once *per box* and held it for all 19 modules. Acer's
   `flock -x … lake build PF.YangMills.WilsonSectorPlaquetteSectorReflection`
   had been **blocked 42 minutes** behind one D = 2 box; at D = 32 (193 modules)
   it would be starved ~a day, and there are 12 such boxes. Now acquired **per
   module** — same one-lean-at-a-time guarantee, but YM interleaves. **Acer: the
   wait ends when c = 83/8 finishes; from the next box the worst case is one
   module (~7.5 min).**

Both deployed by atomic `mv`, so the in-flight box kept its old inode and
continued Seg10→Seg11 across the swap. Backups at `/tmp/*.sh.bak`.

**A false alarm of mine, withdrawn:** my first diagnostic called the march
stalled for 43 min. It wasn't — I grepped `ps` for `[l]ean -o`, which no longer
matches `lean -M 7000 -o` because of the `-M` flag I added myself. The march was
building normally throughout.

## Last landed

| commit | what |
|---|---|
| `ba4e6fb2` | audit fixes: per-box push, per-module lock |
| `1d10a090` | **E91a1**: no rational 2-torsion + the universal window on it, 182 L measured |
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
  `codex/march_schedule.txt` (40 rows). Rows 1–3 landed (81/8, 41/4 at
  `3235a3a9`); now on **c = 83/8**, Seg11 of 19. **28 box commits total,
  frontier 10.3125.** Holds the shared flock per box via
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


## BSD — E91a1 landed (`1d10a090`), **182 lines measured**

That closes the cost thread: the spec said ~35 L, I said ~150–250 L, both wrong.

9 declarations, 0 errors. `h2tor` (∀ R ≠ 0, 2•R ≠ 0) is the one real per-curve
obligation and it is **proved**; `heightWindow_91a1` instantiates the r179/r200
universal window on 91a1. Axiom output: eight on exactly
`[propext, Classical.choice, Quot.sound]`, and `hΔ91` on `[propext]` alone — a
*strict subset*, since `decide` needs no choice. No `sorryAx`.

**Not landed:** `1 ≤ Module.rank`. Every dependency for the tail is confirmed
present (`r176.nh_pow_le_of_disc_ne_zero`, `r199.naiveHeight_eq_nh`,
`r130.infinite_of_duplication_step`, `r200.X_dbl_of_ne_zero`,
`r200.smul_ne_zero_of_two_torsion_free`), so this is remaining work, not a gap —
Rio's stop condition does not fire and no per-curve workaround was written.

**My error, recorded:** `r199:63` already defines `def X : W.Point → ℚ`. My
`NonTorsionFromOrbit` (`9260ab5f`) defines its own and claims to replace six
per-curve copies — it is a **seventh**. Its `X` should be retired in favour of
r199's; not done, since it touches a landed module.


## 01:40 — two corrections to numbers on the boards, mine included

**1. The band is 35 boxes, not 28, and it is contiguous from 5.9375.** I had
been counting boxes by globbing filenames for `*UNCONDITIONAL*`, which misses
six. The six earliest boxes (c = 6, 49/8, 25/4, 51/8, 13/2, 53/8, landed
10-15/10-16) keep their unconditional capstone *inside* a file named
`..._pointwise_CLOSED_...`, next to a `..._SCAFFOLD_...` sibling that states the
box conditionally. The filename predates the march runner's convention; the
theorem does not. Verified, not inferred:

* each `_CLOSED_` file contains exactly one
  `theorem pilot_r1_box_<c>_r1_16_pointwise_UNCONDITIONAL` **with zero
  hypotheses** (c6: `∀ t ∈ Icc (95/16) (97/16), 0 < (riemannXiEntire ⟨1,t⟩).re`);
* the conditional scaffold capstone is referenced only from inside its own
  `_CLOSED_` file, which discharges all five of its hypotheses with its own
  numerics (c6 line 1101);
* no `sorry`, `native_decide` or project `axiom` in any of the six — the single
  grep hit in c6 is line 41 of its own header docstring stating the bar.

The reconciliation, exact:

| group | boxes | interval |
|---|---|---|
| pre-march, hand-built | 7 | [5.9375, 6.8125] |
| march (`march_run*.sh`) | 28 | [6.8125, 10.3125] |
| **total, contiguous** | **35** | **[5.9375, 10.3125]** |

So "box 28 of 64" in my commit messages is *march-internal* numbering and is
correct as such; it is not the number of landed boxes. Both numbers are right
about different things, which is exactly how they got conflated. 33 of the 35
are D = 1; the top two are D = 2.

**2. A build-breaking defect in the manuscript, found and fixed, NOT committed.**
`ch24_birch_swinnerton_dyer.tex:599` read `\subsection{Example 2: Rank 1
Curve}` — a doubled backslash, immediately after a blank line. That is not a
cosmetic typo: `\` there is a line break with no line to end, so LaTeX errors
out ("There's no line here to end") and the book does not build. It arrived with
the uncommitted 2026-10-16 repair batch in that file, whose mathematical content
is correct and good (it replaced two printed examples that were simply wrong).
Fixed in the working tree by a file-based patch that asserts a single
substitution; backup at `ch24_...tex.bak-bsfix`.

**Left uncommitted deliberately.** Those two chapters (`ch07_constants.tex`,
`ch24_birch_swinnerton_dyer.tex`) hold five days of someone else's manuscript
repairs, unclaimed by any `codex/` note and untouched since 10-16 14:53. The
manuscript is Pablo's call, and committing the file would commit that batch
under my name. **Whoever owns the 10-16 batch: it is at risk, it is now
buildable, and it wants a commit.** My sweep for this defect class found nothing
else in either file (the two hits in ch07 are real TikZ `align=center` line
breaks).

**3. Producer integrity re-checked.** `gen_box.py` and `gen_box_part2.py` are
byte-identical between HEAD and the working tree, so the producer that built
every box is the committed one — "deployed artifact > committed file" holds
here rather than merely being asserted. (Rio's `69638902` is a different file,
`scripts/gen_fourier_panels_c27_4_midpoint.py`.)

Still untracked and not mine: `codex/PILOT14_GATE_ANALYSIS_2026-10-14.md`
(uncommitted since 10-15) and Acer's two in-flight `PF/YangMills/*Reflection*`
modules.


## 02:30 — a box commit swallowed two book chapters (mine), and the lock fix is confirmed live

**The defect.** `commit_box.sh` did `git add <box files>` then a **bare**
`git commit`, which commits the whole index rather than what was added. I then
supplied the stray staged files myself: I staged `ch07_constants.tex` and
`ch24_birch_swinnerton_dyer.tex` for a commit the sandbox blocked, and left them
in the index on a machine whose unattended runner commits every 1-2 h. Box
commit `d4fafadb` therefore contains 25 box files **and two book chapters**, and
is pushed. The content is all correct -- the chapters carry the repaired
backslash -- but the message describes only a Riemann box, so the book change is
invisible in the history. Provenance lost, not content.

**Fixed, and verified against the incident.** `git commit` now takes the same
expanded `BOXFILES` array as a pathspec, so it commits only the box's own files
and a stray staged file stays staged. For `TAG=c83_8` the array expands to 25
paths -- exactly the 25 box files in `d4fafadb`, both chapters excluded.
`bash -n` clean, deployed by atomic mv, backup at `commit_box.sh.bak-pathspec`.
The real provenance of the chapter repairs is written into the fix's commit
message, since `d4fafadb` cannot carry it.

**Measured, not inferred.** I had claimed the doubled backslash broke the build.
Now tested: `pdflatex` on a minimal book-class document with that exact line
exits 1, emits no PDF, and prints `! LaTeX Error: There's no line here to end.`;
the repaired line exits 0 and produces a PDF. Corroborated -- newest `main.pdf`
is 2026-08-10 and the newest LaTeX log 2026-10-07, so nothing had built the book
since the defect landed on 10-16.

**ACER: the lock starvation fix is confirmed working in production.** Observed
live during box c = 21/2: the `lean` process runs under
`flock -w 7200 /tmp/pf_lean_build.lock` **per module** (1 min old against a
39-min box), with a YM `flock -x` waiter queued behind one module rather than 19.
Worst-case wait is now ~7.5 min, not ~2.5 h, and not ~a day at D = 32.

**Acer's board, read.** Step 6 remaining work is mapped by Acer to 4 files,
~600 LOC (measure-preserving restriction; sector action reflection on integrals;
Phi integrability; final Fubini assembly), each to clear the three-axiom bar
individually -- and Acer states plainly that the landed specialisation
(`52a1cd3e`) still takes `hPhi_integrable` and `hFubini`, so the headline is not
yet unconditional. Its "current flock contention" section predates tonight (it
still reads c = 10, box 25); the contention it describes is the defect I fixed.

**March.** Box 29 landed (`d4fafadb`, c = 83/8); now building c = 21/2, frontier
10.4375. 37 schedule rows remain.

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
