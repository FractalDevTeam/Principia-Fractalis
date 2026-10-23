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


## 03:16 — the 91a1 rank bound LANDED (`d32dd117`), 275 lines measured

```
E91a1_rank_ge_one : 1 <= Module.rank Z E_91a1.toAffine.Point
P91_nonTorsion    : not (IsOfFinAddOrder P91),   P91 = (0,0)
```

rc=0, 3421 jobs, olean produced. All 11 axiom-checked declarations on exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`, `nativeDecide` or
`ofReduceBool` anywhere in the build. **The un-landed tail from yesterday is now
landed** — and it was remaining work, not a gap, exactly as recorded.

**Honest scope, unchanged:** a LOWER bound on ONE curve. Not the exact rank,
nothing about `L(E,s)`, no part of BSD.

**Cost, measured rather than estimated:**

| | lines | decls |
|---|---|---|
| part 2, this capstone | **275** | 29 |
| part 1 (`1d10a090`) | 182 | 13 |
| **91a1 total** | **457** | 42 |
| `E43a1RankOne_r135`, same conclusion, hand-written | **815** | — |

The 815-line comparator re-derives the Bezout layer, size bound, height join and
driver glue per curve. That is the work the universal layers delete. Nothing
general was re-derived here: r178 for `dblQ`, r176 for the quartic step, r199
for the height bridge, r200 for `X(R+R)` and `2^n.R /= 0`, r130 for the driver,
r129 for the flag. The only new arithmetic is 91a1's own orbit.

**The orbit, exactly:**

```
x(2^n P) : 0 -> 1 -> -2/9 -> 8845/441 -> 6088653225047446/1223724862004841
heights  : 1,   1,    9,      8845,      6088653225047446
```

Threshold bites at `n = 4` — the same shift E43a1 needed.

**kappa computed, never transcribed.** `kap` is *defined* as
`(CL 0 2 1 (-1)).toNat`; `0 < kap` and `kap < 6088653225047446` are proved by
`norm_num` unfolding r175's sixteen cofactor polynomials. Lean computes it, so a
wrong hand-copied value could not hide. Build `#eval` reports **kap = 24388** —
so yesterday's conversational 24388 is now measured, not assumed.

**Why `Psi /= 0` was the whole curve-specific story.** On 91a1
`Psi 0 2 1 X Y = Y*(4X^3 + 4XY^2 + Y^3)`: the duplication denominator IS the
2-torsion cubic, so part 1's parity argument makes `Psi_ne_zero_at` hold at
*every* rational. No case analysis along the orbit, and the orbit can never
reach the identity.

**My duplicate-`X` defect is now load-bearing, and visible rather than hidden.**
The r130 driver consumes `NonTorsionFromOrbit.X` (my seventh copy) while the
capstone should speak through r199's. `X_bridge` proves them equal by
`cases <;> rfl`, docstringed as the pending retirement. Retirement still open.

**Two errors of mine this stretch**, both cheap and both now fenced: `lake` is
not on a non-interactive ssh PATH (needs `$HOME/.elan/bin`), and Lean block
comments NEST — my explanatory text quoted `/-` tokens and swallowed its own
terminator, costing one full lock cycle. I wrote a comment-nesting checker and
validated it against the exact failing input rather than just fixing the line.

**ACER: both lanes are now progressing through the per-module lock.** While my
capstone queued, Acer took the lock and landed `17c2afbf` and `76931203`
(plaquette time-sector reflects strictly; pointwise refined-sector reflection on
non-diag plaquettes) — two of the three files I had flagged as uncommitted.
`WilsonSectorRefinedSumIdentity_2026_10_21.lean` is still untracked, and is
Acer's to commit. Three-way lock queues (march / YM / BSD) are resolving in
minutes, which is what the fix was for.

**March.** Box 29 landed (`d4fafadb`, c = 83/8); building c = 21/2, frontier
10.4375. 37 rows remain.


## 08:45 — the CI axiom gate's *proposed fix* had a hole of its own (`05cd082d`)

**`verify.sh` and the workflow are still untouched** — applying the gate remains
Pablo's call, as recorded 2026-10-17, and the commit's diff against `verify.sh`
and `.github/` is empty. What was wrong is the **proposal** and its self-test.

The 10-17 proposal parsed axiom records with
`r"'([^']+)' depends on axioms:..."`. Lean quotes the declaration name, so a
name **ending in a prime** prints with a doubled quote —
`'...sub_ne_zero'' depends on axioms:`. `[^']+` stops at the inner prime, the
marker no longer follows, and **the record is silently skipped, not flagged.**
A `sorryAx` in any `foo'` would have passed the replacement gate. Primed names
are ordinary Lean style.

**Found by measurement, not reading.** The 10-17 note *was* written by reading,
and this survived both that reading and the self-test. It surfaced only on a
real transcript — the 3421-job build of my capstone:

```
records parsed, proposed parser : 551
lines selected, old line-grep   : 555
```

The replacement parsed FOUR FEWER records than the broken logic it replaces.
That negative delta was the whole tell. The four: r131/r144
`reduced_height_bound'`, r157 `dvd_R6_of_dvd_forms'`, r199 `sub_ne_zero'`.
Fixed by anchoring the name on the marker with a greedy `[^
]+` — now 555/555.

**The new fixture needed five records, and that is the point.** `F5_primed` is
four *clean* records plus the primed violating one. Four records *including* it
would be rejected by the `MIN_RECORDS` guard even with a broken parser — passing
for the wrong reason, the exact slip already on record against this self-test's
first version. Discrimination proved by swapping the parser back:

| parser | F5 | selftest |
|---|---|---|
| `[^']+` as proposed | **PASS** (wrong) | FAILED, exit 1 |
| `[^
]+` fixed | **FAIL(axiom)** | PASSED, exit 0 |

**What this says about applying the gate.** On the closure measured the fixed
gate goes **green**: 522 `[propext, Classical.choice, Quot.sound]`, 16
`[propext]`, 16 `[propext, Quot.sound]`, 1 `[propext, Classical.choice]` — the
small sets are *subsets* of the bar (`decide` needs no choice), not violations.
**Scope, honestly:** one BSD capstone's import closure, not the whole `PF`
target. It does not license a claim about the tree; it does show the fixed gate
is not sitting on a pile of violations in the part measured.

`codex/ci_gate_audit_transcript.py` is committed so this question is answerable
from any ordinary `lake build` log — **no rebuild, no build lock.**

Still open in `verify.sh`, unchanged and Pablo's: the `grep -vE` line-deleter
(so `exit 2` is unreachable), the empty transcript (`PF.lean` imports the three
AxiomCheck modules at 1293/1346/1355-1357, so the three `lake build
PF.AxiomCheck_*` calls are no-ops, and `|| true` swallows failures),
`cancel-in-progress: true`, and `github.sha` in the primary cache key.

## 08:45 — march, and the pathspec fix verified in production

Four more boxes landed unattended while I worked on the gate: **boxes 30-33**
(c = 21/2, 85/8, 43/4, 87/8), frontier **10.9375**. 40 boxes total now
(34 UNCONDITIONAL-named + 6 CLOSED-named). Now building **c = 11 at D = 4** —
the first D = 4 box of the schedule.

**The pathspec fix works on the thing that runs.** `dedd3918` is the first box
committed after it; it and the three following each contain **exactly 25 files,
0 non-box files**. Before the fix, `d4fafadb` carried 25 box files plus two book
chapters.

**Acer** landed `24a2a90c` (sum-level refined sector reflection,
S_-R(theta U) = S_+R(U)) and refreshed its board (`081c0918`): the
sector-action-reflection block is done and it calls the remainder mechanical
plumbing. Its three in-flight files are down to committed work plus
`WilsonSectorRefinedSumIdentity`.


## TO ACER — read this first (Legion, 2026-10-22 ~16:20)

**Three things that affect your lane directly.**

**1. Legion has moved to mathlib PR repairs and is NOT using the Acer build
lock.** Rio assigned me #42093 and #42100 (both red Build checks). That work
runs on Legion hardware plus GitHub CI — it touches
`/tmp/pf_lean_build.lock` **not at all**. So for the duration, the only
competitor for the lock is the unattended march (one module at a time, ~7.5 min
worst case). **The lock is effectively yours for Step 6.** This is the opposite
of last night's starvation; use it.

**2. A trap that will bite any mathlib branch you touch after a master merge.**
#42093's Build failure was not a Lean error at all. The 2026-10-22 merge of
master brought in a newer `linter.style.header.imports`, and its
"Imports can be reformatted" warning is **build-failing** in mathlib CI:

```
warning: .../TwoSidedIdeal.lean:10:0: Imports can be reformatted:
Some required targets logged failures:
- Mathlib.Topology.Algebra.Ring.TwoSidedIdeal
error: build failed
```

The entire fix was swapping two import lines into sorted order
(`...Algebra.IsOpenUnits` sorts before `...Algebra.Ring.Basic`). If you ever
merge master into a mathlib branch, expect a red Build from import order alone
and do not go looking for a maths error.

**3. The CI axiom gate that is supposed to verify your YM modules cannot fail.**
Detail in the 08:45 entry above and in
`codex/CI_GATE_PRIME_HOLE_2026-10-22.md`. Two independent defects in
`verify.sh`, both still live: the allowlist is applied as a line *deleter* so
`exit 2` is unreachable, and the transcript is empty because `PF.lean` already
imports the AxiomCheck modules. **Your `wilson_reflection_positivity` axiom
claims are currently checked only by whatever greps you and I run by hand, not
by CI.** The gate fix is written and self-tested but applying it is Pablo's
call. `codex/ci_gate_audit_transcript.py` will audit any `lake build` log you
already have, with no rebuild and no lock — worth running on your Step 6 log
when it lands.

Nothing of yours is touched by any of this: no `PF/YangMills/*`, no
`TransferOperator.lean`, no shared scripts beyond the `commit_box.sh`/
`march_box.sh` fixes already reported.

## mathlib #42093 — repaired and pushed (Legion, 2026-10-22)

**Error, read from CI's own log** (run 39808925118, job 119929728821, head
`5782b447`, Build failed in 1m49s; Test-and-lint and Lint-style were green):

```
##[warning]warning: Mathlib/Topology/Algebra/Ring/TwoSidedIdeal.lean:10:0:
  Imports can be reformatted:
    public import Mathlib.RingTheory.TwoSidedIdeal.Lattice
    public import Mathlib.Topology.Algebra.IsOpenUnits
    public import Mathlib.Topology.Algebra.Ring.Basic
Some required targets logged failures:
- Mathlib.Topology.Algebra.Ring.TwoSidedIdeal
error: build failed
```

**Diagnosis: merge fallout, not the PR's own code.** Head `5782b447` is a
web-flow "Merge branch 'master'" commit from 2026-10-22 ~08:52 whose file list
is dominated by `.github/**`. That merge brought in a newer
`linter.style.header.imports` which requires the import block sorted and whose
warning is build-failing under mathlib's required-targets mechanism. The branch
was all-green before it. `IsOpenUnits` sorts before `Ring` (`I` < `R`), so the
block as written was unsorted.

**Fix — the smallest change that builds:** swap two import lines into sorted
order. Verified a pure reorder: byte length unchanged and the line multiset
unchanged, so nothing but order moved. Diff is
`1 file changed, 1 insertion(+), 1 deletion(-)`.

**Commit** `44557bce1d`, pushed `5782b44727..44557bce1d` onto
`DrDMT-VR:feat-twosidedideal-closure`. Build check being watched; result
recorded below when it settles.

**The design question was NOT touched.** j-loreaux's open point (a separate
`TwoSidedIdeal` API versus generalising `Ideal`) is untouched by an import
reorder — no declaration, statement, or API surface changed. Per Rio's stop
condition, no design decision was needed.

**No public comment of any kind was made.** Code push only; the reply is
Pablo's.

**One honest limitation.** I did not reproduce the failure with a local mathlib
build. The branch needs toolchain v4.36.0-rc1 while the Legion clone is on
v4.35.0, so a local repro means a fresh multi-GB cache for a different
toolchain on Pablo's interactive machine — and my own recorded incident is a
Legion runaway costing him his desktop. I read the failure from **CI's own log**,
which is stronger evidence than a local repro, and the fix is the exact
reordering the linter itself printed. CI is the verification. If the Build check
comes back red I will stand up the local build rather than guess again.

**Worktree discipline:** the Legion mathlib clone had **4 dirty files** of
someone's in-flight #42101 work (`ZetaAsymp.lean`, `RiemannZeta.lean`,
`PR42101Axioms.lean`, `PR_DESCRIPTION.md`). I did not switch its branch. I added
a separate `git worktree` for the #42093 branch; that tree is still on
`feat-riemannzeta-conj` with all 4 files intact, verified after the checkout.


## mathlib #42093 — GREEN (Legion, 2026-10-22)

`ci (fork) / Build` **pass** on head `44557bce1d`, with Post-Build Step, Upload
to cache, Lint style, main and Verify-Transient all pass. (Test-and-lint and
Lint-and-suggest were still running; they were green on the previous head.)

Fix as described in the entry above: two import lines swapped into sorted order.
Merge fallout from the newer `linter.style.header.imports`, not the PR's code.
Design question untouched. No public comment.

## mathlib #42100 — STOPPING, and why (Legion, 2026-10-22)

**The defect I was sent for was real and is fixed.** `mk_all --check` was
failing:

```
The file 'Mathlib.lean' is out of date: run `lake exe mk_all` to update it
```

Not a Lean error — the same run reported `[8686/8687] Built Mathlib (2.5s)`.
Rather than run `mk_all` (it needs the branch's three-month-old toolchain
built), I checked all 8295 import lines for ordering inversions: exactly **one**,
no duplicates — `...CFC.SpectralProjection` listed before `...CFC.Restrict`,
which sorts first. Moved that one line; re-ran the checker: **no inversions, no
duplicates**. Commit `2c6837ebfe`.

**Confirmed effective:** the new build log contains no "out of date" message at
all, and `Test and lint` + `Lint style` are now **pass**. The job stops earlier,
at a different gate.

**That gate is the blocker, and it is not our code:**

```
ERROR: Your branch's 'lake exe cache' tool is outdated.
It reads from storage that CI does not write for your branch, so it will miss
the artifacts CI builds for your branch and rebuild them locally instead.
Please merge 'master' into your PR branch and push again.
```

CI refuses to build at all — 42 s — until upstream master is merged.

**Measured facts behind the stop:**

| | |
|---|---|
| #42100 head `7f7138a1` commit date | **2026-07-26** (not 10-14; that was a skipped "Check PR titles" run) |
| branch toolchain | `v4.33.0-rc1` |
| upstream master toolchain | `v4.36.0-rc1` |
| **Pablo's fork `master`** | `c8830a1d9c`, **2026-07-25**, also `v4.33.0-rc1` |
| branch vs fork master | **0 commits behind** |

So **merging the fork's own master is a no-op** — it is the same vintage as the
branch. The merge CI wants is of **upstream** `leanprover-community/mathlib4`
master, which is ~3 months and a toolchain ahead.

**Why I stopped rather than doing it.** That is not "the smallest change that
builds":

1. It is a three-month mathlib merge plus a toolchain bump, into an actively
   churning area (`Analysis/CStarAlgebra/ContinuousFunctionalCalculus`), where
   the PR's two new files must still compile.
2. I cannot even **assess** the merge locally: the Legion clone is **shallow**
   (2 grafted tips), so merge-base is empty and `merge-tree` reports "refusing
   to merge unrelated histories". Assessing needs an unshallow fetch of full
   mathlib history.
3. I cannot **verify** the result without a full mathlib build — hours — and I
   will not run that on Pablo's interactive machine (my own recorded runaway
   took his desktop to 51 MB free) nor on the Acer (one build lock, shared with
   the march, Acer mid-Step-6).
4. Post-merge proof repair against three months of CFC drift is upstream-drift
   adaptation, i.e. a material scope change — Pablo's call, not mine.

**Recommended next action, and it is one click:** use GitHub's **"Update
branch"** on #42100. That is exactly what put #42093 right — its head
`5782b447` is a web-flow "Merge branch 'master'" commit carrying toolchain
`v4.36.0-rc1`, i.e. a merge of the *upstream* base, not the fork's master.
After it lands, CI will actually build, and whatever it then reports I will
diagnose. I did not click it myself: it rewrites the PR head with a merge of
3 months of upstream, which is the scope change above.

**I did NOT attempt a narrower workaround.** Hand-updating just the `Cache/`
tooling or bumping `lean-toolchain` alone would be inventing a fix against CI's
explicit instruction, and the cache tool has to match both the protocol and the
toolchain. Reporting beats guessing here.

**No public comment on either PR.** Code pushes only.

**Side findings worth keeping:**

* Pablo's fork `master` is stale at 2026-07-25. Any branch cut from it inherits
  this exact blocker, so it is worth refreshing independently of #42100.
* This Legion clone **fails to write refs** intermittently and now
  reproducibly (`error: couldn't set 'refs/remotes/upstream/master'`) while
  objects fetch fine and the disk has 1.2 TB free and refs/heads is writable.
  Worked around with `--detach` worktrees and by addressing commits by SHA.
* Pablo's #42101 work in that clone is **untouched**: 4 dirty files
  (`ZetaAsymp.lean`, `RiemannZeta.lean`, `PR42101Axioms.lean`,
  `PR_DESCRIPTION.md`) still present on `feat-riemannzeta-conj`, verified after
  every checkout. I never switched its branch.


## 2026-10-22 evening — data-protection sweep + #42100 merge (Rio's pass)

### 1. EXPOSED DATA, NOW PROTECTED (done first, as ordered)

**#42101 working tree — `e0f684ad`.** Those four files existed in exactly one
place: the working tree of a clone that was shallow and intermittently failed to
write refs, two of them untracked (so `git stash` would not have covered them by
default), with Pablo mid-reply on that PR. Landed at
`codex/data/pr42101_worktree_snapshot_2026-10-22/` as **complete file contents**
— not just a diff, so it depends on no base commit staying reachable — plus the
116-line diff checked with `git apply --check --reverse`, SHA256SUMS, the base
commit and restore instructions. **All five hashes re-verified on the Acer after
transfer**, independently of the machine that produced them.

Deliberately NOT done: nothing committed or pushed to `feat-riemannzeta-conj` or
to PR #42101. Adding commits would move the PR head while Pablo is mid-reply,
and that PR's content is his.

**Scratchpad — `b4bf708e`.** Chosen by measurement: all 223 `.py/.sh/.lean/.md`
scratchpad files md5-hashed against **all 9942 tracked files**; **114 had no
content match anywhere** and are preserved at
`codex/data/legion_scratchpad_rescue_2026-10-22/` — one 164 KB archive (nothing
from the measured set omitted), `MANIFEST.txt`, and 10 reusable tools kept
readable. The other 109 are byte-identical to already-committed content.

Recorded honestly: **there is no file called "the BSD falsification script."**
The 91a1 constant probe is `chain91.py` and does exist under that description;
BSD-side checking was spread across four arithmetic probes plus Lean artifacts
already committed. Named rather than shipping something and labelling it that.

### 2. CLONE HAZARDS

**(a) Shallow — FIXED by unshallowing**, not replacement: `is-shallow` is now
`false`. This also removed the false readings the shallow clone had produced —
"refusing to merge unrelated histories", an empty merge-base, and "186 commits
ahead" where the true figure is **2151**.

**(b) Ref-write failures — diagnosed as far as the evidence allows, and not
over-claimed.** Transient, not deterministic: **15/15** `update-ref` writes
succeed on demand, including the exact ref that had just failed. They cluster
during large `fetch` operations, and one happened with no checkout running, so
"file locking during large checkouts" is not the whole story. Defender
real-time scanning is **on** and its exclusion list needs admin to read, so the
AV-contention hypothesis is *consistent with everything observed but unproven*.
I did **not** change `gc.auto` / `maintenance.auto` on a hypothesis I cannot
confirm — that would be cargo-culting.

What matters for safety was checked instead: **`git fsck --connectivity-only`
exits 0**, reporting only dangling objects (one of them literally a `probe` blob
I wrote with `hash-object`; the dangling tags are unshallow residue). Dangling
is not corrupt. **No missing or broken objects — the failed ref writes corrupted
nothing.** Proven workarounds: retry, `git worktree add --detach` (needs no new
branch), and addressing commits by SHA.

**(c) Scripts shipped** — see §1.

### 3. FORK HYGIENE — DONE

`DrDMT-VR/mathlib4` master fast-forwarded `c8830a1d9c` → `0db93bb444`,
advancing **2151 commits**, 2026-07-25 → 2026-10-22. Verified a clean
fast-forward first (`merge-base --is-ancestor` true), so **no force was used**.
Branches cut from the fork no longer inherit #42100's blocker.

### 4. #42100 — merged, then STOPPING on a proof-level break

The merge of upstream master, in the dedicated worktree, produced **exactly one
conflict, `Mathlib.lean` only**; the PR's own two added files merged clean
because upstream never touched those paths. That is inside Rio's bound, so I
resolved rather than stopped. Toolchain came across as `v4.36.0-rc1`.

**My own error, caught by CI and fixed (`33f1363009`).** My first resolution
*restructured* a generated file: it gathered every `public import` line and
sorted them as one block, which moved `Std` from first position to after every
`Mathlib.*` (S > M). mk_all rejected it, correctly. Redone by **literal text
insertion** into upstream's file, verified by reconstruction — deleting exactly
the two inserted lines reproduces upstream's `Mathlib.lean` byte-for-byte.

**STOP CONDITION FIRED — not mine to fix.** Upstream drift broke the PR's own
mathematics:

```
Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Ideal.lean:78:28:
Application type mismatch: the argument h has type
  Frequently (fun g => (cfcHom ha') g in I) (nhds f)
but is expected to have type
  Frequently (fun x => x in coe I) (nhds ((cfcHom ha') f))
in the application
  Frequently.mem_of_closed h
```

`Frequently.mem_of_closed` now wants the predicate stated at the image point
with the ideal coerced to a set, where the PR supplies it composed through
`cfcHom`. Adapting that is a mathematical decision about the PR's content —
Pablo's, not mine. **I did not touch it.**

No public comment on either PR at any point; code pushes only.

### 5. MARCH HALTED — found on sync, diagnosed, not yet fixed

The march **stopped at 11:54** and has been down since. First D = 4 box,
c = 11: all 24 Range + 11 Midpoint + 4 bound modules built `rc=0`; only
`Assemble_c11_threehalves_HYBRID` failed:

```
error: (deterministic) timeout at whnf, maximum number of heartbeats
       (2000000) has been reached        (lines 3031, 3036, 4116, 4121)
```

and two theorems consequently fell back to `sorryAx`:
`reLambda0_threehalves_hybrid_lb_ub` and `imLambda0_threehalves_hybrid_lb_ub`.

**The axiom gate caught it and the runner refused to commit the box** — the gate
working exactly as designed, and the reason no unsound box entered the tree.

Cause: the hierarchical `linarith` fold is `max(15, 12D-1)` wide, so D = 4 gives
**47** terms against 15 at D <= 2. This gates **every D >= 4 row** in the 40-row
schedule, not just c = 11. Two candidate repairs — raise `maxHeartbeats` in the
emitted Assemble, or deepen the fold another level so each `linarith` stays
small. The second is the better engineering; the first is one producer line.
**Measurement first** (how far over budget it actually is), which costs one
locked build. Frontier stands at **10.9375**, 34 boxes committed.


## #42100 — final state of this pass: reduced to ONE blocker

After the merge and three follow-up pushes, CI on head `988a252ceb` reports:

```
mk_all "out of date" messages           : 0
warnings in the PR's own two files      : none
errors                                  : Ideal.lean:78:28 and :78:44
```

Two error positions, one line, one cause. Everything mechanical is cleared and
the PR now carries exactly one genuine blocker.

Sequence, for the record:

| commit | what | result |
|---|---|---|
| `2c6837ebfe` | the inverted `Mathlib.lean` import line | cleared the `mk_all` defect |
| `6db80eacaa` | merge of upstream master, 2151 commits, toolchain → `v4.36.0-rc1` | cleared the outdated-cache-tool gate |
| `33f1363009` | redo my botched `Mathlib.lean` resolution by literal insertion | `mk_all` clean, verified by reconstructing upstream byte-for-byte |
| `988a252ceb` | sort `Ideal.lean`'s imports; `haveI` → `have` | no warnings left in the PR's files |

**The one blocker, untouched and reported:**

```
Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Ideal.lean:78
  | frequently f h => exact h.mem_of_closed (hI.preimage (cfcHom_continuous ha'))

Application type mismatch: the argument h has type
  Frequently (fun g => (cfcHom ha') g in I) (nhds f)
but is expected to have type
  Frequently (fun x => x in coe I) (nhds ((cfcHom ha') f))
```

`Frequently.mem_of_closed` now wants the predicate stated **at the image point**
with the ideal coerced to a set, where the PR supplies it **composed through
`cfcHom`**. That is upstream drift against the PR's own mathematics, so by Rio's
bound it is reported, not repaired — Pablo's call. The `haveI → have` change in
the same file introduced no new error, so it needs no revert.

## March — measurement in flight

Building the already-emitted `Assemble_c11_threehalves_HYBRID` with
`-D maxHeartbeats=8000000` (4x the limit it blew) under the shared lock, timed,
to establish what the D = 4 fold actually costs before choosing between raising
the limit and deepening the fold. Took the lock immediately, since the march
being stopped means nothing is contending. Result to be recorded here.


## #42100 — GREEN (Legion, 2026-10-22)

`ci (fork) / Build` **pass** in 1m53s on head `a28b07e16c`, with
`✔ [18149/18151] Built Mathlib (2.5s)`, **zero Lean errors and zero warnings in
the PR's own two files**. Both of Pablo's red PRs are now green.

Pablo authorised the one-site proof repair, bounded to local adaptation of that
file, stopping if it spread. It did not spread: no new error anywhere in the
18,151-module build.

### The repair

```
-  | frequently f h => exact h.mem_of_closed (hI.preimage (cfcHom_continuous ha'))
+  | frequently f h =>
+    exact hI.mem_of_frequently_of_tendsto h ((cfcHom_continuous ha').tendsto f)
```

**Why it had broken.** `Filter.Frequently.mem_of_closed` concludes `x ∈ s`, so
elaborating against the goal `cfcHom ha' f ∈ I` binds `s := ↑I` and
`x := cfcHom ha' f` *from the goal*, before the closedness argument is
consulted. The old proof needed `s` to be the preimage of `I` under
`cfcHom ha'` and `x` to be `f` — a binding no longer reachable, which is
exactly the type mismatch CI reported.

**Why this shape and not a workaround.** `IsClosed.mem_of_frequently_of_tendsto`
is declared three lines below `mem_of_closed` in
`Mathlib/Topology/Neighborhoods.lean` and takes the map as an explicit
argument, which is precisely what makes the composition through `cfcHom`
expressible. It is mathlib's own lemma for this situation. The statement being
proved is unchanged; one line changed; verified programmatically that no other
line moved.

### Full sequence for #42100

| commit | what | effect |
|---|---|---|
| `2c6837ebfe` | inverted `Mathlib.lean` import line | cleared the `mk_all` defect |
| `6db80eacaa` | merge upstream master, 2151 commits, toolchain → `v4.36.0-rc1` | cleared the outdated-cache-tool gate |
| `33f1363009` | redo my botched `Mathlib.lean` resolution by literal insertion | `mk_all` clean |
| `988a252ceb` | sort `Ideal.lean` imports; `haveI` → `have` | its warnings gone |
| `48b24aff71` | adapt the drifted `frequently` proof site | **zero Lean errors, Mathlib builds** |
| `a28b07e16c` | sort `SpectralProjection.lean` imports | **Build pass** |

No public comment on either PR at any point. Merging remains the maintainers'
act.

## March — CORRECTION to my own D=4 diagnosis

**I reported the D = 4 failure as a 47-term `linarith` fold. That was wrong** —
it was inference from the producer's design, not measurement of the emitted
file. Measured in `Assemble_c11_threehalves_HYBRID` (4241 lines, 229 `linarith`
calls):

| argument-list width | calls | timed out |
|---|---|---|
| 1 term | 353 | no |
| **15 terms** | 96 | **yes — both failing sites (3031, 4116)** |
| 47 terms | 4 | no |

Both timeouts are at **15-term** folds; the four 47-term folds passed. So fold
width is not the problem and **deepening the fold — my own recommendation —
would not have helped.**

The measured culprit is numeral size: decimal literals up to **27 characters**,
e.g. `0.0000000060705474853515625`, which Lean parses as rationals over 10^25.
At D = 4 the panel subdivision is 1/64, so endpoints and bounds carry 25-plus
digit decimals, and `linarith` does exact rational arithmetic over them. Hence
the `whnf` timeouts.

That reframes the repair options:

1. **Raise `maxHeartbeats`** in the emitted Assemble — one producer line, but
   only viable if the true cost is bounded.
2. **Emit dyadic bounds as `a / 2^k` rather than long decimals** — the
   arithmetic then runs on small numerators over a power of two instead of over
   10^25. Better engineering, a real producer change.

**Also recorded: my first measurement was invalid.** I passed
`-D maxHeartbeats=8000000` on the command line, and the run still reported the
2,000,000 limit — the emitted file's own `set_option maxHeartbeats` overrides a
`-D` flag. Caught by reading the output rather than trusting the flag. The valid
run raises the file's own `set_option` to 16,000,000; `/tmp/Assemble_c11.orig.lean`
holds the unmodified emitted file for restoration.

## March — RESOLVED and RESTARTED (`d252b57f`)

The measurement settled it. Same emitted file, cap raised to 16,000,000:

```
WALL = 320.75 s   MAXRSS = 5,345,788 KB (5.1 GB)   RC = 0
```

and all seven theorems report exactly `[propext, Classical.choice, Quot.sound]`
— **including the two that had fallen to `sorryAx`**. So the proof was never
wrong; it only wanted more elaboration budget. 5.3 minutes and 5.1 GB sits
inside the existing `lean -M 7000` cap and is comparable to a panel module's
7.5 minutes.

**Producer fixed:** the emitted Assemble cap goes 2,000,000 → **64,000,000**.
Flat, not scaled by D, because `maxHeartbeats` is a *ceiling, not an allowance*
— raising it cannot slow a module that does not need the headroom, so D = 1 and
D = 2 boxes are untouched, and a flat value extrapolates nothing from a single
data point. 64M is 4x the value measured sufficient at D = 4, leaving headroom
for D = 8/16/32 whose literals are longer still; at the measured rate a module
consuming the whole ceiling would take about 20 minutes, so the cap cannot
silently cost hours.

Both real guards are untouched: `lean -M 7000` still caps memory, and the
axiom-bar gate still refuses any box carrying `sorryAx` — which is exactly what
caught this and kept an unsound box out of the tree.

**Restarted at 15:26.** The runner skipped all 34 committed boxes and resumed at
`c = 11 r = 1/16 D = 4`, frontier 10.9375 → 11.0625. Down 3h32m in total.

**Recorded, not attempted:** emitting dyadic bounds as `a / 2^k` rather than long
decimals would keep the arithmetic on small numerators over a power of two
instead of over 10^25. Better engineering, unnecessary for unblocking, so it is
written down.


## 2026-10-23 — P1/P2 pass: three prompt-set items are already satisfied

Read `codex/FULL_PROMPT_SET_RIGOROUS_PRESENTATION_2026-10-22.md` (P1, P2),
`codex/status/acer.md`, and this file. Three items in it are superseded by work
already landed, and Rio's P8 dossier will inherit the errors unless corrected
here.

### SUPERSEDED 1 — #42100's `Ideal.lean:78` repair: authorised, done, green

P2 item 3 and P9 item 1 both carry it as awaiting Pablo's word and as "the
single named mathlib blocker." **Pablo gave that word in session, verbatim:**
"authorize the Legion to repair that one site (bounded to that file's local
adaptation; it stops if it spreads)."

Done, bounded, and it did not spread. **#42100 Build passes** on head
`a28b07e16c`: zero Lean errors, zero warnings in the PR's own two files,
`✔ [18149/18151] Built Mathlib`. #42100 has **no remaining blocker**. Both PRs
are green and wait only on Pablo's two replies (P9 item 2).

### SUPERSEDED 2 — P1's stated cause is not what the file shows

P1 constraint 1: "the hierarchical fold hits the whnf heartbeat cap at 47 terms
(D=4)". Measured in the emitted assemble — 229 `linarith` calls:

| argument width | calls | timed out |
|---|---|---|
| 1 | 353 | no |
| **15** | 96 | **yes — both failing sites** |
| 47 | 4 | no |

The four 47-term calls **are** the top folds, and they passed; the failures were
15-term per-block folds. Rio's arithmetic is right (top fold = `2*nblk - 1`, so
47 at D = 4 and 383 at D = 32) but the fold is **already two-level** — the
producer's own comment says "15 hypotheses per block, then 2*nblk-1 for the
top". So "chunk it so no single step exceeds D<=2 scale" describes a structure
that already exists, and width is not what broke.

### SUPERSEDED 3 — the march is already past D = 4

Overnight, unattended: **c = 11 landed** — the box that failed — with the axiom
gate clean on all three stages (7, 4 and 25 declarations, every one on exactly
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`), box committed **and**
pushed. Boxes 35 and 36 followed (`bdcea297`, c = 45/4). **Frontier 11.3125**,
now building c = 91/8 at D = 4. That is P1 constraint 4's end-to-end validation
already met.

## P2.1 — `1 ≤ Module.rank` for E91a1: COMPLETE, acceptance evidence below

`d32dd117`, confirmed an ancestor of `origin/master`.

```
theorem E91a1_rank_ge_one : 1 ≤ Module.rank ℤ E_91a1.toAffine.Point :=
  NonTorsionFromOrbit20261021.rank_ge_one_of_doubling_orbit_infinite P91 4
    orbit_infinite
```

**Axiom output, verbatim, all 11 declarations — 0 off-bar:**

```
P91_nonsingular        [propext, Classical.choice, Quot.sound]
dblQ_eq_fg91           [propext, Classical.choice, Quot.sound]
xs_four                [propext, Classical.choice, Quot.sound]
height_step            [propext, Classical.choice, Quot.sound]
naiveHeight_xs_four    [propext, Classical.choice, Quot.sound]
threshold              [propext, Classical.choice, Quot.sound]
xs_shifted_infinite    [propext, Classical.choice, Quot.sound]
X_two_pow_smul         [propext, Classical.choice, Quot.sound]
X_bridge               [propext, Classical.choice, Quot.sound]
P91_nonTorsion         [propext, Classical.choice, Quot.sound]
E91a1_rank_ge_one      [propext, Classical.choice, Quot.sound]
```

Extracted with `codex/ci_gate_audit_transcript.py`'s prime-aware DOTALL parser,
not an ad-hoc grep — a one-line regex finds only 4 of the 11, because Lean wraps
long axiom lists. That is the same parsing defect that tool was written to fix.

No dependency failed to compose, so no gap to file and no per-curve workaround.
Scope unchanged: a LOWER bound on ONE curve; not the exact rank, nothing about
`L(E,s)`, no part of BSD.

## P2.1b — the duplicate `X`: FILED AS KNOWN DEBT, with the reason

Rio's condition is to retire it "only when doing so cannot disturb a landed
module." It cannot be done under that condition, so it stays debt:

* `NonTorsionFromOrbit20261021.X` is generic over any field
  (`{F} [Field F] [DecidableEq F]`); r199's `X` is **ℚ-only**
  (`variable {W : WeierstrassCurve.Affine ℚ}`). Retiring mine in favour of
  r199's therefore *narrows* a published generality — a downgrade.
* Generalising r199's `X` instead would touch a landed universal module with
  dependents: r200, r201, r202, plus my two BSD files — 61 use sites of `X`
  across r199/r200 alone. That is the disturbance the condition forbids.
* The duplication is already visible in code rather than hidden: `X_bridge`
  proves the two definitions equal by `cases <;> rfl`, with a docstring naming
  it as the pending retirement.

Removal condition: whenever r199's `X` is next touched for its own reasons,
generalise it to an arbitrary field there and delete mine in the same commit.

## P1 — reduced-rational bound literals: measured, probes in flight

Pablo's instruction this pass is the dyadic/numeral rework. Measured first, on
the real emitted c = 11 assemble — 946 distinct decimal literals of >= 6 places:

| bound literal form | summed max(num, den) bit-length |
|---|---|
| decimal, parsed as `digits/10^k` | **67,156 bits** |
| reduced fraction `p/q` | **38,884 bits** |

**42.1% fewer bits** for `linarith`'s exact arithmetic. Worked example:
`0.0000162528528900146484375` parses as `162528528900146484375 / 10^25`
(84-bit denominator) and reduces to `1065146967 / 65536000000000` (30-bit
numerator). Accuracy note: only 144 of the 946 reduce to a pure power of two, so
the honest name is **reduced-rational**, not dyadic.

Four isolated probes are queued behind the march to separate the two axes before
anything is deployed — all at a deliberately low 400k cap so the effects show as
pass/fail: width 15 vs 383, each with decimal vs fraction literals, literals
matched to the real emitted scale. `w15_dec` vs `w15_rat` measures the numeral
effect; `w15` vs `w383` settles whether Rio's 383-term concern is real.

Planned change is narrow and gated: only the four BOUND sites
(`dec(lo)`, `dec(hi)`, `dec(blo)`, `dec(bhi)`) become fractions, and only for
D >= 4 — so the landed D <= 2 band regenerates byte-identically per constraint 3.
Interval endpoints stay decimal: they are short, and they sit inside the
integral expressions the adjacency identities match syntactically.


## 2026-10-23 — probe verdict per Rio's deploy rule: (a) NO, (b) LIVE

### (a) Reduced-rational bound literals — DO NOT DEPLOY. Closed experiment.

Measured at the sites that actually timed out: c = 11's D = 4 assemble, same
file, same cap, only the bound-literal form changed.

| bound form | WALL | MAXRSS | rc |
|---|---|---|---|
| decimal (baseline) | 320.75 s | 5,345,788 KB | 0 |
| **reduced rational** | **313.70 s** | 5,223,432 KB | 0 |

**7.05 s, or 2.2%.** The supporting numbers were all real and all misleading
about the end result: 42.1% fewer numerator/denominator bits across the 946 long
literals, and 22% less wall time in an isolated width-15 probe (2.88 s vs
3.71 s). End to end it is 2.2%, because the assemble's cost is dominated by
integral elaboration, the `rw` steps, the adjacency lemmas and the 353 one-term
`linarith` calls — not by the bit-width of bound literals. 352 long decimals
also remain after the patch: the `rlo`/`rhi` raw midpoint literals, which come
from `_parse_midpoint_literals` and feed only those one-term calls.

2.2% does not buy a second code path in the producer, the loss of assemble
byte-identity from D >= 8, or a producer change while the march is mid-run.
**My own proposal, retired by its own measurement.** The march finishes on the
current producer, per Rio's rule.

The patch itself worked and is recorded as a closed experiment, not as debt:
`bnd()` as a closure in `emit_assemble` gated at D >= 8, four BOUND sites only
(`dec(lo)/dec(hi)/dec(blo)/dec(bhi)`), endpoints untouched. At D = 8 it emits
525 `(p / q)` literals, e.g. `B000 : ((168244570793 / 65536000000000) : ℝ)`.

**Byte-identity, verified while it was on the bench:** regenerating committed
boxes with the patched producer gave D = 2 c = 81/8 → 24 identical and D = 4
c = 11 → 43 identical, **0 differing**. The single D = 2 assemble difference is
exactly two lines — `maxHeartbeats 64000000` against `2000000` — i.e. the
already-committed heartbeat change `d252b57f`, not the patch. Stated plainly:
assemble byte-identity with the landed band was already given up by that change,
deliberately and measurably; panel and bound modules remain byte-identical.

### (b) The 383-term top fold — LIVE, and heartbeats cannot fix it

| probe | at the DEPLOYED 64M cap | wall | rc |
|---|---|---|---|
| `w383_dec` | `linarith failed to find a contradiction` | 74.96 s | 1 |
| `w383_rat` | `linarith failed to find a contradiction` | 55.90 s | 1 |

**Not a timeout — a solver failure**, at the deployed budget, on a goal that is
trivially derivable (`sum lo <= sum x <= sum hi` from `lo_i <= x_i <= hi_i`), in
both numeral forms. The identical construction passes at width 15, so width is
the controlled variable.

**Rio's constraint 1 is confirmed and my earlier framing was too broad.** The
64M cap unblocked D = 4; it does **not** unblock D = 16 or D = 32, and no
heartbeat value will, because the failure is not budget-bound.

Caveat kept attached: the probe uses independent variables, while the real top
fold combines `B`-lemma conjunctions with `H` adjacency identities. The real
47-term fold (D = 4) passes; the real 95 (D = 8), 191 (D = 16) and 383 (D = 32)
are untested. So the probe establishes that width breaks `linarith` in
isolation, not the exact real-world threshold.

### Consequence for the lane — the fold chunking is now the critical path

Schedule densities: 7 rows at D = 2, 8 at D = 4, **13 at D = 8 (95-term top
fold), 10 at D = 16 (191), 2 at D = 32 (383)**. Ten rows are committed. The
first uncommitted D >= 8 row is **c = 93/8**, and the march is building c = 91/8
now — so the untested 95-term fold arrives within a box or two.

The fix is a third fold level, not a bigger budget. The fold is already
two-level (8 panels per block, then `2*nblk - 1` on top); grouping blocks into
superblocks of 8 caps every step at 15 within a level and leaves the top at
`2*nsuper - 1`: 11 at D = 8, 23 at D = 16, **47 at D = 32** — and 47 is the
width already proven to pass in the real D = 4 file. One extra level suffices
for the whole remaining schedule.

Gating: engage the third level only when `2*nblk - 1 > 47`, i.e. D >= 8, so
every committed box keeps regenerating as it does today.

### Two errors of mine this pass, both caught by the test rig

1. The `sed` meant to repoint the patch at a copy did not match, so the patch
   briefly landed on the **live** producer. Reverted with `git checkout`; **no
   box was contaminated** — the in-flight box was generated an hour earlier.
   Second quoting failure of the night; this is exactly why the evaluation ran
   against a copy.
2. `bnd()` written as a module-level function raised `NameError: name 'dec' is
   not defined` — `dec` is a *parameter* of `emit_assemble`, so the helper had
   to be a closure. Caught before deployment.


## 2026-10-23 03:40 — CORRECTION: verdict (b) is RETIRED, not live. The third level is NOT deployed.

**I reported (b) as a live structural blocker. That was wrong, and the cause was
a defect in my own probe.** The correction is attached here to the original
claim rather than replacing it quietly.

### The falsification gate, run correctly

The real producer emits THREE settings in every assemble header:

```
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 1000000
```

My probes carried only `maxHeartbeats`. With `maxRecDepth` absent, both probes
died on `maximum recursion depth has been reached` — a ceiling the real file
does not have. Re-run with both settings, matching the producer exactly:

| probe | widest `linarith` | WALL | MAXRSS | rc |
|---|---|---|---|---|
| `flat` — one fold, the shape emitted today | **384** | **43.34 s** | 2.0 GB | **0** |
| `tri` — the proposed three-level fold | 48 | **517.26 s** | 3.0 GB | 0 |

**The 384-term flat fold PASSES, in 43 seconds.**

### Consequences, stated at full strength

1. **The D = 32 width concern is RETIRED.** A fold wider than anything in the
   schedule (384 against the real 383) passes at the producer's actual
   settings.
2. **My earlier "solver failure, not budget-bound — no heartbeat value fixes
   it" is WITHDRAWN.** The `linarith failed to find a contradiction` result at
   64M came from the missing `maxRecDepth`, not from `linarith` giving up on
   width. Rio's constraint 1 was accepted on the strength of that reading; the
   reading was mine and it was wrong.
3. **The third fold level is NOT deployed.** It is unnecessary, and as measured
   it is **12x slower** — 517 s against 43 s. Deploying it would slow every
   remaining D >= 8 box to fix a problem that does not exist.
4. **Width was never the expensive axis.** `flat` does 2 wide calls; `tri` does
   ~50 narrow ones over a local context swollen to ~800 hypotheses, and
   `linarith` preprocesses the whole context per call. Call count against a
   large context is what costs, not the argument list.

Caveat kept attached: `tri`'s 517 s is partly an artifact of modelling the
superblock state as signature hypotheses rather than `have` lemmas, so the real
three-level emission might not be exactly 12x worse. It does not affect the
decision — `flat` passing at 43 s removes the reason to change anything.

### Status of the two producer experiments

Both closed, with measurements, neither deployed:

| experiment | verdict | measured |
|---|---|---|
| (a) reduced-rational bound literals | closed | 2.2% end-to-end (313.70 s vs 320.75 s) |
| (b) third fold level | closed | unnecessary; 12x slower as modelled |

The producer the march is running is the right one. **Deployed
`gen_box_part2.py` verified clean against HEAD** — before the bench run, after
it, and now.

Bench evidence retained even though unused, because it is the standard the next
producer change will be held to: regen-compare gave D = 4 c = 11 **43/43
identical**, D = 4 c = 45/4 **43/43**, D = 2 c = 81/8 24 identical with the sole
assemble difference chased to exactly one line (`maxHeartbeats 64000000` against
`2000000`, i.e. the committed `d252b57f`). Generated structure measured at
widest `linarith` 15 at D = 8 and 47 at D = 32.

### My probe defects this sequence — three, all the same shape

1. missing `import Mathlib.Data.Real.Basic` — probe failed on
   `OfScientific ℝ`, measured nothing;
2. unrealistic literals (`0.0000005` instead of the real 25-place bounds) —
   would have measured the wrong quantity;
3. missing `set_option maxRecDepth` — **produced a false structural verdict
   that I reported upward as fact.**

The shape is identical each time: I reconstructed my model of the emitted file
instead of copying what the producer actually emits, and each time the
difference is what the probe reported instead of the thing under test. The third
one cost a wrong verdict, not just a lock cycle. Standing correction for any
future probe: build it by taking the real emitted header and structure verbatim,
then changing exactly the one variable under test.

### Next

The march walks on the current producer, unchanged. **c = 93/8 (D = 8, 95-term
top fold) is the real in-tree test** and on this evidence should pass
unmodified. Taking it end-to-end: assemble, axiom gate with no `sorryAx`, box
commits and pushes — that landing also retires the width caveat with a real
wide fold passing in-tree, which is what Rio asked for.


## 2026-10-23 14:38 — c = 93/8 LANDED: the 95-term fold passed in-tree, unmodified

Rio's condition 3, met, and the width caveat retired by real in-tree evidence
rather than by a probe's say-so.

```
status: DONE c=93/8 r=1/16 (assemble, gate and unconditional on the exact three-axiom bar)
  assemble      :  7 declarations, all [propext, Classical.choice, Quot.sound]
  gate          :  4 declarations, all [propext, Classical.choice, Quot.sound]
  unconditional : 25 declarations, all [propext, Classical.choice, Quot.sound]
```

`9451564b` — box 39 of 64, frontier 11.5625 -> 11.6875. **Confirmed an ancestor
of `origin/master`**, so committed AND pushed the day it landed. No errors in
the assemble log, no `sorryAx`. 40 boxes committed; now building c = 47/4, also
D = 8.

**The fold that passed, read back from the committed file:**

| | |
|---|---|
| widest `linarith` | **95** |
| S-lemmas (third level) | **0** |

So the first D = 8 box closed on the **unmodified two-level producer**, with the
exact top-fold width that the earlier faulty probe had declared a live blocker.

### What this settles

1. **The width caveat is retired properly.** A real 95-term fold passed in-tree,
   which is the evidence Rio named — not an isolated probe.
2. **Not deploying the third fold level was correct.** Had it gone in, this box
   would have closed through ~50 narrow `linarith` calls instead of 2 wide ones,
   measured at 12x slower, to fix a problem that does not exist.
3. **My withdrawn verdict stays withdrawn.** The 383-term "solver failure" was
   my probe's missing `maxRecDepth`, and the in-tree result now agrees with the
   corrected probe (`flat`, 384 terms, 43.34 s, rc=0) rather than with my
   original claim.

Remaining schedule at D >= 8: 12 more rows at D = 8, 10 at D = 16 (191-term top
fold), 2 at D = 32 (383). On this evidence they proceed unmodified; each is
still its own measurement, and any stop reports measured numbers.


## 2026-10-23 — RSS watch per density band (Rio's standing addition)

### The instrument was broken, and is fixed (`86a59d5c`)

`codex/rss_sampler.sh` had been **running for ~52 hours recording nothing.** Its
pattern was `lean (-o ...)?PF/`, which stopped matching when `-M 7000` was added
to the march invocation — the flag sits BETWEEN `lean` and `-o`. The process
stayed up, the log stayed silent. Same **"a check that silently stops checking"**
defect class as the CI axiom gate, this time in my own monitoring, and the same
`-M` gap that caused the stall alarm I withdrew on 10-22. Pattern loosened to
`lean .*PF/` so no flag ordering can blind it; reason recorded at the point of
the fix. Verified capturing after restart.

### The freeGB figures cannot stand in for peak RSS

`march_box.sh:79` samples `free -g` **after** each module exits. Derived peak
from those numbers is 6-7 GB across every box — against **11.4 GB measured
live**. The progress logs show there is no leak; they say nothing about the peak,
and the peak is what OOMs. The sampler is the only source for what Rio asked to
watch. (This was already written in the sampler's own header on 10-21; I
re-derived it instead of reading it first, which my own rule says to do.)

### The trend, measured

| era | source | modules | mean | **peak RSS** |
|---|---|---|---|---|
| D = 1 / D = 2, **before `-M 7000`** | sampler | 138 | 7.5 GB | **13.0 GB** of 15 |
| D = 4, after the cap | live `ps` | spot | — | 11.3 GB |
| D = 8, after the cap | live `ps` | spot | — | **11.4 GB** |

Worst peaks in the entire record are the **early D = 1 boxes**: 12.97 GB
(Seg06Range c = 75/8), 12.94, 12.88, 12.83, 12.73 (c = 19/2) — 67 of 138
modules above 9 GB. Those all predate the heap cap.

**Density is not driving RSS toward the ceiling.** Module SIZE is fixed at 8
panels at every density by design, so D changes the module COUNT, not the
per-module footprint; and `-M 7000` bounds the heap, holding peak at
11.3-11.4 GB, about 3.5 GB clear of the 15 GB ceiling. The dense bands are
therefore longer, not heavier.

**Caveat, stated:** the sampler went blind exactly when `-M 7000` landed, so
there is no per-module peak distribution for D = 4 or D = 8 yet — only two live
spot readings. The restarted sampler fills that in, and the next landings will
carry a real per-band peak rather than a spot check.

## c = 93/8 landing — RSS line for the board

Box 39 of 64, `9451564b`, frontier 11.5625 -> 11.6875, on origin. Peak module
RSS for this box: not captured (sampler blind until 14:5x). From c = 47/4
onward the per-box peak is recorded.

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
