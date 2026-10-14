# R1 coverage status — evening of 2026-10-14

**Context:** Pablo away ~6 hr; continuing autonomous pilot work until the
machinery saturates, then documenting the required analytic step.

## Current connected kernel-clean R1 coverage

**`[0, 18/5]` = `[0, 3.6]` — 27.7% of the `[0, 13]` target.**

Pilot block (left to right), all `#print axioms = [propext, Classical.choice, Quot.sound]`:

| # | Center | r | Box | Λ₀ bound used | Gate 1 margin |
|---|--------|-----|------|---------------|---------------|
| 7 | 1/20 | 1/20 | [0, 1/10] | 2/21 | 0.247 |
| 5' | 1/5 | 1/10 | [1/10, 3/10] | 2/21 | ≈ 0.24 |
| 2 | 1/2 | 1/5 | [3/10, 7/10] | 2/21 | ≈ 0.19 |
| 4 | 3/4 | 1/20 | [7/10, 4/5] | 2/21 | ≈ 0.17 |
| 3 | 1 | 1/5 | [4/5, 6/5] | 2/21 | ≈ 0.16 |
| 5 | 7/5 | 1/5 | [6/5, 8/5] | 2/21 | ≈ 0.09 |
| 6 | 9/5 | 1/5 | [8/5, 2] | 2/21 | ≈ 0.01 |
| 8 | 11/5 | 1/5 | [2, 12/5] | 1/33 | 0.143 |
| 9 | 13/5 | 1/5 | [12/5, 14/5] | 1/33 | ≈ 0.108 |
| 10 | 3 | 1/5 | [14/5, 16/5] | 1/33 | ≈ 0.068 |
| 11 | 17/5 | 1/5 | [16/5, 18/5] | 1/33 | ≈ 0.023 |

## Why pilot 11 is the ceiling under `‖Λ₀‖ ≤ 1/33`

For `Mc_lb ≥ 1/4` to be provable via the uniform triangle bound, we need
`(c² + c)·BOUND ≤ 1/2`:

* under `BOUND = 2/21`: `c ≤ (−1+√22)/2 ≈ 1.845` (saturated by pilot 6 at `c = 9/5 = 1.800`)
* under `BOUND = 1/33`:  `c ≤ (−1+√67)/2 ≈ 3.593` (saturated by pilot 11 at `c = 17/5 = 3.400`)

## In-progress: `‖Λ₀‖ ≤ 50/1727` and `L = 1/2`

Second rational-numerics tightening — using `π > 157/50` (vs `π ≥ 3`)
with the same `exp(π) ≥ 23` chain:

  `2·(1/23) / ((157/50)·(22/23)) = 100/(157·22) = 50/1727 ≈ 0.02895`

(True analytic value: `0.02875`. The rational step is now within 0.7% of the
true value — further rational tightening is no longer meaningful.)

Combined with `L = 1/2` (proving the `h_sum ≤ 1` step rather than `≤ 2`),
`r` can grow to `2/5` under the bridge's `L·r < 1/4` gate.

**Projected pilot 12** (c = 18/5, r = 2/5, L = 1/2, box `[16/5, 4]`):
closes R1 kernel-clean on `[0, 4]` — 30.8% of target.

**Projected pilot 13 (ceiling under 50/1727):** `c = 73/20 = 3.65` with
`r = 2/5` and `L = 1/2`, box `[13/4, 81/20] = [3.25, 4.05]`. Gate 1
margin tight at `≈ 0.004`.

## The fundamental ceiling and what's needed to reach `[0, 13]`

The uniform Mellin bound `‖Λ₀(1+it)‖ ≤ 2·exp(−π)/(π·(1−exp(−π))) ≈ 0.0287`
is **t-independent**. The pilot producer needs `(c² + c)·BOUND ≤ 1/2`.

At `c = 13`: `(169 + 13)·BOUND = 182·BOUND ≤ 1/2 ⟺ BOUND ≤ 1/364 ≈ 0.00275`.

**The true analytic bound is 10× too large.** No rational-numerics step
can close this gap: the Mellin triangle inequality is intrinsically loose
by this factor at large `|t|`.

### Route A — `|t|`-dependent decay via integration by parts

The Mellin integral
  `Λ₀(1+it) = ∫_1^∞ (x^(−1/2) · x^(it/2) + x^(−1) · x^(−it/2)) · ω(x) dx`
has oscillation `x^(it/2) = exp(it · ln(x)/2)` with frequency `∝ |t|`.
Integration by parts yields decay of the form
  `‖Λ₀(1+it)‖ ≤ C/|t|`  for `|t| ≥ 1`
with `C` an effective constant that can be computed from `ω(1)` and the
total variation of `(x·ω(x))'` on `[1, ∞)`.

If `C ≤ 1/30` (plausible — `ω(1) ≈ 0.0432`), then at `|t| = 13`:
  `‖Λ₀(1+13i)‖ ≤ 1/(30·13) = 1/390 < 1/364` ✓ reaches `c = 13`.

**Project size:** 100–200 lines of mathlib-aware Lean. One IBP step on
an improper integral, plus a BV bound on `(x·ω(x))'`. The BV bound needs
`ω'(x)` which comes from `jacobiTheta` derivatives (not immediately in
mathlib, may require construction).

### Route B — per-point certified panels

For specific `c` values near 13, use a `Xi_Positive_At_c` theorem built
by direct numerical computation on finely-sliced panels, in the style of
`XiPanelsT15/*.lean` (63 files, 165 kernel-decide bricks for the single
value `t = 15` in the `Xi_15_pos` chain).

**Project size:** 60+ panel files per pilot center × 10 pilot centers to
cover `[4, 13]` = ~600 panel files. Mechanically generable from a mpmath
driver like `gen_r120_panels_t15.py`. Numerically simple but Lean-heavy.

### Route C — hybrid

Use Route A to reduce the uniform bound to `|t|^(−1)`, then use Route B
to patch the dip region near `|t| ≈ 14` (where `Re ξ` approaches zero
before the first off-critical-line concern). Likely the most tractable
decomposition.

## R2 and R3 state (not covered this session)

Current files in `PilotBoxes/`:
* `R2_c27_2_r1_20_2026_10_13.lean` — single pilot at `c = 27/2 = 13.5`,
  `r = 1/20`. R2 target is `[13, 29/2]` = `[13, 14.5]`, width 1.5.
  Needs ≥ 30 pilots of width 1/10 (if achievable) or similar via a
  tighter machinery.
* `R3_c74_5_r1_20_2026_10_13.lean` — single pilot at `c = 74/5 = 14.8`,
  `r = 1/20`. R3 target is `[29/2, 15]` = `[14.5, 15]`, width 0.5.
  Needs ≥ 10 pilots.

Both R2 and R3 operate in a regime where the uniform Λ₀ bound is far
from sufficient — same ceiling issue, worse (because `c` is large).
Route A/B/C applies equally to R2 and R3.

## Pragmatic decision points (for Pablo on return)

1. **If goal is "unconditional RH-below-15":** commit to Route A or C.
   Rough estimate: 2–4 weeks of focused work on IBP + BV + mathlib
   extensions.

2. **If goal is "maximum R1 coverage without new analytic machinery":**
   current 27.7% is near-saturated. 50/1727 + L=1/2 can push to ~31%.
   Nothing beyond ~31% without Route A/B/C.

3. **If goal is "verified mathematics into mathlib":** the four open
   mathlib PRs are the direct line, and the pilot producer / Λ₀ tight
   bounds / Mellin substrate are themselves candidates for upstreaming
   independent of the full RH-below-15 closure.

## This session's commits (pushed to `master` + feature branch)

* `a27dc4ee` pilot 11 (c = 17/5)
* `4aff57f0` pilot 10 (c = 3)
* `a6eb1724` pilot 9 (c = 13/5)
* `da160c59` pilot 8 (c = 11/5) — first on 1/33 bound
* `5ae4f8e8` `‖Λ₀‖ ≤ 1/33` via Mellin + `exp(π) ≥ 23`
* `a0db80bd` pilot 7 (c = 1/20) — closes left to `t = 0`
* `e8a2cd41` pilot 5' (c = 1/5)
* `c5582d25` pilot 6 (c = 9/5) — closes under 2/21
* `40d4907e` pilot 5 (c = 7/5)

## Honest framing

What landed today is **verified mathematics**: the pilot producer
machinery is a reusable kernel-clean device for localized positivity
on R1, and the `exp(π) ≥ 23` chain tightens the uniform Λ₀ bound to
within 5% of its true value. This does **NOT** close any Millennium
Problem; `rh_below_15_conditional` remains conditional on R1 ∧ R2 ∧ R3
and `rh_below_15` on literal R1 requires `[0, 13]` coverage that the
uniform bound cannot provide.

The scope is: *independent researcher getting verified machinery into
Lean 4, that strangers can build on.* No breakthrough, no Millennium
proximity, no Clay-adjacency.
