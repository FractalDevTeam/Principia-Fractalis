# The density ladder to 13 is priced at **232 h serial (9.7 days)** — 0.61× of the ~6 h × boxes estimate, so the cost gate passes. But three generator prerequisites block Step 2, and the hard one is the assemble's flat `linarith`: 95 hypotheses today, **1535 at D = 16**.

**Date:** 2026-10-20 (Legion). Computed with the shipped interval arithmetic and
the producer's own `Mc_lb` formula at parametric density — no model.
Scripts: `codex/price_density.py`, `_opt.py`, `_perseg.py`, `_ladder.py`.
Labels **FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**.

---

## HEADLINE

Rio's gate question — *"if the total differs wildly from ~6 h × boxes, say so
before building anything"* — **answers NO on cost**:

| schedule | boxes | panel modules | serial hours |
|---|---|---|---|
| ~6 h × boxes (Rio's estimate) | 64 | — | 384 |
| all-midpoint, optimal | 65 | 2574 | 322 (13.4 days) |
| **per-segment, optimal** | **64** | **1860** | **232 (9.7 days)** |

**Per-segment dominates on both axes** — 28% cheaper to build *and* needing
less new machinery, because it never puts midpoint on segments 5-6 and so never
needs the Tier-C `M` bound that all-midpoint does. It is the schedule to build.

But the cost model prices *panel* modules, and there is a cost it does not see.
The assemble step folds every panel in the box through a **single flat
`linarith`** (`gen_box_part2.py:189-194`): `len(panels)` bound terms plus
`len(panels) − 1` adjacency equations, i.e. **`96D − 1` hypotheses**.

| D | panels/box | hypotheses per `linarith` |
|---|---|---|
| 1 (landed, `c5458211`) | 48 | **95** |
| 4 | 192 | 383 |
| 8 | 384 | 767 |
| 16 | 768 | **1535** |

`linarith` is a simplex over the hypothesis set; this is superlinear in the
count. **The D = 16 band is 84 h of the 232 h total and would be built on a
`linarith` carrying sixteen times the hypotheses that has ever been run.** That
must be refolded before a single dense box is attempted, not discovered at
hour 200.

---

## 1. The ladder. MEASURED

Walk from the landed coverage edge, radii `{1/16, 1/32, 1/64}`, densities
`{1,2,4,8,16,32}`, scheme chosen per segment, cost minimised per unit advance.
`scheme` reads segments 1→6, `m` = midpoint, `r` = range-brick.

| centre band | D | scheme | modules/box | h/box | boxes | r used | subtotal |
|---|---|---|---|---|---|---|---|
| 6.8750 – 10.0000 | 1 | `mmmrrr` | 6 | 0.75 | 26 | 1/16 | 19.5 h |
| 10.1250 – 11.0000 | 2 | `mmmrrr` | 12 | 1.50 | 8 | 1/16 | 12.0 h |
| 11.1250 – 12.0312 | 4 | `mmmrrr` | 24 | 3.00 | 7 | 1/16, 1/32 | 21.0 h |
| 11.7500 – 12.8281 | 8 | `mmmmrr` | 48 | 6.00 | 16 | 1/16, 1/32, 1/64 | **96.0 h** |
| 12.5312 – 12.9844 | 16 | `mmmmrr` | 96 | 12.00 | 7 | 1/32, 1/64 | **84.0 h** |
| **total** | | | **1860** | | **64** | | **232.5 h** |

(Bands overlap because the optimiser sometimes buys a larger `r` at a higher
`D`; the ladder is in cost, not strictly in `c`. Where the rungs begin:
D = 2 at c = 10.125, D = 4 at 11.125, D = 8 at 11.750, D = 16 at 12.531.)

**The first 26 boxes — the whole stretch to c = 10 — are at D = 1 and need no
new machinery.** The producer builds them today; the per-segment optimum there
differs from the shipped hybrid only in segment 3 (a 1.6% near-tie: measured
`Mc_lb(6.875) = 0.14722119` per-segment against the producer's own
`0.14684818` hybrid, 0.25% apart). So the march can start while the three
prerequisites are built.

For reference, the all-midpoint optimum (Dijkstra, radii to 1/256, densities to
64) is **65 boxes, 2574 modules, 321.8 h**, with bands D = 1 (19 boxes, 14.2 h),
2 (11, 16.5 h), 4 (9, 27 h), 8 (10, 60 h), 16 (15, 180 h), 32 (1, 24 h).

`Mc_lb(13)` as a function of density, the quantity that decides the top:

| D | 1 | 2 | 4 | 8 | 16 | 32 | 64 | ∞ |
|---|---|---|---|---|---|---|---|---|
| `Mc_lb(13)` | −0.1503 | −0.0358 | −0.0071 | +0.000038 | **+0.00183** | +0.00228 | +0.00239 | **+0.002425** |

Threshold at `r = 1/64` with the 1.25× safety: **0.0018761**. So D = 16 is the
first rung that clears it, D = 8 misses by 50×, and the `D → ∞` ceiling is only
1.3× above D = 16 — **density is nearly exhausted at 16**; there is no rung that
buys real headroom beyond it.

## 2. Two corrections to my own numbers in `RSCHED_MCLB_IS_THE_CEILING`. MEASURED

**(a) The tightening requirement was understated 4.7×.** I wrote
"`169·δ_R + 13·δ_I < 0.003518` against the current `0.077800` — a 22.1×
tightening". The `0.077800` used the enclosure half-width measured **at
c = 55/8** and applied it at c = 13; the width grows 1.47× over that span. The
measured gate cost of the shipped hybrid at c = 13 is **0.11449**, and the real
target (`r = 1/64`, 1.25× safety) is **< 0.0010978**. The requirement is
therefore **104×**, not 22.1×.

**(b) "≈ 6.7× more midpoint panels, ~6 h per box" was wrong; it is D = 16, 96
modules, 12 h per box.** Three things the 6.7× missed:

* the all-midpoint scheme is **4.0× worse** than the hybrid at D = 1 at c = 13
  (measured `3.0376e−1` vs `1.1449e−1`), because `M` is Tier C on segments 5-6;
* `D` is confined to **powers of 2** — `err = M/(2^18·3·D^3)` must be a
  terminating decimal for the emitted literal (`gen_box.dec`) and the panel
  endpoints must stay dyadic, so 9.35× rounds up to 16;
* the realised tightening is `1.1449e−1 → 6.6190e−4` = **173×** at D = 16,
  against 46× at D = 8 — the first rung that clears 104×.

## 3. The scheme is a ladder too, not just the density. MEASURED — new

The midpoint/range crossover **walks outward through the segments as `D` rises**,
because midpoint error falls as `1/D²` and range-brick as `1/D`. Per-segment
gate cost (`c²·excess_R + c·excess_I`) at c = 13:

| D | all-range | all-midpoint | **per-segment best** | best scheme |
|---|---|---|---|---|
| 1 | 4.2098e−1 | 3.0376e−1 | **1.1449e−1** | segs 1-2 mid, 3-6 rng |
| 4 | 1.0577e−1 | 1.8985e−2 | **9.3404e−3** | segs 1-4 mid, 5-6 rng |
| 16 | 2.6479e−2 | 1.1866e−3 | **6.6190e−4** | segs 1-4 mid, 5-6 rng |

At D = 1 and c = 13 the per-segment optimum **is** the shipped hybrid exactly
(segs 1-2 midpoint, 3-6 range) — an independent confirmation of the `14bc4b7c`
segment choice, now at c = 13 rather than 27/4. Lower down, segment 3 flips to
midpoint (`mmmrrr`), but by 1.6% — a near-tie, worth 0.25% of `Mc_lb`. And the
choice is not cosmetic at the top:

| at c = 13, r = 1/64, D = 16 | `Mc_lb` | vs threshold 0.0018761 |
|---|---|---|
| all-midpoint | +0.00183169 | **FAIL** |
| per-segment (1-4 mid, 5-6 rng) | **+0.00209403** | **PASS 1.12×** |

**JUDGEMENT.** Step 2 must use the per-segment scheme. All-midpoint at D = 16
does not reach 13, and raising to D = 32 to compensate would double the most
expensive band to buy what the scheme choice gives free. Priced end to end the
per-segment schedule is **232 h against all-midpoint's 322 h** (§1) — and it
needs *less* new machinery, since it never puts midpoint on segments 5-6 and so
never needs the Tier-C `M` bound.

## 4. 62 of the 64 boxes are geometry, not density. MEASURED

Re-running the optimiser at **perfect enclosure** (`Terr = 0`, D → ∞):

* **62 boxes minimum** — radii `{1/16: 42, 1/32: 10, 1/64: 10}`.
* Actual ladders: 64 boxes (per-segment), 65 (all-midpoint).

So **only 2 of the 64 boxes exist because the enclosure is imperfect.** The box
count is set by `L₀(c−r)·r < Mc_lb(c) ≤ Re ξ(1+ic)` with `Re ξ → 0` at
13.98838, which caps `r ≤ Re ξ(c)/L₀(c) ≈ 0.026` near the top no matter how
good the panels are. **Density does not buy fewer boxes; it buys boxes above
c ≈ 10.28 existing at all.** The per-box module count is the whole variable.

## 5. What blocks Step 2. FACT — all three verified in the source

1. **Density is not parametric.** `gen_box.py:96-97` has `PANEL_WIDTH = F(1,32)`
   and `N_PANELS = 8` as module constants, and `m_data` (line 174) asserts
   `F(M, 786432) == F(M)·PANEL_WIDTH³/24` — 786432 = 24·32³ hardcoded.
2. **Midpoint is Tier-A only.** `gen_box.py:98`: `MID_SEGS = (1, 2)
   # midpoint tier: T <= 1/2`. `termM_coarse` hardcodes `E_UB = 2`, `T_UB = 2`,
   valid only for `T ≤ log 2`. The per-segment optimum uses segment 3 on
   midpoint throughout and segment 4 from D = 8 — both **Tier B** (`T ≤ 1`:
   `E ≤ 2`, `expT ≤ 3`), which needs tier-aware `termM_coarse` **and** the
   matching Lean `M_sum_le` lemma at that tier. It never needs Tier C, which
   all-midpoint would.
3. **The assemble's flat `linarith`** — `gen_box_part2.py:189-194`, 95 → 1535
   hypotheses as tabulated above. The adjacency chain is cumulative
   (`∫₀^x = ∫₀^y + ∫_y^x`) and therefore associative, so the fix is a
   hierarchical fold: prove one bound per 8-panel module, then combine the `6D`
   module bounds — `6D` small `linarith`s of ~16 hypotheses plus one of ~12D.

**JUDGEMENT.** (3) is the one that can waste the whole march, and it is the
cheapest of the three to fix. Order: (3), then (1), then (2).

## 6. How density should be realised: split segments, don't fatten modules. JUDGEMENT

Peak RSS is **7.6 GB of 15** on a module of 8 panels, so an 8x-denser single
module would not fit and the march would die on memory rather than time. The
design that keeps the measured per-module cost fixed is to hold `N_PANELS = 8`
and **split each segment into `D` sub-segments**:

* segment `s` = `[(s-1)/4, s/4]` becomes `D` sub-segments of width `1/(4D)`,
  each emitted as its own module with 8 panels of width `h = 1/(32D)`;
* `6D` modules per box, each the same size and the same ~7m30s / 7.6 GB as
  today's;
* the 8-panel block of the hierarchical fold (above) is then exactly one source
  module, which is why the fold's blocks were cut at 8.

Concretely, prerequisite (1) is: `PANEL_WIDTH -> F(1, 32*D)`, `m_data`'s
hardcoded `786432 = 24*32^3 -> 24*(32*D)^3`, a sub-segment index in the module
names, and the same two constants in `gen_box_part2.py`. Prerequisite (2) then
falls out: a sub-segment of segment 3 has `T <= 3/4`, so it is **Tier B**, and
`termM_coarse` needs the tier constants it currently hardcodes at Tier A.

**This is also why `D` must be a power of two** beyond the decimal-literal
argument: sub-segment endpoints `(s-1)/4 + j/(4D)` and panel endpoints must
stay dyadic for `dec()` to terminate on all of them.

## 7. Validation of the method. MEASURED

The pricing never models the enclosure; it computes the producer's own
`R_ub`/`I_ub` at parametric density, split as

`R_ub(c,D) = Σ_seg Σ_k h·U_node(m_k) + Σ_seg 8D·(M_seg h³/24)/2`, `h = 1/(32D)`

the second term in closed form, the first converging to the true integral.

* **The midpoint enclosure is pure truncation error, so the `1/D²` scaling is
  exact, not assumed.** Node bounds are outward-rounded to 10 digits (~1e−10)
  while `err = M h³/24` is ~1e−5 per panel. Checked against the shipped widths:
  seg 1-2 `M = 24 → 24/98304 = 2.4414e−4`; seg 3-4 `30 → 3.0518e−4`;
  seg 5-6 `72 → 7.3242e−4` — all three reproduce the measured table exactly.
  *(This was the first thing checked: 2.4414e−4 = 2⁻¹² and 7.3242e−4 = 3·2⁻¹²
  look like a rounding floor, and had they been one, density would buy nothing
  and the whole march would be dead. They are not.)*
* **Node sum vs mpmath at c = 27/4, D = 1:** interval `R = 0.014564272426`,
  true `R = 0.014574454632`; the node sum sits `−1.02e−5` *below* the true
  value while `Terr = 1.19e−3` dominates it by 117×. So substituting
  `R_true + Terr` for `Σh·U + Terr` is **conservative** by 1.02e−5 at D = 1 and
  4e−8 by D = 16 — it understates `Mc_lb`, never overstates it.
* **Against the producer's measured hybrid `Mc_lb`** (`mclb_scan.txt`):

  | c | all-mid D=1 | all-mid D=2 | hybrid (producer) |
  |---|---|---|---|
  | 55/8 | 0.12561362 | 0.14977764 | 0.14684818 |
  | 8 | 0.05574903 | 0.09035596 | 0.08528181 |
  | 10 | −0.04212128 | 0.01704467 | 0.00751429 |
  | 21/2 | −0.06166643 | 0.00466353 | −0.00538046 |

  All-midpoint straddles the hybrid between D = 1 and D = 2, as the 2.8×
  D = 1 penalty and the `1/D²` scaling require.

---

## Label summary

* **FACT:** the three Step-2 blockers, each read off the producer source with
  line numbers; the `96D − 1` hypothesis count; that `Mc_lb` is independent of
  `r`; that `D` must be a power of two for the emitted literals to terminate.
* **MEASURED:** the 65-box / 2574-module / 321.8 h optimal ladder and its six
  density bands; `Mc_lb(13)` at eight densities including the `D → ∞` ceiling
  +0.002425; the 62-box geometry floor; the three-scheme × three-density gate
  cost table at c = 13; the PASS/FAIL split between all-midpoint and
  per-segment at c = 13, r = 1/64, D = 16; the corrected 104× requirement and
  0.11449 hybrid gate cost at c = 13; all three validation checks in §6.
* **JUDGEMENT:** that the assemble fold must be fixed first and is the cheapest
  of the three; that Step 2 must use the per-segment scheme rather than
  all-midpoint; that density is nearly exhausted at D = 16 (the `D → ∞` ceiling
  is only 1.3× above it), so there is no density answer to a further push past
  13.
* **OPEN / NOT established:** the per-segment ladder in §1 is a greedy
  (min cost per unit advance), not a Dijkstra optimum — only the all-midpoint
  schedule was solved exactly — so 232 h is an upper bound on the per-segment
  cost, not necessarily its minimum. The 7.5 min /
  7.6 GB per 8-panel module is the measured D = 1 figure carried forward on the
  assumption that 8 panels per module keeps per-module cost constant as the
  module *count* grows; that is the design intent (it is what holds RSS under
  the 15 GB box) but it has not been measured at D > 1. No Lean has been built
  at any density above 1.
