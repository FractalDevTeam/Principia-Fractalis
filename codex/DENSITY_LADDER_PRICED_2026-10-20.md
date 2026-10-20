# The density ladder to 13 is priced at **322 h serial (13.4 days)** — 0.82× of the ~6 h × boxes estimate, so the cost gate passes. But three generator prerequisites block Step 2, and the hard one is the assemble's flat `linarith`: 95 hypotheses today, **1535 at D = 16**.

**Date:** 2026-10-20 (Legion). Computed with the shipped interval arithmetic and
the producer's own `Mc_lb` formula at parametric density — no model.
Scripts: `codex/price_density.py` (`price3`/`price4`/`price5` stages).
Labels **FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**.

---

## HEADLINE

Rio's gate question — *"if the total differs wildly from ~6 h × boxes, say so
before building anything"* — **answers NO on cost**:

| | boxes | panel modules | serial hours |
|---|---|---|---|
| ~6 h × boxes (Rio's estimate) | 65 | — | 390 |
| **measured optimal ladder** | **65** | **2574** | **322 (13.4 days)** |

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
count. **The D = 16 band is 180 h of the 322 h total and would be built on a
`linarith` carrying sixteen times the hypotheses that has ever been run.** That
must be refolded before a single dense box is attempted, not discovered at
hour 300.

---

## 1. The ladder. MEASURED

Dijkstra over the frontier from the landed coverage edge `109/16 = 6.8125`,
minimising serial hours, radii `{1/16 … 1/256}`, densities `{1,2,4,8,16,32,64}`.

| centre band | D | modules/box | h/box | boxes | r used | subtotal |
|---|---|---|---|---|---|---|
| 6.8750 – 9.0156 | 1 | 6 | 0.75 | 19 | 1/16, 1/32, 1/64 | 14.2 h |
| 9.0938 – 10.3438 | 2 | 12 | 1.50 | 11 | 1/16 | 16.5 h |
| 10.4688 – 11.4375 | 4 | 24 | 3.00 | 9 | 1/16, 1/32 | 27.0 h |
| 11.5312 – 12.6094 | 8 | 48 | 6.00 | 10 | 1/16, 1/32, 1/64 | 60.0 h |
| 11.9688 – 12.9844 | 16 | 96 | 12.00 | 15 | 1/16, 1/32, 1/64 | **180.0 h** |
| 12.6562 | 32 | 192 | 24.00 | 1 | 1/32 | 24.0 h |
| **total** | | **2574** | | **65** | | **321.8 h** |

(Bands overlap because the optimiser sometimes buys a larger `r` at a higher
`D`; the ladder is in cost, not strictly in `c`.)

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

At D = 1 the per-segment optimum **is** the shipped hybrid exactly — an
independent confirmation of the `14bc4b7c` segment choice, now at c = 13 rather
than 27/4. And the choice is not cosmetic at the top:

| at c = 13, r = 1/64, D = 16 | `Mc_lb` | vs threshold 0.0018761 |
|---|---|---|
| all-midpoint | +0.00183169 | **FAIL** |
| per-segment (1-4 mid, 5-6 rng) | **+0.00209403** | **PASS 1.12×** |

**JUDGEMENT.** Step 2 must use the per-segment scheme. All-midpoint at D = 16
does not reach 13, and raising to D = 32 to compensate would double the most
expensive band (180 h → 360 h) to buy what the scheme choice gives free.

## 4. 62 of the 65 boxes are geometry, not density. MEASURED

Re-running the optimiser at **perfect enclosure** (`Terr = 0`, D → ∞):

* **62 boxes minimum** — radii `{1/16: 42, 1/32: 10, 1/64: 10}`.
* Actual ladder: 65 boxes.

So **only 3 of the 65 boxes exist because the enclosure is imperfect.** The box
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
   valid only for `T ≤ log 2`. The per-segment optimum needs segments 3-4 on
   midpoint from D = 4 (Tier B: `E ≤ 2`, `expT ≤ 3`), which needs tier-aware
   `termM_coarse` **and** the matching Lean `M_sum_le` lemma per tier.
3. **The assemble's flat `linarith`** — `gen_box_part2.py:189-194`, 95 → 1535
   hypotheses as tabulated above. The adjacency chain is cumulative
   (`∫₀^x = ∫₀^y + ∫_y^x`) and therefore associative, so the fix is a
   hierarchical fold: prove one bound per 8-panel module, then combine the `6D`
   module bounds — `6D` small `linarith`s of ~16 hypotheses plus one of ~12D.

**JUDGEMENT.** (3) is the one that can waste the whole march, and it is the
cheapest of the three to fix. Order: (3), then (1), then (2).

## 6. Validation of the method. MEASURED

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
* **OPEN / NOT established:** the ladder in §1 is the **all-midpoint** optimum;
  the per-segment scheme is measured only at its binding endpoint (c = 13) and
  at D ∈ {1,4,16}, so the per-segment ladder's exact band boundaries — and
  hence a total somewhat below 322 h — are not yet computed. The 7.5 min /
  7.6 GB per 8-panel module is the measured D = 1 figure carried forward on the
  assumption that 8 panels per module keeps per-module cost constant as the
  module *count* grows; that is the design intent (it is what holds RSS under
  the 15 GB box) but it has not been measured at D > 1. No Lean has been built
  at any density above 1.
