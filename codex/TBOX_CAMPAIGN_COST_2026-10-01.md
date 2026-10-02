# The t-boxed campaign, measured — 2026-10-01

**The 10–15× scaling estimate is numerically right and its reasoning is wrong. Measured:
232 boxes, 56,813 generated modules, 75.9 serial days — against an estimate of 180–230
boxes, 40–60k modules, 10–15×. The estimate was right only because two large errors
cancelled.**

**And the cost is not intrinsic. 58–64% of every box's budget is lost to interval
dependency, at a measured factor of 402× over the true sensitivity. That, not quadrature
and not panel cost, is what sets 232 boxes. Attack it before spending 76 days.**

## 1. The measured schedule

| segment | claim | t-range | boxes | panels | panel modules | total modules | serial days |
|---|---|---|---|---|---|---|---|
| R1 | `0 < Re ξ(1+it)` | [0, 13] | 53 | 8,527 | 3,491 | 7,731 | 7.2 |
| R2 | `0 < Im ξ(1+it)` | [13, 29/2] | 43 | 21,450 | 7,729 | 11,169 | 15.3 |
| R3 | `Re ξ(1+it) < 0` | [29/2, 15] | **136** | 75,643 | 27,033 | 37,913 | **53.3** |
| **total** | | [0, 15] | **232** | **105,620** | 38,253 | **56,813** | **75.9** |
| *existing σ campaign, for scale* | | t=15, σ∈[1/2,1] | 18 | 9,540 | 3,384 | 4,824 | 6.7 |

Ratio 11.3–11.8×, or **9.9× (47,773 modules, 74.8 days) using tiered M certificates** —
legitimate because `MHI` is monotone increasing in `|t|` with `p1, p2` fixed at `1, 2` on
σ = 1, so six tiers × 40 segments serve all 232 boxes.

Days are serial Acer at the campaign-calibrated **166 s per 3-node panel module** — the
figure that reproduces the recorded ~6.5 days for the existing 3,384 panel modules. At the
clean-serial measured rate (225 s) the total is 102 days; at `-j2` on 22 GB, ~38 days.
Parallelism stays at 1 on the 15 GB Acer: `build_r331d.log` shows panel modules OOM-killed
(exit 137) at ~9 GB.

Measured elaboration, clean serial run: panel module n=1150, mean 224.9 s, median 231 s,
max 360 s; segment assembly n=181, median **12 s**; M certificate n=166, median **10 s**.
An earlier 190 s mean for M certificates was a contention artifact of a loaded log, not a
real cost.

Insensitive to the error target: raising the residual from 1e-6 to 1e-5 moves the totals
by under 2%.

## 2. Why the estimate's reasoning is false

The route document's premise was: *"the t-sensitivity of a quadrature node, `(log u)/2`,
equals its σ-sensitivity, so t-boxes need the same widths the σ campaign used."*

The prefactor is shared. What it multiplies is not.

```
realThetaReIntegrandN 3 σ t u = (u^(σ/2−1) + u^((1−σ)/2−1)) · cos((t/2)·log u) · ωP₃(u)
```

`∂/∂σ` produces the **difference** branch `u^(σ/2−1) − u^((1−σ)/2−1)`; `∂/∂t` produces the
**sum** branch. Near `u = 1`, where `exp(−πu)` puts essentially all the mass, the ratio of
sum to difference is ≈ **135**. The trig factor swaps the other way — `|sin((t/2)log u)|`
is small near `u = 1` while `|cos| ≈ 1` — clawing back ≈ 4.5×.

| | ReΛ₀ spread | ImΛ₀ spread | ξ-space spread |
|---|---|---|---|
| t direction, σ=1, t=14.5 | 1.725e-3 | 1.562e-4 | **1.952e-1 per unit t** |
| σ direction, t=15, σ≈1 | 1.407e-4 | 1.719e-3 | **4.161e-2 per unit σ** |
| | 12.3× worse | 11× better | **4.7× worse** |

The spreads transpose exactly, but in the ξ bound the Re spread carries weight `t² = 225`
and the Im spread only `t ≈ 15`, so the swap is not neutral. On top of that there is a term
with **no counterpart in the σ campaign at all**: `d(t²)/dt = 2t = 29` versus
`d(225 − σ(σ−1))/dσ = 2σ − 1 ≈ 1`. That coefficient-variation term eats **22–33% of every
t-box's budget**.

Net: near `t = 14.5` a t-box is **0.00295** wide against the σ campaign's narrowest
`1/64 = 0.01563` — **5.3× narrower, not equal.**

## 3. The two errors that cancelled

The totals came out right because the premise is wrong in **both directions at once**:

- **R3's boxes are 5.3× narrower** than any σ-box.
- **R1's first box spans `t ∈ [0, 5.3248]` — 340× wider** than the σ campaign's narrowest,
  because `ξ(1) = 1/2` leaves enormous slack at low `t`.

13 of the 15 units of `t` are covered by **53 boxes at average width 0.245**; the last
**0.5 units need 136**. The margin profile is doing the work, not matched widths. Any future
estimate built on the same premise will be wrong by a large factor in one direction or the
other depending on which end of the range it happens to sample.

## 4. The finding that actually matters: a 402× interval-dependency loss

Where each box's error budget goes (R3 / R2 / R1):

| contribution | share |
|---|---|
| `t²` · ReΛ₀ spread | 58 / 64 / 58 % |
| `t²` coefficient spread | 22 / 33 / 30 % |
| quadrature | 18 / 3 / 11 % |
| Im terms + envelope | < 3 % |

**This is not a quadrature problem.** The true `|d(2 Re ξ)/dt|` near `t = 14.75` is
**9.71e-4 per unit t**. The interval method's spread is **3.90e-1** — a **402×
interval-dependency loss**. That loss sets the box count.

Panels per box are essentially unchanged from the σ campaign (median 550 against 530). The
entire factor is **box count, 232/18 = 12.9×**, and the box count is set by dependency loss.

So 76 days buys a result whose difficulty is an artifact of how the bound is computed, not
of the mathematics. **The lever to pull before authorising the campaign is the formulation,
not the schedule** — anything that evaluates the `t`-dependence with less interval
dependency (handling the `t²` coefficient analytically rather than through intervals is the
obvious first candidate, since it alone is 22–33%) attacks the dominant term directly.
Re-costing after such a change is cheap; the campaign is not.

## 5. Model validation

The cost model is a Python reimplementation of the certified ledger, calibrated by a single
scalar — β = 1.0521, the midpoint-sum-below-integral deficit as a multiple of `E`; fitted β
per box ranged 1.0515–1.0541.

- Reproduces **all 17 recorded σ-box ξ margins to ≤ 0.25%**.
- Reproduces Box116's exact rationals: `RE_LO` 4.429066e-3 against Lean's 4.429062e-3;
  `IM_LO` 2.739254e-4 against 2.738007e-4.
- Soundness spot-checked against mpmath in every sampled t-box: the certified residual is
  always below the true margin (ratio 0.001–0.66), never above.

## 6. R1 as a pilot — yes, and the first increment is two hours

R1 is 53 boxes, 8,527 panels, 3,491 panel modules, 7,731 generated modules, **7.2 days**
(9.6 at the pessimistic 225 s). About the size of the entire existing campaign, and it
validates the generator transpose end to end. The first increments are trivially small:

| increment | t covered | panels | modules | time |
|---|---|---|---|---|
| box 1 | [0, 5.3248] | 40 | 40 | **≈ 2 hours** |
| boxes 1–5 | [0, 9.6452] | 263 | 200 | ≈ 9 hours |
| boxes 1–9 | [0, 10.77] — 83% of R1 | 568 | 320 | ≈ 15 hours |

**One caveat, specific to R1 and R2.** Both need tight **upper** bounds on Λ₀, and the
existing generator never computed them: its `re_Lambda0_upper` is the trivial `≤ 1`.
Measured, Lean's `RE_HI` is 9.81e-3 against a true 4.432e-3 — **2.2× loose** — and `IM_HI`
5.77e-4 against 3.05e-4. The R1/R2 figures above assume the transpose computes upper bounds
as tightly as it already computes lower bounds; it is the same machinery with signs flipped,
but it is work that has not been done. **R3 needs lower bounds only and sits entirely on the
already-validated path.**

## 7. What the generator actually is

For whoever does the transpose:

- `scripts/opt40tight.py` is **frozen geometry only** — 40 macrosegments of the
  *u*-quadrature interval `[1,5]`, not σ and not t, dyadic widths 1/32 → 1/4, hand-tuned
  `n_j` summing to 530, with a loose rational `MHI` ceiling carrying ~10% slack.
- `scripts/emit_box_segment.py` is the **production emitter** (a box-parametric fork of
  `emit_stage2_segment.py`, still carrying the old docstring). For box `K` and
  `σ ∈ [σ_lo, σ_hi]` it writes `Seg{j}P{p}.lean` panels — **3 quadrature nodes each** — a
  `Seg{j}.lean` assembly, and `PF/Numerics/Box{K}Seg{j}M.lean`. Line 1355 `MHI = sum(_B)*2`
  is the **tight certified majorant**, not opt40tight's slack ceiling.
- `MHI` is a uniform C² bound on `∂²/∂u²` of one elementary term of the truncated theta
  integrand (`RiemannXiThetaRealFormAndBoxes_r331b.lean:1529`), and it is **monotone
  increasing in `|t|`** — the t-transpose substitutes `t_hi` and nothing else.
- Panel count follows `n_j ∝ (MHI_j · h_j³)^{1/3}` at fixed total error, so
  `Σ n_j ∝ E^{−1/2}`. Real cost is `Σ ceil(n_j/3)` panel modules plus 40 segment assemblies
  plus 40 M certificates per box. Envelope target is `1/5000000`
  (`RiemannXiBox0Envelope.lean:121`).

## 8. Provenance

Scripts at `D:\CLAUDE-i9\_tmp\tbox-costing\` (`fastmodel.py`, `tbox_cost.py`, `march.py`,
`verify.py`, `decomp.py`, `segcheck.py`), mirrored to `/tmp/` on Acer; schedules at
`/tmp/tbox_schedule_1e-06.json` and `/tmp/tbox_schedule_1e-05.json`. No Lean was built and
nothing in the corpus was modified. Numerics are mpmath and the calibrated model, **not
certificates**.
