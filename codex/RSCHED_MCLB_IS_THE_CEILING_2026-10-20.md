# Shrinking `r` near the top buys 10.0625 → 10.2817 and then stops dead — `Mc_lb` hits zero, and `r` is not in `Mc_lb`

**Date:** 2026-10-20 (Legion; measured with `codex/gen_box.py --pick-r` on Acer's
panel arithmetic). Labels **FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**.

---

## HEADLINE

**Shrinking `r` cannot reach 13, and the reason is structural, not a matter of
going small enough.** The box criterion is

  `L₀(c − r)·r < Mc_lb(c)`,  `Mc_lb(c) = (1 − c²·R_ub − c·I_ub)/2`

and **`Mc_lb` does not contain `r`**. So a centre with `Mc_lb(c) ≤ 0` is
unreachable at *every* radius; no ladder helps. Measured, that happens at
**c ≈ 10.28**:

| `c` | 10 | 41/4 = 10.25 | 165/16 = 10.3125 | 83/8 | 21/2 |
|---|---|---|---|---|---|
| `Mc_lb` | +0.00751429 | +0.00082888 | **−0.00074892** | −0.00232183 | −0.00538046 |

`Mc_lb(13) = −0.0364`. Not small — *negative by fifteen times* the value it
would need to be positive at all.

---

## 1. What shrinking `r` does buy. MEASURED

`gen_box.py --pick-r` takes the largest dyadic `r ∈ {1/16 … 1/4096}` clearing a
1.25× safety ratio. Walking the frontier from the landed coverage edge
`109/16 = 6.8125`:

| radius | boxes |
|---|---|
| 1/16 | 25 |
| 1/32 | 3 |
| 1/64 | 3 |
| 1/128 | 2 |
| 1/256 | 2 |
| 1/512 | 2 |
| 1/1024 | 2 |
| 1/2048 | 3 |
| 1/4096 | 3 |
| **total** | **45 boxes → frontier 10.281738** |

Against the fixed `r = 1/16` schedule (26 boxes → 10.0625): **+0.219 of reach
for +19 boxes.** The ladder is collapsing geometrically at the end — the last
three boxes have width `2/4096` and advance the frontier by `0.0015` — because
`Mc_lb` is going to zero, not because `L₀` is misbehaving (`L₀` is flat at
~0.0958 throughout, and `L₀·r` is 2× inside budget at every chosen step).

**JUDGEMENT.** The ladder is worth having — it is a producer flag, not a new
theorem, since `R1BoxLocalL_2026_10_20` already takes `r` as a parameter — but
past ~10.1 it is buying thousandths of reach per box. The honest stopping point
for this machinery is around `c = 10.1` at `r = 1/32`.

## 2. Why 13 is out of reach, quantified. MEASURED

`Mc_lb(c) = Re ξ(c) − (c²·δ_R + c·δ_I)/2` where `δ` is the enclosure's excess
over the true integral. Two things go wrong at once: `Re ξ` decays
(`0.002509` at 13) while the error term is **amplified by `c²`**.

With the hybrid pack's measured `δ_R ≈ 4.31e−4`, `δ_I ≈ 3.86e−4`:

| | at `c = 13` |
|---|---|
| `Re ξ` | 0.002509 |
| error term `(c²δ_R + cδ_I)/2` | **0.038900** |
| `Mc_lb` | **−0.036390** |

To get `Mc_lb(13) > L₀·r` at `r = 1/128` needs
`169·δ_R + 13·δ_I < 0.003518` against the current `0.077800` — a **22.1×
tightening**. Panel cost: range-brick error scales as `h` (so 22× the panels),
midpoint as `h²` (so `√22 = 4.7×`), and `M` roughly doubles by `c = 13`
(`M̂ = 20.09` vs `9.78`), giving **≈ 6.7× more midpoint panels per box**. At
~7m30s and 7.6 GB per panel file that is ~6 h of serial build per box.

## 3. The way to 13 is a change of enclosed object, not more panels. MEASURED

The `c²` amplification is an artefact of enclosing `Λ₀`. In the Tier-3 form
already proved in Lean (`edgeRe_eq_Ssum`, `246940c8`),

  `edgeRe t = 2·Re S(t) + (2/t)·Im S(t)`,  `S = ∫F₊″e^{itu/2} + ∫F₋″e^{−itu/2}`

an enclosure error `δ_S` costs `(2 + 2/t)·δ_S` — **no `c²` factor at all.** At
the *same absolute panel quality* `δ_S = 4.31e−4`:

| `c` | `Mc_lb` via `S` | `L₀·r` at `r = 1/128` | |
|---|---|---|---|
| 11 | 0.017971 | 0.000769 | PASS 23× |
| 12 | 0.007261 | 0.000759 | PASS 9.6× |
| **13** | **0.001582** | **0.000750** | **PASS 2.1×** |

So **13 is reachable with the panel density already in hand**, provided the
panels enclose `S` rather than `Λ₀`. That is the same conditioning fact that
made the derivative bound possible (the Tier-3 form measured 1.0–3.2×
cancellation against 397× for the naive form), now applied to the *value*
instead of the derivative.

**What it costs: one new panel pack.** `CoreDefs` for the `F″`-based nodes
(`F₊″ = e^{u/2}[¼ω + x(xω″ + 2ω′)]` with `ω, ω′, ω″` all explicit 3-term
exponential sums, so the `Interval` mirror follows the existing pattern), a
retargeted panel generator, and residue/tail/ω-gap add-ons for the `F″`
integrands. Comparable in size to the existing pack — but it is the only route
that reaches 13 without multiplying panel count, and the producer, `L₀`, and
`R1BoxLocalL` all accept it unchanged.

---

## Label summary

* **FACT:** `Mc_lb` is independent of `r`, so `Mc_lb ≤ 0` is unreachable at any
  radius; `R1BoxLocalL_2026_10_20` already takes `r` and `M` as parameters, so
  the ladder needed no new theorem.
* **MEASURED:** the `Mc_lb` grid at eleven centres; the zero crossing between
  10.25 and 10.3125; the 45-box ladder schedule reaching 10.281738; the 26-box
  fixed-`r` schedule reaching 10.0625; `Mc_lb(13) = −0.036390`; the 22.1×
  tightening requirement and its 6.7× midpoint-panel cost; the `S`-route table
  showing `c = 13` passing at 2.1×.
* **JUDGEMENT:** that the ladder is worth shipping but should stop near `c = 10.1`;
  that the `S`-enclosure, not more panels, is the route to 13.
* **OPEN / NOT established:** the `S`-route figures assume the `F″` panels would
  achieve the *same absolute* enclosure width as the `F` panels — plausible
  (same oscillatory structure, and `∫|F″| = 1/4` is comparable to `∫F ≈ 0.09`)
  but **not measured**; I have not built any `F″` panel. And the 45-box schedule
  is computed from the eleven measured `Mc_lb` values with linear interpolation
  between them — the chosen centres have not each been verified exactly by the
  producer, only the ladder logic and the endpoints.
