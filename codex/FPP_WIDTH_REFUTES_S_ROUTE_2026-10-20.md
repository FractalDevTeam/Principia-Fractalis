# Step 1 refutes the S-route: the `F″` panels are 20–34× wider, and across the whole IBP ladder *amplification × enclosure-width is flat*. No pack.

**Date:** 2026-10-20 (Legion; measured with the shipped interval arithmetic from
`scripts/gen_fourier_panels_c27_4.py`, verbatim). Script:
`codex/measure_Fpp_panels.py`. Labels **FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**.

---

## HEADLINE

**My assumption was wrong, and the correction kills the pack.** I claimed the
`F″` panels would reach the same *absolute* enclosure width as the `F` panels,
making `c = 13` pass at 2.1×. Measured on identical panels with identical
outward-rounded arithmetic:

| | `F` nodes (shipped) | `F″` nodes (`S`) | ratio |
|---|---|---|---|
| width of `∫₀^{3/2}`, Re, at `c = 27/4` | 3.4359e−3 | 8.3705e−2 | **24.4×** |
| width, Im, at `c = 27/4` | 1.8859e−3 | 6.8995e−2 | **36.6×** |
| width, Re, at `c = 13` | 4.8621e−3 | 9.8935e−2 | **20.4×** |
| width, Im, at `c = 13` | 2.1476e−3 | 7.2589e−2 | **33.8×** |

So `δ_S = 4.95e−2` at `c = 13`, against the `4.31e−4` I assumed — **115× worse**.
With that, `Mc_lb(13)` on the `S` route is **−0.104**, versus `−0.036` on the
`Λ₀` route. The `S` route is *worse*, not better.

---

## 1. Why I was wrong. JUDGEMENT

I reasoned purely from **conditioning** — the `S` form has no `c²`
amplification — and silently assumed the integrand would be no harder to
enclose. It is much harder: `F₊″(0) + F₋″(0) = 0.4565` against
`F₊(0) + F₋(0) = 2ω(1) = 0.0864`, a 5× larger integrand to begin with, and the
`x²`, `x` factors (`x = eᵘ`) make it vary far faster across a panel. Enclosure
width is set by the integrand's size and variation, not by how the result will
later be combined.

## 2. The real structure: the exchange rate is fixed. MEASURED — this is the useful finding

`Re ξ(1+ic)` can be written at three rungs of the integration-by-parts ladder,
each with its own amplification of the panel error and its own integrand:

| rung | amplification | `δ` (hybrid quality) | error = amp × `δ` |
|---|---|---|---|
| `Λ₀`, no IBP — `(1 − c²R − cI)/2` | 84.50 | 6.09e−4 | **0.05150** |
| `T`, one IBP — `1/2 + (1+ic)·T` | 14.00 | 2.72e−3 | **0.03808** |
| `S`, two IBPs — `2Re S + (2/c)Im S` | 2.15 | 1.24e−2 | **0.02671** |

(at `c = 13`; `δ` is half the summed range-brick width, scaled by the measured
hybrid/all-range ratio 0.2507.)

**Amplification falls 39× across the ladder while `δ` rises 20×.** The product
improves by only **1.93×**. Integrating by parts trades amplification for
integrand difficulty at a nearly fixed exchange rate — which is what one should
expect, since both are measuring the same information content.

The needed error to put `c = 13` inside the box criterion at `r = 1/128` is
**< 0.001759**. The best rung measured is **0.02671** — a **15.2× shortfall.**

**So no change of representation reaches 13.** The `S` route's 1.93× would move
the ceiling from the producer-measured `10.28` to roughly `10.45` — about
`+0.17` of reach for an entire new panel pack. **Not worth building.**

## 3. What does reach 13. MEASURED, from the previous note

The only measured route remains a tighter enclosure on the `Λ₀` panels:
`169·δ_R + 13·δ_I < 0.003518` against the current `0.077800`, a **22.1×**
tightening, which at midpoint's `h²` scaling (and `M` roughly doubling by
`c = 13`) is **≈ 6.7× more panels per box** — about 6 h of serial build each.

**JUDGEMENT.** That is the honest price of `c = 13`, and it is a panel-count
decision, not a mathematics decision. Everything downstream — `L0`,
`R1BoxLocalL`, the producer's `--pick-r` ladder — already accepts it unchanged.

---

## Label summary

* **FACT:** the measurement reuses `gen_fourier_panels_c27_4.py`'s `I`,
  `exp_pos_interval`, `exp_neg_interval`, `cos_interval`, `sin_interval` and
  panel grid verbatim, so the two widths differ only in the integrand; the
  `ξ = 1/2 + (1+it)·T` and `ξ = i/(2t) + (2−2i/t)·S` identities behind the
  amplification column (the latter already Lean-proved as `edgeRe_eq_Ssum`).
* **MEASURED:** all four width figures and both ratios; `δ_S` at `c = 11, 12, 13`
  and the resulting `Mc_lb`; the three-rung ladder table; the 15.2× shortfall;
  the `S`-route zero crossing at `c = 7.78` on all-range quality.
* **JUDGEMENT:** that enclosure width is governed by integrand size and
  variation rather than downstream conditioning — the error I made; that the
  `S` pack is not worth building for `+0.17` of reach; that `c = 13` is now a
  panel-count decision.
* **OPEN / NOT established:** the `T` (one-IBP) rung's amplification `1 + c`
  ignores that its `1/2` does **not** cancel, so that rung additionally carries
  a ~200× value-cancellation; I did not pursue it, and its entry in the table is
  therefore optimistic rather than exact. The hybrid `δ` column rescales
  all-range widths by a single ratio (0.2507) measured on the `F` panels at
  `c = 27/4` rather than re-running midpoint on each integrand — adequate for a
  15× verdict, not for a 1.5× one.
