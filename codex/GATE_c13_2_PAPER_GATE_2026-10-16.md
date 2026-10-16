# Paper gate for c = 13/2: closable, but the scoped levers are the wrong two — and the march's real ceiling is Gate 2, three boxes out

**Date:** 2026-10-16 (Legion, compute on Acer). **Paper gate before build**, per
the Pilot-14 discipline. No Lean written. Verification scripts in this note's
companion run; all figures reproducible.
Labels FACT / ARITHMETIC / JUDGEMENT / OPEN.

**Scope note, stated first.** The c=13/2 order attributed a tightening scope to
me that I had not produced — the c=51/8 pilots (`bdeb766d`, `35f89b45`) are the
other instance's work and landed while this instance was on the Wallstrom lane.
So rather than execute a scope I did not write, this is the paper gate computed
from scratch. It changes the recommendation in two places.

**Three findings, in order of consequence:**

1. **The march's binding constraint is Gate 2, not Gate 1**, and it hard-stops
   at `|t| ≤ 6.8863` — three more boxes. No amount of Gate-1 enclosure
   tightening moves it.
2. **At current enclosure quality the c=13/2 box FAILS Gate 1 by ≈ 0.0143** —
   but it is comfortably closable, and **the two levers named in the order
   (analytic tail, ω-gap) supply only 34% of what is needed.** The residue term
   is where the room is: it is **32.8× loose for free**, with no new
   mathematics.
3. **§0 of the landed c=51/8 box was numerically false.** Found and **repaired**
   (comment-only; the proof always used the correct constants).

---

## 1. Calibration: what "margin" is, reproduced exactly — ARITHMETIC

The reported margin series `0.0578 → 0.0375 → 0.0171 → 0.0050` is the **Gate-1
slack** `3/4 − (c²·R_ub_f + c·I_ub_f)`. Confirmed at the fourth box from the
rational constants the proof actually uses
(`R1_c51_8_r1_16_pointwise_CLOSED_2026_10_16.lean:893-896`):

```
R_ub_h32 = 542831867/32000000000 ≈ 0.0169634958
I_ub_h32 =  60314889/32000000000 ≈ 0.0018848403
add-on   = 231/279841 + 1/10⁶ + 1/10⁴ ≈ 0.0009264688
(2601/64)·0.0178899646 + (51/8)·0.0028113090 = 0.74498144
slack    = 3/4 − 0.74498144 = +0.00501856      ← the reported +0.0050
```

Calibration confirmed. **It is not the true-value margin** — the true
`Re ξ(1+ic)` at that box's worst edge sits at `+0.0581` above `1/8`. The series
is dominated by *enclosure* quality, not by approach to any mathematical
ceiling. Conflating the two would mis-read the stop condition, which is why §4
matters.

## 2. The repaired header defect — FACT

`§0` of the landed box stated `R_ub_f ≈ 0.018418` and a product `≈ 0.6909`.
These are inconsistent with each other — `40.6406 × 0.018418 = 0.7485`, which
would **fail** the gate — and both disagree with the rational constants at
line 893. The proof was always correct; only the comment was wrong.

**Repaired in place** (comment-only diff, 14 insertions / 4 deletions), with the
correct constants and a dated note recording what was wrong. Per the standing
repair-not-disclosure rule this is a fix, not a flag. Module re-verified after
the edit.

**JUDGEMENT:** a header that states a *failing* product inside a file whose
headline claims the gate closes is exactly the kind of defect that survives
because everyone reads the headline. Worth a sweep of the other three boxes'
§0 blocks for the same error class.

## 3. The c = 13/2 projection — ARITHMETIC

Enclosure quality achieved at c=51/8, net of add-ons:

  `R_ub_h32 − R_true = 1.695e−3`,  `I_ub_h32 − I_true = 9.610e−4`.

Carrying the **same absolute panel widths** to c=13/2 (optimistic: `cos(cu/2)`
oscillates faster at larger `c`, so the real width will be somewhat larger and
the true shortfall is **at least** this):

```
true R(6.5) = 0.0150365631 ,  true I(6.5) = 0.0009226217
projected R_ub_f ≈ 0.0176582339 ,  I_ub_f ≈ 0.0028100519
c²·R_ub_f + c·I_ub_f = 0.76432572   vs budget 0.75
=> slack = −0.01432572          FAILS Gate 1, shortfall ≈ 0.0143
```

So the box does **not** close by rebuilding at current quality. Tightening
first is correct, exactly as ordered.

## 4. Lever ranking — the order named the wrong two. ARITHMETIC

At c=13/2 both `R` and `I` carry the same add-on, with weight `c² + c = 48.75`:

| add-on | value | cost in the 0.75 budget |
|---|---|---|
| **residue** `231/279841` | 8.255e−4 | **0.040242** |
| ω-gap `1/10⁴` | 1.000e−4 | 0.004875 |
| analytic tail `1/10⁶` | 1.000e−6 | 0.000049 |

Needed recovery: **0.014326**.

* analytic tail, killed entirely: buys `0.000049` — **negligible**;
* ω-gap, killed entirely: buys `0.004875` — **34% of the need**;
* **the two scoped levers together buy `0.004924`, i.e. 34%. Insufficient.**
* the **residue** term alone costs `0.040242` — **2.8× the entire need**.

### Why the residue is loose, and why fixing it is free — ARITHMETIC (verified)

The current bound takes, on `u ∈ [3/2, 5]`,
`|f(u)| ≤ (e^{u/2}+1)·3·e^{−π e^u}` and then over-loosens **two factors at the
wrong endpoint**:

* `e^{−π e^u} ≤ e^{−4π} = 3.49e−6`, where the true left-endpoint value is
  `e^{−π e^{3/2}} = 7.68e−7` — **factor 4.5**;
* `e^{u/2} + 1 ≤ 22` (the value at `u = 5`), where at the left endpoint it is
  `3.12` — **factor 7.1**.

`4.5 × 7.1 ≈ 32`, and indeed evaluating the **same majorant** at the correct
endpoint gives `2.513e−5` against the current `8.255e−4` — **32.8× tighter with
no new mathematics**. One bisection gives 65.7×; seven pieces 229.9×.

`g` is verified strictly decreasing on `[3/2,5]`
(`g'/g = ½e^{u/2}/(e^{u/2}+1) − πe^u`, computed as
`−13.74, −22.85, −62.69, −171.08, −465.79` at `u = 1.5, 2, 3, 4, 5`), so
left-endpoint maxima are valid and the subdivision is sound.

Budget impact at c=13/2:

| residue treatment | cost | frees | verdict |
|---|---|---|---|
| current | 0.040242 | — | fails by 0.0143 |
| 2 pieces | 0.000613 | **0.039629** | **ENOUGH** (2.8× over) |
| 4 pieces | 0.000306 | 0.039935 | ENOUGH |
| 7 pieces | 0.000175 | 0.040067 | ENOUGH |

**So: tighten the residue, not the tail or the ω-gap.** Two pieces suffice with
2.8× margin to spare. This is "semantics only, no new math" in the same sense
the previous tightening was — it is not even a subdivision argument, just
evaluating the existing majorant where it is actually largest.

## 5. The real ceiling: Gate 2 at `|t| ≤ 6.8863` — ARITHMETIC, and the strategic point

Gate 2, as written in the scaffold, licenses the derivative bound `L = 1` over
the box via the **uniform** enclosure `‖Λ₀‖ ≤ 50/1727`:

  `50(1+2|t|) + 50(t²+|t|) ≤ 2·1727`, i.e. `t² + 3t + 1 ≤ 1727/25 = 69.08`,

evaluated at the box's **upper edge**. Ceiling: `t ≤ 6.886298`.

| centre | upper edge | `50(t²+3t+1)` | slack | verdict |
|---|---|---|---|---|
| 51/8 | 6.4375 | 3087.70 | 366.30 | PASS (landed) |
| **13/2** | **6.5625** | **3187.70** | **266.30** | **PASS** |
| 53/8 | 6.6875 | 3289.26 | 164.74 | PASS |
| 27/4 | 6.8125 | 3392.38 | 61.62 | PASS |
| **55/8** | **6.9375** | **3497.07** | **−43.07** | **FAIL** |
| 7 | 7.0625 | 3603.32 | −149.32 | FAIL |

Meanwhile Gate 1's **true-value** headroom runs far beyond: `Re ξ(1+ic)` crosses
`1/8` only at `c = 7.5019`, `1/16` at `9.0460`, and `0` at `13.9884` — the last
figure independently reproducing this project's established first sign change at
`t = 13.9883806982`, which cross-checks the whole `Λ₀` convention used here.

> **So the wall is Gate 2, and it arrives at centre 55/8 = 6.875 — three boxes
> after the one requested. Gate-1 enclosure tightening (residue, tail, ω-gap)
> does not move it by a single step, because Gate 2 does not use the panel
> enclosure at all; it uses the uniform `50/1727` derivative route.**

**JUDGEMENT — why this matters for the stop condition.** The stated hard stop is
"if Gate 1 fails after full architectural tightening, stop." On these numbers
Gate 1 will **not** be what fails: it has `0.040` of residue slack available
against a `0.0143` need, and true-value headroom to `c = 7.50`. Gate 2 will fail
first, at 6.875, and it is not addressable by the named levers. Waiting for a
Gate-1 failure to trigger the reassessment would mean three more boxes of work
and then hitting a wall that was visible now.

## 6. Recommendation

**Proceed with c = 13/2 — but tighten the residue, not the tail or the ω-gap.**
Both gates pass on paper (Gate 2 slack 266.30; Gate 1 closes with 2.8× margin
once the residue is fixed), and the residue fix is free.

**Then stop at centre 27/4 and reassess, not at a Gate-1 failure.** Three boxes
(13/2, 53/8, 27/4) are available on the current architecture. Continuing past
them needs the **Gate-2 derivative route** replaced — a pointwise or
box-local derivative bound in place of the uniform `50/1727` one. Whether that
is worth building is a strategy question, not a tightening question, and it
should be taken with the 6.886 number in hand rather than discovered at 6.875.

**OPEN / not done here:** the actual panel enclosure width at c=13/2 (§3 assumes
the c=51/8 width and is therefore optimistic); whether the other three landed
boxes' §0 blocks carry the same arithmetic defect as the one repaired in §2;
and what a box-local Gate-2 derivative bound would cost.

---

## Label summary

* **FACT:** the §0 header defect and its repair; the rational constants at
  line 893; the Gate-2 inequality as written in the scaffold.
* **ARITHMETIC (computed here):** the `+0.00501856` slack reproducing the
  reported margin; the enclosure widths `1.695e−3` / `9.610e−4`; the c=13/2
  shortfall `−0.0143`; the lever cost table; the residue looseness factors
  `4.5 × 7.1 ≈ 32.8` and the subdivision table; `g' < 0` on `[3/2,5]`; the
  Gate-2 ceiling `6.886298` and the per-box table; the Gate-1 true-value
  crossings `7.5019 / 9.0460 / 13.9884`.
* **JUDGEMENT (mine):** that the margin series is enclosure-dominated rather
  than ceiling-dominated; that the stop condition as stated will mis-fire; the
  recommendation to stop at 27/4; that the §0 defect class deserves a sweep.
* **NOT established:** the true panel width at c=13/2; that no Gate-2 route
  past 6.886 exists — only that the current uniform one stops there.
