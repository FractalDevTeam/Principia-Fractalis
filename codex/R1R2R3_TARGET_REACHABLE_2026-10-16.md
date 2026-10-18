# R1/R2/R3 target check: **REACHABLE**. The target is `t = 13` for R1 — and R1 is the cheapest of the three legs.

**Date:** 2026-10-16 (Legion, compute on Acer). The hour of work flagged in
`GATE2_BOXLOCAL_SCOPE_2026-10-16.md` §4. No Lean. Verification:
`codex/r1r2r3_verify.py`, `codex/legs_verify.py`, `codex/encl_verify.py`.
Labels FACT / ARITHMETIC / JUDGEMENT / OPEN.

**VERDICT: REACHABLE.** `[−15, 15]` is reachable by this decomposition. My
flagged concern was precise but the answer is favourable: **R1 was never asked
to reach 15.** It stops at 13 — `0.988381` before the `Re ξ` sign change — and
`Im ξ` carries the interval straight through it.

**But the check turned up three things that matter more than the question:**

1. **The exact positivity target is `t = 13`**, not 15 and not 13.9.
2. **R1 is the cheapest leg.** The march has been building the cheap third:
   R1 = 613 boxes, R2 = 3638, R3 = 1709 (Tier 1). R2's margin is 6.1× tighter
   than R1's over a span 4× shorter.
3. **The binding constraint is Gate 1's enclosure, and it needs 186× at `t=13`
   and 1397× at `t=14.5`.** No Gate-2 work of any tier touches it.

---

## 1. The formal statements — FACT (read in Lean)

`PF/Analytic/RHBelow15Conditional_2026_10_10.lean:85-91`, the unfolded form:

```lean
theorem rh_below_15_conditional'
    (hR1 : ∀ t ∈ Set.Icc (0 : ℝ) 13,      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR2 : ∀ t ∈ Set.Icc (13 : ℝ) (29/2), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im)
    (hR3 : ∀ t ∈ Set.Icc (29/2 : ℝ) 15,   (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0) :
    ∀ σ t, … riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1 / 2
```

* **R1** — `Re ξ(1+it) > 0` on `[0, 13]`
* **R2** — `Im ξ(1+it) > 0` on `[13, 14.5]`
* **R3** — `Re ξ(1+it) < 0` on `[14.5, 15]`

The file's own header is appropriately careful: *"This theorem bears NOTHING on
the open Riemann Hypothesis. The three hypotheses R1/R2/R3 are themselves still
open."*

## 2. Why 15 is reachable: the decomposition routes around the sign change — ARITHMETIC (re-verified independently)

`Re ξ(1+it)` first vanishes at **`t = 13.9883806982`**. R1's interval ends at 13,
i.e. **0.988381 before** it. Over `[13, 14.5]` the decomposition switches to
`Im ξ`, which stays positive *through* the `Re ξ` zero — `Im ξ(1+i·13.9883806982)
= +7.900991e-04` — and then R3 picks `Re ξ` back up with the opposite sign.

**Both handoffs are consistent, with no gap and no contradiction:**

| junction | leg ending | leg starting |
|---|---|---|
| `t = 13` | `Re ξ = +2.509405e-03 > 0` (R1 ✓) | `Im ξ = +1.983233e-03 > 0` (R2 ✓) |
| `t = 14.5` | `Im ξ = +4.141834e-04 > 0` (R2 ✓) | `Re ξ = −5.591037e-04 < 0` (R3 ✓) |

**Worst-case margins, re-derived here and matching the 2026-10-09 record to
every printed digit** (independent confirmation of that campaign):

| leg | worst margin | at |
|---|---|---|
| R1 `Re ξ > 0` on `[0,13]` | `+2.509405052e-03` | right endpoint `t = 13` |
| R2 `Im ξ > 0` on `[13,14.5]` | `+4.141834185e-04` | right endpoint `t = 14.5` |
| R3 `Re ξ < 0` on `[14.5,15]` | `−5.591037171e-04` | left endpoint `t = 14.5` |

`ξ(1+i·0) = 1/2` exactly (the `1/s + 1/(1−s)` poles cancel; the scan starts at
0.01 for that reason).

**So the sign change at 13.9884 costs this decomposition nothing.** It was
designed around it. **JUDGEMENT: that is good engineering and it deserves
saying — the concern I raised was the right one to check and the answer is
clean.**

## 3. The reachable target, named exactly

> **For the positivity march: `t = 13`.** `R1 = ∀ t ∈ [0,13], Re ξ(1+it) > 0`.
> Remaining distance from the landed frontier `6.5625`: **6.4375**.

Not 15 — that is R2's and R3's business, in `Im ξ` and in `−Re ξ`. Not 13.9 —
that overshoots R1 by 0.9 at the most expensive part of the curve.

## 4. All three legs priced — and R1 is the cheapest. ARITHMETIC

The same derivative bound serves all three legs: from
`d/dt[2ξ(1+it)] = (−2t+i)Λ₀ + (−t²+it)iΛ₀'` the modulus bound is identical for
real and imaginary parts, so `L(t) = [(1+2t)B + (t²+t)B']/2` bounds
`|d/dt Re ξ|` and `|d/dt Im ξ|` alike. Per box, `r < margin(c)/L(c)`.

| leg | span | width | Tier-1 boxes | Tier-3 boxes |
|---|---|---|---|---|
| R1 `Re ξ > 0` | 6.5625 → 13 | 6.44 | 613 | 58 |
| **R2 `Im ξ > 0`** | 13 → 14.5 | 1.50 | **3638** | **236** |
| R3 `Re ξ < 0` | 14.5 → 15 | 0.50 | 1709 | 96 |
| **TOTAL** | | | **5960** | **390** |

At ~11.5k generated Lean lines per box: **Tier 1 ≈ 68.5M lines, Tier 3 ≈ 4.5M
lines (15× reduction).**

**R2 is the expensive leg — 6× R1's box count over a span 4× shorter** — purely
because its margin is 6.1× tighter. R3 is 2.8× R1 over a span 13× shorter.
**JUDGEMENT: the march's progress to date is on the cheapest third of the
problem, and the published "boxes past the ceiling" framing does not convey
that.**

## 5. The real wall: Gate 1's enclosure, 186× and 1397× — ARITHMETIC. This dominates everything.

Gate 1 needs `c²R_ub + c·I_ub ≤ 1 − 2Mc_lb`, while the true values satisfy
`c²R + c·I = 1 − 2Re ξ(c)` exactly. So the **enclosure error must fit inside the
margin**:

  `c²(R_ub − R) + c(I_ub − I) ≤ 2(Re ξ(c) − Mc_lb)`.

Achieved at the landed `c = 51/8` box (line 893 constants):
`R_ub − R = 2.6217e−03`, `I_ub − I = 1.8874e−03`, costing **0.118579** of the
budget there — affordable only because the margin was 0.187.

Taking `Mc_lb = Re ξ/2` (half the true margin, leaving slack `= Re ξ`):

| t | `Re ξ` = slack | max allowed `dR` | vs achieved |
|---|---|---|---|
| 6.375 | 1.868e−01 | 4.130e−03 | 1× |
| 8 | 1.019e−01 | 1.461e−03 | 2× |
| 10 | 3.681e−02 | 3.434e−04 | 8× |
| 12 | 8.194e−03 | 5.368e−05 | 49× |
| **13** | **2.509e−03** | **1.407e−05** | **186× tighter** |
| **14.5** (R2 worst) | 4.142e−04 | 1.877e−06 | **1397× tighter** |

**CLARIFICATION 2026-10-17 (Legion) — the column header, and the global worst
point.** The header reads `` `Re ξ` = slack ``, but the margin is a *different*
quantity on each leg (§1): `Re ξ` on R1 `[0,13]`, **`Im ξ` on R2 `[13,14.5]`**,
`|Re ξ|` on R3 `[14.5,15]`. So the `t=14.5` row's `4.142e−04` is
`Im ξ(1+14.5i) = +4.1418e−04` — **the value is correct; the header does not
apply to that row.** (Re-derived independently; `Re ξ(1+14.5i)` is
`−5.5910e−04`, which is R3's margin `|Re ξ|` at the same point, 1.8429e−06 after
the `(t²+t)` weight.)

Per-leg add-on budgets `margin(t)/(t²+t)`, each leg at its own worst t:

| leg | worst t | margin | add-on budget |
|---|---|---|---|
| R1 | 13.000 | `Re ξ = 2.5094e−3` | 1.3788e−5 |
| R2 | 14.495 | `Im ξ = 4.1721e−4` | 1.8576e−6 |
| **R3** | **14.500** | **`\|Re ξ\| = 4.1418e−4`** | **1.8429e−6** ← global worst |

**The binding point for the whole target is t ≈ 14.5, not t = 13 — 7.5×
tighter.** See `codex/ADDON_SCOPE_RESIDUE_IS_THE_WORK_2026-10-17.md`: the
add-on *architecture* floors at 32.7% of that budget (the exact integral of a
majorant that has already discarded all oscillation via `|cos|,|sin| ≤ 1`), so
no amount of subdivision clears it.

**And the residue lever does not reach this.** The 32.8× residue tightening
removes the *add-on* (9.26e−4 of the 2.62e−3 total); the **panel width is
1.70e−3** and must come down by its own large factor. If the panel scheme is
Simpson-like `O(h⁴)` — **ASSUMPTION, flagged** (the centred-form record says
Simpson `O(h⁴)`) — then 186× needs ~3.7× more panels and 1397× needs ~6.1×,
which is tractable *per box* but multiplies an already-large box count.

> **This is the binding constraint for the whole programme, it lives entirely on
> the Gate-1 side, and no Tier of Gate-2 work moves it by anything.**

## 6. Recommendation — and this reverses my previous one. JUDGEMENT

**Previously** I recommended deferring Tier 3 until the target was confirmed.
The target *is* confirmed, and that changes the arithmetic: at Tier 1 the full
programme is **5960 boxes / 68.5M generated lines**, which is not a programme.
So **Tier 3's weeks are now justified** — a 15× cut is the difference between
impossible and merely very large.

**But Tier 3 is not sufficient, and on its own it is not the right next build.**
Three levers are needed, in order of necessity:

1. **Gate-1 enclosure depth** (186× at `t=13`, 1397× at `t=14.5`) — binding,
   and untouched by any Gate-2 work.
2. **Tier-3 decaying bound** — 15× on box count.
3. **Per-box line economy** — 11.5k lines/box is mostly *regenerated* panels
   (6 segments × 1226 lines at `c=51/8`). Shared or parametric panels would
   multiply this down independently of 1 and 2.

**JUDGEMENT on what to actually build.** All three levers point at the same
object, and this project already named it: memory records the frontier object as
a **t-ranging certified interval-quadrature producer for
`completedRiemannZeta₀(1+it)`** (panels currently hard-wired per `t`). That one
construction would collapse levers 1–3 into a single parametric artefact and
turn 5960 bespoke boxes into one producer plus a covering argument. **It, not
Tier 3, is the thing that unlocks the programme.** Tier 3 would then be a
sharpening *inside* it rather than a separate 390-box campaign.

**So: do not start a 390-box Tier-3 campaign. Scope the t-parametric producer
first** — it is the common factor in every remaining cost, and the current
architecture (one bespoke panel pack per box) is what makes all three legs
expensive.

**OPEN:** the `O(h⁴)` panel-scaling assumption in §5 (checkable in an hour from
the generator); whether a t-parametric producer can hold the three-axiom bar
(the hard-wiring may exist precisely to keep `norm_num` goals closed); and the
actual certified panel widths at `t > 6.5`, which no one has measured — §4's and
§5's numbers assume the `c=51/8` width carries, and it will in fact be worse
because `cos(cu/2)` oscillates faster.

---

## Label summary

* **FACT (read in Lean):** the three hypothesis statements and their intervals
  `[0,13]`, `[13,29/2]`, `[29/2,15]`; the file's own disclaimer that R1/R2/R3
  remain open; the `c=51/8` enclosure constants at line 893.
* **ARITHMETIC (computed here):** the first zero of `Re ξ` at 13.9883806982 and
  R1's 0.988381 clearance; all three worst-case margins, matching the
  2026-10-09 record digit-for-digit; both handoff checks; the per-leg box counts
  (613 / 3638 / 1709 Tier 1, 58 / 236 / 96 Tier 3); the required-enclosure table
  and the 186× / 1397× figures; that the residue add-on is 9.26e−4 of a 2.62e−3
  excess.
* **JUDGEMENT (mine):** that the decomposition's design around the sign change
  is sound and deserves credit; that the march is on the cheapest third; that
  the Gate-1 enclosure is the binding constraint; the reversal on Tier 3; that
  the t-parametric producer is the object to scope next.
* **NOT established:** the `O(h⁴)` panel scaling; the real panel widths beyond
  `t = 6.5`; whether a t-parametric producer keeps the axiom bar.
