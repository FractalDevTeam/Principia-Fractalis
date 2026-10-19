# Riemann integration: the march is blocked at 6.75 by a hard-coded Gate-2 constant, not by anything built since 2026-10-16 — and Gate-1 at 27/4 needs a per-segment hybrid, because neither scheme alone passes

**Date:** 2026-10-19 (Legion, measured on Acer). Analysis only, no Lean.
Labels **FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**.
Script: `codex/integ_verify.py` (parses the landed segment files theorem by
theorem).

---

## HEADLINE — read this before the task list

**Everything built since 2026-10-16 is on the Gate-1 side. The wall is Gate-2,
it arrives at centre 55/8 = 6.875, and c = 27/4 = 6.75 is already the last
passing box.** Re-derived from `GATE_c13_2_PAPER_GATE_2026-10-16.md` §5:

`50(1+2t) + 50(t²+t) ≤ 2·1727` ⟺ `t² + 3t + 1 ≤ 69.08` ⟺ **`t ≤ 6.886298`**

| centre | upper edge | `50(t²+3t+1)` | slack |
|---|---|---|---|
| 27/4 = 6.75 | 6.8125 | 3392.38 | **+61.62 PASS** |
| **55/8 = 6.875** | 6.9375 | 3497.07 | **−43.07 FAIL** |

**Gate-2 does not use the panel enclosure at all** — it uses the uniform
`‖Λ₀‖ ≤ 50/1727` derivative route. So the midpoint generator, the 405× add-on
campaign and Tier-3 move it **by zero steps**. That is not a criticism of those
pieces; it is a statement about which gate they serve.

**And the fix is already scoped and cheap.** `GATE2_BOXLOCAL_SCOPE_2026-10-16.md`
concluded, and I re-confirm: *"the 6.886 ceiling is the `L = 1` threshold, not a
limit of the method — and passing it needs no new mathematics."* With a
box-local bound the Gate-2 load peaks at **0.347 against a budget of 2** — 5.8×
headroom at the worst point — and **never binds again up to the hard cap.**

---

## Q1 — Gate-1 margins. MEASURED, and the answer is a hybrid

I parsed all twelve landed `c=27/4` segment files (6 range-brick, 6 midpoint)
theorem by theorem and normalised both schemes onto `nodeR`.

| seg | u-range | M | range-brick + | range-brick − | midpoint | winner |
|---|---|---|---|---|---|---|
| 1 | [0, .25] | 24 | 2.1344e−3 | 7.1936e−4 | **2.4414e−4** | midpoint |
| 2 | [.25, .5] | 24 | 8.7764e−4 | 8.1640e−4 | **2.4414e−4** | midpoint |
| 3 | [.5, .75] | 30 | 3.1012e−4 | 3.0378e−4 | 3.0518e−4 | tie |
| 4 | [.75, 1] | 30 | **9.7020e−5** | **3.6015e−5** | 3.0518e−4 | range |
| 5 | [1, 1.25] | 72 | **1.5901e−5** | **8.8534e−6** | 7.3242e−4 | range |
| 6 | [1.25, 1.5] | 72 | **8.4852e−7** | **1.5222e−6** | 7.3242e−4 | range |

**The crossover is structural, not incidental. JUDGEMENT.** The midpoint error
is `M·h³/24` per panel with **M growing** (24→72, because the derivative bound
is taken over the whole segment), while the range-brick spread **shrinks** as
the integrand decays. By segment 6 midpoint is **863× worse**. Swapping
range-brick for midpoint everywhere makes the tail *much* worse.

### Gate-1 arithmetic. MEASURED

`budget = 2 Re ξ(c) − 1/4`, `cost = c²(dR + A) + c(dI + A)`, `A = 8.2e−7`:

| scheme (c = 27/4, budget 0.0797502) | cost | verdict |
|---|---|---|
| all range brick, old add-ons (3.32e−4) | 0.1866 | FAIL by 0.1069 |
| all range brick, new add-ons | 0.1693 | FAIL by 0.0896 |
| all midpoint, new add-ons | 0.1341 | FAIL by 0.0544 |
| **per-segment best, new add-ons** | **0.0470** | **PASS by 0.0327** |

> **Neither scheme alone closes Gate-1 at c = 27/4. The hybrid does, with 3.8×
> margin to spare.**

**At c = 13/2 the landed pilot passes at +0.0303** (verified against its own
arithmetic in `223354b9`'s chain). No hybrid is needed there and none is
available — the midpoint pack exists **only at c = 27/4**.

### A correction to my own step-4 note. MEASURED

`STEP4_M_BOUND_IS_THE_STORY_2026-10-18.md` estimated c=27/4 as "PASS by 0.0128"
by **assuming** the c=27/4 pack achieves c=13/2 enclosure quality — and flagged
that assumption as OPEN. **Now measured: it does not.** The c=27/4 range-brick
panel `dR` is **3.4359e−3 against c=13/2's 1.37445e−3 — 2.5× worse**, because
higher `c` means faster oscillation and wider per-panel min/max spread. So
range-brick alone *fails* at 27/4 and the optimistic figure was wrong. The open
item is now closed, in the pessimistic direction.

## Q2 — Tier-3 into the count. The mechanism is real; the quoted numbers conflate panels with boxes

**What Tier-3 actually buys. FACT, from the sharp identity (`223354b9`):**
`Λ₀ = 1/t² − (4/t²)(I₊+I₋)`, so `R = 1/t² − (4/t²)Re(I₊+I₋)` and
`I = −(4/t²)Im(I₊+I₋)`. Enclosing `R, I` to precision `δ` therefore needs the
*integrals* only to `δ·t²/4`:

| t | 6.5 | 6.75 | 10 | 13 | 14.5 |
|---|---|---|---|---|---|
| relaxation `t²/4` | 10.56× | 11.39× | 25.0× | **42.25×** | 52.56× |

Midpoint panel count scales as `ε^{−1/2}`, so a 42.25× relaxation is
**√42.25 = 6.5× fewer panels per box** at t=13.

**Two corrections. MEASURED / FACT:**

1. **"~70 R1 boxes with Tier-3 vs 151 with midpoint alone" conflates two
   quantities.** `151` is a **panel** count in my 2026-10-16 record (151 panels
   at t=13, 433 at t=14.5), not a box count. Tier-3 reduces **panels per box**;
   it does not reduce the **number of boxes**, which is set by the box radius
   `r = 1/16`. Whether `r` can grow under Tier-3 is **OPEN and unanalysed** —
   that would be the only route to fewer boxes. Applying the relaxation to the
   panel figures gives 151 → **23** at t=13 and 433 → **60** at t=14.5.
2. **Tier-3's midpoint is currently unpriceable.** Its integrand is `F″`, so
   midpoint quadrature on `F″·e^{icu}` needs `M = max|d²/du²(F″e^{icu}))|` —
   the **fourth** derivative of `F`. The tree has `F″` (`999aa8a5`) and nothing
   beyond. **Way around: range-brick on the `F″` integrand needs no `M` at
   all**, only min/max — and given that range-brick already wins on segments
   4–6, and `F″` decays faster still, that is the cheaper first move.

## Q3 — The sequenced march

| # | step | who | size | depends on |
|---|---|---|---|---|
| **0** | **Settle R1's reach — done in this note (§Q4.4)** | Legion | done | — |
| **1** | **Gate-2 box-local bound ("Tier 1")** — removes the 6.886 hard-coded ceiling. **THE UNBLOCK.** | **Acer** | ~200–400 L, hours | nothing |
| 2 | Gate-1 hybrid pilot at c=27/4 — seg 1–2 midpoint, seg 3–6 range brick | Legion | ~100–150 L | the 12 landed segment files |
| 3 | **c-parametric producer** — one generator taking `c`, emitting all ~12 files + the pilot | **Acer** | ~600–900 L | step 2 (fixes the per-segment recipe first) |
| 4 | The march, 6.875 → 13 | Acer | ~50 boxes × ~12 files ≈ 600 files | steps 1–3 |
| 5 | *Optional* Tier-3 carrier via **range-brick on `F″`** (no `F⁗`) | Legion | ~250–400 L | step 4's per-box cost being the binding constraint |

**Step 1 before anything else. JUDGEMENT.** Steps 2–5 all improve Gate-1, and
Gate-1 is not what is failing. Until step 1 lands, the march's reachable set is
`t ≤ 6.8125` — which is where it already is, so steps 2–5 would buy **zero
boxes**. Step 2 is still worth doing early because it fixes the per-segment
recipe that step 3's producer must emit, and because it is cheap.

**Step 5 is an efficiency play, not an unblock** — order it by whether step 4's
~600 files is the thing that hurts.

## Q4 — Blockers, ranked

1. **Gate-2's hard-coded 6.886 ceiling.** Blocks every box past 6.75. Free to
   remove, scoped 2026-10-16, needs no new mathematics. **Everything else is
   downstream of this.**
2. **The producer — the real cost driver. FACT.** Every `c` is hand-instantiated:
   **11–14 files per c across 7 c-values, eight separate c-hardcoded generator
   scripts** (`gen_fourier_panels_c*.py`, the midpoint one 692 L with `27/4`
   written into the emitted Lean in a dozen places), and **zero parametric
   modules** (`grep` for `variable (c : ℝ)` in `FourierPanels/`: empty).
   Marching 6.875 → 13 at `r = 1/16` is ~50 boxes ≈ 600 files.
3. **`F⁗` for a Tier-3 midpoint carrier.** Avoidable — use range-brick on `F″`.
4. **No c=13/2 midpoint pack.** Only matters if the hybrid is wanted at 13/2,
   and it is not: 13/2 already passes at +0.0303.

### And the 2026-10-16 OPEN item is now closed. FACT

That note flagged: *"If `R1` is right-edge positivity, it cannot reach 15 by
construction, because the sign changes at 13.9884… settle what `R1` needs before
spending weeks."* **Settled, from `R1R2R3_TARGET_REACHABLE:40–42`:**

* **R1** — `Re ξ(1+it) > 0` on **`[0, 13]`**
* **R2** — `Im ξ(1+it) > 0` on `[13, 14.5]`
* **R3** — `Re ξ(1+it) < 0` on `[14.5, 15]`

**R1 only has to reach 13**, and the decomposition deliberately routes around the
`Re ξ` zero at 13.9884 using `Im ξ`. So the sign change does **not** cap R1, the
`t = 13` march target is exactly right, and the worry that the march is "capped
below the target anyway" is resolved. **The weeks are not wasted on a capped
march** — but they are, today, spent on the wrong gate.

---

## Label summary

* **FACT:** the Gate-2 inequality and its 6.886 root, re-derived; the 27/4 and
  55/8 slacks (+61.62, −43.07); the 12 segment files' M values, intervals and
  8-panels-each structure; 11–14 files per c across 7 c-values with 8
  c-hardcoded generators and no parametric module; the R1/R2/R3 statements.
* **MEASURED (script shipped):** the per-segment width table and the 863×
  reversal at segment 6; the four Gate-1 cost rows at both c, with the hybrid the
  only passing one at 27/4; the c=27/4 range-brick `dR` being 2.5× worse than
  c=13/2's; the `t²/4` relaxation table; 151→23 and 433→60 panels.
* **JUDGEMENT:** that the midpoint/range-brick crossover is structural and the
  right scheme is per-segment; that step 1 must precede 2–5; that range-brick on
  `F″` is the cheaper Tier-3 carrier; the sizes in the task table.
* **OPEN / NOT established:** whether the box radius `r = 1/16` can grow under
  Tier-3 — the only route to *fewer boxes* rather than fewer panels, and
  unanalysed; the exact cost of the Gate-2 box-local bound (I am quoting my own
  2026-10-16 "hours", not a re-estimate); and I have not verified that a hybrid
  pilot assembles without friction — the two packs prove bounds about the *same*
  integrals, so it should be mechanical, but "should be" is not "is".
