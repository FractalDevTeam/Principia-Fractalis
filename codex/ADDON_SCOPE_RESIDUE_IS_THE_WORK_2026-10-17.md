# Add-on tightening for Gate-1: the ω-gap is the EASIEST of the three (2.3e17× of slack already proven, one `norm_num`), the residue is the only real work, t=13 is comfortable — and at the programme's true worst point, t≈14.5, the add-on architecture's own floor eats a third of the budget

**Date:** 2026-10-17 (Legion). Scoping. No Lean written. Labels **FACT** /
**MEASURED** / **JUDGEMENT** / **OPEN**. Scripts shipped:
`codex/addon_verify.py`, `codex/addon_rexi_audit.py`,
`codex/addon_perleg_verify.py`.

---

## VERDICT

**All three add-ons reach t = 13 with ~350–500 lines and no new mathematics;
two of the three are one-line changes. Four of the brief's five numbers need
correcting, and the real ceiling is not at t=13 at all.**

| Rio's brief | measured | status |
|---|---|---|
| Enclosure 186× tighter at t=13 | 186× | ✅ **correct** |
| Add-ons 66× over budget | **24.1×** | ❌ **stale** — 66× uses the retired `231/279841` residue |
| Residue 2-piece subdivision free, 32.8× | **18.4×**, and it leaves add-ons at **92%** of the t=13 budget | ❌ **wrong twice** |
| ω-gap needs 100×, "the hard one" | 100× correct; **2.3e17× already proven** — the *easiest* | ❌ **inverted** |
| Tail needs 10× | **8.83× free**; 1e−7 **not** reachable, 1.2e−7 is | ⚠️ **nearly right** |

**And the finding that reorders the lane:**

> **t = 13 is not the hard point. The programme's worst point is t ≈ 14.5
> (R2's far end / R3's start), where the add-on budget is 1.8429e−6 — 7.5×
> tighter than t=13. There, the add-on *architecture's own floor* is 32.7% of
> the budget. No subdivision, no constant-chasing, and no panel work gets below
> it, because the floor is the exact integral of a majorant that has already
> thrown away all oscillation via `|cos|, |sin| ≤ 1`.**

So: **the tightening Rio asked for is correct, cheap, and sufficient for t=13.
It is not sufficient for the `[−15,15]` target**, and the gap there is new
mathematics, not effort.

### A correction I made to myself before shipping

My first pass read the `t=14.5` row of `R1R2R3_TARGET_REACHABLE` as a sign
error, because `Re ξ(1+14.5i) = −5.591e−4` while the row records `+4.142e−4`.
**That reading was wrong and I withdrew it.** The row is labelled *"(R2 worst)"*
and R2 is an **`Im ξ`** fact; `Im ξ(1+14.5i) = +4.1418e−4`, exactly as
recorded. The note's own §2 already explains that the decomposition
deliberately routes around the `Re ξ` zero using `Im ξ`, and already records
that zero at `t = 13.9883806982`. **The only defect is that the table's column
header reads `Re ξ` where that row carries `Im ξ`** — a label, not a value.
I had drafted and applied a withdrawal patch to that note; it is reverted, and
the note is untouched apart from the one-line column clarification described in
§4. **Recorded because a wrong correction to a correct record is the more
dangerous error of the two.**

---

## 1. Rio Q1 — the three add-ons, exactly. FACT

All three enter `R_ub_f` **and** `I_ub_f` additively
(`R1_c13_2_…:55–58`), so an add-on total `A` costs `A·(c² + c)` of the budget.

| add-on | what it bounds | Lean source | current exported |
|---|---|---|---|
| **residue** | `∫_{3/2}^{5} f` — between the panel-pack cutoff `u=3/2` and the analytic-tail cutoff `u=5` | `ResidueBound_c13_2_three_halves_to_5_2026_10_16.lean` (433 L, 24 decls) | **`231/10⁶` = 2.31e−4** |
| **ω-gap** | `∫_{Ioi 0} \|f_full − f_N3\|` — Fourier modes past the `N=3` truncation, i.e. the `n ≥ 16` theta-tail | `R1_c13_2_…:79` (`epsOm`), `:570`, `:700–736` | **`1/10⁴` = 1e−4** |
| **analytic tail** | `∫_{Ioi 5} f` — beyond `U = 5` | `AnalyticTailBound_c13_2_2026_10_16.lean` (578 L) | **`1/10⁶` = 1e−6** |

Total **3.32e−4**.

**All three arguments are c-independent — FACT, quoted from the headers.**
Residue: *"The uniform-over-interval argument is c-independent: we use
`|cos|, |sin| ≤ 1`."* Tail: *"The analytic argument is c-independent since it
uses `|cos|, |sin| ≤ 1` to drop the frequency dependence."* The ω-gap's
`exp(−16π·exp u)` carries the mode gap 16, not `t`.

> **So add-on tightening is a ONE-TIME investment serving every box at every t.**
> That is a stronger argument for front-loading it than the one in the brief —
> and it is also why the shared `|cos|,|sin| ≤ 1` step is the shared ceiling (§4).

**Where the brief's 66× comes from. MEASURED.** The retired c=51/8 total was
`231/279841 + 1e−6 + 1e−4 = 9.2647e−4` → **67.2×** of the t=13 budget. The
c=13/2 pilot already carries `231/10⁶`, giving `3.32e−4` → **24.1×**. The pilot
documents the swap itself at line 76: *"2026-10-17: now recomputed from the
ACTUAL c=13/2 rational constants (`231/10⁶` residue). Margin is `+0.01414`,
not `+0.0050`."*

---

## 2. Rio Q2 — current bound, target, mechanism, per add-on

### 2a. ω-gap — 1e−4 → 1e−21, mechanism: retarget one `norm_num`

**MEASURED, and this inverts the brief.** The chain at `:700–736` proves

```
exp(-16π)·(1/(16π − 1/2) + 1/(16π))·(23/22)
   ≤ (1/10²⁰)·(1/47.5 + 1/48)·(23/22)      -- = 4.3790e-22
   ≤ 1/10⁴                                  -- h_numerical, by norm_num
```

| quantity | value |
|---|---|
| exact value of the bounded integral | **6.1833e−24** |
| what the chain **proves** | **4.3790e−22** |
| what it **exports** (`epsOm`) | **1.0000e−04** |
| slack discarded in the last step | **2.284e+17 ×** |

The file already contains `exp_neg_sixteen_pi_le : exp(-(16π)) ≤ 1/10²⁰` at
`:100`. **100× is needed; 2.28e15× is already proven.** Change
`epsOm := 1/10^4` to `1/10^21`, retarget `h_numerical`; `norm_num` closes it —
rational arithmetic. **No new mathematics. The easiest of the three by
seventeen orders of magnitude.**

### 2b. Analytic tail — 1e−6 → 1.2e−7, same mechanism

`AnalyticTailBound_c13_2_…:499` proves
`1150/(2904·6436343) + 1150/(3454·6436343) ≤ 1/10⁶`, left side **1.1326e−7**:
an **8.83×** free gain, one `norm_num` target.

**1e−7 is NOT reachable this way (1.1326e−7 > 1e−7); `12/10⁸` is.** The
distinction matters because the underlying analysis is already sharp:
`exp(−5π) = 1.5070e−7` vs the `1/23⁵ = 1.5537e−7` used — **1.031×**. Going
below ~1.1e−7 means moving `U = 5` outward: a new file, not a constant.

**At t=13 the tail floor is 0.8% of budget; at t=14.5 it is 6.1%. Do the free
change and stop.**

### 2c. Residue — 2.31e−4, the only real work

**The current bound evaluates its two factors at *different* endpoints. FACT.**
On `[3/2,5]`, `|f(u)| ≤ (e^{u/2}+1)·3·e^{−π e^u}`, and the file takes

* `e^{u/2}+1 ≤ 22` — the value at **u = 5** (header: *"loose — kept"*);
* `e^{−π e^u} ≤ e^{−14} ≤ 1/10⁶` — from the **left** endpoint, then rounded.

`g` is strictly decreasing on `[3/2,5]` (`g'/g = −13.74 … −465.79` at
`u = 1.5,2,3,4,5`, verified in `GATE_c13_2_PAPER_GATE`), so **both** factors
belong at the left endpoint.

| treatment | bound | gain | % of t=13 budget | % of t≈14.5 budget |
|---|---|---|---|---|
| current (mixed endpoint) | 2.3100e−4 | 1× | 1675% | 12535% |
| 1 piece, endpoint-correct | 2.5131e−5 | **9.2×** | 182% | 1364% |
| 2 equal pieces | 1.2566e−5 | **18.4×** | **91%** | 682% |
| 8 | 3.1430e−6 | 76.0× | 23% | 171% |
| 20 | 1.3509e−6 | 171× | 9.8% | 73% |
| 32 | 9.7677e−7 | 237× | 7.1% | 53% |
| **floor** (`∫g` exactly) | **4.8856e−7** | **473×** | 3.5% | **26.5%** |

**The brief's "2 pieces, 32.8× free" is wrong twice. MEASURED.** 32.8× was
measured against the *retired* `231/279841`; against the constant in force two
pieces give **18.4×**, and they leave the add-ons at **92% of the entire t=13
budget** — nothing for the panels. The opposite of "enough".

#### The mechanism to prefer: cut at `u = ln k`, not into equal pieces. MEASURED

Equal pieces need a fresh rational bound on `e^{−π e^{u_i}}` at each irrational
`u_i` — the real cost driver. **Cutting at `u_i = ln k` gives `e^u ≥ k` on each
piece, so `e^{−π e^u} ≤ e^{−kπ} ≤ (1/23)^k` through the house lemma
`exp_neg_pi_le_one_twentythird` that the file already imports.** Every piece is
then pure rational arithmetic with **zero new numeric constants**.

| design | residue | % of t=13 budget | new constants |
|---|---|---|---|
| `ln k` cuts, k = 4…148 (145 pieces) | **4.1016e−6** | **29.8%** | **none** |
| …first piece `[3/2, ln 5]` refined 40× | **7.1218e−7** | **5.2%** | a few `e^{−απ}`, α fractional |

and the cost is sharply concentrated: **the first piece alone is 92.6%** of the
total (3.7966e−6); piece `k = 10` onward is below 1e−12, so `k ≥ 11` collapses
into one geometric-series bound and only ~6 pieces need individual treatment.

**JUDGEMENT: this is the design to build.** 30% of the t=13 budget with no new
numeric machinery, and every further gain localised into one interval.

---

## 3. Rio Q3 — "is the ω-gap 100× reachable? what new mathematics?"

**Reachable, free, no new mathematics — the premise is inverted.** The ω-gap
has 2.3e17× of slack already sitting in the proof, thrown away by one
`norm_num`. 100× is ~15 lines.

**The hard add-on is the residue, and even it needs no new mathematics** —
subdivision of an existing majorant, which the corpus already calls *"semantics
only, no new math"*.

**New mathematics is needed in exactly one place, and it is not at t=13.** The
residue floor `4.8856e−7` is the exact integral of the **majorant**, which
discards all oscillation via `|cos|, |sin| ≤ 1`. Below it you must keep the
oscillation — a genuinely different argument. At t=13 that floor is 3.5% of
budget and irrelevant. **At t ≈ 14.5 the whole add-on architecture floors at
32.7% of budget, and that is where the new mathematics becomes mandatory.**

---

## 4. The real ceiling, per leg. MEASURED

The three sign facts (`R1R2R3_TARGET_REACHABLE:40–42`) use **different
quantities on different legs**:

* **R1** — `Re ξ(1+it) > 0` on `[0, 13]`
* **R2** — `Im ξ(1+it) > 0` on `[13, 14.5]`
* **R3** — `Re ξ(1+it) < 0` on `[14.5, 15]`

so the margin — and hence the add-on budget `margin(t)/(t²+t)` — is `Re ξ`,
then `Im ξ`, then `|Re ξ|`. **This is what routes the decomposition around the
`Re ξ` zero at `t = 13.9883806982`** (independently re-derived here, agreeing
with the note's §2 to 3.5e−11; `Im ξ` there is `+7.9e−4`, comfortably positive).

| leg | its worst t | margin | add-on budget |
|---|---|---|---|
| R1 | 13.000 | `Re ξ = 2.5094e−3` | 1.3788e−5 |
| R2 | 14.495 | `Im ξ = 4.1721e−4` | 1.8576e−6 |
| **R3** | **14.500** | **`\|Re ξ\| = 4.1418e−4`** | **1.8429e−6** ← global worst |

**The binding point for the whole `[−15,15]` target is t ≈ 14.5, at
1.8429e−6 — 7.5× tighter than t = 13.** Against it:

| configuration | add-on | % of t=13 | % of global worst |
|---|---|---|---|
| current | 3.3200e−4 | 2408% | 18015% |
| free ω+tail only | 2.3111e−4 | 1676% | 12541% |
| + residue `ln k` (no new consts) | 4.2149e−6 | **30.6%** | 229% |
| + first piece refined 40× | 8.2544e−7 | 6.0% | 44.8% |
| **architecture floor** (residue `∫g` + tail `U=5`) | **6.0182e−7** | 4.4% | **32.7%** |

**JUDGEMENT.** t=13 is comfortably reachable and the brief's instinct to
front-load the add-ons is right. But the `[−15,15]` target is **not** reachable
by tightening: at its worst point the add-on architecture cannot go below ~33%
of budget, leaving the panels at most ~67% where they need 186×–1397× of their
own. **The honest statement is that add-on tightening is necessary, cheap,
sufficient for t=13, and structurally insufficient for t=14.5.**

**One-line correction owed to `R1R2R3_TARGET_REACHABLE` (filed with this
commit):** the budget table's column header reads `` `Re ξ` = slack ``, but the
`t=14.5` row carries `Im ξ` (per R2). Value correct, header not. No withdrawal —
see the self-correction in the VERDICT.

**Also worth recording: the current add-ons do NOT bind at the landed pilots.**
At t = 6.75 they are 10.5% of budget, at 6.886 11.5%. This is preparatory work
for t ≈ 10–13, not a fire.

---

## 5. Rio Q4 — lines, difficulty, blockers

| add-on | lines | difficulty | blocker |
|---|---|---|---|
| **ω-gap** `1e−4 → 1e−21` | **~15** (1 `abbrev`, 1 `norm_num` target, Gate-1 recheck) | **trivial** | none |
| **tail** `1e−6 → 12/10⁸` | **~10** (1 `norm_num` target, recheck) | **trivial** | none; below 1.1e−7 needs moving `U=5` (new file) |
| **residue**, `ln k` design → 4.1e−6 | **~270–400**: general per-interval lemma (~120–180), ~6 explicit pieces at ~10–15 each, geometric tail `k ≥ 11` (~60–100), `integral_add_adjacent_intervals` chaining (~30) | **medium** | none mathematical |
| residue, first piece refined → 7.1e−7 | +~150–250 | medium | needs a few `e^{−απ}` bounds, α fractional |
| below the floor (only needed for t≈14.5) | **unscoped** | **research** | **must keep the oscillation; `\|cos\|,\|sin\| ≤ 1` is the ceiling** |
| pilot rewiring (3 constants → `R_ub_f`/`I_ub_f` → Gate-1 check) | ~40–60 **per pilot** | low | mechanical, ×6 if propagated |

**Total for a t=13-capable add-on stack: ~350–500 lines**, one new file plus
edits to two existing. **No new mathematics, no mathlib gap.**

**Calibration, measured not guessed:** the existing single-piece residue file is
**433 L / 24 decls**; `MIDPOINT_LINES_PER_PANEL` measures quadrature panels at
**~80 L/panel structural** against the range-brick's ~153. A residue piece is
strictly cheaper than a quadrature panel — no derivative witness, no midpoint
rule — which is why ~10–15 L/piece is right *once the general lemma exists*.
**OPEN: I have not built one piece to confirm it**, and that is the same
exposure that made the `O(h⁴)` estimate wrong by 70×.

**Risks, ranked.** (1) The per-piece numeric `e^{−π e^{u_i}}` bounds — removed
entirely by the `ln k` design, which is the reason to prefer it. (2) The
pilot-side recheck multiplies by pilot count; decide once whether to propagate
to all six c-values or only the live one. (3) Nothing else at t=13.

---

## 6. One next action

**Do the two one-line add-ons together: `epsOm 1e−4 → 1e−21` and the tail
`1e−6 → 12/10⁸`, then re-run the Gate-1 numeric check in the c=13/2 pilot.**
~25 lines, no new mathematics, converting 2.3e17× of already-proven slack into
real margin — after which the residue is 99.7% of the remaining add-on total
and the `ln k` subdivision has a single clean target.

---

## Label summary

* **FACT (quoted from source):** the three add-on roles and Lean locations;
  `231/10⁶` in force at c=13/2 and the pilot's own line-76 note on the swap; the
  mixed-endpoint structure of the residue bound and its *"loose — kept"* header;
  `exp_neg_sixteen_pi_le` at `:100`; the tail's `1150/(2904·6436343)+…` step at
  `:499`; c-independence of all three, quoted from two headers; the R1/R2/R3
  statements at `:40–42`; the 433 L / 24 decl and ~80 L/panel calibrations.
* **MEASURED (scripts shipped):** ω-gap exact 6.1833e−24, proven 4.3790e−22,
  exported 1e−4, slack 2.284e17×; tail proven 1.1326e−7, free 8.83×, 1e−7
  unreachable, `exp(−5π)` vs `1/23⁵` = 1.031×; the residue table (9.2× / 18.4× /
  … / floor 4.8856e−7 = 473×); the `ln k` design at 4.1016e−6 with no new
  constants, 92.6% of it in the first piece, 7.1218e−7 once refined; t=13 budget
  1.3788e−5 with the current total 24.1× over (stale 67.2×); the per-leg budget
  table and the global worst 1.8429e−6 at t=14.5; the architecture floor at
  32.7% of it; `Re ξ` zero at 13.9883806982; add-ons at 10.5% of budget at
  t=6.75.
* **JUDGEMENT (mine):** that c-independence is the real argument for
  front-loading; that the `ln k` subdivision is the design to build; that the
  tightening is sufficient for t=13 and structurally insufficient for t=14.5;
  the line estimates; that going below the residue floor needs an
  oscillation-keeping argument.
* **OPEN / NOT established:** I have not built a single residue piece in Lean, so
  ~10–15 L/piece is unconfirmed and is the number here most likely to be wrong;
  whether to propagate to all six pilots; the exact `e^{−απ}` constants the
  first-piece refinement needs; and whether an oscillation-keeping majorant can
  actually clear the t≈14.5 budget — I have shown the current architecture
  cannot, **not** that a better one can.
