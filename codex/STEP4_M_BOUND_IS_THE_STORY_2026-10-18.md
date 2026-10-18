# Step-4 chain closure: the midpoint file as landed is 14–42× LOOSER than the range brick, not 3–25× tighter — the M bound is the entire story (3000 vs a true 1.377). And c=27/4 is closed by the two add-on fixes, not by midpoint.

**Date:** 2026-10-18 (Legion). Measurement. No Lean written for this note
(the add-on changes it motivates landed separately as `4f21f035`). Labels
**FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**. Scripts:
`codex/step4_verify.py`, `codex/step4_gate1_c27_4.py`.

---

## VERDICT

**Neither of Rio's two branches, as posed.**

* **Not "yes, route to Acer for full segment generation":** the midpoint file as
  landed is **14.3× looser** (plus side) and **42.4× looser** (minus side) than
  the range bricks it replaces. Generating 5 more segments of it would make
  every enclosure worse.
* **Not "no, range-brick stands and the C² layer is infrastructure":** that
  writes off a scheme whose only defect is a crude constant. With the provable
  `M = 7.5` the same file would be **30.5× tighter**, and with the true
  `M = 1.377`, **166× tighter**.

> **The decision is not midpoint-vs-range-brick. It is "fix the M bound",
> which is a 2178× reduction sitting in one lemma.**

**And the question's own premise is answered elsewhere:** Gate-1 at c=27/4 is
closed by the two one-line add-on tightenings (`4f21f035`), with no midpoint
work at all. **MEASURED:** FAILS by 0.0045287 before them, PASSES by 0.0007489
after.

---

## 1. Three corrections to the brief

### 1a. There is no c=27/4 pilot box. FACT

`PF/Analytic/PilotBoxes/` contains `R1_c13_2_…`, `R1_c25_4_…`, `R1_c49_8_…`,
`R1_c51_8_…`, `R1_c53_8_…` — **and no `c27_4`**. The only c=27/4 artefacts are
panel files (`Seg01..Seg06Range`, `Seg01Midpoint`, `CoreDefs`,
`MidpointPanelDemo`). So "does Gate-1 close at c=27/4" has no landed Gate-1 to
evaluate; what can be measured is what a c=27/4 box *would* need, which is §3.

### 1b. `0.0143` is the c=13/2 shortfall, not c=27/4's. MEASURED, reproduced

Provenance: `codex/GATE_c13_2_PAPER_GATE_2026-10-16.md:19, 81, 128` — *"At
current enclosure quality the c=13/2 box FAILS Gate 1 by ≈ 0.0143"*, *"slack =
−0.01432572"*.

Re-derived independently from `2 Re ξ(c) − 1/4` and the c=51/8-era enclosure
(`dR = 2.6217e−3`, `dI = 1.8874e−3`): **shortfall at c = 6.5 = 0.014327** —
matching the note to five digits. **At c = 27/4 the same enclosure gives
0.052441**, 3.7× larger.

**And there is a trap here worth naming, because it is almost certainly what
caused the conflation:** the c=13/2 box's *shortfall* under the old enclosure
(−0.014327) and its *margin* as landed (+0.014139) are numerically almost
identical and differ only in sign. They are different quantities at different
enclosure qualities. My model reproduces the landed margin to all seven printed
digits (`+0.0141387`), which is what validates the arithmetic used below.

### 1c. "Midpoint is 3–25× tighter" is false as landed. MEASURED

The two files are directly comparable — both cover `u ∈ [0, 0.25]` with 8
panels of width 1/32 — but **they integrate different functions**:

* `Seg01Range`: `nodeR_fourier_plus_at_c27_4_N3 u = (e^{u/2}+1)·ω_N3(e^u)·cos(3.375u)`
* `Seg01Midpoint`: `f_plus u = Σ_{n<3} fourier_plus_term(27/4,n,u) = (e^{u/2}+1)·[Σ_{n<3} 2e^{−π(n+1)²e^u}]·cos(3.375u)`

and since `ω_N3(x) = Σ_{m=1..3} e^{−πm²x}`, **`f_plus = 2·nodeR`**. Verified
numerically at u = 0, 0.125, 0.25: ratio `2.000000` exactly.

> **The Midpoint file's header states this backwards** — *"Equal to
> `nodeR_fourier_plus_at_c27_4_N3 u / 2` via definitional unfolding"*. It is
> `nodeR` that equals `f_plus/2`. A factor-4 error for anyone who trusts the
> comment and compares the two files. **The Lean is correct; the comment is
> inverted.**

Normalising both onto `nodeR`:

| panel | range-brick width | midpoint/2 width | ratio |
|---|---|---|---|
| 0 | 2.9127e−4 | 3.8147e−3 | 13.1× |
| 3 | 2.8505e−4 | 3.8147e−3 | 13.4× |
| 7 | 2.1029e−4 | 3.8147e−3 | 18.1× |
| **segment, plus** | **2.1344e−3** | **3.0518e−2** | **14.3× worse** |
| **segment, minus** | **7.1936e−4** | **3.0518e−2** | **42.4× worse** |

**Both schemes are correct** — each encloses the true integral (checked against
a high-precision quadrature):

| side | true `∫₀^0.25` | range-brick | midpoint/2 |
|---|---|---|---|
| plus | 0.013586657 | [0.012532499, 0.014666919] ✓ | [−0.001674589, 0.028842989] ✓ |
| minus | 0.000196954 | [−0.000143373, 0.000575986] ✓ | [−0.015062065, 0.015455513] ✓ |

**There is no bug.** But on the minus side the midpoint enclosure
`[−0.0151, +0.0155]` does not even determine the **sign** of a quantity whose
true value is `1.97e−4`.

### 1d. The line count, and a correction to my own prior estimate

186 L/panel confirmed (1489 L / 8 panels), against the range brick's ~153
(1226 L / 8). **1.22× more lines — Rio's 1.2× is right.**

**My own `MIDPOINT_LINES_PER_PANEL_2026-10-17` estimated ~80 L/panel. That was
wrong by 2.3×.** It measured a demo panel with the M-bound `sorry`'d and the
minus side absent, then doubled it. **The lesson is the one already in the
ledger from the `O(h⁴)` miss: a measurement taken on an incomplete artefact
prices the wrong object.** The honest figure is 186.

---

## 2. The M bound is the entire story. MEASURED

The file uses `M = 3000` (`:63`), giving a per-panel error of exactly
`3000·(1/32)³/24 = 3.814697265625e−3` — matching the file's literal to the last
digit, and **identical on every panel**, which is why every ratio above is flat.

| `M` | per-panel half-width on `nodeR` | vs range brick |
|---|---|---|
| **3000 — as landed** | 1.9073e−3 | **13.1× worse** |
| 229.1 — break-even | 1.4566e−4 | 1.0× |
| **7.5 — provable from the existing `termM` machinery** | 4.7684e−6 | **30.5× tighter** |
| **1.3773 — the true `max\|f''\|` on [0,0.25]** | 8.7566e−7 | **166.3× tighter** |

True second derivatives, measured on a 401-point grid:
`max|f_plus''| = 1.3773`, `max|f_minus''| = 0.2917`. **So `M = 3000` is crude by
2178×**, and the midpoint scheme is on the wrong side of break-even by 13.1×
purely because of it.

**JUDGEMENT: Rio's "3–25× tighter" is the right order for the *provable* M
(30.5×) and understates the true one (166×). What it does not describe is the
landed file.** The gap between the claim and the artefact is one `norm_num`-class
numeric lemma — the very one my earlier note flagged as *"~15–20 L of
`exp(-A) ≤ 1` + `π ≤ 4` + `exp(1/32) ≤ 2` arithmetic"* and which was left at the
crude value.

---

## 3. Does Gate-1 close at c = 27/4? MEASURED

Gate-1 as the pilots write it is `c²·R_ub_f + c·I_ub_f ≤ 3/4`, and identically
`c²R + c·I = 1 − 2 Re ξ(c)` — **verified to all printed digits at c = 6.5**
(`0.6412918324` both sides, with `R = Re Λ₀(1+ci)`, `I = Im Λ₀(1+ci)`). So the
budget for enclosure error plus add-ons is `2 Re ξ(c) − 1/4`:

* c = 13/2: budget **0.10870817**
* c = 27/4: budget **0.07975022**, weights `c² = 45.5625`, `c = 6.75`

Holding the panel enclosure at the **current best** (the landed c=13/2 pilot:
panel-only `dR = 1.3745e−3`, `dI = 6.3521e−4`):

| configuration | cost | verdict |
|---|---|---|
| current add-ons, range-brick | 0.0842789 | **FAIL by 0.0045287** |
| **+ the two one-line add-on fixes** | **0.0790013** | **PASS by 0.0007489** |
| + residue `ln k` subdivision | 0.0671317 | PASS by 0.0126185 |
| current add-ons, **midpoint as landed (M=3000)** | 0.8943165 | **FAIL by 0.8145663** |
| two fixes + midpoint at provable M = 7.5 | 0.0142839 | PASS by 0.0654663 |

**So:**

1. **The two add-on fixes close c=27/4 by themselves** (+0.00075 — thin but
   real). They are landed in `4f21f035`.
2. **The residue subdivision makes it comfortable** (+0.0126).
3. **Midpoint as landed would lose c=27/4 catastrophically** — by 0.81, more
   than ten times the entire budget.
4. **Midpoint at a fixed M is worth a lot, but not here** — it buys margin
   c=27/4 does not need. Where it will be needed is t ≳ 10, where the panel
   term dominates (`codex/ADDON_SCOPE…`: the add-on architecture floors at 32.7%
   of budget at t ≈ 14.5, leaving the panels to supply everything else).

---

## 4. Recommendation

**Do not generate the remaining 5 midpoint segments yet, and do not write off
the C² layer.** Fix `M` first. The order:

1. ✅ **The two add-on fixes** — landed (`4f21f035`); c=27/4 now closes.
2. **Tighten `M_sum_le` from 3000 to ≤ 7.5** on both sides of the existing
   `Seg01Midpoint` file — one numeric lemma, the file's only real defect.
   Re-measure the segment widths: the prediction is **30.5× tighter than range
   brick**, and it is falsifiable from the same two scripts.
3. **Only then** decide on full segment generation, with the 186 L/panel cost
   known and a measured tightness in hand.
4. Fix the two inverted comments (`f_plus = nodeR/2` in `Seg01Midpoint`'s
   header; the same file's *"AND SHORTER per panel"*, which is 1.22× false).

**One next action: tighten `M` from 3000 to 7.5 in
`Seg01Midpoint_c27_4_2026_10_17.lean`.** Everything else about the
midpoint-vs-range-brick decision is downstream of that one number, and the
decision cannot be made honestly until it is measured rather than assumed.

---

## Label summary

* **FACT (from source):** no c=27/4 pilot box exists; the two integrand
  definitions and `ω_N3`'s form; `M := 3000` at `:63` and the per-panel error
  literal; 1489 L / 8 panels and 1226 L / 8 for the range brick; the
  `0.0143` provenance lines in `GATE_c13_2_PAPER_GATE`; the Midpoint header's
  inverted `/2` claim and its "SHORTER per panel" claim.
* **MEASURED (scripts shipped):** `f_plus/nodeR = 2.000000` at three points; the
  per-panel and per-segment width tables (14.3× / 42.4× worse); both schemes
  enclose the true integrals; `max|f_plus''| = 1.3773`, `max|f_minus''| =
  0.2917`, so M=3000 is crude by 2178×; break-even M = 229.1; 30.5× at M=7.5 and
  166.3× at the true M; the identity `c²Re + c·Im = 1 − 2Re ξ` to all printed
  digits; the landed c=13/2 margin `+0.0141387` reproduced; the c=13/2 shortfall
  `0.014327` reproduced to five digits; the c=27/4 table above.
* **JUDGEMENT (mine):** that the decision is "fix M", not
  midpoint-vs-range-brick; that Rio's 3–25× describes the provable M and not the
  artefact; that my own ~80 L/panel estimate was wrong because it priced an
  incomplete artefact; the recommended order.
* **OPEN / NOT established:** that `M ≤ 7.5` is actually provable in the ~15–20 L
  my earlier note guessed — **unbuilt, and it is the number this whole
  recommendation rests on**; whether a c=27/4 panel pack assembled from the 6
  Range segments really achieves the c=13/2 enclosure quality (assumed, since no
  c=27/4 box exists to measure); and the c=27/4 `+0.00075` margin is thin enough
  that a worse-than-assumed panel pack could still fail it.
