# THE SPECTRAL-GAP NUMBERS ARE BLOCKED BY A CONFLICT IN OUR OWN ADJUDICATIONS

**Date:** 2026-10-31
**Scope:** read-only audit plus one unrelated repair (appJ, commit `84c93dba`).
No spectral-gap number was changed anywhere. ch07 and ch24 untouched.

---

## 0. THE BLOCKER — read this before editing any α or Δ number in ch21

Two dated adjudications in this repo give **opposite prescriptions** for
`λ₀(H_NP) = 0.1330222423` and `Δ = 0.0891219046`.

| artifact | date | prescription |
|---|---|---|
| `codex/BOOK_LEAN_SUPERSESSION_MAP_2026-10-05.md` §1, §4 | 2026-10-05 | **SUPERSEDED.** λ₀(NP) → 0.1681764182 (+26.4 %), Δ → 0.0539677287 (−39 %). Names ch21 explicitly: "both Δ values — yes — internally inconsistent." Prescribes "replace the superseded numeral with the certified one, cite the closed form symbolically, and recompute any downstream number that scales with Δ." |
| `PF/MillenniumSixReductions.lean:3436ff` | dated notice | agrees: both were "retracted as artifacts of a pre-v3.3.1 buggy spectral-truncation pipeline." |
| `ch21:1169–1189` `\manuscriptcorrection` | **2026-10-27** | **LIVE THREE-WAY SPLIT.** Treats 0.0891 as an unreconciled candidate alongside 0.054 and 0.131, citing `PF/TuringEncoding/SpectralGapInconsistencyAnalysis.lean`, which states it "does NOT discharge the inconsistency." |

**Resolution by the project's own rule** — ch34's addendum: *"the ledgers govern,
audits bind, deployed artifacts outrank committed ones, and no status is reported
from a layer above the evidence for it."* The 2026-10-27 in-chapter correction
and `INSTRUCTIONS_FOR_EVERY_AI_2026-10-21` both **postdate** the supersession
map. **The three-way record governs; the numbers do not get substituted.**

Recorded here because the supersession map is still in `codex/` giving the
opposite instruction, and a reader who finds it first will do the wrong thing.
Under the supersession framing a substitution is a repair; under the governing
framing it is **vandalism of a deliberately maintained open record**. One of us
will act on the wrong one unless this is settled in writing.

### What the three values are

`PF/TuringEncoding/SpectralGapInconsistencyAnalysis.lean` (2026-06-06, zero
project axioms) defines all three and proves them pairwise distinct with
quantified separations:

```lean
Delta_emp = 891219046 / 10000000000   -- IBM hardware measurement
Delta_gm  = 131 / 1000                -- manuscript golden-modulation estimate
Delta_lcf = 54 / 1000                 -- Lean closed form
```

Its honest-scope note: *"the Lean closed-form is the only one with rigorous
derivation; the IBM empirical and manuscript golden-modulation estimates are
external anchors with their own published-math sources. The inconsistency is a
known research-frontier open question."* Resolution requires discharging
`FrameworkNPSelfAdjointnessReductionToQuadratic`.

Certified values, recomputed at 30 dps from `PF/SpectralGap.lean:21,25` and
`PF/IntervalArithmetic.lean:274,306`:

| | value | bracket |
|---|---|---|
| λ₀(P) = (π/10)/√2 | 0.222144146907918 | `< 1e-10` |
| λ₀(NP) = (π/10)/(φ+¼) = 2π/(5(3+2√5)) | 0.168176418229524 | `< 1e-9` |
| Δ_lcf | 0.053967728678394 | |
| ratio √2/(φ+¼) | 0.757059866620 | `ratio_bracket_3digit`: (0.756, 0.758) |

appK's identity `Δ·√2·(φ+¼) = (π/10)((φ+¼)−√2)` closes on Δ_lcf **exactly**,
both sides `0.1425718917554`.

---

## 1. VERIFIED ch21 DEFECTS — three confirmed, one refuted

Independently checked twice: by me at 40 dps, and by an adversarial agent
instructed to refute rather than confirm. **Line numbers below are from the
committed file** (md5 `339d6a29280e`); an earlier pass reported them +37 to +45
high because the buffer still held reverted edits.

### CONFIRMED, and already adjudicated by the chapter itself

**D1 — `ch21:1428`.** Inside `\begin{intuitive}`:
`$\lambda_0(H_{NP}) = \frac{\pi(\sqrt{5}-1)}{30\sqrt{2}} \approx 0.133$`.
The expression is `0.091528422127295583`; the printed numeral is wrong by
`0.0414716`. This is the *exact* error `ch21:474` already corrects ("Prior
editions stated π(√5−1)/(30√2) ≈ 0.1330 … the formulas evaluate to ≈ 0.0915"),
fixed at :469 and missed here. No correction covers the block.

**The naive repair is wrong and must not be applied.** The whole block is valued
on the empirical triple — 0.222 at :1421, 0.133 at :1428, Δ = 0.089 at :1433 —
so changing 0.133 → 0.0915 makes :1433 false (it would become 0.131). **Repair
the block as a unit or not at all.** Three separable defects live here: the
numeral; the bare `=` asserting a conjectured closed form as an identity, which
:451/:474/:988/:1603 all deny; and the golden angle below.

**D2 — `ch21:986`,** inside `thm:ground-states`: "matching to within numerical
precision" after displaying λ₀(NP) `\stackrel{?}{=}` 0.0915 against the
empirical 0.1330222423. False by `0.041493820`. The `?` scopes the
*identification*, not this separate factual assertion. The identical correction
note sits at **both** :988 and :1603 — there is no coverage asymmetry — and the
chapter asserts on :986 and denies on :988, two lines apart.

**The worse defect is in the `\begin{proof}` at :991–999, which is OUTSIDE the
theorem so note :988 does not reach it.** It displays
`|0.1330222423 − π(√5−1)/(30√2)| < 1e-10`, false by a factor of **414,938,202**.
A false inequality inside a proof environment, uncovered.

**D3 — `ch21:448`,** inside `\begin{observation}[Golden Ratio Emergence]`:
`\frac{0.1330222423}{0.2221441469} \approx 0.5988854382`. True quotient
`0.598810475793814`; printed differs by `7.4962e-5`, agreeing to 5 decimals
while shown to 10.

**Provenance established.** 0.5988854382 is a stranded literal from the
pre-correction edition, where it sat on the *sine-ratio* display:
`ARCHIVE/2026-05-XX-historical/.../ch21_p_vs_np.tex:637` preserves
`|0.798635510/0.847127424| ≈ 0.5988854382`. The 2026-05-18 pass repaired the
sine site to 0.9427 and **relocated the condemned digits onto :448**. The kernel
condemns them twice — `manuscript_sine_ratio_ne_5988` and
`manuscript_sqrt5_identity_ne_5988` (`MillenniumSixReductions.lean:2118,2153`).
All 6,084 ordered quotients of ch21's 78 literals were tested: nothing else
produces it. The note at :451 **endorses** the number ("the empirical ratio
0.5988 remains the authoritative measurement"); the note at :545 that calls
0.5988 wrong is 97 lines away and about a different quantity.

### REFUTED — my claim, and it was a category error

**`± 10^{-10}` is NOT an overclaim.** All 15 sites frame it as the chapter's own
truncation ("Relative Error" column headers at :394–400 and :426–432; "we
compute … numerically"; "the extrapolated limit is"). The kernel's 1e-9 bracket
is on `0.168176418230`, a *different number* — a bound on one cannot overclaim
the other. λ₀(P) is bracketed at exactly 1e-10, the precision printed. And
`ch21:1664` already states the refuting reading: *"The 10⁻¹⁰ precision is the
stability of a truncation computation, not an error bound on a limit."*
`grep` for `certif|verifi|machine|kernel|formal` in the relevant windows: zero
hits outside the dated correction notes.

---

## 2. FOUND IN PASSING, NOT ACTED ON

**A φ symbol collision.** ch21 uses φ as the golden ratio 1.618 in 20 places
(`φ+1/4 ≈ 1.868` at :1200) and as an "angle" 1.9416 in 4 (:343, :525, :1429, and
a **subsection heading** at :1447). The kernel requires the ratio reading:
π/(10(φ+¼)) = `0.168176418229530` with 1.618 but `0.143346268935` with 1.9416,
which fails `lambda_0_NP_precise`. Three of the four angle sites are bare. The
stated "golden angle" (√5−1)π/2 = `1.941611038725` rad = 111.246° is just π/φ;
the actual golden angle is 2π/φ² = `2.399963229729` rad = 137.508°.

**`ch21:1613`,** Conclusion, no note:
`λ₀(H_NP)/λ₀(H_P) = sin(π/√2)/sin(π/√2+φ) = (√5−1)/3`, labelled "(verified
numerically)". Three mutually distinct numbers chained as one: `0.932958278642`,
`0.412022659167`, `0.598810475794`. Kernel-refuted at
`manuscript_sine_identity_both_sides_wrong`.

**A guard-scope defect in the kernel.** `manuscript_sine_ratio_bracket` proves
0.94 < |0.798635510/0.847127424| < 0.95 — it brackets **the division of two
wrong sine values**. True sines: `0.795693201567`, `−0.852810772690`; true
|ratio| `0.932958278642`, so the "corrected" 0.9427 is itself off by `9.799e-3`.
Correct bracket, wrong scope.

---

## 3. WHAT WAS NOT DONE, AND WHY

A 40-site substitution of the certified pair for the printed pair was written,
applied to a scratch copy, diffed against HEAD, and **reverted without landing**.
It broke six sentences, and the Lean settles the matter against it:

```lean
-- PF/Ch09QuantumEnhancementRefutationAttempt.lean:108
noncomputable def Delta_ch09 : ℝ := 891219046 / 10 ^ 10
```

The printed gap is hardcoded there **on purpose**, so six axiom-free theorems —
`exponent_at_1000_gt_27`, `etaEnhance_1000_gt_1e11`,
`etaEnhance_1000_ne_claimed`, `etaEnhance_strictMono`,
`claimedEta_lt_etaEnhance_ten` — refute the chapter's own η claim *at that
value*. At Δ_lcf, η(1000) = `2.308e7`, so `etaEnhance_1000_gt_1e11` would stop
being a statement about this chapter. **Overwriting the number desynchronises the
manuscript from its own machine-checked refutation.**

All eight touched files were restored and verified byte-identical to HEAD.

## 4. THE ONE DECISION NEEDED

Does `BOOK_LEAN_SUPERSESSION_MAP_2026-10-05` govern, or the 2026-10-27 three-way
record? Until that is written down, every numeric edit in ch21 is a downgrade
under one of the two framings. Dates and the governing rule say the three-way
record wins; that reading needs to be ratified in the supersession map itself, or
the map needs a superseded-by header, so the conflict stops being live.

D1–D3 are repairable **without** settling it, since none requires choosing a Δ —
but D1 must be repaired as a block, not as a numeral.
