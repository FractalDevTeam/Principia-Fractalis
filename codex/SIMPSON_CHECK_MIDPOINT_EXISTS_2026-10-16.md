# Simpson check: mathlib has nothing — but **this repo already has a general, kernel-clean composite O(h²) rule**. Don't build; wire.

**Date:** 2026-10-16 (Legion, probes on Acer). The mathlib check requested
before the Simpson build. No new Lean. Verification: `codex/midpoint_probe.lean`
+ its output. Labels FACT / MEASURED / JUDGEMENT.

**ANSWER: do not build Simpson. Wire `composite_midpoint_error`, which has been
sitting in `PF/Analytic/XiQuadrature.lean` since 2026-07-25, is fully generic,
and is kernel-clean.** It gives `O(h²)` with the sharp `/24` constant — **179
panels at `t = 13` and 554 at `t = 14.5`, i.e. 74× and 179× fewer than the
current scheme.** Build cost for the rule itself: **zero.**

---

## 1. mathlib: nothing. FACT

Searched the pinned tree (`.lake/packages/mathlib/Mathlib`, **6860 `.lean`
files**) for `simpson | newton-cotes | quadrature | trapezoid | trapezium`:

> **0 files.**

mathlib at `v4.24.0-rc1` has no numerical quadrature rule of any order. It has
the raw ingredients — `taylor_mean_remainder_lagrange`,
`taylor_mean_remainder_bound` (`Analysis/Calculus/Taylor.lean:318, 382`),
`norm_integral_le_of_norm_le`, `integral_sub`, `integral_const` — but no rule
with a remainder. **So the "import it" branch of the order is closed.**

## 2. But the repo already built one — and it is generic. FACT (machine-checked)

`PF/Analytic/XiQuadrature.lean` (779 lines, 2026-07-25, Hardy route milestone
B4). Its own header advertises *"the composite midpoint rule with the SHARP
`/24` constant, and explicit `C²` bounds for the truncated integrand."*

```lean
theorem composite_midpoint_error {f f' f'' : ℝ → ℝ} {a b M : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hf  : ∀ x ∈ Set.uIcc a b, HasDerivAt f  (f'  x) x)
    (hf' : ∀ x ∈ Set.uIcc a b, HasDerivAt f' (f'' x) x)
    (hM  : ∀ x ∈ Set.uIcc a b, |f'' x| ≤ M) :
    |(∫ x in a..b, f x)
        - (b - a)/n * ∑ i ∈ Finset.range n, f (a + (b - a)/n * (i + 1/2))|
      ≤ M * (b - a) ^ 3 / (24 * n ^ 2)
```

**Machine-checked this session:**

* `midpoint_rule_error` — axioms `[propext, Classical.choice, Quot.sound]`
* `composite_midpoint_error` — axioms `[propext, Classical.choice, Quot.sound]`
* probe `EXIT=0`

**It is fully general** — arbitrary `f, f', f'', a, b, M, n`, no Hardy
hypotheses anywhere in the signature. This is exactly the missing lever, already
at the bar.

**JUDGEMENT:** this is the standing rule earning its keep. The campaign existed;
the quadrature layer was built three months ago for a different route and never
wired into the Fourier panel generator, which has been emitting zeroth-order
range bricks the whole time.

## 3. What it buys — MEASURED

With the sharp constant, `n ≥ √(M·(b−a)³/(24·B))` and `b − a = 3/2`:

| t | `max\|g''\|` | budget B | panels now `O(h)` | **midpoint** | gain |
|---|---|---|---|---|---|
| 13 | 3.1944 | 1.407e−05 | 13,205 | **179** | **74×** |
| 14.5 | 4.0857 | 1.877e−06 | 98,988 | **554** | **179×** |

For comparison, Simpson would need 27 and 48 — a **further** 6.6× / 11.5× — but
requires building a rule that neither mathlib nor the repo has.

> **Midpoint captures 74–179× of the available 493–2055× for zero build cost on
> the rule. Simpson is the last 7–12×, at the cost of a new certified rule.
> Take the free 74× first.**

## 4. What is actually left to do

The quadrature layer is done. The remaining work is the **C² layer for the
Fourier integrand**, and the existing file is a working template for it.

**Generic and reusable as-is** (no Hardy specialisation):

* `abs_sub_taylor1_le` (:260) — the Taylor-1 step
* `midpoint_rule_error` (:335), `composite_midpoint_error` (:399)
* **`hasDerivAt_mul3` (:540)** — product rule for a three-factor product

**Hardy-specific, and the template to copy** (`thetaTerm` = the θ-integrand
`2u^{−3/4}cos((t/2)log u)·e^{−πn²u}`): `thetaTerm/D1/D2/M` (:493–534),
`hasDerivAt_thetaTerm` (:601), `hasDerivAt_thetaTermD1` (:607),
`abs_thetaTermD2_le` (:650), and the sum-level
`hasDerivAt_truncated_integrand` / `abs_thetaTermD2_sum_le` (:737, :754).

**The Fourier integrand has the same shape** — a three-factor product
`(e^{u/2}+1) · e^{−πn²e^u} · cos(tu/2)` — so `hasDerivAt_mul3` applies directly
and the work is mechanical: define `fourierTerm/D1/D2/M`, prove two `HasDerivAt`
lemmas and one `|D2| ≤ M` bound, sum over `n ≤ 3`. By analogy with :493–758,
**~250 lines, one time, not per box.**

Then the generator changes from emitting per-panel range bricks to emitting a
midpoint sum plus one `composite_midpoint_error` application per segment — which
should *reduce* lines per panel, since a midpoint needs one point enclosure
rather than a critical-point range. **That per-panel line cost should be measured
on the first segment rather than assumed** (I have assumed line costs twice this
week and been wrong once).

## 5. Recommendation

1. **Wire `composite_midpoint_error`.** Free, kernel-clean, generic.
2. **Build the Fourier C² layer** on the `thetaTerm` template using
   `hasDerivAt_mul3`. ~250 lines, one time.
3. **Measure lines-per-panel on segment 1** before projecting any box cost.
4. **Revisit Simpson only if 179/554 panels is still too many** — it is the last
   7–12×, and it is the only piece that would be a genuine mathlib
   contribution. **JUDGEMENT: not now.**

**And the add-ons still bust the budget 66× at `t = 13` independently of all of
this** (`PRODUCER_SCOPE_2026-10-16.md` §4.4) — residue to ≤1e−6, ω-gap 100×,
tail 10×. Quadrature order and add-on tightening are both necessary; neither
substitutes for the other.

---

## Label summary

* **FACT:** 0 hits for quadrature/Simpson/Newton-Cotes/trapezoid across 6860
  mathlib files at the pin; the mathlib ingredients that do exist and their
  locations; `composite_midpoint_error`'s full statement and its generality; the
  generic/Hardy-specific split of `XiQuadrature.lean` by line number.
* **MEASURED (machine-checked this session):** both midpoint theorems print
  exactly `[propext, Classical.choice, Quot.sound]`; probe `EXIT=0`; panel counts
  179 and 554 from the measured `max|g''|` = 3.1944 / 4.0857.
* **JUDGEMENT (mine):** that wiring beats building; that Simpson is the last
  7–12× and not now; that lines-per-panel must be measured not assumed.
* **NOT established:** the per-panel line cost under midpoint emission; whether
  the Fourier `|D2| ≤ M` bound closes as cleanly as the θ one did (the `e^u`
  inside the exponential is the one structural difference from `thetaTerm`, and
  it is the thing to check first).

---

# ADDENDUM 2026-10-16 — the flagged `|D2| ≤ M` unknown is RESOLVED, favourably, and the panel counts IMPROVE

§5 flagged one structural unknown: whether the Fourier `|D2| ≤ M` bound closes
as cleanly as the θ one, given that the `e^u` sits **inside** the exponential
(`e^{−πn²e^u}` versus `thetaTerm`'s `e^{−πn²u}`). Checked.
Verification: `codex/d2_bound_verify.py`.

**Answer: it closes, and it is not close to marginal.** MEASURED

## The concern, and why it evaporates

Differentiating `e^{−πn²e^u}` twice brings `(πn²e^u)²`, which at `u = 3/2` is
large. But it is multiplied by the exponential itself, which is smaller by tens
of orders:

| n | `(πn²e^u)²` at u=3/2 | `e^{−πn²e^u}` | product |
|---|---|---|---|
| 1 | 1.982e+02 | 7.679e−07 | 1.522e−04 |
| 2 | 3.172e+03 | 3.477e−25 | 1.103e−21 |
| 3 | 1.606e+04 | 9.281e−56 | 1.490e−51 |

**The `n ≥ 2` terms are numerically irrelevant; only `n = 1` near `u = 0`
matters.** The polynomial growth from the chain rule never competes with the
exponential it multiplies.

## The provable majorant, per segment

With `A = e^{u/2}+1`, `P = πn²e^u`, taking `|cos|,|sin| ≤ 1`, each algebraic
factor at the segment's right end and the exponential at its left end:

  `|g''| ≤ Bmax · [ A'' + A·P(P+1) + A·t²/4 + 2A'·P + A'·t + A·P·t ]`

summed over `n ≤ 3`. Measured against the true maximum, per segment:

**At `t = 13` (budget 1.407e−05):**

| segment | measured `M₂` | majorant | loose | panels |
|---|---|---|---|---|
| [0, 1/4] | 3.1944e+00 | 1.1133e+01 | 3.5× | 56 |
| [1/4, 1/2] | 1.9258e+00 | 5.9973e+00 | 3.1× | 41 |
| [1/2, 3/4] | 3.4315e−01 | 2.5921e+00 | 7.6× | 27 |
| [3/4, 1] | 2.6312e−01 | 8.3654e−01 | 3.2× | 16 |
| [1, 5/4] | 2.6713e−02 | 1.8370e−01 | 6.9× | 8 |
| [5/4, 3/2] | 5.8126e−03 | 2.4350e−02 | 4.2× | 3 |
| **total** | | | | **151** |

**At `t = 14.5` (budget 1.877e−06): total 433 panels** (163/119/78/44/21/8 by
segment, majorant 2.8–12.2× loose).

## The numbers improve on §3

§3 reported 179 / 554 from a *global measured* `max|g''|`. A **provable
per-segment** majorant does better, because the segments where the exponential
has already crushed everything need almost no panels (3 and 8 on `[5/4, 3/2]`):

| t | §3 (global, measured) | **this addendum (per-segment, PROVABLE)** | one global majorant | gain vs `O(h)` |
|---|---|---|---|---|
| 13 | 179 | **151** | 781 | **87×** |
| 14.5 | 554 | **433** | 2211 | **229×** |

So the revised gains are **87× and 229×**, up from the 74×/179× reported in §3
— and these are with a bound that is *provable*, not merely measured.

**Note the contrast with a single global majorant** (781 / 2211): applying the
rule **per segment with a local `M`** is worth ~5× over one interval. The
generator already works per segment, so this costs nothing to adopt.

**Headroom left:** the measured-`M` floor is 78 / 235 against the provable 151 /
433, so a tighter majorant (taking `A` and `P` at their true sup rather than the
right endpoint, or splitting the first segment) would recover ~2× more. **Not
needed — 151/433 already clears the budget.**

## What this closes and what it leaves

* **CLOSED:** the `e^u`-in-the-exponential concern. The bound closes with room,
  and the majorant is a routine six-term product-rule expansion — no new
  technique beyond `hasDerivAt_mul3` (:540).
* **STILL OPEN, unchanged:** the per-panel *line* cost under midpoint emission
  (§5.3 — measure on segment 1, do not assume), and the add-on tightening, which
  remains 66× over budget at `t = 13` independently of all quadrature work.

**JUDGEMENT:** with this resolved, the midpoint route has no remaining
structural unknown — only engineering. The recommendation in §5 stands and is
now better supported: wire `composite_midpoint_error`, build the Fourier C²
layer per segment on the `thetaTerm` template, and leave Simpson alone.
