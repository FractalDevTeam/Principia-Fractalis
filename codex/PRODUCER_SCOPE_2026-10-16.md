# Producer scoping: the binding lever is the quadrature ORDER, not the parametricity. My O(h⁴) assumption was wrong — measured p = 1.000.

**Date:** 2026-10-16 (Legion, measurements on Acer). Scoping for a build
decision. No Lean. Verification: `codex/producer_scope_verify.py`,
`codex/producer_tcost_verify.py`, `codex/producer_deriv_verify.py`. Labels FACT / MEASURED / JUDGEMENT / OPEN.

**Correction up front.** Last turn I recommended scoping the t-parametric
producer, resting on an assumption I flagged but had not checked: that the panel
scheme is Simpson-like `O(h⁴)`. **Measured: `p = 1.000` to four digits — first
order.** The scheme is a zeroth-order range enclosure. That changes the
arithmetic by ~70× and with it the recommendation. The producer is worth
building, but **it is not what makes the target reachable.**

**VERDICT: the producer is necessary-but-insufficient; the quadrature order is
the binding lever — and it is FAVOURABLE.** Measured with real derivative
constants, a certified **Simpson** rule needs **27 panels at `t = 13` and 48 at
`t = 14.5`** — fewer than the 48 in use today — against **13,205 / 98,988** for
the current zeroth-order scheme. A hard-end box drops from ~2M lines to ~4k.
**The architecture is not at its limit; its quadrature rule is.**

---

## 1. What the object is — exact definition

**The producer.** A theorem schema

> `∀ t ∈ [t₀, t₁],  L(t) ≤ (completedRiemannZeta₀ (1+it)).re ≤ U(t)`

with `L, U` **explicit rational-coefficient functions of `t`** (not numeric
literals), proved by:

1. a fixed panel decomposition of `u ∈ [0, 3/2]` into `N` panels;
2. per panel, a **2-D** interval enclosure of the integrand
   `g(u,t) = (e^{u/2}+1)·ω₃(e^u)·cos(tu/2)` over `u ∈ [a,b] × t ∈ [t₀,t₁]`,
   contributing `h·[L_panel, U_panel]` by `intervalIntegral.integral_const`;
3. the existing three add-ons — residue on `[3/2, 5]`, analytic tail beyond 5,
   ω-gap — carried unchanged in form.

**Measured cost model** (the central quantitative result of this note):

> **`W(N, r) ≈ 0.1858/N + 3.504e−3 · r`**

where `W` is the total enclosure width, `N` the panel count, `r` the t-halfwidth
the single enclosure covers. The first term is the `u`-part, the second the
price of parametricity.

**What it replaces.** Today each box regenerates a bespoke panel pack: 6
segments × 1226 lines + 3280 lines of assembly ≈ **11.5k lines per box**, with
per-panel bounds emitted as numeric literals for one hard-wired `c`.

## 2. The three flags, closed by measurement

### 2a. `O(h⁴)` — **WRONG. Measured `p = 1.000`.** MEASURED

The generator (`gen_fourier_panels_c51_8.py:493, 691-702`) emits per panel

```
(width : ℝ) * (L : ℝ) ≤ ∫ … ≤ (width : ℝ) * (U : ℝ)
```

via `intervalIntegral.integral_const`, with `L,U` the integrand's **range** on
the panel (critical-point enumeration for cos/sin). That is a **zeroth-order
range enclosure**: per-panel error `≈ h·(max−min) ≈ |g'|h²`, summed over `N =
L/h` panels gives **total `O(h)`**.

| panels | h | enclosure width | ratio |
|---|---|---|---|
| 12 | 0.12500 | 1.149482e−02 | — |
| 24 | 0.06250 | 5.747410e−03 | 2.000 |
| 48 | 0.03125 | 2.875349e−03 | 1.999 |
| 96 | 0.01562 | 1.437674e−03 | 2.000 |
| 192 | 0.00781 | 7.188410e−04 | 2.000 |

Exponent per doubling: `1.000, 0.999, 1.000, 1.000`. **First order, flat.**
(48 panels is the current geometry, width 1/32. My proxy reads 2.88e−3 against
the file's panel-only 1.70e−3 — same order, factor 1.7, from exact
critical-point enumeration being tighter than dense probing. The *scaling* is
what matters and it is robust.)

**Consequence.** Required panels per box:

| budget | `O(h)` (now) | `O(h²)` | `O(h⁴)` |
|---|---|---|---|
| `t = 13`, B = 1.407e−05 | **13,207** | 796 | 195 |
| `t = 14.5`, B = 1.877e−06 | **99,001** | 2,180 | 323 |

At ~153 Lean lines per panel (7356 lines / 48 panels, measured), `O(h)` means
**~2M lines per box at t=13 and ~15M at t=14.5.** That is the end of the current
architecture, independent of everything else.

### 2b. The three-axiom bar — the hard-wiring **is** there to keep `norm_num` closed, and parametricity is **cheap**. FACT + MEASURED

**The hard-wiring is deliberate.** Per-panel `L,U` are numeric literals computed
offline for one `c`; the emitted proof discharges arithmetic by `norm_num` on
concrete rationals (`hwidth : (b:ℝ) − (a:ℝ) = (width:ℝ) := by norm_num`), and
the cos/sin critical-point enumeration is for the fixed argument `(51/16)·u`.
The generator's own header says the *only* mathematical difference from the
`c=25/4` generator is that argument — i.e. the existing "parametricity" is
copy-paste, one generator per `c`.

**Can a parametric producer hold the bar? Yes in principle** — it stays pure
`Fraction` arithmetic with `norm_num`-discharged inequalities, now on
rational-coefficient *functions* rather than literals. Nothing about it needs
`native_decide` or an axiom. **But it is a rewrite of the emission layer, not a
parameter change** (see §4 for the specific obstacle).

**And the t-penalty is small.** Measured at `c = 13`, 48 panels:

| r | W(48,r) | t-part |
|---|---|---|
| 0 (pointwise) | 3.871335e−03 | — |
| 0.0005 | 3.873088e−03 | 1.752e−06 |
| 0.002 | 3.878344e−03 | 7.009e−06 |
| 0.008 | 3.899371e−03 | 2.804e−05 |
| 0.03 | 3.976460e−03 | 1.051e−04 |

Linear in `r`, **`C₂ ≈ 3.504e−03`**. At `r = 1/16` the penalty is `2.2e−04` —
**6% of the current enclosure.** So going parametric costs almost nothing in
tightness. **It simply does not address the `u`-part, which is the whole
problem.**

### 2c. Panel widths past `t = 6.5` — they **grow**. MEASURED

| c | enclosure width (48 panels) | vs c=51/8 |
|---|---|---|
| 6.0 | 2.838760e−03 | 1.00× |
| 6.375 | 2.875349e−03 | 1.01× |
| 6.5 | 2.887995e−03 | 1.02× |
| 8.0 | 3.070006e−03 | 1.08× |
| 10.0 | 3.364727e−03 | 1.19× |
| 13.0 | 3.871335e−03 | 1.36× |
| 14.5 | 4.144106e−03 | 1.46× |

Faster `cos(tu/2)` oscillation widens every panel's range. **The `c=51/8` width
does not carry; the earlier box counts are optimistic by 1.2–1.5× in the
enclosure**, which feeds proportionally into panel count.

## 3. What the producer buys, quantitatively — **not the target**. MEASURED

Solving `W(N,r) ≤ B` for the largest affordable `r`:

**At `t = 13`, B = 1.407e−05:**

| panels N | u-part `0.1858/N` | r affordable | t-width covered |
|---|---|---|---|
| 8,928 | 2.081e−05 | **none** | u-part alone busts B |
| 20,000 | 9.291e−06 | 1.364e−03 | 2.727e−03 |
| 50,000 | 3.716e−06 | 2.954e−03 | 5.909e−03 |
| 200,000 | 9.291e−07 | 3.750e−03 | 7.500e−03 |

**At `t = 14.5`, B = 1.877e−06:** `none` at 8,928, 20,000 **and** 50,000; only
at 200,000 panels does `r = 2.705e−04` become affordable.

**Read that carefully.** Even at 200,000 panels per enclosure, one enclosure
covers a t-width of `7.5e−03` at `t=13`. Covering `[12,13]` would take ~133 such
enclosures. **Boxes-to-target does not improve on 5960/390 at all** — the
producer changes the per-box *authoring* cost (regenerate 11.5k lines →
instantiate one theorem), which is real but second-order, and leaves the panel
count untouched.

**What does buy the target is the order:**

| | `O(h)` → `O(h²)` | `O(h)` → `O(h⁴)` |
|---|---|---|
| panels at t=13 | 17× fewer | 68× fewer |
| panels at t=14.5 | 45× fewer | 307× fewer |

> **The producer makes each box cheap to author. The quadrature order makes each
> box possible at all. Only the second is load-bearing.**

## 4. Failure modes, named exactly — OPEN

1. ~~Higher-order rules need derivative bounds, and the constants may eat the
   gain.~~ **MEASURED, AND THE RISK DOES NOT MATERIALISE — see §4a.** This was
   the one I expected to bite. It does not.
2. **mathlib may have no certified trapezoid/Simpson with remainder.** Building
   one to the three-axiom bar is its own project, though it is one reusable
   lemma rather than per-box work.
3. **The 2-D critical-point enumeration is a genuine rewrite.** `cos(tu/2)`'s
   critical points *move with `t`*, so the existing 1-D `_k_range_for_cos` /
   `_half_k_range_for_sin` logic does not lift; the enumeration becomes a
   2-parameter problem. This is the specific obstacle behind §2b's "rewrite, not
   a parameter change".
4. **The add-ons alone bust the budget — by 66× — before any panel work.**
   Current add-on total is `231/279841 + 1/10⁶ + 1/10⁴ = 9.2647e−04` against a
   `t=13` budget of `1.407e−05` (**66× over**) and a `t=14.5` budget of
   `1.877e−06` (**494× over**). Even after the free 32.8× residue fix
   (→ 2.51e−05) the **ω-gap at `1e−04` alone is 7× the t=13 budget.** So all
   three add-ons need real tightening: residue to ≲1e−06 (the 28-piece
   subdivision reaches 1.061e−06), ω-gap from 1e−04 to ≲1e−06 (100×), analytic
   tail from 1e−06 to ≲1e−07. **None of this is optional and none of it is the
   producer.**
5. **Per-box line count does not fall even in the best case.** At `O(h⁴)`'s
   195–323 panels and ~153 lines/panel, a box is ~30–50k lines — **3–4× the
   current 11.5k**, because today's 48 panels are far coarser than the target
   needs. The producer's authoring win is what offsets this.

## 4a. The decisive measurement: Simpson makes a box **cheaper than it is today**. MEASURED

Classical remainders on `[0, 3/2]` with `N` panels: trapezoid
`≤ 0.28125·M₂/N²`, Simpson `≤ 0.0421875·M₄/N⁴`.

| t | `max\|g\|` | `max\|g''\|` | `max\|g⁗\|` | crude `t⁴/16` |
|---|---|---|---|---|
| 6.375 | 8.643e−02 | 6.702e−01 | 2.876e+01 | 103.2 |
| 13.0 | 8.643e−02 | 3.194e+00 | 1.713e+02 | 1785.1 |
| 14.5 | 8.643e−02 | 4.086e+00 | 2.398e+02 | 2762.8 |

**`M₄` comes in ~10× below the crude `t⁴/16` bound**, because `ω₃(e^u)` decays
so fast that the large-`u` region — where `cos`'s derivatives are largest —
contributes almost nothing. The feared `t⁴` blow-up is real in form but small in
size.

**Panels needed, with real constants:**

| t | budget B | `O(h)` now | trapezoid | **Simpson** |
|---|---|---|---|---|
| 13.0 | 1.407e−05 | 13,205 | 253 | **27** |
| 14.5 | 1.877e−06 | 98,988 | 782 | **48** |

Gains: trapezoid **52× / 127×**, Simpson **493× / 2055×**. Per-box line counts
at ~153 lines/panel:

| t | `O(h)` | trapezoid | **Simpson** |
|---|---|---|---|
| 13.0 | 2.02M | 39k | **4k** |
| 14.5 | 15.15M | 120k | **7k** |

> **Simpson needs 27 panels at `t = 13` and 48 at `t = 14.5` — fewer than the
> 48 in use today — while meeting budgets 186× and 1397× tighter. A box at the
> hard end becomes ~4–7k lines against today's 11.5k.** The architecture is not
> at its limit; its quadrature rule is.

## 5. Recommendation — the programme is feasible, in this order

**Build the certified Simpson rule first. It is the whole ballgame.** One
reusable lemma (`∫` over a panel vs. the Simpson value, remainder
`(b−a)h⁴/180·max|f⁗|`), then a `max|g⁗|` bound for the specific integrand.

Priority stack, with measured multipliers:

| # | lever | buys | status |
|---|---|---|---|
| 1 | **certified Simpson** | 493×–2055× panels; boxes get *cheaper* than today | essential, favourable |
| 2 | **add-on tightening** (§4.4) | the add-ons are **66× over budget at t=13** before any panel work | essential, mostly free |
| 3 | **Tier-3 decaying bound** | 15× box count (5960 → 390) | high value |
| 4 | **t-parametric producer** | cheap authoring per box; t-penalty only 6% | second-order |

With 1–3: **~390 boxes × ~7k lines ≈ 2.7M lines.** Large, but a real programme
— against 68.5M for the current architecture, which is not one.

**JUDGEMENT.** The answer to "scope the producer" is that the producer was the
wrong thing to scope, and the measurement says so cleanly: parametricity costs
6% and buys authoring convenience, while the quadrature rule costs one lemma and
buys three orders of magnitude. Had I measured the generator two turns ago, both
the Tier-3 priority and the producer recommendation would have come out
differently the first time. **The lesson is the one already in my notes and I
did not apply it: measure the artefact before pricing anything built on it.**

---

## Label summary

* **FACT (read in source):** the per-panel `width × [L,U]` emission via
  `intervalIntegral.integral_const`; `norm_num` on concrete rationals;
  critical-point enumeration at the fixed argument `(51/16)u`; the generator's
  own statement that only that argument differs between `c` generators; panel
  geometry 6 segments × 8 panels of width 1/32.
* **MEASURED (this session):** `p = 1.000` scaling over 12→192 panels;
  `W(N,r) ≈ 0.1858/N + 3.504e−3·r`; required panels 13,207 / 796 / 195 at t=13
  and 99,001 / 2,180 / 323 at t=14.5; the t-penalty table and `C₂`; the
  enclosure-width growth 1.00×→1.46× over `c ∈ [6, 14.5]`; the affordable-`r`
  tables; ~153 Lean lines per panel.
* **JUDGEMENT (mine):** that the quadrature order is the binding lever and
  parametricity is second-order; that the `t⁴` constant in `|g⁴|` is the main
  risk and the next thing to measure; that the 2-D critical-point enumeration is
  the specific rewrite obstacle; the recommendation to measure before building.
* **MEASURED (§4a):** `max|g''|` = 0.670 / 3.194 / 4.086 and `max|g⁴|` = 28.76 /
  171.3 / 239.8 at `t` = 6.375 / 13 / 14.5 — the latter ~10× below the crude
  `t⁴/16`; Simpson panel counts 27 and 48; per-box line counts 4k and 7k.
* **NOT established:** whether mathlib has a certified Simpson-with-remainder
  (and if not, the cost of building one to the three-axiom bar); whether a 2-D
  critical-point enumeration can be made exact in `Fraction` arithmetic; the
  `max|g⁴|` bound as a *proved* rational bound rather than a measured maximum.
