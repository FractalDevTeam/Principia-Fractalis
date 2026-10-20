# The c-parametric producer is built — and it must not be run in a loop yet, because the box *geometry* is the wall now, not the per-box cost

**Date:** 2026-10-20 (Legion, generated locally, built on Acer).
Labels **FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**.
Scripts: `codex/gen_box.py`, `codex/gen_box_part2.py`.

---

## HEADLINE

**The producer works end to end: one command emits a complete 16-file box pack
at any centre, and the pack built at `c = 55/8` compiles kernel-clean with the
unconditional `R1` box as its headline — 426 theorems, zero non-three-axiom.** But the measurement that had to come first says the march should not
be run with it as specified:

> With the fixed `r = 1/16`, `L = 1`, `Mc_lb = 1/8` box shape, Gate-1 itself
> fails at `c ≈ 7.22`, so the producer can emit **three** more boxes and no
> more. And covering `[6.75, 13]` at `L = 1` would take **193 boxes**, where a
> box-local `L` takes **3**.

So the producer takes `r` and `L` as *parameters*, not constants, and refuses
to emit a pilot whose Gate-1 fails. Running it 193 times would industrialise
the wrong thing.

---

## 1. Why the fixed box shape does not survive. MEASURED

`R1_box_centered_of_lb` needs `L·r < Mc_lb ≤ Re ξ(1+ic)`. And `Re ξ(1+ic)`
decays to zero at its first zero `13.98838`:

| `c` | `Re ξ(1+ic)` | `≥ 1/8`? | `r = 1/16` ok? |
|---|---|---|---|
| 6.75 | 0.164875 | yes | yes |
| 7.5 | 0.125095 | **borderline** | yes |
| 8 | 0.101916 | no | yes |
| 9 | 0.063978 | no | **borderline** |
| 10 | 0.036811 | no | no |
| 13 | 0.002509 | no | no |

* `Mc_lb = 1/8` — the constant every landed pilot uses — **fails past
  `c = 7.50194`. FACT** (solve `Re ξ(1+ic) = 1/8`).
* `r = 1/16` **fails past `c = 9.04600`.**
* Gate-1 `c²·R_ub + c·I_ub ≤ 3/4` *is* exactly `Re ξ(1+ic) ≥ 1/8`, so this is
  not an artefact of the enclosure — it is the box shape.

The landed `c = 13/2` and `c = 27/4` pilots are both below 7.5, which is why
nothing has complained yet.

## 2. The real cost driver is `L`, not the enclosure. MEASURED

Box count to cover `[6.75, 13]`, as `∫ L(c)/(2·Re ξ(c)) dc`:

| `L` | boxes |
|---|---|
| uniform `L = 1` (what Gate-2 proves) | **193** |
| box-local `L = 1.25·\|d/dt Re ξ\|` | **3** |

`L = 1` is **17.6× too loose at `c = 6.75` and 261× at `c = 13`**. One box at
`c = 7` could carry radius `2.22` — covering `[4.78, 9.22]` in a single box —
instead of `1/16`.

## 3. No better *constant* fixes it: `ξ'` cancels. MEASURED — this is the key negative

`ξ' = ((2s−1)Λ₀ + s(s−1)Λ₀')/2`, and the two pieces very nearly cancel:

| `t` | `\|term₁\|/2` | `\|term₂\|/2` | triangle sum | `\|ξ'\|` | overestimate |
|---|---|---|---|---|---|
| 6.75 | 0.098843 | 0.042446 | 0.141289 | 0.056961 | 2.5× |
| 9 | 0.096516 | 0.064227 | 0.160743 | 0.032823 | 4.9× |
| 11 | 0.087211 | 0.073235 | 0.160446 | 0.014396 | 11.1× |
| 13 | 0.076369 | 0.072503 | 0.148872 | 0.004141 | **36.0×** |

So the **best possible** triangle bound — using the *exact* `‖Λ₀‖` and
`‖Λ₀'‖`, not any rational relaxation — is `0.157–0.173` and **flat in `t`**.
It permits `r = 1/16` only to about `c ≈ 11.6`:

| `t` | best triangle `L` | `L` needed for `r=1/16` | ok? |
|---|---|---|---|
| 6.75 | 0.154083 | 2.638002 | yes |
| 11 | 0.170646 | 0.302566 | yes |
| 13 | 0.157097 | 0.040150 | **no** |

**JUDGEMENT.** This is the same disease as the Gate-2 reach I fixed in
`15ddbf2e`, one level up: a uniform bound standing in for a decaying quantity.
But the cure is different. Tightening `Λ₀`/`Λ₀'` constants cannot help, because
the loss is cancellation *between* the two terms, which the triangle inequality
destroys by construction. Closing it needs an **enclosure of `deriv edgeRe`
itself** — the same panel treatment `Re Λ₀` already gets — not a better
constant. That is the next real build, and it is worth ~60× on the march.

### Correction to my own first reading of this. MEASURED

I first wrote that `L = 1/4` was "available for free" because it sits above the
0.173 exact-value ceiling. **That is wrong** — 0.173 uses the *exact* `‖Λ₀‖`
and `‖Λ₀'‖`, not the constants that are actually proved. With what is in hand
today (Tier-3's `‖Λ₀‖ ≤ 2/t²` from `K = 1/4`, plus the log-weighted
`‖Λ₀'‖ ≤ 3/650`) the provable `L` is:

| `t` | 6.875 | 8 | 10 | 11 | 13 |
|---|---|---|---|---|---|
| provable `L` | 0.3385 | 0.4122 | 0.4638 | 0.4947 | 0.5798 |
| still loose by | 6.1× | 9.5× | 20.9× | 35.5× | 151× |

So the interim step is real but smaller than I claimed:

| `L` | boxes `[6.75, 13]` |
|---|---|
| `L = 1` (today) | 193 |
| **`L` provable now** (`2/t²` + `3/650`) | **102** |
| `L = 1.25·\|d/dt Re ξ\|` (needs the enclosure) | 3 |

A **1.9× win, not 4×.** And it is not sufficient on its own: past `c = 7.502`
the pilot's hardcoded `Mc_lb = 1/8` is itself unprovable, so `pilot_r1_hvalue_lb`
needs a *parameterised* target as well. Both changes are needed before any
march past 7.5, and together they still leave ~100 boxes — which is why the
`deriv edgeRe` enclosure, not these, is the build that matters.

## 4. A reproducibility gap in the midpoint generator. FACT

`scripts/gen_fourier_panels_c27_4_midpoint.py` hardcodes `M := 24` and the
whole M-bound proof at `T = 1/4` (lines 194, 207, 263, 331, 402, 561, 588),
while computing per-panel errors from `M_for_seg` = 24/30/72. The six landed
files carry **six different `(M,T)` pairs**:

| seg | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| `M` | 24 | 24 | 30 | 30 | 72 | 72 |
| `T` | 1/4 | 1/2 | 3/4 | 1 | 5/4 | 3/2 |

**So the generator reproduces exactly one of its own six outputs.** The other
five must have been hand-edited.

The hardcoding is in **two** places, and I only found the second by building:

1. `seg_preamble_mp` — `M := 24` and the three per-`n` lemmas at `T = 1/4`.
2. **`emit_midpoint_panel_block`** — every panel emits
   `have h_bu : u ≤ (1/4 : ℝ)` and
   `abs_fourier_*_termD2_sum_le c (1/4) 3`. For segment 2 the panels live on
   `[1/4, 1/2]`, so `u ≤ 1/4` is **false** and `linarith` fails. My first
   producer run fixed (1) and not (2); `Seg01` built clean and `Seg02` failed
   with 32 errors. Both are now specialised with asserted substitution counts. Nothing landed is *wrong* — each file's `M`
and `T` are internally consistent, and I verified every landed `M` is a valid
bound — but the generator is not the source of truth, which would have bitten
the march hard.

The producer closes it by computing `M` from `(c, T)` with **the same coarse
bounds the emitted Lean proof supplies**:

`π ≤ 4`, `exp(T/2) ≤ 2`, `exp(T) ≤ 2`, `exp(−π(n+1)²) ≤ (1/23)^{(n+1)²}`

so the emitted constant is provable by construction rather than by luck.
**Validation:** at `(27/4, 1/4)` the formula gives per-`n` targets
`[19, 1, 1]` — *exactly* the landed constants — and a total of `8.4315`, which
matches the generator's own comment *"symbolic upper bound ≈ 8.44"*. **MEASURED.**

It also shows `M = 24` stays valid for `T ≤ 1/2` all the way to `c = 13`
(`M̂ = 20.09` there), so the midpoint tier needs no re-derivation across the
march — only re-emission.

## 5. What the producer emits. FACT

`python3 gen_box.py --c 55/8 --out <dir>` → 16 files:

| component | files | mechanism |
|---|---|---|
| `CoreDefs` | 1 | textual port from `c = 13/2` |
| `Seg0{1..6}Range` | 6 | existing generator, retagged (already parametric) |
| `Seg0{1,2}Midpoint` | 2 | `(c,T,M,targets)`-parameterised emission |
| `Assemble…HYBRID` | 1 | parses the emitted panels, halves midpoint |
| residue / residue-tight / analytic-tail / ω-gap | 4 | textual port |
| `R1_…_HYBRID` (gate composition) | 1 | generated |
| `R1_…_pointwise_UNCONDITIONAL` | 1 | ported edge-identity chain |

Measured at `c = 55/8`: hybrid plus `[0.0138908614, 0.0147522731]`, minus
`[0.0005357044, 0.0013067406]`, **Gate-1 `0.70630364` vs `3/4`, margin
`+0.04369636`**.

### How far the producer actually reaches, measured by running it. MEASURED

Gate-1 *is* `Re ξ(1+ic) ≥ 1/8`, so it fails on its own once `Re ξ` drops —
independently of enclosure quality. Running the producer across centres:

| `c` | Gate-1 lhs | margin | |
|---|---|---|---|
| 27/4 = 6.75 | 0.69130112 | `+0.05869888` | landed |
| 55/8 = 6.875 | 0.70630364 | `+0.04369636` | PASS |
| 7 | 0.72272444 | `+0.02727556` | PASS |
| 57/8 = 7.125 | 0.73719385 | `+0.01280615` | PASS |
| 115/16 = 7.1875 | 0.74431281 | `+0.00568719` | PASS |
| **29/4 = 7.25** | 0.75135357 | **`−0.00135357`** | **producer refuses to emit** |
| 15/2 = 7.5 | 0.77871494 | `−0.02871494` | refuses |

**So the producer delivers exactly three new boxes** — `55/8`, `7`, `57/8` —
extending R1 coverage from the current frontier `t ≤ 6.8125` to `t ≤ 7.1875`,
and then stops. The guard fires on its own; I did not have to discover the
limit by a failed Lean build.

The three thresholds line up consistently, which is the check that the
diagnosis is coherent:

| what fails | at `c` |
|---|---|
| Gate-1 *with* the hybrid enclosure | **≈ 7.22** |
| `Mc_lb = 1/8` exactly (`Re ξ = 1/8`) | 7.50194 |
| `r = 1/16` (`Re ξ = 1/16`) | 9.04600 |

The enclosure costs ~0.28 of reach against the exact value — small. The box
*shape* costs everything after that. **Three boxes is the whole value of this
producer until `(Mc_lb, r, L)` are parameterised in the Lean too.**

### Self-test: it reproduces the known-good centre. MEASURED

Re-running the producer at `c = 27/4` — the centre whose box was hand-built and
is already machine-checked (`c5458211`, `6b21de74`) — gives

| | Gate-1 margin |
|---|---|
| landed, hand-built | `+0.05710243` |
| producer, regenerated | **`+0.05869888`** |

*Better*, and the whole difference is accounted for: the producer computes
`M = 21` (the least multiple of 3 above its target sum) where the hand-built
file carries `M = 24`. That shrinks each midpoint panel's error by
`24/786432 − 21/786432 = 3.814697e−6`, so `R_ub` and `I_ub` each drop by
`16·err/2 = 3.051758e−5`, improving Gate-1 by
`c²·ΔR + c·ΔI = 0.00159645`. Observed difference: `0.00159645`. **Agreement to
eight decimals**, so the producer is reproducing the landed arithmetic exactly
and the only delta is its tighter `M`.

### Guards the producer enforces

* **Refuses to emit the pilot if Gate-1 fails** at that centre.
* Asserts `r < 1/8` (needed for `L·r < Mc_lb` with `L = 1`) and `c + r ≤ 14`
  (the Gate-2 reach of the log-weighted bound).
* Asserts `T ≤ log 2`, which is what `exp(T) ≤ 2` in the emitted proof needs.
* Asserts the 48 panels tile `[0, 3/2]` contiguously with no gap.
* The assemble recomputes the Gate-1 margin independently and the producer
  asserts the two agree to `10⁻⁹`.
* Every numeric retag is anchored with negative lookaround on digits and dots,
  and asserted afterwards.

### Two retag hazards found by the build, now guarded

1. **`|((27:ℝ)/4)|`** — the digits there are followed by `:` not `/`, so the
   bare-fraction rule skipped them while rewriting the bare `27/4` on the same
   line, leaving the false `|((27:ℝ)/4)| = 55/8`. Now substituted explicitly.
2. **`exp((1:ℝ)/8)` vs `exp((1:ℝ)/4)`** — for `T = 1/2` the new `E = exp(1/4)`
   collides with the template's old `T̂ = exp(1/4)`, so an ordered in-place
   substitution clobbers one with the other. Routed through placeholders. The
   same collision exists in the `≤ Real.log 2` proof bodies and bit once.

---

## Label summary

* **FACT (read from source):** the six range generators differ only in
  `C_VALUE`/`C_HALF` and the `c13_2` token; `CoreDefs` and the four add-ons
  differ only in the phase; the midpoint generator's hardcoded `M := 24`/`T = 1/4`
  against its six differing outputs; `fourier_plus_termM`'s closed form;
  `R1_box_centered_of_lb` being generic in `(c, r, L, Mc_lb)`.
* **MEASURED:** `Re ξ(1+ic) = 1/8` at `7.50194` and `= 1/16` at `9.04600`; the
  first zero at `13.98838`; box counts 193 vs 3; the `L = 1` looseness 17.6×→261×;
  the `ξ'` cancellation table; the best-triangle ceiling `0.157–0.173`; `M̂`
  reproducing `[19,1,1]` and `8.4315`; the `c = 55/8` enclosure and margin
  `+0.04369636`.
* **JUDGEMENT:** that the producer must take `r` and `L` as parameters; that
  the next build is a panel enclosure of `deriv edgeRe`, not a better constant;
  that the provable-`L` interim step (193 → 102 boxes) is worth taking but is
  not close to sufficient.
* **BUILT END TO END (c = 55/8, a centre never compiled before):** every one
  of the sixteen emitted modules compiles `rc=0`, zero errors —
  **426 `#print axioms` lines, zero `sorryAx` / `nativeDecide` / `ofReduceBool`**.
  The headline,

      PilotR1Box_c55_8_r1_16_pointwise_UNCONDITIONAL
        .pilot_r1_box_c55_8_r1_16_pointwise_UNCONDITIONAL
      depends on axioms: [propext, Classical.choice, Quot.sound]

  is `∀ t ∈ Icc (109/16) (111/16), 0 < (riemannXiEntire (1+it)).re` with **zero
  hypotheses** — i.e. **R1 on `[6.8125, 6.9375]`, the box the old Gate-2
  ceiling blocked**, produced by one command. Wall time strictly serial: ~7m30s
  per panel file, the four add-ons 42s total, assemble 54s, both pilots 41s;
  peak free RAM 9–11 GB of 15;
  and the provable-`L` figures are arithmetic from the constants in hand, not a
  Lean proof — `min(50/1727, 2/t²)` additionally needs `K_sum = 1/4` as a Lean
  theorem, which still wants `F₊″, F₋″ ≥ 0` (numerically true, unproved).
