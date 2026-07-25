# Interval Spike — girving/interval as the RH-arc certified-numerics engine

**Date:** 2026-07-24
**Purpose:** go/no-go gate from `HARDY_SCOPING_2026-07-24.md` — can the Ξ(14)<0<Ξ(15)
sign-change certificate be built kernel-clean (axioms exactly
`[propext, Classical.choice, Quot.sound]`, no `native_decide`) using
girving/interval (Geoffrey Irving's kernel-verified interval arithmetic,
https://github.com/girving/interval, Apache 2.0)?

## Verdict: GO-WITH-PORT

Kernel-clean end-to-end transcendental inequalities were demonstrated **on our exact
pin** (lean4 v4.24.0-rc1, mathlib `eed770a4`). The scoping doc's risk 1 ("no
kernel-acceptable certified-numerics path in the pinned mathlib") is **empirically
refuted**. Estimated total to the full Ξ certificate: **≈1.5–2.5 months** (vs 3–5
from scratch), axiom budget intact.

## Pins

| | lean-toolchain | mathlib rev |
|---|---|---|
| Ours (PF_Lean4_Code) | v4.24.0-rc1 | `eed770a434957369c6262aa3fb1d6426419016d4` |
| Upstream HEAD (`f4a3231`, 2026-01-20) | v4.27.0-rc1 | `725c803e` (master) |
| **Port base used** | `2eb9470` (v4.23.0-rc2, 2025-08-15) | — forced onto our pin |

No upstream commit sits on v4.24; no tags/releases. Port = `2eb9470` + toolchain/
lakefile repin + **~50 mechanical lines across 5 files** (removed-transitive-import
of `Mathlib.Tactic.Cases`; `Nat.floor_div_eq_div` moved to `Floor.Semifield`; core
`Nat.log2` redefinition; one `field_simp` and one cast-`rw` regression; one
`norm_num`-evaluates-`2^(2^63−1)` OOM fixed with `congr 1`). Full patch:
`codex/interval-port-2eb9470-to-v4.24.0-rc1.patch`. Three `EulerMaclaurin/*` files
left unfixed (not needed). Ported target set built green on our pin:
`Interval.Interval.{Exp,Sincos,Pow,Order,Pi,Sqrt,Division,Constants}`,
`Interval.Box.Exp`, `Interval.Tactic.Approx` — `Build completed successfully (2142 jobs)`.

## Axiom audit (the decisive datum)

`SpikeTest.lean` via `by approx` + `Interval.approx_lt` + `decide +kernel` — NOT the
`interval` tactic (which is documented to use `native_decide` and is BANNED here).
On BOTH upstream HEAD and our ported pin, all four test theorems
(π < 3.15; 2.7 < exp 1; 5.76 < exp 1 + exp(1/2) + exp(1/3); cos 1 < 0.5404):

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

Grep for `native_decide`/`ofReduceBool`/`trustCompiler`: **zero hits in the core
library**; only in `test/` and the convenience `Interval/Tactic/Interval.lean`
tactic (unused by us). Upstream self-polices via `test/axioms.lean` guard.

**Scaling probe:** 20 chained `exp` evaluations in one `decide +kernel` = 48s ⇒
≈2s marginal kernel cost per transcendental interval evaluation (64-bit software FP,
`exp_series_16`).

## API fit for the theta-Mellin integrand

Present, `@[approx]`-instrumented: Floating/Interval/Box (complex), field ops,
powNat/powInt, real rpow (covers u^(−3/4)), exp, log, sqrt, sin/cos/sinh/cosh, cis,
**Box.exp** (complex exp — covers u^(s/2−1) as exp((s/2−1)·log u)), tight pi/e,
ofRat/ofScientific, decidable interval < / ≤ with bridges
`Interval.approx_lt/approx_le`, generic `Series.approx_of_taylor`.

**Absent — ours to build (the whole remaining gap):** verified definite integration.
B4 = composite midpoint/Simpson over [1,8] + integrand 2nd-derivative (or Lipschitz)
bound + sum-vs-integral error theorem, on top of mathlib's
`norm_jacobiTheta_sub_one_le` tail bound.

**Architecture (kernel time):** never one giant `decide` — one lemma per quadrature
panel (own small `decide +kernel`), then add the real inequalities. Expect ~8–10
transcendental evals/node, few hundred–1000 nodes ⇒ **~1–6 kernel-hours per Ξ
evaluation**, parallelizable across files/lemmas.

## Risks

1. **B4 quadrature layer is ours** (biggest): 2–4 weeks + kernel-compute engineering.
2. **No upstream releases:** vendor a pinned copy (Apache 2.0, keep LICENSE +
   attribution); expect re-porting on any toolchain bump.

## Revised milestone plan (Route B, from scoping doc)

- B1–B2 (theta-integral representation of Ξ, truncation): 1–2 weeks — unchanged.
- B3 (integrand bounds): 1–3 weeks — unchanged.
- B4 (quadrature certificate): **2–4 weeks** (was 2–4 months from scratch).
- B5 (assembly + kernel compute): ~1 week + compute.
- Vendoring hygiene: 1–3 days.
