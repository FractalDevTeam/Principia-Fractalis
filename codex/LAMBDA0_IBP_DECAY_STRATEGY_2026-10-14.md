# Λ₀(1+it) t-dependent decay via integration by parts

**Date:** 2026-10-14 (evening)
**Author:** Pablo Cohen + Claude Opus 4.7 (session continuation while Pablo away)
**Status:** PLAN. No Lean code yet. Codex-only.

## Why

The uniform Mellin bound `‖Λ₀(1+it)‖ ≤ 2·exp(-π)/(π·(1-exp(-π))) ≈ 0.0287`
is t-independent. The pilot producer at `Mc_lb = 1/4` requires
`(c² + c)·BOUND ≤ 1/2`, i.e. `BOUND ≤ 1/(2(c²+c))`. At `c = 13` the
required `BOUND ≤ 1/364 ≈ 0.00275` — **10× smaller than the uniform
bound's true value**. No rational-numerics tightening can close this gap.

The physical reason: `Λ₀(1+it)` oscillates with frequency `∝ t`; the
integral `∫_1^∞ … exp(it·ln(x)/2) dx` decays by Riemann–Lebesgue, and
quantitatively like `1/|t|` under integration by parts.

**Target:** prove `‖Λ₀(1+it)‖ ≤ C/|t|` for an explicit rational `C` and
all `|t| ≥ 1` (or `|t| ≥ 2`). Combined with the uniform bound for small
`|t|`, this unlocks the full R1 range `[0, 13]`.

## The analytic derivation (plain math)

Start from the mathlib-shaped integral representation (as used in
`Lambda0UniformBound_2026_10_14`):

```
Λ₀(s) = ∫_1^∞ (x^(s/2 − 1) + x^((1−s)/2 − 1)) · ω(x) dx                      (M)
```

where `ω(x) = ½·(evenKernel 0 x − 1)` is the Jacobi theta minus its
constant term. At `s = 1 + it`:

```
x^(s/2 − 1)      = x^(−1/2) · exp(it · ln(x) / 2)
x^((1−s)/2 − 1)  = x^(−1)   · exp(−it · ln(x) / 2)
```

Call the two pieces `I₊(t), I₋(t)`:

```
I₊(t) = ∫_1^∞ x^(−1/2) · exp(it · ln(x) / 2) · ω(x) dx                       (I+)
I₋(t) = ∫_1^∞ x^(−1)   · exp(−it · ln(x) / 2) · ω(x) dx                      (I-)
```

so `Λ₀(1+it) = I₊(t) + I₋(t)`.

### Change of variable `u = ln(x)`

For `I₊`: `x = e^u`, `dx = e^u du`, `ln(x)/2 = u/2`, `x^(−1/2) = e^(−u/2)`.

```
I₊(t) = ∫_0^∞ e^(−u/2) · exp(it·u/2) · ω(e^u) · e^u du
      = ∫_0^∞ e^(u/2) · exp(it·u/2) · ω(e^u) du
      = ∫_0^∞ F₊(u) · exp(it·u/2) du      where F₊(u) := e^(u/2) · ω(e^u)
```

For `I₋`: similarly,

```
I₋(t) = ∫_0^∞ F₋(u) · exp(−it·u/2) du    where F₋(u) := ω(e^u)
```

(Note `F₋` has the `x^(−1) · e^u = 1` factor collapsing.)

### Decay of `F₊(u)` and `F₋(u)` at infinity

`ω(x)` satisfies the geometric bound (already in XiThetaIntegral):
`ω(x) ≤ exp(−π·x)/(1 − exp(−π·x))` for `x > 0`.

So for `u ≥ 0`:
```
F₊(u) ≤ e^(u/2) · exp(−π·e^u) / (1 − exp(−π·e^u))
F₋(u) ≤                exp(−π·e^u) / (1 − exp(−π·e^u))
```

Both decay super-exponentially (since `−π·e^u` → −∞). Both `F₊`, `F₋`,
and their derivatives are integrable on `[0, ∞)`.

### Integration by parts

For `I₊`, with `v(u) = exp(it·u/2)`, `v'(u) = (it/2)·exp(it·u/2)`:

```
∫_0^∞ F₊(u) · exp(it·u/2) du
    = [F₊(u) · (2/(it)) · exp(it·u/2)]_0^∞
      − ∫_0^∞ F₊'(u) · (2/(it)) · exp(it·u/2) du
    = (2/(it)) · (0 − F₊(0))
      + (−2/(it)) · ∫_0^∞ F₊'(u) · exp(it·u/2) du
```

Taking moduli (and using `|exp(iθ)| = 1`):

```
|I₊(t)| ≤ (2/|t|) · |F₊(0)| + (2/|t|) · ∫_0^∞ |F₊'(u)| du
      = (2/|t|) · (F₊(0) + V(F₊))                                            (IBP+)
```

where `V(F₊) := ∫_0^∞ |F₊'(u)| du` is the total variation of `F₊` on
`[0, ∞)`.

Similarly `|I₋(t)| ≤ (2/|t|) · (F₋(0) + V(F₋))`.

Therefore:

```
‖Λ₀(1+it)‖ ≤ (2/|t|) · (F₊(0) + F₋(0) + V(F₊) + V(F₋))                       (★)
```

with `F₊(0) = ω(1)`, `F₋(0) = ω(1)`, so `F₊(0) + F₋(0) = 2·ω(1)`.

### Bounding `V(F₊)` and `V(F₋)`

Both `F₊` and `F₋` are smooth on `[0, ∞)` (`ω` is smooth away from 0).
If each is **monotone decreasing** on `[0, ∞)`, then `V = F(0) − F(∞) = F(0)`.

Check `F₋(u) = ω(e^u)`: as `u` increases, `e^u` increases, so `ω(e^u)`
decreases (`ω` is antitone on `(0, ∞)` — proved in XiThetaIntegral as
`omega_antitone`). So `F₋` is monotone decreasing, `V(F₋) = ω(1)`.

Check `F₊(u) = e^(u/2) · ω(e^u)`:
`F₊'(u) = (1/2) · e^(u/2) · ω(e^u) + e^(u/2) · ω'(e^u) · e^u`
       `= (1/2) · e^(u/2) · [ω(e^u) + 2·e^u · ω'(e^u)]`

Since `ω` is a tail of a theta series:
`ω(x) = ∑_{n≥1} exp(−π·n²·x)`
`ω'(x) = ∑_{n≥1} (−π·n²) · exp(−π·n²·x)`
`x·ω'(x) = ∑_{n≥1} (−π·n²·x) · exp(−π·n²·x)`

At `x = e^u` with `u ≥ 0` (`x ≥ 1`), each term `−π·n²·x · exp(−π·n²·x)`
is negative, and `|2·x·ω'(x)| ≥ 2·π·x·exp(−π·x)` for the n=1 term alone.

Compare to `ω(x) ≤ exp(−π·x)/(1 − exp(−π·x)) ≤ (23/22) · exp(−π·x)` for `x ≥ 1`
(using `exp(−π) ≤ 1/23`).

So for `x ≥ 1`:
`ω(x) + 2·x·ω'(x) ≤ (23/22) · exp(−π·x) − 2·π·x·exp(−π·x) + (tail)`
                 `≤ (23/22 − 2π·x) · exp(−π·x) + (small tail)`

For `x ≥ 1`: `23/22 − 2π ≤ 1.045 − 6.28 < 0`. So the bracket is negative
at `x = 1`, and remains negative for all `x ≥ 1`.

**Conclusion:** `F₊'(u) < 0` for all `u ≥ 0`, i.e. `F₊` is also monotone
decreasing on `[0, ∞)`. So `V(F₊) = F₊(0) = ω(1)`.

### Final constant

```
‖Λ₀(1+it)‖ ≤ (2/|t|) · (ω(1) + ω(1) + ω(1) + ω(1))                           (⋆⋆)
          = (8·ω(1)) / |t|
```

Now bound `ω(1)`:
`ω(1) = ∑_{n≥1} exp(−π·n²) ≤ exp(−π)/(1 − exp(−π)) ≤ (1/23)/(22/23) = 1/22`.

So:
```
‖Λ₀(1+it)‖ ≤ (8/22) / |t| = 4/(11·|t|)                                       (⋆⋆⋆)
```

**Verification at |t| = 13:** `4/(11·13) = 4/143 ≈ 0.028`. Needed: `1/364 ≈ 0.00275`.

Hmm — not enough. **The bare IBP bound is still 10× too loose at `|t| = 13`.**

### Second IBP (iterated)

The IBP identity can be applied again to the remainder integral:

```
∫_0^∞ F'(u) · exp(it·u/2) du
    = [F'(u) · (2/(it)) · exp(it·u/2)]_0^∞ − (2/(it))·∫_0^∞ F''(u)·exp(it·u/2) du
    = −(2/(it))·F'(0) − (2/(it))·∫_0^∞ F''(u)·exp(it·u/2) du
```

So:
```
|I₊(t)| ≤ (2/|t|) · F(0) + (2/|t|)² · (|F'(0)| + V(F'))
```

If `V(F')` is also finite (which it is since `F''` is integrable), we get
decay like `1/|t|²` for the second-order correction.

**At `|t| ≥ 2`:** the dominant term is `(2/|t|)·F(0)`, and iterating helps
reduce the overall constant. But the fundamental scaling stays `1/|t|`.

**Conclusion:** single IBP gives `4/(11·|t|)`. To reach `|t| = 13` with
margin `1/364`, we need the constant reduced from `4/11 ≈ 0.364` to `≤ 1/28`.
That's a 10× tightening. Second IBP contributes a `1/|t|²` term with its
own constant — may or may not close the gap.

**Fallback: Route C (hybrid).** Use IBP for `|t| ∈ [1, T₀]` with `T₀`
determined by where the uniform bound takes over backward and the IBP
bound suffices forward. Patch the dip near `t = 14` (first zero at
`14.1347`) with per-point certified panels.

### Rough lemma dependency graph (progress during autonomous session)

```
L1a omega_hasDerivAt (x>0): ω' as tsum interchange     [LANDED kernel-clean ✓]
L1b omega'_nonpos on Ioi 0                               [LANDED kernel-clean ✓]
L1c differentiableOn_omega, deriv_omega_eq               [LANDED kernel-clean ✓]
L1d F±  definitions, nonneg, F_minus_antitone            [LANDED kernel-clean ✓]
L1e F_minus_hasDerivAt (chain rule)                      [LANDED kernel-clean ✓]
L1f F_plus_hasDerivAt (product+chain rule)               [LANDED kernel-clean ✓]
---
L2  omega_prime_abs_bound: |ω'(x)| ≤ π · [series bound]  [NOT YET]
L3a F_plus_antitone on Ici 0 (from F_plus' ≤ 0)          [NOT YET; needs L2]
L3b F_plus_variation: V(F₊) = F₊(0) = ω(1)               [NOT YET]
L3c F_minus_variation: V(F₋) = F₋(0) = ω(1)              [NOT YET]
---
L4  IBP_identity: `∫_0^∞ F(u) · exp(it·u/2) du` =         [BIG REMAINING STEP]
    boundary + `(-2/it) · ∫_0^∞ F'(u) · exp(it·u/2) du`
    (requires improper-interval IBP in Lean —
     mathlib has IBP on [a,b] via IntegrationByParts;
     IntegralEqImproper has FTC on Ioi; combining
     needs limit-passing on boundary term.)
---
L5  lambda0_abs_decay_1_over_t: ‖Λ₀(1+it)‖ ≤ 4/(11·|t|)   [DEPENDS ON L4]
```

**Landed in `PF/Analytic/OmegaDerivative_2026_10_14.lean`** (13 theorems):

- `hasDerivAt_omega_term`, `omega_term_deriv_abs_le_on_Ioi`,
  `summable_omega_term_deriv_bound`, `omega_hasDerivAt`
- `omega'_term_nonpos`, `omega'_nonpos`
- `differentiableOn_omega`, `deriv_omega_eq`
- `F_minus`, `F_plus` (defs) + `F_minus_antitone`,
  `F_minus_nonneg`, `F_plus_nonneg`
- `F_minus_hasDerivAt`, `F_plus_hasDerivAt`

All axiom-clean `[propext, Classical.choice, Quot.sound]`.

**Remaining work (rough estimates):**
- L2 (quantitative bound on `|ω'|`): 50–100 LoC with series manipulation.
- L3 (antitone + variation): 100–200 LoC combined.
- L4 (IBP on improper interval): 150–300 LoC, requires combining
  mathlib's finite-interval IBP with FTC-on-Ioi.
- L5 (final decay bound): 50–100 LoC composition.

**Total remaining estimate:** 350–700 LoC. 1–3 days focused work.

### Mathlib dependencies likely required

- `MeasureTheory.integral_bySubst`, `MeasureTheory.setIntegral_eq_setIntegral_of_ae`
- `Complex.exp_mul_I`, `Complex.norm_exp_mul_I` (for `|exp(iθ)| = 1`)
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` or improper-integral IBP equivalent
- `Jacobi` or custom `omega_hasDerivAt` (not directly in mathlib)

### Feasibility probe result (autonomous session 2026-10-14)

**Target was:** `omega_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt omega (omega' x) x`

**RESULT: LANDED** — kernel-clean via `hasDerivAt_tsum_of_isPreconnected`
+ `Real.summable_pow_mul_exp_neg_nat_mul`. Chain rule corollaries
(F_minus_hasDerivAt, F_plus_hasDerivAt) also land cleanly.

**Implication:** The IBP route is feasible in Lean. The remaining steps
(quantitative `|ω'|` bound, antitonicity of F±, improper-interval IBP)
are routine but substantial LoC.

## Current state at end of this session

* R1 kernel-clean on `[0, 4]` (12 pilots, 30.8% of `[0, 13]`).
* Λ₀ uniform bound tightened to `50/1727` (within 0.7% of true analytic value).
* No further rational-numerics gain available.
* IBP decay strategy documented (this file).
* IBP implementation: not started. Needs Pablo's go/no-go.

## Decision for Pablo on return

A. **Go on IBP (Route A).** 2–4 day analytic project to prove
   `‖Λ₀(1+it)‖ ≤ 4/(11·|t|)` (plus possible second-IBP tightening).
   May need second-IBP to close the full `|t| ≤ 13` range.

B. **Switch to per-point panels (Route B).** Mechanical generation of
   per-c certified lower bounds `Re ξ(1 + c·i) ≥ Mc_lb` by the r120-style
   panels. 10 pilot centers × ~60 panel files each = ~600 files.
   Entirely in the existing architecture, mpmath-generatable.

C. **Mixed Route C.** IBP for the bulk, per-point panels near the first
   zero (`t ≈ 14.1`). Likely the overall minimum effort.

D. **Stop here, publish current state.** Pilot producer + Λ₀ 1/33 +
   Λ₀ 50/1727 + 12-pilot R1 block on `[0, 4]` is itself a verified-math
   contribution. The uniform-bound ceiling is a precise analytic
   observation worth documenting.
