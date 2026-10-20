# Gate-2: `b9d6d27e` is vacuous, the binding term was never `Λ₀`, and the real unblock is one `log x` — now landed (`3034bdef`)

**Date:** 2026-10-19 (Legion, built and verified on Acer).
Labels **FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**.

---

## HEADLINE

**The march was not unblocked. `b9d6d27e` proves its hbound conditional on a
hypothesis that is false, and the conclusion it reaches is unreachable.** The
repair needed different mathematics from the one the brief prescribed, and it
is now built, kernel-clean, as `PF/Analytic/Lambda0PrimeThetaLogBound_2026_10_19.lean`
(`3034bdef`, 593 L, eight theorems, three-axiom bar).

---

## 1. The hypothesis is false. FACT + MEASURED

`Gate2BoxLocalC55_8_2026_10_19.lean` carries `hK : K_sum ≤ 1/16` on **every**
theorem — `gate2_num_bound_c55_8_r1_16`,
`norm_deriv_riemannXiEntire_num_le_two_c55_8_r1_16`,
`norm_deriv_riemannXiEntire_le_one_c55_8_r1_16`,
`abs_deriv_edgeRe_le_one_c55_8_r1_16`, and `pilot_r1_hbound_c55_8_r1_16`.

**It is discharged nowhere in the tree. FACT** — `grep -rn "K_sum"` outside that
file returns only two unrelated hits in
`PF/YangMillsCanonicalPartialFractionKernel.lean` (a resolvent sum).

**And it is false. MEASURED, two independent ways agreeing to 8 digits:**

| | |
|---|---|
| `∫₀^∞ \|F₊″\|` | `0.11419565` |
| `∫₀^∞ \|F₋″\|` | `0.13580435` |
| **`K_sum`** | **`0.25000000`** |
| hypothesis | `1/16 = 0.0625` → **false by 4.00×** |

The cross-check is the pretty part: `F₊″, F₋″ ≥ 0`, so
`K_sum = −(F₊′(0) + F₋′(0)) = −(ω(1)/2 + 2ω′(1))`, and that is **exactly the
boundary constant `boundary_const_eq_neg_quarter` already proves `= −1/4`** in
`223354b9`. So `K_sum = 1/4` is not merely measured, it is a consequence of a
theorem already in the tree.

The file's own header says *"Legion measured `K_sum` is tiny empirically"*. I
did not. The only figure I had reported was `∫|F₊″| = 0.1142`, which on its own
is already 1.83× the hypothesis.

## 2. No sharper `K` rescues it. MEASURED

At the box edge `t = 111/16`, with `‖Λ₀′‖ ≤ 50/1727` giving
`term2 = 1.59428`, the budget leaves `term1 ≤ 0.40572`, i.e.
`‖Λ₀‖ ≤ 0.027275`, i.e. **`K_sum ≤ 0.078183`**. True `K_sum = 0.25` — short by
**3.20×**. So the gap is not a loose estimate of `K`; the route does not reach.

**And the sharp identity is actively *worse* than what it replaces, there:**

| at `t = 111/16` | |
|---|---|
| Tier-3 `(1+4K)/t²` with exact `K=1/4` → `2/t²` | **`0.041555`** |
| the uniform `50/1727` | `0.028952` |

**Tier-3's `Λ₀` bound only overtakes the uniform constant for `t ≥ 8.311`. FACT**
(solve `(1+4K)/t² = 50/1727`). The `c = 55/8` box sits at `6.875`, below the
crossover. The brief's step 1 — *"use the sharp identity"* — therefore cannot
work at the box it was required to pass.

## 3. Why: the binding term is `Λ₀′`, and Tier-3 does not bound `Λ₀′`. MEASURED

This is the actual root cause, and it inverts the brief's framing.

| `t` | `term1 = (1+2\|t\|)‖Λ₀‖` | `term2 = (t²+\|t\|)‖Λ₀′‖` | total |
|---|---|---|---|
| `6.9375` (the 55/8 edge) | `0.4307` | **`1.5943`** | `2.0249` FAIL |
| `13` | `0.7817` | **`5.2693`** | `6.0510` |

`term2` is 3.7× `term1` at the edge and 6.7× at `t = 13`. The slack is all in
`Λ₀′`: the uniform constant is **15.8×** too big there (`0.028952` vs the true
`0.001833`), while for `Λ₀` it is only 2.0× too big. **Gate-2 is a `Λ₀′` wall.**
Tier-3's identity is a statement about `Λ₀`.

## 4. Cauchy cannot deliver it. FACT — this is the load-bearing negative

`lambda0_prime_abs_le_fifty_over_1727` is Cauchy's estimate `‖Λ₀′‖ ≤ M/R` at
`R = 1`, with `M` the strip sup on `σ ∈ [0,2]`. Both knobs are stuck:

* **`R` cannot grow.** The `[0,2]` range is not a stylistic choice — in
  `norm_integrand_bound_strip` it is exactly the range where *both* theta
  exponents `σ/2−1` and `(1−σ)/2−1` are `≤ 0`, which is what licenses
  `x^{σ/2−1} + x^{(1−σ)/2−1} ≤ 2`. Past `σ = 2` the dominating function must
  become `x^{σ/2−1}e^{−πx}`, an incomplete-Gamma integral.
* **`M` cannot fall far.** The sharp strip sup is `B(2) = 0.023599`
  (MEASURED), so even a perfect `M` buys `1.23×`.

Optimising the radius *if* the strip could widen would give `B(1+R)/R`,
minimised near `R = 6` at `0.006195` — but that needs `σ ∈ [−5,7]`, which the
proof cannot supply. **So Cauchy is capped at ≈ `0.024`, and `0.024` does not
pass `t = 13`.** A new representation was required, not a better constant.

## 5. The repair: one `log x`. FACT, built and kernel-clean

Differentiating the theta integral under the integral sign:

`Λ₀′(s) = ∫₁^∞ ½ log x · (x^{s/2−1} − x^{(1−s)/2−1}) · ω(x) dx`

On `σ ∈ [0,2]` the same two ingredients the `Λ₀` bound already uses give
`‖·‖ ≤ ∫₁^∞ log x · ω(x) dx ≤ ∫₁^∞ log x · e^{−πx}/(1−e^{−π}) dx`, and then
`log x ≤ x − 1` with `∫₁^∞ (x−1)e^{−πx} dx = e^{−π}/π²`:

> **`‖Λ₀′(1+it)‖ ≤ e^{−π}/(π²(1−e^{−π})) ≈ 0.0045763 ≤ 3/650`**

The gain is exactly `1/(2π) = 6.28×` — the `½` cancels the `2` from the two
terms, and the `log x` turns `∫e^{−πx} = e^{−π}/π` into `e^{−π}/π²`. Note
`50/1727` is itself precisely `2e^{−π}/(π(1−e^{−π}))` relaxed through
`e^{−π} ≤ 1/23`, `π > 157/50` (verified: `2/(22·157/50) = 50/1727`), so
`3/650` is the same relaxation applied to the new constant.

### What it unlocks. MEASURED

Ceiling `6.886 → 14.974`:

| `t` | load | verdict |
|---|---|---|
| `6.8125` — the `c=55/8` lower edge | `0.6691` | PASS |
| `6.9375` — the `c=55/8` upper edge | **`0.6847`** | PASS, 2.9× headroom |
| `10` | `1.1157` | PASS |
| `13` — R1's march target | `1.6217` | PASS |
| `14.5` — R2's upper end | `1.9059` | PASS |
| `14.974` | `2.0000` | the new ceiling |
| `15` — R3's top | `2.0052` | **just over** — see OPEN |

**`pilot_r1_hbound_box` covers every centre in `[55/8, 13]` at radius `1/16`
in one theorem** — the march needs no per-box Gate-2 work at all, which is
better than the box-local scheme the brief asked for.

## 6. The eight theorems. FACT

All at `[propext, Classical.choice, Quot.sound]`:

`hasDerivAt_lambda0_edge`, `lambda0_prime_abs_le_theta_log`,
`lambda0_prime_abs_le_three_over_650`, `gate2_num_bound_le_fourteen`,
`norm_deriv_riemannXiEntire_le_one_le_fourteen`,
`abs_deriv_edgeRe_le_one_le_fourteen`, `pilot_r1_hbound_c55_8_r1_16`
(unconditional — the drop-in replacement), `pilot_r1_hbound_box`.

Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` is `RCLike`-general,
so it applies at complex parameter directly; integrability and measurability
both come from the tree's own `integrableOn_cpow_smul_evenKernel_sub_one`,
which holds for *every* complex exponent.

---

## 7. Consequences for the plan. JUDGEMENT

1. **`Gate2BoxLocalC55_8_2026_10_19.lean` should not be deleted but must not be
   consumed.** Its `lambda0_abs_sharp_le` is *true and unconditional* and is the
   right `Λ₀` bound for `t ≥ 8.31` — worth keeping, with `K_sum ≤ 1/4` proved
   (OPEN, needs `F₊″, F₋″ ≥ 0`; numerics say both hold). Only the five
   `hK`-conditional theorems are dead.
2. **Nothing downstream is contaminated. FACT, swept.** `grep -rln` for
   `Gate2BoxLocalC55_8` and `pilot_r1_hbound_c55_8_r1_16` across all `*.lean`
   returns **no file** outside that module and this one. The vacuous chain was
   never consumed, so no pilot needs repointing — the damage was confined to a
   false belief that the march was open.
3. **Step 2 (the Gate-1 hybrid at c=27/4) is now genuinely unblocked** and is
   the right next action.

## Label summary

* **FACT (read from source):** `hK` on all five theorems in `b9d6d27e` and its
  absence everywhere else in the tree; the `[0,2]` range being the
  both-exponents-nonpositive condition in `norm_integrand_bound_strip`;
  `50/1727 = 2e^{−π}/(π(1−e^{−π}))` relaxed; `Λ₀′`'s Cauchy-at-radius-1 proof;
  `integrableOn_cpow_smul_evenKernel_sub_one` holding for all `w`;
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` being `RCLike`-general.
* **MEASURED:** `K_sum = 0.25000000` by quadrature **and** by the proved
  boundary constant; the required `K ≤ 0.078183`; the `8.311` crossover; the
  term1/term2 split at `6.9375` and `13`; `B(σ)` and the `R = 6` optimum
  `0.006195`; the new ceiling `14.974` and the three load rows.
* **JUDGEMENT:** that the brief's prescribed method targets the wrong object;
  that the `Λ₀`-side half of `b9d6d27e` is worth keeping; the three plan
  consequences above.
* **OPEN / NOT established:** `K_sum = 1/4` is not yet a Lean theorem (needs
  `F₊″, F₋″ ≥ 0`, numerically true, unproved); I have not swept for existing
  consumers of the vacuous hbound; the ceiling `14.974` falls `0.026` short of
  R3's top at `t = 15`, which would need the `Λ₀` side improved too (where
  Tier-3's `2/t²` does work, since `15 > 8.31`) — so R3 is reachable but not
  yet covered by this file.
