/-
# `JonquieresExpansionEqualsGeomTendstoPartialAtHalf` — Bernoulli-Identity Discharge

This file SHARPENS the partial-sum `HasSum` residual
`JonquieresExpansionEqualsGeomTendstoPartialAtHalf` (defined in
`JonquieresExpansionEqualsGeomGermAtHalfClosure.lean`) by reducing it
to a SINGLE named open analytic Prop — the **analytic Bernoulli
generating-function identity** in `HasSum` form at `u = -log z` for
`z` near `1/2`.

## Mathematical content

The classical Bernoulli generating function

```
v / (e^v - 1) = Σ_{k≥0} B_k · v^k / k!
```

holds **formally as a power series** in mathlib
(`Mathlib.NumberTheory.Bernoulli`, theorem
`bernoulliPowerSeries_mul_exp_sub_one`). It is converted to an
**analytic** identity on `|v| < 2π` by standard radius-of-convergence
arguments (NOT yet in mathlib).

Setting `v = -u` where `u = log z` (so `e^u = z`, `e^{-u} = z⁻¹`):
```
(-u) / (e^{-u} - 1) = (-u) / ((1 - z) / z) = u · z / (z - 1).
```

So the analytic identity at `v = -log z` reads:
```
Σ_{k≥0} B_k · (-log z)^k / k! = log z · z / (z - 1).        (*)
```

Combined with mathlib's `riemannZeta_neg_nat_eq_bernoulli`
(`ζ(-m) = (-1)^m · B_{m+1} / (m+1)`), the k-th Jonquières ζ-term is

```
ζ(-m) · (log z)^m / m!  =  B_{m+1} · (-log z)^m / (m+1)!,
```

i.e. exactly the `(m+1)`-st term of (*) divided by `(-log z)`. So (*)
implies — via:
  (i) subtraction of the `k = 0` term `B_0 = 1`,
  (ii) reindexing `k ↦ m + 1`,
  (iii) factoring out `(-log z)`,
  (iv) division by the non-zero scalar `-log z`,
the target `HasSum` form on a punctured nhd of `1/2`.

The arithmetic on the RHS, with `u := log z`:
```
[u·z/(z-1) − 1] / (−u)
  = (uz − z + 1) / (−u·(z − 1))
  = (uz − z + 1) / (u·(1 − z))
  = z/(1−z) + 1/u
  = z/(1−z) − jonquieresGammaTerm 0 z,
```
since `jonquieresGammaTerm 0 z = Γ(1)·(−log z)^(−1) = −1/log z = −1/u`.

## What this file delivers (axiom-free, no `sorry`)

1. **`BernoulliExpHasSumAtNegLogNhdsHalf`** — the SINGLE named open
   analytic Prop:
   ```
   ∀ᶠ z in nhds (1/2 : ℂ),
       HasSum (fun k : ℕ => (bernoulli k : ℂ) · (-log z)^k / k!)
              (log z · z / (z − 1)).
   ```
   This is the analytic (HasSum) form of the classical Bernoulli
   generating-function identity on a nhd of `1/2`, evaluated at
   `v = -log z`. **Open**: mathlib has the formal-power-series
   identity (`bernoulliPowerSeries_mul_exp_sub_one`) but not the
   analytic `HasSum` lift. Discharging this Prop is a clean
   instance of the formal-PS → analytic-HasSum bridge for entire
   ratios, and is roughly equivalent to formalising
   `Complex.analyticOn` for `v ↦ v/(e^v - 1)` on `|v| < 2π`.

2. **`jonquieresExpansionEqualsGeomTendstoPartialAtHalf_of_bernoulli`**
   — the DISCHARGE theorem: the analytic Bernoulli identity ⟹
   `JonquieresExpansionEqualsGeomTendstoPartialAtHalf`. Axiom-free,
   pure algebra on `HasSum` (`hasSum_nat_add_iff`, `HasSum.mul_left`,
   `HasSum.congr`) plus mathlib's `riemannZeta_neg_nat_eq_bernoulli`.

3. **`jonquieresIdentityPointGermAtHalf_zero_of_bernoulli`** — the
   COMPOSED capstone: the analytic Bernoulli identity ⟹ the classical
   germ identity at `(s, z) = (0, 1/2)` (`JonquieresIdentityPointGermAtHalf 0`),
   via the existing reduction
   `jonquieresIdentityPointGermAtHalf_zero_of_tendstoPartial`.

## Strategic position

Before this file, the partial-sum residual
`JonquieresExpansionEqualsGeomTendstoPartialAtHalf` was the
sharpest open Prop on the closure path. After this file, the
SHARPEST open Prop is the analytic Bernoulli identity
`BernoulliExpHasSumAtNegLogNhdsHalf`, which:
* Is a **single classical analytic identity** for a function with
  known holomorphy structure (`v ↦ v/(e^v - 1)` extends to an
  entire function on the disc `|v| < 2π` after removing the simple
  pole at `v = 0` cancelled by the numerator);
* Has its formal-power-series shadow already in mathlib;
* Is a **drop-in target** for any future contributor formalising
  `bernoulliPowerSeries → HasSum` (radius-of-convergence theory for
  formal exponential generating functions).

The remaining mathematical content is purely classical complex
analysis — no number-theoretic or operator-theoretic open content.

Stage L24 — Bernoulli generating-function discharge of the partial-sum
residual at (0, 1/2).
-/

import PF.Analytic.JonquieresExpansionEqualsGeomGermAtHalfClosure
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology
open PrincipiaTractalis.Analytic

/-! ## The named open Prop: analytic Bernoulli identity at `v = -log z` near `z = 1/2` -/

/-- **Analytic Bernoulli generating-function identity at `v = -log z`,
    eventually in `nhds (1/2 : ℂ)`**.

    The classical Bernoulli generating function `v/(e^v - 1) =
    Σ B_k v^k/k!`, evaluated at `v = -log z` (so `e^v = z⁻¹`,
    `v/(e^v - 1) = log z · z/(z - 1)`), holds as an analytic `HasSum`
    on a neighborhood of `z = 1/2`. -/
def BernoulliExpHasSumAtNegLogNhdsHalf : Prop :=
  ∀ᶠ z in nhds (1/2 : ℂ),
    HasSum (fun k : ℕ => (bernoulli k : ℂ) * (-(Complex.log z))^k / (k.factorial : ℂ))
      (Complex.log z * z / (z - 1))

/-! ## Algebraic helpers -/

/-- **Per-term Bernoulli ↔ ζ identity**: for any `m : ℕ` and any
    `u : ℂ`, the `m`-th Jonquières ζ-term (with `s = 0`) equals the
    `(m+1)`-st Bernoulli term divided by `(-u)`. Pure algebra +
    `riemannZeta_neg_nat_eq_bernoulli`. -/
lemma jonquieresZetaTerm_zero_eq_bernoulli_shift (z : ℂ) (m : ℕ) :
    riemannZeta (0 - m) * (Complex.log z) ^ m / (m.factorial : ℂ) =
      (bernoulli (m + 1) : ℂ) * (-(Complex.log z)) ^ m /
        ((m + 1).factorial : ℂ) := by
  -- `ζ(-m) = (-1)^m · B_{m+1}/(m+1)` from mathlib.
  have hzeta : riemannZeta (0 - (m : ℂ)) =
      (-1 : ℂ) ^ m * (bernoulli (m + 1) : ℂ) / ((m : ℂ) + 1) := by
    have h0 : (0 - (m : ℂ)) = -(m : ℂ) := by ring
    rw [h0, riemannZeta_neg_nat_eq_bernoulli]
  rw [hzeta]
  -- `(m+1).factorial = (m+1) * m.factorial`.
  rw [Nat.factorial_succ]
  -- (−log z)^m = (−1)^m · (log z)^m
  have hneg_pow : (-(Complex.log z)) ^ m = (-1 : ℂ) ^ m * (Complex.log z) ^ m := neg_pow _ m
  rw [hneg_pow]
  -- Now both sides are products; reduce via field_simp + ring after handling factorial ≠ 0.
  have hfact : (m.factorial : ℂ) ≠ 0 := by
    exact_mod_cast m.factorial_ne_zero
  have hmp1 : ((m : ℂ) + 1) ≠ 0 := by
    have h := Nat.succ_ne_zero m
    have : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast h
    push_cast at this; exact this
  field_simp
  push_cast
  ring

/-! ## Discharge theorem -/

/-- **DISCHARGE**: the analytic Bernoulli generating-function identity
    at `v = -log z` (eventually in `nhds (1/2 : ℂ)`) implies
    `JonquieresExpansionEqualsGeomTendstoPartialAtHalf`. -/
theorem jonquieresExpansionEqualsGeomTendstoPartialAtHalf_of_bernoulli
    (h : BernoulliExpHasSumAtNegLogNhdsHalf) :
    JonquieresExpansionEqualsGeomTendstoPartialAtHalf := by
  unfold JonquieresExpansionEqualsGeomTendstoPartialAtHalf
  unfold BernoulliExpHasSumAtNegLogNhdsHalf at h
  -- The nhds of 1/2 (away from 0 and 1) — needed so that `log z ≠ 0` and `z ≠ 1`.
  have h_z_ne_one : ∀ᶠ z in nhds (1/2 : ℂ), z ≠ 1 := by
    refine (isOpen_ne).eventually_mem ?_
    norm_num
  have h_z_ne_zero : ∀ᶠ z in nhds (1/2 : ℂ), z ≠ 0 := by
    refine (isOpen_ne).eventually_mem ?_
    norm_num
  have h_log_ne_zero : ∀ᶠ z in nhds (1/2 : ℂ), Complex.log z ≠ 0 := by
    -- log is continuous at 1/2, log(1/2) ≠ 0, and log = 0 iff z ∈ {0, 1, -1, ...}; near 1/2 only z=1 matters.
    -- Easier: log z = 0 ↔ z = 1 in the slit plane near 1/2.
    filter_upwards [h_z_ne_one, h_z_ne_zero] with z hz1 hz0
    intro hlog
    -- log z = 0 ⟹ z = exp(log z) = exp 0 = 1.
    have : z = 1 := by
      have := Complex.exp_log hz0
      rw [hlog, Complex.exp_zero] at this
      exact this.symm
    exact hz1 this
  filter_upwards [h, h_z_ne_one, h_z_ne_zero, h_log_ne_zero]
    with z hHS hz1 _hz0 hlog
  -- hHS : HasSum (fun k => B_k · (-log z)^k / k!) (log z · z / (z - 1))
  -- Goal: HasSum (fun k : ℕ => jonquieresZetaTerm 0 z k)
  --              (z / (1 - z) - jonquieresGammaTerm 0 z)
  -- Step A: reindex k ↦ k + 1 to drop the k = 0 term.
  --   k = 0 term: B_0 · 1 / 0! = 1.
  --   tail sum   : (log z · z / (z - 1)) - 1.
  have h_tail :
      HasSum (fun k : ℕ => (bernoulli (k + 1) : ℂ) *
              (-(Complex.log z))^(k + 1) / ((k + 1).factorial : ℂ))
        (Complex.log z * z / (z - 1) - 1) := by
    -- The k=0 term equals 1.
    have h_k0 :
        ∑ i ∈ Finset.range 1,
          (bernoulli i : ℂ) * (-(Complex.log z))^i / (i.factorial : ℂ) = 1 := by
      simp [bernoulli_zero]
    -- Rewrite hHS to expose the (sum + range sum) form expected by `hasSum_nat_add_iff.mpr`.
    have hHS' :
        HasSum (fun k : ℕ => (bernoulli k : ℂ) * (-(Complex.log z))^k / (k.factorial : ℂ))
          ((Complex.log z * z / (z - 1) - 1) +
            ∑ i ∈ Finset.range 1,
              (bernoulli i : ℂ) * (-(Complex.log z))^i / (i.factorial : ℂ)) := by
      rw [h_k0]; convert hHS using 1; ring
    exact (hasSum_nat_add_iff (f := fun k : ℕ =>
        (bernoulli k : ℂ) * (-(Complex.log z))^k / (k.factorial : ℂ)) 1).mpr hHS'
  -- Step B: factor `(-log z)` out of the tail term.
  --   B_{k+1} · (-log z)^(k+1) / (k+1)! = (-log z) · B_{k+1} · (-log z)^k / (k+1)!
  have h_factored :
      HasSum (fun k : ℕ => (-(Complex.log z)) *
              ((bernoulli (k + 1) : ℂ) * (-(Complex.log z))^k /
                ((k + 1).factorial : ℂ)))
        (Complex.log z * z / (z - 1) - 1) := by
    refine h_tail.congr_fun (fun k => ?_)
    rw [pow_succ]
    ring
  -- Step C: divide both sides by `-log z` (i.e. multiply by `(-log z)⁻¹`).
  have h_neg_log_ne : -(Complex.log z) ≠ 0 := neg_ne_zero.mpr hlog
  have h_divided :
      HasSum (fun k : ℕ => (bernoulli (k + 1) : ℂ) *
              (-(Complex.log z))^k / ((k + 1).factorial : ℂ))
        ((Complex.log z * z / (z - 1) - 1) * (-(Complex.log z))⁻¹) := by
    have hLeft := h_factored.mul_left ((-(Complex.log z))⁻¹)
    -- hLeft has value `(-u)⁻¹ * (log z · z / (z-1) - 1)`.
    -- Switch product order on the value (commutativity in ℂ).
    have hValEq :
        (-(Complex.log z))⁻¹ * (Complex.log z * z / (z - 1) - 1) =
          (Complex.log z * z / (z - 1) - 1) * (-(Complex.log z))⁻¹ := mul_comm _ _
    rw [hValEq] at hLeft
    -- Simplify the function on the LHS: (−u)⁻¹ · ((−u) · X) = X.
    refine hLeft.congr_fun (fun k => ?_)
    field_simp
  -- Step D: rewrite the per-term LHS via the jonquieresZetaTerm identity.
  have h_target_terms :
      HasSum (fun k : ℕ => jonquieresZetaTerm 0 z k)
        ((Complex.log z * z / (z - 1) - 1) * (-(Complex.log z))⁻¹) := by
    refine h_divided.congr_fun (fun k => ?_)
    -- Goal: B_{k+1}·(-log z)^k/(k+1)! = jonquieresZetaTerm 0 z k
    --     = ζ(0-k)·(log z)^k/k!
    unfold jonquieresZetaTerm
    exact (jonquieresZetaTerm_zero_eq_bernoulli_shift z k)
  -- Step E: rewrite the RHS scalar to match the target form.
  --   (log z · z / (z - 1) - 1) · (-log z)⁻¹
  --     = z/(1-z) - jonquieresGammaTerm 0 z
  --   where jonquieresGammaTerm 0 z = Γ(1)·(-log z)^(-1) = -1/log z.
  have h_RHS :
      (Complex.log z * z / (z - 1) - 1) * (-(Complex.log z))⁻¹ =
        z / (1 - z) - jonquieresGammaTerm 0 z := by
    -- Simplify jonquieresGammaTerm 0 z.
    have h_gamma_term : jonquieresGammaTerm 0 z = -((Complex.log z)⁻¹) := by
      unfold jonquieresGammaTerm
      rw [show ((1 : ℂ) - 0) = 1 from by ring, show ((0 : ℂ) - 1) = -1 from by ring,
          Complex.Gamma_one, one_mul, Complex.cpow_neg_one]
      -- (-log z)⁻¹ = -(log z)⁻¹
      rw [show -(Complex.log z) = -1 * Complex.log z from by ring]
      rw [mul_inv]
      ring
    rw [h_gamma_term]
    -- The arithmetic identity.
    have h_z_minus_one_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have h_one_minus_z_ne : (1 : ℂ) - z ≠ 0 := by
      intro h0
      apply h_z_minus_one_ne
      have : z = 1 := by linear_combination -h0
      simp [this]
    field_simp
    ring
  rw [h_RHS] at h_target_terms
  exact h_target_terms

/-! ## Composed closure capstone -/

/-- **COMPOSED CAPSTONE**: the analytic Bernoulli identity
    `BernoulliExpHasSumAtNegLogNhdsHalf` ⟹ the classical Jonquières
    germ identity at `(s, z) = (0, 1/2)`:
    `JonquieresIdentityPointGermAtHalf 0`. Composes the discharge
    with the existing
    `jonquieresIdentityPointGermAtHalf_zero_of_tendstoPartial`. -/
theorem jonquieresIdentityPointGermAtHalf_zero_of_bernoulli
    (h : BernoulliExpHasSumAtNegLogNhdsHalf) :
    JonquieresIdentityPointGermAtHalf 0 :=
  jonquieresIdentityPointGermAtHalf_zero_of_tendstoPartial
    (jonquieresExpansionEqualsGeomTendstoPartialAtHalf_of_bernoulli h)

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `BernoulliExpHasSumAtNegLogNhdsHalf` — the SHARPEST open analytic
  Prop on the `(s, z) = (0, 1/2)` closure path: the `HasSum` form of
  the classical Bernoulli generating-function identity at `v = -log z`,
  eventually in `nhds (1/2)`.

* `jonquieresZetaTerm_zero_eq_bernoulli_shift` — the per-term
  algebraic bridge `ζ(-m) · u^m/m! = B_{m+1} · (-u)^m/(m+1)!`, proven
  axiom-free using `riemannZeta_neg_nat_eq_bernoulli`.

* `jonquieresExpansionEqualsGeomTendstoPartialAtHalf_of_bernoulli` —
  the DISCHARGE: analytic Bernoulli identity ⟹ partial-sum `HasSum`
  residual. Uses only `hasSum_nat_add_iff`, `HasSum.mul_left`,
  `HasSum.congr_fun`, and the per-term identity above.

* `jonquieresIdentityPointGermAtHalf_zero_of_bernoulli` — COMPOSED:
  analytic Bernoulli identity ⟹ classical Jonquières germ identity
  at `(0, 1/2)`.

**Mathlib infrastructure used**:

| Lemma | Source |
|-------|--------|
| `riemannZeta_neg_nat_eq_bernoulli` | `Mathlib.NumberTheory.LSeries.HurwitzZetaValues` |
| `Nat.bernoulli_zero` | `Mathlib.NumberTheory.Bernoulli` |
| `hasSum_nat_add_iff` | `Mathlib.Topology.Algebra.InfiniteSum.NatInt` |
| `HasSum.mul_left`, `HasSum.congr_fun` | core `Mathlib.Topology.Algebra.InfiniteSum.Basic` |
| `Complex.Gamma_one`, `Complex.cpow_neg_one` | `Mathlib.Analysis.SpecialFunctions.{Gamma.Basic,Pow.Complex}` |

**Sharpest remaining open content at `(0, 1/2)` after this file**:
`BernoulliExpHasSumAtNegLogNhdsHalf` — the analytic `HasSum`
counterpart of mathlib's existing formal-power-series identity
`bernoulliPowerSeries_mul_exp_sub_one`. Discharging it requires the
standard radius-of-convergence theory for exponential generating
functions (`v/(e^v - 1)` is analytic on `|v| < 2π`), not yet in
mathlib. This is a clean classical complex-analysis target with no
number-theoretic or operator-theoretic dependencies.

Stage L24 — Bernoulli generating-function discharge of the partial-sum
residual at (0, 1/2).
-/

end PrincipiaTractalis.Analytic.Sheaf
