/-
# PF.Analytic.FourierPanels.FourierTermC2_2026_10_16

**Generic `C²` layer** for one term of the Fourier panel integrand:

  `fourier_plus_term c n u = (exp(u/2) + 1) · (2 · exp(−π(n+1)² · exp u))
                             · cos((c/2) · u)`

with `c, n` free. The full integrand `nodeR_fourier_plus_at_c_N3 u` is the
`n = 0, 1, 2` sum of `fourier_plus_term c n u`.

**Mirror of** `PF/Analytic/XiQuadrature.lean` lines 493–754 (the `thetaTerm`
C² chain). Same three-factor shape, same `hasDerivAt_mul3` scaffold, same
six-term Leibniz expansion. The only novelty is that `exp u` appears
inside the exponent of the exp factor (chain rule), which produces an
extra `exp u` in both derivatives.

**Deliverables:**
* `fourier_plus_term`, `fourier_plus_termD1`, `fourier_plus_termD2`,
  `fourier_plus_termM` — the three-factor product, its first and second
  derivatives, and the explicit `C²` constant.
* `hasDerivAt_fourier_plus_term`, `hasDerivAt_fourier_plus_termD1` — the
  derivative chain.
* `abs_fourier_plus_termD2_le` — the pointwise `C²` bound on `[0, T]`.
* `abs_fourier_plus_termD2_sum_le` — the `N3` sum bound.
* Analogous `_minus_` variants (sin in place of cos, `exp(u/2) − 1` growth
  factor).

Three-axiom bar: every top-level declaration prints exactly
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

namespace PrincipiaTractalis
namespace FourierTermC2

open Real

noncomputable section

/-! ## §1 — Definitions -/

/-- One `n`-term of the plus-side `N3` sum × cos factor:
`(exp(u/2) + 1) · 2·exp(-π(n+1)²·exp u) · cos((c/2) · u)`. -/
def fourier_plus_term (c : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (Real.exp (u / 2) + 1)
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
    * Real.cos (c / 2 * u)

/-- One `n`-term of the minus-side `N3` sum × sin factor:
`(exp(u/2) − 1) · 2·exp(-π(n+1)²·exp u) · sin((c/2) · u)`. -/
def fourier_minus_term (c : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (Real.exp (u / 2) - 1)
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
    * Real.sin (c / 2 * u)

/-- First derivative of `fourier_plus_term c n` at `u`.
Parenthesization matches the `hasDerivAt_mul3` output. -/
def fourier_plus_termD1 (c : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 2) * Real.exp (u / 2)
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
    * Real.cos (c / 2 * u)
  + (Real.exp (u / 2) + 1)
    * (2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u
            * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)))
    * Real.cos (c / 2 * u)
  + (Real.exp (u / 2) + 1)
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
    * (-(c / 2) * Real.sin (c / 2 * u))

/-- Second derivative of `fourier_plus_term c n` at `u`. The six-term
Leibniz expansion `P''QR + PQ''R + PQR'' + 2P'Q'R + 2P'QR' + 2PQ'R'`
with
  `P = exp(u/2) + 1,   P' = (1/2)·exp(u/2),   P'' = (1/4)·exp(u/2)`
  `Q = 2·exp(-A·exp u),` where `A = π(n+1)²`,
     `Q' = -2A·exp u · exp(-A·exp u)`,
     `Q'' = 2·exp(-A·exp u) · exp u · (A²·exp u − A)
          = 2A·exp u · (A·exp u − 1) · exp(-A·exp u)`,
  `R = cos((c/2)·u),   R' = -(c/2)·sin((c/2)·u),  R'' = -(c/2)²·cos((c/2)·u)`.
-/
def fourier_plus_termD2 (c : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  -- P''·Q·R
  ((1 / 4) * Real.exp (u / 2))
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
    * Real.cos (c / 2 * u)
  + -- P·Q''·R
    (Real.exp (u / 2) + 1)
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)
       * Real.exp u
       * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp u
          - (π * ((n : ℝ) + 1) ^ 2)))
    * Real.cos (c / 2 * u)
  + -- P·Q·R''
    (Real.exp (u / 2) + 1)
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
    * (-(c / 2) ^ 2 * Real.cos (c / 2 * u))
  + 2 * -- P'·Q'·R
    ((1 / 2) * Real.exp (u / 2)
      * (2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u
              * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)))
      * Real.cos (c / 2 * u))
  + 2 * -- P'·Q·R'
    ((1 / 2) * Real.exp (u / 2)
      * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
      * (-(c / 2) * Real.sin (c / 2 * u)))
  + 2 * -- P·Q'·R'
    ((Real.exp (u / 2) + 1)
      * (2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u
              * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)))
      * (-(c / 2) * Real.sin (c / 2 * u)))

/-- Explicit `C²` upper bound for `|fourier_plus_termD2 c n u|` on `u ∈ [0, T]`.

With `A := π(n+1)²`, `E := exp(T/2)` (so `|P| ≤ E+1`, `|P'| ≤ E/2`, `|P''| ≤ E/4`),
`B := exp(-A)` (so `|Q| ≤ 2B`, `exp(-A·exp u) ≤ B` on `u ≥ 0`),
`|Q'| ≤ 2A·B` (max at `u = 0`), `|Q''| ≤ 2A·(A·exp T − 1)·B` using the fact
`exp u · exp(-A·exp u) ≤ B` on `[0, T]` (monotone-decreasing for `A ≥ 1`),
`|R| ≤ 1`, `|R'| ≤ |c|/2`, `|R''| ≤ (c/2)²`:

  `M(c, n, T) = (E/4)·2B + (E+1)·2A·(A·exp T − 1)·B
              + (E+1)·2B·(c/2)²
              + 2 · (E/2)·2A·B
              + 2 · (E/2)·2B·(|c|/2)
              + 2 · (E+1)·2A·B·(|c|/2)`.

Requires `A ≥ 1`, i.e. `π(n+1)² ≥ 1`. For `n ≥ 0`, `A ≥ π > 1`. ✓
-/
def fourier_plus_termM (c : ℝ) (n : ℕ) (T : ℝ) : ℝ :=
  let A := π * ((n : ℝ) + 1) ^ 2
  let E := Real.exp (T / 2)
  let B := Real.exp (-A)
  (E / 4) * (2 * B)
  + (E + 1) * (2 * A * (A * Real.exp T - 1) * B)
  + (E + 1) * (2 * B) * (c / 2) ^ 2
  + 2 * ((E / 2) * (2 * A * B))
  + 2 * ((E / 2) * (2 * B) * (|c| / 2))
  + 2 * ((E + 1) * (2 * A * B) * (|c| / 2))

/-! ## §2 — Private factor derivatives -/

/-- Pointwise Leibniz rule for a triple product (copied verbatim from
`XiQuadrature.lean:540` for use within this file). -/
theorem hasDerivAt_mul3 {P Q R : ℝ → ℝ} {p q r u : ℝ}
    (hP : HasDerivAt P p u) (hQ : HasDerivAt Q q u) (hR : HasDerivAt R r u) :
    HasDerivAt (fun y ↦ P y * Q y * R y)
      (p * Q u * R u + P u * q * R u + P u * Q u * r) u := by
  have h := (hP.fun_mul hQ).fun_mul hR
  convert h using 1
  ring

/-- `P(u) = exp(u/2) + 1`, `P'(u) = (1/2) · exp(u/2)`. -/
private theorem hasDerivAt_P (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (y / 2) + 1)
      ((1 / 2) * Real.exp (u / 2)) u := by
  have h_half : HasDerivAt (fun y : ℝ ↦ y / 2) ((1 : ℝ) / 2) u := by
    simpa using (hasDerivAt_id' u).div_const 2
  have h_exp : HasDerivAt (fun y : ℝ ↦ Real.exp (y / 2))
      (Real.exp (u / 2) * (1 / 2)) u := h_half.exp
  have h_add : HasDerivAt (fun y : ℝ ↦ Real.exp (y / 2) + 1)
      (Real.exp (u / 2) * (1 / 2)) u := h_exp.add_const 1
  convert h_add using 1
  ring

/-- `P'(u) = (1/2) · exp(u/2)`, `P''(u) = (1/4) · exp(u/2)`. -/
private theorem hasDerivAt_P' (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (1 / 2) * Real.exp (y / 2))
      ((1 / 4) * Real.exp (u / 2)) u := by
  have h_half : HasDerivAt (fun y : ℝ ↦ y / 2) ((1 : ℝ) / 2) u := by
    simpa using (hasDerivAt_id' u).div_const 2
  have h_exp : HasDerivAt (fun y : ℝ ↦ Real.exp (y / 2))
      (Real.exp (u / 2) * (1 / 2)) u := h_half.exp
  have h := h_exp.const_mul (1 / 2)
  convert h using 1
  ring

/-- The exp factor: `Q(u) = 2 · exp(-A · exp u)`,
`Q'(u) = 2 · (-A · exp u) · exp(-A · exp u)`. Chain rule applied twice. -/
private theorem hasDerivAt_Q (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp y))
      (2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u
            * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))) u := by
  set A := π * ((n : ℝ) + 1) ^ 2 with hA_def
  have h_exp_y : HasDerivAt (fun y : ℝ ↦ Real.exp y) (Real.exp u) u := by
    simpa using (hasDerivAt_id' u).exp
  have h_scale : HasDerivAt (fun y : ℝ ↦ -A * Real.exp y) (-A * Real.exp u) u :=
    h_exp_y.const_mul (-A)
  have h_outer : HasDerivAt (fun y : ℝ ↦ Real.exp (-A * Real.exp y))
      (Real.exp (-A * Real.exp u) * (-A * Real.exp u)) u := h_scale.exp
  have h_two : HasDerivAt (fun y : ℝ ↦ 2 * Real.exp (-A * Real.exp y))
      (2 * (Real.exp (-A * Real.exp u) * (-A * Real.exp u))) u :=
    h_outer.const_mul 2
  convert h_two using 1
  ring

/-- `Q'(u) = -2A · exp u · exp(-A · exp u)`,
`Q''(u) = 2 · exp(-A · exp u) · exp u · (A² · exp u − A)`
        = `2A · exp u · (A · exp u − 1) · exp(-A · exp u)`. -/
private theorem hasDerivAt_Q' (n : ℕ) (u : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦ 2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp y
                        * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp y)))
      (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u) * Real.exp u
        * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp u
           - (π * ((n : ℝ) + 1) ^ 2))) u := by
  set A := π * ((n : ℝ) + 1) ^ 2 with hA_def
  have h_exp_y : HasDerivAt (fun y : ℝ ↦ Real.exp y) (Real.exp u) u := by
    simpa using (hasDerivAt_id' u).exp
  have h_neg_A_exp : HasDerivAt (fun y : ℝ ↦ -A * Real.exp y) (-A * Real.exp u) u :=
    h_exp_y.const_mul (-A)
  -- G(y) = exp(-A · exp y), G'(y) = exp(-A·exp y) · (-A · exp y) = -A·exp y·exp(-A·exp y)
  have h_outer_exp : HasDerivAt (fun y : ℝ ↦ Real.exp (-A * Real.exp y))
      (Real.exp (-A * Real.exp u) * (-A * Real.exp u)) u := h_neg_A_exp.exp
  -- product of (-A·exp y) and exp(-A·exp y)
  have h_prod_inner : HasDerivAt
      (fun y : ℝ ↦ -A * Real.exp y * Real.exp (-A * Real.exp y))
      (-A * Real.exp u * Real.exp (-A * Real.exp u)
        + (-A * Real.exp u) * (Real.exp (-A * Real.exp u) * (-A * Real.exp u))) u :=
    h_neg_A_exp.mul h_outer_exp
  have h_two : HasDerivAt
      (fun y : ℝ ↦ 2 * (-A * Real.exp y * Real.exp (-A * Real.exp y)))
      (2 * ((-A) * Real.exp u * Real.exp (-A * Real.exp u)
            + (-A * Real.exp u) * (Real.exp (-A * Real.exp u) * (-A * Real.exp u)))) u :=
    h_prod_inner.const_mul 2
  convert h_two using 1
  ring

/-- `R(u) = cos((c/2) · u)`, `R'(u) = -(c/2) · sin((c/2) · u)`. -/
private theorem hasDerivAt_R (c u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.cos (c / 2 * y))
      (-(c / 2) * Real.sin (c / 2 * u)) u := by
  have h_arg : HasDerivAt (fun y : ℝ ↦ c / 2 * y) (c / 2) u := by
    simpa using (hasDerivAt_id' u).const_mul (c / 2)
  have h := h_arg.cos
  convert h using 1
  ring

/-- `R'(u) = -(c/2) · sin((c/2) · u)`, `R''(u) = -(c/2)² · cos((c/2) · u)`. -/
private theorem hasDerivAt_R' (c u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ -(c / 2) * Real.sin (c / 2 * y))
      (-(c / 2) ^ 2 * Real.cos (c / 2 * u)) u := by
  have h_arg : HasDerivAt (fun y : ℝ ↦ c / 2 * y) (c / 2) u := by
    simpa using (hasDerivAt_id' u).const_mul (c / 2)
  have h_sin : HasDerivAt (fun y : ℝ ↦ Real.sin (c / 2 * y))
      (Real.cos (c / 2 * u) * (c / 2)) u := h_arg.sin
  have h := h_sin.const_mul (-(c / 2))
  convert h using 1
  ring

/-! ## §3 — Derivative chain -/

/-- `fourier_plus_term c n` has derivative `fourier_plus_termD1 c n u` at every `u`. -/
theorem hasDerivAt_fourier_plus_term (c : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ fourier_plus_term c n y) (fourier_plus_termD1 c n u) u := by
  have h := hasDerivAt_mul3 (hasDerivAt_P u) (hasDerivAt_Q n u) (hasDerivAt_R c u)
  simp only [fourier_plus_term, fourier_plus_termD1]
  convert h using 1

/-- `fourier_plus_termD1 c n` has derivative `fourier_plus_termD2 c n u` at every `u`. -/
theorem hasDerivAt_fourier_plus_termD1 (c : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ fourier_plus_termD1 c n y) (fourier_plus_termD2 c n u) u := by
  have hT1 := hasDerivAt_mul3 (hasDerivAt_P' u) (hasDerivAt_Q n u) (hasDerivAt_R c u)
  have hT2 := hasDerivAt_mul3 (hasDerivAt_P u) (hasDerivAt_Q' n u) (hasDerivAt_R c u)
  have hT3 := hasDerivAt_mul3 (hasDerivAt_P u) (hasDerivAt_Q n u) (hasDerivAt_R' c u)
  have h := (hT1.add hT2).add hT3
  simp only [fourier_plus_termD1, fourier_plus_termD2]
  convert h using 1
  ring

/-! ## §4 — Factor absolute bounds on `u ∈ [0, T]` -/

/-- Core monotonicity: `u − A · exp u ≤ -A` on `u ∈ [0, ∞)` when `A ≥ 1`.
Proof: `g(u) = u − A · exp u` has `g'(u) = 1 − A · exp u ≤ 1 − A ≤ 0` for
`u ≥ 0`, so `g` is antitone on `[0, ∞)`; hence `g(u) ≤ g(0) = -A`. -/
private lemma u_sub_A_exp_u_le_neg_A {A u : ℝ} (hA : (1 : ℝ) ≤ A) (hu : 0 ≤ u) :
    u - A * Real.exp u ≤ -A := by
  -- exp u ≥ 1 + u ≥ 1 (from add_one_le_exp with x=u ≥ 0)
  have h_exp_u : (1 : ℝ) + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h_exp_u_ge_one : (1 : ℝ) ≤ Real.exp u := by linarith
  have h_A_exp_ge : A * (1 + u) ≤ A * Real.exp u :=
    mul_le_mul_of_nonneg_left h_exp_u (by linarith : (0 : ℝ) ≤ A)
  nlinarith [h_A_exp_ge, hA, hu]

/-- Monotone-product bound: `exp u · exp(-A · exp u) ≤ exp(-A)` on `u ≥ 0`
when `A ≥ 1`. Equivalent to `exp(u − A · exp u) ≤ exp(-A)` via `exp_add`. -/
private lemma exp_u_mul_exp_neg_A_exp_u_le {A u : ℝ} (hA : (1 : ℝ) ≤ A) (hu : 0 ≤ u) :
    Real.exp u * Real.exp (-A * Real.exp u) ≤ Real.exp (-A) := by
  have h_combine : Real.exp u * Real.exp (-A * Real.exp u)
      = Real.exp (u + (-A * Real.exp u)) := (Real.exp_add u (-A * Real.exp u)).symm
  rw [h_combine]
  have h_eq : u + (-A * Real.exp u) = u - A * Real.exp u := by ring
  rw [h_eq]
  exact Real.exp_le_exp.mpr (u_sub_A_exp_u_le_neg_A hA hu)

/-- `exp(-A · exp u) ≤ exp(-A)` on `u ≥ 0` for `A ≥ 0` (not just `A ≥ 1`). -/
private lemma exp_neg_A_exp_u_le_exp_neg_A {A u : ℝ} (hA : 0 ≤ A) (hu : 0 ≤ u) :
    Real.exp (-A * Real.exp u) ≤ Real.exp (-A) := by
  have h_exp_u_ge : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  have h_mul : -A * Real.exp u ≤ -A := by nlinarith [h_exp_u_ge, hA]
  exact Real.exp_le_exp.mpr h_mul

/-! Absolute-value bounds on P, P', P'', Q, Q', Q'', R, R', R'' at `u ∈ [0, T]`. -/
section FactorBounds

variable {c : ℝ} {n : ℕ} {u T : ℝ}

private lemma hP0 (hu : 0 ≤ u) (hT : u ≤ T) :
    |Real.exp (u / 2) + 1| ≤ Real.exp (T / 2) + 1 := by
  have h1 : Real.exp (u / 2) ≤ Real.exp (T / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : (0 : ℝ) ≤ Real.exp (u / 2) + 1 := by
    have := Real.exp_pos (u / 2); linarith
  rw [abs_of_nonneg h2]
  linarith

private lemma hP1 (hu : 0 ≤ u) (hT : u ≤ T) :
    |(1 / 2) * Real.exp (u / 2)| ≤ Real.exp (T / 2) / 2 := by
  have h1 : Real.exp (u / 2) ≤ Real.exp (T / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : (0 : ℝ) ≤ (1 / 2) * Real.exp (u / 2) := by
    have := Real.exp_pos (u / 2); linarith
  rw [abs_of_nonneg h2]
  linarith

private lemma hP2 (hu : 0 ≤ u) (hT : u ≤ T) :
    |(1 / 4) * Real.exp (u / 2)| ≤ Real.exp (T / 2) / 4 := by
  have h1 : Real.exp (u / 2) ≤ Real.exp (T / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : (0 : ℝ) ≤ (1 / 4) * Real.exp (u / 2) := by
    have := Real.exp_pos (u / 2); linarith
  rw [abs_of_nonneg h2]
  linarith

private lemma hQ0 (hu : 0 ≤ u) :
    |2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)|
      ≤ 2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2)) := by
  have hA : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
  have hpos : (0 : ℝ) ≤ 2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u) := by
    have := Real.exp_pos (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u); linarith
  rw [abs_of_nonneg hpos]
  have h_mono := exp_neg_A_exp_u_le_exp_neg_A hA hu
  linarith

/-- The key bound: `|Q'| ≤ 2A · exp(-A)` on `u ≥ 0` for `A ≥ 1` (we have `A ≥ π > 1`). -/
private lemma hQ1 (hu : 0 ≤ u) :
    |2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u
          * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))|
      ≤ 2 * (π * ((n : ℝ) + 1) ^ 2) * Real.exp (-(π * ((n : ℝ) + 1) ^ 2)) := by
  set A := π * ((n : ℝ) + 1) ^ 2 with hA_def
  have hA_pos : (0 : ℝ) < A := by positivity
  have hA_ge_one : (1 : ℝ) ≤ A := by
    have hπ : (3.14 : ℝ) < π := Real.pi_gt_d2
    have h_sq : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      nlinarith
    nlinarith [hπ, Real.pi_pos, h_sq]
  have h_exp_pos : (0 : ℝ) < Real.exp u := Real.exp_pos _
  have h_prod : Real.exp u * Real.exp (-A * Real.exp u) ≤ Real.exp (-A) :=
    exp_u_mul_exp_neg_A_exp_u_le hA_ge_one hu
  have h_eq : (-A * Real.exp u * Real.exp (-A * Real.exp u))
      = -(A * (Real.exp u * Real.exp (-A * Real.exp u))) := by ring
  have h_bound : |-A * Real.exp u * Real.exp (-A * Real.exp u)|
      ≤ A * Real.exp (-A) := by
    rw [h_eq, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤
      A * (Real.exp u * Real.exp (-A * Real.exp u)))]
    exact mul_le_mul_of_nonneg_left h_prod hA_pos.le
  rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
  linarith

/-- `|Q''| ≤ 2A · (A · exp T − 1) · exp(-A)` on `u ∈ [0, T]` for `A ≥ 1`. -/
private lemma hQ2 (hu : 0 ≤ u) (hT : u ≤ T) :
    |2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)
       * Real.exp u
       * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp u
          - (π * ((n : ℝ) + 1) ^ 2))|
      ≤ 2 * (π * ((n : ℝ) + 1) ^ 2) * ((π * ((n : ℝ) + 1) ^ 2) * Real.exp T - 1)
        * Real.exp (-(π * ((n : ℝ) + 1) ^ 2)) := by
  set A := π * ((n : ℝ) + 1) ^ 2 with hA_def
  have hA_pos : (0 : ℝ) < A := by positivity
  have hA_ge_one : (1 : ℝ) ≤ A := by
    have hπ : (3.14 : ℝ) < π := Real.pi_gt_d2
    have h_sq : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      nlinarith
    nlinarith [hπ, Real.pi_pos, h_sq]
  have h_exp_pos : (0 : ℝ) < Real.exp u := Real.exp_pos _
  have h_exp_u_T : Real.exp u ≤ Real.exp T := Real.exp_le_exp.mpr hT
  have h_prod : Real.exp u * Real.exp (-A * Real.exp u) ≤ Real.exp (-A) :=
    exp_u_mul_exp_neg_A_exp_u_le hA_ge_one hu
  -- A² · exp u − A = A · (A · exp u − 1), bounded by A · (A · exp T − 1)
  have h_A_exp_u_ge_one : (1 : ℝ) ≤ A * Real.exp u := by
    have h_exp_u_ge : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
    nlinarith [hA_ge_one, h_exp_u_ge]
  have h_sub_nn : (0 : ℝ) ≤ A * Real.exp u - 1 := by linarith
  have h_sub_le : A * Real.exp u - 1 ≤ A * Real.exp T - 1 := by
    nlinarith [h_exp_u_T, hA_pos]
  -- Rewrite the integrand
  have h_rewrite : 2 * Real.exp (-A * Real.exp u) * Real.exp u
                   * (A ^ 2 * Real.exp u - A)
      = 2 * A * (A * Real.exp u - 1) * (Real.exp u * Real.exp (-A * Real.exp u)) := by
    ring
  have h_pos_body : (0 : ℝ) ≤ 2 * A * (A * Real.exp u - 1)
                              * (Real.exp u * Real.exp (-A * Real.exp u)) := by
    have h1 : (0 : ℝ) ≤ 2 * A := by positivity
    have h2 : (0 : ℝ) ≤ A * Real.exp u - 1 := h_sub_nn
    have h3 : (0 : ℝ) ≤ Real.exp u * Real.exp (-A * Real.exp u) := by positivity
    have h12 : (0 : ℝ) ≤ 2 * A * (A * Real.exp u - 1) := mul_nonneg h1 h2
    exact mul_nonneg h12 h3
  rw [h_rewrite, abs_of_nonneg h_pos_body]
  -- Bound 2A · (A · exp u − 1) · (exp u · exp(-A · exp u))
  --      ≤ 2A · (A · exp T − 1) · exp(-A)
  have h_pos_2A : (0 : ℝ) ≤ 2 * A := by positivity
  have h_pos_sub_T : (0 : ℝ) ≤ A * Real.exp T - 1 := by linarith
  have h_pos_prod : (0 : ℝ) ≤ Real.exp u * Real.exp (-A * Real.exp u) := by positivity
  have h_bound1 : 2 * A * (A * Real.exp u - 1) * (Real.exp u * Real.exp (-A * Real.exp u))
                   ≤ 2 * A * (A * Real.exp T - 1) * (Real.exp u * Real.exp (-A * Real.exp u)) := by
    have := mul_le_mul_of_nonneg_right h_sub_le h_pos_prod
    nlinarith [h_pos_2A, h_pos_prod]
  have h_bound2 : 2 * A * (A * Real.exp T - 1) * (Real.exp u * Real.exp (-A * Real.exp u))
                   ≤ 2 * A * (A * Real.exp T - 1) * Real.exp (-A) := by
    have h_coeff_nn : (0 : ℝ) ≤ 2 * A * (A * Real.exp T - 1) := by positivity
    exact mul_le_mul_of_nonneg_left h_prod h_coeff_nn
  linarith

private lemma hR0 (c u : ℝ) : |Real.cos (c / 2 * u)| ≤ 1 := Real.abs_cos_le_one _

private lemma hR1 (c u : ℝ) : |-(c / 2) * Real.sin (c / 2 * u)| ≤ |c| / 2 := by
  rw [abs_mul, abs_neg, show |c / 2| = |c| / 2 from by rw [abs_div, abs_two]]
  have h_sin : |Real.sin (c / 2 * u)| ≤ 1 := Real.abs_sin_le_one _
  have h_c_nn : (0 : ℝ) ≤ |c| := abs_nonneg c
  have h_c_half_nn : (0 : ℝ) ≤ |c| / 2 := by positivity
  calc |c| / 2 * |Real.sin (c / 2 * u)|
      ≤ |c| / 2 * 1 := mul_le_mul_of_nonneg_left h_sin h_c_half_nn
    _ = |c| / 2 := by ring

private lemma hR2 (c u : ℝ) : |-(c / 2) ^ 2 * Real.cos (c / 2 * u)| ≤ (c / 2) ^ 2 := by
  rw [abs_mul, show |(-(c / 2) ^ 2 : ℝ)| = (c / 2) ^ 2 from by
    rw [abs_neg, abs_of_nonneg (sq_nonneg _)]]
  have h_cos : |Real.cos (c / 2 * u)| ≤ 1 := Real.abs_cos_le_one _
  nlinarith [sq_nonneg (c / 2)]

end FactorBounds

/-! ## §5 — Triangle-inequality helpers -/

/-- Triple-product absolute bound (copied from `XiQuadrature.lean:618`). -/
private theorem abs_triple_le {x y z bx by' bz : ℝ}
    (hx : |x| ≤ bx) (hy : |y| ≤ by') (hz : |z| ≤ bz) :
    |x * y * z| ≤ bx * by' * bz := by
  have hbx : 0 ≤ bx := (abs_nonneg x).trans hx
  have hby : 0 ≤ by' := (abs_nonneg y).trans hy
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg y) hbx) hz (abs_nonneg z)
    (mul_nonneg hbx hby)

/-- Six-term triangle inequality in the shape of `fourier_plus_termD2`. -/
private theorem abs_sum6_le {x₁ x₂ x₃ x₄ x₅ x₆ b₁ b₂ b₃ b₄ b₅ b₆ : ℝ}
    (h₁ : |x₁| ≤ b₁) (h₂ : |x₂| ≤ b₂) (h₃ : |x₃| ≤ b₃)
    (h₄ : |x₄| ≤ b₄) (h₅ : |x₅| ≤ b₅) (h₆ : |x₆| ≤ b₆) :
    |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅ + 2 * x₆|
      ≤ b₁ + b₂ + b₃ + 2 * b₄ + 2 * b₅ + 2 * b₆ := by
  have k₄ : |2 * x₄| ≤ 2 * b₄ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₄]
  have k₅ : |2 * x₅| ≤ 2 * b₅ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₅]
  have k₆ : |2 * x₆| ≤ 2 * b₆ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₆]
  calc |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅ + 2 * x₆|
      ≤ |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅| + |2 * x₆| := abs_add _ _
    _ ≤ |x₁ + x₂ + x₃ + 2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂ + x₃ + 2 * x₄) (2 * x₅)]
    _ ≤ |x₁ + x₂ + x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂ + x₃) (2 * x₄)]
    _ ≤ |x₁ + x₂| + |x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂) x₃]
    _ ≤ |x₁| + |x₂| + |x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add x₁ x₂]
    _ ≤ b₁ + b₂ + b₃ + 2 * b₄ + 2 * b₅ + 2 * b₆ := by linarith

/-! ## §6 — The `C²` bound. -/

/-- **★ Fourier `C²` BOUND, single term ★** — on `u ∈ [0, T]`:
`|fourier_plus_termD2 c n u| ≤ fourier_plus_termM c n T`. -/
theorem abs_fourier_plus_termD2_le (c T : ℝ) (n : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hT : u ≤ T) :
    |fourier_plus_termD2 c n u| ≤ fourier_plus_termM c n T := by
  have h1 := abs_triple_le (hP2 hu hT) (hQ0 (n := n) hu) (hR0 c u)
  have h2 := abs_triple_le (hP0 hu hT) (hQ2 (n := n) hu hT) (hR0 c u)
  have h3 := abs_triple_le (hP0 hu hT) (hQ0 (n := n) hu) (hR2 c u)
  have h4 := abs_triple_le (hP1 hu hT) (hQ1 (n := n) hu) (hR0 c u)
  have h5 := abs_triple_le (hP1 hu hT) (hQ0 (n := n) hu) (hR1 c u)
  have h6 := abs_triple_le (hP0 hu hT) (hQ1 (n := n) hu) (hR1 c u)
  simp only [fourier_plus_termD2, fourier_plus_termM]
  refine le_trans (abs_sum6_le h1 h2 h3 h4 h5 h6) (le_of_eq ?_)
  ring

/-! ## §7 — Sum version over `Finset.range N` (for the N3 integrand) -/

/-- First-derivative witness for the sum of `fourier_plus_term c n` over `n < N`. -/
theorem hasDerivAt_fourier_plus_term_sum (c : ℝ) (N : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ ∑ n ∈ Finset.range N, fourier_plus_term c n y)
      (∑ n ∈ Finset.range N, fourier_plus_termD1 c n u) u :=
  HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_fourier_plus_term c n u

/-- Second-derivative witness for the sum of `fourier_plus_term c n` over `n < N`. -/
theorem hasDerivAt_fourier_plus_termD1_sum (c : ℝ) (N : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ ∑ n ∈ Finset.range N, fourier_plus_termD1 c n y)
      (∑ n ∈ Finset.range N, fourier_plus_termD2 c n u) u :=
  HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_fourier_plus_termD1 c n u

/-- **★ Fourier `C²` BOUND, N-term sum ★** — on `u ∈ [0, T]`:
`|∑ n < N, fourier_plus_termD2 c n u| ≤ ∑ n < N, fourier_plus_termM c n T`. -/
theorem abs_fourier_plus_termD2_sum_le (c T : ℝ) (N : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hT : u ≤ T) :
    |∑ n ∈ Finset.range N, fourier_plus_termD2 c n u|
      ≤ ∑ n ∈ Finset.range N, fourier_plus_termM c n T :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun n _ ↦ abs_fourier_plus_termD2_le c T n hu hT)

end

end FourierTermC2
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.FourierTermC2.hasDerivAt_fourier_plus_term
#print axioms PrincipiaTractalis.FourierTermC2.hasDerivAt_fourier_plus_termD1
#print axioms PrincipiaTractalis.FourierTermC2.abs_fourier_plus_termD2_le
#print axioms PrincipiaTractalis.FourierTermC2.hasDerivAt_fourier_plus_term_sum
#print axioms PrincipiaTractalis.FourierTermC2.hasDerivAt_fourier_plus_termD1_sum
#print axioms PrincipiaTractalis.FourierTermC2.abs_fourier_plus_termD2_sum_le
