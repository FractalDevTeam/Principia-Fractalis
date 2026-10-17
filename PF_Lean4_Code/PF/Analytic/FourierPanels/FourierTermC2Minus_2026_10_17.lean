/-
# PF.Analytic.FourierPanels.FourierTermC2Minus_2026_10_17

**Minus-side C² layer** — mirror of `FourierTermC2_2026_10_16` for the
sin-side Fourier integrand

  `fourier_minus_term c n u = (exp(u/2) − 1) · 2·exp(−A·exp u) · sin((c/2)·u)`

with `A = π(n+1)²`.

### What this file provides

* `fourier_minus_termD1`, `fourier_minus_termD2` — the first and second
  derivatives (Leibniz triple product).
* `hasDerivAt_fourier_minus_term` — first-derivative witness.
* `hasDerivAt_fourier_minus_termD1` — second-derivative witness.
* `abs_fourier_minus_termD2_le` — the pointwise `C²` bound on `[0, T]`:
  `|fourier_minus_termD2 c n u| ≤ fourier_plus_termM c n T`. Reuses the
  plus-side `fourier_plus_termM` as a valid upper bound (crude but
  sufficient; `|exp(u/2) − 1| ≤ exp(u/2) + 1 ≤ E + 1`).
* Sum versions over `Finset.range N`.

### Design note on private-helper duplication

The plus-side file (`FourierTermC2_2026_10_16.lean`) marks its factor
derivatives (`hasDerivAt_P'`, `hasDerivAt_Q`, `hasDerivAt_Q'`) and factor
bounds (`hP1`, `hP2`, `hQ0`, `hQ1`, `hQ2`, `abs_triple_le`, `abs_sum6_le`)
`private`, i.e. file-local. Rather than modify the plus-side file's
API, this file re-proves them under the same names with `private` scope
inside this file. The proofs are verbatim copies — their statements are
P/Q-only and do not depend on R (cos vs sin), so no genuine divergence.

### Three-axiom bar

Every top-level declaration kernel-clean
`[propext, Classical.choice, Quot.sound]`. No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import PF.Analytic.FourierPanels.FourierTermC2_2026_10_16

namespace PrincipiaTractalis
namespace FourierTermC2

open Real

noncomputable section

/-! ## §1 — Minus-side derivative definitions -/

/-- First derivative of `fourier_minus_term c n` at `u`. -/
def fourier_minus_termD1 (c : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 2) * Real.exp (u / 2)
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
    * Real.sin (c / 2 * u)
  + (Real.exp (u / 2) - 1)
    * (2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u
            * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)))
    * Real.sin (c / 2 * u)
  + (Real.exp (u / 2) - 1)
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
    * ((c / 2) * Real.cos (c / 2 * u))

/-- Second derivative of `fourier_minus_term c n` at `u`. -/
def fourier_minus_termD2 (c : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ((1 / 4) * Real.exp (u / 2))
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
    * Real.sin (c / 2 * u)
  + (Real.exp (u / 2) - 1)
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)
       * Real.exp u
       * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp u
          - (π * ((n : ℝ) + 1) ^ 2)))
    * Real.sin (c / 2 * u)
  + (Real.exp (u / 2) - 1)
    * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
    * (-(c / 2) ^ 2 * Real.sin (c / 2 * u))
  + 2 *
    ((1 / 2) * Real.exp (u / 2)
      * (2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u
              * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)))
      * Real.sin (c / 2 * u))
  + 2 *
    ((1 / 2) * Real.exp (u / 2)
      * (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))
      * ((c / 2) * Real.cos (c / 2 * u)))
  + 2 *
    ((Real.exp (u / 2) - 1)
      * (2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u
              * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)))
      * ((c / 2) * Real.cos (c / 2 * u)))

/-! ## §2 — Minus-side factor derivatives -/

/-- `P_minus(u) = exp(u/2) − 1`, same derivative as `P`. -/
private theorem hasDerivAt_P_minus (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (y / 2) - 1)
      ((1 / 2) * Real.exp (u / 2)) u := by
  have h_half : HasDerivAt (fun y : ℝ ↦ y / 2) ((1 : ℝ) / 2) u := by
    simpa using (hasDerivAt_id' u).div_const 2
  have h_exp : HasDerivAt (fun y : ℝ ↦ Real.exp (y / 2))
      (Real.exp (u / 2) * (1 / 2)) u := h_half.exp
  have h_sub : HasDerivAt (fun y : ℝ ↦ Real.exp (y / 2) - 1)
      (Real.exp (u / 2) * (1 / 2)) u := h_exp.sub_const 1
  convert h_sub using 1
  ring

/-- `R_minus(u) = sin((c/2)·u)`, `R_minus'(u) = (c/2)·cos((c/2)·u)`. -/
private theorem hasDerivAt_R_minus (c u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.sin (c / 2 * y))
      ((c / 2) * Real.cos (c / 2 * u)) u := by
  have h_lin : HasDerivAt (fun y : ℝ ↦ c / 2 * y) (c / 2) u := by
    simpa using (hasDerivAt_id' u).const_mul (c / 2)
  have h_sin : HasDerivAt (fun y : ℝ ↦ Real.sin (c / 2 * y))
      (Real.cos (c / 2 * u) * (c / 2)) u := h_lin.sin
  convert h_sin using 1
  ring

/-- `R_minus'(u) = (c/2)·cos((c/2)·u)`, `R_minus''(u) = -(c/2)²·sin((c/2)·u)`. -/
private theorem hasDerivAt_R_minus' (c u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (c / 2) * Real.cos (c / 2 * y))
      (-(c / 2) ^ 2 * Real.sin (c / 2 * u)) u := by
  have h_lin : HasDerivAt (fun y : ℝ ↦ c / 2 * y) (c / 2) u := by
    simpa using (hasDerivAt_id' u).const_mul (c / 2)
  have h_cos : HasDerivAt (fun y : ℝ ↦ Real.cos (c / 2 * y))
      (-Real.sin (c / 2 * u) * (c / 2)) u := h_lin.cos
  have h := h_cos.const_mul (c / 2)
  convert h using 1
  ring

/-! ## §3 — Private helpers (copies of plus-side's file-local privates) -/

/-- Copy of plus-side `hasDerivAt_P'` (file-local, not accessible from here). -/
private theorem hasDerivAt_P'_local (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (1 / 2) * Real.exp (y / 2))
      ((1 / 4) * Real.exp (u / 2)) u := by
  have h_half : HasDerivAt (fun y : ℝ ↦ y / 2) ((1 : ℝ) / 2) u := by
    simpa using (hasDerivAt_id' u).div_const 2
  have h_exp : HasDerivAt (fun y : ℝ ↦ Real.exp (y / 2))
      (Real.exp (u / 2) * (1 / 2)) u := h_half.exp
  have h := h_exp.const_mul (1 / 2)
  convert h using 1
  ring

/-- Copy of plus-side `hasDerivAt_Q`. -/
private theorem hasDerivAt_Q_local (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp y))
      (2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u
            * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u))) u := by
  set A := π * ((n : ℝ) + 1) ^ 2
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

/-- Copy of plus-side `hasDerivAt_Q'`. -/
private theorem hasDerivAt_Q'_local (n : ℕ) (u : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦ 2 * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp y
                        * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp y)))
      (2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u) * Real.exp u
        * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp u
           - (π * ((n : ℝ) + 1) ^ 2))) u := by
  set A := π * ((n : ℝ) + 1) ^ 2
  have h_exp_y : HasDerivAt (fun y : ℝ ↦ Real.exp y) (Real.exp u) u := by
    simpa using (hasDerivAt_id' u).exp
  have h_neg_A_exp : HasDerivAt (fun y : ℝ ↦ -A * Real.exp y) (-A * Real.exp u) u :=
    h_exp_y.const_mul (-A)
  have h_outer_exp : HasDerivAt (fun y : ℝ ↦ Real.exp (-A * Real.exp y))
      (Real.exp (-A * Real.exp u) * (-A * Real.exp u)) u := h_neg_A_exp.exp
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

/-! ## §4 — Derivative witnesses -/

/-- `fourier_minus_term c n` has derivative `fourier_minus_termD1 c n u` at `u`. -/
theorem hasDerivAt_fourier_minus_term (c : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ fourier_minus_term c n y) (fourier_minus_termD1 c n u) u := by
  have h := hasDerivAt_mul3 (hasDerivAt_P_minus u) (hasDerivAt_Q_local n u)
    (hasDerivAt_R_minus c u)
  simp only [fourier_minus_term, fourier_minus_termD1]
  convert h using 1

/-- `fourier_minus_termD1 c n` has derivative `fourier_minus_termD2 c n u` at `u`. -/
theorem hasDerivAt_fourier_minus_termD1 (c : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ fourier_minus_termD1 c n y) (fourier_minus_termD2 c n u) u := by
  have hT1 := hasDerivAt_mul3 (hasDerivAt_P'_local u) (hasDerivAt_Q_local n u)
    (hasDerivAt_R_minus c u)
  have hT2 := hasDerivAt_mul3 (hasDerivAt_P_minus u) (hasDerivAt_Q'_local n u)
    (hasDerivAt_R_minus c u)
  have hT3 := hasDerivAt_mul3 (hasDerivAt_P_minus u) (hasDerivAt_Q_local n u)
    (hasDerivAt_R_minus' c u)
  have h := (hT1.add hT2).add hT3
  simp only [fourier_minus_termD1, fourier_minus_termD2]
  convert h using 1
  ring

/-! ## §5 — Factor bound helpers (copies of plus-side's file-local privates) -/

private lemma u_sub_A_exp_u_le_neg_A_local {A u : ℝ} (hA : (1 : ℝ) ≤ A) (hu : 0 ≤ u) :
    u - A * Real.exp u ≤ -A := by
  have h_exp_u : (1 : ℝ) + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h_exp_u_ge_one : (1 : ℝ) ≤ Real.exp u := by linarith
  have h_A_exp_ge : A * (1 + u) ≤ A * Real.exp u :=
    mul_le_mul_of_nonneg_left h_exp_u (by linarith : (0 : ℝ) ≤ A)
  nlinarith [h_A_exp_ge, hA, hu]

private lemma exp_u_mul_exp_neg_A_exp_u_le_local {A u : ℝ} (hA : (1 : ℝ) ≤ A) (hu : 0 ≤ u) :
    Real.exp u * Real.exp (-A * Real.exp u) ≤ Real.exp (-A) := by
  have h_combine : Real.exp u * Real.exp (-A * Real.exp u)
      = Real.exp (u + (-A * Real.exp u)) := (Real.exp_add u (-A * Real.exp u)).symm
  rw [h_combine]
  have h_eq : u + (-A * Real.exp u) = u - A * Real.exp u := by ring
  rw [h_eq]
  exact Real.exp_le_exp.mpr (u_sub_A_exp_u_le_neg_A_local hA hu)

private lemma exp_neg_A_exp_u_le_exp_neg_A_local {A u : ℝ} (hA : 0 ≤ A) (hu : 0 ≤ u) :
    Real.exp (-A * Real.exp u) ≤ Real.exp (-A) := by
  have h_exp_u_ge : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  have h_mul : -A * Real.exp u ≤ -A := by nlinarith [h_exp_u_ge, hA]
  exact Real.exp_le_exp.mpr h_mul

/-! ## §6 — Factor absolute bounds on `u ∈ [0, T]` (minus-side specifics + copies) -/

section FactorBounds

variable {c : ℝ} {n : ℕ} {u T : ℝ}

/-- `|P_minus| = |exp(u/2) − 1| ≤ E + 1` on `[0, T]`. Loose; the tight bound
is `E − 1` on `[0, T]` with `u ≥ 0`, but `E + 1` keeps the structure
matching plus-side's M. -/
private lemma hP0_minus (hu : 0 ≤ u) (hT : u ≤ T) :
    |Real.exp (u / 2) - 1| ≤ Real.exp (T / 2) + 1 := by
  have h1 : Real.exp (u / 2) ≤ Real.exp (T / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : (0 : ℝ) ≤ Real.exp (u / 2) := (Real.exp_pos _).le
  rcases le_or_gt 1 (Real.exp (u / 2)) with h | h
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

private lemma hP1_local (hu : 0 ≤ u) (hT : u ≤ T) :
    |(1 / 2) * Real.exp (u / 2)| ≤ Real.exp (T / 2) / 2 := by
  have h1 : Real.exp (u / 2) ≤ Real.exp (T / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : (0 : ℝ) ≤ (1 / 2) * Real.exp (u / 2) := by
    have := Real.exp_pos (u / 2); linarith
  rw [abs_of_nonneg h2]
  linarith

private lemma hP2_local (hu : 0 ≤ u) (hT : u ≤ T) :
    |(1 / 4) * Real.exp (u / 2)| ≤ Real.exp (T / 2) / 4 := by
  have h1 : Real.exp (u / 2) ≤ Real.exp (T / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : (0 : ℝ) ≤ (1 / 4) * Real.exp (u / 2) := by
    have := Real.exp_pos (u / 2); linarith
  rw [abs_of_nonneg h2]
  linarith

private lemma hQ0_local (hu : 0 ≤ u) :
    |2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u)|
      ≤ 2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2)) := by
  have hA : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
  have hpos : (0 : ℝ) ≤ 2 * Real.exp (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u) := by
    have := Real.exp_pos (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp u); linarith
  rw [abs_of_nonneg hpos]
  have h_mono := exp_neg_A_exp_u_le_exp_neg_A_local hA hu
  linarith

private lemma hQ1_local (hu : 0 ≤ u) :
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
    exp_u_mul_exp_neg_A_exp_u_le_local hA_ge_one hu
  have h_eq : (-A * Real.exp u * Real.exp (-A * Real.exp u))
      = -(A * (Real.exp u * Real.exp (-A * Real.exp u))) := by ring
  have h_bound : |-A * Real.exp u * Real.exp (-A * Real.exp u)|
      ≤ A * Real.exp (-A) := by
    rw [h_eq, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤
      A * (Real.exp u * Real.exp (-A * Real.exp u)))]
    exact mul_le_mul_of_nonneg_left h_prod hA_pos.le
  rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
  linarith

private lemma hQ2_local (hu : 0 ≤ u) (hT : u ≤ T) :
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
    exp_u_mul_exp_neg_A_exp_u_le_local hA_ge_one hu
  have h_A_exp_u_ge_one : (1 : ℝ) ≤ A * Real.exp u := by
    have h_exp_u_ge : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
    nlinarith [hA_ge_one, h_exp_u_ge]
  have h_sub_nn : (0 : ℝ) ≤ A * Real.exp u - 1 := by linarith
  have h_sub_le : A * Real.exp u - 1 ≤ A * Real.exp T - 1 := by
    nlinarith [h_exp_u_T, hA_pos]
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

/-- `|R_minus| = |sin((c/2)·u)| ≤ 1`. -/
private lemma hR0_minus (c u : ℝ) : |Real.sin (c / 2 * u)| ≤ 1 := Real.abs_sin_le_one _

/-- `|R_minus'| = |(c/2)·cos((c/2)·u)| ≤ |c|/2`. -/
private lemma hR1_minus (c u : ℝ) : |(c / 2) * Real.cos (c / 2 * u)| ≤ |c| / 2 := by
  rw [abs_mul, show |c / 2| = |c| / 2 from by rw [abs_div, abs_two]]
  have h_cos : |Real.cos (c / 2 * u)| ≤ 1 := Real.abs_cos_le_one _
  have h_c_half_nn : (0 : ℝ) ≤ |c| / 2 := by positivity
  calc |c| / 2 * |Real.cos (c / 2 * u)|
      ≤ |c| / 2 * 1 := mul_le_mul_of_nonneg_left h_cos h_c_half_nn
    _ = |c| / 2 := by ring

/-- `|R_minus''| = |-(c/2)²·sin((c/2)·u)| ≤ (c/2)²`. -/
private lemma hR2_minus (c u : ℝ) : |-(c / 2) ^ 2 * Real.sin (c / 2 * u)| ≤ (c / 2) ^ 2 := by
  rw [abs_mul, show |(-(c / 2) ^ 2 : ℝ)| = (c / 2) ^ 2 from by
    rw [abs_neg, abs_of_nonneg (sq_nonneg _)]]
  have h_sin : |Real.sin (c / 2 * u)| ≤ 1 := Real.abs_sin_le_one _
  nlinarith [sq_nonneg (c / 2)]

end FactorBounds

/-! ## §7 — Triangle-inequality helpers -/

private theorem abs_triple_le_local {x y z bx by' bz : ℝ}
    (hx : |x| ≤ bx) (hy : |y| ≤ by') (hz : |z| ≤ bz) :
    |x * y * z| ≤ bx * by' * bz := by
  have hbx : 0 ≤ bx := (abs_nonneg x).trans hx
  have hby : 0 ≤ by' := (abs_nonneg y).trans hy
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg y) hbx) hz (abs_nonneg z)
    (mul_nonneg hbx hby)

private theorem abs_sum6_le_local {x₁ x₂ x₃ x₄ x₅ x₆ b₁ b₂ b₃ b₄ b₅ b₆ : ℝ}
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

/-! ## §8 — The minus-side `C²` bound -/

/-- **★ Fourier `C²` BOUND, minus-side single term ★** — on `u ∈ [0, T]`:
`|fourier_minus_termD2 c n u| ≤ fourier_plus_termM c n T`. Reuses plus-side `M`. -/
theorem abs_fourier_minus_termD2_le (c T : ℝ) (n : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hT : u ≤ T) :
    |fourier_minus_termD2 c n u| ≤ fourier_plus_termM c n T := by
  have h1 := abs_triple_le_local (hP2_local hu hT) (hQ0_local (n := n) hu) (hR0_minus c u)
  have h2 := abs_triple_le_local (hP0_minus hu hT) (hQ2_local (n := n) hu hT) (hR0_minus c u)
  have h3 := abs_triple_le_local (hP0_minus hu hT) (hQ0_local (n := n) hu) (hR2_minus c u)
  have h4 := abs_triple_le_local (hP1_local hu hT) (hQ1_local (n := n) hu) (hR0_minus c u)
  have h5 := abs_triple_le_local (hP1_local hu hT) (hQ0_local (n := n) hu) (hR1_minus c u)
  have h6 := abs_triple_le_local (hP0_minus hu hT) (hQ1_local (n := n) hu) (hR1_minus c u)
  simp only [fourier_minus_termD2, fourier_plus_termM]
  refine le_trans (abs_sum6_le_local h1 h2 h3 h4 h5 h6) (le_of_eq ?_)
  ring

/-! ## §9 — Sum versions -/

theorem hasDerivAt_fourier_minus_term_sum (c : ℝ) (N : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ ∑ n ∈ Finset.range N, fourier_minus_term c n y)
      (∑ n ∈ Finset.range N, fourier_minus_termD1 c n u) u :=
  HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_fourier_minus_term c n u

theorem hasDerivAt_fourier_minus_termD1_sum (c : ℝ) (N : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ ∑ n ∈ Finset.range N, fourier_minus_termD1 c n y)
      (∑ n ∈ Finset.range N, fourier_minus_termD2 c n u) u :=
  HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_fourier_minus_termD1 c n u

/-- **★ Fourier `C²` BOUND, minus-side N-term sum ★** — on `u ∈ [0, T]`:
`|∑ n < N, fourier_minus_termD2 c n u| ≤ ∑ n < N, fourier_plus_termM c n T`. -/
theorem abs_fourier_minus_termD2_sum_le (c T : ℝ) (N : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hT : u ≤ T) :
    |∑ n ∈ Finset.range N, fourier_minus_termD2 c n u|
      ≤ ∑ n ∈ Finset.range N, fourier_plus_termM c n T :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun n _ ↦ abs_fourier_minus_termD2_le c T n hu hT)

end

end FourierTermC2
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.FourierTermC2.hasDerivAt_fourier_minus_term
#print axioms PrincipiaTractalis.FourierTermC2.hasDerivAt_fourier_minus_termD1
#print axioms PrincipiaTractalis.FourierTermC2.abs_fourier_minus_termD2_le
#print axioms PrincipiaTractalis.FourierTermC2.hasDerivAt_fourier_minus_term_sum
#print axioms PrincipiaTractalis.FourierTermC2.hasDerivAt_fourier_minus_termD1_sum
#print axioms PrincipiaTractalis.FourierTermC2.abs_fourier_minus_termD2_sum_le
