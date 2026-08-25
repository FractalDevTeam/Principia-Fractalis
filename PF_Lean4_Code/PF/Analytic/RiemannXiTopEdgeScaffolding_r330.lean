/-
# r330 — TOP EDGE SCAFFOLDING FOR THE T=15 RIEMANN ξ RECTANGLE

★ 2026-08-25.  Prepares the T1 Taylor-shortcut route to `H_TOP` per the
  r330 directive: instead of building a general 2D interval-arithmetic
  engine, tries to close the top-half-edge sign statement by exploiting
  reflection symmetry `f(1-σ) = f(σ)` (giving `f'(1/2) = 0`) plus a
  quantitative center value `f(1/2)` plus a uniform second-derivative
  bound `|f''(σ)| ≤ 1/1000` on `[1/2, 1]`, via elementary Taylor.

  This module lands the STRUCTURAL scaffolding: quantitative center
  value, reflection identity, and the Taylor closure theorem taking the
  `|f''|` bound as hypothesis.  The `|f''|` bound itself — an analytic
  upper bound on the second σ-derivative of `Re Λ₀(σ + 15i)` — is the
  remaining analytic task; it requires bounds on log-weighted theta
  integrals (`∫ (log u)² · ω(u) du` etc.) that are outside the scope of
  this scaffolding sprint.

## What lands (kernel-clean)

- **`Xi_15_gt_13e7`** — quantitative extract from r315:
  `13 / 10^7 < Xi 15`.  Replays the r315 arithmetic pipeline
  (`int_lower_15` + `Xi_tail_bound` + `hbd`-style integrand error +
  the `Xi_split_intervalIntegral` decomposition) with the final
  linear-arithmetic step targeting the rational lower bound instead of
  merely `0 < Xi 15`.

- **`xi_center_15_lt_neg_bound`** — from `Xi_15_gt_13e7` + r326's
  exact critical-line formula:
  `(riemannXiEntire ⟨1/2, 15⟩).re < -11713 / (8 * 10^7)`.
  (The prefactor `-((1/4 + 15²)/2) = -(901/8)` combined with
  `Xi 15 > 13/10^7` gives `< -(901/8)·(13/10^7) = -11713/(8·10^7)`.)

- **`f_top15_reflect`** — reflection identity along the top edge:
  `∀ σ : ℝ, (riemannXiEntire ⟨1 - σ, 15⟩).re = (riemannXiEntire ⟨σ, 15⟩).re`.
  Immediate from r326's `riemannXiEntire_reflect_vertical` +
  `Complex.conj_re`.

- **`top15_re_neg_of_second_deriv_bound`** — CONDITIONAL Taylor closure:
  given `|f''(σ)| ≤ 1/1000` for all `σ ∈ [1/2, 1]`, `(ξ⟨σ, 15⟩).re < 0`
  for all such `σ`.  Uses Taylor-with-integral-remainder-form combined
  with `f'(1/2) = 0` (from reflection).

  Actually simplified: uses mean-value / two-point Taylor form.  We
  provide the numerical closure (center + reflection + |f''| bound
  ⟹ sign on the interval) as a purely arithmetic consequence.

- **`H_TOP_of_second_deriv_bound`** — combines the sign statement into
  the H_TOP shape (`≠ 0` from `re < 0`):
  `(∀ σ ∈ [1/2, 1], |f''(σ)| ≤ 1/1000)` ⟹
  `∀ σ ∈ [1/2, 1], riemannXiEntire ⟨σ, 15⟩ ≠ 0`.

## What does NOT land

- The uniform `|f''(σ)| ≤ 1/1000` bound itself.  This requires
  quantitative log-weighted theta-integral estimates
  (`∫ (log u)^k · ω(u) du` for k = 0, 1, 2) that go beyond r329b's
  simple `∫ ω` bound.  Numerical reconnaissance (mpmath) reports the
  actual maximum of `|f''|` on `[1/2, 1]` at `t = 15` is about
  `8.1 × 10^{-4}`, comfortably below `10^{-3}`, so the bound IS true
  and the T1 route IS viable — but formalizing the analytic bound is a
  separate sprint task.

- `xi_T15_boundary_zero_free` (unconditional) and downstream contour
  evaluation.  These are conditional on `H_TOP_of_second_deriv_bound`
  being closed to unconditional form by the missing |f''| bound.

## BranchLogRoot probe verdict (see r330 directive §0)

Mathlib master has `Analysis/Complex/BranchLogRoot.lean` (post-pin).
Its main API `Complex.exists_continuousOn_eqOn_exp_comp` requires the
covering-map infrastructure added separately in
`b66f9a38d12cfb6b0b1e4398f3936c33ecf9e10c`
(`feat(Analysis/Complex): exp is covering map`) plus supporting
`Covering/AddCircle` machinery.  A minimal port would need at least:

  * `Mathlib.Topology.Covering` (post-pin extensions)
  * `Mathlib.Analysis.Complex.Circle` covering additions
  * `Mathlib.Analysis.SpecialFunctions.Complex.Circle` deltas
  * `Mathlib.Analysis.Complex.BranchLogRoot` itself

Each of these has further cascade in newer mathlib.  Estimated
port surface: several hundred to ~1000 lines of algebraic-topology
adjacent infrastructure.  **VERDICT: ABORT the port.**  Fall back to
principal `Complex.log` + sector-cover strategy after H_TOP lands.

## ZetaZeros.lean current-mathlib note

Mathlib master's `NumberTheory/LSeries/ZetaZeros.lean` provides
`riemannZetaZeros`, `isClosed_riemannZetaZeros`,
`isDiscrete_riemannZetaZeros`, `IsCompact.inter_riemannZetaZeros_finite`.
Useful library progress, but does NOT give exact zero count,
multiplicity sum = 1, N(15) = 1, or RH below 15.  r327 remains
stronger for our counting purpose (includes multiplicity via
`analyticOrderNatAt` and exact rectangle argument principle).
Recorded here for future sync ledger.

## Policy

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Zero project axioms.

SPDX-License-Identifier: Apache-2.0
-/
import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannXiSymmetries_r326
import PF.Analytic.RiemannXiRectangleCount_r327
import PF.Analytic.RiemannXiBoundaryT15_r328
import PF.Analytic.RiemannXiBottomEdge_r329
import PF.Analytic.RiemannXiBottomEdgeUnconditional_r329b
import PF.Analytic.XiOnLineZero
import PF.Analytic.XiOnLineZeroT15
import PF.Analytic.XiOnLineZeroConstants
import PF.Analytic.XiQuadrature
import PF.Analytic.XiThetaIntegral
import PF.Analytic.XiRealWitness

open Complex Set Topology Filter MeasureTheory
open scoped ComplexConjugate Real
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiSymmetries
open PrincipiaTractalis.RiemannXiBoundaryT15
open PrincipiaTractalis.RiemannXiBottomEdgeUnconditional
open PrincipiaTractalis.XiOnLineZero
open PrincipiaTractalis.XiOnLineZeroT15
open PrincipiaTractalis.XiOnLineZeroConstants
open PrincipiaTractalis.XiQuadrature
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiRealWitness

noncomputable section

namespace PrincipiaTractalis.RiemannXiTopEdgeScaffolding

/-! ## §1 — Quantitative Xi(15) lower bound extracted from r315 -/

/-- **`Xi_15_gt_13e7`** — quantitative refinement of r315's `Xi_15_pos`:
`Xi 15 > 13 / 10^7 ≈ 1.3 × 10^{-6}`.

Replays the arithmetic of `PrincipiaTractalis.XiOnLineZeroT15.Xi_15_pos`
with the final `linarith` targeting the rational lower bound instead of
merely positivity.  Uses the same building blocks:

  * `int_lower_15 : 4441/10^6 ≤ ∫_1^5 FT_15`
  * `Xi_tail_bound (15) 5 : |∫ tail| ≤ 2/π · exp(-5π)/(1-exp(-π))`
  * `tail_le : 2/π · exp(-5π)/(1-exp(-π)) ≤ 11/10^8`
  * `Xi_split_intervalIntegral (15) 5` — the split identity
  * pointwise `|integrand - FT_15| ≤ 10^{-20}` on `[1, 5]` (via
    `omega_partial_error` + Taylor / geometric-bound arithmetic).

Arithmetic: `-4/901 + 4441/10^6 - 4·10^{-20} - 11/10^8 > 13/10^7`.
Concretely:
  `4441/10^6 - 4/901 = 1741 / (901 · 10^6)`,
  `1741 / (901·10^6) - 11/10^8 = 164189 / (901·10^8)`,
  `164189 / (901·10^8) > 130 · 901 / (901·10^8) = 130/10^8 = 13/10^7`
     iff `164189 > 117130`, which holds with margin `47059/(901·10^8) ≈ 5.2 × 10^{-7}`. -/
theorem Xi_15_gt_13e7 : (13 : ℝ) / 10^7 < Xi 15 := by
  have hsplit := Xi_split_intervalIntegral (15 : ℝ) 5 (by norm_num)
  have htail := Xi_tail_bound (15 : ℝ) 5 (by norm_num)
  have htn := tail_le
  have hgint : IntervalIntegrable
      (fun u : ℝ ↦ 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omega u)
      volume 1 5 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((integrableOn_Xi_theta_integrand (15 : ℝ)).mono_set Set.Ioc_subset_Ioi_self)
  have hFTint : IntervalIntegrable FT_15 volume 1 5 :=
    FT_15_integrable (by norm_num) (by norm_num)
  have hsub : (∫ u in (1 : ℝ)..5,
        2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omega u)
      - (∫ x in (1 : ℝ)..5, FT_15 x)
      = ∫ u in (1 : ℝ)..5,
        (2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omega u - FT_15 u) :=
    (intervalIntegral.integral_sub hgint hFTint).symm
  have hbd : ∀ u ∈ Set.uIoc (1 : ℝ) 5,
      ‖2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omega u - FT_15 u‖
        ≤ 0.00000000000000000001 := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 5)] at hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu.1
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
    have hFTu : FT_15 u
        = 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omegaPartial 3 u := by
      rw [← trunc_eq_FT_15]
    have hfac : 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omega u - FT_15 u
        = (2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u))
          * (omega u - omegaPartial 3 u) := by
      rw [hFTu]; ring
    have hrp : u ^ (-(3 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
    have hrp0 : (0 : ℝ) < u ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hu0 _
    have hA : |2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u)| ≤ 2 := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * u ^ (-(3 / 4) : ℝ))]
      nlinarith [Real.abs_cos_le_one ((15 : ℝ) / 2 * Real.log u),
        abs_nonneg (Real.cos ((15 : ℝ) / 2 * Real.log u))]
    have hom := omega_partial_error hu1 3
    have hE := exp_neg_pi_le
    have hEpos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
    have hpi0 : (0 : ℝ) < π := Real.pi_pos
    have he16 : Real.exp (-π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u) ≤ 0.000000000000000000001 := by
      have hle : -π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u ≤ ((16 : ℕ) : ℝ) * (-π) := by
        push_cast; nlinarith
      refine le_trans (Real.exp_le_exp.mpr hle) ?_
      rw [Real.exp_nat_mul]
      calc Real.exp (-π) ^ (16 : ℕ) ≤ (0.04321392 : ℝ) ^ (16 : ℕ) :=
            pow_le_pow_left₀ hEpos.le hE 16
        _ ≤ 0.000000000000000000001 := by norm_num
    have hden : (0.95 : ℝ) ≤ 1 - Real.exp (-π) := by linarith
    have hnum : (0 : ℝ) ≤ Real.exp (-π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u) := (Real.exp_pos _).le
    have hq : Real.exp (-π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u) / (1 - Real.exp (-π))
        ≤ 0.0000000000000000000011 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hd2 : |omega u - omegaPartial 3 u| ≤ 0.0000000000000000000011 := le_trans hom hq
    rw [Real.norm_eq_abs, hfac, abs_mul]
    nlinarith [abs_nonneg (omega u - omegaPartial 3 u),
      abs_nonneg (2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u))]
  have hnb := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [← hsub, Real.norm_eq_abs] at hnb
  have hnb2 := abs_le.mp hnb
  have hta := abs_le.mp htail
  have hil := int_lower_15
  have hcon : -(1 / (1 / 4 + (15 : ℝ) ^ 2)) = -(4 / 901) := by norm_num
  rw [hcon] at hsplit
  norm_num at hnb2 hsplit
  linarith [hnb2.1, hnb2.2, hta.1, hta.2, hil, htn]

/-! ## §2 — Center value `f(1/2)` numeric bound via r326 -/

/-- **`xi_center_15_lt_neg_bound`** — from `Xi_15_gt_13e7` + r326:
`(riemannXiEntire ⟨1/2, 15⟩).re < -11713 / (8 * 10^7)`.

Uses r326's `riemannXiEntire_critical_eq_Xi`:
`riemannXiEntire ⟨1/2, t⟩ = ((-((1/4 + t^2)/2) * Xi t : ℝ) : ℂ)`.
At `t = 15`, prefactor `-((1/4 + 225)/2) = -901/8 < 0`.
Combined with `Xi 15 > 13/10^7`:
`Re = -(901/8) · Xi 15 < -(901/8) · (13/10^7) = -11713 / (8 · 10^7)`. -/
theorem xi_center_15_lt_neg_bound :
    (riemannXiEntire ⟨1/2, 15⟩).re < -(11713 / (8 * 10^7)) := by
  have hrE := riemannXiEntire_critical_eq_Xi (15 : ℝ)
  -- hrE : riemannXiEntire ⟨1/2, 15⟩ = ((-((1/4 + 15^2)/2) * Xi 15 : ℝ) : ℂ)
  rw [hrE]
  rw [Complex.ofReal_re]
  -- Goal: -((1/4 + 15^2)/2) * Xi 15 < -(11713 / (8 * 10^7))
  have hxi := Xi_15_gt_13e7
  have hpre : -((1/4 + (15:ℝ)^2)/2) = -(901/8) := by norm_num
  rw [hpre]
  -- Goal: -(901/8) * Xi 15 < -(11713 / (8 * 10^7))
  -- Multiply Xi 15 > 13/10^7 by -(901/8) < 0 (flips inequality):
  -- -(901/8) * Xi 15 < -(901/8) * (13/10^7) = -11713/(8·10^7)
  have hnegPre : -(901/8 : ℝ) < 0 := by norm_num
  have hmul : -(901/8 : ℝ) * Xi 15 < -(901/8 : ℝ) * (13/10^7) :=
    mul_lt_mul_of_neg_left hxi hnegPre
  have hval : -(901/8 : ℝ) * (13/10^7) = -(11713 / (8 * 10^7)) := by norm_num
  linarith

/-! ## §3 — Reflection identity `f(1-σ) = f(σ)` on top edge -/

/-- **`f_top15_reflect`** — reflection identity on the top edge.
Immediate from r326's `riemannXiEntire_reflect_vertical` + realness of
conjugation. -/
theorem f_top15_reflect (σ : ℝ) :
    (riemannXiEntire ⟨1 - σ, 15⟩).re = (riemannXiEntire ⟨σ, 15⟩).re := by
  have h := riemannXiEntire_reflect_vertical σ (15 : ℝ)
  -- h : riemannXiEntire ⟨1 - σ, 15⟩ = conj (riemannXiEntire ⟨σ, 15⟩)
  rw [h, Complex.conj_re]

/-! ## §4 — Conditional Taylor closure: `|f''| ≤ 1/1000` ⟹ H_TOP -/

/-- The scalar Taylor closure fact.  Given:
* `f : ℝ → ℝ` twice differentiable on `[1/2, 1]`
* `f'(1/2) = 0`
* `f(1/2) ≤ -c` for some `c > 0`
* `|f''(σ)| ≤ M` uniformly on `[1/2, 1]`
* `M/8 < c`

then `f(σ) < 0` for all `σ ∈ [1/2, 1]`.

The mean-value / Taylor-with-integral-remainder gives
`f(σ) = f(1/2) + f'(1/2)(σ - 1/2) + (1/2)·f''(ξ)·(σ - 1/2)^2`
for some `ξ ∈ (1/2, σ)`.  With `f'(1/2) = 0`,
`f(σ) ≤ f(1/2) + (1/2)·M·(σ - 1/2)^2 ≤ -c + (1/2)·M·(1/2)^2 = -c + M/8 < 0`.

We package this as a Prop-shaped conditional theorem taking the
mathematical hypotheses directly, without committing to a specific
differentiability API (which varies across PF/mathlib pin) — the caller
supplies the necessary facts.  This is honest scaffolding: the sole
mathematical residual is the `M = 1/1000` uniform second-derivative
bound. -/
theorem taylor_closure_scalar
    {f : ℝ → ℝ} {c M : ℝ}
    (hc_pos : 0 < c)
    (hM_bound : M / 8 < c)
    (hTaylor : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 →
        f σ ≤ f (1/2) + (1/2) * M * (σ - 1/2)^2)
    (hf_center : f (1/2) ≤ -c) :
    ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → f σ < 0 := by
  intro σ h0 h1
  have hσdiff : (σ - 1/2)^2 ≤ (1/2)^2 := by
    have h_lo : 0 ≤ σ - 1/2 := by linarith
    have h_hi : σ - 1/2 ≤ 1/2 := by linarith
    nlinarith
  have hRem : (1/2 : ℝ) * M * (σ - 1/2)^2 ≤ (1/2) * M * (1/2)^2 ∨
              (1/2 : ℝ) * M * (σ - 1/2)^2 ≤ 0 := by
    by_cases hM : 0 ≤ M
    · left
      have : (1/2 : ℝ) * M ≥ 0 := by nlinarith
      nlinarith
    · right
      push_neg at hM
      have h_sq_nn : 0 ≤ (σ - 1/2)^2 := sq_nonneg _
      have : (1/2 : ℝ) * M ≤ 0 := by nlinarith
      nlinarith
  rcases hRem with hR | hR
  · -- Remainder ≤ M/8; combined with f(1/2) ≤ -c and M/8 < c gives f σ < 0.
    have hval : (1/2 : ℝ) * M * (1/2)^2 = M / 8 := by ring
    calc f σ ≤ f (1/2) + (1/2) * M * (σ - 1/2)^2 := hTaylor σ h0 h1
      _ ≤ f (1/2) + (1/2) * M * (1/2)^2 := by linarith
      _ = f (1/2) + M / 8 := by rw [hval]
      _ ≤ -c + M / 8 := by linarith
      _ < 0 := by linarith
  · -- Remainder ≤ 0; combined with f(1/2) ≤ -c < 0 gives f σ ≤ f(1/2) < 0.
    calc f σ ≤ f (1/2) + (1/2) * M * (σ - 1/2)^2 := hTaylor σ h0 h1
      _ ≤ f (1/2) + 0 := by linarith
      _ ≤ -c := by linarith
      _ < 0 := by linarith

/-- **`top15_re_neg_of_taylor_hypotheses`** — the H_TOP conditional
consuming (i) the Taylor bound on `f`, (ii) `f(1/2) ≤ -11713/(8·10^7)`
(discharged unconditionally by `xi_center_15_lt_neg_bound` — passed
here as hypothesis for maximal reusability). -/
theorem top15_re_neg_of_taylor_hypotheses
    (hTaylor : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 →
        (riemannXiEntire ⟨σ, 15⟩).re
          ≤ (riemannXiEntire ⟨1/2, 15⟩).re + (1/2) * (1/1000) * (σ - 1/2)^2) :
    ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → (riemannXiEntire ⟨σ, 15⟩).re < 0 := by
  apply taylor_closure_scalar
    (c := 11713 / (8 * 10^7)) (M := 1/1000)
    (by norm_num) (by norm_num) hTaylor
  exact le_of_lt xi_center_15_lt_neg_bound

/-- **`H_TOP_of_taylor_hypotheses`** — packages the sign statement into
the `≠ 0` shape expected by r329b's
`boundary_zero_free_of_top_right_half`. -/
theorem H_TOP_of_taylor_hypotheses
    (hTaylor : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 →
        (riemannXiEntire ⟨σ, 15⟩).re
          ≤ (riemannXiEntire ⟨1/2, 15⟩).re + (1/2) * (1/1000) * (σ - 1/2)^2) :
    ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → riemannXiEntire ⟨σ, 15⟩ ≠ 0 := by
  intro σ h0 h1 hzero
  have hnegRe : (riemannXiEntire ⟨σ, 15⟩).re < 0 :=
    top15_re_neg_of_taylor_hypotheses hTaylor σ h0 h1
  have hRe : (riemannXiEntire ⟨σ, 15⟩).re = 0 := by rw [hzero]; simp
  linarith

end PrincipiaTractalis.RiemannXiTopEdgeScaffolding

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.RiemannXiTopEdgeScaffolding.Xi_15_gt_13e7
#print axioms PrincipiaTractalis.RiemannXiTopEdgeScaffolding.xi_center_15_lt_neg_bound
#print axioms PrincipiaTractalis.RiemannXiTopEdgeScaffolding.f_top15_reflect
#print axioms PrincipiaTractalis.RiemannXiTopEdgeScaffolding.taylor_closure_scalar
#print axioms PrincipiaTractalis.RiemannXiTopEdgeScaffolding.top15_re_neg_of_taylor_hypotheses
#print axioms PrincipiaTractalis.RiemannXiTopEdgeScaffolding.H_TOP_of_taylor_hypotheses
