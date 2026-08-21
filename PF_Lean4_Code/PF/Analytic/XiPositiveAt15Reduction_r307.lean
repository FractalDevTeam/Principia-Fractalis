/-
# r307: Xi_Positive_At_15 RESIDUAL REDUCTION to `0 < P₁₅.re` + chain-closer
#      (dependency-reduction step ending the symbolic phase and exposing the
#       exact numerical target)

★ 2026-08-21 r307 — collapses the r304-r306 symbolic peeling chain
into a single kernel-clean equivalence:

  `Xi_Positive_At_15 ↔ 0 < P₁₅.re`

where

  `P₁₅ := riemannZeta ⟨1/2, 15⟩
            · Complex.exp (((-(15/2) · Real.log Real.pi : ℝ) : ℂ) · Complex.I)
            · Complex.Gamma ⟨1/4, 15/2⟩`

and lands the **chain-closer** that terminates the discharge once any
positive lower bound on `P₁₅.re` is proved.

## Framework-first dependency-reduction ledger

**Before r307**: `Xi_Positive_At_15` was carried through the r304-r306
chain as a target requiring the entire symbolic factorization to be
re-invoked at each downstream landing.

**After r307**: `Xi_Positive_At_15` reduces to a strict positivity of
the real part of one mathlib-native complex product, plus a kernel-
clean closer that discharges the residual from any positive lower
bound. The remaining unresolved dependency is exactly a certified
numerical enclosure of `P₁₅.re`.

**Remaining smallest missing certified theorems** (r308+):

1. Certified enclosure of `Complex.Gamma ⟨1/4, 15/2⟩` — mathlib has
   `Complex.Gamma` as a noncomputable definition but no certified
   evaluators at general complex arguments. Requires formalization of
   a Stirling-series or Lanczos-approximation with rigorous error
   bounds; magnitude on order `10⁻⁵` at this argument, so enclosure
   precision must exceed that.

2. Certified enclosure of `riemannZeta ⟨1/2, 15⟩` — mathlib has
   `riemannZeta` as noncomputable but no certified evaluators. Requires
   Euler-Maclaurin, Riemann-Siegel, or Dirichlet-eta-based expansion
   with rigorous error bounds on the critical line.

3. Certified evaluation of `Real.cos`/`Real.sin` at
   `(15/2) · Real.log Real.pi` for the phase factor. Achievable via
   mathlib's Taylor bounds and mod-2π reduction on
   `(15/2) · Real.log Real.pi ≈ 8.586`.

Each is a multi-landing subproject. The direct-attack estimate:
`P₁₅.re ≈ Xi 15 / π^(-1/4) ≈ 1.5e-5`, so total enclosure precision
must be substantially below `10⁻⁵`.

## What r307 delivers

- `P15 : ℂ` — the specific complex product exposed by the r304-r306
  peeling chain.

- `xi_15_eq_pi_neg_quarter_mul_re_P15 : Xi 15 = Real.pi^(-1/4) * P15.re`
  — the r304-r306 chain state as a kernel-clean equation.

- `Xi_Positive_At_15_iff_re_P15_pos : Xi_Positive_At_15 ↔ 0 < P15.re` —
  the residual reformulated to a mathlib-native strict positivity.

- `Xi_Positive_At_15_from_P15_re_lower_bound : ∀ {a : ℝ}, 0 < a →
  a ≤ P15.re → Xi_Positive_At_15` — the CHAIN-CLOSER. Any certified
  positive lower bound on `P15.re` discharges the residual.

## Framework-first scope

Not a discharge. Strictly-necessary dependency-reduction infrastructure
that collapses the symbolic chain into one equivalence + one closer,
exposing the exact numerical target.

r308 begins certified numerical enclosure of the smallest achievable
component (likely the phase factor `Real.cos`/`Real.sin` at
`(15/2) · Real.log Real.pi` via mathlib's Taylor bounds).

Book anchors: Ch 20 § 20.4 (RH via Fractal Resonance), Ch 34A § 34A.5.
Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6.
-/

import PF.Analytic.PiCpowPolarAt15_r306

namespace PrincipiaTractalis.XiPositiveAt15Reduction

open Complex
open PrincipiaTractalis.PiCpowPolarAt15
open PrincipiaTractalis.GammaRAtCritical15
open PrincipiaTractalis.XiExplicitFactorization
open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning

/-! ## §1 The specific complex product `P₁₅`. -/

/-- **`P15`** — the specific complex product exposed by the r304-r306
symbolic peeling chain:
  `P₁₅ := ζ(1/2+15i) · exp(-i·(15/2)·log π) · Γ(1/4+15i/2)`.

Downstream numerical work targets `0 < P15.re`. -/
noncomputable def P15 : ℂ :=
  riemannZeta ⟨(1 : ℝ)/2, (15 : ℝ)⟩
    * Complex.exp (((-((15 : ℝ)/2) * Real.log Real.pi : ℝ) : ℂ) * Complex.I)
    * Complex.Gamma ⟨(1 : ℝ)/4, (15 : ℝ)/2⟩

/-! ## §2 Chain state equation: `Xi 15 = π^(-1/4) · P15.re`. -/

/-- **`xi_15_eq_pi_neg_quarter_mul_re_P15`** — the r304-r306 chain state
as a kernel-clean equation:

  `Xi 15 = Real.pi^(-1/4) * P15.re`.

Proof: `Xi_eq_re_zeta_mul_Gammaℝ` (r304) at t = 15 →
`Gammaℝ_at_critical_15_polar_form` (r306) → rearrange the complex
product via `ring` to put the real scalar `((π^(-1/4) : ℝ) : ℂ)` at
the outside → extract via `Complex.mul_re` and
`Complex.ofReal_re/ofReal_im`. -/
theorem xi_15_eq_pi_neg_quarter_mul_re_P15 :
    Xi 15 = Real.pi^(-(1 : ℝ)/4) * P15.re := by
  rw [Xi_eq_re_zeta_mul_Gammaℝ 15, Gammaℝ_at_critical_15_polar_form]
  have h_rearrange :
      riemannZeta ⟨(1 : ℝ)/2, (15 : ℝ)⟩
        * (((Real.pi^(-(1 : ℝ)/4) : ℝ) : ℂ)
            * Complex.exp (((-((15 : ℝ)/2) * Real.log Real.pi : ℝ) : ℂ) * Complex.I)
            * Complex.Gamma ⟨(1 : ℝ)/4, (15 : ℝ)/2⟩)
      = ((Real.pi^(-(1 : ℝ)/4) : ℝ) : ℂ) * P15 := by
    unfold P15
    ring
  rw [h_rearrange]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-! ## §3 The residual reformulated: `Xi_Positive_At_15 ↔ 0 < P15.re`. -/

/-- **`Xi_Positive_At_15_iff_re_P15_pos`** — the aggregate's Xi witness
residual reformulated as a strict positivity of `P15.re`:

  `Xi_Positive_At_15 ↔ 0 < P15.re`.

Since `Real.pi^(-1/4) > 0` (r306 `pi_cpow_at_neg_15halves_abs_pos`)
and `Xi 15 = Real.pi^(-1/4) * P15.re` (this file, §2), the positivity
of `Xi 15` is equivalent to the positivity of `P15.re`. -/
theorem Xi_Positive_At_15_iff_re_P15_pos :
    Xi_Positive_At_15 ↔ 0 < P15.re := by
  unfold Xi_Positive_At_15
  rw [xi_15_eq_pi_neg_quarter_mul_re_P15]
  constructor
  · intro h
    exact (mul_pos_iff_of_pos_left pi_cpow_at_neg_15halves_abs_pos).mp h
  · intro h
    exact mul_pos pi_cpow_at_neg_15halves_abs_pos h

/-! ## §4 THE CHAIN-CLOSER — from any positive lower bound to discharge. -/

/-- **★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★ (r307) Xi_Positive_At_15 CHAIN-CLOSER ★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★** —
any positive lower bound on `P15.re` discharges the aggregate's Xi
witness residual:

  `∀ {a : ℝ}, 0 < a → a ≤ P15.re → Xi_Positive_At_15`.

r308+ certified numerical enclosure work terminates the discharge by
producing an `a > 0` with `a ≤ P15.re`. This closer converts that
enclosure directly to `Xi_Positive_At_15`. -/
theorem Xi_Positive_At_15_from_P15_re_lower_bound
    {a : ℝ} (ha : 0 < a) (h : a ≤ P15.re) :
    Xi_Positive_At_15 :=
  Xi_Positive_At_15_iff_re_P15_pos.mpr (lt_of_lt_of_le ha h)

/-! ## §5 Axiom checks. -/

#print axioms
  PrincipiaTractalis.XiPositiveAt15Reduction.xi_15_eq_pi_neg_quarter_mul_re_P15
#print axioms
  PrincipiaTractalis.XiPositiveAt15Reduction.Xi_Positive_At_15_iff_re_P15_pos
#print axioms
  PrincipiaTractalis.XiPositiveAt15Reduction.Xi_Positive_At_15_from_P15_re_lower_bound

end PrincipiaTractalis.XiPositiveAt15Reduction
