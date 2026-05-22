/-
# `T3NormBound` — Refined Factorisation of the Mayer Contractivity Bound

This file refines the single norm-bound Prop `T3NormBound`
(`PF/Analytic/T3LinearStructureDischarge.lean:250`) — Mayer 1991's
`‖T_3 f‖ ≤ ‖f‖` on `L²([0,1], dx/x)` — into a SMALLER, mathematically
sharper named sub-Prop plus a PROVEN REDUCTION between them. The
remaining analytic obligation shrinks from a norm inequality to the
core L²-squared integral inequality (the "Mayer 1991 estimate" proper),
factored along the natural decomposition

  `‖T_3 f‖²  =  re ⟪T_3 f, T_3 f⟫_(Lp ℂ 2 μ)
            =  ∫_(0,1) |T_3 f|² ∂μ_log
           ≤  ∫_(0,1) |f|² ∂μ_log
            =  re ⟪f, f⟫_(Lp ℂ 2 μ)
            =  ‖f‖²`

with the inequality in the middle being the Cauchy–Schwarz +
per-branch-CoV + partition step that Mayer 1991 (BAMS) discharges via
explicit kernel manipulations.

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`T3NormSquaredBound`** — refined sub-Prop bundling the L²-squared
     integral inequality on the canonical `LogWeightedL2` integrand
     (the irreducible analytic content of Mayer 1991 §2).

  2. **`T3NormBound_proved_from_squared`** — PROVED reduction:
     `T3NormSquaredBound → T3NormBound`. The full chain
       (a) Lp norm-squared ↔ self-inner-product real-part
           (mathlib `inner_self_eq_norm_sq` instantiated at the
            registered `InnerProductSpace ℂ LogWeightedL2`),
       (b) Lp inner-product `⟪f,f⟫_ℂ` ↔ existing project integral
           form via `MeasureTheory.L2.inner_def` +
           `MeasureTheory.integral_complex_inner_eq_lintegral`-style
           ℂ-inner-as-conj-mul,
       (c) AE-equality of the `T3.apply` representative with the
           explicit pointwise formula via `T3_toFunℝ_Ioo_unconditional`,
       (d) reduction from `A ≤ B` (squared, nonneg) to `√A ≤ √B`
           (`Real.sqrt_le_sqrt` + `Real.sqrt_sq` for nonneg norms).

  3. **`T3LinearStructure_proved_from_squared`** — composes (2) with
     `T3LinearStructure_proved_from_norm_bound` to get the contracting
     half `T3LinearStructure` directly from the squared sub-Prop.

  4. **`T3SymCLMSymmetricWitness_proved_from_squared`** —
     end-to-end discharge: given `T3NormSquaredBound` +
     `T3AdjointLinearStructureFactored`, produces the full
     `T3SymCLMSymmetricWitness`.

## Honest framing

After this file, the contracting-half `T3LinearStructure` gap reduces
from the norm Prop `T3NormBound` (a `‖·‖ ≤ ‖·‖` inequality on
abstract `Lp`-elements) to the SQUARED integral Prop
`T3NormSquaredBound` (a `∫ |·|² ≤ ∫ |·|²` inequality on the canonical
`toFunℝ` representatives). The reduction is a clean Hilbert-space
identity chain — the remaining open content is exactly the per-branch
Cauchy–Schwarz + partition estimate of Mayer 1991 §2, factored at its
most natural mathematical statement (no `Lp`-norm bookkeeping; pure
real-valued integral inequality).

## Build state

ZERO project axioms. ZERO `sorry`. Builds against the same mathlib
snapshot as `PF.Analytic.T3LinearStructureDischarge`.
-/

import PF.Analytic.T3LinearStructureDischarge

namespace PrincipiaTractalis

open scoped InnerProductSpace
open MeasureTheory

/-! ## 1. Refined L²-squared sub-Prop -/

/-- **`T3NormSquaredBound`** — the L²-squared integral inequality
    underlying Mayer 1991 contractivity for the contracting transfer
    operator `T3.apply`.

    Provenance (when supplied): Mayer 1991 (BAMS) §2 — pointwise
    Cauchy–Schwarz `|∑_k ω_k · w_k(x) · f(y_k(x))|² ≤ 3 · ∑_k
    |w_k(x)|² · |f(y_k(x))|²` (using `phaseFactorBase3_norm` to drop
    phase moduli) + per-branch change-of-variables
    `branch_logWeightedMeasure_norm_sq_eq_real`
    (`PF/TransferOperator.lean:1617`) + partition of `(0,1) = ⋃_k I_k`
    + the `(1/3)²` prefactor in `transferOperatorAction_func`.

    Stated on the EXPLICIT pointwise formula
    `transferOperatorAction_func 3 phaseFactorBase3 f` — this is the
    representative that AE-coincides with `(T3.apply f).toFunℝ` via
    `T3_toFunℝ_Ioo_unconditional` (`PF/TransferOperator.lean:1800`).
    Stated this way the irreducible content is exactly the per-branch
    L² estimate; the bridge to the `Lp`-norm is discharged below in
    `T3NormBound_proved_from_squared`. -/
structure T3NormSquaredBound : Prop where
  /-- `∫_(0,1) |(T_3 f)(x)|² dμ_log(x) ≤ ∫_(0,1) |f(x)|² dμ_log(x)`. -/
  sq_le : ∀ (f : LogWeightedL2),
    (∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (transferOperatorAction_func 3 phaseFactorBase3 f x)
        ∂logWeightedMeasure)
    ≤ (∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (f.toFunℝ x)
        ∂logWeightedMeasure)

/-! ## 2. Bridge lemmas: Lp norm-squared ↔ integral of normSq -/

/-- **`LogWeightedL2`'s `Lp` norm-squared equals `re ⟪f, f⟫_ℂ_Lp`.**
    Direct from mathlib's `inner_self_eq_norm_sq` for any inner-product
    space, instantiated at the registered `InnerProductSpace ℂ
    LogWeightedL2` instance. -/
lemma logWeightedL2_lp_norm_sq_eq_re_inner (f : LogWeightedL2) :
    ‖f‖ ^ 2 = RCLike.re (Inner.inner (𝕜 := ℂ) f f) :=
  (@inner_self_eq_norm_sq ℂ LogWeightedL2 _ _ _ f).symm

/-- **Project-side `Lp` norm-squared identity**: `‖f‖² = ∫ |f.toFunℝ|² ∂μ_log`.

    The chain:
      `‖f‖²  =  re ⟪f, f⟫_ℂ_Lp`                          (inner_self_eq_norm_sq)
            `=  re (∫ ⟪f.val a, f.val a⟫_ℂ ∂μ)`         (MeasureTheory.L2.inner_def)
            `=  re (∫ conj(f.toFunℝ x) · f.toFunℝ x ∂μ)`  (ℂ-inner ≡ conj-mul +
                                                          definition of `toFunℝ`)
            `=  re ((∫ ↑normSq(f.toFunℝ x) ∂μ : ℂ))`     (Complex.normSq_eq_conj_mul_self)
            `=  ∫ normSq(f.toFunℝ x) ∂μ`                  (integral_ofReal + Complex.ofReal_re).
    With `μ = μ_log.restrict (Ioo 0 1)`, the whole-space integral against
    the restricted measure equals the setIntegral over `Ioo 0 1`. -/
lemma logWeightedL2_lp_norm_sq_eq_integral_normSq (f : LogWeightedL2) :
    ‖f‖ ^ 2 = ∫ x in Set.Ioo (0:ℝ) 1,
                Complex.normSq (f.toFunℝ x) ∂logWeightedMeasure := by
  -- Step 1: ‖f‖² = re ⟪f, f⟫_ℂ_Lp
  rw [logWeightedL2_lp_norm_sq_eq_re_inner f]
  -- Step 2: unfold Lp inner via MeasureTheory.L2.inner_def. Mathlib produces the
  -- form `∫ a in Set.Ioo 0 1, ⟪↑↑f a, ↑↑f a⟫_ℂ ∂μ_log` after elaborator simplification.
  rw [MeasureTheory.L2.inner_def (𝕜 := ℂ) f f]
  -- Step 3: integrand rewrite. `↑↑f a` is definitionally `f.toFunℝ a`
  -- (via `LogWeightedL2.toFunℝ`, `LogWeightedL2.toFun`, and `Lp` coercion).
  -- `⟪z, z⟫_ℂ = conj z · z = ↑normSq z` by RCLike.inner_apply +
  -- Complex.normSq_eq_conj_mul_self.
  have h_integrand : ∀ x : ℝ,
      (Inner.inner (𝕜 := ℂ) (f.toFunℝ x) (f.toFunℝ x) : ℂ)
        = ((Complex.normSq (f.toFunℝ x) : ℝ) : ℂ) := by
    intro x
    rw [RCLike.inner_apply, Complex.normSq_eq_conj_mul_self]; ring
  -- Use the fact that `↑↑f a = f.toFunℝ a` definitionally to rewrite the integrand
  show RCLike.re (∫ a in Set.Ioo (0:ℝ) 1,
        (Inner.inner (𝕜 := ℂ) (f.toFunℝ a) (f.toFunℝ a) : ℂ)
        ∂logWeightedMeasure)
      = ∫ x in Set.Ioo (0:ℝ) 1, Complex.normSq (f.toFunℝ x) ∂logWeightedMeasure
  rw [show (fun a => (Inner.inner (𝕜 := ℂ) (f.toFunℝ a) (f.toFunℝ a) : ℂ))
        = (fun x => ((Complex.normSq (f.toFunℝ x) : ℝ) : ℂ))
      from by funext x; exact h_integrand x]
  -- Now: re (∫ ↑(normSq …)) = ∫ normSq …
  -- Use `integral_ofReal : ∫ x, (F x : 𝕜) ∂μ = ↑(∫ x, F x ∂μ)` to lift `↑` out of `∫`.
  have h_lift : (∫ x in Set.Ioo (0:ℝ) 1,
        ((Complex.normSq (f.toFunℝ x) : ℝ) : ℂ) ∂logWeightedMeasure)
      = ((∫ x in Set.Ioo (0:ℝ) 1, Complex.normSq (f.toFunℝ x)
            ∂logWeightedMeasure : ℝ) : ℂ) := integral_ofReal
  rw [h_lift]
  exact Complex.ofReal_re _

/-- **AE-equality lifts to equality of `Complex.normSq` integrands**. -/
lemma logWeightedL2_normSq_integral_eq_of_ae (f : LogWeightedL2)
    (h_ae : (T3.apply f).toFunℝ
              =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
              transferOperatorAction_func 3 phaseFactorBase3 f) :
    (∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq ((T3.apply f).toFunℝ x) ∂logWeightedMeasure)
    = (∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (transferOperatorAction_func 3 phaseFactorBase3 f x)
        ∂logWeightedMeasure) := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h_ae] with x hx
  rw [hx]

/-- **`(T3.apply f)`'s `Lp` squared norm equals the integral of `normSq` of the
    pointwise-formula representative**. Composes the previous bridge with the
    AE-equality `T3_toFunℝ_Ioo_unconditional`. -/
lemma T3_apply_lp_norm_sq_eq_integral_pointwise (f : LogWeightedL2) :
    ‖T3.apply f‖ ^ 2 =
    ∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (transferOperatorAction_func 3 phaseFactorBase3 f x)
        ∂logWeightedMeasure := by
  rw [logWeightedL2_lp_norm_sq_eq_integral_normSq (T3.apply f)]
  exact logWeightedL2_normSq_integral_eq_of_ae f (T3_toFunℝ_Ioo_unconditional f)

/-! ## 3. PROVED reduction `T3NormSquaredBound → T3NormBound` -/

/-- **★★ Bridge: `T3NormSquaredBound → T3NormBound` ★★**

    Given the L²-squared integral inequality, produces the `Lp`-norm
    inequality via the standard Hilbert-space identity chain. -/
theorem T3NormBound_proved_from_squared
    (hSq : T3NormSquaredBound) : T3NormBound := by
  refine ⟨fun f => ?_⟩
  -- It suffices to show ‖T3.apply f‖² ≤ ‖f‖², then take √ of both sides.
  have h_nn_lhs : (0 : ℝ) ≤ ‖T3.apply f‖ := norm_nonneg _
  have h_nn_rhs : (0 : ℝ) ≤ ‖f‖ := norm_nonneg _
  -- Squared inequality at the Lp level
  have h_sq_lp : ‖T3.apply f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [T3_apply_lp_norm_sq_eq_integral_pointwise f,
        logWeightedL2_lp_norm_sq_eq_integral_normSq f]
    exact hSq.sq_le f
  -- Take square root: x ≤ y when x² ≤ y² and both nonneg
  have h_sqrt : ‖T3.apply f‖ ≤ ‖f‖ := by
    have h1 : Real.sqrt (‖T3.apply f‖ ^ 2) ≤ Real.sqrt (‖f‖ ^ 2) :=
      Real.sqrt_le_sqrt h_sq_lp
    rwa [Real.sqrt_sq h_nn_lhs, Real.sqrt_sq h_nn_rhs] at h1
  exact h_sqrt

/-! ## 4. End-to-end discharge wrappers -/

/-- **★★ `T3LinearStructure` from `T3NormSquaredBound` + the proven
    additivity/homogeneity ★★**

    Composes `T3NormBound_proved_from_squared` with
    `T3LinearStructure_proved_from_norm_bound`
    (`PF/Analytic/T3LinearStructureDischarge.lean:270`). After this
    theorem, the contracting-half `T3LinearStructure` reduces to
    the SQUARED integral Prop `T3NormSquaredBound`. -/
theorem T3LinearStructure_proved_from_squared
    (hSq : T3NormSquaredBound) : T3LinearStructure :=
  T3LinearStructure_proved_from_norm_bound (T3NormBound_proved_from_squared hSq)

/-- **★★★ `T3SymCLMSymmetricWitness` from `T3NormSquaredBound` +
    `T3AdjointLinearStructureFactored` ★★★**

    End-to-end refinement chain:

      `T3NormSquaredBound + T3AdjointLinearStructureFactored`
         → `T3LinearStructure + T3AdjointLinearStructure`        (this file + Discharge)
         → `T3SymLinearStructure`                                 (Sym half-sum)
         → `T3SymCLMSymmetricWitness`                             (logWeightedL2InnerBridge). -/
theorem T3SymCLMSymmetricWitness_proved_from_squared
    (hSq : T3NormSquaredBound)
    (hFac : T3AdjointLinearStructureFactored) :
    T3SymCLMSymmetricWitness :=
  T3SymCLMSymmetricWitness_proved_from_refined
    (T3NormBound_proved_from_squared hSq) hFac

/-! ## 5. Axiom-freeness verification -/

#print axioms T3NormSquaredBound
#print axioms logWeightedL2_lp_norm_sq_eq_re_inner
#print axioms logWeightedL2_lp_norm_sq_eq_integral_normSq
#print axioms logWeightedL2_normSq_integral_eq_of_ae
#print axioms T3_apply_lp_norm_sq_eq_integral_pointwise
#print axioms T3NormBound_proved_from_squared
#print axioms T3LinearStructure_proved_from_squared
#print axioms T3SymCLMSymmetricWitness_proved_from_squared

end PrincipiaTractalis
