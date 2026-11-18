import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# NS Route A, item 3 — Young's convolution inequality, L¹ ⋆ L¹ → L¹

For real-valued `f g : G → ℝ` on a measurable additive group `G` with a
right-translation-invariant σ-finite measure `μ`, the extended-norm
`L¹`-bound on the convolution:

    `∫⁻ x, ‖(f ⋆[lsmul ℝ ℝ, μ] g) x‖ₑ ∂μ ≤ (∫⁻ y, ‖f y‖ₑ ∂μ) · (∫⁻ z, ‖g z‖ₑ ∂μ)`

on the three-axiom bar `[propext, Classical.choice, Quot.sound]`. Not
in mathlib — `Mathlib.Analysis.Convolution` lists `Lp`-convolution bounds
as a TODO (line 82).

## Proof outline (five steps)

1. Pointwise norm bound via `enorm_integral_le_lintegral_enorm`:
   `‖(f ⋆ g) x‖ₑ ≤ ∫⁻ t, ‖f t * g (x - t)‖ₑ ∂μ`, with `enorm_mul` factoring
   the integrand to `‖f t‖ₑ * ‖g (x - t)‖ₑ`.
2. Fubini swap on `μ.prod μ` via `lintegral_lintegral_swap`.
3. Pull the `‖f t‖ₑ` constant out of the inner `x`-integral
   (`lintegral_const_mul'` using `enorm_ne_top` for real scalars).
4. Translation invariance: `∫⁻ x, ‖g (x - t)‖ₑ ∂μ = ∫⁻ x, ‖g x‖ₑ ∂μ` via
   `lintegral_sub_right_eq_self` (needs `IsAddRightInvariant μ`).
5. Final factorisation via `lintegral_mul_const''`.

This is the L¹⋆L¹ corner of NS Route A item 3 (`L¹⋆L² → L²` is the
required target for the NS lane; the L¹⋆L¹ brick is the shared skeleton
and the natural first step).
-/

namespace PrincipiaTractalis.NavierStokes.RouteA_Young_L1L1_2026_11_18

open MeasureTheory MeasureTheory.Measure Convolution

/-- **Young's convolution inequality, L¹⋆L¹ case, at the `enorm` level.** -/
theorem lintegral_enorm_convolution_le_mul
    {G : Type*} [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    {μ : Measure G} [SFinite μ] [IsAddRightInvariant μ]
    (f g : G → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, ‖(convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) μ) x‖ₑ ∂μ ≤
      (∫⁻ y, ‖f y‖ₑ ∂μ) * (∫⁻ z, ‖g z‖ₑ ∂μ) := by
  -- AEStronglyMeasurable on the product (from mathlib's convolution_integrand).
  have hprodASM : AEStronglyMeasurable
      (fun p : G × G => f p.2 * g (p.1 - p.2)) (μ.prod μ) := by
    have h := AEStronglyMeasurable.convolution_integrand
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hf hg
    simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h
  -- Lift to AEMeasurable for the ENNReal-valued factored integrand.
  have hprodAM : AEMeasurable
      (fun p : G × G => ‖f p.2‖ₑ * ‖g (p.1 - p.2)‖ₑ) (μ.prod μ) := by
    have h1 : AEMeasurable (fun p : G × G => ‖f p.2 * g (p.1 - p.2)‖ₑ) (μ.prod μ) :=
      hprodASM.enorm
    refine h1.congr ?_
    filter_upwards with p
    exact enorm_mul _ _
  calc ∫⁻ x, ‖(convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) μ) x‖ₑ ∂μ
      ≤ ∫⁻ x, ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ ∂μ := by
        refine lintegral_mono fun x => ?_
        unfold convolution
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
        refine (enorm_integral_le_lintegral_enorm _).trans ?_
        refine lintegral_mono fun t => ?_
        rw [enorm_mul]
    _ = ∫⁻ t, ∫⁻ x, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ ∂μ :=
        lintegral_lintegral_swap hprodAM
    _ = ∫⁻ t, ‖f t‖ₑ * ∫⁻ x, ‖g (x - t)‖ₑ ∂μ ∂μ := by
        refine lintegral_congr fun t => ?_
        exact lintegral_const_mul' _ _ (enorm_ne_top)
    _ = ∫⁻ t, ‖f t‖ₑ * ∫⁻ x, ‖g x‖ₑ ∂μ ∂μ := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) t]
    _ = (∫⁻ y, ‖f y‖ₑ ∂μ) * (∫⁻ z, ‖g z‖ₑ ∂μ) :=
        lintegral_mul_const'' _ hf.enorm

#print axioms lintegral_enorm_convolution_le_mul

end PrincipiaTractalis.NavierStokes.RouteA_Young_L1L1_2026_11_18
