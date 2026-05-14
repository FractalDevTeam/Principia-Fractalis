/-
# Hilbert-Schmidt Operator Construction

Given a kernel `V : K × K → ℂ` with `V ∈ L²(K × K, μ ⊗ μ)`, this file
constructs the **integral kernel operator** `T_V : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`
acting as

  (T_V f)(x) = ∫ V(x, y) · f(y) dμ(y)

and proves the **Hilbert-Schmidt bound**

  ‖T_V‖_{op} ≤ ‖V‖_{L²(K × K)}.

This is the missing piece of L2: with this operator construction in place,
`PF.IntegralKernel.SelfAdjoint`'s `isSelfAdjoint_of_kernel_conjSymm` lift
applies directly to `V_P` (and `V_NP` once R_φ is added), yielding
`IsSelfAdjoint H_P` as a theorem.

**Foundation layer in this file** (the integrability prerequisites for
the action's well-definedness):
* `integrable_kernel_mul` — `V · f.comp_snd ∈ L¹(μ ⊗ μ)` via Hölder
  (HolderConjugate 2 2).
* `integrable_kernel_section` — for a.e. `x`, the section
  `y ↦ V(x, y) · f(y)` is in `L¹(μ)`.

This makes `kernelAction V f x = ∫ V(x, y) · f(y) dμ(y)` well-defined
almost-everywhere, the prerequisite for promoting it to an L²-function.
The full Hilbert-Schmidt bound and CLM construction sit on top.

Reference: Reed-Simon §VI.6 (Hilbert-Schmidt operators), Mathlib's
`MemLp.mul'` and `Integrable.prod_right_ae` for the API.

Stage L2 — operator construction layer (Hilbert-Schmidt scaffolding).
-/

import PF.IntegralKernel.Basic
import PF.IntegralKernel.FractalKernel
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod

namespace PrincipiaTractalis.IntegralKernel

open MeasureTheory

variable {K : Type*} [MeasurableSpace K] {μ : Measure K}

/-! ## Integrability of the integrand `V(z) · f(z.2)` -/

/-- **Hölder for V · f.comp_snd**: if `V ∈ L²(K × K, μ ⊗ μ)` and
    `f ∈ L²(K, μ)` (with `μ` finite, so the snd-projection of `f`
    lifts to `L²(μ ⊗ μ)`), then the integrand `z ↦ V(z) · f(z.2)`
    is in `L¹(μ ⊗ μ)`. Holder triple: `1/2 + 1/2 = 1`. -/
theorem integrable_kernel_mul [SFinite μ] [IsFiniteMeasure μ]
    {V : K × K → ℂ} (hV : MemLp V 2 (μ.prod μ))
    {f : K → ℂ} (hf : MemLp f 2 μ) :
    Integrable (fun z : K × K => V z * f z.2) (μ.prod μ) := by
  rw [← memLp_one_iff_integrable]
  -- Use Hölder: 1/2 + 1/2 = 1. MemLp.mul' returns `φ x * f x` where
  -- `hf` (first arg) becomes f and `hφ` (second arg) becomes φ.
  -- So to get `V z * f z.2`, we call as `(hf.comp_snd μ).mul' hV`:
  -- the snd-projected f is the "f" arg, V is the "φ" arg.
  have h : MemLp (fun z => V z * f z.2) 1 (μ.prod μ) :=
    (hf.comp_snd μ).mul' hV
      (hpqr := inferInstanceAs (ENNReal.HolderConjugate 2 2))
  exact h

/-- For a.e. `x : K`, the section `y ↦ V(x, y) · f(y)` is integrable.
    This is `Integrable.prod_right_ae` applied to `integrable_kernel_mul`.

    With this in place, `kernelAction V (f : K → ℂ) μ x = ∫ V(x, y) · f(y) dμ(y)`
    is well-defined for μ-a.e. `x`. -/
theorem integrable_kernel_section [SFinite μ] [IsFiniteMeasure μ]
    {V : K × K → ℂ} (hV : MemLp V 2 (μ.prod μ))
    {f : K → ℂ} (hf : MemLp f 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => V (x, y) * f y) μ := by
  have h_total : Integrable (fun z : K × K => V z * f z.2) (μ.prod μ) :=
    integrable_kernel_mul hV hf
  -- For a.e. x, the section is integrable; the section equals our integrand
  filter_upwards [h_total.prod_right_ae] with x hx
  exact hx

/-! ## The action `kernelAction V f` is AEStronglyMeasurable

This is the second prerequisite for promoting the action to a member of
`Lp ℂ 2 μ`. It follows from Fubini-Tonelli (mathlib provides this for
integrable joint integrands).
-/

/-- The kernel action `kernelAction V f` is AEStronglyMeasurable for the
    measure `μ`, given that `V ∈ L²` and `f ∈ L²` on a finite measure. -/
theorem aestronglyMeasurable_kernelAction [SFinite μ] [IsFiniteMeasure μ]
    {V : K × K → ℂ} (hV : MemLp V 2 (μ.prod μ))
    {f : K → ℂ} (hf : MemLp f 2 μ) :
    AEStronglyMeasurable (kernelAction V f μ) μ := by
  unfold kernelAction
  exact (integrable_kernel_mul hV hf).aestronglyMeasurable.integral_prod_right'

/-! ## `KernelL2` — the bundled kernel data

To make downstream `kernelOperator` constructions clean, we package the
data `(V, hMem)` as a single subtype. This is the input type to the
eventual `kernelOperator : KernelL2 μ → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`. -/

/-- The space of L²(K × K, μ ⊗ μ)-valued kernels. -/
def KernelL2 (μ : Measure K) [SFinite μ] : Type _ :=
  { V : K × K → ℂ // MemLp V 2 (μ.prod μ) }

namespace KernelL2

variable [SFinite μ]

/-- The kernel as a raw function. -/
@[coe] def toFun (V : KernelL2 μ) : K × K → ℂ := V.val

instance : CoeFun (KernelL2 μ) (fun _ => K × K → ℂ) := ⟨toFun⟩

/-- The bundled `MemLp` witness. -/
theorem memLp (V : KernelL2 μ) : MemLp (V : K × K → ℂ) 2 (μ.prod μ) := V.property

section FiniteMeasure
variable [IsFiniteMeasure μ]

/-- Integrability of `V · f.comp_snd` on the product measure, packaged. -/
theorem integrable_mul (V : KernelL2 μ) {f : K → ℂ} (hf : MemLp f 2 μ) :
    Integrable (fun z => (V : K × K → ℂ) z * f z.2) (μ.prod μ) :=
  integrable_kernel_mul V.memLp hf

/-- For a.e. `x`, the section `y ↦ V(x, y) · f y` is integrable, packaged. -/
theorem integrable_section (V : KernelL2 μ) {f : K → ℂ} (hf : MemLp f 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => (V : K × K → ℂ) (x, y) * f y) μ :=
  integrable_kernel_section V.memLp hf

/-- `kernelAction (V : KernelL2 μ) f` is AEStronglyMeasurable, packaged. -/
theorem aestronglyMeasurable_action (V : KernelL2 μ) {f : K → ℂ}
    (hf : MemLp f 2 μ) :
    AEStronglyMeasurable (kernelAction (V : K × K → ℂ) f μ) μ :=
  aestronglyMeasurable_kernelAction V.memLp hf

end FiniteMeasure
end KernelL2

/-! ## The Hilbert-Schmidt L²-bound

For `V ∈ L²(K × K, μ ⊗ μ)` and `f ∈ L²(K, μ)`, the integral kernel action

  (T_V f)(x) = ∫ V(x, y) · f(y) dμ(y)

satisfies

  ‖T_V f‖_{L²(μ)} ≤ ‖V‖_{L²(μ ⊗ μ)} · ‖f‖_{L²(μ)}.

Proof strategy (lintegral form, then take square roots):
1. For a.e. `x`: pointwise bound from triangle inequality + Cauchy-Schwarz
   gives `‖(T_V f)(x)‖ₑ² ≤ (∫⁻ y, ‖V(x, y)‖ₑ² ∂μ) · (∫⁻ y, ‖f(y)‖ₑ² ∂μ)`.
2. Integrate in `x`, pull `eLpNorm f 2 μ²` out as constant, apply Fubini-Tonelli
   to identify `∫⁻ x, ∫⁻ y, ‖V(x, y)‖ₑ² ∂μ ∂μ = (eLpNorm V 2 (μ.prod μ))²`.
3. Convert from squared lintegrals back to `eLpNorm` via `rpow (1/2)`.
-/

section HilbertSchmidtBound

variable [SFinite μ] [IsFiniteMeasure μ]

open ENNReal

omit [SFinite μ] [IsFiniteMeasure μ] in
/-- **Pointwise lintegral bound** for the kernel action via Cauchy-Schwarz.

    `‖kernelAction V f x‖ₑ ≤ (∫⁻ y, ‖V(x, y)‖ₑ ^ 2 ∂μ) ^ (1/2)
                         · (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) ^ (1/2)`.

    Combines `enorm_integral_le_lintegral_enorm` (Bochner norm bound) with
    `ENNReal.lintegral_mul_le_Lp_mul_Lq` (Hölder at lintegral level, p=q=2).

    Requires AEMeasurability of the relevant sections for the Hölder step. -/
theorem enorm_kernelAction_le
    {V : K × K → ℂ} {f : K → ℂ} (x : K)
    (hVsec : AEMeasurable (fun y => ‖V (x, y)‖ₑ) μ)
    (hfMble : AEMeasurable (fun y => ‖f y‖ₑ) μ) :
    ‖kernelAction V f μ x‖ₑ ≤
      (∫⁻ y, ‖V (x, y)‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
      (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
  unfold kernelAction
  -- Step A: ‖∫ V(x,y)·f y dμ y‖ₑ ≤ ∫⁻ y, ‖V(x,y)‖ₑ · ‖f y‖ₑ ∂μ
  have h_norm_int :
      ‖∫ y, V (x, y) * f y ∂μ‖ₑ ≤
        ∫⁻ y, ‖V (x, y)‖ₑ * ‖f y‖ₑ ∂μ := by
    calc ‖∫ y, V (x, y) * f y ∂μ‖ₑ
        ≤ ∫⁻ y, ‖V (x, y) * f y‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ‖V (x, y)‖ₑ * ‖f y‖ₑ ∂μ := by
          congr 1
          ext y
          rw [enorm_mul]
  -- Step B: Hölder/Cauchy-Schwarz at lintegral level (p=q=2)
  have h_holder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
      (p := 2) (q := 2)
      ⟨by norm_num, by norm_num, by norm_num⟩
      hVsec hfMble
  -- Chain via transitivity
  exact h_norm_int.trans h_holder

omit [SFinite μ] [IsFiniteMeasure μ] in
/-- **Squared pointwise bound.** Squaring `enorm_kernelAction_le` yields
    `‖kernelAction V f x‖ₑ² ≤ (∫⁻ y, ‖V(x,y)‖ₑ² ∂μ) · (∫⁻ y, ‖f y‖ₑ² ∂μ)`. -/
theorem enorm_kernelAction_sq_le
    {V : K × K → ℂ} {f : K → ℂ} (x : K)
    (hVsec : AEMeasurable (fun y => ‖V (x, y)‖ₑ) μ)
    (hfMble : AEMeasurable (fun y => ‖f y‖ₑ) μ) :
    ‖kernelAction V f μ x‖ₑ ^ (2 : ℝ) ≤
      (∫⁻ y, ‖V (x, y)‖ₑ ^ (2 : ℝ) ∂μ) *
      (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) := by
  have h := enorm_kernelAction_le (μ := μ) x hVsec hfMble
  -- h : ‖kAct‖ₑ ≤ A^(1/2) * B^(1/2)
  -- Square both sides (rpow 2 is monotone on ENNReal)
  calc ‖kernelAction V f μ x‖ₑ ^ (2 : ℝ)
      ≤ ((∫⁻ y, ‖V (x, y)‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
         (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by
        gcongr
    _ = (∫⁻ y, ‖V (x, y)‖ₑ ^ (2 : ℝ) ∂μ) ^ ((1 / (2 : ℝ)) * 2) *
        (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) ^ ((1 / (2 : ℝ)) * 2) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    _ = (∫⁻ y, ‖V (x, y)‖ₑ ^ (2 : ℝ) ∂μ) *
        (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) := by
        rw [show (1 / (2 : ℝ)) * 2 = 1 by norm_num]
        simp [ENNReal.rpow_one]

omit [IsFiniteMeasure μ] in
/-- **Hilbert-Schmidt L²-bound (lintegral form).** Integrating the squared
    pointwise bound in `x` and applying Fubini-Tonelli to the iterated
    integral of `‖V(x, y)‖ₑ²` gives the lintegral-level H-S bound:
    `∫⁻ x, ‖(T_V f)(x)‖ₑ² ∂μ ≤ (∫⁻ z, ‖V z‖ₑ² ∂(μ⊗μ)) · (∫⁻ y, ‖f y‖ₑ² ∂μ)`. -/
theorem lintegral_enorm_kernelAction_sq_le
    {V : K × K → ℂ} (hV : Measurable V)
    {f : K → ℂ} (hf : AEMeasurable (fun y => ‖f y‖ₑ) μ) :
    (∫⁻ x, ‖kernelAction V f μ x‖ₑ ^ (2 : ℝ) ∂μ) ≤
      (∫⁻ z, ‖V z‖ₑ ^ (2 : ℝ) ∂(μ.prod μ)) *
      (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) := by
  -- Apply the pointwise squared bound for each x, then integrate.
  -- The pointwise bound needs AEMeasurable (fun y => ‖V (x, y)‖ₑ) μ for each x,
  -- which follows from Measurable V via section measurability.
  have hVsec : ∀ x, Measurable (fun y => ‖V (x, y)‖ₑ) := fun x => by
    exact (hV.comp (Measurable.prodMk measurable_const measurable_id)).enorm
  -- Squared pointwise bound, holding for ALL x:
  have h_pt : ∀ x, ‖kernelAction V f μ x‖ₑ ^ (2 : ℝ) ≤
      (∫⁻ y, ‖V (x, y)‖ₑ ^ (2 : ℝ) ∂μ) *
      (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) := fun x =>
    enorm_kernelAction_sq_le x (hVsec x).aemeasurable hf
  -- Integrate the pointwise bound
  -- The inner integral x ↦ ∫⁻ y, ‖V(x,y)‖ₑ² ∂μ is measurable (Fubini-Tonelli kernel).
  have h_inner_mble :
      Measurable (fun x => ∫⁻ y, ‖V (x, y)‖ₑ ^ (2 : ℝ) ∂μ) := by
    exact Measurable.lintegral_prod_right (hV.enorm.pow_const _)
  calc (∫⁻ x, ‖kernelAction V f μ x‖ₑ ^ (2 : ℝ) ∂μ)
      ≤ ∫⁻ x, (∫⁻ y, ‖V (x, y)‖ₑ ^ (2 : ℝ) ∂μ) *
              (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) ∂μ := lintegral_mono h_pt
    _ = (∫⁻ x, ∫⁻ y, ‖V (x, y)‖ₑ ^ (2 : ℝ) ∂μ ∂μ) *
        (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) :=
        lintegral_mul_const'' _ h_inner_mble.aemeasurable
    _ = (∫⁻ z, ‖V z‖ₑ ^ (2 : ℝ) ∂(μ.prod μ)) *
        (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) := by
        -- Fubini-Tonelli for lintegral
        congr 1
        exact (MeasureTheory.lintegral_prod _ (hV.enorm.pow_const _).aemeasurable).symm

omit [IsFiniteMeasure μ] in
/-- **The Hilbert-Schmidt L²-bound (eLpNorm form).**
    `eLpNorm (kernelAction V f) 2 μ ≤ eLpNorm V 2 (μ ⊗ μ) · eLpNorm f 2 μ`. -/
theorem eLpNorm_kernelAction_le
    {V : K × K → ℂ} (hV : Measurable V)
    {f : K → ℂ} (hf : AEMeasurable (fun y => ‖f y‖ₑ) μ) :
    eLpNorm (kernelAction V f μ) 2 μ ≤
      eLpNorm V 2 (μ.prod μ) * eLpNorm f 2 μ := by
  -- Express all three eLpNorms via lintegrals
  have hp_ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_two : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne hp_top,
      eLpNorm_eq_lintegral_rpow_enorm hp_ne hp_top,
      eLpNorm_eq_lintegral_rpow_enorm hp_ne hp_top,
      h_two]
  -- Goal: (∫⁻ x, ‖kAct x‖ₑ^2 ∂μ)^(1/2) ≤ (∫⁻ z, ‖V z‖ₑ^2 ∂(μ.prod μ))^(1/2) * (∫⁻ y, ‖f y‖ₑ^2 ∂μ)^(1/2)
  -- Use the lintegral bound + monotonicity of rpow + mul_rpow distribution
  have h_lint := lintegral_enorm_kernelAction_sq_le hV hf
  calc (∫⁻ x, ‖kernelAction V f μ x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      ≤ ((∫⁻ z, ‖V z‖ₑ ^ (2 : ℝ) ∂(μ.prod μ)) *
         (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ)) ^ (1 / (2 : ℝ)) := by gcongr
    _ = (∫⁻ z, ‖V z‖ₑ ^ (2 : ℝ) ∂(μ.prod μ)) ^ (1 / (2 : ℝ)) *
        (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- **`MemLp` for the kernel action.** Combines the H-S bound with the
    AEStronglyMeasurable witness to certify that `kernelAction V f` is in
    `L²(μ)` whenever `V` is measurable & in `L²(μ⊗μ)` and `f` is in `L²(μ)`. -/
theorem memLp_kernelAction
    {V : K × K → ℂ} (hVmble : Measurable V) (hV : MemLp V 2 (μ.prod μ))
    {f : K → ℂ} (hf : MemLp f 2 μ) :
    MemLp (kernelAction V f μ) 2 μ := by
  refine ⟨aestronglyMeasurable_kernelAction hV hf, ?_⟩
  -- eLpNorm < ∞ from H-S bound: ≤ ‖V‖_{L²(μ⊗μ)} · ‖f‖_{L²(μ)}, both finite
  calc eLpNorm (kernelAction V f μ) 2 μ
      ≤ eLpNorm V 2 (μ.prod μ) * eLpNorm f 2 μ :=
        eLpNorm_kernelAction_le hVmble hf.aestronglyMeasurable.enorm
    _ < ∞ := ENNReal.mul_lt_top hV.eLpNorm_lt_top hf.eLpNorm_lt_top

/-! ### Linearity of the kernel action -/

/-- Additivity (a.e.): `kernelAction V (f + g) =ᵐ kernelAction V f + kernelAction V g`
    when each section product is integrable. -/
theorem kernelAction_add_ae
    {V : K × K → ℂ} (hV : MemLp V 2 (μ.prod μ))
    {f g : K → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    kernelAction V (f + g) μ =ᵐ[μ]
      kernelAction V f μ + kernelAction V g μ := by
  filter_upwards [integrable_kernel_section hV hf,
                  integrable_kernel_section hV hg] with x hxf hxg
  simp only [Pi.add_apply, kernelAction]
  -- ∫ V(x,y) * (f y + g y) dμ y = ∫ V(x,y) * f y + V(x,y) * g y dμ y
  --                            = ∫ V(x,y) * f y dμ y + ∫ V(x,y) * g y dμ y
  have h_eq : (fun y => V (x, y) * (f y + g y))
            = (fun y => V (x, y) * f y + V (x, y) * g y) := by
    funext y; ring
  rw [h_eq, integral_add hxf hxg]

/-- Scalar multiplication (a.e.): `kernelAction V (c • f) =ᵐ c • kernelAction V f`. -/
theorem kernelAction_smul_ae
    {V : K × K → ℂ} (hV : MemLp V 2 (μ.prod μ))
    (c : ℂ) {f : K → ℂ} (hf : MemLp f 2 μ) :
    kernelAction V (c • f) μ =ᵐ[μ] c • kernelAction V f μ := by
  filter_upwards [integrable_kernel_section hV hf] with x hxf
  simp only [Pi.smul_apply, kernelAction, smul_eq_mul]
  -- ∫ V(x,y) * (c * f y) dμ y = c * ∫ V(x,y) * f y dμ y
  have h_eq : (fun y => V (x, y) * (c * f y))
            = (fun y => c * (V (x, y) * f y)) := by
    funext y; ring
  rw [h_eq, integral_const_mul]

/-! ### The kernel operator as a function and as a linear map -/

/-- Function-level kernel operator action: takes an `Lp ℂ 2 μ` element `f` to
    the `Lp ℂ 2 μ` element of `kernelAction V f` (using `memLp_kernelAction`
    as the membership witness). -/
noncomputable def kernelOperatorFn
    {V : K × K → ℂ} (hVmble : Measurable V) (hV : MemLp V 2 (μ.prod μ))
    (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_kernelAction hVmble hV (Lp.memLp f)).toLp (kernelAction V (f : K → ℂ) μ)

/-- The Lp-coercion of `kernelOperatorFn V f` is a.e. equal to the raw
    `kernelAction V f`. -/
theorem coeFn_kernelOperatorFn
    {V : K × K → ℂ} (hVmble : Measurable V) (hV : MemLp V 2 (μ.prod μ))
    (f : Lp ℂ 2 μ) :
    (kernelOperatorFn hVmble hV f : K → ℂ) =ᵐ[μ] kernelAction V (f : K → ℂ) μ :=
  MemLp.coeFn_toLp _

/-- Norm bound on the function-level operator action. -/
theorem norm_kernelOperatorFn_le
    {V : K × K → ℂ} (hVmble : Measurable V) (hV : MemLp V 2 (μ.prod μ))
    (f : Lp ℂ 2 μ) :
    ‖kernelOperatorFn hVmble hV f‖ ≤ (eLpNorm V 2 (μ.prod μ)).toReal * ‖f‖ := by
  unfold kernelOperatorFn
  rw [Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  -- Goal: (eLpNorm (kernelAction V (↑f) μ) 2 μ).toReal ≤ (eLpNorm V 2 (μ.prod μ)).toReal * ‖f‖
  have h_norm_f : ‖f‖ = (eLpNorm (f : K → ℂ) 2 μ).toReal := Lp.norm_def f
  rw [h_norm_f]
  rw [← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
  · exact ENNReal.mul_ne_top hV.eLpNorm_ne_top (Lp.memLp f).eLpNorm_ne_top
  · exact eLpNorm_kernelAction_le hVmble (Lp.memLp f).aestronglyMeasurable.enorm

/-- Additivity of `kernelOperatorFn` on `Lp ℂ 2 μ`. -/
theorem kernelOperatorFn_add
    {V : K × K → ℂ} (hVmble : Measurable V) (hV : MemLp V 2 (μ.prod μ))
    (f g : Lp ℂ 2 μ) :
    kernelOperatorFn hVmble hV (f + g) =
      kernelOperatorFn hVmble hV f + kernelOperatorFn hVmble hV g := by
  apply Lp.ext
  refine (coeFn_kernelOperatorFn hVmble hV (f + g)).trans ?_
  -- kernelAction V ((f + g : Lp) : K → ℂ) μ =ᵐ (kOp f + kOp g : Lp ℂ 2 μ : K → ℂ)
  have h_coe_add : ((f + g : Lp ℂ 2 μ) : K → ℂ) =ᵐ[μ]
                   (f : K → ℂ) + (g : K → ℂ) := Lp.coeFn_add f g
  -- kernelAction is congruent under ae-eq of input
  have h1 : kernelAction V ((f + g : Lp ℂ 2 μ) : K → ℂ) μ =ᵐ[μ]
            kernelAction V ((f : K → ℂ) + (g : K → ℂ)) μ := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    unfold kernelAction
    apply integral_congr_ae
    filter_upwards [h_coe_add] with y hy
    rw [hy]
  -- additivity at the function level
  have h2 := kernelAction_add_ae hV (Lp.memLp f) (Lp.memLp g)
  refine (h1.trans h2).trans ?_
  -- now align with the Lp coercion of the sum
  symm
  refine (Lp.coeFn_add _ _).trans ?_
  filter_upwards [coeFn_kernelOperatorFn hVmble hV f,
                  coeFn_kernelOperatorFn hVmble hV g] with x hx1 hx2
  simp [hx1, hx2]

/-- Homogeneity of `kernelOperatorFn` on `Lp ℂ 2 μ`. -/
theorem kernelOperatorFn_smul
    {V : K × K → ℂ} (hVmble : Measurable V) (hV : MemLp V 2 (μ.prod μ))
    (c : ℂ) (f : Lp ℂ 2 μ) :
    kernelOperatorFn hVmble hV (c • f) = c • kernelOperatorFn hVmble hV f := by
  apply Lp.ext
  refine (coeFn_kernelOperatorFn hVmble hV (c • f)).trans ?_
  have h_coe_smul : ((c • f : Lp ℂ 2 μ) : K → ℂ) =ᵐ[μ]
                    c • (f : K → ℂ) := Lp.coeFn_smul c f
  have h1 : kernelAction V ((c • f : Lp ℂ 2 μ) : K → ℂ) μ =ᵐ[μ]
            kernelAction V (c • (f : K → ℂ)) μ := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    unfold kernelAction
    apply integral_congr_ae
    filter_upwards [h_coe_smul] with y hy
    rw [hy]
  have h2 := kernelAction_smul_ae hV c (Lp.memLp f)
  refine (h1.trans h2).trans ?_
  symm
  refine (Lp.coeFn_smul c _).trans ?_
  filter_upwards [coeFn_kernelOperatorFn hVmble hV f] with x hx1
  simp [hx1]

/-- **The Hilbert-Schmidt integral kernel operator** as a bounded linear map
    `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`.

    Given a measurable kernel `V` in `L²(K × K, μ ⊗ μ)`, the operator acts as
    `(kernelOperator V _ _ f)(x) = ∫ V(x, y) · f(y) dμ(y)` (a.e. in x), and
    its operator norm is bounded by `‖V‖_{L²(μ ⊗ μ)}`. -/
noncomputable def kernelOperator
    {V : K × K → ℂ} (hVmble : Measurable V) (hV : MemLp V 2 (μ.prod μ)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := kernelOperatorFn hVmble hV
      map_add' := kernelOperatorFn_add hVmble hV
      map_smul' := kernelOperatorFn_smul hVmble hV }
    (eLpNorm V 2 (μ.prod μ)).toReal
    (norm_kernelOperatorFn_le hVmble hV)

end HilbertSchmidtBound

end PrincipiaTractalis.IntegralKernel
