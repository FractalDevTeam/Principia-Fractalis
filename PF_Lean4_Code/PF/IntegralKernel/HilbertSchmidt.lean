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

/-! ## Next milestone: the Hilbert-Schmidt L²-bound

The remaining analytic step:
```
theorem eLpNorm_kernelAction_le (V : KernelL2 μ) (f : K → ℂ) (hf : MemLp f 2 μ) :
    eLpNorm (kernelAction V f μ) 2 μ ≤ eLpNorm V 2 (μ.prod μ) * eLpNorm f 2 μ
```

Proof outline:
1. **Pointwise Cauchy-Schwarz** (for a.e. `x`): viewing the integrand as an
   inner-product-like form, `|∫ V(x, y) · f(y) dμ(y)| ≤ ‖V(x, ·)‖₂ · ‖f‖₂`.
2. **Fubini-Tonelli for the squared norm**:
   `∫⁻ x, ‖V(x, ·)‖₊² ∂μ = ∫⁻ x, ∫⁻ y, ‖V(x, y)‖₊² ∂μ ∂μ = eLpNorm V 2 (μ ⊗ μ)²`.
3. Combine and take square roots.

Once established, `kernelAction V f` lies in `Lp ℂ 2 μ` and we build:
```
def kernelOperator (V : KernelL2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous {
    toFun := fun f => MemLp.toLp _ (memLp_kernelAction V f.memLp)
    map_add' := …  -- from linearity of the inner integral
    map_smul' := …
  } ‖(V : K × K → ℂ)‖_{L²(μ⊗μ)} (eLpNorm_kernelAction_le V)
```

The L1 lift then gives `IsSelfAdjoint (kernelOperator V)` whenever
`IsConjSymmetric (V : K × K → ℂ) μ` holds, closing the L2 chain for V_P. -/

end PrincipiaTractalis.IntegralKernel
