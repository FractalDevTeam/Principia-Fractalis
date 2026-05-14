/-
# Integral Kernel Operators — Self-Adjointness Lift

Given a bounded linear operator `T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` whose action
agrees almost everywhere with the kernel action of a conjugate-symmetric
kernel `V : K × K → ℂ`, this file proves that `T` is *symmetric* (and hence
self-adjoint, since `T` is bounded) by lifting the integrand-level Fubini
symmetry from `Basic.lean` to the L² inner product.

The lift route:
1. `⟪f, T g⟫ = ∫ x, conj(f(x)) · (T g)(x) dμ`            (definition)
2. `(T g)(x) = ∫ y, V(x, y) · g(y) dμ(y)` a.e.            (action hypothesis)
3. `∫ x, conj(f(x)) · ∫ y, V(x, y) · g(y) dμ(y) dμ(x)
       = ∫ x, ∫ y, conj(f(x)) · V(x, y) · g(y) dμ(y) dμ(x)`
                                                            (pull constant in)
4. `= pairing V f g μ`                                       (definition)
5. Symmetric pairing under `IsConjSymmetric V μ` (from `Basic.lean`)
6. Combined: `⟪f, T g⟫ = pairing V f g μ
                       = conj (pairing V g f μ)
                       = conj ⟪g, T f⟫
                       = ⟪T f, g⟫`.

Reference: Principia Fractalis, Chapter 21, Theorem 4.4 (Self-Adjointness
of the fractal convolution operators).

Stage L1 — file 2 of 2.
-/

import PF.IntegralKernel.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace PrincipiaTractalis.IntegralKernel

open MeasureTheory

variable {K : Type*} [MeasurableSpace K] {μ : Measure K} [SFinite μ]

/-! ## Identifying the pairing with the L² inner product -/

/-- **Step 1 lemma**: `⟪f, T g⟫_L² = pairing V f g μ` whenever the action of
    `T` on `g` equals the kernel action of `V` almost everywhere, and the
    relevant integrability conditions hold.

    The hypotheses are:
    * `hAction` — pointwise a.e. identification of `T g` with `kernelAction V g`;
    * `hInner_int` — integrability of the inner-product integrand
      (automatic for L² functions on a kernel-action of an L² function once
      bounded; users supply directly here);
    * `hFub` — integrability of the joint integrand on the product measure
      (Fubini precondition). -/
theorem inner_eq_pairing
    (V : K × K → ℂ) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (f g : Lp ℂ 2 μ)
    (hAction : (T g : K → ℂ) =ᵐ[μ] kernelAction V ((g : K → ℂ)) μ)
    (hFub : Integrable (pairingIntegrand V ((f : K → ℂ)) ((g : K → ℂ)))
              (μ.prod μ)) :
    @inner ℂ _ _ f (T g) = pairing V ((f : K → ℂ)) ((g : K → ℂ)) μ := by
  -- inner ↦ integral form (L² definition)
  rw [L2.inner_def (𝕜 := ℂ)]
  -- Rewrite the integrand using the action hypothesis a.e.
  have h_ae :
      (fun x => @inner ℂ _ _ ((f : K → ℂ) x) ((T g : K → ℂ) x))
        =ᵐ[μ]
      (fun x => (starRingEnd ℂ) ((f : K → ℂ) x) *
                (kernelAction V ((g : K → ℂ)) μ x)) := by
    filter_upwards [hAction] with x hx
    rw [RCLike.inner_apply' (𝕜 := ℂ), hx]
  rw [integral_congr_ae h_ae]
  -- Pull `conj (f x)` inside the inner integral
  have h_pull :
      (fun x => (starRingEnd ℂ) ((f : K → ℂ) x) *
                (kernelAction V ((g : K → ℂ)) μ x))
        = (fun x => ∫ y, (starRingEnd ℂ) ((f : K → ℂ) x) *
                          (V (x, y) * (g : K → ℂ) y) ∂μ) := by
    funext x
    unfold kernelAction
    rw [integral_const_mul]
  rw [h_pull]
  -- Re-associate to match `pairingIntegrand`
  have h_assoc :
      (fun x => ∫ y, (starRingEnd ℂ) ((f : K → ℂ) x) *
                       (V (x, y) * (g : K → ℂ) y) ∂μ)
        = (fun x => ∫ y, pairingIntegrand V ((f : K → ℂ)) ((g : K → ℂ))
                          (x, y) ∂μ) := by
    funext x
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    unfold pairingIntegrand
    ring
  rw [h_assoc, pairing_eq_integral_prod hFub]
  -- Goal: ∫ x, ∫ y, pairingIntegrand V f g (x, y) ∂μ ∂μ
  --     = ∫ z, pairingIntegrand V f g z ∂(μ.prod μ)
  exact (MeasureTheory.integral_prod _ hFub).symm

/-! ## Symmetry of the operator from conjugate symmetry of the kernel

The composite theorem: a CLM whose action matches a conjugate-symmetric
kernel's action is symmetric (and therefore self-adjoint, since it is
already bounded).
-/

/-- **Symmetric-operator lift.** If `T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`'s action
    matches that of a conjugate-symmetric kernel `V`, and the natural
    Fubini integrability holds for every pair `(f, g)`, then the
    underlying linear map `(T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ)` is symmetric. -/
theorem isSymmetric_of_kernel_conjSymm
    (V : K × K → ℂ) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hAction : ∀ g : Lp ℂ 2 μ,
        (T g : K → ℂ) =ᵐ[μ] kernelAction V ((g : K → ℂ)) μ)
    (hSym : IsConjSymmetric V μ)
    (hFub : ∀ f g : Lp ℂ 2 μ,
        Integrable (pairingIntegrand V ((f : K → ℂ)) ((g : K → ℂ)))
          (μ.prod μ)) :
    LinearMap.IsSymmetric (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) := by
  intro f g
  -- Normalize the LinearMap-coercion form to the CLM-application form
  show @inner ℂ _ _ (T f) g = @inner ℂ _ _ f (T g)
  -- Convert via inner_eq_pairing on both sides
  have h_fg : @inner ℂ _ _ f (T g) =
              pairing V ((f : K → ℂ)) ((g : K → ℂ)) μ :=
    inner_eq_pairing V T f g (hAction g) (hFub f g)
  have h_gf : @inner ℂ _ _ g (T f) =
              pairing V ((g : K → ℂ)) ((f : K → ℂ)) μ :=
    inner_eq_pairing V T g f (hAction f) (hFub g f)
  -- inner_conj_symm a b : conj ⟪b, a⟫ = ⟪a, b⟫;  with a = T f, b = g
  --   gives conj ⟪g, T f⟫ = ⟪T f, g⟫
  have h_Tf_g : @inner ℂ _ _ (T f) g = (starRingEnd ℂ) (@inner ℂ _ _ g (T f)) :=
    (inner_conj_symm (𝕜 := ℂ) (T f) g).symm
  rw [h_Tf_g, h_gf, h_fg]
  -- Goal: conj (pairing V g f μ) = pairing V f g μ
  have := pairing_conj_symm hSym (hFub f g) (hFub g f)
  exact this.symm

/-- **Self-adjoint-operator lift.** A bounded operator whose action matches
    a conjugate-symmetric kernel is self-adjoint. Immediate corollary of
    `isSymmetric_of_kernel_conjSymm` and Mathlib's
    `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`. -/
theorem isSelfAdjoint_of_kernel_conjSymm
    (V : K × K → ℂ) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hAction : ∀ g : Lp ℂ 2 μ,
        (T g : K → ℂ) =ᵐ[μ] kernelAction V ((g : K → ℂ)) μ)
    (hSym : IsConjSymmetric V μ)
    (hFub : ∀ f g : Lp ℂ 2 μ,
        Integrable (pairingIntegrand V ((f : K → ℂ)) ((g : K → ℂ)))
          (μ.prod μ)) :
    IsSelfAdjoint T :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (isSymmetric_of_kernel_conjSymm V T hAction hSym hFub)

end PrincipiaTractalis.IntegralKernel
