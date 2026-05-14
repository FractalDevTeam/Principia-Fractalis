/-
# Integral Kernel Operators — Foundation

Infrastructure for building integral kernel operators on `L²(K, μ)` from
a kernel `V : K × K → ℂ`. The operator acts as

  (T_V f)(x) = ∫ V(x, y) · f(y) dμ(y)

This file establishes the *action* of the kernel as an unwrapped function
`K → ℂ` plus the foundational Fubini lemma: if `V` is conjugate-symmetric
(`V(x, y) = conj(V(y, x))`), then the bilinear pairing

  ⟨f, T_V g⟩ = ∫∫ conj(f(x)) · V(x, y) · g(y) dμ(y) dμ(x)

is conjugate-symmetric in `(f, g)`. This is the seed of self-adjointness:
once the action is wrapped into a bounded operator on `Lp ℂ 2 μ` (next file,
`SelfAdjoint.lean`), the symmetry passes to `⟪f, T_V g⟫ = ⟪T_V f, g⟫`.

Reference: Principia Fractalis, Chapter 21, Definition 4.2
(`def:fractal-convolution`), and Theorem 4.3 (Self-Adjointness Criterion).

Stage L1 — file 1 of 2.
-/

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.RCLike.Basic

namespace PrincipiaTractalis.IntegralKernel

open MeasureTheory

variable {K : Type*} [MeasurableSpace K] {μ : Measure K} [SFinite μ]

/-- The unwrapped *kernel action* of `V : K × K → ℂ` on a function `f : K → ℂ`:
    `(kernelAction V f) x = ∫ V(x, y) · f(y) dμ(y)`.

    This is the integrand-level operator before promotion to a bounded map on
    `Lp ℂ 2 μ`. Well-definedness as an `Lp` element requires extra hypotheses
    (`V ∈ L²(K × K, μ ⊗ μ)`), which are addressed in `SelfAdjoint.lean`. -/
noncomputable def kernelAction (V : K × K → ℂ) (f : K → ℂ) (μ : Measure K) :
    K → ℂ :=
  fun x => ∫ y, V (x, y) * f y ∂μ

/-- The bilinear pairing associated with a kernel:
    `pairing V f g = ∫∫ conj(f(x)) · V(x, y) · g(y) dμ(y) dμ(x)`.

    This unwrapped form is what eventually equals `⟪f, T_V g⟫` once `T_V` is
    a bounded operator on `Lp ℂ 2 μ`. -/
noncomputable def pairing (V : K × K → ℂ) (f g : K → ℂ) (μ : Measure K) : ℂ :=
  ∫ x, ∫ y, (starRingEnd ℂ) (f x) * V (x, y) * g y ∂μ ∂μ

/-- A kernel `V` is **conjugate-symmetric** if `V(x, y) = conj(V(y, x))` almost
    everywhere with respect to the product measure. This is the kernel-level
    self-adjointness condition. -/
def IsConjSymmetric (V : K × K → ℂ) (μ : Measure K) : Prop :=
  ∀ᵐ z ∂(μ.prod μ), V z = (starRingEnd ℂ) (V z.swap)

/-! ## Symmetry of the pairing under a conjugate-symmetric kernel

The key Fubini computation: if `V` is conjugate-symmetric and the integrand
is integrable on the product measure, then `pairing V f g = conj (pairing V g f)`.

This is the *unwrapped* self-adjointness identity. The wrapped version
(`⟪f, T_V g⟫ = ⟪T_V f, g⟫`) follows once `T_V` is realized as a bounded
operator and the pairing identified with the L² inner product (next file).
-/

/-- The integrand `(x, y) ↦ conj(f(x)) · V(x, y) · g(y)` written as a function
    on the product space. -/
noncomputable def pairingIntegrand (V : K × K → ℂ) (f g : K → ℂ) :
    K × K → ℂ :=
  fun z => (starRingEnd ℂ) (f z.1) * V z * g z.2

/-- If the pairing integrand is integrable on `μ.prod μ`, then `pairing V f g`
    equals the integral of `pairingIntegrand` on the product space. This is
    Fubini in one direction. -/
theorem pairing_eq_integral_prod
    {V : K × K → ℂ} {f g : K → ℂ}
    (hInt : Integrable (pairingIntegrand V f g) (μ.prod μ)) :
    pairing V f g μ = ∫ z, pairingIntegrand V f g z ∂(μ.prod μ) := by
  unfold pairing pairingIntegrand
  exact (MeasureTheory.integral_prod _ hInt).symm

/-- **Conjugate symmetry of the bilinear pairing under a conjugate-symmetric
    kernel.** If `V(x, y) = conj(V(y, x))` a.e. and the pairing integrand is
    integrable for both `(f, g)` and `(g, f)`, then
    `pairing V f g = conj (pairing V g f)`. -/
theorem pairing_conj_symm
    {V : K × K → ℂ} {f g : K → ℂ}
    (hSym : IsConjSymmetric V μ)
    (hInt_fg : Integrable (pairingIntegrand V f g) (μ.prod μ))
    (hInt_gf : Integrable (pairingIntegrand V g f) (μ.prod μ)) :
    pairing V f g μ = (starRingEnd ℂ) (pairing V g f μ) := by
  rw [pairing_eq_integral_prod hInt_fg, pairing_eq_integral_prod hInt_gf]
  -- conj of an integral is integral of conj
  rw [← integral_conj]
  -- swap the integration variables on the RHS
  rw [← MeasureTheory.integral_prod_swap (fun z => (starRingEnd ℂ)
        (pairingIntegrand V g f z))]
  -- Now we need to show the integrands agree pointwise a.e.
  apply integral_congr_ae
  filter_upwards [hSym] with z hzSym
  -- hzSym : V z = conj (V z.swap)
  -- Pointwise: conj(f(z.1)) * V(z.1, z.2) * g(z.2)
  --   =? conj (conj(g(z.2)) * V(z.2, z.1) * f(z.1)) ... wait, after swap
  -- After swap, z.swap = (z.2, z.1), so pairingIntegrand V g f z.swap
  --   = conj(g(z.2)) * V(z.2, z.1) * f(z.1)
  -- conj of that: g(z.2) * conj(V(z.2, z.1)) * conj(f(z.1))
  --             = conj(f(z.1)) * conj(V(z.2, z.1)) * g(z.2)  (commutativity)
  --             = conj(f(z.1)) * V(z.1, z.2) * g(z.2)  (using hzSym: V z = conj V z.swap)
  unfold pairingIntegrand
  simp only [Prod.fst_swap, Prod.snd_swap]
  -- Rewrite using V z = conj (V z.swap)
  have hV : V z.swap = (starRingEnd ℂ) (V z) := by
    have h2 := congrArg (starRingEnd ℂ) hzSym
    simp at h2
    exact h2.symm
  rw [hV]
  -- Goal: conj(f z.1) * V z * g z.2 = conj (conj(g z.2) * conj(V z) * f z.1)
  -- Distribute the outer conj over the product (RingHom is multiplicative),
  -- then `conj conj = id`, then commute factors.
  simp only [map_mul, Complex.conj_conj]
  ring

end PrincipiaTractalis.IntegralKernel
