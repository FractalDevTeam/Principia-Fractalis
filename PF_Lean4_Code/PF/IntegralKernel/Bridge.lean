/-
# Bridge: H_P from V_P via the Hilbert-Schmidt construction

The book's H_P operator (Chapter 21, Definition 4.2) is the integral kernel
operator on `L²(K, μ)` with kernel `V_P(x, y) = Σ a^{-n} cos(π · √2^n · d(x, y))`.

Using:
* `V_P_canonical` (Ch 21 canonical α = √2 kernel, from `FractalKernel.lean`)
* `kernelOperator` (the Hilbert-Schmidt operator construction, from `HilbertSchmidt.lean`)
* `fractalKernel_isConjSymmetric` (conjugate symmetry of V_P)
* `isSelfAdjoint_of_kernel_conjSymm` (the L1 self-adjointness lift)

this file defines `H_P_canonical` as `kernelOperator V_P_canonical _ _` and
proves `IsSelfAdjoint H_P_canonical` as a theorem.

Stage L2 — bridge layer connecting V_P kernel to H_P self-adjointness.
-/

import PF.IntegralKernel.SelfAdjoint
import PF.IntegralKernel.FractalKernel
import PF.IntegralKernel.HilbertSchmidt

namespace PrincipiaTractalis.IntegralKernel

open MeasureTheory

variable {K : Type*} [PseudoMetricSpace K] [MeasurableSpace K]
  [SecondCountableTopology K] [OpensMeasurableSpace K]
  {μ : Measure K} [SFinite μ] [IsFiniteMeasure μ]

/-! ## Norm-domination bound for the pairing integrand

For a kernel `V` bounded by `C` (almost everywhere), the pairing integrand
`(x, y) ↦ conj(f x) · V(x, y) · g(y)` is dominated by `C · ‖f x‖ · ‖g y‖`,
which is integrable on `μ.prod μ` whenever `f, g ∈ L¹(μ)`.
-/

omit [PseudoMetricSpace K] [SecondCountableTopology K] [OpensMeasurableSpace K]
  [SFinite μ] in
/-- For finite μ and a kernel V bounded by C, the pairing integrand is
    `L¹(μ⊗μ)`-integrable whenever f, g ∈ L²(μ). -/
theorem integrable_pairingIntegrand_of_bounded
    {V : K × K → ℂ} (hVmble : Measurable V) {C : ℝ} (hC : 0 ≤ C)
    (hVbdd : ∀ z, ‖V z‖ ≤ C)
    {f g : K → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (pairingIntegrand V f g) (μ.prod μ) := by
  -- Both |f| and |g| are integrable (L² ⊂ L¹ on finite measure).
  have h_one_le_two : (1 : ENNReal) ≤ 2 := by norm_num
  have hf_int : Integrable f μ := hf.integrable h_one_le_two
  have hg_int : Integrable g μ := hg.integrable h_one_le_two
  have hf_norm_int : Integrable (fun y => ‖f y‖) μ := hf_int.norm
  have hg_norm_int : Integrable (fun y => ‖g y‖) μ := hg_int.norm
  -- Their product is integrable on the product measure via Integrable.mul_prod.
  have h_prod_norm_int :
      Integrable (fun z : K × K => ‖f z.1‖ * ‖g z.2‖) (μ.prod μ) :=
    hf_norm_int.mul_prod hg_norm_int
  -- Scaled by C:
  have h_C_prod : Integrable
      (fun z : K × K => C * (‖f z.1‖ * ‖g z.2‖)) (μ.prod μ) :=
    h_prod_norm_int.const_mul C
  -- pairingIntegrand is AEStronglyMeasurable (continuous-ish composition).
  -- conj is continuous, V is measurable, f, g are aestronglyMeasurable.
  have h_pi_aestronglyMeasurable :
      AEStronglyMeasurable (pairingIntegrand V f g) (μ.prod μ) := by
    unfold pairingIntegrand
    refine .mul (.mul ?_ ?_) ?_
    · -- (z → conj(f z.1)) = Complex.conj ∘ (z → f z.1)
      exact Complex.continuous_conj.comp_aestronglyMeasurable
              hf.aestronglyMeasurable.comp_fst
    · exact hVmble.aestronglyMeasurable
    · exact hg.aestronglyMeasurable.comp_snd
  -- Norm domination: |conj(f x) · V(x,y) · g y| ≤ C · |f x| · |g y|
  apply Integrable.mono h_C_prod h_pi_aestronglyMeasurable
  refine Filter.Eventually.of_forall (fun z => ?_)
  unfold pairingIntegrand
  -- |conj(f z.1) * V z * g z.2| = |f z.1| * |V z| * |g z.2| ≤ |f z.1| * C * |g z.2|
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ C * (‖f z.1‖ * ‖g z.2‖))]
  have h_norm_eq : ‖(starRingEnd ℂ) (f z.1) * V z * g z.2‖
                 = ‖f z.1‖ * ‖V z‖ * ‖g z.2‖ := by
    rw [norm_mul, norm_mul]
    congr 1
    congr 1
    exact Complex.norm_conj _
  rw [h_norm_eq]
  calc ‖f z.1‖ * ‖V z‖ * ‖g z.2‖
      ≤ ‖f z.1‖ * C * ‖g z.2‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (hVbdd z) (norm_nonneg _)
    _ = C * (‖f z.1‖ * ‖g z.2‖) := by ring

/-! ## H_P_canonical and its self-adjointness -/

/-- **The book's canonical H_P operator**, instantiated as a Hilbert-Schmidt
    integral kernel operator with the V_P kernel (Ch 21 Definition 4.2). -/
noncomputable def H_P_canonical {a : ℝ} (ha : 1 < a) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  kernelOperator
    (measurable_fractalKernel (Real.sqrt 2) ha)
    (memLp_fractalKernel (Real.sqrt 2) ha μ 2)

/-- **Self-adjointness of H_P**. Proved by combining:
    - `coeFn_kernelOperatorFn` (the action matches the kernel action)
    - `fractalKernel_isConjSymmetric` (V_P is conj-symmetric)
    - `integrable_pairingIntegrand_of_bounded` (V_P is bounded by a/(a-1))
    - `isSelfAdjoint_of_kernel_conjSymm` (L1 lift). -/
theorem H_P_canonical_isSelfAdjoint {a : ℝ} (ha : 1 < a) :
    IsSelfAdjoint (H_P_canonical (μ := μ) ha) := by
  apply isSelfAdjoint_of_kernel_conjSymm
      (V := fractalKernel (Real.sqrt 2) a)
      (T := H_P_canonical (μ := μ) ha)
  · -- hAction: (H_P_canonical g : K → ℂ) =ᵐ kernelAction V g μ
    intro g
    exact coeFn_kernelOperatorFn
      (measurable_fractalKernel (Real.sqrt 2) ha)
      (memLp_fractalKernel (Real.sqrt 2) ha μ 2) g
  · -- hSym: IsConjSymmetric V_P μ
    exact fractalKernel_isConjSymmetric (Real.sqrt 2) a μ
  · -- hFub: pairingIntegrand integrable for all f, g ∈ Lp ℂ 2 μ
    intro f g
    -- V_P satisfies ‖V_P z‖ ≤ a/(a-1) for all z
    have C := a / (a - 1)
    have h_a_pos : 0 < a := lt_trans zero_lt_one ha
    have h_C_nn : 0 ≤ a / (a - 1) :=
      div_nonneg h_a_pos.le (by linarith)
    have h_Vbdd : ∀ z : K × K,
        ‖(fractalKernel (Real.sqrt 2) a) z‖ ≤ a / (a - 1) := by
      intro z
      unfold fractalKernel
      rw [show ‖(((fractalKernelReal (Real.sqrt 2) a z : ℝ) : ℂ))‖ =
            |fractalKernelReal (Real.sqrt 2) a z| from
          RCLike.norm_ofReal (K := ℂ) _]
      exact abs_fractalKernelReal_le (Real.sqrt 2) ha z
    exact integrable_pairingIntegrand_of_bounded
      (measurable_fractalKernel (Real.sqrt 2) ha) h_C_nn h_Vbdd
      (Lp.memLp f) (Lp.memLp g)

/-! ## H_NP_canonical via unitary conjugation

The book's H_NP (Ch 21 line 510) is a unitary conjugate of H_P:
`H_NP = U(φ) · H_P · U(φ)†`, where `U(φ)` is a rotation by the golden
angle. Since unitary conjugation preserves self-adjointness, H_NP's
self-adjointness follows immediately from H_P's.

For the abstract framework, we parameterize over an arbitrary conjugating
CLM `S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`. The book's `R_φ` is a specific
instance; for self-adjointness we don't need to fix the instance, since
`IsSelfAdjoint.conj_adjoint` works for any conjugating map.
-/

/-- **The book's canonical H_NP operator** as a conjugate of H_P by a CLM
    `S` (think `S = U(φ)`, the unitary rotation by golden angle). -/
noncomputable def H_NP_via_conjugation
    (S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) {a : ℝ} (ha : 1 < a) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  S ∘L (H_P_canonical (μ := μ) ha) ∘L S.adjoint

/-- **Self-adjointness of H_NP_via_conjugation**. Follows from
    `IsSelfAdjoint.conj_adjoint`: conjugating any self-adjoint operator
    by an arbitrary CLM preserves self-adjointness. -/
theorem H_NP_via_conjugation_isSelfAdjoint
    (S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) {a : ℝ} (ha : 1 < a) :
    IsSelfAdjoint (H_NP_via_conjugation S ha) :=
  (H_P_canonical_isSelfAdjoint ha).conj_adjoint S

/-- **The identity-conjugate case**: when `S = id`, `H_NP_via_conjugation`
    coincides with `H_P_canonical`. Useful as the trivial (degenerate)
    instance illustrating the construction. -/
theorem H_NP_via_conjugation_id_eq_H_P
    {a : ℝ} (ha : 1 < a) :
    H_NP_via_conjugation
      (ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) ha =
      H_P_canonical (μ := μ) ha := by
  unfold H_NP_via_conjugation
  simp

end PrincipiaTractalis.IntegralKernel
