/-
# PF.TransferCompose_r192

★★★ 2026-08-04 — A⁽ⁿ⁾ = Aⁿ: THE TRANSFER MATRIX IS A SEMIGROUP ★★★

r191 proved the trace formula for the WORD system of L^n.  This stone closes
the gap between the word system and honest matrix powers: the coefficient
matrix of the composed system IS the matrix product,

  `transferMatrix_pow` :  A⁽ⁿ⁺¹⁾ = A · A · ⋯ · A   (n+1 factors, ℓ²-products)

so combined with r191 the **trace of the actual matrix power** is the
periodic-orbit sum:

  `trace_matPow_eq_residues` :
  Σ'_m (Aⁿ⁺¹)[m,m]  =  Σ_{|α|=n+1}  W_α(x_α)/(1 − Φ_α'(x_α)).

**The analytic core** (`coeff_comp`): if `H` is given on the contraction
ball by a coefficient series `H(y) = Σ'_p b_p·((y−c)/R)^p` with
`‖b_p‖ ≤ C(R/R₁)^p`, then the `m`-th Cauchy coefficient of the transferred
image `z ↦ Σ_k w_k(z)·H(φ_k z)` is `Σ'_p A[m,p]·b_p` — coefficient
extraction commutes with the series, by the r188 dominated-interchange
machinery (`intervalIntegral_tsum`) with the geometric bound
`(R/R₁)^p·(τ/R)^p = (τ/R₁)^p`.

**The Taylor bridge** (`hasSum_transferMatrix_series`): the image functions
of any holomorphic system ARE their own coefficient series on the disc —
mathlib's `DiffContOnCl.hasFPowerSeriesOnBall` applied to the r186 Cauchy
coefficients (`cauchyPowerSeries` is `mkPiRing`, so evaluation at constant
vectors is the monomial series).

**Why it matters**: with A⁽ⁿ⁾ = Aⁿ, the periodic-orbit data of r191 computes
the trace of every matrix power of ONE fixed matrix.  These are exactly the
inputs of the Fredholm-determinant expansion det(1−tA) =
exp(−Σ_n tⁿ·Tr(Aⁿ)/n) — the dynamical zeta function / Mayer's
det(1 ∓ L_s) whose zeros carry the Selberg spectrum.  The determinant
assembly (exp/log, convergence in t) is the NEXT stone, not this one.

Scope — NOT claimed: determinants, zeta functions, spectral traces
(Lidskii), infinite-branch operators, anything about ζ(s).

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-04.
-/
import PF.TransferPower_r191

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.HilbertSchmidtL2

open Complex Metric Real
open scoped Real NNReal ENNReal

noncomputable section

variable {c : ℂ} {R R₁ τ W : ℝ} {K : ℕ} {w φ : Fin K → ℂ → ℂ}

/-! ### Matrix products -/

/-- The ℓ²-matrix product. -/
def matMul (A B : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ := fun m n => ∑' p : ℕ, A m p * B p n

/-- Positive matrix powers: `matPowPos A n = A^(n+1)`. -/
def matPowPos (A : ℕ → ℕ → ℂ) : ℕ → ℕ → ℕ → ℂ
  | 0 => A
  | n + 1 => matMul A (matPowPos A n)

/-! ### Evaluation of the Cauchy series at constant vectors -/

/-- `cauchyPowerSeries` is `mkPiRing`, so its value on the constant vector
`v` is `v^p` times its value on `1`. -/
theorem cauchyPowerSeries_apply_const (f : ℂ → ℂ) (c₀ : ℂ) (r : ℝ) (p : ℕ)
    (v : ℂ) :
    (cauchyPowerSeries f c₀ r p) (fun _ => v)
      = v ^ p * ((cauchyPowerSeries f c₀ r p) (fun _ => 1)) := by
  show (ContinuousMultilinearMap.mkPiRing ℂ (Fin p) _) (fun _ => v)
    = v ^ p * ((ContinuousMultilinearMap.mkPiRing ℂ (Fin p) _) fun _ => 1)
  rw [ContinuousMultilinearMap.mkPiRing_apply,
    ContinuousMultilinearMap.mkPiRing_apply]
  simp [smul_eq_mul, Finset.prod_const]

/-! ### The Taylor bridge -/

/-- **The image functions are their own coefficient series**: for a system
with holomorphic data, the function `F_q(z) = Σ_k w_k(z)·((φ_k z − c)/R)^q`
equals `Σ'_p A[p,q]·((y−c)/R)^p` at every `y` inside the disc. -/
theorem hasSum_transferMatrix_series {K' : ℕ} {w' φ' : Fin K' → ℂ → ℂ}
    (hR : 0 < R) (hR₁ : 0 < R₁)
    (hwd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (w' k) z)
    (hφd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (φ' k) z)
    (q : ℕ) {y : ℂ} (hy : y ∈ Metric.ball c R₁) :
    HasSum (fun p : ℕ => transferMatrix c R R₁ K' w' φ' p q * ((y - c) / (R : ℂ)) ^ p)
      (∑ k : Fin K', w' k y * (((φ' k y) - c) / (R : ℂ)) ^ q) := by
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  set F : ℂ → ℂ :=
    fun z => ∑ k : Fin K', w' k z * (((φ' k z) - c) / (R : ℂ)) ^ q with hFdef
  have hFd : ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ F z := by
    intro z hz
    have hsplit : F = ∑ k : Fin K',
        (fun z => w' k z * (((φ' k z) - c) / (R : ℂ)) ^ q) := by
      funext z
      rw [hFdef]
      simp [Finset.sum_apply]
    rw [hsplit]
    apply DifferentiableAt.sum
    intro k _
    exact (hwd k z hz).mul
      ((((hφd k z hz).sub_const c).div_const (R : ℂ)).pow q)
  have hdc : DiffContOnCl ℂ F (Metric.ball c R₁) :=
    diffContOnCl_of_differentiableAt hR₁ hFd
  -- lift the radius to ℝ≥0 for the mathlib power-series theorem
  set R₁' : ℝ≥0 := R₁.toNNReal with hR₁'def
  have hcoe : (R₁' : ℝ) = R₁ := Real.coe_toNNReal _ hR₁.le
  have hdc' : DiffContOnCl ℂ F (Metric.ball c (R₁' : ℝ)) := by
    rw [hcoe]; exact hdc
  have hps := hdc'.hasFPowerSeriesOnBall
    (by simp [hR₁'def, Real.toNNReal_pos.mpr hR₁])
  have hmem : y - c ∈ EMetric.ball (0 : ℂ) R₁' := by
    rw [EMetric.mem_ball, edist_zero_right]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    calc ‖y - c‖ₑ = ENNReal.ofReal ‖y - c‖ := by
          rw [← ofReal_norm_eq_enorm]
      _ < ENNReal.ofReal R₁ :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr hy
      _ = (R₁' : ℝ≥0∞) := by
          rw [← hcoe, ENNReal.ofReal_coe_nnreal]
  have hsum := hps.hasSum hmem
  have hcy : c + (y - c) = y := by ring
  rw [hcy] at hsum
  -- identify the terms
  have hterm : ∀ p : ℕ,
      (cauchyPowerSeries F c (R₁' : ℝ) p) (fun _ => y - c)
        = transferMatrix c R R₁ K' w' φ' p q * ((y - c) / (R : ℂ)) ^ p := by
    intro p
    rw [hcoe, cauchyPowerSeries_apply_const]
    have hA : transferMatrix c R R₁ K' w' φ' p q
        = (R : ℂ) ^ p * ((cauchyPowerSeries F c R₁ p) fun _ => 1) := by
      show (R : ℂ) ^ p • ((cauchyPowerSeries F c R₁ p) fun _ => 1) = _
      rw [smul_eq_mul]
    rw [hA, div_pow]
    field_simp
  have hfun : (fun p : ℕ => (cauchyPowerSeries F c (R₁' : ℝ) p) (fun _ => y - c))
      = fun p : ℕ => transferMatrix c R R₁ K' w' φ' p q * ((y - c) / (R : ℂ)) ^ p :=
    funext hterm
  rw [hfun] at hsum
  exact hsum

/-! ### The analytic core: coefficient extraction through a series -/

/-- **Coefficient extraction commutes with the inner series**: if
`H(y) = Σ'_p b_p·((y−c)/R)^p` on the contraction ball with
`‖b_p‖ ≤ C(R/R₁)^p`, then the `m`-th coefficient of the transferred image
`z ↦ Σ_k w_k(z)·H(φ_k z)` is `Σ'_p A[m,p]·b_p`. -/
theorem coeff_comp (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hwc : ∀ k, ContinuousOn (w k) (Metric.sphere c R₁))
    (hφc : ∀ k, ContinuousOn (φ k) (Metric.sphere c R₁))
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ)
    {C : ℝ} (hC : 0 ≤ C) {b : ℕ → ℂ} (hb : ∀ p, ‖b p‖ ≤ C * (R / R₁) ^ p)
    {H : ℂ → ℂ}
    (hH : ∀ y ∈ Metric.closedBall c τ,
      HasSum (fun p : ℕ => b p * ((y - c) / (R : ℂ)) ^ p) (H y)) (m : ℕ) :
    (R : ℂ) ^ m • (cauchyPowerSeries
        (fun z => ∑ k : Fin K, w k z * H (φ k z)) c R₁ m (fun _ => 1))
      = ∑' p : ℕ, transferMatrix c R R₁ K w φ m p * b p := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hτR₁ : τ < R₁ := hτR.trans hRR
  have hratio : τ / R₁ < 1 := by rw [div_lt_one hR₁]; linarith
  have hmem : ∀ θ : ℝ, circleMap c R₁ θ ∈ Metric.sphere c R₁ :=
    fun θ => circleMap_mem_sphere c hR₁.le θ
  have hne : ∀ θ : ℝ, circleMap c R₁ θ - c ≠ 0 := by
    intro θ
    have h := hmem θ
    rw [Metric.mem_sphere, dist_eq_norm] at h
    intro h0
    rw [h0, norm_zero] at h
    linarith
  set F : ℕ → ℂ → ℂ :=
    fun p z => ∑ k : Fin K, w k z * (((φ k z) - c) / (R : ℂ)) ^ p with hFdef
  have hFbound : ∀ (p : ℕ) {z : ℂ}, z ∈ Metric.sphere c R₁ →
      ‖F p z‖ ≤ (K : ℝ) * W * (τ / R) ^ p :=
    fun p _ hz => image_norm_le hR hτ0 hw hφ hW hz p
  have hpow_eq : ∀ p : ℕ,
      (R / R₁ : ℝ) ^ p * (τ / R) ^ p = (τ / R₁) ^ p := by
    intro p
    rw [← mul_pow]
    congr 1
    field_simp
  have hqk : ∀ (k : Fin K) {z : ℂ}, z ∈ Metric.sphere c R₁ →
      ‖(((φ k z) - c) / (R : ℂ))‖ ≤ τ / R := by
    intro k z hz
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have h1 : ‖φ k z - c‖ ≤ τ := by
      have := hφ k z hz
      rwa [Metric.mem_closedBall, dist_eq_norm] at this
    gcongr
  have hsummand : ∀ (k : Fin K) {z : ℂ}, z ∈ Metric.sphere c R₁ →
      Summable (fun p : ℕ => b p * (((φ k z) - c) / (R : ℂ)) ^ p) := by
    intro k z hz
    have hg : Summable (fun p : ℕ => C * (τ / R₁) ^ p) :=
      (summable_geometric_of_lt_one (by positivity) hratio).mul_left C
    apply Summable.of_norm_bounded hg
    intro p
    rw [norm_mul, norm_pow]
    calc ‖b p‖ * ‖(((φ k z) - c) / (R : ℂ))‖ ^ p
        ≤ (C * (R / R₁) ^ p) * (τ / R) ^ p :=
          mul_le_mul (hb p) (pow_le_pow_left₀ (norm_nonneg _) (hqk k hz) p)
            (by positivity) (by positivity)
      _ = C * (τ / R₁) ^ p := by rw [mul_assoc, hpow_eq]
  -- pointwise on the sphere: the transferred image is the b-series of images
  have hpoint : ∀ {z : ℂ}, z ∈ Metric.sphere c R₁ →
      (∑ k : Fin K, w k z * H (φ k z)) = ∑' p : ℕ, b p * F p z := by
    intro z hz
    calc (∑ k : Fin K, w k z * H (φ k z))
        = ∑ k : Fin K, ∑' p : ℕ,
            w k z * (b p * (((φ k z) - c) / (R : ℂ)) ^ p) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← (hH (φ k z) (hφ k z hz)).tsum_eq, ← tsum_mul_left]
      _ = ∑' p : ℕ, ∑ k : Fin K,
            w k z * (b p * (((φ k z) - c) / (R : ℂ)) ^ p) :=
          (Summable.tsum_finsetSum
            (fun k _ => (hsummand k hz).mul_left (w k z))).symm
      _ = ∑' p : ℕ, b p * F p z := by
          congr 1
          funext p
          simp only [hFdef]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
  -- extract the m-th coefficient
  rw [cauchyPowerSeries_apply]
  have hint : (∮ z in C(c, R₁), ((1 : ℂ) / (z - c)) ^ m • ((z - c)⁻¹ •
        (∑ k : Fin K, w k z * H (φ k z))))
      = ∮ z in C(c, R₁), ∑' p : ℕ,
          b p * (((1 : ℂ) / (z - c)) ^ m * ((z - c)⁻¹ * F p z)) := by
    apply circleIntegral.integral_congr hR₁.le
    intro z hz
    have hz' : z ∈ Metric.sphere c R₁ := by
      simpa [abs_of_pos hR₁] using hz
    dsimp only
    rw [smul_eq_mul, smul_eq_mul, hpoint hz', ← tsum_mul_left, ← tsum_mul_left]
    congr 1
    funext p
    ring
  rw [hint]
  simp only [circleIntegral]
  -- continuity of the p-summands along the parametrization
  have hcont : ∀ p : ℕ, Continuous fun θ : ℝ =>
      deriv (circleMap c R₁) θ •
        (b p * (((1 : ℂ) / (circleMap c R₁ θ - c)) ^ m *
          ((circleMap c R₁ θ - c)⁻¹ * F p (circleMap c R₁ θ)))) := by
    intro p
    apply Continuous.smul
    · exact ((continuous_circleMap 0 R₁).mul continuous_const).congr
        fun θ => (deriv_circleMap c R₁ θ).symm
    apply Continuous.mul continuous_const
    apply Continuous.mul
    · apply Continuous.pow
      exact Continuous.div continuous_const
        ((continuous_circleMap c R₁).sub continuous_const) hne
    apply Continuous.mul
    · exact Continuous.inv₀
        ((continuous_circleMap c R₁).sub continuous_const) hne
    · apply continuous_finset_sum
      intro k _
      apply Continuous.mul
      · exact (hwc k).comp_continuous (continuous_circleMap c R₁) hmem
      · apply Continuous.pow
        exact (((hφc k).comp_continuous (continuous_circleMap c R₁)
          hmem).sub continuous_const).div_const _
  -- the summable uniform bound
  have hbsum : Summable (fun p : ℕ =>
      R₁ * ((1 / R₁) ^ m * ((1 / R₁) * ((C * ((K : ℝ) * W)) * (τ / R₁) ^ p)))) := by
    apply Summable.mul_left
    apply Summable.mul_left
    apply Summable.mul_left
    exact (summable_geometric_of_lt_one (by positivity) hratio).mul_left _
  have hub : ∀ (p : ℕ) (θ : ℝ),
      ‖deriv (circleMap c R₁) θ •
        (b p * (((1 : ℂ) / (circleMap c R₁ θ - c)) ^ m *
          ((circleMap c R₁ θ - c)⁻¹ * F p (circleMap c R₁ θ))))‖
      ≤ R₁ * ((1 / R₁) ^ m * ((1 / R₁) * ((C * ((K : ℝ) * W)) * (τ / R₁) ^ p))) := by
    intro p θ
    have hzc : ‖circleMap c R₁ θ - c‖ = R₁ := by
      have := hmem θ
      rwa [Metric.mem_sphere, dist_eq_norm] at this
    have hd : ‖deriv (circleMap c R₁) θ‖ = R₁ := by
      simp [deriv_circleMap, abs_of_pos hR₁]
    rw [norm_smul, hd, norm_mul, norm_mul, norm_mul, norm_pow, norm_div,
      norm_one, norm_inv, hzc]
    apply mul_le_mul_of_nonneg_left _ hR₁.le
    calc ‖b p‖ * ((1 / R₁) ^ m * (R₁⁻¹ * ‖F p (circleMap c R₁ θ)‖))
        ≤ (C * (R / R₁) ^ p) *
            ((1 / R₁) ^ m * (R₁⁻¹ * ((K : ℝ) * W * (τ / R) ^ p))) := by
          apply mul_le_mul (hb p) _ (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left
            (hFbound p (hmem θ)) (by positivity)
      _ = (1 / R₁) ^ m * ((1 / R₁) * ((C * ((K : ℝ) * W)) * (τ / R₁) ^ p)) := by
          rw [← hpow_eq p, one_div]
          ring
  -- interchange the tsum with the contour
  have hswap : (∫ θ in (0 : ℝ)..2 * π, deriv (circleMap c R₁) θ •
        ∑' p : ℕ, b p * (((1 : ℂ) / (circleMap c R₁ θ - c)) ^ m *
          ((circleMap c R₁ θ - c)⁻¹ * F p (circleMap c R₁ θ))))
      = ∑' p : ℕ, ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap c R₁) θ •
          (b p * (((1 : ℂ) / (circleMap c R₁ θ - c)) ^ m *
            ((circleMap c R₁ θ - c)⁻¹ * F p (circleMap c R₁ θ)))) := by
    rw [← intervalIntegral_tsum hcont hbsum hub]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [tsum_const_smul'']
  rw [hswap]
  -- pull the outer scalars into the sum and identify each term
  rw [← tsum_const_smul'', ← tsum_const_smul'']
  congr 1
  funext p
  -- pull b_p out of the integral
  have hpull : (∫ θ in (0 : ℝ)..2 * π, deriv (circleMap c R₁) θ •
        (b p * (((1 : ℂ) / (circleMap c R₁ θ - c)) ^ m *
          ((circleMap c R₁ θ - c)⁻¹ * F p (circleMap c R₁ θ)))))
      = b p * ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap c R₁) θ •
          (((1 : ℂ) / (circleMap c R₁ θ - c)) ^ m *
            ((circleMap c R₁ θ - c)⁻¹ * F p (circleMap c R₁ θ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [smul_eq_mul, smul_eq_mul]
    ring
  rw [hpull]
  -- fold the remaining integral back into the transfer matrix entry
  have hA : transferMatrix c R R₁ K w φ m p
      = (R : ℂ) ^ m • ((2 * ↑π * Complex.I)⁻¹ •
          ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap c R₁) θ •
            (((1 : ℂ) / (circleMap c R₁ θ - c)) ^ m *
              ((circleMap c R₁ θ - c)⁻¹ * F p (circleMap c R₁ θ)))) := by
    show (R : ℂ) ^ m • ((cauchyPowerSeries (F p) c R₁ m) fun _ => 1) = _
    rw [cauchyPowerSeries_apply]
    simp only [circleIntegral]
    congr 2
  rw [hA]
  simp only [smul_eq_mul]
  ring

/-! ### Regrouping the word sums -/

theorem ofFn_cons {n : ℕ} (k : Fin K) (f : Fin n → Fin K) :
    List.ofFn (Fin.cons k f : Fin (n + 1) → Fin K) = k :: List.ofFn f := by
  rw [List.ofFn_succ,
    show (fun i : Fin n => (Fin.cons k f : Fin (n + 1) → Fin K) i.succ) = f from
      funext fun i => Fin.cons_succ _ _ _,
    Fin.cons_zero]

/-- The image function of the `(n+1)`-word system regroups as one base step
applied to the image function of the `n`-word system. -/
theorem powerF_succ (w φ : Fin K → ℂ → ℂ) (n q : ℕ) (z : ℂ) :
    (∑ i : Fin (K ^ (n + 1)), powerWeight w φ (n + 1) i z
        * ((powerBranch φ (n + 1) i z - c) / (R : ℂ)) ^ q)
      = ∑ k : Fin K, w k z *
          (∑ j : Fin (K ^ n), powerWeight w φ n j (φ k z)
            * ((powerBranch φ n j (φ k z) - c) / (R : ℂ)) ^ q) := by
  calc (∑ i : Fin (K ^ (n + 1)), powerWeight w φ (n + 1) i z
        * ((powerBranch φ (n + 1) i z - c) / (R : ℂ)) ^ q)
      = ∑ a : Fin (n + 1) → Fin K,
          listWeight w φ (List.ofFn a) z
            * ((listBranch φ (List.ofFn a) z - c) / (R : ℂ)) ^ q := by
        refine (Fintype.sum_equiv (finFunctionFinEquiv (m := K) (n := n + 1))
          (fun a : Fin (n + 1) → Fin K => listWeight w φ (List.ofFn a) z
            * ((listBranch φ (List.ofFn a) z - c) / (R : ℂ)) ^ q)
          (fun i : Fin (K ^ (n + 1)) => powerWeight w φ (n + 1) i z
            * ((powerBranch φ (n + 1) i z - c) / (R : ℂ)) ^ q)
          fun a => ?_).symm
        simp only [powerWeight, powerBranch, Equiv.symm_apply_apply]
    _ = ∑ x : Fin K × (Fin n → Fin K),
          listWeight w φ (List.ofFn (Fin.cons x.1 x.2)) z
            * ((listBranch φ (List.ofFn (Fin.cons x.1 x.2)) z - c) / (R : ℂ)) ^ q := by
        refine (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Fin K)
          (fun x : Fin K × (Fin n → Fin K) =>
            listWeight w φ (List.ofFn (Fin.cons x.1 x.2)) z
              * ((listBranch φ (List.ofFn (Fin.cons x.1 x.2)) z - c) / (R : ℂ)) ^ q)
          (fun a : Fin (n + 1) → Fin K => listWeight w φ (List.ofFn a) z
            * ((listBranch φ (List.ofFn a) z - c) / (R : ℂ)) ^ q)
          fun x => ?_).symm
        rfl
    _ = ∑ k : Fin K, ∑ f : Fin n → Fin K,
          listWeight w φ (k :: List.ofFn f) z
            * ((listBranch φ (k :: List.ofFn f) z - c) / (R : ℂ)) ^ q := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro f _
        rw [ofFn_cons]
    _ = ∑ k : Fin K, w k z * ∑ f : Fin n → Fin K,
          listWeight w φ (List.ofFn f) (φ k z)
            * ((listBranch φ (List.ofFn f) (φ k z) - c) / (R : ℂ)) ^ q := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f _
        simp only [listWeight_cons, listBranch_cons]
        ring
    _ = ∑ k : Fin K, w k z *
          (∑ j : Fin (K ^ n), powerWeight w φ n j (φ k z)
            * ((powerBranch φ n j (φ k z) - c) / (R : ℂ)) ^ q) := by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        refine Fintype.sum_equiv (finFunctionFinEquiv (m := K) (n := n))
          (fun f : Fin n → Fin K => listWeight w φ (List.ofFn f) (φ k z)
            * ((listBranch φ (List.ofFn f) (φ k z) - c) / (R : ℂ)) ^ q)
          (fun j : Fin (K ^ n) => powerWeight w φ n j (φ k z)
            * ((powerBranch φ n j (φ k z) - c) / (R : ℂ)) ^ q)
          fun f => ?_
        simp only [powerWeight, powerBranch, Equiv.symm_apply_apply]

/-- The image function of the `1`-word system is the base image function. -/
theorem powerF_one (w φ : Fin K → ℂ → ℂ) (q : ℕ) (z : ℂ) :
    (∑ i : Fin (K ^ 1), powerWeight w φ 1 i z
        * ((powerBranch φ 1 i z - c) / (R : ℂ)) ^ q)
      = ∑ k : Fin K, w k z * (((φ k z) - c) / (R : ℂ)) ^ q := by
  calc (∑ i : Fin (K ^ 1), powerWeight w φ 1 i z
        * ((powerBranch φ 1 i z - c) / (R : ℂ)) ^ q)
      = ∑ a : Fin 1 → Fin K,
          listWeight w φ (List.ofFn a) z
            * ((listBranch φ (List.ofFn a) z - c) / (R : ℂ)) ^ q := by
        refine (Fintype.sum_equiv (finFunctionFinEquiv (m := K) (n := 1))
          (fun a : Fin 1 → Fin K => listWeight w φ (List.ofFn a) z
            * ((listBranch φ (List.ofFn a) z - c) / (R : ℂ)) ^ q)
          (fun i : Fin (K ^ 1) => powerWeight w φ 1 i z
            * ((powerBranch φ 1 i z - c) / (R : ℂ)) ^ q)
          fun a => ?_).symm
        simp only [powerWeight, powerBranch, Equiv.symm_apply_apply]
    _ = ∑ k : Fin K, w k z * (((φ k z) - c) / (R : ℂ)) ^ q := by
        refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin K))
          (fun a : Fin 1 → Fin K => listWeight w φ (List.ofFn a) z
            * ((listBranch φ (List.ofFn a) z - c) / (R : ℂ)) ^ q)
          (fun k : Fin K => w k z * (((φ k z) - c) / (R : ℂ)) ^ q)
          fun a => ?_
        dsimp only
        have hofn : List.ofFn a = [a 0] := by
          simp only [List.ofFn_succ, List.ofFn_zero]
        rw [hofn]
        have hval : (Equiv.funUnique (Fin 1) (Fin K)) a = a 0 := rfl
        rw [hval]
        simp only [listWeight_cons, listWeight_nil, listBranch_cons,
          listBranch_nil, mul_one]

/-! ### A⁽ⁿ⁾ = Aⁿ -/

/-- The 1-word system has the base matrix. -/
theorem transferMatrix_power_one :
    transferMatrix c R R₁ (K ^ 1) (powerWeight w φ 1) (powerBranch φ 1)
      = transferMatrix c R R₁ K w φ := by
  funext m q
  show (R : ℂ) ^ m • (cauchyPowerSeries _ c R₁ m fun _ => 1)
    = (R : ℂ) ^ m • (cauchyPowerSeries _ c R₁ m fun _ => 1)
  rw [show (fun z => ∑ i : Fin (K ^ 1), powerWeight w φ 1 i z
        * ((powerBranch φ 1 i z - c) / (R : ℂ)) ^ q)
      = fun z => ∑ k : Fin K, w k z * (((φ k z) - c) / (R : ℂ)) ^ q from
    funext fun z => powerF_one w φ q z]

/-- **The composition step**: the matrix of the `(n+2)`-word system is the
product of the base matrix with the matrix of the `(n+1)`-word system. -/
theorem transferMatrix_power_succ (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hw : ∀ k, ∀ z ∈ Metric.closedBall c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (hwd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (w k) z)
    (hφd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (φ k) z)
    (n : ℕ) :
    transferMatrix c R R₁ (K ^ (n + 2))
        (powerWeight w φ (n + 2)) (powerBranch φ (n + 2))
      = matMul (transferMatrix c R R₁ K w φ)
          (transferMatrix c R R₁ (K ^ (n + 1))
            (powerWeight w φ (n + 1)) (powerBranch φ (n + 1))) := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hτR₁ : τ < R₁ := hτR.trans hRR
  have hτR₁' : τ ≤ R₁ := hτR₁.le
  -- sphere-grade data for the base system
  have hw' : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W :=
    fun k z hz => hw k z (Metric.sphere_subset_closedBall hz)
  have hφ' : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ :=
    fun k z hz => hφ k z (Metric.sphere_subset_closedBall hz)
  have hwc : ∀ k, ContinuousOn (w k) (Metric.sphere c R₁) :=
    fun k z hz => ((hwd k z
      (Metric.sphere_subset_closedBall hz)).continuousAt).continuousWithinAt
  have hφc : ∀ k, ContinuousOn (φ k) (Metric.sphere c R₁) :=
    fun k z hz => ((hφd k z
      (Metric.sphere_subset_closedBall hz)).continuousAt).continuousWithinAt
  -- the inner (n+1)-word system, sphere-grade
  have hword_ne : ∀ i : Fin (K ^ (n + 1)),
      (List.ofFn (finFunctionFinEquiv.symm i) : List (Fin K)) ≠ [] :=
    fun i => List.ne_nil_of_length_pos
      (by rw [List.length_ofFn]; exact Nat.succ_pos n)
  have hwn : ∀ j, ∀ z ∈ Metric.sphere c R₁,
      ‖powerWeight w φ (n + 1) j z‖ ≤ W ^ (n + 1) := by
    intro j z hz
    have h := norm_listWeight_le hτR₁' hW hw hφ
      (List.ofFn (finFunctionFinEquiv.symm j)) z
      (Metric.sphere_subset_closedBall hz)
    rwa [List.length_ofFn] at h
  have hφn : ∀ j, ∀ z ∈ Metric.sphere c R₁,
      powerBranch φ (n + 1) j z ∈ Metric.closedBall c τ :=
    fun j z hz => listBranch_mem_tau_of_ne_nil hτR₁' hφ (hword_ne j) z
      (Metric.sphere_subset_closedBall hz)
  have hwdn : ∀ j, ∀ z ∈ Metric.closedBall c R₁,
      DifferentiableAt ℂ (powerWeight w φ (n + 1) j) z :=
    fun j z hz => differentiableAt_listWeight hτR₁' hφ hwd hφd _ z hz
  have hφdn : ∀ j, ∀ z ∈ Metric.closedBall c R₁,
      DifferentiableAt ℂ (powerBranch φ (n + 1) j) z :=
    fun j z hz => differentiableAt_listBranch hτR₁' hφ hφd _ z hz
  have hwcn : ∀ j, ContinuousOn (powerWeight w φ (n + 1) j)
      (Metric.sphere c R₁) :=
    fun j z hz => ((hwdn j z
      (Metric.sphere_subset_closedBall hz)).continuousAt).continuousWithinAt
  have hφcn : ∀ j, ContinuousOn (powerBranch φ (n + 1) j)
      (Metric.sphere c R₁) :=
    fun j z hz => ((hφdn j z
      (Metric.sphere_subset_closedBall hz)).continuousAt).continuousWithinAt
  -- geometric bound on the inner matrix columns
  have hgb := geomBound_transferMatrix hR hRR hτ0 hτR
    (pow_nonneg hW (n + 1)) hwcn hφcn hwn hφn
  funext m q
  -- the inner image function, as the H of the core lemma
  set H : ℂ → ℂ := fun y => ∑ j : Fin (K ^ (n + 1)),
    powerWeight w φ (n + 1) j y
      * ((powerBranch φ (n + 1) j y - c) / (R : ℂ)) ^ q with hHdef
  have hH : ∀ y ∈ Metric.closedBall c τ,
      HasSum (fun p : ℕ => transferMatrix c R R₁ (K ^ (n + 1))
          (powerWeight w φ (n + 1)) (powerBranch φ (n + 1)) p q
        * ((y - c) / (R : ℂ)) ^ p) (H y) :=
    fun y hy => hasSum_transferMatrix_series hR hR₁ hwdn hφdn q
      (Metric.closedBall_subset_ball hτR₁ hy)
  have hb : ∀ p : ℕ, ‖transferMatrix c R R₁ (K ^ (n + 1))
        (powerWeight w φ (n + 1)) (powerBranch φ (n + 1)) p q‖
      ≤ (((K ^ (n + 1) : ℕ) : ℝ) * W ^ (n + 1) * (τ / R) ^ q)
          * (R / R₁) ^ p := by
    intro p
    have h := hgb p q
    calc ‖transferMatrix c R R₁ (K ^ (n + 1))
          (powerWeight w φ (n + 1)) (powerBranch φ (n + 1)) p q‖
        ≤ ((K ^ (n + 1) : ℕ) : ℝ) * W ^ (n + 1) * (R / R₁) ^ p * (τ / R) ^ q := h
      _ = (((K ^ (n + 1) : ℕ) : ℝ) * W ^ (n + 1) * (τ / R) ^ q)
            * (R / R₁) ^ p := by ring
  have hC : (0 : ℝ) ≤ ((K ^ (n + 1) : ℕ) : ℝ) * W ^ (n + 1) * (τ / R) ^ q := by
    positivity
  -- assemble
  show (R : ℂ) ^ m • (cauchyPowerSeries _ c R₁ m fun _ => 1) = _
  rw [show (fun z => ∑ i : Fin (K ^ (n + 2)), powerWeight w φ (n + 2) i z
        * ((powerBranch φ (n + 2) i z - c) / (R : ℂ)) ^ q)
      = fun z => ∑ k : Fin K, w k z * H (φ k z) from
    funext fun z => powerF_succ w φ (n + 1) q z]
  exact coeff_comp hR hRR hτ0 hτR hW hwc hφc hw' hφ' hC hb hH m

/-- **A⁽ⁿ⁾ = Aⁿ**: the coefficient matrix of the `(n+1)`-word system is the
`(n+1)`-st matrix power of the base transfer matrix. -/
theorem transferMatrix_pow (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hw : ∀ k, ∀ z ∈ Metric.closedBall c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (hwd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (w k) z)
    (hφd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (φ k) z)
    (n : ℕ) :
    transferMatrix c R R₁ (K ^ (n + 1))
        (powerWeight w φ (n + 1)) (powerBranch φ (n + 1))
      = matPowPos (transferMatrix c R R₁ K w φ) n := by
  induction n with
  | zero => exact transferMatrix_power_one
  | succ n ih =>
    rw [show matPowPos (transferMatrix c R R₁ K w φ) (n + 1)
        = matMul (transferMatrix c R R₁ K w φ)
            (matPowPos (transferMatrix c R R₁ K w φ) n) from rfl,
      ← ih]
    exact transferMatrix_power_succ hR hRR hτ0 hτR hW hw hφ hwd hφd n

/-! ### THE CAPSTONE: traces of honest matrix powers -/

/-- **The trace of the matrix power is the periodic-orbit sum**: combining
`transferMatrix_pow` with r191's `trace_pow_eq_residues`,

`Σ'_m (Aⁿ⁺¹)[m,m] = Σ_{|α|=n+1} W_α(x_α)/(1 − Φ_α'(x_α))`. -/
theorem trace_matPow_eq_residues (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hw : ∀ k, ∀ z ∈ Metric.closedBall c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (hwd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (w k) z)
    (hφd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (φ k) z)
    (n : ℕ)
    {x : Fin (K ^ (n + 1)) → ℂ} (hx : ∀ i, x i ∈ Metric.ball c R₁)
    {g : Fin (K ^ (n + 1)) → ℂ → ℂ}
    (hfactor : ∀ i, ∀ z ∈ Metric.closedBall c R₁,
      z - powerBranch φ (n + 1) i z = (z - x i) * g i z)
    (hgd : ∀ i, DiffContOnCl ℂ (g i) (Metric.ball c R₁))
    (hg0 : ∀ i, ∀ z ∈ Metric.closedBall c R₁, g i z ≠ 0) :
    (∑' m : ℕ, matPowPos (transferMatrix c R R₁ K w φ) n m m)
      = ∑ i : Fin (K ^ (n + 1)), powerWeight w φ (n + 1) i (x i)
          / (1 - deriv (powerBranch φ (n + 1) i) (x i)) := by
  rw [← transferMatrix_pow hR hRR hτ0 hτR hW hw hφ hwd hφd n]
  exact trace_pow_eq_residues hR hRR hτ0 hτR hW hw hφ hwd hφd
    (Nat.succ_pos n) hx hfactor hgd hg0

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.coeff_comp
#print axioms PrincipiaTractalis.HilbertSchmidtL2.hasSum_transferMatrix_series
#print axioms PrincipiaTractalis.HilbertSchmidtL2.transferMatrix_pow
#print axioms PrincipiaTractalis.HilbertSchmidtL2.trace_matPow_eq_residues
