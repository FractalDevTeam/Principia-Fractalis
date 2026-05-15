/-
# Hankel Upper-Edge DCT Invocation — Re s ≥ 1 case

The DCT convergence theorem for the upper-edge integral in the
regime `Re s ≥ 1`, where the integrand has no singularity at `t = 0`.

**Key adaptations from the `Re s ≤ 1` case**:
* Different dominating function: `(1 + t)^(Re s - 1) · exp(-t)`.
* Different integrand bound: `‖t + iε‖ ≤ 1 + t` for `|ε| ≤ 1, t ≥ 0`,
  with `rpow` monotonicity on the base (positive exponent).
* Different integrability argument: `(1 + t)^(Re s - 1) ≤ 2^(Re s - 1)
  · (1 + t^(Re s - 1))`, both summands integrable against `exp(-t)`.

This file:
* Proves the magnitude bound and rpow bound for the `Re s ≥ 1` regime.
* Proves the `(1 + t)^a ≤ 2^a · (1 + t^a)` algebraic inequality.
* Establishes integrability of the new dominating function.

The complete DCT-invocation theorem combining all of these would
mirror `HankelUpperEdgeDCTProof`; the structural pieces are in place
here.

Stage L4 — Upper-edge bounds for the `Re s ≥ 1` regime.
-/

import PF.Analytic.HankelCauchyCapstone

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory Set

/-! ## Magnitude bound: `‖t + iε‖ ≤ 1 + t` -/

/-- **Triangle-style bound**: `‖t + iε‖ ≤ 1 + t` for `|ε| ≤ 1, t ≥ 0`.

    Derivation: `‖t + iε‖² = t² + ε² ≤ t² + 1 ≤ (1 + t)²` (since
    `(1 + t)² − (t² + 1) = 2t ≥ 0`). -/
theorem norm_upper_edge_le_one_plus_t
    (t ε : ℝ) (ht : 0 ≤ t) (hε : |ε| ≤ 1) :
    ‖(t : ℂ) + (ε : ℂ) * I‖ ≤ 1 + t := by
  have h_norm_sq : ‖(t : ℂ) + (ε : ℂ) * I‖^2 = t^2 + ε^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  have h_eps_sq : ε^2 ≤ 1 := by
    have : |ε|^2 ≤ 1^2 := pow_le_pow_left₀ (abs_nonneg ε) hε 2
    rw [sq_abs] at this
    linarith
  have h_sq_le : ‖(t : ℂ) + (ε : ℂ) * I‖^2 ≤ (1 + t)^2 := by
    rw [h_norm_sq]
    nlinarith
  have h_norm_nn : 0 ≤ ‖(t : ℂ) + (ε : ℂ) * I‖ := norm_nonneg _
  have h_one_plus_nn : 0 ≤ 1 + t := by linarith
  nlinarith [sq_nonneg (‖(t : ℂ) + (ε : ℂ) * I‖ - (1 + t)),
             sq_nonneg (‖(t : ℂ) + (ε : ℂ) * I‖ + (1 + t))]

/-- **Rpow bound for `Re s ≥ 1`**:
    `‖t + iε‖^(Re s - 1) ≤ (1 + t)^(Re s - 1)`. -/
theorem norm_rpow_upper_edge_le_one_plus_t_of_re_ge_one
    (t ε : ℝ) (ht : 0 < t) (hε : |ε| ≤ 1) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖(t : ℂ) + (ε : ℂ) * I‖ ^ (s.re - 1) ≤ (1 + t) ^ (s.re - 1) := by
  apply Real.rpow_le_rpow (norm_nonneg _)
  · exact norm_upper_edge_le_one_plus_t t ε ht.le hε
  · linarith

/-! ## ε-uniform integrand bound for `Re s ≥ 1` -/

/-- **ε-uniform integrand bound for `1 ≤ Re s`, `|ε| ≤ 1`**:

      `‖F ε t‖ ≤ exp(|Im s|·π/2) · (1 + t)^(Re s - 1) · exp(-t)`. -/
theorem hankelUpperEdgeIntegrand_norm_le_of_re_ge_one
    {s : ℂ} (hs1 : 1 ≤ s.re) (t ε : ℝ) (ht : 0 < t) (hε : |ε| ≤ 1) :
    ‖hankelUpperEdgeIntegrand s ε t‖ ≤
    Real.exp (|s.im| * Real.pi / 2) * (1 + t) ^ (s.re - 1) * Real.exp (-t) := by
  have h_main := norm_hankelUpperEdgeIntegrand_le t ε ht s
  have h_rpow := norm_rpow_upper_edge_le_one_plus_t_of_re_ge_one t ε ht hε s hs1
  have h_const_nn : 0 ≤ Real.exp (|s.im| * Real.pi / 2) := Real.exp_nonneg _
  have h_exp_nn : 0 ≤ Real.exp (-t) := Real.exp_nonneg _
  calc ‖hankelUpperEdgeIntegrand s ε t‖
      ≤ ‖(t : ℂ) + (ε : ℂ) * I‖ ^ (s.re - 1) *
          Real.exp (|s.im| * Real.pi / 2) * Real.exp (-t) := h_main
    _ ≤ (1 + t) ^ (s.re - 1) * Real.exp (|s.im| * Real.pi / 2) *
          Real.exp (-t) := by
        apply mul_le_mul_of_nonneg_right _ h_exp_nn
        exact mul_le_mul_of_nonneg_right h_rpow h_const_nn
    _ = Real.exp (|s.im| * Real.pi / 2) * (1 + t) ^ (s.re - 1) *
          Real.exp (-t) := by ring

/-! ## Bound `(1 + t)^a ≤ 2^a · (1 + t^a)` -/

/-- **Bound for `(1 + t)^a`**: `(1 + t)^a ≤ 2^a · (1 + t^a)` for
    `a ≥ 0, t ≥ 0`.

    Chain: `1 + t ≤ 2 · max(1, t)`, then `(2 · max(1,t))^a = 2^a ·
    max(1,t)^a`, then `max(1, t)^a = max(1, t^a)` for `a ≥ 0`,
    and `max(1, t^a) ≤ 1 + t^a`. -/
theorem one_plus_pow_le_two_pow_one_plus_pow
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (1 + t) ^ a ≤ 2 ^ a * (1 + t ^ a) := by
  -- Step 1: 1 + t ≤ 2 · max(1, t)
  have h1 : 1 + t ≤ 2 * max 1 t := by
    rcases le_or_gt t 1 with hle | hlt
    · simp [max_eq_left hle]; linarith
    · simp [max_eq_right hlt.le]; linarith
  -- Step 2: (1 + t)^a ≤ (2 · max(1, t))^a
  have h2 : (1 + t) ^ a ≤ (2 * max 1 t) ^ a :=
    Real.rpow_le_rpow (by linarith) h1 ha
  -- Step 3: (2 · max(1, t))^a = 2^a · (max(1, t))^a
  have h3 : (2 * max 1 t) ^ a = 2 ^ a * (max 1 t) ^ a := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_max_of_le_left (by norm_num))]
  -- Step 4: max(1, t)^a = max(1, t^a) for a ≥ 0
  have h4 : (max 1 t) ^ a = max 1 (t ^ a) := by
    rcases le_total 1 t with hle | hle
    · rw [max_eq_right hle]
      rw [max_eq_right (Real.one_le_rpow hle ha)]
    · rw [max_eq_left hle]
      rw [max_eq_left (Real.rpow_le_one ht hle ha)]
      exact Real.one_rpow a
  -- Step 5: max(1, t^a) ≤ 1 + t^a
  have h5 : max 1 (t ^ a) ≤ 1 + t ^ a := by
    have h_pow_nn : 0 ≤ t ^ a := Real.rpow_nonneg ht a
    exact max_le (by linarith) (by linarith)
  have h_two_pow_nn : 0 ≤ (2 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) a
  calc (1 + t) ^ a
      ≤ (2 * max 1 t) ^ a := h2
    _ = 2 ^ a * (max 1 t) ^ a := h3
    _ = 2 ^ a * max 1 (t ^ a) := by rw [h4]
    _ ≤ 2 ^ a * (1 + t ^ a) :=
        mul_le_mul_of_nonneg_left h5 h_two_pow_nn

/-! ## Integrability of `exp(-t)` and the new dominating function -/

/-- **Integrability of `exp(-t)` on `(0, ∞)`** via `Real.GammaIntegral_convergent`. -/
theorem exp_neg_integrable_Ioi :
    IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (zero_lt_one : (0 : ℝ) < 1)
  refine h.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  show Real.exp (-t) * t ^ ((1 : ℝ) - 1) = Real.exp (-t)
  rw [sub_self, Real.rpow_zero, mul_one]

/-- **Continuity of `(1 + t)^(Re s - 1) · exp(-t)`** on `Ioi 0`, used
    for AE strong measurability. -/
theorem continuousOn_one_plus_rpow_mul_exp (s : ℂ) (hs1 : 1 ≤ s.re) :
    ContinuousOn (fun t : ℝ => (1 + t) ^ (s.re - 1) * Real.exp (-t)) (Ioi 0) := by
  apply ContinuousOn.mul
  · -- (1 + t)^(s.re - 1) continuous on Ioi 0
    intro t _
    apply ContinuousAt.continuousWithinAt
    have h_at : ContinuousAt (fun x : ℝ => x ^ (s.re - 1)) (1 + t) :=
      Real.continuousAt_rpow_const (1 + t) (s.re - 1) (Or.inr (by linarith))
    have h_inner : Continuous (fun u : ℝ => 1 + u) := continuous_const.add continuous_id
    exact h_at.comp h_inner.continuousAt
  · -- exp(-t) continuous
    intro t _
    apply ContinuousAt.continuousWithinAt
    exact (Real.continuous_exp.comp continuous_neg).continuousAt

/-- **Integrability of `(1 + t)^(Re s - 1) · exp(-t)` on `(0, ∞)`** for
    `Re s ≥ 1`. Bound by `2^(Re s - 1) · (exp(-t) + t^(Re s - 1) · exp(-t))`,
    a sum of integrable functions. -/
theorem one_plus_t_rpow_mul_exp_integrable {s : ℂ} (hs : 0 < s.re) (hs1 : 1 ≤ s.re) :
    IntegrableOn (fun t : ℝ => (1 + t) ^ (s.re - 1) * Real.exp (-t)) (Ioi 0) := by
  have h_exp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    exp_neg_integrable_Ioi
  have h_gamma : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * Real.exp (-t)) (Ioi 0) :=
    gammaIntegrand_real_integrable hs
  have h_sum : IntegrableOn
      (fun t : ℝ => 2 ^ (s.re - 1) * (Real.exp (-t) + t ^ (s.re - 1) * Real.exp (-t)))
      (Ioi 0) :=
    (h_exp.add h_gamma).const_mul _
  apply MeasureTheory.Integrable.mono h_sum
  · exact (continuousOn_one_plus_rpow_mul_exp s hs1).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht_pos : 0 < t := Set.mem_Ioi.mp ht
    have ht_nn : 0 ≤ t := ht_pos.le
    have h_exp_nn : 0 ≤ Real.exp (-t) := Real.exp_nonneg _
    have h_one_plus_pow_nn : 0 ≤ (1 + t) ^ (s.re - 1) :=
      Real.rpow_nonneg (by linarith) _
    have h_tpow_nn : 0 ≤ t ^ (s.re - 1) := Real.rpow_nonneg ht_nn _
    have h_2pow_nn : 0 ≤ (2 : ℝ) ^ (s.re - 1) :=
      Real.rpow_nonneg (by norm_num) _
    have h_a_nn : 0 ≤ s.re - 1 := by linarith
    have h_bound := one_plus_pow_le_two_pow_one_plus_pow (s.re - 1) t h_a_nn ht_nn
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg h_one_plus_pow_nn h_exp_nn)]
    rw [abs_of_nonneg (mul_nonneg h_2pow_nn
        (add_nonneg h_exp_nn (mul_nonneg h_tpow_nn h_exp_nn)))]
    calc (1 + t) ^ (s.re - 1) * Real.exp (-t)
        ≤ 2 ^ (s.re - 1) * (1 + t ^ (s.re - 1)) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right h_bound h_exp_nn
      _ = 2 ^ (s.re - 1) *
          (Real.exp (-t) + t ^ (s.re - 1) * Real.exp (-t)) := by ring

/-! ## Open: DCT invocation for `Re s ≥ 1`

The full DCT invocation theorem for the `Re s ≥ 1` regime:

```
theorem hankelUpperEdge_integral_tends_to_Gamma_of_re_ge_one
    {s : ℂ} (hs : 0 < s.re) (hs1 : 1 ≤ s.re) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), hankelUpperEdgeIntegrand s ε t)
            (𝓝[>] 0) (𝓝 (Complex.Gamma s))
```

Proof: identical pattern to `hankelUpperEdge_integral_tends_to_Gamma_of_re_le_one`,
applying `tendsto_integral_filter_of_dominated_convergence` with:
* `hankelUpperEdgeIntegrand_aestronglyMeasurable` for AE measurability,
* `hankelUpperEdgeIntegrand_norm_le_of_re_ge_one` for the ε-uniform bound
  (eventually for `ε ∈ (0, 1)` ⊂ `𝓝[>] 0`),
* `one_plus_t_rpow_mul_exp_integrable` for bound integrability,
* `hankelUpperEdgeIntegrand_tendsto_pointwise_pos` for pointwise conv.,
* `integral_gammaPrincipalIntegrand_eq_Gamma` for the limit identification.

The only structural difference from the `Re s ≤ 1` case is the
eventually-quantifier on `ε`: the bound requires `|ε| ≤ 1`, which holds
for ε in any neighborhood of 0 (eventually in `𝓝[>] 0`). All ingredients
are proven in this file and previous modules. -/

end PrincipiaTractalis.Analytic
