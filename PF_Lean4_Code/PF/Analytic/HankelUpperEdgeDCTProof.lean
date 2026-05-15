/-
# Hankel Upper-Edge DCT Invocation

The final DCT-invocation step for the upper-edge integral. Combines
all previously-proven ingredients into the convergence

  `∫ t in Ioi 0, hankelUpperEdgeIntegrand s ε t → Γ(s)`  as `ε → 0⁺`

for `0 < Re s ≤ 1`.

**Ingredients** (all proven axiom-clean in previous files):
1. Pointwise convergence (`HankelUpperEdgeDCT`).
2. ε-uniform integrand bound (`HankelUpperEdgeIntegralLimit`).
3. Integrability of bound (`HankelIntegrability`).
4. AE strong measurability of each `F ε` (proved here via
   `ContinuousOn.aestronglyMeasurable`).
5. Limit-integral identification with `Γ(s)`
   (`HankelUpperEdgeIntegralLimit`).

The DCT itself: `tendsto_integral_filter_of_dominated_convergence`
applied to the filter `𝓝[>] 0` (countably generated in ℝ).

Stage L4 — Upper-edge DCT closure.
-/

import PF.Analytic.HankelUpperEdgeIntegralLimit

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory Set

/-! ## AE strong measurability of the integrand -/

/-- **Continuity of the upper-edge integrand** on `Ioi 0`.

    The integrand `(t + iε)^(s-1) · exp(-(t + iε))` is continuous in
    `t` on `Ioi 0`: for `t > 0`, `(t + iε) ∈ slitPlane` (since
    `Re(t + iε) = t > 0`), so `cpow` is continuous there; `exp` is
    continuous everywhere; the product is continuous. -/
theorem hankelUpperEdgeIntegrand_continuousOn (s : ℂ) (ε : ℝ) :
    ContinuousOn (fun t : ℝ => hankelUpperEdgeIntegrand s ε t) (Ioi 0) := by
  unfold hankelUpperEdgeIntegrand
  have h_z_cont : Continuous (fun t : ℝ => (t : ℂ) + (ε : ℂ) * I) :=
    Complex.continuous_ofReal.add continuous_const
  apply ContinuousOn.mul
  · -- (· ^ (s - 1)) ∘ z is continuous on Ioi 0
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have h_z_slit : (t : ℂ) + (ε : ℂ) * I ∈ Complex.slitPlane := by
      show 0 < ((t : ℂ) + (ε : ℂ) * I).re ∨ ((t : ℂ) + (ε : ℂ) * I).im ≠ 0
      left
      simp
      exact Set.mem_Ioi.mp ht
    -- Use Filter.Tendsto.cpow (same API as HankelUpperEdgeDCT)
    have h_z_tendsto : Tendsto (fun u : ℝ => (u : ℂ) + (ε : ℂ) * I) (𝓝 t)
                                (𝓝 ((t : ℂ) + (ε : ℂ) * I)) :=
      h_z_cont.continuousAt
    exact h_z_tendsto.cpow tendsto_const_nhds h_z_slit
  · -- exp(-z) continuous everywhere
    intro t _
    apply ContinuousAt.continuousWithinAt
    have h_neg_tendsto : Tendsto (fun u : ℝ => -((u : ℂ) + (ε : ℂ) * I)) (𝓝 t)
                                  (𝓝 (-((t : ℂ) + (ε : ℂ) * I))) :=
      h_z_cont.neg.continuousAt
    exact (Complex.continuous_exp.tendsto _).comp h_neg_tendsto

/-- **AE strong measurability** on `volume.restrict (Ioi 0)`. -/
theorem hankelUpperEdgeIntegrand_aestronglyMeasurable (s : ℂ) (ε : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => hankelUpperEdgeIntegrand s ε t)
                          (volume.restrict (Ioi 0)) :=
  (hankelUpperEdgeIntegrand_continuousOn s ε).aestronglyMeasurable measurableSet_Ioi

/-! ## The DCT-application theorem (`0 < Re s ≤ 1` case) -/

/-- **Upper-edge integral converges to `Γ(s)`** for `0 < Re s ≤ 1`.

    Applies `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
    with the filter `𝓝[>] 0` (countably generated in ℝ), using:
    * `hankelUpperEdgeIntegrand_aestronglyMeasurable` for AE measurability,
    * `hankelUpperEdgeIntegrand_norm_le_of_re_le_one` for ε-uniform bound,
    * `upper_edge_dominating_integrable` for bound integrability,
    * `hankelUpperEdgeIntegrand_tendsto_pointwise_pos` for pointwise conv.

    Then `integral_gammaPrincipalIntegrand_eq_Gamma` identifies the
    limit integral with `Γ(s)`. -/
theorem hankelUpperEdge_integral_tends_to_Gamma_of_re_le_one
    {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), hankelUpperEdgeIntegrand s ε t)
            (𝓝[>] 0) (𝓝 (Complex.Gamma s)) := by
  -- Identify Γ(s) with the integral of the principal integrand
  rw [← integral_gammaPrincipalIntegrand_eq_Gamma hs]
  -- Define the bound
  set bound : ℝ → ℝ := fun t =>
    Real.exp (|s.im| * Real.pi / 2) * t ^ (s.re - 1) * Real.exp (-t)
  -- Apply the DCT
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    (Filter.Eventually.of_forall (fun _ =>
      hankelUpperEdgeIntegrand_aestronglyMeasurable s _))
    ?_ ?_ ?_
  · -- ε-uniform bound
    refine Filter.Eventually.of_forall (fun ε => ?_)
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact hankelUpperEdgeIntegrand_norm_le_of_re_le_one hs1 t ε
      (Set.mem_Ioi.mp ht)
  · -- Integrability of bound
    have h := upper_edge_dominating_integrable hs
    -- h : IntegrableOn (fun t => exp(|Im s|·π/2) · (t^(Re s - 1) · exp(-t))) (Ioi 0)
    -- our bound: exp(|Im s|·π/2) · t^(Re s - 1) · exp(-t) — same up to associativity
    refine h.congr ?_
    filter_upwards with t
    show Real.exp (|s.im| * Real.pi / 2) * (t ^ (s.re - 1) * Real.exp (-t)) =
         bound t
    show Real.exp (|s.im| * Real.pi / 2) * (t ^ (s.re - 1) * Real.exp (-t)) =
         Real.exp (|s.im| * Real.pi / 2) * t ^ (s.re - 1) * Real.exp (-t)
    ring
  · -- Pointwise convergence
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact hankelUpperEdgeIntegrand_tendsto_pointwise_pos (Set.mem_Ioi.mp ht)

end PrincipiaTractalis.Analytic
