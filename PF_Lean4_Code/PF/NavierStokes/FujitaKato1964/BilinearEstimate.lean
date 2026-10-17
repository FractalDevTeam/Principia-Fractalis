/-
# Fujita-Kato 1964 — Bilinear Estimate (step 3 of 4)

**Rio's NS carrier migration, step 3**: the load-bearing analytic lemma.
With the Banach bilinear (`BanachBilinear.lean`, step 2) and operator
shells (`BanachOperatorShell.lean`, step 2b) in place, we derive the
pointwise-in-time norm bound

    `‖B(u, v)(t)‖ ≤ C · U · V · |t|`

where `U = sup_s ‖u(s)‖`, `V = sup_s ‖v(s)‖`, and `C` is the Ḣ^{1/2}
product-estimate constant for the convective derivative. This bound is
CONDITIONAL on three hypotheses — the standing data of the Fujita-Kato
construction — made explicit here as named Prop-level predicates:

* `IsContractiveHeatSemigroup heatSG` — `∀ s, ‖heatSG s‖ ≤ 1`. True for
  the genuine `e^{sΔ}` on L² (Plancherel + Fourier multiplier bounded by
  1). TRIVIAL instance `CLM.id` satisfies this with equality.

* `IsContractiveLerayProjection leray` — `‖leray‖ ≤ 1`. True for the
  genuine Leray projection (orthogonal projection on L²). TRIVIAL
  instance `CLM.id` satisfies this with equality.

* `HasProductEstimate conv C` — `‖conv u v‖ ≤ C · ‖u‖ · ‖v‖`. This is
  the **KEY ANALYTIC HYPOTHESIS** — the Ḣ^{1/2} product estimate. For
  the genuine convective derivative `(u·∇)v`, this is the content of the
  Fujita-Kato 1964 paper's main technical lemma. For the step-2b trivial
  realization `conv = 0`, trivially satisfied with any `C ≥ 0`.

### What this file proves

* `mildBilinear_integrand_norm_le` — pointwise integrand bound
  `‖heatSG(t−s)(leray(conv(u s)(v s)))‖ ≤ C · ‖u s‖ · ‖v s‖`.

* `mildBilinear_norm_le_of_uniform_bounds` — **the step-3 theorem**:
  for `u, v : TimeFieldR3C_Banach` with uniform bounds `‖u s‖ ≤ U` and
  `‖v s‖ ≤ V`, the mild bilinear satisfies
  `‖mildBilinear heatSG leray conv u v t‖ ≤ C · U · V · |t|`.

* `banachMildBilinear_norm_le_of_uniform_bounds` — specialization to the
  concrete step-2b operators. With the trivial realizations, `C = 0`, so
  the bound degenerates to `0`, consistent with `banachMildBilinear ≡ 0`.
  The bound becomes GENUINE Fujita-Kato content when step-2c (density
  extension of the real operators) and the actual Ḣ^{1/2} product
  estimate derivation land.

### Three-axiom bar

Every declaration kernel-clean `[propext, Classical.choice, Quot.sound]`.
No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import PF.NavierStokes.FujitaKato1964.BanachBilinearCapstone

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964

open MeasureTheory

noncomputable section

/-! ## §1 — Hypotheses: operator norms + product estimate. -/

/-- **Heat-semigroup contractivity**: `∀ s, ‖e^{sΔ}‖ ≤ 1`. True for the
genuine `e^{sΔ}` on `L²(ℝ³, ℂ³)` via Plancherel (Fourier multiplier
`e^{−s|ξ|²}` is bounded by 1 on `s ≥ 0`). -/
def IsContractiveHeatSemigroup
    (heatSG : ℝ → VectorBanach3C →L[ℂ] VectorBanach3C) : Prop :=
  ∀ s : ℝ, ‖heatSG s‖ ≤ 1

/-- **Leray-projection contractivity**: `‖ℙ‖ ≤ 1`. True for the genuine
Leray projection (orthogonal projection on `L²`). -/
def IsContractiveLerayProjection
    (leray : VectorBanach3C →L[ℂ] VectorBanach3C) : Prop :=
  ‖leray‖ ≤ 1

/-- **Ḣ^{1/2} product estimate** — the LOAD-BEARING analytic input to
Fujita-Kato 1964. For the genuine convective derivative `(u·∇)v`
viewed as a bilinear map `Ḣ^{1/2} × Ḣ^{1/2} → Ḣ^{−1/2}`, this is the
classical bound

    `‖(u·∇)v‖_{Ḣ^{−1/2}} ≤ C · ‖u‖_{Ḣ^{1/2}} · ‖v‖_{Ḣ^{1/2}}`.

(On the current L²-based carrier, equivalently `‖conv u v‖ ≤ C ‖u‖ ‖v‖`
after absorbing the Sobolev-order mismatch into the heat regularization.) -/
def HasProductEstimate
    (conv : VectorBanach3C → VectorBanach3C → VectorBanach3C) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ u v : VectorBanach3C, ‖conv u v‖ ≤ C * ‖u‖ * ‖v‖

/-! ## §2 — Pointwise integrand bound. -/

/-- **Pointwise bound on the bilinear integrand**:
`‖heatSG(t−s)(leray(conv(u s)(v s)))‖ ≤ C · ‖u s‖ · ‖v s‖`.
Chain: operator norm of `heatSG` (contractive), operator norm of
`leray` (contractive), product estimate on `conv`. -/
lemma mildBilinear_integrand_norm_le
    {heatSG : ℝ → VectorBanach3C →L[ℂ] VectorBanach3C}
    {leray : VectorBanach3C →L[ℂ] VectorBanach3C}
    {conv : VectorBanach3C → VectorBanach3C → VectorBanach3C}
    {C : ℝ}
    (hHeat : IsContractiveHeatSemigroup heatSG)
    (hLeray : IsContractiveLerayProjection leray)
    (hConv : HasProductEstimate conv C)
    (u v : TimeFieldR3C_Banach) (t s : ℝ) :
    ‖heatSG (t - s) (leray (conv (u s) (v s)))‖ ≤ C * ‖u s‖ * ‖v s‖ := by
  calc ‖heatSG (t - s) (leray (conv (u s) (v s)))‖
      ≤ ‖heatSG (t - s)‖ * ‖leray (conv (u s) (v s))‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖leray (conv (u s) (v s))‖ :=
          mul_le_mul_of_nonneg_right (hHeat (t - s)) (norm_nonneg _)
    _ = ‖leray (conv (u s) (v s))‖ := one_mul _
    _ ≤ ‖leray‖ * ‖conv (u s) (v s)‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖conv (u s) (v s)‖ :=
          mul_le_mul_of_nonneg_right hLeray (norm_nonneg _)
    _ = ‖conv (u s) (v s)‖ := one_mul _
    _ ≤ C * ‖u s‖ * ‖v s‖ := hConv.2 (u s) (v s)

/-! ## §3 — The main bilinear estimate. -/

/-- **★ Step-3 bilinear estimate ★**: for `u, v : TimeFieldR3C_Banach`
with time-uniform bounds `‖u s‖ ≤ U` and `‖v s‖ ≤ V`, the mild bilinear
satisfies

    `‖mildBilinear heatSG leray conv u v t‖ ≤ C · U · V · |t|`

for all `t : ℝ`. This is the Fujita-Kato bilinear estimate at the shell
level — the "load-bearing analytic lemma" of the construction, modulo the
Ḣ^{1/2} product estimate hypothesis.

Proof: pointwise bound (`mildBilinear_integrand_norm_le`) + composition
with the uniform bounds + `intervalIntegral.norm_integral_le_of_norm_le_const`
on the Bochner interval integral. -/
theorem mildBilinear_norm_le_of_uniform_bounds
    {heatSG : ℝ → VectorBanach3C →L[ℂ] VectorBanach3C}
    {leray : VectorBanach3C →L[ℂ] VectorBanach3C}
    {conv : VectorBanach3C → VectorBanach3C → VectorBanach3C}
    {C : ℝ}
    (hHeat : IsContractiveHeatSemigroup heatSG)
    (hLeray : IsContractiveLerayProjection leray)
    (hConv : HasProductEstimate conv C)
    (u v : TimeFieldR3C_Banach) {U V : ℝ}
    (hU_nn : 0 ≤ U) (hV_nn : 0 ≤ V)
    (hU : ∀ s, ‖u s‖ ≤ U) (hV : ∀ s, ‖v s‖ ≤ V)
    (t : ℝ) :
    ‖mildBilinear heatSG leray conv u v t‖ ≤ C * U * V * |t| := by
  have h_pointwise : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖heatSG (t - s) (leray (conv (u s) (v s)))‖ ≤ C * U * V := by
    intro s _
    calc ‖heatSG (t - s) (leray (conv (u s) (v s)))‖
        ≤ C * ‖u s‖ * ‖v s‖ := mildBilinear_integrand_norm_le hHeat hLeray hConv u v t s
      _ ≤ C * U * V := by
          have hC_nn := hConv.1
          have h1 : C * ‖u s‖ ≤ C * U := mul_le_mul_of_nonneg_left (hU s) hC_nn
          have h2 : 0 ≤ C * U := mul_nonneg hC_nn hU_nn
          calc C * ‖u s‖ * ‖v s‖
              ≤ C * U * ‖v s‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ ≤ C * U * V := mul_le_mul_of_nonneg_left (hV s) h2
  calc ‖mildBilinear heatSG leray conv u v t‖
      = ‖∫ s in (0 : ℝ)..t, heatSG (t - s) (leray (conv (u s) (v s)))‖ := rfl
    _ ≤ C * U * V * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_pointwise
    _ = C * U * V * |t| := by rw [sub_zero]

/-! ## §4 — Instantiation at the concrete step-2b operators. -/

/-- The concrete `banachHeatSemigroup = CLM.id` is contractive (operator
norm = 1). Satisfies the hypothesis trivially with equality for all `s`. -/
theorem banachHeatSemigroup_isContractive :
    IsContractiveHeatSemigroup banachHeatSemigroup := by
  intro s
  unfold banachHeatSemigroup
  exact (ContinuousLinearMap.norm_id_le)

/-- The concrete `banachLerayProjection = CLM.id` is contractive. -/
theorem banachLerayProjection_isContractive :
    IsContractiveLerayProjection banachLerayProjection := by
  unfold banachLerayProjection IsContractiveLerayProjection
  exact ContinuousLinearMap.norm_id_le

/-- The concrete `banachConvectiveDerivative = 0` satisfies the product
estimate with `C = 0`. (Trivially — both sides are 0.) -/
theorem banachConvectiveDerivative_hasProductEstimate :
    HasProductEstimate banachConvectiveDerivative 0 := by
  refine ⟨le_refl 0, ?_⟩
  intros u v
  unfold banachConvectiveDerivative
  simp

/-- **Specialization of the bilinear estimate to the concrete step-2b
operators.** With the trivial realizations, `C = 0`, so the bound is
`0 · U · V · |t| = 0`. Consistent with `banachMildBilinear ≡ 0`.

Becomes GENUINE Fujita-Kato content when step 2c (density extension of
`vectorHeatEvolveFreq`, `lerayProjectFreq`, `convectiveComponent` from
`VectorSchwartz3C` to `VectorBanach3C`) + the actual Ḣ^{1/2} product
estimate derivation land. The theorem statement does not change. -/
theorem banachMildBilinear_norm_le_of_uniform_bounds
    (u v : TimeFieldR3C_Banach) {U V : ℝ}
    (hU_nn : 0 ≤ U) (hV_nn : 0 ≤ V)
    (hU : ∀ s, ‖u s‖ ≤ U) (hV : ∀ s, ‖v s‖ ≤ V)
    (t : ℝ) :
    ‖banachMildBilinear u v t‖ ≤ 0 * U * V * |t| :=
  mildBilinear_norm_le_of_uniform_bounds
    banachHeatSemigroup_isContractive
    banachLerayProjection_isContractive
    banachConvectiveDerivative_hasProductEstimate
    u v hU_nn hV_nn hU hV t

end

end PF.NavierStokes.FujitaKato1964

/-! ## §Axiom check -/
#print axioms PF.NavierStokes.FujitaKato1964.mildBilinear_integrand_norm_le
#print axioms PF.NavierStokes.FujitaKato1964.mildBilinear_norm_le_of_uniform_bounds
#print axioms PF.NavierStokes.FujitaKato1964.banachHeatSemigroup_isContractive
#print axioms PF.NavierStokes.FujitaKato1964.banachLerayProjection_isContractive
#print axioms PF.NavierStokes.FujitaKato1964.banachConvectiveDerivative_hasProductEstimate
#print axioms PF.NavierStokes.FujitaKato1964.banachMildBilinear_norm_le_of_uniform_bounds
