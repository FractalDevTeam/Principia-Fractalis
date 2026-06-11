/-
# Fujita-Kato 1964 — Leray Projector Contracts the Ḣ^{1/2} Seminorm (Frequency-Domain Image)

★ 2026-06-10 — Bridge result combining the Leray frequency-domain image
  shell (`LerayProjectorOperator.lean`, `LerayImageIsDivFree.lean`) with
  the vector Sobolev integrand integrability shell
  (`VectorSobolevIntegrandIntegrable.lean`).

This is one of the key ingredients of the Fujita-Kato 1964 contraction
argument: the Leray projector `P` is an *orthogonal* projector at the
frequency level, hence cannot grow the homogeneous vector Sobolev
`Ḣ^{1/2}` seminorm.

At the frequency-domain image layer (no Fourier inversion required),
the statement is

  `∫ ‖ξ‖ · ‖lerayProjectFreq u ξ‖²_{ℂ³} dξ ≤ ‖u‖²_{Ḣ^{1/2}}`     (★)

for any vector Schwartz `u`. The proof outline is:

  (1) Pointwise operator-norm bound on the complex Leray symbol:
      `‖lerayFourierSymbolC ξ w‖ ≤ ‖w‖` for every `ξ` and `w`.
      At `ξ = 0` the symbol is the identity, so equality holds. At
      `ξ ≠ 0` the symbol is an orthogonal projector onto the subspace
      perpendicular to `complexifyVec ξ`, so the Pythagorean identity
      gives `‖w‖² = ‖lerayFourierSymbolC ξ w‖² + ‖w_∥‖²` where `w_∥`
      is the projection onto the `complexifyVec ξ` line. Therefore
      `‖lerayFourierSymbolC ξ w‖² ≤ ‖w‖²`.

  (2) Pointwise integrand bound: from (1), squaring and multiplying
      by `‖ξ‖ ≥ 0` gives
      `‖ξ‖ · ‖lerayProjectFreq u ξ‖² ≤ ‖ξ‖ · ‖(F u) ξ‖² = vectorH12IntegrandSq u ξ`.

  (3) Integrating gives (★), using
      `MeasureTheory.integral_mono_of_nonneg` and the unconditional
      vector Schwartz integrability lemma
      `vectorH12IntegrandSq_integrable_general` from
      `VectorSobolevIntegrandIntegrable.lean`.

The substantive analytic content is (1) — the pointwise operator-norm
bound. The key non-trivial step is the Pythagorean decomposition

  `w = (w - λ • complexifyVec ξ) + λ • complexifyVec ξ`,

where `λ := ⟨complexifyVec ξ, w⟩ / ((‖ξ‖² : ℝ) : ℂ)`. The first
summand is `lerayFourierSymbolC ξ w` (by definition); the
perpendicularity `⟨complexifyVec ξ, lerayFourierSymbolC ξ w⟩ = 0` from
`LerayImageIsDivFree.lean` translates (via Hermitian conjugate symmetry
and linearity of the inner product) to
`⟨lerayFourierSymbolC ξ w, λ • complexifyVec ξ⟩ = 0`. The Pythagorean
theorem `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` then
gives the squared-norm identity, and dropping the non-negative
`‖λ • complexifyVec ξ‖²` summand yields the bound.

Scope: vector (`ℂ³`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.
Mechanical lift of the standard `‖P‖_{op} = 1` orthogonal-projector
bound to the integrated `Ḣ^{1/2}` seminorm. This is the form
Navier-Stokes consumes after complexification of the velocity field.

Bricks landed here:

  §1 — Pointwise operator-norm bound on the complex Leray symbol.
  §2 — Pointwise integrand bound.
  §3 — Integrated Sobolev contraction.
  §4 — Zero-input consequence.
  §5 — Capstone bundling §1-§4.
  §6 — `#print axioms` audit (kernel-only).

Axiom-free; depends only on `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.LerayImageIsDivFree
import PF.NavierStokes.FujitaKato1964.VectorSobolevIntegrandIntegrable

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.LerayContractsSobolev

open MeasureTheory SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 C3 VectorSchwartz3C vectorH12IntegrandSq vectorH12IntegrandSq_nonneg
   vectorH12IntegrandSq_zero vectorHomogeneousH12SeminormSq
   vectorHomogeneousH12SeminormSq_zero)
open PF.NavierStokes.FujitaKato1964.LerayProjectorOperator
  (complexifyVec lerayFourierSymbolC lerayProjectFreq
   lerayFourierSymbolC_zero_freq lerayFourierSymbolC_zero_field
   lerayProjectFreq_zero)
open PF.NavierStokes.FujitaKato1964.LerayImageIsDivFree
  (complexifyVec_inner_self lerayFourierSymbolC_inner_eq_zero)
open PF.NavierStokes.FujitaKato1964.VectorSobolevIntegrandIntegrable
  (vectorH12IntegrandSq_integrable_general)

/-! ## §1 — Pointwise operator-norm bound on the complex Leray symbol -/

/-- **Perpendicularity in the second slot:** for `ξ ≠ 0` and any `w`,

  `⟨lerayFourierSymbolC ξ w, complexifyVec ξ⟩_ℂ = 0`.

Hermitian-conjugate symmetric version of `lerayFourierSymbolC_inner_eq_zero`:
the first-slot vanishing transfers to the second slot via
`inner_conj_symm` and `starRingEnd_apply` on zero. Used in the
Pythagorean decomposition of §1's operator-norm bound. -/
theorem inner_lerayFourierSymbolC_complexifyVec_eq_zero
    (ξ : R3) (hξ : ξ ≠ 0) (w : C3) :
    inner ℂ (lerayFourierSymbolC ξ w) (complexifyVec ξ) = 0 := by
  have h := lerayFourierSymbolC_inner_eq_zero ξ hξ w
  -- `inner_conj_symm x y : ⟪y, x⟫† = ⟪x, y⟫`.
  -- With x := complexifyVec ξ, y := lerayFourierSymbolC ξ w:
  --   ⟪lerayFourierSymbolC ξ w, complexifyVec ξ⟫† = ⟪complexifyVec ξ, lerayFourierSymbolC ξ w⟫
  have hconj : (starRingEnd ℂ)
      (inner ℂ (lerayFourierSymbolC ξ w) (complexifyVec ξ))
        = inner ℂ (complexifyVec ξ) (lerayFourierSymbolC ξ w) :=
    inner_conj_symm (𝕜 := ℂ) (complexifyVec ξ) (lerayFourierSymbolC ξ w)
  -- From h: rhs of hconj is 0; therefore lhs (a star of our target) is 0,
  -- so target = 0 by injectivity of star.
  rw [h] at hconj
  -- hconj : (starRingEnd ℂ) (inner ℂ (lerayFourierSymbolC ξ w) (complexifyVec ξ)) = 0
  -- Apply starRingEnd ℂ to both sides; star is involutive on ℂ.
  have := congrArg (starRingEnd ℂ) hconj
  simpa using this

/-- **★ Pointwise operator-norm bound on the complex Leray symbol.**

For every frequency `ξ ∈ ℝ³` and every complex vector `w ∈ ℂ³`,

  `‖lerayFourierSymbolC ξ w‖ ≤ ‖w‖`.

This is the assertion that the Leray symbol is a contraction at every
frequency — equivalently, its operator norm is at most 1.

Proof.

  * `ξ = 0` branch: the symbol is the identity, so the bound holds
    with equality.

  * `ξ ≠ 0` branch: write the symbol-defining decomposition

      `w = (lerayFourierSymbolC ξ w) + λ • complexifyVec ξ`     (◇)

    where `λ := ⟨complexifyVec ξ, w⟩_ℂ / ((‖ξ‖² : ℝ) : ℂ)`. (This is
    just the definition of `lerayFourierSymbolC` solved for `w`.)
    The first summand is perpendicular to the second:

      `⟨lerayFourierSymbolC ξ w, λ • complexifyVec ξ⟩_ℂ
          = λ * ⟨lerayFourierSymbolC ξ w, complexifyVec ξ⟩_ℂ
          = λ * 0 = 0`

    using `inner_smul_right` plus the second-slot perpendicularity
    `inner_lerayFourierSymbolC_complexifyVec_eq_zero` above.

    The Pythagorean theorem
    `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` applied to
    (◇) then yields

      `‖w‖ * ‖w‖ = ‖lerayFourierSymbolC ξ w‖ * ‖lerayFourierSymbolC ξ w‖
                + ‖λ • complexifyVec ξ‖ * ‖λ • complexifyVec ξ‖`

    and dropping the non-negative second summand gives the squared
    bound. Converting `‖·‖ * ‖·‖` to `‖·‖^2` and applying
    `le_of_sq_le_sq` against `0 ≤ ‖w‖` finishes. -/
theorem norm_lerayFourierSymbolC_le
    (ξ : R3) (w : C3) :
    ‖lerayFourierSymbolC ξ w‖ ≤ ‖w‖ := by
  by_cases hξ : ξ = 0
  · -- ξ = 0 branch: identity
    rw [hξ, lerayFourierSymbolC_zero_freq]
  · -- ξ ≠ 0 branch: Pythagorean decomposition
    set v : C3 := lerayFourierSymbolC ξ w with hv
    set e : C3 := complexifyVec ξ with he
    set coeff : ℂ := inner ℂ e w / ((‖ξ‖ ^ 2 : ℝ) : ℂ) with hcoeff
    -- Step 1: decomposition w = v + coeff • e (just unfold the symbol)
    have hdecomp : w = v + coeff • e := by
      have hv_def : v = w - coeff • e := by
        show lerayFourierSymbolC ξ w = w - coeff • e
        unfold lerayFourierSymbolC
        rw [if_neg hξ]
      rw [hv_def]
      abel
    -- Step 2: perpendicularity ⟨v, coeff • e⟩ = 0
    have hperp_second_slot :
        inner ℂ v e = 0 :=
      inner_lerayFourierSymbolC_complexifyVec_eq_zero ξ hξ w
    have hperp : inner ℂ v (coeff • e) = 0 := by
      rw [inner_smul_right]
      rw [hperp_second_slot]
      ring
    -- Step 3: Pythagorean identity
    have hpyth :
        ‖v + coeff • e‖ * ‖v + coeff • e‖
          = ‖v‖ * ‖v‖ + ‖coeff • e‖ * ‖coeff • e‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v (coeff • e) hperp
    -- Step 4: squared-norm bound on v
    have hw_eq : w = v + coeff • e := hdecomp
    have hw_sq : ‖w‖ * ‖w‖ = ‖v‖ * ‖v‖ + ‖coeff • e‖ * ‖coeff • e‖ := by
      rw [hw_eq]; exact hpyth
    have hresidual_nn : 0 ≤ ‖coeff • e‖ * ‖coeff • e‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq_le : ‖v‖ * ‖v‖ ≤ ‖w‖ * ‖w‖ := by
      rw [hw_sq]; linarith
    -- Step 5: convert ‖·‖ * ‖·‖ to ‖·‖ ^ 2 and apply le_of_sq_le_sq
    have hsq_le' : ‖v‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      have h1 : ‖v‖ * ‖v‖ = ‖v‖ ^ 2 := by ring
      have h2 : ‖w‖ * ‖w‖ = ‖w‖ ^ 2 := by ring
      rw [h1, h2] at hsq_le
      exact hsq_le
    exact le_of_sq_le_sq hsq_le' (norm_nonneg _)

/-- **Zero-frequency identity:** `‖lerayFourierSymbolC 0 w‖ = ‖w‖`.
At zero frequency the symbol is the identity. -/
theorem norm_lerayFourierSymbolC_zero_freq (w : C3) :
    ‖lerayFourierSymbolC 0 w‖ = ‖w‖ := by
  rw [lerayFourierSymbolC_zero_freq]

/-! ## §2 — Pointwise integrand bound -/

/-- **Pointwise integrand of the Leray-projected homogeneous Ḣ^{1/2}
seminorm squared.**

For a vector Schwartz field `u`, frequency `ξ ∈ ℝ³`, the integrand is

  `‖ξ‖ · ‖lerayProjectFreq u ξ‖²_{ℂ³}`.

Integrating over `ξ ∈ ℝ³` gives the Leray-projected `Ḣ^{1/2}` seminorm
squared. -/
noncomputable def vectorH12IntegrandSqOfLeray
    (u : VectorSchwartz3C) (ξ : R3) : ℝ :=
  ‖ξ‖ * ‖lerayProjectFreq u ξ‖ ^ 2

/-- **The Leray-projected Sobolev integrand is pointwise non-negative.**
The factor `‖ξ‖` is non-negative and the squared norm `‖·‖²` is
non-negative. -/
theorem vectorH12IntegrandSqOfLeray_nonneg
    (u : VectorSchwartz3C) (ξ : R3) :
    0 ≤ vectorH12IntegrandSqOfLeray u ξ :=
  mul_nonneg (norm_nonneg _) (sq_nonneg _)

/-- **★ Pointwise contraction of the Leray-projected Sobolev integrand.**

From §1's operator-norm bound `‖lerayFourierSymbolC ξ w‖ ≤ ‖w‖`
applied to `w := (F u) ξ`, squaring and multiplying by `‖ξ‖ ≥ 0`
gives

  `‖ξ‖ · ‖lerayProjectFreq u ξ‖² ≤ ‖ξ‖ · ‖(F u) ξ‖² = vectorH12IntegrandSq u ξ`.

This is the pointwise form of the Leray-projector `Ḣ^{1/2}` contraction
estimate, before any integration. -/
theorem vectorH12IntegrandSqOfLeray_le_vectorH12IntegrandSq
    (u : VectorSchwartz3C) (ξ : R3) :
    vectorH12IntegrandSqOfLeray u ξ ≤ vectorH12IntegrandSq u ξ := by
  unfold vectorH12IntegrandSqOfLeray vectorH12IntegrandSq
  -- Reduce to the operator-norm bound at w := (F u) ξ.
  have h_norm_le : ‖lerayProjectFreq u ξ‖
      ≤ ‖(fourierTransformCLM ℂ u) ξ‖ := by
    unfold lerayProjectFreq
    exact norm_lerayFourierSymbolC_le ξ _
  have h_norm_nn : 0 ≤ ‖lerayProjectFreq u ξ‖ := norm_nonneg _
  have h_sq_le : ‖lerayProjectFreq u ξ‖ ^ 2
      ≤ ‖(fourierTransformCLM ℂ u) ξ‖ ^ 2 :=
    pow_le_pow_left₀ h_norm_nn h_norm_le 2
  have h_xi_nn : 0 ≤ ‖ξ‖ := norm_nonneg _
  exact mul_le_mul_of_nonneg_left h_sq_le h_xi_nn

/-- **For the zero vector Schwartz input the Leray-projected integrand
vanishes identically.** The Leray image of the zero field is zero
(`lerayProjectFreq_zero`), so its squared norm is zero. -/
theorem vectorH12IntegrandSqOfLeray_zero (ξ : R3) :
    vectorH12IntegrandSqOfLeray (0 : VectorSchwartz3C) ξ = 0 := by
  unfold vectorH12IntegrandSqOfLeray
  rw [lerayProjectFreq_zero]
  simp

/-! ## §3 — Integrated Leray-projected seminorm and contraction bound -/

/-- **Integrated Leray-projected homogeneous Ḣ^{1/2} seminorm squared.**

  `∫ ξ ∈ ℝ³, ‖ξ‖ · ‖lerayProjectFreq u ξ‖² dξ`

This is the frequency-domain image of the squared `Ḣ^{1/2}` seminorm
of the Leray-projected field. Plancherel transports it to the
physical-space Leray-projected Sobolev seminorm; the Plancherel /
Fourier-inversion bridge to physical space is a separate brick. -/
noncomputable def vectorHomogeneousH12SeminormSqOfLeray
    (u : VectorSchwartz3C) : ℝ :=
  ∫ ξ : R3, vectorH12IntegrandSqOfLeray u ξ

/-- **The Leray-projected Ḣ^{1/2} seminorm squared is non-negative.**
Follows from pointwise non-negativity of the integrand and monotonicity
of the Bochner integral. -/
theorem vectorHomogeneousH12SeminormSqOfLeray_nonneg
    (u : VectorSchwartz3C) :
    0 ≤ vectorHomogeneousH12SeminormSqOfLeray u := by
  unfold vectorHomogeneousH12SeminormSqOfLeray
  exact MeasureTheory.integral_nonneg
    (fun ξ => vectorH12IntegrandSqOfLeray_nonneg u ξ)

/-- **For the zero vector Schwartz input the Leray-projected seminorm
squared is zero.** The integrand vanishes identically. -/
theorem vectorHomogeneousH12SeminormSqOfLeray_zero :
    vectorHomogeneousH12SeminormSqOfLeray (0 : VectorSchwartz3C) = 0 := by
  unfold vectorHomogeneousH12SeminormSqOfLeray
  simp only [vectorH12IntegrandSqOfLeray_zero, integral_zero]

/-- **★★★ THE HEADLINE THEOREM: Leray-projector contraction of the
homogeneous vector Ḣ^{1/2} seminorm squared at the frequency-domain
image level.** ★★★

For any vector Schwartz `u`,

  `∫ ‖ξ‖ · ‖lerayProjectFreq u ξ‖² dξ
        ≤ ∫ ‖ξ‖ · ‖(F u) ξ‖² dξ = ‖u‖²_{Ḣ^{1/2}}`.

This is the linear-projector dissipation step of Fujita-Kato 1964 at
the frequency-domain image level: the orthogonal Leray projector
cannot grow the homogeneous vector Sobolev seminorm of the data,
without any extra hypothesis on the vector Schwartz input.

Proof: from the pointwise contraction (§2) plus integral monotonicity
via `MeasureTheory.integral_mono_of_nonneg`, using non-negativity of
the Leray-projected integrand on the LHS and the unconditional
integrability of the comparison integrand on the RHS
(`vectorH12IntegrandSq_integrable_general` from
`VectorSobolevIntegrandIntegrable.lean`). -/
theorem vectorHomogeneousH12SeminormSqOfLeray_le
    (u : VectorSchwartz3C) :
    vectorHomogeneousH12SeminormSqOfLeray u
      ≤ vectorHomogeneousH12SeminormSq u := by
  unfold vectorHomogeneousH12SeminormSqOfLeray vectorHomogeneousH12SeminormSq
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall
      (fun ξ => vectorH12IntegrandSqOfLeray_nonneg u ξ))
    (vectorH12IntegrandSq_integrable_general u)
    (Filter.Eventually.of_forall
      (fun ξ => vectorH12IntegrandSqOfLeray_le_vectorH12IntegrandSq u ξ))

/-! ## §4 — Zero-input consequence -/

/-- **Sobolev seminorm of zero on zero input via the Leray-projected
route.** Independent re-derivation: the Leray image of the zero field
has Sobolev seminorm zero (§3), and the zero field itself has Sobolev
seminorm zero. The contraction bound is therefore trivially saturated
on the zero input. -/
theorem vectorHomogeneousH12SeminormSqOfLeray_le_zero_input :
    vectorHomogeneousH12SeminormSqOfLeray (0 : VectorSchwartz3C)
      ≤ vectorHomogeneousH12SeminormSq (0 : VectorSchwartz3C) := by
  rw [vectorHomogeneousH12SeminormSqOfLeray_zero,
      vectorHomogeneousH12SeminormSq_zero]

/-! ## §5 — Capstone -/

/-- **★ Fujita-Kato Leray-contracts-Sobolev brick capstone ★**

Bundles the seven results of this file:

  (a) Pointwise operator-norm bound on the complex Leray symbol:
      `‖lerayFourierSymbolC ξ w‖ ≤ ‖w‖`. This is the substantive
      analytic content — the Pythagorean / orthogonal-projector
      operator-norm = 1 statement.
  (b) Zero-frequency identity: `‖lerayFourierSymbolC 0 w‖ = ‖w‖`.
  (c) Pointwise non-negativity of the Leray-projected Sobolev integrand.
  (d) Pointwise contraction of the Leray-projected Sobolev integrand:
      `vectorH12IntegrandSqOfLeray u ξ ≤ vectorH12IntegrandSq u ξ`.
  (e) Pointwise vanishing on the zero input.
  (f) Integrated non-negativity of the Leray-projected Sobolev
      seminorm squared.
  (g) Integrated Leray-projector contraction bound (unconditional):
      `vectorHomogeneousH12SeminormSqOfLeray u
          ≤ vectorHomogeneousH12SeminormSq u`.

This is the linear-projector dissipation step of Fujita-Kato 1964 at
the frequency-domain image level: the Leray projector cannot grow the
homogeneous vector `Ḣ^{1/2}` seminorm. Together with the heat-semigroup
contraction (`VectorSobolevIntegrandIntegrable.lean` §4) this yields
the contraction of the Fujita-Kato linear propagator
`P e^{tΔ}` on the homogeneous vector `Ḣ^{1/2}` seminorm — the key
linear-side ingredient of the small-data global-existence theorem.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_leray_contracts_sobolev_brick_capstone :
    -- (a) Pointwise operator-norm bound on the complex Leray symbol
    (∀ (ξ : R3) (w : C3),
       ‖lerayFourierSymbolC ξ w‖ ≤ ‖w‖) ∧
    -- (b) Zero-frequency identity
    (∀ (w : C3),
       ‖lerayFourierSymbolC 0 w‖ = ‖w‖) ∧
    -- (c) Integrand non-negativity
    (∀ (u : VectorSchwartz3C) (ξ : R3),
       0 ≤ vectorH12IntegrandSqOfLeray u ξ) ∧
    -- (d) Pointwise contraction
    (∀ (u : VectorSchwartz3C) (ξ : R3),
       vectorH12IntegrandSqOfLeray u ξ ≤ vectorH12IntegrandSq u ξ) ∧
    -- (e) Pointwise vanishing on zero input
    (∀ (ξ : R3),
       vectorH12IntegrandSqOfLeray (0 : VectorSchwartz3C) ξ = 0) ∧
    -- (f) Integrated non-negativity
    (∀ (u : VectorSchwartz3C),
       0 ≤ vectorHomogeneousH12SeminormSqOfLeray u) ∧
    -- (g) Integrated contraction bound (unconditional)
    (∀ (u : VectorSchwartz3C),
       vectorHomogeneousH12SeminormSqOfLeray u
         ≤ vectorHomogeneousH12SeminormSq u) :=
  ⟨norm_lerayFourierSymbolC_le,
   norm_lerayFourierSymbolC_zero_freq,
   vectorH12IntegrandSqOfLeray_nonneg,
   vectorH12IntegrandSqOfLeray_le_vectorH12IntegrandSq,
   vectorH12IntegrandSqOfLeray_zero,
   vectorHomogeneousH12SeminormSqOfLeray_nonneg,
   vectorHomogeneousH12SeminormSqOfLeray_le⟩

/-! ## §6 — Axiom audit -/

#print axioms inner_lerayFourierSymbolC_complexifyVec_eq_zero
#print axioms norm_lerayFourierSymbolC_le
#print axioms norm_lerayFourierSymbolC_zero_freq
#print axioms vectorH12IntegrandSqOfLeray_nonneg
#print axioms vectorH12IntegrandSqOfLeray_le_vectorH12IntegrandSq
#print axioms vectorH12IntegrandSqOfLeray_zero
#print axioms vectorHomogeneousH12SeminormSqOfLeray_nonneg
#print axioms vectorHomogeneousH12SeminormSqOfLeray_zero
#print axioms vectorHomogeneousH12SeminormSqOfLeray_le
#print axioms vectorHomogeneousH12SeminormSqOfLeray_le_zero_input
#print axioms fujitaKato_leray_contracts_sobolev_brick_capstone

end PF.NavierStokes.FujitaKato1964.LerayContractsSobolev
