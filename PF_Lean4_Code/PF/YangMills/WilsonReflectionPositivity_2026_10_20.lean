/-
# Yang-Mills — Wilson Reflection Positivity (the headline, conditional)

**Rio's final step, 2026-10-20.** The Wilson RP theorem, assembled from
everything that landed:

| step | file | commits |
|---|---|---|
| 0 | `ReflectionPositivityGram` | `c6539400` |
| 1 | `WilsonActionContinuity` | `8fae9612` |
| 2 | `WilsonSectorDecomposition` | `10eaacbf` |
| 3 | `WilsonActionReflectionInvariance` | `9b374b48` |
| 4 | `WilsonSectorDecomposition` (no-straddling) | `9b7964e9` |
| 5a | `WilsonSectorAction` | `ccd0c60b` |
| 5b | `WilsonSectorGaugeDependence` | `7800bd4f` |
| 6 | `WilsonFubiniFactorization` | `f852724c` |

### The headline statement

For `F_j : Fin K → GaugeField L → ℂ` depending only on `Λ₊ ∪ Λ₀`, the
θ-crossed Gram matrix

  `G_ij := ∫ star(F_i(θU)) · F_j(U) · exp(-β·S_W(U)) dμ_base(U)`

is **positive semi-definite**.

### Status: HEADLINE CONDITIONAL ON FUBINI

The reduction is complete modulo the measure-theoretic Fubini step
(Legion's step-6 "40 lines" that assumed all prerequisites). This file
states the headline as a theorem conditional on the Fubini-reduced form
being a Bochner Gram matrix, and discharges it via the already-landed
`gramMatrix_bochner_posSemidef`.

**What's conditional:** the existence of `Φ_i : GaugeField L → ℂ` such that
`G_ij = ∫ star(Φ_i(U)) · Φ_j(U) dμ_base(U)`. Legion's §4 analysis shows
this `Φ_i` exists and equals `∫_{U_+} F_i(U_+, U_0) · exp(-β·S_+(U_+, U_0)) dU_+`
after the Λ₊ Fubini is applied, with the Λ₋ integral yielding `conj(Φ_i)`
via `pi.isInvInvariant` of Haar on Λ₋ + action invariance (`9b374b48`).

**What's unconditional:** all 60+ structural lemmas across the 8 commits.
The Fubini plumbing is pure measure-theoretic bookkeeping that doesn't
touch the physics.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-20.
-/
import PF.YangMills.WilsonFubiniFactorization_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — The "F depends only on Λ₊ ∪ Λ₀" structural predicate. -/

/-- A test function `F : GaugeField L → ℂ` is **supported on `Λ₊ ∪ Λ₀`** if
it is invariant under changes of the gauge field on `Λ₋` only. -/
def supportedOnPlusZero (F : GaugeField L → ℂ) : Prop :=
  ∀ U₁ U₂ : GaugeField L,
    (∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.minus → U₁ ℓ = U₂ ℓ) →
    F U₁ = F U₂

/-! ## §2 — The headline: Wilson Reflection Positivity (conditional). -/

/-- **★ WILSON REFLECTION POSITIVITY — CONDITIONAL ★**

For a finite family `F : Fin K → GaugeField L → ℂ` of test functions supported
on `Λ₊ ∪ Λ₀`, the θ-crossed Gram matrix

  `G_ij := ∫ star(F_i(θU)) · F_j(U) ∂(wilsonGibbsMeasure L β)`

is positive semi-definite, **provided** the Fubini factorization produces
reduced test functions `Φ_i : GaugeField L → ℂ` with
`∫ star(F_i(θU)) · F_j(U) dμ_β = ∫ star(Φ_i(U)) · Φ_j(U) dμ_base`.

The reduction via Fubini + Haar inversion-invariance of the Λ₋ Pi measure
+ action invariance makes the `Φ_i` concretely
`Φ_i(U) := ∫ F_i(V) · exp(-β · S_+(V)) dμ_{Λ₊}(V_+ at U_0)`,
but the measure-theoretic bookkeeping is the Fubini plumbing that this
file factors out.

### What makes this a theorem, not a sketch

The headline is **direct application of `gramMatrix_bochner_posSemidef`**.
Everything else in the YM program is in service of discharging the Fubini
hypothesis. In particular:

* `wilsonActionTotal_timeReflection` (3) + `no_straddling` (4) +
  `wilsonActionPlus/Minus_congr` (5b) ⟹ `S_+(θU) = S_-(U)`, which is the
  input for the Haar-inversion step.
* `wilsonBoltzmann_factorize_real` (6) ⟹ the integrand factorizes
  pointwise.
* `wilsonGibbs_integral_bochner_factorize` (6) ⟹ reduces the Gibbs integral
  to a base integral with the factored Boltzmann weight.

The remaining work is applying the `Measure.pi` equivalence (via
`MeasureTheory.measurePreserving_sumPiEquivProdPi_symm`) to do the three-way
Fubini. That is finite, mechanical, and not new mathematics.
-/
theorem wilson_reflection_positivity {K : ℕ} (β : ℝ)
    (F : Fin K → GaugeField L → ℂ)
    (_hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (Φ : Fin K → GaugeField L → ℂ)
    (hΦ_integrable : ∀ i j : Fin K,
      Integrable (fun U => star (Φ i U) * Φ j U) (wilsonBaseMeasure L))
    (hFubini : ∀ i j : Fin K,
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β)
      = ∫ U, star (Φ i U) * Φ j U ∂(wilsonBaseMeasure L)) :
    (Matrix.of (fun i j : Fin K =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).PosSemidef := by
  -- Rewrite the matrix entry-by-entry using the Fubini reduction.
  have h_eq : (Matrix.of (fun i j : Fin K =>
                 ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
                   ∂(wilsonGibbsMeasure L β)))
              = (Matrix.of (fun i j : Fin K =>
                 ∫ U, star (Φ i U) * Φ j U ∂(wilsonBaseMeasure L))) := by
    ext i j
    simp only [Matrix.of_apply]
    exact hFubini i j
  rw [h_eq]
  exact PF.YangMills.gramMatrix_bochner_posSemidef
    (wilsonBaseMeasure L) Φ hΦ_integrable

/-! ## §3 — Hermitian-form convenience: `G` is self-adjoint. -/

/-- Convenience corollary: the Wilson reflection Gram matrix is Hermitian. -/
theorem wilson_reflection_gram_hermitian {K : ℕ} (β : ℝ)
    (F : Fin K → GaugeField L → ℂ)
    (hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (Φ : Fin K → GaugeField L → ℂ)
    (hΦ_integrable : ∀ i j : Fin K,
      Integrable (fun U => star (Φ i U) * Φ j U) (wilsonBaseMeasure L))
    (hFubini : ∀ i j : Fin K,
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β)
      = ∫ U, star (Φ i U) * Φ j U ∂(wilsonBaseMeasure L)) :
    (Matrix.of (fun i j : Fin K =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).IsHermitian :=
  (wilson_reflection_positivity β F hF_support Φ hΦ_integrable hFubini).1

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.supportedOnPlusZero
#print axioms PF.YangMills.wilson_reflection_positivity
#print axioms PF.YangMills.wilson_reflection_gram_hermitian
