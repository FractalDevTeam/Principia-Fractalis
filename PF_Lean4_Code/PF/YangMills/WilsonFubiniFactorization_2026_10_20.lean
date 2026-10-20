/-
# Yang-Mills — Fubini factorization (Legion step 6)

**Rio's Step 6, 2026-10-20.** The culminating structural lemma of the
sector-split route. Combines:
* Step 5a sector sum identity `S_W = S_+ + S_-` (`ccd0c60b`),
* Step 5b sector-wise gauge dependence (`7800bd4f`),
* Step 1 continuity + measurability + finiteness (`8fae9612`),
to deliver the **Boltzmann weight factorization**

  `exp(-β · S_W(U)) = exp(-β · S_+(U)) · exp(-β · S_-(U))`

as a pointwise identity on `GaugeField L`. This is the key input to the
Fubini factorization of the Wilson Gibbs integral over `Λ₊ ⊕ Λ₀ ⊕ Λ₋`.

### What this file provides

* `wilsonBoltzmann_factorize_real` — the real-valued Boltzmann weight
  factorizes.
* `wilsonBoltzmann_factorize_ennreal` — the ENNReal version used by
  `Measure.withDensity`.
* `wilsonActionTotal_eq_plus_add_minus` — convenience restatement of the
  sector sum identity for inlining into the Boltzmann weight.
* **`wilsonGibbs_integral_bochner_factorize`** — the headline Bochner
  integral factorization: for any `ℂ`-valued integrable `F : GaugeField L → ℂ`,

  `∫ F(U) ∂(wilsonGibbsMeasure L β)
     = ∫ F(U) · exp(-β·S_+(U)) · exp(-β·S_-(U)) ∂(wilsonBaseMeasure L)`,

  which is the entry point to the Fubini step on the `Λ₊ ⊕ Λ₀ ⊕ Λ₋` split.

### What remains for the final Wilson RP headline

Pending the following measure-theoretic plumbing (not in this file):

1. The explicit `Equiv (LatticeLink L) (Λ₊ ⊕ Λ₀ ⊕ Λ₋)` and the resulting
   `MeasurePreserving (Measure.pi SU2_haar) (Measure.pi × Measure.pi × Measure.pi)`.
2. Fubini on this split to get `∫_{Λ₊} ⊗ ∫_{Λ₀} ⊗ ∫_{Λ₋}`.
3. θ-invariance of the base Haar lifted to Λ₋ via `pi.isInvInvariant`.
4. Final apply of `gramMatrix_bochner_posSemidef`.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-20.
-/
import PF.YangMills.WilsonActionContinuity_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory Real

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Convenience: inline the sector sum identity. -/

/-- Pointwise form of the sector sum identity: `S_W(U) = S_+(U) + S_-(U)`.
Convenient as a `rw` lemma. -/
lemma wilsonActionTotal_eq_plus_add_minus (U : GaugeField L) :
    wilsonActionTotal U = wilsonActionPlus U + wilsonActionMinus U :=
  wilsonActionTotal_sector_decomposition U

/-! ## §2 — Boltzmann weight factorizes. -/

/-- **★ BOLTZMANN FACTORIZATION (ℝ-valued) ★**

`exp(-β · S_W(U)) = exp(-β · S_+(U)) · exp(-β · S_-(U))`.

Pure consequence of `Real.exp_add` and the sector sum identity. -/
theorem wilsonBoltzmann_factorize_real (β : ℝ) (U : GaugeField L) :
    Real.exp (-β * wilsonActionTotal U)
      = Real.exp (-β * wilsonActionPlus U) * Real.exp (-β * wilsonActionMinus U) := by
  rw [wilsonActionTotal_eq_plus_add_minus, mul_add, Real.exp_add]

/-- **★ BOLTZMANN FACTORIZATION (ℝ≥0∞) ★**

The `ENNReal.ofReal`-valued version used by `Measure.withDensity`. -/
theorem wilsonBoltzmann_factorize_ennreal (β : ℝ) (U : GaugeField L) :
    ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U))
      = ENNReal.ofReal (Real.exp (-β * wilsonActionPlus U))
          * ENNReal.ofReal (Real.exp (-β * wilsonActionMinus U)) := by
  rw [wilsonBoltzmann_factorize_real]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-! ## §3 — Integral factorization against the Gibbs measure. -/

/-- The Boltzmann weight is nonneg and continuous ⇒ measurable + bounded. -/
lemma wilsonBoltzmann_real_nonneg (β : ℝ) (U : GaugeField L) :
    0 ≤ Real.exp (-β * wilsonActionTotal U) :=
  Real.exp_nonneg _

/-- **Boltzmann weight factors as `S_+` weight times `S_-` weight — pointwise.**

Phrased explicitly as a function identity for use with
`MeasureTheory.lintegral_mul_const` and friends. -/
theorem wilsonBoltzmann_as_product (β : ℝ) :
    (fun U : GaugeField L => ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U)))
      = (fun U => ENNReal.ofReal (Real.exp (-β * wilsonActionPlus U))
                    * ENNReal.ofReal (Real.exp (-β * wilsonActionMinus U))) := by
  funext U
  exact wilsonBoltzmann_factorize_ennreal β U

/-! ## §4 — Bochner integral factorization: the Fubini entry point. -/

/-- For a `ℂ`-valued integrable function `F`, the Bochner integral against
`wilsonGibbsMeasure` equals the integral against `wilsonBaseMeasure` with
the Boltzmann weight applied. This is `integral_withDensity_eq_integral_toReal_smul`
applied to `wilsonGibbsMeasure`'s definition. -/
theorem wilsonGibbs_integral_eq_base_integral (β : ℝ) (F : GaugeField L → ℂ) :
    ∫ U, F U ∂(wilsonGibbsMeasure L β)
      = ∫ U, Real.exp (-β * wilsonActionTotal U) • F U ∂(wilsonBaseMeasure L) := by
  unfold wilsonGibbsMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (expWilsonDensity_measurable β)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  congr 1
  funext U
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]

/-- **★ THE FACTORIZATION ENTRY POINT ★**

Combining Boltzmann factorization + the Gibbs-to-base rewrite: for integrable
`F`, the Gibbs integral splits into a base integral with **both** sector
Boltzmann weights:

  `∫ F · dμ_β = ∫ F · exp(-β·S_+) · exp(-β·S_-) · dμ_base`.

This is the form the Fubini factorization over `Λ₊ ⊕ Λ₀ ⊕ Λ₋` consumes. -/
theorem wilsonGibbs_integral_bochner_factorize (β : ℝ) (F : GaugeField L → ℂ) :
    ∫ U, F U ∂(wilsonGibbsMeasure L β)
      = ∫ U, (Real.exp (-β * wilsonActionPlus U)
              * Real.exp (-β * wilsonActionMinus U)) • F U
        ∂(wilsonBaseMeasure L) := by
  rw [wilsonGibbs_integral_eq_base_integral β F]
  congr 1
  funext U
  rw [wilsonBoltzmann_factorize_real]

/-! ## §5 — Convenience: factored weight separates `S_+`-dependence from `S_-`-dependence.

By step 5b (`wilsonActionPlus_congr`, `wilsonActionMinus_congr`), `S_+` reads
only `Λ₊ ∪ Λ₀` and `S_-` reads only `Λ₋ ∪ Λ₀`. Combined with the factorization,
the two Boltzmann factors have **disjoint** gauge-field dependence in the sense
that under the Fubini split, one integrates against `U_+` only, the other
against `U_-` only. -/

/-- Convenience: the Boltzmann plus-factor depends only on `Λ₊ ∪ Λ₀`. -/
theorem wilsonBoltzmann_plus_congr (hL : Even L) (β : ℝ) (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.minus → U₁ ℓ = U₂ ℓ) :
    Real.exp (-β * wilsonActionPlus U₁) = Real.exp (-β * wilsonActionPlus U₂) := by
  rw [wilsonActionPlus_congr hL U₁ U₂ hAgree]

/-- Convenience: the Boltzmann minus-factor depends only on `Λ₋ ∪ Λ₀`. -/
theorem wilsonBoltzmann_minus_congr (hL : Even L) (β : ℝ) (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.plus → U₁ ℓ = U₂ ℓ) :
    Real.exp (-β * wilsonActionMinus U₁) = Real.exp (-β * wilsonActionMinus U₂) := by
  rw [wilsonActionMinus_congr hL U₁ U₂ hAgree]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonActionTotal_eq_plus_add_minus
#print axioms PF.YangMills.wilsonBoltzmann_factorize_real
#print axioms PF.YangMills.wilsonBoltzmann_factorize_ennreal
#print axioms PF.YangMills.wilsonBoltzmann_real_nonneg
#print axioms PF.YangMills.wilsonBoltzmann_as_product
#print axioms PF.YangMills.wilsonGibbs_integral_eq_base_integral
#print axioms PF.YangMills.wilsonGibbs_integral_bochner_factorize
#print axioms PF.YangMills.wilsonBoltzmann_plus_congr
#print axioms PF.YangMills.wilsonBoltzmann_minus_congr
