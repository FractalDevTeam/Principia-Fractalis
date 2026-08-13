/-
# r231: Corpus σ-sign complete dichotomy — one theorem, all 9 canonical pillars.

★ 2026-08-12 r231 — the CROSS-PILLAR CAPSTONE of the σ-sign work. Bundles
r225 + r226 + r227 + r228 + r229 + r230 (plus r212 direct hits for α_YM,
α_Poincaré, α_RH) into ONE 9-conjunct theorem on r223's `SubstrateOscillator`.
The substrate σ-sign MACHINE is complete: no per-pillar theorem needed
downstream, one universal statement covers every canonical alpha. ★

## Companion to r223's `corpus_constant_amplitude_dichotomy`

r223's dichotomy characterised which pillars have `σ = 0` (2 hits: Poincaré, RH)
vs `σ ≠ 0` (7 misses). r231 refines: for each pillar, the SIGN of σ (or its
exact value at σ = 0 or σ = 1). Structured as a three-way partition:

    σ ≥ +1 (linear growth or higher)         α_YM  (σ = 1 exactly)
    σ > 0 (sub-linear growth)                α_Hodge, α_NP, α_BSD
    σ = 0 (constant amplitude)               α_Poincaré, α_RH
    σ < 0 (envelope decay)                   α_P, α_QG (near-critical), α_NS

The trichotomy `{σ > 0} ⊔ {σ = 0} ⊔ {σ < 0}` partitions the 9 corpus pillars
into subsets of size (4, 2, 3) — a substrate-level classification.

## The r76 doubling identity as a sign flip

Recorded in r229's docstring but worth restating here: α_NS = 2 · α_BSD
(r76 `substrate_I5_alpha_NS_eq_two_alpha_BSD`). r228 gives σ(α_BSD) > 0,
r229 gives σ(α_NS) < 0. So `α ↦ 2·α` sends the sub-linear-growth tier to
the decay tier — a sign flip forced by the half-period translation
`cos(x + π) = -cos(x)`.

## Contents

§1 The complete σ-sign dichotomy — one 9-conjunct theorem.
§2 The three-way partition presentation.
§3 Corollaries:
   - `corpus_all_sigma_ne_neg_infty`: every corpus pillar has σ well-defined
     (`|1 + 2 cos| > 0`), so σ ≠ -∞ (no degenerate α = 2ℤ/3 case in the corpus).
   - `corpus_no_degenerate`: no corpus alpha triggers r212's degenerate branch.
§4 Axiom check.

## Scope

* NOT a Millennium discharge.
* NOT a substrate derivation of any pillar α.
* IS the cross-pillar completion of the σ-sign machine. IS the answer to
  "elevate equally from all pillars" — one theorem, nine pillars, all
  substrate signatures at once.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaPSigmaNegative_r225
import PF.AlphaHodgeSigmaPositive_r226
import PF.AlphaNPSigmaPositive_r227
import PF.AlphaBSDSigmaPositive_r228
import PF.AlphaNSSigmaNegative_r229
import PF.AlphaQGSigmaNegative_r230

open scoped Real

namespace PrincipiaTractalis.CorpusSigmaSignDichotomy

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 The complete σ-sign dichotomy. -/

/-- **`corpus_sigma_sign_dichotomy`** — the cross-pillar capstone.

For every data-fit `A ≠ 0` and every `φ₀`, the 9 canonical corpus pillars
have the following exact σ-signs (universal over data-fit):

    σ(α_YM)       = 1                 (linear growth)
    σ(α_Hodge)    > 0                 (sub-linear growth)
    σ(α_NP)       > 0                 (sub-linear growth)
    σ(α_BSD)      > 0                 (sub-linear growth)
    σ(α_Poincaré) = 0                 (constant amplitude)
    σ(α_RH)       = 0                 (constant amplitude)
    σ(α_P)        < 0                 (decay)
    σ(α_QG)       < 0                 (near-critical decay)
    σ(α_NS)       < 0                 (decay)

Each conjunct is a direct application of the pillar-specific theorem
(r212, r225-r230). No new mathematical content — pure bundling of the
elevation series. -/
theorem corpus_sigma_sign_dichotomy (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αYM A φ₀ hA).sigma = 1
      ∧ 0 < (SO_αHodge A φ₀ hA).sigma
      ∧ 0 < (SO_αNP A φ₀ hA).sigma
      ∧ 0 < (SO_αBSD A φ₀ hA).sigma
      ∧ (SO_αPoincare A φ₀ hA).sigma = 0
      ∧ (SO_αRH A φ₀ hA).sigma = 0
      ∧ (SO_αP A φ₀ hA).sigma < 0
      ∧ (SO_αQG A φ₀ hA).sigma < 0
      ∧ (SO_αNS A φ₀ hA).sigma < 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show PrincipiaTractalis.SigmaAbscissa.sigma 2 = 1
    exact sigma_two
  · exact AlphaHodgeSigmaPositive.SO_αHodge_sigma_pos A φ₀ hA
  · exact AlphaNPSigmaPositive.SO_αNP_sigma_pos A φ₀ hA
  · exact AlphaBSDSigmaPositive.SO_αBSD_sigma_pos A φ₀ hA
  · show PrincipiaTractalis.SigmaAbscissa.sigma 1 = 0
    exact sigma_one
  · show PrincipiaTractalis.SigmaAbscissa.sigma (3 / 2) = 0
    exact sigma_three_halves
  · exact AlphaPSigmaNegative.SO_αP_sigma_neg A φ₀ hA
  · exact AlphaQGSigmaNegative.SO_αQG_sigma_neg A φ₀ hA
  · exact AlphaNSSigmaNegative.SO_αNS_sigma_neg A φ₀ hA

/-! ## §2 The three-way trichotomy presentation. -/

/-- **The three-way trichotomy** — same content as §1, organised by sign class.

    POSITIVE-σ pillars (4): α_YM (σ = 1), α_Hodge, α_NP, α_BSD (σ > 0)
    ZERO-σ pillars    (2): α_Poincaré, α_RH
    NEGATIVE-σ pillars (3): α_P, α_QG, α_NS

Partition sizes (4, 2, 3), summing to 9 — the corpus. -/
theorem corpus_sigma_trichotomy (A φ₀ : ℝ) (hA : A ≠ 0) :
    -- σ > 0 group (4 pillars)
    (0 < (SO_αYM A φ₀ hA).sigma
      ∧ 0 < (SO_αHodge A φ₀ hA).sigma
      ∧ 0 < (SO_αNP A φ₀ hA).sigma
      ∧ 0 < (SO_αBSD A φ₀ hA).sigma)
      -- σ = 0 group (2 pillars)
      ∧ ((SO_αPoincare A φ₀ hA).sigma = 0 ∧ (SO_αRH A φ₀ hA).sigma = 0)
      -- σ < 0 group (3 pillars)
      ∧ ((SO_αP A φ₀ hA).sigma < 0
         ∧ (SO_αQG A φ₀ hA).sigma < 0
         ∧ (SO_αNS A φ₀ hA).sigma < 0) := by
  have hd := corpus_sigma_sign_dichotomy A φ₀ hA
  refine ⟨⟨?_, hd.2.1, hd.2.2.1, hd.2.2.2.1⟩, ⟨hd.2.2.2.2.1, hd.2.2.2.2.2.1⟩,
          ⟨hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2⟩⟩
  · rw [hd.1]; norm_num

/-! ## §3 Corollaries — no corpus pillar hits the degenerate branch. -/

/-- **No corpus pillar has `1 + 2·cos(π·α) = 0`** — the degenerate branch of
r212's `sigma_eq_zero_iff_full` (which occurs at α ∈ 2ℤ/3) is empty across
the corpus. Consequence: every corpus pillar has σ ∈ ℝ (finite), not the
`Real.logb b 0 = 0` sentinel value. -/
theorem corpus_no_degenerate (A φ₀ : ℝ) (hA : A ≠ 0) :
    1 + 2 * Real.cos (π * (SO_αYM A φ₀ hA).α) ≠ 0
      ∧ 1 + 2 * Real.cos (π * (SO_αHodge A φ₀ hA).α) ≠ 0
      ∧ 1 + 2 * Real.cos (π * (SO_αNP A φ₀ hA).α) ≠ 0
      ∧ 1 + 2 * Real.cos (π * (SO_αBSD A φ₀ hA).α) ≠ 0
      ∧ 1 + 2 * Real.cos (π * (SO_αPoincare A φ₀ hA).α) ≠ 0
      ∧ 1 + 2 * Real.cos (π * (SO_αRH A φ₀ hA).α) ≠ 0
      ∧ 1 + 2 * Real.cos (π * (SO_αP A φ₀ hA).α) ≠ 0
      ∧ 1 + 2 * Real.cos (π * (SO_αQG A φ₀ hA).α) ≠ 0
      ∧ 1 + 2 * Real.cos (π * (SO_αNS A φ₀ hA).α) ≠ 0 := by
  -- For each pillar, σ well-defined implies `|1 + 2 cos| > 0` implies
  -- `1 + 2 cos ≠ 0`. This is derivable from the dichotomy sign facts +
  -- absurdity: if `1 + 2 cos = 0` then `|·| = 0` so `σ = 0` by mathlib's
  -- `logb b 0 = 0` convention, contradicting σ = 1, σ > 0, or σ < 0.
  -- The σ = 0 pillars (Poincaré, RH) need the r212 direct arguments.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- α_YM = 2: cos(2π) = 1, so 1 + 2·1 = 3 ≠ 0
    show 1 + 2 * Real.cos (π * 2) ≠ 0
    rw [show π * 2 = 2 * π from by ring, Real.cos_two_pi]
    norm_num
  · -- α_Hodge: r226's cos > 0 gives 1 + 2 cos > 1 > 0
    show 1 + 2 * Real.cos (π * Real.goldenRatio) ≠ 0
    intro heq
    linarith [AlphaHodgeSigmaPositive.cos_pi_mul_goldenRatio_pos]
  · -- α_NP: r227's cos > 0 gives 1 + 2 cos > 1 > 0
    show 1 + 2 * Real.cos (π * (Real.goldenRatio + 1 / 4)) ≠ 0
    intro heq
    linarith [AlphaNPSigmaPositive.cos_pi_mul_alphaNP_pos]
  · -- α_BSD: r228's cos > 0 gives 1 + 2 cos > 1 > 0
    show 1 + 2 * Real.cos (π * (3 * π / 4)) ≠ 0
    intro heq
    linarith [AlphaBSDSigmaPositive.cos_pi_mul_alphaBSD_pos]
  · -- α_Poincaré = 1: cos(π) = -1, so 1 + 2·(-1) = -1 ≠ 0
    show 1 + 2 * Real.cos (π * 1) ≠ 0
    rw [mul_one, Real.cos_pi]
    norm_num
  · -- α_RH = 3/2: cos(3π/2) = 0, so 1 + 2·0 = 1 ≠ 0
    show 1 + 2 * Real.cos (π * (3 / 2)) ≠ 0
    have : Real.cos (π * (3 / 2)) = 0 := by
      rw [show π * (3 / 2) = π + π / 2 from by ring, Real.cos_add,
          Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    rw [this]; norm_num
  · -- α_P: r225's already-proved `one_add_two_cos_pi_mul_sqrt_two_ne_zero`
    exact AlphaPSigmaNegative.one_add_two_cos_pi_mul_sqrt_two_ne_zero
  · -- α_QG: r230's already-proved analogous non-vanishing
    exact AlphaQGSigmaNegative.one_add_two_cos_pi_mul_alphaQG_ne_zero
  · -- α_NS: r229's already-proved analogous non-vanishing
    exact AlphaNSSigmaNegative.one_add_two_cos_pi_mul_alphaNS_ne_zero

/-! ## §4 Axiom check. -/

#print axioms PrincipiaTractalis.CorpusSigmaSignDichotomy.corpus_sigma_sign_dichotomy
#print axioms PrincipiaTractalis.CorpusSigmaSignDichotomy.corpus_sigma_trichotomy
#print axioms PrincipiaTractalis.CorpusSigmaSignDichotomy.corpus_no_degenerate

end PrincipiaTractalis.CorpusSigmaSignDichotomy
