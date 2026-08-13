/-
# r235: Corpus 10-pillar σ-sign dichotomy — full capstone with α_HN.

★ 2026-08-13 r235 — extends r231's 9-pillar σ-sign dichotomy to the FULL
10-pillar corpus by adding α_HN = 5 (r232). Completes the substrate σ-sign
machine at the 10-instance level. Trichotomy sizes shift from (4, 2, 3) to
**(4, 3, 3)** — α_HN joins the σ = 0 constant-amplitude tier. ★

## The completed 10-pillar σ-sign dichotomy

| pillar     | α       | σ           | tier                  |
|------------|---------|-------------|-----------------------|
| α_YM       | 2       | σ = 1       | linear growth (r224)  |
| α_Hodge    | φ       | σ > 0       | sub-linear (r226)     |
| α_NP       | φ + 1/4 | σ > 0       | sub-linear (r227)     |
| α_BSD      | 3π/4    | σ > 0       | sub-linear (r228)     |
| α_Poincaré | 1       | σ = 0       | constant (r221)       |
| α_RH       | 3/2     | σ = 0       | constant (r221)       |
| **α_HN**   | 5       | σ = 0       | constant (r232 THIS)  |
| α_P        | √2      | σ < 0       | decay (r225)          |
| α_QG       | √(2π)   | σ < 0       | decay near-critical (r230) |
| α_NS       | 3π/2    | σ < 0       | decay (r229)          |

**Trichotomy sizes (4, 3, 3)** summing to 10.

## Contents

§1 `corpus_10_pillar_sigma_sign_dichotomy` — the 10-conjunct capstone.
§2 `corpus_10_pillar_trichotomy` — three-way partition presentation.
§3 Axiom check.

## Scope

* Framework-first bundling. No new mathematical content beyond r231 + r232.
* IS the completed corpus σ-sign machine at the 10-instance level.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaHNPillar_r232
import PF.CorpusSigmaSignDichotomy_r231

open scoped Real

namespace PrincipiaTractalis.Corpus10PillarDichotomy

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis
open PrincipiaTractalis.CorpusSigmaSignDichotomy

/-! ## §1 The full 10-pillar dichotomy. -/

/-- **`corpus_10_pillar_sigma_sign_dichotomy`** — the completed capstone.

10-conjunct universal theorem covering every canonical corpus pillar:

    σ(α_YM)       = 1                (r224 / sigma_two)
    σ(α_Hodge)    > 0                (r226)
    σ(α_NP)       > 0                (r227)
    σ(α_BSD)      > 0                (r228)
    σ(α_Poincaré) = 0                (r221 / sigma_one)
    σ(α_RH)       = 0                (r221 / sigma_three_halves)
    σ(α_HN)       = 0                (r232)  ← the extension
    σ(α_P)        < 0                (r225)
    σ(α_QG)       < 0                (r230)
    σ(α_NS)       < 0                (r229)

Universally quantified over data-fit `(A, φ₀)`. -/
theorem corpus_10_pillar_sigma_sign_dichotomy (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αYM A φ₀ hA).sigma = 1
      ∧ 0 < (SO_αHodge A φ₀ hA).sigma
      ∧ 0 < (SO_αNP A φ₀ hA).sigma
      ∧ 0 < (SO_αBSD A φ₀ hA).sigma
      ∧ (SO_αPoincare A φ₀ hA).sigma = 0
      ∧ (SO_αRH A φ₀ hA).sigma = 0
      ∧ (SO_αHN A φ₀ hA).sigma = 0
      ∧ (SO_αP A φ₀ hA).sigma < 0
      ∧ (SO_αQG A φ₀ hA).sigma < 0
      ∧ (SO_αNS A φ₀ hA).sigma < 0 := by
  have h9 := corpus_sigma_sign_dichotomy A φ₀ hA
  have hHN := SO_αHN_sigma_eq_zero A φ₀ hA
  exact ⟨h9.1, h9.2.1, h9.2.2.1, h9.2.2.2.1,
         h9.2.2.2.2.1, h9.2.2.2.2.2.1,
         hHN,
         h9.2.2.2.2.2.2.1, h9.2.2.2.2.2.2.2.1, h9.2.2.2.2.2.2.2.2⟩

/-! ## §2 The three-way trichotomy presentation. -/

/-- **The three-way trichotomy at the 10-pillar level.**

    POSITIVE-σ pillars (4): α_YM (σ = 1), α_Hodge, α_NP, α_BSD (σ > 0)
    ZERO-σ pillars    (3): α_Poincaré, α_RH, α_HN     ← α_HN added
    NEGATIVE-σ pillars (3): α_P, α_QG, α_NS

Partition sizes **(4, 3, 3)** summing to 10 — the extended corpus. -/
theorem corpus_10_pillar_trichotomy (A φ₀ : ℝ) (hA : A ≠ 0) :
    -- σ > 0 group (4 pillars)
    (0 < (SO_αYM A φ₀ hA).sigma
      ∧ 0 < (SO_αHodge A φ₀ hA).sigma
      ∧ 0 < (SO_αNP A φ₀ hA).sigma
      ∧ 0 < (SO_αBSD A φ₀ hA).sigma)
      -- σ = 0 group (3 pillars, expanded from r231's 2 with α_HN)
      ∧ ((SO_αPoincare A φ₀ hA).sigma = 0
         ∧ (SO_αRH A φ₀ hA).sigma = 0
         ∧ (SO_αHN A φ₀ hA).sigma = 0)
      -- σ < 0 group (3 pillars)
      ∧ ((SO_αP A φ₀ hA).sigma < 0
         ∧ (SO_αQG A φ₀ hA).sigma < 0
         ∧ (SO_αNS A φ₀ hA).sigma < 0) := by
  have hd := corpus_10_pillar_sigma_sign_dichotomy A φ₀ hA
  refine ⟨⟨?_, hd.2.1, hd.2.2.1, hd.2.2.2.1⟩,
          ⟨hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1⟩,
          ⟨hd.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2⟩⟩
  · rw [hd.1]; norm_num

/-! ## §3 Axiom check. -/

#print axioms PrincipiaTractalis.Corpus10PillarDichotomy.corpus_10_pillar_sigma_sign_dichotomy
#print axioms PrincipiaTractalis.Corpus10PillarDichotomy.corpus_10_pillar_trichotomy

end PrincipiaTractalis.Corpus10PillarDichotomy
