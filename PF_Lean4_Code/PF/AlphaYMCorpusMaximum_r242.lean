/-
# r242: α_YM IS THE UNIQUE σ-MAXIMUM IN THE 10-PILLAR CORPUS.

★ 2026-08-13 r242 — THE BRIDGE landing tying r241's universal σ-ceiling
to r235's 10-pillar corpus σ-sign dichotomy. Corollary: α_YM = 2 is the
UNIQUE α in the canonical corpus that reaches the substrate maximum
σ = 1; every other corpus pillar strictly misses. ★

## The result

Combining r241 (`sigma_le_one`, σ ≤ 1 for all α), r212 (`sigma_two`,
σ(2) = 1), and the corpus σ-sign classification (r212 `sigma_alpha*_ne_zero_one`
+ r225–r232 individual pillar σ-signs), we get:

- `α_YM = 2` — σ = 1 ✓ (r212, on the ceiling)
- `α_Poincaré = 1, α_RH = 3/2, α_HN = 5` — σ = 0 (r212, r232, strictly < 1)
- `α_Hodge = φ, α_NP = φ+1/4, α_BSD = 3π/4` — σ > 0, σ ≠ 1 (r212 + r226/r227/r228, strictly < 1)
- `α_P = √2, α_QG = √(2π), α_NS = 3π/2` — σ < 0 (r225/r230/r229, strictly < 1)

So σ(α_YM) = 1 is achieved and NO other corpus α reaches it.

## Why this matters

The r231/r235 σ-sign dichotomy classifies each pillar's substrate growth
regime (linear, sub-linear, constant, decay). r241's universal ceiling
puts a HARD upper bound of 1 on the substrate spectrum. r242 fuses them:

- The corpus has ONE pillar (α_YM) at the top of the spectrum.
- Every other pillar is strictly below.
- The substrate maximum is UNIQUE within the canonical corpus.

Framework-first: no per-axis fragmentation. One theorem, one referent.

α_YM = 2 being the ζ-pole abscissa (r233 tie-in via σ(0) = 1 = ζ classical
abscissa; α = 2 and α = 0 both in 2ℤ per r241 characterization) also means:
the substrate's maximum growth tier is the SAME lattice as the classical
Riemann-ζ pole. The corpus max is empirically anchored to a well-known
external classical result.

## Contents

§1 `sigma_alphaYM_eq_one` — restatement of r212 `sigma_two` in α_YM language.
§2 `sigma_lt_alphaYM_of_ne_alphaYM_in_corpus` — pillar-by-pillar strict
   comparison against α_YM = 2.
§3 `alphaYM_unique_maximum_in_10_pillar_corpus` — the packaged capstone.
§4 Axiom check.

## Scope

* NOT a novel result — direct composition of r241 + r212 + r235.
* NOT a Millennium discharge.
* IS a corpus-level bridging theorem showing α_YM is the substrate's
  unique growth-tier peak in the 10-canonical corpus.

Third structural landing after r240 (symmetries) and r241 (upper bound).
Bridges structural (r241) to corpus (r235). Framework-first.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.SigmaUpperBound_r241
import PF.Corpus10PillarDichotomy_r235

open scoped Real

namespace PrincipiaTractalis.AlphaYMCorpusMaximum

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.SigmaUpperBound
open PrincipiaTractalis

/-! ## §1 `σ(α_YM) = 1` in α_YM language. -/

/-- **`sigma_alphaYM_eq_one`** — restatement of r212's `sigma_two` in
α_YM = 2 identity form. α_YM is at the substrate ceiling. -/
theorem sigma_alphaYM_eq_one :
    PrincipiaTractalis.SigmaAbscissa.sigma 2 = 1 :=
  PrincipiaTractalis.SigmaAbscissa.sigma_two

/-! ## §2 Pillar-by-pillar strict comparisons to α_YM. -/

/-- **α_Poincaré strictly below α_YM.** σ(1) = 0 < 1 = σ(2). -/
theorem sigma_alphaPoincare_lt_alphaYM :
    PrincipiaTractalis.SigmaAbscissa.sigma 1 <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 := by
  rw [PrincipiaTractalis.SigmaAbscissa.sigma_one, sigma_alphaYM_eq_one]
  norm_num

/-- **α_RH strictly below α_YM.** σ(3/2) = 0 < 1 = σ(2). -/
theorem sigma_alphaRH_lt_alphaYM :
    PrincipiaTractalis.SigmaAbscissa.sigma (3/2) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 := by
  rw [PrincipiaTractalis.SigmaAbscissa.sigma_three_halves, sigma_alphaYM_eq_one]
  norm_num

/-- **α_HN strictly below α_YM.** σ(5) = 0 < 1 = σ(2). -/
theorem sigma_alphaHN_lt_alphaYM :
    PrincipiaTractalis.SigmaAbscissa.sigma 5 <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 := by
  rw [PrincipiaTractalis.sigma_alphaHN_eq_zero, sigma_alphaYM_eq_one]
  norm_num

/-- **α_Hodge strictly below α_YM.** σ(φ) ≤ 1 (r241) and σ(φ) ≠ 1 (r212). -/
theorem sigma_alphaHodge_lt_alphaYM :
    PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 := by
  rw [sigma_alphaYM_eq_one]
  have hle : PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio ≤ 1 :=
    sigma_le_one Real.goldenRatio
  have hne : PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio ≠ 1 :=
    PrincipiaTractalis.SigmaAbscissa.sigma_alphaHodge_ne_zero_one.2
  exact lt_of_le_of_ne hle hne

/-- **α_P strictly below α_YM.** σ(√2) ≤ 1 (r241) and σ(√2) ≠ 1 (r212). -/
theorem sigma_alphaP_lt_alphaYM :
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 := by
  rw [sigma_alphaYM_eq_one]
  have hle : PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) ≤ 1 :=
    sigma_le_one (Real.sqrt 2)
  have hne : PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) ≠ 1 :=
    PrincipiaTractalis.SigmaAbscissa.sigma_alphaP_ne_zero_one.2
  exact lt_of_le_of_ne hle hne

/-- **α_NP strictly below α_YM.** σ(φ+1/4) ≤ 1 (r241) and σ(φ+1/4) ≠ 1 (r212). -/
theorem sigma_alphaNP_lt_alphaYM :
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1/4) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 := by
  rw [sigma_alphaYM_eq_one]
  have hle : PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1/4) ≤ 1 :=
    sigma_le_one _
  have hne : PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1/4) ≠ 1 :=
    PrincipiaTractalis.SigmaAbscissa.sigma_alphaNP_ne_zero_one.2
  exact lt_of_le_of_ne hle hne

/-- **α_QG strictly below α_YM.** σ(√(2π)) ≤ 1 (r241) and σ(√(2π)) ≠ 1 (r212). -/
theorem sigma_alphaQG_lt_alphaYM :
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 := by
  rw [sigma_alphaYM_eq_one]
  have hle : PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) ≤ 1 :=
    sigma_le_one _
  have hne : PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) ≠ 1 :=
    PrincipiaTractalis.SigmaAbscissa.sigma_alphaQG_ne_zero_one.2
  exact lt_of_le_of_ne hle hne

/-- **α_BSD strictly below α_YM.** σ(3π/4) ≤ 1 (r241) and σ(3π/4) ≠ 1 (r212). -/
theorem sigma_alphaBSD_lt_alphaYM :
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 := by
  rw [sigma_alphaYM_eq_one]
  have hle : PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) ≤ 1 :=
    sigma_le_one _
  have hne : PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) ≠ 1 :=
    PrincipiaTractalis.SigmaAbscissa.sigma_alphaBSD_ne_zero_one.2
  exact lt_of_le_of_ne hle hne

/-- **α_NS strictly below α_YM.** σ(3π/2) ≤ 1 (r241) and σ(3π/2) ≠ 1 (r212). -/
theorem sigma_alphaNS_lt_alphaYM :
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 := by
  rw [sigma_alphaYM_eq_one]
  have hle : PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) ≤ 1 :=
    sigma_le_one _
  have hne : PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) ≠ 1 :=
    PrincipiaTractalis.SigmaAbscissa.sigma_alphaNS_ne_zero_one.2
  exact lt_of_le_of_ne hle hne

/-! ## §3 The α_YM unique-maximum capstone over the 10-pillar corpus. -/

/-- **`alphaYM_unique_maximum_in_10_pillar_corpus`** — the capstone.

α_YM = 2 achieves the substrate ceiling σ = 1, and every OTHER pillar
in the 10-canonical corpus (α_Poincaré, α_RH, α_HN, α_Hodge, α_P, α_NP,
α_QG, α_BSD, α_NS) has σ strictly less than α_YM's.

10-conjunct bundle: 1 equality + 9 strict inequalities. Framework-first
composition of r241's universal ceiling with r212/r232's individual
pillar characterizations. -/
theorem alphaYM_unique_maximum_in_10_pillar_corpus :
    -- α_YM at the ceiling:
    PrincipiaTractalis.SigmaAbscissa.sigma 2 = 1 ∧
    -- σ = 0 tier strictly below:
    PrincipiaTractalis.SigmaAbscissa.sigma 1 <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (3/2) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma 5 <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
    -- Growth tier strictly below:
    PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1/4) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
    -- Decay tier strictly below:
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) <
      PrincipiaTractalis.SigmaAbscissa.sigma 2 :=
  ⟨sigma_alphaYM_eq_one,
   sigma_alphaPoincare_lt_alphaYM,
   sigma_alphaRH_lt_alphaYM,
   sigma_alphaHN_lt_alphaYM,
   sigma_alphaHodge_lt_alphaYM,
   sigma_alphaNP_lt_alphaYM,
   sigma_alphaBSD_lt_alphaYM,
   sigma_alphaP_lt_alphaYM,
   sigma_alphaQG_lt_alphaYM,
   sigma_alphaNS_lt_alphaYM⟩

/-! ## §4 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaYMCorpusMaximum.sigma_alphaYM_eq_one
#print axioms PrincipiaTractalis.AlphaYMCorpusMaximum.sigma_alphaHodge_lt_alphaYM
#print axioms PrincipiaTractalis.AlphaYMCorpusMaximum.alphaYM_unique_maximum_in_10_pillar_corpus

end PrincipiaTractalis.AlphaYMCorpusMaximum
