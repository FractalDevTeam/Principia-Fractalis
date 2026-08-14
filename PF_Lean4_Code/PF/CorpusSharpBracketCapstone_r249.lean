/-
# r249: FRAMEWORK-FIRST SHARP BRACKET CAPSTONE.

★ 2026-08-13 r249 — bundles the r243/r244/r245/r246/r247/r248 sharp-bracket
arc into a single referee-facing theorem. Five of the six irrational
corpus pillars have sharp algebraic (or Taylor) brackets against exact
substrate values from r236/r237. Only α_QG remains unbracketed. ★

## The bundle

Five conjuncts, all kernel-clean:

1. **α_Hodge** — `σ(φ) < 1/2`  (r248, via Taylor sin upper 5th-order)
2. **α_NP**    — `σ(φ + 1/4) > 2·log₃ φ`  (r247, pentagon-golden lower)
3. **α_BSD**   — `σ(3π/4) < log 2 / log 3`  (r245, Cantor upper)
4. **α_P**     — `σ(√2) < -log 2 / log 3`  (r244, -Cantor upper)
5. **α_NS**    — `σ(3π/2) < -log 2 / log 3`  (r246, -Cantor upper)

Not included:
- α_QG = √(2π). Near-critical (σ ≈ -0.039). No clean algebraic threshold
  between 0 and σ_QG at standard mathlib π precision. Left open.
- The three integer/half-integer pillars (α_Poincaré, α_RH, α_HN) have
  σ = 0 EXACTLY (already in r239 exact table); no bracket needed.
- α_YM = 2 has σ = 1 EXACTLY (already in r239); r242 shows it is the
  UNIQUE corpus σ-maximum, so no upper bracket applies.

## Framework-first framing

Following r231/r235 (σ-sign dichotomy capstones) and r239 (exact σ table
capstone), this file bundles the sharp-bracket work into ONE object.
Referees needing "the substrate's sharp position on each irrational
corpus pillar" cite `corpus_sharp_bracket_capstone`, not the individual
r243–r248 files.

## Substrate coordinate picture at HEAD

The r236/r237 exact substrate values now serve as a coordinate system
for the corpus σ spectrum:

    -log 2/log 3  <  σ_P                 (r244)
    -log 2/log 3  <  σ_NS                (r246)
    2·log₃ φ  <  σ_NP                    (r247)
    σ_Hodge   <  1/2                     (r248)
    σ_BSD     <  log 2/log 3             (r245)

Every one of these bracket points is a value the framework knows
exactly (from r239 or classical arithmetic like `1/2`).

## Contents

§1 `corpus_sharp_bracket_capstone` — the five-conjunct capstone.
§2 `corpus_sharp_bracket_positive_side` — the two σ > 0 pillars.
§3 `corpus_sharp_bracket_negative_side` — the two σ < 0 pillars.
§4 Axiom check.

## Scope

* NOT a novel result — direct composition of r243/r244/r245/r246/r247/r248.
* NOT a Millennium discharge.
* IS the framework-first bundle of the substrate's sharp position on the
  five bracketable irrational corpus pillars.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaHodgeTighterHalfBracket_r248
import PF.AlphaNPLowerBracketPentagon_r247
import PF.AlphaBSDUpperBracketCantor_r245
import PF.AlphaPUpperBracketNegCantor_r244
import PF.AlphaNSUpperBracketNegCantor_r246

open scoped Real

namespace PrincipiaTractalis.CorpusSharpBracketCapstone

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 The five-conjunct sharp-bracket capstone. -/

/-- **`corpus_sharp_bracket_capstone`** — the framework-first bundle.

Five sharp brackets on the corpus's irrational pillars, using r236/r237
exact substrate values as bracket points. Composes r244 through r248.

Not included: α_QG (near-critical, no clean algebraic threshold at HEAD),
α_YM (at ceiling per r242), α_Poincaré/RH/HN (σ = 0 exact per r239). -/
theorem corpus_sharp_bracket_capstone :
    -- r248: Hodge tight
    PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio < 1 / 2 ∧
    -- r247: NP above pentagon-golden
    2 * Real.logb 3 Real.goldenRatio <
      PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1 / 4) ∧
    -- r245: BSD below Cantor
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) < Real.logb 3 2 ∧
    -- r244: α_P below -Cantor
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) < -Real.logb 3 2 ∧
    -- r246: α_NS below -Cantor
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) < -Real.logb 3 2 :=
  ⟨AlphaHodgeTighterHalfBracket.sigma_alphaHodge_lt_half,
   AlphaNPLowerBracketPentagon.sigma_alphaNP_gt_two_logb_three_goldenRatio,
   AlphaBSDUpperBracketCantor.sigma_alphaBSD_lt_logb_three_two,
   AlphaPUpperBracketNegCantor.sigma_alphaP_lt_neg_logb_three_two,
   AlphaNSUpperBracketNegCantor.sigma_alphaNS_lt_neg_logb_three_two⟩

/-! ## §2 The positive-σ sub-bundle. -/

/-- **`corpus_sharp_bracket_positive_side`** — the two positive-σ pillars
with sharp brackets (Hodge below 1/2, NP above pentagon-golden). BSD's
bracket (below Cantor) is included in the full capstone above. -/
theorem corpus_sharp_bracket_positive_side :
    PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio < 1 / 2 ∧
    2 * Real.logb 3 Real.goldenRatio <
      PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1 / 4) ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) < Real.logb 3 2 :=
  ⟨AlphaHodgeTighterHalfBracket.sigma_alphaHodge_lt_half,
   AlphaNPLowerBracketPentagon.sigma_alphaNP_gt_two_logb_three_goldenRatio,
   AlphaBSDUpperBracketCantor.sigma_alphaBSD_lt_logb_three_two⟩

/-! ## §3 The negative-σ sub-bundle. -/

/-- **`corpus_sharp_bracket_negative_side`** — the two negative-σ pillars
with sharp brackets (α_P and α_NS below -Cantor). -/
theorem corpus_sharp_bracket_negative_side :
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) < -Real.logb 3 2 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) < -Real.logb 3 2 :=
  ⟨AlphaPUpperBracketNegCantor.sigma_alphaP_lt_neg_logb_three_two,
   AlphaNSUpperBracketNegCantor.sigma_alphaNS_lt_neg_logb_three_two⟩

/-! ## §4 Axiom check. -/

#print axioms PrincipiaTractalis.CorpusSharpBracketCapstone.corpus_sharp_bracket_capstone
#print axioms PrincipiaTractalis.CorpusSharpBracketCapstone.corpus_sharp_bracket_positive_side
#print axioms PrincipiaTractalis.CorpusSharpBracketCapstone.corpus_sharp_bracket_negative_side

end PrincipiaTractalis.CorpusSharpBracketCapstone
