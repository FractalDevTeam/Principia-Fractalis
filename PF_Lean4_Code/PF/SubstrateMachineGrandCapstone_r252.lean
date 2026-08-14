/-
# r252: SUBSTRATE MACHINE GRAND CAPSTONE.

★ 2026-08-13 r252 — the framework-first GRAND CAPSTONE for the substrate σ
machine at HEAD. Bundles every layer of the substrate machine's corpus-level
content into ONE referee-facing conjunctive theorem:

- r239 exact σ table (11 closed forms)
- r240 σ structural symmetries (3 universal facts)
- r241 σ universal ceiling with 2ℤ characterization
- r242 α_YM unique corpus σ-max
- r251 6-conjunct sharp-bracket capstone (all irrational corpus pillars)

Every conjunct is kernel-clean and traceable to a specific r212–r251 landing.

## What this capstone represents

The substrate σ machine, applied to the 10-canonical corpus at HEAD, knows:
(1) exact closed-form values for the four σ = 0 pillars, α_YM at σ = 1,
and seven additional validation-instance rationals; (2) three universal
symmetries (period 2, evenness, integer double-shift); (3) a universal
ceiling σ ≤ 1 with equality iff α ∈ 2ℤ; (4) that α_YM = 2 is the unique
corpus σ-maximum; and (5) sharp brackets on every irrational corpus pillar
tying them to substrate exact values (Cantor Hausdorff, pentagon-golden,
half-integer discriminant, and rational-approximation thresholds).

## Framework-first framing

Per the anti-fragmentation doctrine (`principia_FRAMEWORK_FIRST.md`), the
substrate machine's corpus-level position should be presentable as ONE
object, not fragmented per pillar or per layer. r252 IS that object.

A referee asking "what does the substrate know about its own α-skeleton?"
cites `substrate_machine_grand_capstone`. No per-file drill-down. No
per-axis fragmentation.

## Contents

§1 `substrate_machine_grand_capstone` — the five-conjunct bundle of the
   framework-first capstones r239 + r240 + r241 + r242 + r251.
§2 Axiom check.

## Scope

* NOT novel — direct composition of upstream capstones.
* NOT a Millennium discharge.
* NOT a claim exceeding what r236–r251 already prove individually.
* IS the framework-first GRAND CAPSTONE: everything the substrate σ
  machine knows about the corpus at HEAD, in ONE theorem.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.ExactSigmaTableCapstone_r239
import PF.SigmaSymmetries_r240
import PF.SigmaUpperBound_r241
import PF.AlphaYMCorpusMaximum_r242
import PF.CorpusSharpBracketComplete_r251

open scoped Real

namespace PrincipiaTractalis.SubstrateMachineGrandCapstone

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 The five-conjunct grand capstone. -/

/-- **`substrate_machine_grand_capstone`** — the framework-first GRAND CAPSTONE.

Bundles every layer of the substrate σ machine's corpus-level knowledge at
HEAD into ONE conjunctive theorem:

1. r239 exact σ-value table (11 closed forms).
2. r240 σ structural symmetries (period 2, evenness, integer shift).
3. r241 σ ≤ 1 universal ceiling with 2ℤ characterization.
4. r242 α_YM = 2 unique corpus σ-max.
5. r251 sharp brackets on all six irrational corpus pillars.

The referee-facing single-citation object for the substrate σ machine's
complete corpus-level content. -/
theorem substrate_machine_grand_capstone :
    -- Layer 1: exact σ table (r239, 11 conjuncts).
    (PrincipiaTractalis.SigmaAbscissa.sigma 0 = 1 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (1/6) = Real.logb 3 (1 + Real.sqrt 3) ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (1/5) = 2 * Real.logb 3 Real.goldenRatio ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (1/4) = Real.logb 3 (1 + Real.sqrt 2) ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (1/3) = Real.log 2 / Real.log 3 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (2/5) = Real.logb 3 Real.goldenRatio ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (1/2) = 0 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma 1 = 0 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (3/2) = 0 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma 2 = 1 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma 5 = 0) ∧
    -- Layer 2: σ structural symmetries (r240, 3 conjuncts).
    ((∀ α : ℝ, PrincipiaTractalis.SigmaAbscissa.sigma (α + 2)
        = PrincipiaTractalis.SigmaAbscissa.sigma α) ∧
     (∀ α : ℝ, PrincipiaTractalis.SigmaAbscissa.sigma (-α)
        = PrincipiaTractalis.SigmaAbscissa.sigma α) ∧
     (∀ (α : ℝ) (k : ℤ), PrincipiaTractalis.SigmaAbscissa.sigma (α + 2 * k)
        = PrincipiaTractalis.SigmaAbscissa.sigma α)) ∧
    -- Layer 3: universal ceiling (r241, 3 conjuncts).
    ((∀ α : ℝ, PrincipiaTractalis.SigmaAbscissa.sigma α ≤ 1) ∧
     (∀ α : ℝ, PrincipiaTractalis.SigmaAbscissa.sigma α < 1 ↔ Real.cos (π * α) ≠ 1) ∧
     (∀ α : ℝ, PrincipiaTractalis.SigmaAbscissa.sigma α = 1 ↔ ∃ k : ℤ, α = 2 * k)) ∧
    -- Layer 4: α_YM unique corpus max (r242, 10 conjuncts).
    (PrincipiaTractalis.SigmaAbscissa.sigma 2 = 1 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma 1 <
       PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (3/2) <
       PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma 5 <
       PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio <
       PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1/4) <
       PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) <
       PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) <
       PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) <
       PrincipiaTractalis.SigmaAbscissa.sigma 2 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) <
       PrincipiaTractalis.SigmaAbscissa.sigma 2) ∧
    -- Layer 5: sharp brackets on all six irrational pillars (r251, 6 conjuncts).
    (PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio < 1 / 2 ∧
     2 * Real.logb 3 Real.goldenRatio <
       PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1 / 4) ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) < Real.logb 3 2 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) < -Real.logb 3 2 ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) < Real.logb 3 (49 / 50) ∧
     PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) < -Real.logb 3 2) :=
  ⟨ExactSigmaTableCapstone.substrate_exact_sigma_table_capstone,
   SigmaSymmetries.sigma_symmetries_capstone,
   SigmaUpperBound.substrate_max_envelope_characterization,
   AlphaYMCorpusMaximum.alphaYM_unique_maximum_in_10_pillar_corpus,
   CorpusSharpBracketComplete.corpus_sharp_bracket_complete_capstone⟩

/-! ## §2 Axiom check. -/

#print axioms PrincipiaTractalis.SubstrateMachineGrandCapstone.substrate_machine_grand_capstone

end PrincipiaTractalis.SubstrateMachineGrandCapstone
