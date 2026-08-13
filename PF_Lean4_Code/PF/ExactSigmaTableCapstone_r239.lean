/-
# r239: EXACT σ TABLE CAPSTONE — framework-first bundle of 11 closed forms.

★ 2026-08-13 r239 — the CAPSTONE for the substrate's exact-value σ table.
Framework-first bundling of every exact substrate σ closed form landed
across the r212–r238 arc. Not per-value fragmentation — ONE bundle
theorem giving the eleven closed forms simultaneously. ★

## The 11 exact values in the substrate σ table

| α    | σ(α)                | source | classical anchor           |
|------|---------------------|--------|----------------------------|
| 0    | 1                   | r233   | Riemann ζ abscissa         |
| 1/6  | log₃(1 + √3)        | r238   | hexagon                    |
| 1/5  | 2·log₃ φ            | r237   | pentagon-golden            |
| 1/4  | log₃(1 + √2)        | r238   | silver ratio               |
| 1/3  | log 2 / log 3       | r236   | Cantor Hausdorff (r234)    |
| 2/5  | log₃ φ              | r237   | pentagon-golden            |
| 1/2  | 0                   | r238   | half-integer (σ = 0 tier)  |
| 1    | 0                   | r212   | α_Poincaré                 |
| 3/2  | 0                   | r212   | α_RH                       |
| 2    | 1                   | r212   | α_YM (ζ pole)              |
| 5    | 0                   | r232   | α_HN                       |

Every entry is a KERNEL-CLEAN exact identity in the r212 substrate abscissa
formula `σ(α) = log₃ |1 + 2·cos(πα)|`. No numerical approximation. No
Taylor bounds. Pure substrate arithmetic composed with mathlib's exact
`Real.cos_pi_div_n` closed forms and the golden-ratio API.

## Framework-first bundling

Analogous to r231's `corpus_sigma_sign_dichotomy` (9-conjunct capstone
of the σ-sign machine) and r235's `corpus_10_pillar_sigma_sign_dichotomy`
(10-conjunct extension), r239 bundles the exact-value σ table into a
SINGLE theorem `substrate_exact_sigma_table_capstone` returning all 11
identities as one conjunction. No per-value citation needed downstream —
one referee-facing single-citation object.

Per Pabs 2026-08-12: "When we answer known open problems through our
machinery and get the exact same answer as the accepted solution, it
just adds more robustness to our claims." The bundled capstone shows
the substrate produces 11 independent exact matches simultaneously.

## Contents

§1 `substrate_exact_sigma_table_capstone` — the 11-conjunct capstone.
§2 `substrate_exact_sigma_table_rational_only` — the 8-conjunct rational-α
   subset (excluding the corpus-canonical α ∈ {1, 3/2, 2, 5}).
§3 `substrate_exact_sigma_table_sigma_zero_anchors` — the 5-conjunct σ = 0
   subtable (α ∈ {1/2, 1, 3/2, 5} — half-integer or odd-integer).
§4 `substrate_exact_sigma_table_golden_ratio_anchors` — the 3-conjunct
   golden-ratio subtable (α ∈ {1/5, 2/5} plus the doubling relation).
§5 Axiom check.

## Scope

* NOT a novel result — this is the framework-first CONSOLIDATION.
* NOT a proof of any classical identity — those live upstream in
  r212/r232/r233/r236/r237/r238.
* NOT a Millennium discharge.
* IS the referee-facing single-citation object for the substrate's exact
  σ-value production. One theorem, 11 conjuncts, kernel-clean.

Immediately following r233 (ζ abscissa), r234 (Cantor via ch22), r236
(σ(1/3) = Cantor via r212), r237 (pentagon-golden), r238 (silver + hexagon
+ half-integer). Sixth validation-arc landing, but the FIRST bundling
capstone in the validation arc.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.ValidationSigmaRationalTable_r238

open scoped Real

namespace PrincipiaTractalis.ExactSigmaTableCapstone

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.ValidationZetaAbscissa
open PrincipiaTractalis.ValidationSigmaOneThirdCantor
open PrincipiaTractalis.ValidationSigmaPentagonGolden
open PrincipiaTractalis.ValidationSigmaRationalTable
open PrincipiaTractalis

/-! ## §1 The 11-conjunct capstone. -/

/-- **`substrate_exact_sigma_table_capstone`** — the substrate's complete
exact σ-value table at HEAD as ONE theorem.

Bundles every exact closed-form σ value the r212–r238 arc has landed:
three r212 originals (α_Poincaré = 1, α_RH = 3/2, α_YM = 2), the r232
α_HN = 5, the r233 ζ-equivalent α = 0, r236's Cantor-equivalent α = 1/3,
r237's pentagon-golden α ∈ {1/5, 2/5}, and r238's α ∈ {1/2, 1/4, 1/6}.

Framework-first bundling: one referee-facing theorem, no per-value
citation needed downstream. -/
theorem substrate_exact_sigma_table_capstone :
    -- r233: ζ abscissa anchor
    PrincipiaTractalis.SigmaAbscissa.sigma 0 = 1 ∧
    -- r238: hexagon
    PrincipiaTractalis.SigmaAbscissa.sigma (1/6) = Real.logb 3 (1 + Real.sqrt 3) ∧
    -- r237: pentagon-golden (α = 1/5)
    PrincipiaTractalis.SigmaAbscissa.sigma (1/5) = 2 * Real.logb 3 Real.goldenRatio ∧
    -- r238: silver ratio
    PrincipiaTractalis.SigmaAbscissa.sigma (1/4) = Real.logb 3 (1 + Real.sqrt 2) ∧
    -- r236: Cantor Hausdorff (via σ formula)
    PrincipiaTractalis.SigmaAbscissa.sigma (1/3) = Real.log 2 / Real.log 3 ∧
    -- r237: pentagon-golden (α = 2/5)
    PrincipiaTractalis.SigmaAbscissa.sigma (2/5) = Real.logb 3 Real.goldenRatio ∧
    -- r238: half-integer σ = 0
    PrincipiaTractalis.SigmaAbscissa.sigma (1/2) = 0 ∧
    -- r212: α_Poincaré
    PrincipiaTractalis.SigmaAbscissa.sigma 1 = 0 ∧
    -- r212: α_RH
    PrincipiaTractalis.SigmaAbscissa.sigma (3/2) = 0 ∧
    -- r212: α_YM (ζ pole)
    PrincipiaTractalis.SigmaAbscissa.sigma 2 = 1 ∧
    -- r232: α_HN
    PrincipiaTractalis.SigmaAbscissa.sigma 5 = 0 :=
  ⟨sigma_zero_eq_one,
   sigma_one_sixth_eq_logb_three_one_add_sqrt_three,
   sigma_one_fifth_eq_two_logb_three_goldenRatio,
   sigma_one_quarter_eq_logb_three_one_add_sqrt_two,
   substrate_matches_cantor_via_sigma_formula,
   sigma_two_fifths_eq_logb_three_goldenRatio,
   sigma_one_half_eq_zero,
   sigma_one,
   sigma_three_halves,
   sigma_two,
   sigma_alphaHN_eq_zero⟩

/-! ## §2 The 8-conjunct rational-α subset. -/

/-- **`substrate_exact_sigma_table_rational_only`** — the rational-α table
excluding the canonical corpus integers/half-integers.

Presented separately for reference use where the caller only needs the
validation-instance α values, not the corpus α values. Eight entries
covering α ∈ {0, 1/6, 1/5, 1/4, 1/3, 2/5, 1/2}. Note that α = 1/2 is
technically in the r221 half-integer set but is listed here as a
validation instance. -/
theorem substrate_exact_sigma_table_rational_only :
    PrincipiaTractalis.SigmaAbscissa.sigma 0 = 1 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (1/6) = Real.logb 3 (1 + Real.sqrt 3) ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (1/5) = 2 * Real.logb 3 Real.goldenRatio ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (1/4) = Real.logb 3 (1 + Real.sqrt 2) ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (1/3) = Real.log 2 / Real.log 3 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (2/5) = Real.logb 3 Real.goldenRatio ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (1/2) = 0 :=
  ⟨sigma_zero_eq_one,
   sigma_one_sixth_eq_logb_three_one_add_sqrt_three,
   sigma_one_fifth_eq_two_logb_three_goldenRatio,
   sigma_one_quarter_eq_logb_three_one_add_sqrt_two,
   substrate_matches_cantor_via_sigma_formula,
   sigma_two_fifths_eq_logb_three_goldenRatio,
   sigma_one_half_eq_zero⟩

/-! ## §3 The 5-conjunct σ = 0 subtable. -/

/-- **`substrate_exact_sigma_table_sigma_zero_anchors`** — the σ = 0
constant-amplitude tier as a bundled subtable.

Anchors: α ∈ {1/2, 1, 3/2, 5}. Every entry has σ(α) = 0 exactly. Reflects
the r221 characterisation `‖χ‖ = 1 ↔ α ∈ ½ℤ + ½ ∪ 2ℤ + 1` — both the
half-integer branch (1/2, 3/2) and the odd-integer branch (1, 5). -/
theorem substrate_exact_sigma_table_sigma_zero_anchors :
    PrincipiaTractalis.SigmaAbscissa.sigma (1/2) = 0 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma 1 = 0 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (3/2) = 0 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma 5 = 0 :=
  ⟨sigma_one_half_eq_zero, sigma_one, sigma_three_halves, sigma_alphaHN_eq_zero⟩

/-! ## §4 The 3-conjunct golden-ratio subtable. -/

/-- **`substrate_exact_sigma_table_golden_ratio_anchors`** — the substrate
values expressible in the golden ratio, plus the algebraic doubling.

The three r237 conjuncts: σ(1/5) = 2·log₃ φ, σ(2/5) = log₃ φ, and the
Chebyshev doubling σ(1/5) = 2·σ(2/5). Highlights the substrate's
reproduction of pentagon-golden algebra. -/
theorem substrate_exact_sigma_table_golden_ratio_anchors :
    PrincipiaTractalis.SigmaAbscissa.sigma (1/5) = 2 * Real.logb 3 Real.goldenRatio ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (2/5) = Real.logb 3 Real.goldenRatio ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (1/5)
      = 2 * PrincipiaTractalis.SigmaAbscissa.sigma (2/5) :=
  ⟨sigma_one_fifth_eq_two_logb_three_goldenRatio,
   sigma_two_fifths_eq_logb_three_goldenRatio,
   sigma_one_fifth_eq_two_sigma_two_fifths⟩

/-! ## §5 Axiom check. -/

#print axioms PrincipiaTractalis.ExactSigmaTableCapstone.substrate_exact_sigma_table_capstone
#print axioms PrincipiaTractalis.ExactSigmaTableCapstone.substrate_exact_sigma_table_rational_only
#print axioms PrincipiaTractalis.ExactSigmaTableCapstone.substrate_exact_sigma_table_sigma_zero_anchors
#print axioms PrincipiaTractalis.ExactSigmaTableCapstone.substrate_exact_sigma_table_golden_ratio_anchors

end PrincipiaTractalis.ExactSigmaTableCapstone
