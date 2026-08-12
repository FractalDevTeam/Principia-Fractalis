/-
# r224: ‖1 + e^{iπα} + e^{2iπα}‖ = 3 ↔ α ∈ 2ℤ — the even-integer level set.

★ 2026-08-12 r224 — elevating the YM pillar (α_YM = 2) via the companion
level-set theorem to r221. `‖χ‖ = 3` characterises the σ = 1 tier (linear
amplitude growth), just as `‖χ‖ = 1` characterised the σ = 0 tier
(constant amplitude). Together with r212's degenerate branch (`‖χ‖ = 0`)
this closes ALL THREE integer-valued level sets of the ternary character
norm at rational α. ★

## What this file does

The r220 ternary character `χ(ω) = 1 + ω + ω²` has norm `|1 + 2 cos(πα)|`
at `ω = e^{iπα}` (r212's `norm_one_add_exp_add_exp_sq_pi_mul`). The three
integer values `‖χ‖` can take at rational α:

    ‖χ‖ = 0   ↔ cos(πα) = -1/2    ↔ α ∈ 2ℤ/3           (r212 degenerate branch)
    ‖χ‖ = 1   ↔ cos(πα) ∈ {0,-1}  ↔ α ∈ ½ℤ+½ ∪ 2ℤ+1   (r221)
    ‖χ‖ = 3   ↔ cos(πα) = 1       ↔ α ∈ 2ℤ            (THIS FILE)

The three level sets are pairwise disjoint at rational α. Every other value
`‖χ‖ ∈ ℝ \ {0, 1, 3}` requires irrational cos(πα), hence irrational α, since
`cos(πα)` is only rational at half-integers, odd integers, and the ⅔ℤ / 4ℤ
family.

## The YM pillar elevation

`α_YM = 2` sits in the `‖χ‖ = 3` level set (`k = 1` in `α = 2k`). The
substrate consequences that fall out:
- `σ(α_YM) = log₃ 3 = 1` (already r212's `sigma_two`).
- The r220 log-cosine observable at `α_YM` has envelope `a^1 = a` — linear
  amplitude growth.
- The `√3`-spaced zero structure from r222 still applies (the shift depends
  on `logFrequency`, not on the pillar).

`α_YM = 2` is the FLAGSHIP even-integer hit for `‖χ‖ = 3`. The other 8
canonical corpus alphas all miss (§6): the 6 irrational alphas via r212's
`sigma_alpha*_ne_zero_one` theorems, and the two constant-amplitude
rationals (α_Poincaré = 1, α_RH = 3/2) via `sigma_one = 0` and
`sigma_three_halves = 0`.

## Cross-pillar coverage r221 + r224

Between r221 (‖χ‖ = 1) and r224 (‖χ‖ = 3), all 6 Clay-axis alphas from
r212's table have their level-set membership explicitly formalised:

  α_YM       = 2      → ‖χ‖ = 3   (r224 HIT)
  α_RH       = 3/2    → ‖χ‖ = 1   (r221 HIT)
  α_Hodge    = φ      → ‖χ‖ ≠ 3   (r224 MISS)
  α_P        = √2     → ‖χ‖ ≠ 3   (r224 MISS)
  α_NP       = φ+1/4  → ‖χ‖ ≠ 3   (r224 MISS)
  α_BSD      = 3π/4   → ‖χ‖ ≠ 3   (r224 MISS)
  α_NS       = 3π/2   → ‖χ‖ ≠ 3   (r224 MISS, also r221 MISS)

Plus the ancillary anchors: α_Poincaré = 1 (r221 HIT), α_QG = √(2π) (r224 MISS).

## σ ↔ ‖χ‖ correspondence

r220's `sigma_eq_logb_norm_chi` implies:
- σ = 0 ↔ ‖χ‖ = 1  (r221 pattern)
- σ = 1 ↔ ‖χ‖ = 3  (this file, §5)

Section 5 makes the second correspondence explicit as
`sigma_eq_one_iff_chi_norm_eq_three`.

## Scope

* NOT a Yang–Mills mass gap discharge.
* NOT a substrate derivation of `α_YM = 2` (r212's scope note applies).
* NOT a physical claim about YM observables. Each level-set membership is
  a statement about ‖χ‖ on the unit circle, not about physical QCD.
* IS an exact level-set characterisation companion to r221, closing the
  three-value integer landscape `‖χ‖ ∈ {0, 1, 3}` at rational α; and IS
  the flagship YM-pillar elevation.

## Contents

§1 Real form:  `|1 + 2 cos(πα)| = 3 ↔ cos(πα) = 1`  (uses cos ≥ -1).
§2 Chi form:   `‖χ(e^{iπα})‖ = 3 ↔ cos(πα) = 1`.
§3 α-form:     **`chi_norm_three_iff_even_integer`** — `‖χ‖ = 3 ↔ α ∈ 2ℤ`.
§4 Corpus hits: `chi_norm_three_at_even_integer` (family), α_YM (k = 1),
   plus α = 4 (k = 2) and α = 0 (k = 0) non-vacuity witnesses.
§5 σ correspondence: `sigma_eq_one_iff_chi_norm_eq_three`.
§6 Corpus misses (via §5 + r212): α_Hodge, α_P, α_NP, α_QG, α_BSD, α_NS,
   plus α_Poincaré and α_RH.
§7 Disjointness with r221's `‖χ‖ = 1` level set.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.ChiNormUnity_r221

open scoped Real

namespace PrincipiaTractalis.ChiNormLevelThree

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.ChiNormUnity

/-! ## §1 The real closed form for `|1 + 2c| = 3` when `c = cos(πα)`. -/

/-- **The real closed form.**  `|1 + 2 · cos(πα)| = 3 ↔ cos(πα) = 1`.

The `1 + 2c = -3` branch of `|1 + 2c| = 3` forces `c = -2`, impossible
since `cos ≥ -1`. So only the `1 + 2c = +3` branch survives, giving
`cos(πα) = 1`. -/
theorem abs_one_add_two_cos_eq_three_iff (α : ℝ) :
    |1 + 2 * Real.cos (π * α)| = 3 ↔ Real.cos (π * α) = 1 := by
  constructor
  · intro h
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 3)).mp h with h' | h'
    · linarith
    · have hbnd := Real.neg_one_le_cos (π * α)
      linarith
  · intro h
    rw [h]; norm_num

/-! ## §2 The chi-norm form. -/

/-- **The chi-norm identity.**  `‖1 + e^{iπα} + e^{2iπα}‖ = 3 ↔ cos(πα) = 1`.
Off r212's `norm_one_add_exp_add_exp_sq_pi_mul` and §1. -/
theorem chi_norm_pi_mul_eq_three_iff (α : ℝ) :
    ‖1 + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I) ^ 2‖ = 3
      ↔ Real.cos (π * α) = 1 := by
  rw [norm_one_add_exp_add_exp_sq_pi_mul]
  exact abs_one_add_two_cos_eq_three_iff α

/-! ## §3 The α-classification (the named stone). -/

/-- **The named stone.**  `‖χ(e^{iπα})‖ = 3 ↔ α ∈ 2ℤ` (even integers).
Companion to r221's `chi_norm_unity_iff_half_or_odd_integer`.  Via r212's
`cos_pi_mul_eq_one_iff` (`cos(πα) = 1 ↔ ∃ k : ℤ, α = 2k`). -/
theorem chi_norm_three_iff_even_integer (α : ℝ) :
    ‖1 + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I) ^ 2‖ = 3
      ↔ ∃ k : ℤ, α = 2 * k := by
  rw [chi_norm_pi_mul_eq_three_iff]
  exact cos_pi_mul_eq_one_iff α

/-! ## §4 Corpus hits — every even integer, and α_YM = 2 as the flagship. -/

/-- **Every even integer hits `‖χ‖ = 3`** — infinite family. -/
theorem chi_norm_three_at_even_integer (k : ℤ) :
    ‖1 + Complex.exp (((π * ((2 * k : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * ((2 * k : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) ^ 2‖ = 3 := by
  rw [chi_norm_three_iff_even_integer]
  refine ⟨k, ?_⟩
  push_cast
  ring

/-- **α_YM = 2 hits** (even integer, k = 1) — the flagship. -/
theorem chi_norm_alphaYM :
    ‖1 + Complex.exp (((π * (2 : ℝ) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (2 : ℝ) : ℝ) : ℂ) * Complex.I) ^ 2‖ = 3 := by
  rw [chi_norm_three_iff_even_integer]
  exact ⟨1, by push_cast; ring⟩

/-- **α = 4 hits** (even integer, k = 2) — non-vacuity beyond α_YM. -/
theorem chi_norm_alpha_four :
    ‖1 + Complex.exp (((π * (4 : ℝ) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (4 : ℝ) : ℝ) : ℂ) * Complex.I) ^ 2‖ = 3 := by
  rw [chi_norm_three_iff_even_integer]
  exact ⟨2, by push_cast; ring⟩

/-- **α = 0 hits** (even integer, k = 0). -/
theorem chi_norm_alpha_zero :
    ‖1 + Complex.exp (((π * (0 : ℝ) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (0 : ℝ) : ℝ) : ℂ) * Complex.I) ^ 2‖ = 3 := by
  rw [chi_norm_three_iff_even_integer]
  exact ⟨0, by norm_num⟩

/-! ## §5 σ ↔ ‖χ‖ correspondence at the level of unity. -/

/-- **σ = 1 ↔ `‖χ‖ = 3`.**  The r212 abscissa hits the value 1 iff the
character norm hits 3 — the sigma-side version of §2's chi-norm identity. -/
theorem sigma_eq_one_iff_chi_norm_eq_three (α : ℝ) :
    PrincipiaTractalis.SigmaAbscissa.sigma α = 1
      ↔ ‖1 + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I)
           + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I) ^ 2‖ = 3 := by
  rw [sigma_eq_one_iff]
  exact (chi_norm_pi_mul_eq_three_iff α).symm

/-! ## §6 Corpus misses — the 6 irrational + the 2 constant-amplitude pillars. -/

/-- **α_Hodge = φ misses `‖χ‖ = 3`** (irrational). -/
theorem chi_norm_alphaHodge_ne_three :
    ‖1 + Complex.exp (((π * Real.goldenRatio : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * Real.goldenRatio : ℝ) : ℂ) * Complex.I) ^ 2‖ ≠ 3 :=
  mt (sigma_eq_one_iff_chi_norm_eq_three Real.goldenRatio).mpr
     sigma_alphaHodge_ne_zero_one.2

/-- **α_P = √2 misses `‖χ‖ = 3`** (irrational). -/
theorem chi_norm_alphaP_ne_three :
    ‖1 + Complex.exp (((π * Real.sqrt 2 : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * Real.sqrt 2 : ℝ) : ℂ) * Complex.I) ^ 2‖ ≠ 3 :=
  mt (sigma_eq_one_iff_chi_norm_eq_three (Real.sqrt 2)).mpr
     sigma_alphaP_ne_zero_one.2

/-- **α_NP = φ + 1/4 misses `‖χ‖ = 3`** (irrational). -/
theorem chi_norm_alphaNP_ne_three :
    ‖1 + Complex.exp (((π * (Real.goldenRatio + 1 / 4) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (Real.goldenRatio + 1 / 4) : ℝ) : ℂ) * Complex.I) ^ 2‖ ≠ 3 :=
  mt (sigma_eq_one_iff_chi_norm_eq_three (Real.goldenRatio + 1 / 4)).mpr
     sigma_alphaNP_ne_zero_one.2

/-- **α_QG = √(2π) misses `‖χ‖ = 3`** (irrational). -/
theorem chi_norm_alphaQG_ne_three :
    ‖1 + Complex.exp (((π * Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.I) ^ 2‖ ≠ 3 :=
  mt (sigma_eq_one_iff_chi_norm_eq_three (Real.sqrt (2 * π))).mpr
     sigma_alphaQG_ne_zero_one.2

/-- **α_BSD = 3π/4 misses `‖χ‖ = 3`** (irrational). -/
theorem chi_norm_alphaBSD_ne_three :
    ‖1 + Complex.exp (((π * (3 * π / 4) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (3 * π / 4) : ℝ) : ℂ) * Complex.I) ^ 2‖ ≠ 3 :=
  mt (sigma_eq_one_iff_chi_norm_eq_three (3 * π / 4)).mpr
     sigma_alphaBSD_ne_zero_one.2

/-- **α_NS = 3π/2 misses `‖χ‖ = 3`** (irrational cosmology axis). -/
theorem chi_norm_alphaNS_ne_three :
    ‖1 + Complex.exp (((π * (3 * π / 2) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (3 * π / 2) : ℝ) : ℂ) * Complex.I) ^ 2‖ ≠ 3 :=
  mt (sigma_eq_one_iff_chi_norm_eq_three (3 * π / 2)).mpr
     sigma_alphaNS_ne_zero_one.2

/-- **α_Poincaré = 1 misses `‖χ‖ = 3`** — odd integer, `σ = 0 ≠ 1`. -/
theorem chi_norm_alphaPoincare_ne_three :
    ‖1 + Complex.exp (((π * (1 : ℝ) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (1 : ℝ) : ℝ) : ℂ) * Complex.I) ^ 2‖ ≠ 3 :=
  mt (sigma_eq_one_iff_chi_norm_eq_three 1).mpr
     (by rw [sigma_one]; norm_num)

/-- **α_RH = 3/2 misses `‖χ‖ = 3`** — half-integer, `σ = 0 ≠ 1`. -/
theorem chi_norm_alphaRH_ne_three :
    ‖1 + Complex.exp (((π * (3 / 2 : ℝ) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (3 / 2 : ℝ) : ℝ) : ℂ) * Complex.I) ^ 2‖ ≠ 3 :=
  mt (sigma_eq_one_iff_chi_norm_eq_three (3 / 2)).mpr
     (by rw [sigma_three_halves]; norm_num)

/-! ## §7 Disjointness with r221's `‖χ‖ = 1` level set. -/

/-- **Level sets `‖χ‖ = 1` and `‖χ‖ = 3` are disjoint.**  No α satisfies both.

Trivially true from `1 ≠ 3`; still worth stating as a level-set fact for
clarity of the three-value integer landscape. -/
theorem chi_norm_one_and_three_disjoint (α : ℝ) :
    ¬ (‖1 + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I)
         + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I) ^ 2‖ = 1
       ∧ ‖1 + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I)
           + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I) ^ 2‖ = 3) := by
  rintro ⟨h1, h3⟩
  linarith

/-! ## §8 Axiom check. -/

#print axioms PrincipiaTractalis.ChiNormLevelThree.abs_one_add_two_cos_eq_three_iff
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_pi_mul_eq_three_iff
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_three_iff_even_integer
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_three_at_even_integer
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alphaYM
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alpha_four
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alpha_zero
#print axioms PrincipiaTractalis.ChiNormLevelThree.sigma_eq_one_iff_chi_norm_eq_three
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alphaHodge_ne_three
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alphaP_ne_three
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alphaNP_ne_three
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alphaQG_ne_three
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alphaBSD_ne_three
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alphaNS_ne_three
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alphaPoincare_ne_three
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_alphaRH_ne_three
#print axioms PrincipiaTractalis.ChiNormLevelThree.chi_norm_one_and_three_disjoint

end PrincipiaTractalis.ChiNormLevelThree
