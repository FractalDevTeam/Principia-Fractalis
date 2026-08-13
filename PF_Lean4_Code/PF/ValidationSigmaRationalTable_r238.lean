/-
# r238: VALIDATION — σ at 1/2, 1/4, 1/6 (half-integer σ = 0, silver ratio, hexagon).

★ 2026-08-13 r238 — the FIFTH validation landing. Extends the rational-α
σ table with three more exact substrate values:

    σ(1/2) = 0                              (half-integer, σ = 0 tier)
    σ(1/4) = log₃(1 + √2)                   (silver ratio: 1 + √2 = δ_S)
    σ(1/6) = log₃(1 + √3)                   (hexagon: cos(π/6) = √3/2)

Combined with r236 (σ(1/3) = log₃ 2 = Cantor dim) and r237
(σ(1/5) = 2·log₃ φ, σ(2/5) = log₃ φ), this fills out the σ table for
rational α ∈ {1/2, 1/3, 1/4, 1/5, 2/5, 1/6} — the six "small rational
denominators" with clean cosine closed forms. ★

## The three values

**α = 1/2**: `cos(π · (1/2)) = cos(π/2) = 0` via mathlib
`Real.cos_pi_div_two`. Then
    1 + 2·0 = 1
    σ(1/2) = log₃|1| = log₃ 1 = 0.

σ = 0 constant-amplitude tier. Half-integer, hits r221's
`‖χ‖ = 1 ↔ α ∈ ½ℤ + ½ ∪ 2ℤ + 1` (α = 1/2 = 1/2 + 0, k = 0 branch).

**α = 1/4**: `cos(π · (1/4)) = cos(π/4) = √2/2` via mathlib
`Real.cos_pi_div_four`. Then
    1 + 2·(√2/2) = 1 + √2 = δ_S  (silver ratio)
    σ(1/4) = log₃(1 + √2) = log₃ δ_S.

The silver ratio `δ_S = 1 + √2` satisfies `δ_S² = 2·δ_S + 1`
(analogue of `φ² = φ + 1`).

**α = 1/6**: `cos(π · (1/6)) = cos(π/6) = √3/2` via mathlib
`Real.cos_pi_div_six`. Then
    1 + 2·(√3/2) = 1 + √3
    σ(1/6) = log₃(1 + √3).

Hexagon algebra. Note `(1 + √3)/2` is not a named metallic ratio, but
`1 + √3 ≈ 2.732` and `log₃(1 + √3) ≈ 0.914` — close to but distinct
from σ(α_YM) = 1.

## Why this matters

Six exact substrate values now form a rational-α σ table:

| α    | σ closed form           | classical name          |
|------|-------------------------|-------------------------|
| 1/2  | 0                       | σ = 0 tier (r221 hit)   |
| 1/3  | log₃ 2 = log 2 / log 3  | Cantor Hausdorff (r236) |
| 1/4  | log₃(1 + √2)            | silver ratio (r238)     |
| 1/5  | 2·log₃ φ                | golden pentagon (r237)  |
| 2/5  | log₃ φ                  | golden pentagon (r237)  |
| 1/6  | log₃(1 + √3)            | hexagon (r238)          |

Every entry uses only mathlib's exact `Real.cos_pi_div_n` values plus
r212's σ formula. No numerical approximation. No Taylor bounds. Pure
substrate arithmetic reproducing classical closed forms.

Per doctrine (Pabs 2026-08-12): "When we answer known open problems
through our machinery and get the exact same answer as the accepted
solution, it just adds more robustness to our claims." The rational-α
σ table extends this pattern to six independent closed-form matches.

## Contents

§1 `sigma_one_half_eq_zero` — σ(1/2) = 0.
§2 `sigma_one_quarter_eq_logb_three_one_add_sqrt_two` — σ(1/4) silver.
§3 `sigma_one_sixth_eq_logb_three_one_add_sqrt_three` — σ(1/6) hexagon.
§4 `SO_αHalf`, `SO_αSilver`, `SO_αHexagon` — SubstrateOscillator instances.
§5 `substrate_rational_alpha_sigma_table_r238_extension` — named claim.
§6 Axiom check.

## Scope

* NOT novel results — all three cos values are classical (Euclidean /
  mathlib basic).
* NOT proofs of any classical identity.
* NOT Millennium discharges.
* IS extension of the substrate rational-α σ table by three exact
  values, each using r212's σ formula on a mathlib-native cos identity.

Fifth validation landing after r233, r234, r236, r237.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.ValidationSigmaPentagonGolden_r237

open scoped Real

namespace PrincipiaTractalis.ValidationSigmaRationalTable

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 `σ(1/2) = 0` (half-integer, constant-amplitude tier). -/

/-- **`sigma_one_half_eq_zero`** — the half-integer σ = 0 anchor.

Via `Real.cos_pi_div_two : cos(π/2) = 0`. Then `1 + 2·0 = 1` and
`log₃|1| = log₃ 1 = 0`. Fits r221's `‖χ‖ = 1 ↔ α ∈ ½ℤ + ½ ∪ 2ℤ + 1`
characterisation at the k = 0 branch of ½ℤ + ½. -/
theorem sigma_one_half_eq_zero :
    PrincipiaTractalis.SigmaAbscissa.sigma (1/2) = 0 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hcos : Real.cos (π * (1/2)) = 0 := by
    rw [show π * (1/2) = π / 2 by ring]
    exact Real.cos_pi_div_two
  rw [hcos]
  norm_num

/-! ## §2 `σ(1/4) = log₃(1 + √2)` (silver-ratio value). -/

/-- **`sigma_one_quarter_eq_logb_three_one_add_sqrt_two`** — the silver
ratio σ value.

Via `Real.cos_pi_div_four : cos(π/4) = √2/2`. Then
`1 + 2·(√2/2) = 1 + √2`, the silver ratio. Positivity of `1 + √2`
handled via `Real.sqrt_nonneg`. -/
theorem sigma_one_quarter_eq_logb_three_one_add_sqrt_two :
    PrincipiaTractalis.SigmaAbscissa.sigma (1/4) = Real.logb 3 (1 + Real.sqrt 2) := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hcos : Real.cos (π * (1/4)) = Real.sqrt 2 / 2 := by
    rw [show π * (1/4) = π / 4 by ring]
    exact Real.cos_pi_div_four
  rw [hcos]
  have hpos : (0 : ℝ) < 1 + Real.sqrt 2 := by
    have := Real.sqrt_nonneg 2; linarith
  have hval : (1 : ℝ) + 2 * (Real.sqrt 2 / 2) = 1 + Real.sqrt 2 := by ring
  rw [hval, abs_of_pos hpos]

/-! ## §3 `σ(1/6) = log₃(1 + √3)` (hexagon value). -/

/-- **`sigma_one_sixth_eq_logb_three_one_add_sqrt_three`** — the hexagon
σ value.

Via `Real.cos_pi_div_six : cos(π/6) = √3/2`. Then `1 + 2·(√3/2) = 1 + √3`.
Positivity via `Real.sqrt_nonneg`. -/
theorem sigma_one_sixth_eq_logb_three_one_add_sqrt_three :
    PrincipiaTractalis.SigmaAbscissa.sigma (1/6) = Real.logb 3 (1 + Real.sqrt 3) := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hcos : Real.cos (π * (1/6)) = Real.sqrt 3 / 2 := by
    rw [show π * (1/6) = π / 6 by ring]
    exact Real.cos_pi_div_six
  rw [hcos]
  have hpos : (0 : ℝ) < 1 + Real.sqrt 3 := by
    have := Real.sqrt_nonneg 3; linarith
  have hval : (1 : ℝ) + 2 * (Real.sqrt 3 / 2) = 1 + Real.sqrt 3 := by ring
  rw [hval, abs_of_pos hpos]

/-! ## §4 The corpus instances. -/

/-- **`SO_αHalf`** — SubstrateOscillator at α = 1/2.

The half-integer case: substrate σ = 0. Extends the constant-amplitude
tier (α_Poincaré = 1, α_RH = 3/2, α_HN = 5) with the half-integer α = 1/2.
Not a Millennium pillar. -/
noncomputable def SO_αHalf (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := 1/2, A := A, φ₀ := φ₀, hA := hA }

/-- **`SO_αSilver`** — SubstrateOscillator at α = 1/4.

The silver-ratio case: substrate σ = log₃(1 + √2) = log₃ δ_S. Validation
instance. Not a Millennium pillar. -/
noncomputable def SO_αSilver (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := 1/4, A := A, φ₀ := φ₀, hA := hA }

/-- **`SO_αHexagon`** — SubstrateOscillator at α = 1/6.

The hexagon case: substrate σ = log₃(1 + √3). Validation instance. Not
a Millennium pillar. -/
noncomputable def SO_αHexagon (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := 1/6, A := A, φ₀ := φ₀, hA := hA }

/-- **`SO_αHalf_sigma_eq_zero`** — elevated form. -/
theorem SO_αHalf_sigma_eq_zero (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αHalf A φ₀ hA).sigma = 0 := by
  show PrincipiaTractalis.SigmaAbscissa.sigma (1/2) = 0
  exact sigma_one_half_eq_zero

/-- **`SO_αSilver_sigma`** — elevated form. -/
theorem SO_αSilver_sigma (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αSilver A φ₀ hA).sigma = Real.logb 3 (1 + Real.sqrt 2) := by
  show PrincipiaTractalis.SigmaAbscissa.sigma (1/4) = Real.logb 3 (1 + Real.sqrt 2)
  exact sigma_one_quarter_eq_logb_three_one_add_sqrt_two

/-- **`SO_αHexagon_sigma`** — elevated form. -/
theorem SO_αHexagon_sigma (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αHexagon A φ₀ hA).sigma = Real.logb 3 (1 + Real.sqrt 3) := by
  show PrincipiaTractalis.SigmaAbscissa.sigma (1/6) = Real.logb 3 (1 + Real.sqrt 3)
  exact sigma_one_sixth_eq_logb_three_one_add_sqrt_three

/-! ## §5 Named table-extension claim. -/

/-- **`substrate_rational_alpha_sigma_table_r238_extension`** — the named
paired claim.

The three r238 additions to the rational-α σ table:
- σ(1/2) = 0
- σ(1/4) = log₃(1 + √2)   (silver ratio)
- σ(1/6) = log₃(1 + √3)   (hexagon)

Extends r236 (σ(1/3) = log₃ 2, Cantor Hausdorff dim) and r237
(σ(1/5) = 2·log₃ φ, σ(2/5) = log₃ φ, pentagon golden) to a six-entry
substrate rational-α table. All entries kernel-clean via mathlib's
`Real.cos_pi_div_n` values + r212's σ formula. -/
theorem substrate_rational_alpha_sigma_table_r238_extension :
    PrincipiaTractalis.SigmaAbscissa.sigma (1/2) = 0 ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (1/4) = Real.logb 3 (1 + Real.sqrt 2) ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (1/6) = Real.logb 3 (1 + Real.sqrt 3) :=
  ⟨sigma_one_half_eq_zero,
   sigma_one_quarter_eq_logb_three_one_add_sqrt_two,
   sigma_one_sixth_eq_logb_three_one_add_sqrt_three⟩

/-! ## §6 Axiom check. -/

#print axioms PrincipiaTractalis.ValidationSigmaRationalTable.sigma_one_half_eq_zero
#print axioms PrincipiaTractalis.ValidationSigmaRationalTable.sigma_one_quarter_eq_logb_three_one_add_sqrt_two
#print axioms PrincipiaTractalis.ValidationSigmaRationalTable.sigma_one_sixth_eq_logb_three_one_add_sqrt_three
#print axioms PrincipiaTractalis.ValidationSigmaRationalTable.substrate_rational_alpha_sigma_table_r238_extension

end PrincipiaTractalis.ValidationSigmaRationalTable
