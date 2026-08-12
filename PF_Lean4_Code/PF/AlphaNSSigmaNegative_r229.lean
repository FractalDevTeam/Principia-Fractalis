/-
# r229: α_NS = 3π/2 pillar — σ(α_NS) < 0 (envelope-decaying tier).

★ 2026-08-12 r229 — elevating the Navier–Stokes / cosmology pillar
(α_NS = 3π/2) via the sharp SIGN characterisation `σ(α_NS) < 0`. SEVENTH
σ-sign class formalised; second σ < 0 pillar after r225 (α_P). Uses the
same π-only bracket technique as r228 (α_BSD) plus r225's irrationality
tricks. ★

## Corpus tally after r229

    σ = +1     α_YM                                           (r224)
    σ > 0      α_Hodge, α_NP, α_BSD                           (r226, r227, r228)
    σ = 0      α_Poincaré, α_RH                               (r221)
    σ < 0      α_P (r225), α_NS (THIS)                        (envelope-decaying tier)
    pending    α_QG (near-critical, mixed π · √(2π) bracket)

**Eight of nine pillars now have σ-sign explicitly formalised**, leaving
only the near-critical α_QG = √(2π).

## The r76 doubling identity

From the substrate corpus: **α_NS = 2 · α_BSD** (r76, Lean
`substrate_I5_alpha_NS_eq_two_alpha_BSD`; also `PF/I5VortexDoubling*.lean`).
The r228 landing gave `σ(α_BSD) > 0`; r229 gives `σ(α_NS) < 0`. So:

    DOUBLING the α value FLIPS the σ sign (α_BSD > 0 → α_NS < 0).

This is a substrate observation, not a general fact — it holds specifically
because `π · α_BSD = 3π²/4` lands in (2π, 5π/2) where cos > 0, while
`π · α_NS = 3π²/2` lands in (4π + π/2, 5π) where cos < 0. The doubling of
α doubles the argument of cos, sending it through a half-period of the
underlying `cos_add_pi` symmetry.

## What the book says (insights from ch10, ch22, ch26)

- **ch22 (Navier–Stokes)**: vortex generation cascades ℓ_n = ℓ₀ · 3^{-n}
  with circulations Γ_n = Γ₀ · (-1)^n · 3^{-n/2}. The (-1)^n alternation
  is the ternary character's cos-oscillation at α_NS = 3π/2; the
  3^{-n/2} matches the substrate amplitude scale.
- **ch10 (hydrodynamic)**: consciousness regularization with π/10 dissipation.
- **ch26 (cosmological constant)**: Λ_eff = Λ₀ · exp[-∫ ch₂ · R_f(√(2π), |x|) dV]
  suppression mechanism. The SHAPE (envelope decay `a^σ` with σ < 0) is
  consistent; the RATE `g(t) ∝ t²` was refuted 2026-08-10 (DESI DR2,
  1156× error on `w₀`). r229 formalises the SIGN, not the rate.
- **Emergence dimension** log 2 / log 3 (ch22:289–290) — same base-3
  substrate that gives r212's `sigma = log₃ |1 + 2 cos(πα)|`.

Consistent with r221 + r222 + the 2026-08-12 cosmology doc §5: substrate-
consistent cosmology cannot be constant-amplitude at α_NS; needs
`a^{σ(α_NS)}` envelope with σ ≈ -1.308. r229 formalises the sign of that σ.

## The proof chain

α_NS = 3π/2. Then π · α_NS = 3π²/2.

1. π-only brackets: `4π + π/2 < 3π²/2 < 5π`. Both reduce to π-only linear
   inequalities via division: lower gives `π > 3` (`Real.pi_gt_three`),
   upper gives `π < 10/3` (from `Real.pi_lt_d2 : π < 3.15`).
2. Let `z := 3π²/2 - 4π`. Then `z ∈ (π/2, π)`.
3. cos(π · α_NS) = cos(z + 4π) = cos(z) via 2π periodicity twice.
4. `cos(z) < 0`: via `cos(π - w) = -cos(w)` with `w := π - z ∈ (0, π/2)`
   and `cos(w) > 0` on that interval.
5. `cos(π · α_NS) > -1`: irrationality of 3π/2 (r212's
   `irrational_three_pi_div_two`) rules out `cos = -1` which requires
   `α = 1 + 2k` odd integer (r212's `cos_pi_mul_eq_neg_one_iff`).
6. `1 + 2·cos(π · α_NS) ≠ 0`: irrationality rules out `cos = -1/2` which
   requires `α = 2k/3` rational (r212's `cos_pi_mul_eq_neg_half_imp_rational`).
7. `|1 + 2·cos(π · α_NS)| ∈ (0, 1)`: combines 4, 5, 6.
8. **`sigma_alphaNS_lt_zero`** via `Real.logb_neg`.
9. Elevated to r223: `SO_αNS_sigma_neg`.

## Contents

§0 Local `cos_add_four_pi` from two `cos_add_two_pi`.
§1 π-based brackets: `4π + π/2 < 3π²/2 < 5π`.
§2 `cos(π · α_NS) < 0` via 4π shift + `cos_pi_sub` chain.
§3 `cos(π · α_NS) > -1` via irrationality.
§4 `1 + 2·cos(π · α_NS) ≠ 0` via irrationality + r212 degenerate branch.
§5 `|1 + 2·cos(π · α_NS)| ∈ (0, 1)`.
§6 **`sigma_alphaNS_lt_zero`** — the named stone.
§7 Elevated to r223: `SO_αNS_sigma_neg`.
§8 Axiom check.

## Scope

* NOT a Navier–Stokes regularity discharge.
* NOT a cosmological constant / dark-energy discharge.
* NOT a substrate derivation of `α_NS = 3π/2` (that's r76's identity
  α_NS = 2·α_BSD, itself substrate-level).
* NOT a physical claim about fluids or cosmology; the rate `g(t)` for
  Λ_eff was refuted by DESI DR2 (r220 CHANGELOG 2026-08-10).
* IS the sharp SIGN characterisation of σ at the Navier–Stokes / cosmology
  pillar. IS a substrate consequence: envelope-decaying observable for
  α_NS, consistent with the book's suppression framings (shape, not rate).

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.SubstrateOscillator_r223

open scoped Real

namespace PrincipiaTractalis.AlphaNSSigmaNegative

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §0 Local: `cos_add_two_pi` and `cos_add_four_pi`. -/

lemma cos_add_two_pi (x : ℝ) : Real.cos (x + 2 * π) = Real.cos x := by
  have h : x + 2 * π = (x + π) + π := by ring
  rw [h, Real.cos_add_pi, Real.cos_add_pi]
  ring

lemma cos_add_four_pi (x : ℝ) : Real.cos (x + 4 * π) = Real.cos x := by
  have h : x + 4 * π = (x + 2 * π) + 2 * π := by ring
  rw [h, cos_add_two_pi, cos_add_two_pi]

/-! ## §1 π-only brackets on `π · α_NS = 3π²/2`. -/

/-- **`4π + π/2 < 3π²/2`**.  Reduces to `π > 3` via division by π. -/
lemma nine_pi_div_two_lt_pi_mul_alphaNS :
    4 * π + π / 2 < π * (3 * π / 2) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hpi_gt_three : 3 < π := Real.pi_gt_three
  nlinarith

/-- **`3π²/2 < 5π`**.  Reduces to `π < 10/3` via division by π; `π < 3.15 < 10/3`. -/
lemma pi_mul_alphaNS_lt_five_pi :
    π * (3 * π / 2) < 5 * π := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hpi_lt : π < 3.15 := Real.pi_lt_d2
  nlinarith

/-! ## §2 `cos(π · α_NS) < 0`. -/

/-- **`cos(π · α_NS) < 0`.**  Shift by `-4π` to land in (π/2, π); rewrite
`cos(z) = -cos(π - z)` with `π - z ∈ (0, π/2)` where cos > 0. -/
lemma cos_pi_mul_alphaNS_neg : Real.cos (π * (3 * π / 2)) < 0 := by
  set z := π * (3 * π / 2) - 4 * π with hz_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hz_gt_pi_div_two : π / 2 < z := by
    rw [hz_def]; linarith [nine_pi_div_two_lt_pi_mul_alphaNS]
  have hz_lt_pi : z < π := by
    rw [hz_def]; linarith [pi_mul_alphaNS_lt_five_pi]
  set w := π - z with hw_def
  have hw_pos : 0 < w := by rw [hw_def]; linarith
  have hw_lt : w < π / 2 := by rw [hw_def]; linarith
  have hw_gt_neg : -(π / 2) < w := by linarith
  have hcos_w_pos : 0 < Real.cos w :=
    Real.cos_pos_of_mem_Ioo ⟨hw_gt_neg, hw_lt⟩
  have hz_eq : z = π - w := by rw [hw_def]; ring
  have hcos_z : Real.cos z = -Real.cos w := by
    rw [hz_eq]; exact Real.cos_pi_sub w
  have heq : π * (3 * π / 2) = z + 4 * π := by rw [hz_def]; ring
  rw [heq, cos_add_four_pi, hcos_z]
  linarith

/-! ## §3 `cos(π · α_NS) > -1` via irrationality of 3π/2. -/

/-- **`cos(π · α_NS) > -1`.** Equality would give α_NS = 1 + 2k odd integer
via r212, contradicting `irrational_three_pi_div_two`. -/
lemma cos_pi_mul_alphaNS_gt_neg_one :
    -1 < Real.cos (π * (3 * π / 2)) := by
  have hge : -1 ≤ Real.cos (π * (3 * π / 2)) := Real.neg_one_le_cos _
  rcases lt_or_eq_of_le hge with h | h
  · exact h
  · exfalso
    have hEq : Real.cos (π * (3 * π / 2)) = -1 := h.symm
    obtain ⟨k, hk⟩ := (cos_pi_mul_eq_neg_one_iff (3 * π / 2)).mp hEq
    exact irrational_three_pi_div_two ⟨(1 + 2 * k : ℚ), by push_cast; linarith⟩

/-! ## §4 `1 + 2·cos(π · α_NS) ≠ 0` via irrationality. -/

/-- **`1 + 2·cos(π · α_NS) ≠ 0`.** Equality would give α_NS = 2k/3 rational
via r212's `cos_pi_mul_eq_neg_half_imp_rational`, contradicting
`irrational_three_pi_div_two`. -/
lemma one_add_two_cos_pi_mul_alphaNS_ne_zero :
    1 + 2 * Real.cos (π * (3 * π / 2)) ≠ 0 := by
  intro hEq
  obtain ⟨k, hk⟩ := cos_pi_mul_eq_neg_half_imp_rational (3 * π / 2) hEq
  exact irrational_three_pi_div_two ⟨(2 * k / 3 : ℚ), by push_cast; linarith⟩

/-! ## §5 `|1 + 2·cos(π · α_NS)| ∈ (0, 1)`. -/

lemma abs_one_add_two_cos_pi_mul_alphaNS_pos :
    0 < |1 + 2 * Real.cos (π * (3 * π / 2))| :=
  abs_pos.mpr one_add_two_cos_pi_mul_alphaNS_ne_zero

lemma abs_one_add_two_cos_pi_mul_alphaNS_lt_one :
    |1 + 2 * Real.cos (π * (3 * π / 2))| < 1 := by
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · linarith [cos_pi_mul_alphaNS_gt_neg_one]
  · linarith [cos_pi_mul_alphaNS_neg]

/-! ## §6 The named stone — `σ(α_NS) < 0`. -/

/-- **`sigma_alphaNS_lt_zero`** — the substrate sign at the Navier–Stokes /
cosmology pillar.

`σ(α_NS) < 0` where α_NS = 3π/2.  Consequence: the substrate observable at
α_NS has envelope `a^σ` with σ < 0 — amplitude DECAYS toward the past
(a → 0). Consistent with the book's ch10 consciousness regularization and
ch26 Λ_eff suppression framings (shape/sign, not rate — the rate was
refuted by DESI DR2 in 2026-08-10, see r220 CHANGELOG).

Combined with r212's `sigma_alphaNS_ne_zero_one`, σ(α_NS) ∈ (-∞, 0) \ {}
= (-∞, 0). Corpus value ≈ -1.308. -/
theorem sigma_alphaNS_lt_zero :
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) < 0 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  apply Real.logb_neg (by norm_num : (1 : ℝ) < 3)
  · exact abs_one_add_two_cos_pi_mul_alphaNS_pos
  · exact abs_one_add_two_cos_pi_mul_alphaNS_lt_one

/-! ## §7 Elevated to r223's `SubstrateOscillator`. -/

/-- **`SO_αNS_sigma_neg`** — the r223 `SubstrateOscillator` method form.

For every data-fit `A ≠ 0` and every `φ₀`, the α_NS substrate oscillator has
`sigma < 0`. Universal over data-fit. Companion to r225's
`SO_αP_sigma_neg` on the σ < 0 tier. -/
theorem SO_αNS_sigma_neg (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αNS A φ₀ hA).sigma < 0 := by
  show PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) < 0
  exact sigma_alphaNS_lt_zero

/-! ## §8 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.cos_add_two_pi
#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.cos_add_four_pi
#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.nine_pi_div_two_lt_pi_mul_alphaNS
#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.pi_mul_alphaNS_lt_five_pi
#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.cos_pi_mul_alphaNS_neg
#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.cos_pi_mul_alphaNS_gt_neg_one
#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.one_add_two_cos_pi_mul_alphaNS_ne_zero
#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.abs_one_add_two_cos_pi_mul_alphaNS_pos
#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.abs_one_add_two_cos_pi_mul_alphaNS_lt_one
#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.sigma_alphaNS_lt_zero
#print axioms PrincipiaTractalis.AlphaNSSigmaNegative.SO_αNS_sigma_neg

end PrincipiaTractalis.AlphaNSSigmaNegative
