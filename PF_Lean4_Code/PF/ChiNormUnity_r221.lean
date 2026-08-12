/-
# r221: ‖1 + e^{iπα} + e^{2iπα}‖ = 1 ↔ α ∈ half-integers ∪ odd-integers

★ 2026-08-12 r221 — the amplitude-constraint closed form for the r220
substrate-consistent log-cosine ansatz. Companion to r212. ★

## Where this comes from

r220 (`PF/LogPeriodicity_r220.lean`) pins the log-frequency `2π / ln 3` on any
substrate-consistent oscillation with no free parameter. r219
(`PF/EquationOfStateBridge_r219.lean`) turns that into an observable via
`w(a) = -1 + g(a) / (3 H(a))`. The most parsimonious substrate-consistent
ansatz is the log-cosine

    g(a) = A · a^{σ(α)} · cos( (2π / ln 3) · ln a + φ₀ )

where `σ(α) = log₃ ‖χ(e^{iπα})‖` (r212) is the amplitude exponent forced by
the substrate. The **constant-amplitude** case (no `a^σ` envelope) is exactly
`σ = 0`, i.e. `‖χ(e^{iπα})‖ = 1`.

This file states and proves the closed form of that condition:

    ‖1 + e^{iπα} + e^{2iπα}‖ = 1
      ↔ cos(πα) = 0 ∨ cos(πα) = -1
      ↔ (∃ k : ℤ, α = 1/2 + k) ∨ (∃ k : ℤ, α = 1 + 2k)
      i.e. α is a half-integer or an odd integer.

The proof is one rewrite off r212's `norm_one_add_exp_add_exp_sq_pi_mul` plus
the elementary `|1 + 2c| = 1 ↔ c ∈ {0, -1}`. Unlike r212's `sigma_eq_zero_iff`
this has NO degenerate branch: `|1 + 2c| = 1` excludes `c = -1/2`, so the
`Real.logb b 0 = 0` pitfall that forced the three-branch form of
`sigma_eq_zero_iff_full` cannot occur here.

## Corpus application

Among r212's nine canonical corpus alphas, exactly two satisfy `‖χ‖ = 1`:

  HIT:  α_Poincaré = 1     (odd integer, k = 0 in α = 1 + 2k)
  HIT:  α_RH       = 3/2   (half-integer, k = 1 in α = 1/2 + k)
  MISS: α_YM       = 2     (cos(2π) = 1 ∉ {0, -1})
  MISS: α_Hodge    = φ     (irrational)
  MISS: α_P        = √2    (irrational)
  MISS: α_NP       = φ+1/4 (irrational)
  MISS: α_QG       = √(2π) (irrational)
  MISS: α_BSD      = 3π/4  (irrational)
  MISS: α_NS       = 3π/2  (irrational — the cosmology axis)

The three exact hits are exactly r212's three `sigma = 0` hits at rational
argument (`sigma_one`, `sigma_three_halves`, and — extending — every odd
integer).

## The cosmology consequence

α_NS = 3π/2 MISSES. So under the substrate the cosmology axis does NOT
support a constant-amplitude log-cosine; it requires the envelope

    g(a) = A · a^{σ(α_NS)} · cos( (2π / ln 3) · ln a + φ₀ )

with `σ(α_NS) = -1.308…` (already computed via `sigma_alphaNS_ne_zero_one`).
The next-zero prediction at `z ≈ 1.44` from
`docs/COSMOLOGY_LOGPERIODIC_G_2026-08-12.md` §2 is a **phase** statement and
is unchanged by the envelope; the **amplitude** grows toward the past.

## Scope

* NOT a discharge of any Millennium problem.
* NOT a substrate derivation of `g`, `A`, or `φ₀`.
* NOT a resolution of the DESI–CMB tension.
* NOT a physical claim about dark energy — the file speaks about `‖χ‖` on
  the unit circle only.
* IS an exact algebraic identity plus its α-classification, plus the
  three hits / one explicit corpus miss for α_NS.

## Contents

§1 The real closed form `|1 + 2c| = 1 ↔ c ∈ {0, -1}`.
§2 The unity identity `‖χ(e^{iπα})‖ = 1 ↔ cos(πα) ∈ {0, -1}`.
§3 The α-form `chi_norm_unity_iff_half_or_odd_integer` (the named stone
   from the queue).
§4 Corpus hits: α = 1, α = 3/2, α = 5, and the general
   `chi_norm_unity_at_odd_integer` / `chi_norm_unity_at_half_integer`.
§5 Corpus miss: α_NS = 3π/2 excluded via `irrational_three_pi_div_two`.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.SigmaAbscissa_r212

open scoped Real

namespace PrincipiaTractalis.ChiNormUnity

open PrincipiaTractalis.SigmaAbscissa

/-! ## §1 The real closed form -/

/-- **The two-line algebraic identity.** `|1 + 2c| = 1 ↔ c = 0 ∨ c = -1`.

Proof: `|1 + 2c| = 1 ↔ 1 + 2c = ±1`; the `+1` branch gives `c = 0`, the `-1`
branch gives `c = -1`. -/
theorem abs_one_add_two_mul_eq_one_iff (c : ℝ) :
    |1 + 2 * c| = 1 ↔ c = 0 ∨ c = -1 := by
  constructor
  · intro h
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h with h' | h'
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · rw [h]; norm_num
    · rw [h]; norm_num

/-! ## §2 The unity identity for `χ(e^{iπα})` -/

/-- **The unity identity.**  `‖1 + e^{iπα} + e^{2iπα}‖ = 1 ↔ cos(πα) ∈ {0, -1}`.

Follows from r212's `norm_one_add_exp_add_exp_sq_pi_mul` (which gives
`‖·‖ = |1 + 2 cos(πα)|`) plus §1.  No non-degeneracy hypothesis is required:
`|1 + 2c| = 1` implies `1 + 2c ∈ {±1}` which excludes `c = -1/2`, so r212's
`sigma_eq_zero_iff_full` degenerate branch is impossible at norm-one. -/
theorem chi_norm_pi_mul_eq_one_iff (α : ℝ) :
    ‖1 + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I) ^ 2‖ = 1
      ↔ Real.cos (π * α) = 0 ∨ Real.cos (π * α) = -1 := by
  rw [norm_one_add_exp_add_exp_sq_pi_mul]
  exact abs_one_add_two_mul_eq_one_iff _

/-! ## §3 The α-classification (the named stone) -/

/-- **The named stone.**  `‖χ(e^{iπα})‖ = 1` iff α is a half-integer
`(1/2 + k)` or an odd integer `(1 + 2k)`.

This is the amplitude-constraint closed form referenced in
`docs/COSMOLOGY_LOGPERIODIC_G_2026-08-12.md` §5 and queued there as
`chi_norm_unity_iff_half_or_odd_integer`. Elementary, kernel-clean,
mathlib-native. -/
theorem chi_norm_unity_iff_half_or_odd_integer (α : ℝ) :
    ‖1 + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I) ^ 2‖ = 1
      ↔ (∃ k : ℤ, α = 1 / 2 + k) ∨ (∃ k : ℤ, α = 1 + 2 * k) := by
  rw [chi_norm_pi_mul_eq_one_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ((cos_pi_mul_eq_zero_iff α).mp h)
    · exact Or.inr ((cos_pi_mul_eq_neg_one_iff α).mp h)
  · rintro (h | h)
    · exact Or.inl ((cos_pi_mul_eq_zero_iff α).mpr h)
    · exact Or.inr ((cos_pi_mul_eq_neg_one_iff α).mpr h)

/-! ## §4 Corpus hits — the three exact α that satisfy `‖χ‖ = 1` -/

/-- Every odd integer hits `‖χ‖ = 1`. -/
theorem chi_norm_unity_at_odd_integer (k : ℤ) :
    ‖1 + Complex.exp (((π * ((1 : ℝ) + 2 * k) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * ((1 : ℝ) + 2 * k) : ℝ) : ℂ) * Complex.I) ^ 2‖ = 1 := by
  rw [chi_norm_unity_iff_half_or_odd_integer]
  exact Or.inr ⟨k, rfl⟩

/-- Every half-integer hits `‖χ‖ = 1`. -/
theorem chi_norm_unity_at_half_integer (k : ℤ) :
    ‖1 + Complex.exp (((π * ((1 / 2 : ℝ) + k) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * ((1 / 2 : ℝ) + k) : ℝ) : ℂ) * Complex.I) ^ 2‖ = 1 := by
  rw [chi_norm_unity_iff_half_or_odd_integer]
  exact Or.inl ⟨k, rfl⟩

/-- **α_Poincaré = 1** hits (odd integer, k = 0). -/
theorem chi_norm_alphaPoincare :
    ‖1 + Complex.exp (((π * (1 : ℝ) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (1 : ℝ) : ℝ) : ℂ) * Complex.I) ^ 2‖ = 1 := by
  rw [chi_norm_unity_iff_half_or_odd_integer]
  exact Or.inr ⟨0, by push_cast; ring⟩

/-- **α_RH = 3/2** hits (half-integer, k = 1). -/
theorem chi_norm_alphaRH :
    ‖1 + Complex.exp (((π * (3 / 2 : ℝ) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (3 / 2 : ℝ) : ℝ) : ℂ) * Complex.I) ^ 2‖ = 1 := by
  rw [chi_norm_unity_iff_half_or_odd_integer]
  exact Or.inl ⟨1, by push_cast; ring⟩

/-- **α = 5** hits (odd integer, k = 2) — a second odd-integer instance beyond
Poincaré = 1, exhibiting non-vacuity of the odd-integer branch. -/
theorem chi_norm_alpha_five :
    ‖1 + Complex.exp (((π * (5 : ℝ) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (5 : ℝ) : ℝ) : ℂ) * Complex.I) ^ 2‖ = 1 := by
  rw [chi_norm_unity_iff_half_or_odd_integer]
  exact Or.inr ⟨2, by push_cast; ring⟩

/-! ## §5 Corpus miss — α_NS = 3π/2 (the cosmology axis) -/

/-- **α_NS = 3π/2 misses `‖χ‖ = 1`.**

Both branches of the α-classification (half-integers and odd integers) are
rational; `3π/2` is irrational (r212's `irrational_three_pi_div_two`), so it
sits in neither branch.

Consequence: the substrate-consistent log-cosine ansatz at the cosmology `α`
cannot be constant-amplitude — it needs the `a^{σ(α_NS)}` envelope with
`σ(α_NS) = log₃ ‖χ(e^{iπ·3π/2})‖ = -1.308…` from
`sigma_alphaNS_ne_zero_one`. -/
theorem chi_norm_alphaNS_ne_one :
    ‖1 + Complex.exp (((π * (3 * π / 2) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * (3 * π / 2) : ℝ) : ℂ) * Complex.I) ^ 2‖ ≠ 1 := by
  intro h
  rw [chi_norm_unity_iff_half_or_odd_integer] at h
  apply irrational_three_pi_div_two
  rcases h with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨((1 : ℚ) / 2 + k), by push_cast; linarith⟩
  · exact ⟨((1 : ℚ) + 2 * k), by push_cast; linarith⟩

/-! ## §6 Axiom check -/

#print axioms PrincipiaTractalis.ChiNormUnity.abs_one_add_two_mul_eq_one_iff
#print axioms PrincipiaTractalis.ChiNormUnity.chi_norm_pi_mul_eq_one_iff
#print axioms PrincipiaTractalis.ChiNormUnity.chi_norm_unity_iff_half_or_odd_integer
#print axioms PrincipiaTractalis.ChiNormUnity.chi_norm_alphaPoincare
#print axioms PrincipiaTractalis.ChiNormUnity.chi_norm_alphaRH
#print axioms PrincipiaTractalis.ChiNormUnity.chi_norm_alpha_five
#print axioms PrincipiaTractalis.ChiNormUnity.chi_norm_alphaNS_ne_one

end PrincipiaTractalis.ChiNormUnity
