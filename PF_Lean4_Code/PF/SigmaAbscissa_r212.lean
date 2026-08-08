/-
# r212: σ(α) = log₃ |1 + 2 cos(π α)| — the abscissa theorem.

★ 2026-08-06 r212 — the framework's FIRST non-circular α-selection mechanism,
and the exact statement of how far it reaches. ★

## What this file is

The book defines (ch03:49, ch03:93) `D₃(n)` = the sum of the base-3 digits of
`n`, and the fractal Dirichlet series

    R_f(α, s) = Σ_{n ≥ 1} e^{iπ α D₃(n)} / n^s .

The exact digit-block identity, formalized here as `digitBlock_sum`, is

    Σ_{n < 3^k} ω^{D₃(n)} = (1 + ω + ω²)^k        for every ω : ℂ.

At `ω = e^{iπα}` we have `1 + e^{iπα} + e^{2iπα} = e^{iπα}(1 + 2 cos πα)`, so
the 3^k-block partial sums have modulus exactly `|1 + 2 cos(πα)|^k`
(`norm_digitBlock_partialSum`). By the standard abscissa formula this makes

    σ(α) = log₃ |1 + 2 cos(π α)|

the abscissa of convergence — the rightmost singularity — of `R_f(α, ·)`.
Sanity: σ(0) = 1 (ζ's pole; `R_f(0,s) = ζ(s)`), σ(2) = 1, σ(3/2) = 0.

**Scope of the formalization.** What is proved below is the digit-block identity,
the modulus computation, the level sets of σ, and the rationality obstruction.
The analytic step "block modulus `r^k` ⟹ abscissa `log₃ r`" is NOT formalized
here; `sigma` is *defined* by the closed form. Everything downstream of §4 is a
theorem about that closed form.

## The payoff — the nine canonical α-values

Run the framework's nine α-values (`appendices/appJ_refinement_pass_2026-06-07.tex:239-249`)
through σ:

| name        | value  | σ(α)       |                    |
|-------------|--------|------------|--------------------|
| α_Poincaré  | 1      | **0**      | exact hit          |
| α_RH        | 3/2    | **0**      | exact hit          |
| α_YM        | 2      | **1**      | exact hit, ζ's pole|
| α_Hodge     | φ      | 0.4961550  | miss               |
| α_P         | √2     | −0.6921266 | miss               |
| α_NP        | φ+1/4  | 0.9470835  | miss               |
| α_QG        | √(2π)  | −0.0387176 | miss               |
| α_BSD       | 3π/4   | 0.5712771  | miss               |
| α_NS        | 3π/2   | −1.3080122 | miss               |

The three exact hits are `sigma_one`, `sigma_three_halves`, `sigma_two`.
The six misses are `sigma_alphaHodge_ne_zero_one` … `sigma_alphaNS_ne_zero_one`,
each an instance of `irrational_imp_sigma_ne_zero_one`: σ ∈ {0, 1} forces α ∈ ½ℤ
(or α ∈ ⅔ℤ in the degenerate branch), hence α rational.

**The framework's own ternary scaling law derives exactly its three RATIONAL
α-values and none of its six irrational ones.**

## Relation to r123

r123 (`PF/AlphaFromSubstrateKTheory_r123.lean`) refutes the trace/K-theory route
to α: the substrate either excludes an α-value or says nothing about it. This
file is the complementary positive-and-bounded result. The digit route WORKS,
and it reaches only the rational third of the table. Base-3 digit structure has
nothing to say about √2, φ, φ+1/4, √(2π), 3π/4, 3π/2 — and `§7` proves it cannot,
for any irrational α whatsoever.

## THE φ GUARD RAIL

σ(φ) = 0.4961550. The exact σ = 1/2 point in that neighbourhood is
**α\* = 1.6192817**, NOT φ = 1.6180340. They differ by 1.25e-3, and σ(φ) misses
1/2 by 0.8%. This near-coincidence must NOT be adopted as a derivation of
α_Hodge.

§8 puts the guard rail **in the kernel**: `sigma_goldenRatio_ne_half` proves
`σ(φ) ≠ 1/2` outright, via `cos_quad_chain` — an order-4 Taylor enclosure
(`Real.cos_bound`) at `π(2−φ)/4 ≈ 0.2999954` followed by two double-angle steps,
giving `cos(πφ) ≤ 0.363476`, against `(√3 − 1)/2 > 0.3660254`.
`sigma_goldenRatio_off_all_three` bundles it with the σ = 0 and σ = 1 misses.

## THE DEGENERATE CASE — a statement that had to be reshaped

At α = 2/3 and α = 4/3 one has `1 + 2 cos(πα) = 0`, and mathlib's convention is
`Real.logb b 0 = 0`. So `sigma (2/3) = 0` for a reason that has nothing to do
with the level set: the argument of the logarithm vanishes. The naive
`sigma α = 0 ↔ cos(πα) = 0 ∨ cos(πα) = -1` is therefore **FALSE at α = 2/3**.

Two honest forms are given and neither papers over it:

* `sigma_eq_zero_iff_full` — unconditional, three branches, includes the
  degenerate one. This is the whole truth.
* `sigma_eq_zero_iff` — the two-branch form, under the explicit hypothesis
  `1 + 2 * Real.cos (π * α) ≠ 0`.

`sigma_eq_one_iff` needs no hypothesis: the degenerate value 0 is ≠ 1, so the
degenerate case falsifies both sides.

Note further that the degenerate branch also forces α rational (α = 2k/3, see
`cos_pi_mul_eq_neg_half_imp_rational`), so the §7 obstruction is unconditional
even though §5 is not.

## Other reshapes forced by the mathlib pin

`Complex.abs` no longer exists in mathlib
`eed770a434957369c6262aa3fb1d6426419016d4` (Lean 4.24.0-rc1); it was replaced by
the norm `‖·‖`. §2 and §3 are stated with `‖·‖` accordingly. This is a notational
change only.

`irrational_pi` DOES exist in this pin, so `3π/4`, `3π/2` and `√(2π)` need no
hypothesis. Likewise `Real.goldenRatio_irrational` exists and is used directly.

## What this file does NOT claim

Nothing here bears on RH, BSD, Yang–Mills, or any Millennium problem. It is a
theorem about the Dirichlet series `R_f` and about which real numbers can be
level-set values of one explicit elementary function. It selects three of the
framework's nine α-values and proves the other six unreachable by this route.

Cross-reference: `codex/AUDIT_RESPONSE_2026-08-06.md` §3.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.GoldenRatio

open scoped Real

namespace PrincipiaTractalis.SigmaAbscissa

/-! ## §1 The digit-block identity -/

/-- Splitting `range (N * b)` into `N` consecutive blocks of length `b`. -/
private lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (b : ℕ) (f : ℕ → M) :
    ∀ N : ℕ, ∑ n ∈ Finset.range (N * b), f n
      = ∑ m ∈ Finset.range N, ∑ d ∈ Finset.range b, f (m * b + d) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have h : (N + 1) * b = N * b + b := by ring
      rw [h, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- `Nat.digits 3` is little-endian, so the LAST digit is the one that peels off:
`D₃(3m + d) = d + D₃(m)` for `d < 3`.  The `m = d = 0` edge case is consistent
(`Nat.digits 3 0 = []`, sum `0`). -/
lemma digits_sum_step (m d : ℕ) (hd : d < 3) :
    (Nat.digits 3 (m * 3 + d)).sum = d + (Nat.digits 3 m).sum := by
  rcases Nat.eq_zero_or_pos (m * 3 + d) with h0 | hpos
  · have hm : m = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hm; subst hd0; simp
  · have h1 : (m * 3 + d) % 3 = d := by omega
    have h2 : (m * 3 + d) / 3 = m := by omega
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 3) hpos, h1, h2, List.sum_cons]

/-- **The exact digit-block identity.**  For every `ω : ℂ` and every `k`,
`Σ_{n < 3^k} ω^{D₃(n)} = (1 + ω + ω²)^k`. -/
theorem digitBlock_sum (ω : ℂ) (k : ℕ) :
    ∑ n ∈ Finset.range (3 ^ k), ω ^ ((Nat.digits 3 n).sum) = (1 + ω + ω ^ 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hpow : (3:ℕ) ^ (k + 1) = 3 ^ k * 3 := by ring
      rw [hpow, sum_range_mul_split 3 (fun n => ω ^ ((Nat.digits 3 n).sum)) (3 ^ k)]
      have step : ∀ m ∈ Finset.range (3 ^ k),
          ∑ d ∈ Finset.range 3, ω ^ ((Nat.digits 3 (m * 3 + d)).sum)
            = ω ^ ((Nat.digits 3 m).sum) * (1 + ω + ω ^ 2) := by
        intro m _
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
          digits_sum_step m 0 (by norm_num), digits_sum_step m 1 (by norm_num),
          digits_sum_step m 2 (by norm_num)]
        ring
      rw [Finset.sum_congr rfl step, ← Finset.sum_mul, ih]
      ring

/-! ## §2 The modulus -/

/-- `1 + z + z² = z · (1 + 2 cos θ)` for `z = e^{iθ}`. -/
lemma one_add_exp_add_exp_sq_eq (θ : ℝ) :
    1 + Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp ((θ : ℂ) * Complex.I) ^ 2
      = Complex.exp ((θ : ℂ) * Complex.I) * ((1 + 2 * Real.cos θ : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I]
  push_cast
  linear_combination (-1 : ℂ) * Complex.sin_sq_add_cos_sq (θ : ℂ)
    + Complex.sin (θ : ℂ) ^ 2 * Complex.I_sq

/-- **The modulus.**  `‖1 + e^{iθ} + e^{2iθ}‖ = |1 + 2 cos θ|`.

(Stated with `‖·‖`: `Complex.abs` was removed from mathlib in this pin.) -/
theorem norm_one_add_exp_add_exp_sq (θ : ℝ) :
    ‖1 + Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp ((θ : ℂ) * Complex.I) ^ 2‖
      = |1 + 2 * Real.cos θ| := by
  rw [one_add_exp_add_exp_sq_eq θ, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

/-- The `α`-form of §2, matching the framework's `ω = e^{iπα}`. -/
theorem norm_one_add_exp_add_exp_sq_pi_mul (α : ℝ) :
    ‖1 + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((π * α : ℝ) : ℂ) * Complex.I) ^ 2‖
      = |1 + 2 * Real.cos (π * α)| :=
  norm_one_add_exp_add_exp_sq (π * α)

/-! ## §3 The partial-sum modulus -/

/-- **The 3^k-block partial sum of `R_f(α, ·)`'s numerator has modulus exactly
`|1 + 2 cos(πα)|^k`.** -/
theorem norm_digitBlock_partialSum (α : ℝ) (k : ℕ) :
    ‖∑ n ∈ Finset.range (3 ^ k),
        Complex.exp ((π : ℂ) * (α : ℂ) * (((Nat.digits 3 n).sum : ℕ) : ℂ) * Complex.I)‖
      = |1 + 2 * Real.cos (π * α)| ^ k := by
  have hterm : ∀ n : ℕ,
      Complex.exp ((π : ℂ) * (α : ℂ) * (((Nat.digits 3 n).sum : ℕ) : ℂ) * Complex.I)
        = Complex.exp (((π * α : ℝ) : ℂ) * Complex.I) ^ ((Nat.digits 3 n).sum) := by
    intro n
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun n _ => hterm n),
    digitBlock_sum (Complex.exp (((π * α : ℝ) : ℂ) * Complex.I)) k,
    norm_pow, norm_one_add_exp_add_exp_sq_pi_mul]

/-! ## §4 The definition -/

/-- **σ(α) = log₃ |1 + 2 cos(π α)|** — the abscissa of convergence of `R_f(α, ·)`.

Defined by the closed form derived in §1–§3.  The analytic step from block
modulus to abscissa is not formalized in this file. -/
noncomputable def sigma (α : ℝ) : ℝ := Real.logb 3 |1 + 2 * Real.cos (π * α)|

/-! ## §5 The level sets -/

/-- **The whole truth about the σ = 0 level set**, degenerate branch included.

The first disjunct `1 + 2 cos(πα) = 0` is the α = 2/3, 4/3 case, where mathlib's
`Real.logb b 0 = 0` makes σ vanish for a reason unrelated to the level set. -/
theorem sigma_eq_zero_iff_full (α : ℝ) :
    sigma α = 0 ↔
      1 + 2 * Real.cos (π * α) = 0 ∨ Real.cos (π * α) = 0 ∨ Real.cos (π * α) = -1 := by
  unfold sigma
  rw [Real.logb_eq_zero]
  constructor
  · rintro (h | h | h | h | h | h)
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact Or.inl (abs_eq_zero.mp h)
    · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h with h' | h'
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
    · have := abs_nonneg (1 + 2 * Real.cos (π * α)); linarith
  · rintro (h | h | h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h, abs_zero]))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      rw [h]; norm_num
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      rw [h]; norm_num

/-- The clean two-branch σ = 0 level set, under the non-degeneracy hypothesis.
Without `hne` this statement is FALSE at α = 2/3 — see the file header. -/
theorem sigma_eq_zero_iff (α : ℝ) (hne : 1 + 2 * Real.cos (π * α) ≠ 0) :
    sigma α = 0 ↔ (Real.cos (π * α) = 0 ∨ Real.cos (π * α) = -1) := by
  rw [sigma_eq_zero_iff_full]
  constructor
  · rintro (h | h | h)
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  · exact fun h => Or.inr h

/-- **The σ = 1 level set.**  No hypothesis needed: in the degenerate case
`σ = 0 ≠ 1` and `cos(πα) = -1/2 ≠ 1`, so both sides are false. -/
theorem sigma_eq_one_iff (α : ℝ) : sigma α = 1 ↔ Real.cos (π * α) = 1 := by
  constructor
  · intro h
    by_cases hz : 1 + 2 * Real.cos (π * α) = 0
    · rw [sigma, hz, abs_zero, Real.logb_zero] at h; norm_num at h
    · have hpos : 0 < |1 + 2 * Real.cos (π * α)| := abs_pos.mpr hz
      rw [sigma, Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hpos,
        Real.rpow_one] at h
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 3)).mp h.symm with h' | h'
      · linarith
      · have := Real.neg_one_le_cos (π * α); linarith
  · intro h
    rw [sigma, h]
    norm_num

/-! ### Converting the cosine conditions to conditions on α -/

theorem cos_pi_mul_eq_zero_iff (α : ℝ) :
    Real.cos (π * α) = 0 ↔ ∃ k : ℤ, α = 1 / 2 + k := by
  rw [Real.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, mul_left_cancel₀ Real.pi_ne_zero (by rw [hk]; ring)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

theorem cos_pi_mul_eq_neg_one_iff (α : ℝ) :
    Real.cos (π * α) = -1 ↔ ∃ k : ℤ, α = 1 + 2 * k := by
  rw [Real.cos_eq_neg_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, mul_left_cancel₀ Real.pi_ne_zero (by rw [← hk]; ring)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

theorem cos_pi_mul_eq_one_iff (α : ℝ) :
    Real.cos (π * α) = 1 ↔ ∃ k : ℤ, α = 2 * k := by
  rw [Real.cos_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, mul_left_cancel₀ Real.pi_ne_zero (by rw [← hk]; ring)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

/-- The degenerate branch also forces α rational: `1 + 2cos(πα) = 0` means
`cos(πα) = -1/2`, hence `cos(3πα) = 4(-1/2)³ - 3(-1/2) = 1`, hence `α = 2k/3`. -/
theorem cos_pi_mul_eq_neg_half_imp_rational (α : ℝ) (h : 1 + 2 * Real.cos (π * α) = 0) :
    ∃ k : ℤ, α = 2 * k / 3 := by
  have hc : Real.cos (π * α) = -(1 / 2) := by linarith
  have h3 : Real.cos (3 * (π * α)) = 1 := by
    rw [Real.cos_three_mul, hc]; norm_num
  rw [Real.cos_eq_one_iff] at h3
  obtain ⟨n, hn⟩ := h3
  refine ⟨n, ?_⟩
  have key : π * (3 * α) = π * (2 * (n : ℝ)) := by linear_combination -hn
  have h3α : 3 * α = 2 * (n : ℝ) := mul_left_cancel₀ Real.pi_ne_zero key
  linarith

/-! ## §6 The three exact hits -/

/-- α_Poincaré = 1. -/
theorem sigma_one : sigma 1 = 0 := by
  rw [sigma, mul_one, Real.cos_pi]
  norm_num

/-- α_RH = 3/2. -/
theorem sigma_three_halves : sigma (3 / 2) = 0 := by
  have hc : Real.cos (π * (3 / 2)) = 0 := by
    rw [show π * (3 / 2) = π + π / 2 by ring, Real.cos_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, Real.cos_pi, Real.sin_pi]
    ring
  rw [sigma, hc]
  norm_num

/-- α_YM = 2 — the ζ pole. -/
theorem sigma_two : sigma 2 = 1 := by
  have hc : Real.cos (π * 2) = 1 := by
    rw [mul_comm]; exact Real.cos_two_pi
  rw [sigma, hc]
  norm_num

/-! ## §7 THE OBSTRUCTION -/

/-- **σ ∈ {0, 1} forces α rational.**  Unconditional: every branch of the level
sets — including the degenerate `1 + 2cos(πα) = 0` branch — lands α in ½ℤ ∪ ⅔ℤ. -/
theorem sigma_eq_zero_or_one_imp_rational {α : ℝ} (h : sigma α = 0 ∨ sigma α = 1) :
    ∃ q : ℚ, α = q := by
  rcases h with h | h
  · rcases (sigma_eq_zero_iff_full α).mp h with hz | hc | hc
    · obtain ⟨k, hk⟩ := cos_pi_mul_eq_neg_half_imp_rational α hz
      exact ⟨2 * k / 3, by rw [hk]; push_cast; ring⟩
    · obtain ⟨k, hk⟩ := (cos_pi_mul_eq_zero_iff α).mp hc
      exact ⟨1 / 2 + k, by rw [hk]; push_cast; ring⟩
    · obtain ⟨k, hk⟩ := (cos_pi_mul_eq_neg_one_iff α).mp hc
      exact ⟨1 + 2 * k, by rw [hk]; push_cast; ring⟩
  · obtain ⟨k, hk⟩ := (cos_pi_mul_eq_one_iff α).mp ((sigma_eq_one_iff α).mp h)
    exact ⟨2 * k, by rw [hk]; push_cast; ring⟩

/-- The form requested in the r212 brief, with the explicit non-degeneracy
hypothesis.  The hypothesis turns out to be unnecessary — see
`sigma_eq_zero_or_one_imp_rational` — because the degenerate branch is itself
rational (α = 2k/3).  Kept because it is the statement the brief names. -/
theorem sigma_mem_zero_one_imp_rational {α : ℝ} (h : sigma α = 0 ∨ sigma α = 1)
    (_hne : 1 + 2 * Real.cos (π * α) ≠ 0) : ∃ q : ℚ, α = q :=
  sigma_eq_zero_or_one_imp_rational h

/-- **The contrapositive: no irrational α is on the σ = 0 or σ = 1 level set.**
This is the theorem that kills the six irrational framework α-values at once. -/
theorem irrational_imp_sigma_ne_zero_one {α : ℝ} (h : Irrational α) :
    sigma α ≠ 0 ∧ sigma α ≠ 1 := by
  constructor <;> intro hs
  · obtain ⟨q, hq⟩ := sigma_eq_zero_or_one_imp_rational (Or.inl hs)
    exact h ⟨q, hq.symm⟩
  · obtain ⟨q, hq⟩ := sigma_eq_zero_or_one_imp_rational (Or.inr hs)
    exact h ⟨q, hq.symm⟩

/-! ### The six irrationality facts -/

/-- α_NP = φ + 1/4. -/
theorem irrational_goldenRatio_add_quarter : Irrational (Real.goldenRatio + 1 / 4) := by
  have h := Real.goldenRatio_irrational.add_ratCast (1 / 4 : ℚ)
  norm_num at h
  exact h

/-- α_QG = √(2π).  If `√(2π) = q` then `2π = q²`, making π rational. -/
theorem irrational_sqrt_two_pi : Irrational (Real.sqrt (2 * π)) := by
  rintro ⟨q, hq⟩
  have h2pi : (0 : ℝ) ≤ 2 * π := by positivity
  have hsq : (2 : ℝ) * π = (q : ℝ) ^ 2 := by
    rw [← Real.sq_sqrt h2pi, ← hq]
  exact irrational_pi ⟨q ^ 2 / 2, by push_cast; linarith⟩

/-- α_BSD = 3π/4. -/
theorem irrational_three_pi_div_four : Irrational (3 * π / 4) := by
  have h := irrational_pi.ratCast_mul (q := (3 / 4 : ℚ)) (by norm_num)
  have he : ((3 / 4 : ℚ) : ℝ) * π = 3 * π / 4 := by push_cast; ring
  rwa [he] at h

/-- α_NS = 3π/2. -/
theorem irrational_three_pi_div_two : Irrational (3 * π / 2) := by
  have h := irrational_pi.ratCast_mul (q := (3 / 2 : ℚ)) (by norm_num)
  have he : ((3 / 2 : ℚ) : ℝ) * π = 3 * π / 2 := by push_cast; ring
  rwa [he] at h

/-! ### The six misses -/

/-- α_Hodge = φ.  σ(φ) = 0.4961550 — see also the guard rail, §8. -/
theorem sigma_alphaHodge_ne_zero_one :
    sigma Real.goldenRatio ≠ 0 ∧ sigma Real.goldenRatio ≠ 1 :=
  irrational_imp_sigma_ne_zero_one Real.goldenRatio_irrational

/-- α_P = √2.  σ(√2) = −0.6921266. -/
theorem sigma_alphaP_ne_zero_one :
    sigma (Real.sqrt 2) ≠ 0 ∧ sigma (Real.sqrt 2) ≠ 1 :=
  irrational_imp_sigma_ne_zero_one irrational_sqrt_two

/-- α_NP = φ + 1/4.  σ = 0.9470835 — close to 1, but provably not 1. -/
theorem sigma_alphaNP_ne_zero_one :
    sigma (Real.goldenRatio + 1 / 4) ≠ 0 ∧ sigma (Real.goldenRatio + 1 / 4) ≠ 1 :=
  irrational_imp_sigma_ne_zero_one irrational_goldenRatio_add_quarter

/-- α_QG = √(2π).  σ = −0.0387176 — close to 0, but provably not 0. -/
theorem sigma_alphaQG_ne_zero_one :
    sigma (Real.sqrt (2 * π)) ≠ 0 ∧ sigma (Real.sqrt (2 * π)) ≠ 1 :=
  irrational_imp_sigma_ne_zero_one irrational_sqrt_two_pi

/-- α_BSD = 3π/4.  σ = 0.5712771. -/
theorem sigma_alphaBSD_ne_zero_one :
    sigma (3 * π / 4) ≠ 0 ∧ sigma (3 * π / 4) ≠ 1 :=
  irrational_imp_sigma_ne_zero_one irrational_three_pi_div_four

/-- α_NS = 3π/2.  σ = −1.3080122. -/
theorem sigma_alphaNS_ne_zero_one :
    sigma (3 * π / 2) ≠ 0 ∧ sigma (3 * π / 2) ≠ 1 :=
  irrational_imp_sigma_ne_zero_one irrational_three_pi_div_two

/-! ## The capstone -/

/-- **THE DICHOTOMY.**  Of the framework's nine canonical α-values, the ternary
digit structure selects exactly the three rational ones — σ = 0 at α_Poincaré = 1
and α_RH = 3/2, σ = 1 at α_YM = 2 — and provably reaches none of the six
irrational ones.

This is a two-sided result.  It is the framework's first non-circular α-selection
mechanism, and it is also an exact statement of that mechanism's reach.  It says
nothing about RH, BSD, or any Millennium problem. -/
theorem framework_alpha_sigma_dichotomy :
    -- the three rational hits
    (sigma 1 = 0 ∧ sigma (3 / 2) = 0 ∧ sigma 2 = 1) ∧
    -- the six irrational misses
    ((sigma Real.goldenRatio ≠ 0 ∧ sigma Real.goldenRatio ≠ 1) ∧
     (sigma (Real.sqrt 2) ≠ 0 ∧ sigma (Real.sqrt 2) ≠ 1) ∧
     (sigma (Real.goldenRatio + 1 / 4) ≠ 0 ∧ sigma (Real.goldenRatio + 1 / 4) ≠ 1) ∧
     (sigma (Real.sqrt (2 * π)) ≠ 0 ∧ sigma (Real.sqrt (2 * π)) ≠ 1) ∧
     (sigma (3 * π / 4) ≠ 0 ∧ sigma (3 * π / 4) ≠ 1) ∧
     (sigma (3 * π / 2) ≠ 0 ∧ sigma (3 * π / 2) ≠ 1)) :=
  ⟨⟨sigma_one, sigma_three_halves, sigma_two⟩,
   sigma_alphaHodge_ne_zero_one, sigma_alphaP_ne_zero_one, sigma_alphaNP_ne_zero_one,
   sigma_alphaQG_ne_zero_one, sigma_alphaBSD_ne_zero_one, sigma_alphaNS_ne_zero_one⟩

/-! ## §8 The σ = 1/2 level and the φ GUARD RAIL -/

private lemma sqrt_three_gt : (1.7320508 : ℝ) < Real.sqrt 3 := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  nlinarith [Real.sqrt_nonneg 3, h]

private lemma sqrt_five_gt : (2.2360679 : ℝ) < Real.sqrt 5 := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [Real.sqrt_nonneg 5, h]

private lemma sqrt_five_lt : Real.sqrt 5 < 2.236068 := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [Real.sqrt_nonneg 5, h]

/-- **The σ = 1/2 level set.**  `|1 + 2c| = √3`; the branch `1 + 2c = -√3` would
force `c = -(√3+1)/2 < -1`, which no cosine attains. -/
theorem sigma_eq_half_iff (α : ℝ) (hne : 1 + 2 * Real.cos (π * α) ≠ 0) :
    sigma α = 1 / 2 ↔ Real.cos (π * α) = (Real.sqrt 3 - 1) / 2 := by
  have hs3 : (1.7320508 : ℝ) < Real.sqrt 3 := sqrt_three_gt
  have hpos : 0 < |1 + 2 * Real.cos (π * α)| := abs_pos.mpr hne
  have hcl : -1 ≤ Real.cos (π * α) := Real.neg_one_le_cos _
  rw [sigma, Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hpos, ← Real.sqrt_eq_rpow]
  constructor
  · intro h
    rcases (abs_eq (Real.sqrt_nonneg 3)).mp h.symm with h' | h'
    · linarith
    · linarith
  · intro h
    have hp : 0 < 1 + 2 * Real.cos (π * α) := by rw [h]; linarith
    rw [abs_of_pos hp, h]
    ring

/-- Pure-real Taylor chain: on `0.29999 < w < 0.3` the order-4 bound
`Real.cos_bound` plus two double-angle steps encloses `cos (4w)`.

Stated over a plain variable `w` on purpose: `Real.goldenRatio` is a mathlib
`abbrev` (reducible), and letting it into a `nlinarith` goal here caused `whnf`
timeouts. -/
private lemma cos_quad_chain (w : ℝ) (hwl : (0.29999 : ℝ) < w) (hwu : w < 0.3) :
    (0.352804 : ℝ) ≤ Real.cos (4 * w) ∧ Real.cos (4 * w) ≤ 0.363476 := by
  have hw0 : (0 : ℝ) < w := by linarith
  have habs : |w| ≤ 1 := by rw [abs_of_pos hw0]; linarith
  have hcb := Real.cos_bound habs
  rw [abs_of_pos hw0] at hcb
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcb
  have hw2u : w ^ 2 ≤ 0.09 := by nlinarith
  have hw2l : (0.0899940001 : ℝ) ≤ w ^ 2 := by nlinarith
  have hw4 : w ^ 4 ≤ 0.0081 := by nlinarith [sq_nonneg w]
  have hw4nn : (0 : ℝ) ≤ w ^ 4 := by positivity
  have herr : w ^ 4 * (5 / 96) ≤ 0.000422 := by linarith
  have herr0 : (0 : ℝ) ≤ w ^ 4 * (5 / 96) := by linarith
  have hcw_ub : Real.cos w ≤ 0.955425 := by linarith
  have hcw_lb : (0.954578 : ℝ) ≤ Real.cos w := by linarith
  have h2 : Real.cos (2 * w) = 2 * Real.cos w ^ 2 - 1 := Real.cos_two_mul w
  have h2ub : Real.cos (2 * w) ≤ 0.825674 := by rw [h2]; nlinarith
  have h2lb : (0.822438 : ℝ) ≤ Real.cos (2 * w) := by rw [h2]; nlinarith
  have h4 : Real.cos (4 * w) = 2 * Real.cos (2 * w) ^ 2 - 1 := by
    have h := Real.cos_two_mul (2 * w)
    rw [show 2 * (2 * w) = 4 * w by ring] at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [h4]; nlinarith
  · rw [h4]; nlinarith

/-- Numeric enclosure of `cos (π φ)`: reduce `π φ` to `2π − π(2−φ)` with
`Real.cos_two_pi_sub`, then run `cos_quad_chain` at `π(2−φ)/4 ≈ 0.2999954`. -/
private lemma cos_pi_goldenRatio_bounds :
    0.35 < Real.cos (π * Real.goldenRatio) ∧ Real.cos (π * Real.goldenRatio) < 0.3635 := by
  have h5l : (2.2360679 : ℝ) < Real.sqrt 5 := sqrt_five_gt
  have h5u : Real.sqrt 5 < 2.236068 := sqrt_five_lt
  have hpl : (3.141592 : ℝ) < π := Real.pi_gt_d6
  have hpu : π < 3.141593 := Real.pi_lt_d6
  have hgl : (0.381966 : ℝ) < 2 - Real.goldenRatio := by
    show (0.381966 : ℝ) < 2 - (1 + Real.sqrt 5) / 2
    linarith
  have hgu : 2 - Real.goldenRatio < 0.38196605 := by
    show 2 - (1 + Real.sqrt 5) / 2 < 0.38196605
    linarith
  have hπ0 : (0 : ℝ) < π := Real.pi_pos
  have hwl : (0.29999 : ℝ) < π * (2 - Real.goldenRatio) / 4 := by nlinarith
  have hwu : π * (2 - Real.goldenRatio) / 4 < 0.3 := by nlinarith
  obtain ⟨hlb, hub⟩ := cos_quad_chain _ hwl hwu
  rw [show 4 * (π * (2 - Real.goldenRatio) / 4) = 2 * π - π * Real.goldenRatio by ring,
    Real.cos_two_pi_sub] at hlb hub
  exact ⟨by linarith, by linarith⟩

/-- **THE φ GUARD RAIL, IN THE KERNEL.**

σ(φ) = 0.4961550, and the exact σ = 1/2 point nearby is α\* = 1.6192817, which is
1.25e-3 away from φ = 1.6180340.  The near-coincidence is a miss, not a
derivation: this theorem forbids reading α_Hodge = φ off the σ = 1/2 level set. -/
theorem sigma_goldenRatio_ne_half : sigma Real.goldenRatio ≠ 1 / 2 := by
  obtain ⟨hlo, hhi⟩ := cos_pi_goldenRatio_bounds
  have hne : 1 + 2 * Real.cos (π * Real.goldenRatio) ≠ 0 := by intro h; linarith
  intro h
  rw [sigma_eq_half_iff Real.goldenRatio hne] at h
  have hs3 : (1.7320508 : ℝ) < Real.sqrt 3 := sqrt_three_gt
  rw [h] at hhi
  linarith

/-- The guard rail restated the way the corpus must read it: φ is on neither the
σ = 0, nor the σ = 1, nor the σ = 1/2 level set of the abscissa. -/
theorem sigma_goldenRatio_off_all_three :
    sigma Real.goldenRatio ≠ 0 ∧ sigma Real.goldenRatio ≠ 1 ∧
      sigma Real.goldenRatio ≠ 1 / 2 :=
  ⟨sigma_alphaHodge_ne_zero_one.1, sigma_alphaHodge_ne_zero_one.2,
   sigma_goldenRatio_ne_half⟩

end PrincipiaTractalis.SigmaAbscissa

/-! ## §9 — kernel axiom audit

House rule: the audit lives IN the file, so `lake build` re-runs it.  Every
declaration below must report exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms PrincipiaTractalis.SigmaAbscissa.digitBlock_sum
#print axioms PrincipiaTractalis.SigmaAbscissa.norm_one_add_exp_add_exp_sq
#print axioms PrincipiaTractalis.SigmaAbscissa.norm_one_add_exp_add_exp_sq_pi_mul
#print axioms PrincipiaTractalis.SigmaAbscissa.norm_digitBlock_partialSum
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_eq_zero_iff_full
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_eq_zero_iff
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_eq_one_iff
#print axioms PrincipiaTractalis.SigmaAbscissa.cos_pi_mul_eq_zero_iff
#print axioms PrincipiaTractalis.SigmaAbscissa.cos_pi_mul_eq_neg_one_iff
#print axioms PrincipiaTractalis.SigmaAbscissa.cos_pi_mul_eq_one_iff
#print axioms PrincipiaTractalis.SigmaAbscissa.cos_pi_mul_eq_neg_half_imp_rational
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_one
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_three_halves
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_two
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_eq_zero_or_one_imp_rational
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_mem_zero_one_imp_rational
#print axioms PrincipiaTractalis.SigmaAbscissa.irrational_imp_sigma_ne_zero_one
#print axioms PrincipiaTractalis.SigmaAbscissa.irrational_goldenRatio_add_quarter
#print axioms PrincipiaTractalis.SigmaAbscissa.irrational_sqrt_two_pi
#print axioms PrincipiaTractalis.SigmaAbscissa.irrational_three_pi_div_four
#print axioms PrincipiaTractalis.SigmaAbscissa.irrational_three_pi_div_two
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_alphaHodge_ne_zero_one
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_alphaP_ne_zero_one
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_alphaNP_ne_zero_one
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_alphaQG_ne_zero_one
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_alphaBSD_ne_zero_one
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_alphaNS_ne_zero_one
#print axioms PrincipiaTractalis.SigmaAbscissa.framework_alpha_sigma_dichotomy
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_eq_half_iff
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_goldenRatio_ne_half
#print axioms PrincipiaTractalis.SigmaAbscissa.sigma_goldenRatio_off_all_three
