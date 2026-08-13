/-
# r241: σ UNIVERSAL UPPER BOUND — σ(α) ≤ 1 for all α ∈ ℝ.

★ 2026-08-13 r241 — the SECOND structural landing after the r236–r239
validation arc. Framework-generic upper bound on r212's substrate
abscissa: `σ(α) ≤ 1` for every real α, with equality iff cos(πα) = 1
(iff α ∈ 2ℤ). Completes the σ ≤ 1 top-of-spectrum characterization. ★

## The bound

`σ(α) = log₃ |1 + 2·cos(πα)|`. Since `cos` is bounded in `[-1, 1]`:
    -1 ≤ 1 + 2·cos(πα) ≤ 3,
so
    |1 + 2·cos(πα)| ≤ 3,
and monotonicity of `log₃` on positives gives
    σ(α) ≤ log₃ 3 = 1.

Care at the degenerate branch: if `1 + 2·cos(πα) = 0` (α = 2/3 etc.), then
`|…| = 0` and mathlib's convention `logb 3 0 = 0` gives `σ(α) = 0 ≤ 1`.

## The equality characterization

Combined with r212's `sigma_eq_one_iff : σ α = 1 ↔ cos(πα) = 1` and
r212's `cos_pi_mul_eq_one_iff : cos(πα) = 1 ↔ ∃ k : ℤ, α = 2·k`, we get:

- `σ(α) = 1 ↔ α ∈ 2ℤ` (even integers only)
- `σ(α) < 1 ↔ α ∉ 2ℤ` (every other α)
- Universal: `σ(α) ≤ 1` (all α).

α_YM = 2 is the framework's canonical σ = 1 pillar (r212 `sigma_two`).
Even-integer α = 0 also hits (r233 validation). Every irrational α misses
σ = 1 (r212 `irrational_imp_sigma_ne_zero_one`).

## Why this matters

The σ-sign machine (r212 + r225–r230 + r231 + r235) partitions the corpus
by σ-sign into three tiers. r241's universal `σ ≤ 1` bound puts a CEILING
on the growth tier — the linear-growth tier at σ = 1 is EXACTLY α ∈ 2ℤ,
no other pillar exceeds it. The substrate has a maximum-growth envelope,
achieved only on the ζ pole (α = 2) and other even integers.

Combined with r240's period-2 symmetry, `σ = 1` is exactly the ℤ-orbit of
α_YM = 2 (equivalently α = 0), giving a substrate-intrinsic
characterization of the maximum-envelope-growth tier.

## Contents

§1 `sigma_le_one` — the universal upper bound.
§2 `sigma_lt_one_iff` — strict-inequality characterization.
§3 `sigma_lt_one_of_cos_ne_one` — companion form.
§4 `sigma_eq_one_iff_even_integer` — combines r212's `sigma_eq_one_iff`
    with `cos_pi_mul_eq_one_iff` into α-language.
§5 `substrate_max_envelope_characterization` — three-conjunct capstone.
§6 Axiom check.

## Scope

* NOT a novel result — `cos ∈ [-1, 1]` is elementary.
* NOT a Millennium discharge.
* IS framework-generic structural bound on the r212 σ formula: a universal
  ceiling of 1, with equality iff the phase is stationary at 0 mod 2π.

Second structural landing after r240 (period-2 + evenness).

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.SigmaSymmetries_r240

open scoped Real

namespace PrincipiaTractalis.SigmaUpperBound

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 The universal upper bound `σ(α) ≤ 1`. -/

/-- **`sigma_le_one`** — every substrate σ value is ≤ 1.

Proof: `|1 + 2·cos(πα)| ≤ 1 + 2·|cos(πα)| ≤ 1 + 2 = 3` by triangle
inequality plus `|cos| ≤ 1`. Then `log₃` is monotone on `[0, 3]` and
`log₃ 3 = 1`. Degenerate case `|…| = 0`: mathlib's `Real.logb_zero = 0 ≤ 1`. -/
theorem sigma_le_one (α : ℝ) : PrincipiaTractalis.SigmaAbscissa.sigma α ≤ 1 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hbound : |1 + 2 * Real.cos (π * α)| ≤ 3 := by
    have hc : |Real.cos (π * α)| ≤ 1 := Real.abs_cos_le_one _
    have : |1 + 2 * Real.cos (π * α)| ≤ |1| + |2 * Real.cos (π * α)| :=
      abs_add _ _
    calc |1 + 2 * Real.cos (π * α)|
        ≤ |1| + |2 * Real.cos (π * α)| := this
      _ = 1 + 2 * |Real.cos (π * α)| := by
          rw [abs_of_pos (by norm_num : (0:ℝ) < 1), abs_mul,
              abs_of_pos (by norm_num : (0:ℝ) < 2)]
      _ ≤ 1 + 2 * 1 := by nlinarith [hc]
      _ = 3 := by norm_num
  -- Split on the degenerate branch.
  by_cases hz : |1 + 2 * Real.cos (π * α)| = 0
  · rw [hz, Real.logb_zero]; norm_num
  · have hpos : 0 < |1 + 2 * Real.cos (π * α)| :=
      lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
    have hle : Real.logb 3 |1 + 2 * Real.cos (π * α)| ≤ Real.logb 3 3 :=
      Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 3) hpos hbound
    have h33 : Real.logb 3 3 = 1 :=
      Real.logb_self_eq_one (by norm_num : (1:ℝ) < 3)
    linarith

/-! ## §2 Strict inequality characterization. -/

/-- **`sigma_lt_one_iff`** — `σ(α) < 1 ↔ cos(πα) ≠ 1`.

Follows from `sigma_le_one` + r212's `sigma_eq_one_iff`. Every α that
doesn't have `cos(πα) = 1` strictly misses the σ = 1 ceiling. -/
theorem sigma_lt_one_iff (α : ℝ) :
    PrincipiaTractalis.SigmaAbscissa.sigma α < 1 ↔ Real.cos (π * α) ≠ 1 := by
  constructor
  · intro h heq
    have hσ1 : PrincipiaTractalis.SigmaAbscissa.sigma α = 1 :=
      (sigma_eq_one_iff α).mpr heq
    linarith
  · intro h
    have hle := sigma_le_one α
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact absurd ((sigma_eq_one_iff α).mp heq) h

/-! ## §3 Companion form: `σ < 1` from `cos ≠ 1`. -/

/-- **`sigma_lt_one_of_cos_ne_one`** — the forward direction of §2 as
a standalone theorem for convenience. -/
theorem sigma_lt_one_of_cos_ne_one {α : ℝ} (h : Real.cos (π * α) ≠ 1) :
    PrincipiaTractalis.SigmaAbscissa.sigma α < 1 :=
  (sigma_lt_one_iff α).mpr h

/-! ## §4 α-language: `σ = 1 ↔ α ∈ 2ℤ`. -/

/-- **`sigma_eq_one_iff_even_integer`** — the σ = 1 tier is exactly the
even integers.

Composition of r212's `sigma_eq_one_iff` (σ = 1 ↔ cos(πα) = 1) with
r212's `cos_pi_mul_eq_one_iff` (cos(πα) = 1 ↔ ∃ k : ℤ, α = 2·k). -/
theorem sigma_eq_one_iff_even_integer (α : ℝ) :
    PrincipiaTractalis.SigmaAbscissa.sigma α = 1 ↔ ∃ k : ℤ, α = 2 * k := by
  rw [sigma_eq_one_iff, cos_pi_mul_eq_one_iff]

/-! ## §5 The three-conjunct capstone. -/

/-- **`substrate_max_envelope_characterization`** — the complete top-of-
spectrum characterization.

Three conjuncts:
- Universal `σ(α) ≤ 1` for every α.
- Strict `σ(α) < 1 ↔ cos(πα) ≠ 1`.
- α-language `σ(α) = 1 ↔ α ∈ 2ℤ`.

The substrate has a maximum-growth envelope of `σ = 1`, achieved only
on the even-integer lattice `2ℤ` (which via r240's period-2 is the same
as the ℤ-orbit of α_YM = 2 in the corpus). Every other α — including
every irrational pillar — strictly misses the ceiling. -/
theorem substrate_max_envelope_characterization :
    (∀ α : ℝ, PrincipiaTractalis.SigmaAbscissa.sigma α ≤ 1) ∧
    (∀ α : ℝ, PrincipiaTractalis.SigmaAbscissa.sigma α < 1 ↔ Real.cos (π * α) ≠ 1) ∧
    (∀ α : ℝ, PrincipiaTractalis.SigmaAbscissa.sigma α = 1 ↔ ∃ k : ℤ, α = 2 * k) :=
  ⟨sigma_le_one, sigma_lt_one_iff, sigma_eq_one_iff_even_integer⟩

/-! ## §6 Axiom check. -/

#print axioms PrincipiaTractalis.SigmaUpperBound.sigma_le_one
#print axioms PrincipiaTractalis.SigmaUpperBound.sigma_lt_one_iff
#print axioms PrincipiaTractalis.SigmaUpperBound.sigma_lt_one_of_cos_ne_one
#print axioms PrincipiaTractalis.SigmaUpperBound.sigma_eq_one_iff_even_integer
#print axioms PrincipiaTractalis.SigmaUpperBound.substrate_max_envelope_characterization

end PrincipiaTractalis.SigmaUpperBound
