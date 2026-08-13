/-
# r240: σ STRUCTURAL SYMMETRIES — period-2, evenness, integer double-shift.

★ 2026-08-13 r240 — the FIRST structural landing after the r236–r239
validation arc. Three fundamental symmetries of the r212 substrate σ
abscissa formula, framework-generic (no per-α, no per-pillar), all
kernel-clean. ★

## The three symmetries

**Period 2**: `σ(α + 2) = σ(α)`. Follows from `cos(π(α + 2)) = cos(πα + 2π)
= cos(πα)`. The substrate abscissa is invariant under α ↦ α + 2.

**Evenness**: `σ(-α) = σ(α)`. Follows from `cos(-πα) = cos(πα)` (cosine
is even). The substrate abscissa depends only on |α mod 2|-ish structure.

**Integer double-shift**: `σ(α + 2·k) = σ(α)` for `k : ℤ`. Iterates the
period-2 symmetry in both directions.

## Why this matters

The r236–r239 validation arc verified σ at seven small-denominator
rationals. Every one of those exact values EXTENDS via r240:

    σ(1/2 + 2k) = σ(1/2) = 0           (extended σ = 0 anchors)
    σ(1/3 + 2k) = σ(1/3) = log 2/log 3  (extended Cantor anchors)
    σ(1/5 + 2k) = σ(1/5) = 2·log₃ φ     (extended golden anchors)
    σ(2/5 + 2k) = σ(2/5) = log₃ φ       (extended golden anchors)
    …

Every closed-form value is now an INFINITE FAMILY of α-values with the
same σ, indexed by k ∈ ℤ. The rational-α σ table becomes a rational-α
σ *lattice*.

Evenness gives additional σ(−α) = σ(α), so each α value has an ℤ-orbit
plus its negation.

Combined: the substrate σ machine has a Klein-four-like symmetry group
acting on α that leaves σ invariant. Framework-generic; no per-pillar
proof needed.

## Contents

§1 `sigma_add_two` — `σ(α + 2) = σ(α)`.
§2 `sigma_neg` — `σ(-α) = σ(α)` (evenness).
§3 `sigma_add_two_int` — `σ(α + 2·k) = σ(α)` for `k : ℤ`.
§4 `sigma_sub_two` — companion: `σ(α - 2) = σ(α)`.
§5 `sigma_symmetries_capstone` — the three-conjunct bundle.
§6 Axiom check.

## Scope

* NOT novel results — period 2 and evenness of cos are elementary.
* NOT a Millennium discharge.
* IS framework-generic structural content on r212's σ formula: three
  substrate symmetries that let every exact-σ closed form generate an
  infinite ℤ-orbit of α-values with the same σ.

Framework-first: no per-pillar per-α application; one universal statement
covers every α. This is real substrate machinery, not validation.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.ExactSigmaTableCapstone_r239

open scoped Real

namespace PrincipiaTractalis.SigmaSymmetries

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 Period 2. -/

/-- **`sigma_add_two`** — the substrate σ formula has period 2 in α.

`σ(α + 2) = log₃|1 + 2·cos(π·(α+2))| = log₃|1 + 2·cos(π·α + 2π)|
        = log₃|1 + 2·cos(π·α)| = σ(α)` via `Real.cos_add_two_pi`. -/
theorem sigma_add_two (α : ℝ) :
    PrincipiaTractalis.SigmaAbscissa.sigma (α + 2)
      = PrincipiaTractalis.SigmaAbscissa.sigma α := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  congr 2
  have : π * (α + 2) = π * α + 2 * π := by ring
  rw [this, Real.cos_add_two_pi]

/-! ## §2 Evenness. -/

/-- **`sigma_neg`** — the substrate σ formula is even in α.

`σ(-α) = log₃|1 + 2·cos(π·(-α))| = log₃|1 + 2·cos(-π·α)|
      = log₃|1 + 2·cos(π·α)| = σ(α)` via `Real.cos_neg`. -/
theorem sigma_neg (α : ℝ) :
    PrincipiaTractalis.SigmaAbscissa.sigma (-α)
      = PrincipiaTractalis.SigmaAbscissa.sigma α := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  congr 2
  have : π * (-α) = -(π * α) := by ring
  rw [this, Real.cos_neg]

/-! ## §3 Companion: shift by −2. -/

/-- **`sigma_sub_two`** — the companion of `sigma_add_two`: `σ(α − 2) = σ(α)`. -/
theorem sigma_sub_two (α : ℝ) :
    PrincipiaTractalis.SigmaAbscissa.sigma (α - 2)
      = PrincipiaTractalis.SigmaAbscissa.sigma α := by
  have h : PrincipiaTractalis.SigmaAbscissa.sigma ((α - 2) + 2)
      = PrincipiaTractalis.SigmaAbscissa.sigma (α - 2) := sigma_add_two (α - 2)
  have hα : (α - 2) + 2 = α := by ring
  rw [hα] at h
  exact h.symm

/-! ## §4 Integer double-shift. -/

/-- **`sigma_add_two_int`** — the integer-shift form: `σ(α + 2·k) = σ(α)`
for every `k : ℤ`.

Direct via mathlib's `Real.cos_add_int_mul_two_pi`. -/
theorem sigma_add_two_int (α : ℝ) (k : ℤ) :
    PrincipiaTractalis.SigmaAbscissa.sigma (α + 2 * k)
      = PrincipiaTractalis.SigmaAbscissa.sigma α := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  congr 2
  have h : π * (α + 2 * (k : ℝ)) = π * α + (k : ℝ) * (2 * π) := by ring
  rw [h, Real.cos_add_int_mul_two_pi]

/-! ## §5 The three-conjunct capstone. -/

/-- **`sigma_symmetries_capstone`** — the framework-generic substrate σ
symmetry bundle.

Three conjuncts:
- Period 2 (`sigma_add_two`).
- Evenness (`sigma_neg`).
- Integer double-shift (`sigma_add_two_int`).

Every exact-σ closed form landed in r212–r239 lifts through this
capstone to an infinite ℤ-orbit of α-values with the same σ, plus
negation symmetry. -/
theorem sigma_symmetries_capstone :
    (∀ α : ℝ, PrincipiaTractalis.SigmaAbscissa.sigma (α + 2)
      = PrincipiaTractalis.SigmaAbscissa.sigma α) ∧
    (∀ α : ℝ, PrincipiaTractalis.SigmaAbscissa.sigma (-α)
      = PrincipiaTractalis.SigmaAbscissa.sigma α) ∧
    (∀ (α : ℝ) (k : ℤ), PrincipiaTractalis.SigmaAbscissa.sigma (α + 2 * k)
      = PrincipiaTractalis.SigmaAbscissa.sigma α) :=
  ⟨sigma_add_two, sigma_neg, sigma_add_two_int⟩

/-! ## §6 Axiom check. -/

#print axioms PrincipiaTractalis.SigmaSymmetries.sigma_add_two
#print axioms PrincipiaTractalis.SigmaSymmetries.sigma_neg
#print axioms PrincipiaTractalis.SigmaSymmetries.sigma_sub_two
#print axioms PrincipiaTractalis.SigmaSymmetries.sigma_add_two_int
#print axioms PrincipiaTractalis.SigmaSymmetries.sigma_symmetries_capstone

end PrincipiaTractalis.SigmaSymmetries
