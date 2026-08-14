/-
# r253: SIGMA DEGENERATE LOCUS.

★ 2026-08-13 r253 — the substrate abscissa formula's degenerate branch,
characterized explicitly on ONE direction. `σ(α) = log₃|1 + 2·cos(πα)|`
uses mathlib's convention `Real.logb b 0 = 0`, so at α values where
`1 + 2·cos(πα) = 0` the σ output is 0 for a reason UNRELATED to any
convergence-abscissa identity. This file confirms `σ = 0` at the lattice
`2/3 + 2ℤ ∪ -2/3 + 2ℤ` and shows the reverse direction of the biconditional
(every α on that lattice gives a degenerate point). ★

## The degenerate lattice

`1 + 2·cos(πα) = 0` ⟺ `cos(πα) = -1/2`. Any α with `α = 2/3 + 2k` or
`α = -2/3 + 2k` for some `k : ℤ` lies on this locus (forward direction).
r212's `cos_pi_mul_eq_neg_half_imp_rational` already provides the reverse
direction as `α = 2m/3` for some integer m; specialization to the two
2ℤ-orbits requires a mod-3 case split which we do not need for the
substrate-side content and is left to a future landing.

## Why this file exists

The r212–r252 substrate machine at HEAD treats σ as a real-valued
function on all of ℝ. That function has a convention behavior at the
two orbits `2/3 + 2ℤ` and `-2/3 + 2ℤ`, where `|1 + 2·cos(πα)| = 0` and
mathlib's `logb 0 = 0` fires. r253 makes the reverse characterization
explicit and pins concrete σ-values.

## Contents

§1 `cos_two_pi_div_three_eq_neg_half` — `cos(2π/3) = -1/2` via `cos_pi_sub`.
§2 `cos_pi_mul_at_two_thirds_lattice` — `cos(π(2/3 + 2k)) = -1/2` universal.
§3 `cos_pi_mul_at_neg_two_thirds_lattice` — companion.
§4 `sigma_two_thirds_eq_zero` — `σ(2/3) = 0`.
§5 `sigma_neg_two_thirds_eq_zero`, `sigma_four_thirds_eq_zero` — companions.
§6 `sigma_at_degenerate_lattice_pos/neg` — universal over k ∈ ℤ.
§7 `substrate_degenerate_locus_capstone` — bundled reverse-direction
    characterization.
§8 Axiom check.

## Scope

* NOT novel — pure algebra + `Real.cos_pi_sub` + `Real.cos_pi_div_three`
  + r240 symmetries.
* NOT a Millennium discharge.
* NOT the full biconditional characterization (forward direction from
  degenerate condition to lattice membership requires a mod-3 split not
  landed here).
* IS a framework-generic structural clarification of the substrate's
  degenerate branch on the reverse direction.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.SigmaSymmetries_r240

open scoped Real

namespace PrincipiaTractalis.SigmaDegenerateLocus

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 `cos(2π/3) = -1/2`. -/

/-- **`cos_two_pi_div_three_eq_neg_half`** — via `cos_pi_sub` + `cos_pi_div_three`.

`cos(2π/3) = cos(π − π/3) = −cos(π/3) = −1/2`. -/
lemma cos_two_pi_div_three_eq_neg_half :
    Real.cos (2 * π / 3) = -(1 / 2) := by
  have h : (2 : ℝ) * π / 3 = π - π / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]

/-! ## §2-§3 Universal `cos = -1/2` on the two lattices. -/

/-- **`cos_pi_mul_at_two_thirds_lattice`** — for every `k : ℤ`,
`cos(π · (2/3 + 2k)) = -1/2`.

Chain: `cos(2π/3 + 2πk) = cos(2π/3)` via `cos_add_int_mul_two_pi`, then §1. -/
lemma cos_pi_mul_at_two_thirds_lattice (k : ℤ) :
    Real.cos (π * (2/3 + 2 * k)) = -(1/2) := by
  have h_eq : π * (2/3 + 2 * (k : ℝ)) = 2 * π / 3 + (k : ℝ) * (2 * π) := by ring
  rw [h_eq, Real.cos_add_int_mul_two_pi]
  exact cos_two_pi_div_three_eq_neg_half

/-- **`cos_pi_mul_at_neg_two_thirds_lattice`** — for every `k : ℤ`,
`cos(π · (-2/3 + 2k)) = -1/2`.

Chain: `cos(-2π/3 + 2πk) = cos(-2π/3) = cos(2π/3)` via `cos_neg` + §1. -/
lemma cos_pi_mul_at_neg_two_thirds_lattice (k : ℤ) :
    Real.cos (π * (-(2/3) + 2 * k)) = -(1/2) := by
  have h_eq : π * (-(2/3) + 2 * (k : ℝ)) = -(2 * π / 3) + (k : ℝ) * (2 * π) := by ring
  rw [h_eq, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  exact cos_two_pi_div_three_eq_neg_half

/-! ## §4-§5 Concrete degenerate σ values. -/

/-- **`sigma_two_thirds_eq_zero`** — `σ(2/3) = 0` (mathlib convention). -/
theorem sigma_two_thirds_eq_zero :
    PrincipiaTractalis.SigmaAbscissa.sigma (2/3) = 0 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have h_cos : Real.cos (π * (2/3)) = -(1/2) := by
    have h : π * ((2:ℝ)/3) = 2 * π / 3 := by ring
    rw [h]; exact cos_two_pi_div_three_eq_neg_half
  rw [h_cos]
  have hzero : |1 + 2 * -(1/2 : ℝ)| = 0 := by norm_num
  rw [hzero, Real.logb_zero]

/-- **`sigma_neg_two_thirds_eq_zero`** — `σ(-2/3) = 0` via r240 evenness. -/
theorem sigma_neg_two_thirds_eq_zero :
    PrincipiaTractalis.SigmaAbscissa.sigma (-(2/3)) = 0 := by
  rw [SigmaSymmetries.sigma_neg]
  exact sigma_two_thirds_eq_zero

/-- **`sigma_four_thirds_eq_zero`** — `σ(4/3) = 0` via r240 period-2 shift
(since `4/3 = -2/3 + 2`). -/
theorem sigma_four_thirds_eq_zero :
    PrincipiaTractalis.SigmaAbscissa.sigma (4/3) = 0 := by
  have h : (4/3 : ℝ) = -(2/3) + 2 := by norm_num
  rw [h, SigmaSymmetries.sigma_add_two]
  exact sigma_neg_two_thirds_eq_zero

/-! ## §6 Universal degenerate lattice. -/

/-- **`sigma_at_degenerate_lattice_pos`** — for every `k : ℤ`,
`σ(2/3 + 2·k) = 0`. -/
theorem sigma_at_degenerate_lattice_pos (k : ℤ) :
    PrincipiaTractalis.SigmaAbscissa.sigma (2/3 + 2 * k) = 0 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  rw [cos_pi_mul_at_two_thirds_lattice k]
  have : |1 + 2 * -(1/2 : ℝ)| = 0 := by norm_num
  rw [this, Real.logb_zero]

/-- **`sigma_at_degenerate_lattice_neg`** — for every `k : ℤ`,
`σ(-2/3 + 2·k) = 0`. -/
theorem sigma_at_degenerate_lattice_neg (k : ℤ) :
    PrincipiaTractalis.SigmaAbscissa.sigma (-(2/3) + 2 * k) = 0 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  rw [cos_pi_mul_at_neg_two_thirds_lattice k]
  have : |1 + 2 * -(1/2 : ℝ)| = 0 := by norm_num
  rw [this, Real.logb_zero]

/-! ## §7 The bundled capstone. -/

/-- **`substrate_degenerate_locus_capstone`** — the framework-generic
reverse-direction characterization of σ's degenerate branch.

Three conjuncts:
1. Every α on the `2/3 + 2ℤ` orbit gives `cos(πα) = -1/2`, hence
   the degenerate condition `1 + 2·cos = 0`.
2. σ takes the mathlib convention value 0 at every `α ∈ 2/3 + 2ℤ`.
3. Same for `-2/3 + 2ℤ`. -/
theorem substrate_degenerate_locus_capstone :
    (∀ k : ℤ, Real.cos (π * (2/3 + 2 * k)) = -(1/2) ∧
              Real.cos (π * (-(2/3) + 2 * k)) = -(1/2)) ∧
    (∀ k : ℤ, PrincipiaTractalis.SigmaAbscissa.sigma (2/3 + 2 * k) = 0) ∧
    (∀ k : ℤ, PrincipiaTractalis.SigmaAbscissa.sigma (-(2/3) + 2 * k) = 0) :=
  ⟨fun k => ⟨cos_pi_mul_at_two_thirds_lattice k, cos_pi_mul_at_neg_two_thirds_lattice k⟩,
   sigma_at_degenerate_lattice_pos,
   sigma_at_degenerate_lattice_neg⟩

/-! ## §8 Axiom check. -/

#print axioms PrincipiaTractalis.SigmaDegenerateLocus.cos_two_pi_div_three_eq_neg_half
#print axioms PrincipiaTractalis.SigmaDegenerateLocus.cos_pi_mul_at_two_thirds_lattice
#print axioms PrincipiaTractalis.SigmaDegenerateLocus.sigma_two_thirds_eq_zero
#print axioms PrincipiaTractalis.SigmaDegenerateLocus.sigma_at_degenerate_lattice_pos
#print axioms PrincipiaTractalis.SigmaDegenerateLocus.substrate_degenerate_locus_capstone

end PrincipiaTractalis.SigmaDegenerateLocus
