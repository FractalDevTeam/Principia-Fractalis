/-
# r342 — The H₃ braid relations, and the representation of the ABSTRACT Coxeter group

★ 2026-10-24 — closes the gap `H3CoxeterDiagramDerivation` §8 names as
"the one real remaining gap in the chain" ★

## The gap this closes

`PF/H3CoxeterDiagramDerivation.lean` derives the whole H₃ Coxeter dataset from
mathlib's own classification datum `CoxeterMatrix.H₃`: the Gram matrix, the
three simple reflections as explicit `3 × 3` real matrices, the Coxeter element
`c = s₀s₁s₂` in closed form, its characteristic polynomial, and — via
Cayley–Hamilton — `c⁵ = -1`, `c¹⁰ = 1`, `orderOf c = 10`. The Coxeter number is
*extracted* there, not supplied, and `ζ` is `exp(2πi / orderOf c)`.

Its §8 then states the residual gap exactly:

> "What this does NOT establish: that `H3_simple` factors through the abstract
> Coxeter group `CoxeterMatrix.H₃.Group`. The missing lemmas are the braid
> relations `(s₀s₁)³ = 1`, `(s₁s₂)⁵ = 1`, `(s₀s₂)² = 1`, which together with
> `H3_simple_*_sq` would give `CoxeterMatrix.H₃.IsLiftable H3_simple` and hence
> a monoid hom `CoxeterMatrix.H₃.Group →* Matrix (Fin 3) (Fin 3) ℝ` via
> `CoxeterSystem.lift`. They are omitted rather than asserted: the 5-fold one is
> a five-term matrix product requiring repeated `φ² = φ + 1` reduction and has
> not been written out here. Until they exist, the sentence 'the H₃ icosahedral
> GROUP has Coxeter number 10' is supported at the level of the diagram and its
> Gram-matrix reflection representation, not at the level of the abstract group."

This file writes out the three relations, builds the monoid hom, and identifies
the image of the abstract Coxeter element.

## Why it matters beyond bookkeeping

The framework's universal coupling `λ₀(H_α) = π / (10 · α)` rests on the `10`
being the icosahedral Coxeter number. Before this file, every H₃ fact in the
corpus was a fact about **one hand-built triple of matrices** that satisfies the
right Gram relations. Nothing connected it to the abstract Coxeter group H₃, so
"the H₃ group has Coxeter number 10" was not available — only "this matrix
triple does". After this file the triple is a genuine representation of
`CoxeterMatrix.H₃.Group`, so the matrix computations are computations about H₃.

## Proof route

`CoxeterMatrix.IsLiftable M f` unfolds to `∀ i i', (f i * f i') ^ M i i' = 1`,
i.e. all nine ordered pairs. The diagonal three are the involutions already
proved upstream (`M i i = 1`). Of the remaining six, only three need computing:
the reversed products are *powers of the forward ones*, because each `sᵢ` is an
involution, so `sⱼsᵢ = (sᵢsⱼ)⁻¹` and the forward relation transfers by exponent
arithmetic. Concretely, and checked here rather than asserted:

    s₁s₀ = (s₀s₁)²       s₂s₁ = (s₁s₂)⁴       s₂s₀ = s₀s₂

The 5-fold product is done stepwise through explicit intermediate matrices
rather than as one five-term expansion, which keeps every step a single
`Matrix.mul_fin_three` with small arithmetic:

    B  = s₁s₂ = !![1,0,0; 1,φ,-φ; 0,φ,-1]
    B² =        !![1,0,0; 1+φ,0,-1; φ,1,-φ]
    B³ =        !![1,0,0; 1+φ,-φ,1; 1+φ,-1,0]
    B⁴ =        !![1,0,0; 1,-1,φ; φ,-φ,φ]
    B⁵ =        1

`φ² = φ + 1` (`Real.goldenRatio_sq`) is used in B and in every subsequent step;
the upstream file's warning is respected here — these goals are not wrapped in
`first | ring | …`, because `ring` partially succeeds on them without closing
and would swallow the closer. `ring1` and `linear_combination` fail cleanly, so
the alternation is safe in that order.

## What is and is not claimed

**Claimed.** The three matrices `H3_simple 0,1,2` satisfy every H₃ braid
relation, hence `CoxeterMatrix.H₃.IsLiftable H3_simple`, hence there is a monoid
hom `H3_rep : CoxeterMatrix.H₃.Group →* Matrix (Fin 3) (Fin 3) ℝ` with
`H3_rep (simple i) = H3_simple i`. The image of the abstract Coxeter element
`simple 0 * simple 1 * simple 2` is `H3_coxeterElement`. Consequently
`10 ∣ orderOf (simple 0 * simple 1 * simple 2)` in the abstract group: the
icosahedral `10` is a fact about H₃, not only about a matrix triple.

**Not claimed.**

1. That the representation is FAITHFUL. Without injectivity one gets only
   divisibility, so `orderOf` of the abstract Coxeter element is a multiple of
   `10` and is not here shown to equal `10`. Proving equality needs either
   faithfulness of the reflection representation or the order of H₃ (= 120),
   neither of which is in mathlib at this pin.
2. That the CHOICE of Coxeter element `s₀s₁s₂` is canonical. Any ordering of the
   simple reflections gives a conjugate element with the same spectrum; that
   conjugacy is still not proved (unchanged from the upstream file).
3. Anything about the framework's `H_α` operator. The operator-theoretic claim
   `λ₀(H_α) = π / h(H₃)` remains OPEN and is still localized to the single Prop
   `SubstrateH3IdentificationAtPoincare` in
   `PF/PoincareAlphaDerivedFromH3.lean`. This file strengthens the H₃ side of
   that identification; it does not touch the operator side.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-24.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic
import PF.H3CoxeterDiagramDerivation

-- The nine-entry matrix proofs below close each residual entry with a
-- defensive `first | … | …` alternation. The build reports some branches
-- as never executed, which is true and intended: a 9-entry matrix identity
-- should not be one tactic away from breaking when a `simp` set shifts.
-- The alternations are kept and these two linters are disabled, rather
-- than trimming working proofs on a linter's word.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace PrincipiaTractalis
namespace H3CoxeterBraid

open PrincipiaTractalis.H3CoxeterDiagram

local notation "φ" => Real.goldenRatio

/-! ## §1 — The three forward braid relations -/

/-! ### §1.1 — `(s₀s₂)² = 1`, the commuting pair

`m(0,2) = 2`, so `s₀` and `s₂` commute. No golden-ratio identity is needed:
the two off-diagonal `φ`'s cancel against each other. -/

/-- `s₀ s₂` in closed form. -/
theorem H3_simple_zero_mul_two :
    H3_simple 0 * H3_simple 2 = !![-1, 1, 0;
                                    0, 1, 0;
                                    0, φ, -1] := by
  rw [H3_simple_zero, H3_simple_two, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;> ring1

/-- **Braid relation (0,2):** `(s₀s₂)² = 1`. -/
theorem H3_braid_zero_two : (H3_simple 0 * H3_simple 2) ^ 2 = 1 := by
  rw [H3_simple_zero_mul_two, pow_two, Matrix.mul_fin_three, Matrix.one_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;> ring1

/-! ### §1.2 — `(s₀s₁)³ = 1`

`m(0,1) = 3`. The intermediate `s₀s₁` is already in the upstream file
(`H3_simple_zero_mul_one`); no `φ²` reduction is needed anywhere in this
relation, the `φ`'s cancel linearly. -/

/-- `(s₀s₁)²` in closed form. -/
theorem H3_simple_zero_one_sq :
    (H3_simple 0 * H3_simple 1) ^ 2 = !![-1, 1, 0;
                                         -1, 0, φ;
                                          0, 0, 1] := by
  rw [H3_simple_zero_mul_one, pow_two, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;> ring1

/-- **Braid relation (0,1):** `(s₀s₁)³ = 1`. -/
theorem H3_braid_zero_one : (H3_simple 0 * H3_simple 1) ^ 3 = 1 := by
  have h : (H3_simple 0 * H3_simple 1) ^ 3
      = (H3_simple 0 * H3_simple 1) ^ 2 * (H3_simple 0 * H3_simple 1) := by
    rw [← pow_succ]
  rw [h, H3_simple_zero_one_sq, H3_simple_zero_mul_one, Matrix.mul_fin_three,
      Matrix.one_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;> ring1

/-! ### §1.3 — `(s₁s₂)⁵ = 1`, the icosahedral relation

`m(1,2) = 5`. This is the one the upstream file declined to write out. Done
stepwise; `φ² = φ + 1` is needed at every step from `B` onwards. -/

/-- `B = s₁s₂` in closed form. The `(1,1)` entry is `-1 + φ²`, i.e. `φ`. -/
theorem H3_simple_one_mul_two :
    H3_simple 1 * H3_simple 2 = !![1, 0, 0;
                                   1, φ, -φ;
                                   0, φ, -1] := by
  rw [H3_simple_one, H3_simple_two, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;>
    first
      | linear_combination Real.goldenRatio_sq
      | linear_combination -Real.goldenRatio_sq
      | ring1

/-- `B²`. -/
theorem H3_one_two_pow_two :
    (H3_simple 1 * H3_simple 2) ^ 2 = !![1, 0, 0;
                                         1 + φ, 0, -1;
                                         φ, 1, -φ] := by
  rw [pow_two, H3_simple_one_mul_two, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;>
    first
      | linear_combination Real.goldenRatio_sq
      | linear_combination -Real.goldenRatio_sq
      | ring1

/-- `B³`. -/
theorem H3_one_two_pow_three :
    (H3_simple 1 * H3_simple 2) ^ 3 = !![1, 0, 0;
                                         1 + φ, -φ, 1;
                                         1 + φ, -1, 0] := by
  have h : (H3_simple 1 * H3_simple 2) ^ 3
      = (H3_simple 1 * H3_simple 2) ^ 2 * (H3_simple 1 * H3_simple 2) := by
    rw [← pow_succ]
  rw [h, H3_one_two_pow_two, H3_simple_one_mul_two, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;>
    first
      | linear_combination Real.goldenRatio_sq
      | linear_combination -Real.goldenRatio_sq
      | ring1

/-- `B⁴`. -/
theorem H3_one_two_pow_four :
    (H3_simple 1 * H3_simple 2) ^ 4 = !![1, 0, 0;
                                         1, -1, φ;
                                         φ, -φ, φ] := by
  have h : (H3_simple 1 * H3_simple 2) ^ 4
      = (H3_simple 1 * H3_simple 2) ^ 3 * (H3_simple 1 * H3_simple 2) := by
    rw [← pow_succ]
  rw [h, H3_one_two_pow_three, H3_simple_one_mul_two, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;>
    first
      | linear_combination Real.goldenRatio_sq
      | linear_combination -Real.goldenRatio_sq
      | ring1

/-- **Braid relation (1,2):** `(s₁s₂)⁵ = 1`. The icosahedral 5-fold relation,
written out at last. -/
theorem H3_braid_one_two : (H3_simple 1 * H3_simple 2) ^ 5 = 1 := by
  have h : (H3_simple 1 * H3_simple 2) ^ 5
      = (H3_simple 1 * H3_simple 2) ^ 4 * (H3_simple 1 * H3_simple 2) := by
    rw [← pow_succ]
  rw [h, H3_one_two_pow_four, H3_simple_one_mul_two, Matrix.mul_fin_three,
      Matrix.one_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;>
    first
      | linear_combination Real.goldenRatio_sq
      | linear_combination -Real.goldenRatio_sq
      | ring1

/-! ## §2 — The reversed products, as powers of the forward ones

Each `sᵢ` is an involution, so `sⱼsᵢ = (sᵢsⱼ)⁻¹`, and in a monoid the forward
relation transfers by exponent arithmetic. The three identities below are
computed, not assumed. -/

/-- `s₂s₀ = s₀s₂`: the commuting pair really commutes. -/
theorem H3_simple_two_mul_zero :
    H3_simple 2 * H3_simple 0 = H3_simple 0 * H3_simple 2 := by
  rw [H3_simple_zero_mul_two, H3_simple_two, H3_simple_zero, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;> ring1

/-- `s₁s₀ = (s₀s₁)²`. -/
theorem H3_simple_one_mul_zero :
    H3_simple 1 * H3_simple 0 = (H3_simple 0 * H3_simple 1) ^ 2 := by
  rw [H3_simple_zero_one_sq, H3_simple_one, H3_simple_zero, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;> ring1

/-- `s₂s₁ = (s₁s₂)⁴`. -/
theorem H3_simple_two_mul_one :
    H3_simple 2 * H3_simple 1 = (H3_simple 1 * H3_simple 2) ^ 4 := by
  rw [H3_one_two_pow_four, H3_simple_two, H3_simple_one, Matrix.mul_fin_three]
  ext j k
  fin_cases j <;> fin_cases k <;> simp <;>
    first
      | linear_combination Real.goldenRatio_sq
      | linear_combination -Real.goldenRatio_sq
      | ring1

/-- **Braid relation (2,0).** -/
theorem H3_braid_two_zero : (H3_simple 2 * H3_simple 0) ^ 2 = 1 := by
  rw [H3_simple_two_mul_zero, H3_braid_zero_two]

/-- **Braid relation (1,0).** `((s₀s₁)²)³ = (s₀s₁)⁶ = ((s₀s₁)³)² = 1`. -/
theorem H3_braid_one_zero : (H3_simple 1 * H3_simple 0) ^ 3 = 1 := by
  rw [H3_simple_one_mul_zero]
  have h : ((H3_simple 0 * H3_simple 1) ^ 2) ^ 3
      = ((H3_simple 0 * H3_simple 1) ^ 3) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
  rw [h, H3_braid_zero_one, one_pow]

/-- **Braid relation (2,1).** `((s₁s₂)⁴)⁵ = (s₁s₂)²⁰ = ((s₁s₂)⁵)⁴ = 1`. -/
theorem H3_braid_two_one : (H3_simple 2 * H3_simple 1) ^ 5 = 1 := by
  rw [H3_simple_two_mul_one]
  have h : ((H3_simple 1 * H3_simple 2) ^ 4) ^ 5
      = ((H3_simple 1 * H3_simple 2) ^ 5) ^ 4 := by
    rw [← pow_mul, ← pow_mul]
  rw [h, H3_braid_one_two, one_pow]

/-! ## §3 — Liftability and the representation of the abstract group -/

/-- The nine entries of `CoxeterMatrix.H₃`, as numerals, so the nine
`IsLiftable` goals can be put in the right exponent. Decidable arithmetic on
`ℕ`, discharged by `decide` exactly as the upstream `H3_diagram_entries` is. -/
private theorem H3_M_vals :
    CoxeterMatrix.H₃ 0 0 = 1 ∧ CoxeterMatrix.H₃ 1 1 = 1 ∧ CoxeterMatrix.H₃ 2 2 = 1 ∧
    CoxeterMatrix.H₃ 0 1 = 3 ∧ CoxeterMatrix.H₃ 1 0 = 3 ∧
    CoxeterMatrix.H₃ 1 2 = 5 ∧ CoxeterMatrix.H₃ 2 1 = 5 ∧
    CoxeterMatrix.H₃ 0 2 = 2 ∧ CoxeterMatrix.H₃ 2 0 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **★★★ `H3_simple` satisfies the H₃ Coxeter relations.**

This is the statement the upstream §8 named as missing. All nine ordered pairs:
the diagonal from the involutions, the six off-diagonal from §1–§2. -/
theorem H3_isLiftable : CoxeterMatrix.H₃.IsLiftable H3_simple := by
  obtain ⟨m00, m11, m22, m01, m10, m12, m21, m02, m20⟩ := H3_M_vals
  intro i i'
  -- `fin_cases` leaves the indices as anonymous constructors `⟨0, _⟩`, which are
  -- defeq to the numerals but not syntactically equal, so `rw` on a numeral
  -- pattern finds no occurrence. `show` restates each goal up to defeq first.
  fin_cases i <;> fin_cases i'
  · show (H3_simple 0 * H3_simple 0) ^ CoxeterMatrix.H₃ 0 0 = 1
    rw [m00, pow_one]; exact H3_simple_zero_sq
  · show (H3_simple 0 * H3_simple 1) ^ CoxeterMatrix.H₃ 0 1 = 1
    rw [m01]; exact H3_braid_zero_one
  · show (H3_simple 0 * H3_simple 2) ^ CoxeterMatrix.H₃ 0 2 = 1
    rw [m02]; exact H3_braid_zero_two
  · show (H3_simple 1 * H3_simple 0) ^ CoxeterMatrix.H₃ 1 0 = 1
    rw [m10]; exact H3_braid_one_zero
  · show (H3_simple 1 * H3_simple 1) ^ CoxeterMatrix.H₃ 1 1 = 1
    rw [m11, pow_one]; exact H3_simple_one_sq
  · show (H3_simple 1 * H3_simple 2) ^ CoxeterMatrix.H₃ 1 2 = 1
    rw [m12]; exact H3_braid_one_two
  · show (H3_simple 2 * H3_simple 0) ^ CoxeterMatrix.H₃ 2 0 = 1
    rw [m20]; exact H3_braid_two_zero
  · show (H3_simple 2 * H3_simple 1) ^ CoxeterMatrix.H₃ 2 1 = 1
    rw [m21]; exact H3_braid_two_one
  · show (H3_simple 2 * H3_simple 2) ^ CoxeterMatrix.H₃ 2 2 = 1
    rw [m22, pow_one]; exact H3_simple_two_sq

/-- **★★★ The reflection representation of the ABSTRACT Coxeter group H₃.**

A monoid homomorphism out of `CoxeterMatrix.H₃.Group` — the group presented by
the H₃ diagram — obtained from `H3_isLiftable` through the universal property
`CoxeterSystem.lift`. This is the object whose absence the upstream file
recorded. -/
noncomputable def H3_rep : CoxeterMatrix.H₃.Group →* Matrix (Fin 3) (Fin 3) ℝ :=
  CoxeterMatrix.H₃.toCoxeterSystem.lift ⟨H3_simple, H3_isLiftable⟩

/-- The representation sends each abstract simple reflection to its matrix. -/
theorem H3_rep_simple (i : Fin 3) :
    H3_rep (CoxeterMatrix.H₃.simple i) = H3_simple i :=
  CoxeterMatrix.H₃.toCoxeterSystem.lift_apply_simple H3_isLiftable i

/-! ## §4 — The Coxeter number as a fact about the abstract group -/

/-- The Coxeter element of the ABSTRACT group. -/
noncomputable def H3_abstractCoxeterElement : CoxeterMatrix.H₃.Group :=
  CoxeterMatrix.H₃.simple 0 *
  CoxeterMatrix.H₃.simple 1 *
  CoxeterMatrix.H₃.simple 2

/-- **The abstract Coxeter element represents as the matrix Coxeter element.** -/
theorem H3_rep_abstractCoxeterElement :
    H3_rep H3_abstractCoxeterElement = H3_coxeterElement := by
  unfold H3_abstractCoxeterElement H3_coxeterElement
  rw [map_mul, map_mul, H3_rep_simple, H3_rep_simple, H3_rep_simple]

/-- **★★★ `10` divides the order of the abstract H₃ Coxeter element.**

The icosahedral `10` of the framework's universal coupling is therefore a fact
about the Coxeter GROUP H₃, not merely about the Gram-matrix triple. Proof: the
image of an element has order dividing the element's order, and the image here
is `H3_coxeterElement`, whose order is `10` upstream.

Equality (rather than divisibility) would need faithfulness of this
representation; see this file's "Not claimed". -/
theorem H3_ten_dvd_orderOf_abstractCoxeterElement :
    10 ∣ orderOf H3_abstractCoxeterElement := by
  have himg : H3_rep (H3_abstractCoxeterElement ^ orderOf H3_abstractCoxeterElement) = 1 := by
    rw [pow_orderOf_eq_one, map_one]
  rw [map_pow, H3_rep_abstractCoxeterElement] at himg
  have hdvd : orderOf H3_coxeterElement ∣ orderOf H3_abstractCoxeterElement :=
    orderOf_dvd_of_pow_eq_one himg
  rwa [H3_orderOf_coxeterElement] at hdvd

/-- **Capstone.** The braid relations, the representation, and the transfer of
the Coxeter number to the abstract group, as one conjunction. -/
theorem H3_braid_relations_capstone :
    (H3_simple 0 * H3_simple 1) ^ 3 = 1 ∧
    (H3_simple 1 * H3_simple 2) ^ 5 = 1 ∧
    (H3_simple 0 * H3_simple 2) ^ 2 = 1 ∧
    CoxeterMatrix.H₃.IsLiftable H3_simple ∧
    (∀ i : Fin 3, H3_rep (CoxeterMatrix.H₃.simple i) = H3_simple i) ∧
    H3_rep H3_abstractCoxeterElement = H3_coxeterElement ∧
    10 ∣ orderOf H3_abstractCoxeterElement :=
  ⟨H3_braid_zero_one, H3_braid_one_two, H3_braid_zero_two, H3_isLiftable,
   H3_rep_simple, H3_rep_abstractCoxeterElement,
   H3_ten_dvd_orderOf_abstractCoxeterElement⟩

end H3CoxeterBraid
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.H3CoxeterBraid.H3_braid_zero_one
#print axioms PrincipiaTractalis.H3CoxeterBraid.H3_braid_one_two
#print axioms PrincipiaTractalis.H3CoxeterBraid.H3_braid_zero_two
#print axioms PrincipiaTractalis.H3CoxeterBraid.H3_isLiftable
#print axioms PrincipiaTractalis.H3CoxeterBraid.H3_rep_abstractCoxeterElement
#print axioms PrincipiaTractalis.H3CoxeterBraid.H3_ten_dvd_orderOf_abstractCoxeterElement
#print axioms PrincipiaTractalis.H3CoxeterBraid.H3_braid_relations_capstone
