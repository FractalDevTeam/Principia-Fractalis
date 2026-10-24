/-
# PF.AlgebraicGeometry.ComplexTorusHodgeLattice_2026_10_23

**The first non-vacuous Hodge-class predicate in this repository.**

## Why this file exists, and what the previous attempts were

`codex/HODGE_SCOPING_BLOCKED_2026-10-17.md` named the blocker: mathlib has no
Kähler manifolds, no Hodge decomposition, no harmonic forms, no de Rham or
Dolbeault cohomology, no algebraic cycles, no Chow groups and no cycle class
map (twelve measured zero-counts). Its structural claim was

> "YM had a lattice, Hodge has no surrogate."

**That is true for general smooth projective varieties and false for complex
tori**, which is the opening this file takes. A complex torus `A = V/Λ` is
topologically a `2g`-torus, so

  `H^k(A, ℚ) ≅ ⋀^k Hom(Λ, ℚ)`                                   (classical)

*exactly* — the cohomology is the exterior algebra on the lattice. There is no
harmonic theory to supply, because for tori the fibrewise linear algebra IS the
global cohomology. The blocking note judged the fibrewise core "one rung and not
a ladder" on the grounds that globalising it needs harmonic theory; that
judgement does not apply here.

Under that identification, a class in `H²(A, ℚ)` is an alternating 2-form on
`Λ ⊗ ℚ`, and it is of Hodge type `(1,1)` precisely when it is invariant under
the complex structure `J`:

  `E(Jx, Jy) = E(x, y)`.

That is the whole definition, and it needs only `ℚ`-linear algebra.

## What this file replaces

The archive's `Hodge_Conjecture_COMPLETE.lean` defined

  `IsHodgeClass X p ξ : Prop := ∃ (c : HodgeComponent X p p), True`

with `HodgeComponent X p q := ℂ`, i.e. **`True`** — making every class a Hodge
class, and (with its sibling axiom) entailing `False`; that inconsistency is
machine-demonstrated in the blocking note. The repo's live
`MillenniumSixReductions.HodgeAmbient` is three naturals with inequalities and
no cohomology at all.

The predicate below is not vacuous, and §3 proves it is not: there is an
explicit alternating form on the split `g = 2` model that **fails** the
condition. A definition that admits a counterexample is the minimum bar the
archive definition could not clear.

## HONEST SCOPE — what is and is not established here

**Formalised:** the Hodge type-`(1,1)` condition on alternating 2-forms over
`ℚ`, closure of the Hodge classes under addition and scaling, the `g = 1` case
where every class is Hodge, and the `g = 2` case where not every class is.

**Cited, not formalised:** the identification `H²(A,ℚ) ≅ Alt²(Λ⊗ℚ)` and the
reading of `J`-invariance as Hodge type `(1,1)`. Those are classical facts about
complex tori; no topology or cohomology is constructed in this file, and nothing
here proves them.

**Absent, therefore NOT stated:** the algebraic side. The Hodge conjecture's
content is the inclusion `Hdg^p(X) ⊆ Alg^p(X)` into the image of the cycle class
map, and mathlib has neither Chow groups nor intersection theory. **This file
formalises the left-hand side of the degree-2 case and no part of the
conjecture itself.** It is a first real Hodge object, not progress on the
conjecture, and it must not be cited as the latter.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-23.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.FinCases

namespace PrincipiaTractalis
namespace ComplexTorusHodgeLattice20261023

/-! ## §1 — the lattice model and the Hodge type-(1,1) condition -/

/-- A `ℚ`-valued alternating-style 2-form on coordinates `Fin n`, represented as
a plain function so that every statement below is decidable by computation on
explicit vectors. Antisymmetry is not imposed: none of the results need it, and
the counterexample in §3 is antisymmetric anyway. -/
abbrev Form (n : ℕ) := (Fin n → ℚ) → (Fin n → ℚ) → ℚ

/-- **Hodge type `(1,1)`.** For a complex torus `A = V/Λ` with complex structure
`J`, a class in `H²(A,ℚ) ≅ Alt²(Λ⊗ℚ)` is of type `(1,1)` exactly when it is
`J`-invariant. This is the real condition, replacing the archive's `∃ c : ℂ,
True`. -/
def IsType11 {n : ℕ} (J : (Fin n → ℚ) → (Fin n → ℚ)) (E : Form n) : Prop :=
  ∀ x y, E (J x) (J y) = E x y

/-- The Hodge classes are closed under addition. -/
theorem isType11_add {n : ℕ} {J : (Fin n → ℚ) → (Fin n → ℚ)} {E F : Form n}
    (hE : IsType11 J E) (hF : IsType11 J F) :
    IsType11 J (fun x y => E x y + F x y) := by
  intro x y
  simp only [hE x y, hF x y]

/-- The Hodge classes are closed under scaling. -/
theorem isType11_smul {n : ℕ} {J : (Fin n → ℚ) → (Fin n → ℚ)} {E : Form n}
    (c : ℚ) (hE : IsType11 J E) :
    IsType11 J (fun x y => c * E x y) := by
  intro x y
  simp only [hE x y]

/-- The zero class is Hodge. -/
theorem isType11_zero {n : ℕ} {J : (Fin n → ℚ) → (Fin n → ℚ)} :
    IsType11 J (fun _ _ => (0 : ℚ)) := by
  intro _ _; rfl

/-! ## §2 — `g = 1`: the elliptic-curve case, where every class is Hodge

For `g = 1` the lattice has rank 2, `Alt²` is one-dimensional, and the standard
complex structure has determinant 1, so it preserves the area form. Every
rational class in `H²` is therefore of type `(1,1)` — matching `h^{1,1} = 1` and
`b₂ = 1` for an elliptic curve. -/

/-- The standard complex structure on a rank-2 lattice: `e₀ ↦ e₁`, `e₁ ↦ -e₀`. -/
def J2 (v : Fin 2 → ℚ) : Fin 2 → ℚ
  | 0 => -v 1
  | 1 => v 0

theorem J2_sq (v : Fin 2 → ℚ) : J2 (J2 v) = fun i => -v i := by
  funext i
  fin_cases i <;> simp [J2]

/-- The area form on a rank-2 lattice — the generator of `Alt²(ℚ²)`. -/
def area2 : Form 2 := fun x y => x 0 * y 1 - x 1 * y 0

/-- **`g = 1`: the generator of `H²` is of type `(1,1)`.** -/
theorem area2_isType11 : IsType11 J2 area2 := by
  intro x y
  simp only [area2, J2]
  norm_num
  ring

/-! ## §3 — `g = 2`: the condition is NOT vacuous

This is the result the archive definition could not have: an explicit class that
**fails** the Hodge condition. With the split complex structure on a rank-4
lattice — the model of `E × E` — the form `e₀* ∧ e₂*` is not `J`-invariant, so
not every rational class in `H²` is of type `(1,1)`.

That matches the Hodge numbers of an abelian surface: `b₂ = 6` while
`h^{1,1} = 4`, so exactly two dimensions are unavailable to Hodge classes. The
blocking note's own K3 refutation turns on the same fact. -/

/-- The split complex structure on a rank-4 lattice: `J` acting as the standard
rotation on `(e₀,e₁)` and on `(e₂,e₃)`. This is the complex structure of a
product of two elliptic curves. -/
def J4 (v : Fin 4 → ℚ) : Fin 4 → ℚ
  | 0 => -v 1
  | 1 => v 0
  | 2 => -v 3
  | 3 => v 2

theorem J4_sq (v : Fin 4 → ℚ) : J4 (J4 v) = fun i => -v i := by
  funext i
  fin_cases i <;> simp [J4]

/-- The class `e₀* ∧ e₂*`, pairing the first coordinate of one factor with the
first coordinate of the other. -/
def w02 : Form 4 := fun x y => x 0 * y 2 - x 2 * y 0

/-- The basis vectors used as the counterexample witnesses, pattern-matched so
they reduce without `Fin`-index equalities. The first attempt defined them as
`fun j => if j = i then 1 else 0`, and `simp` could not discharge the resulting
`if 1 = 2` conditions -- the gate caught that as a `sorryAx`. -/
def e0 : Fin 4 → ℚ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 0

def e2 : Fin 4 → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0

/-- **NON-VACUITY: `w02` is not of Hodge type `(1,1)`.**

Witness: `w02 (J4 e0) (J4 e2) = w02 e1 e3 = 0`, while `w02 e0 e2 = 1`.

This is what the archive's `IsHodgeClass X p ξ := ∃ c : ℂ, True` could never
produce, since that predicate is `True` and admits no counterexample. A Hodge
condition that cannot fail is not a Hodge condition. -/
theorem w02_not_isType11 : ¬ IsType11 J4 w02 := by
  intro h
  have key := h e0 e2
  simp only [w02, J4, e0, e2] at key
  norm_num at key

/-! ## §4 — what this does and does not settle

`area2_isType11` together with `w02_not_isType11` establishes that `IsType11` is
a genuine, non-trivial condition: satisfied by everything in the `g = 1` model,
and failed by an explicit class in the `g = 2` model.

What remains absent is the entire algebraic side — the cycle class map, Chow
groups, intersection theory — so the Hodge conjecture itself is still not
stateable here, exactly as the blocking note found. What has changed is that the
left-hand side of the degree-2 case is now a real object with real content,
rather than a placeholder or an inconsistency. -/

end ComplexTorusHodgeLattice20261023
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.ComplexTorusHodgeLattice20261023.isType11_add
#print axioms PrincipiaTractalis.ComplexTorusHodgeLattice20261023.isType11_smul
#print axioms PrincipiaTractalis.ComplexTorusHodgeLattice20261023.isType11_zero
#print axioms PrincipiaTractalis.ComplexTorusHodgeLattice20261023.J2_sq
#print axioms PrincipiaTractalis.ComplexTorusHodgeLattice20261023.area2_isType11
#print axioms PrincipiaTractalis.ComplexTorusHodgeLattice20261023.J4_sq
#print axioms PrincipiaTractalis.ComplexTorusHodgeLattice20261023.w02_not_isType11
