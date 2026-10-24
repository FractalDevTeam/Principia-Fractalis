/-
# r344 — The wedge product on algebraic differential forms, and `ω ∧ ω = 0`

★ 2026-10-24 — step 2's missing infrastructure, after a measurement that
refuted my own previous one ★

## A correction, first — and a correction to the correction

While scoping this file I concluded that mathlib has no wedge-product map on
exterior powers, on the strength of two greps over
`Mathlib/LinearAlgebra/ExteriorPower/`. **That was wrong: I searched the wrong
directory.** The graded structure lives in `ExteriorAlgebra/`.

Two things are worth stating precisely, because the first draft of this header
got the second one backwards:

* The false claim was never committed. It was made in session only.
  `codex/GROTHENDIECK_ROUTE_PRICED_2026-10-23.md` contains the string "wedge"
  zero times — checked, not remembered. An earlier draft of this header said
  the note "reported" it, which would have put a false statement about one
  committed artifact inside another. That is the precise failure
  `H3CoxeterDiagramDerivation`'s own header warns about, so it is corrected
  here rather than shipped.
* What the note DOES say (line 146) is that no `Derivation` into an exterior
  power exists anywhere in `Mathlib/LinearAlgebra/ExteriorPower/`, and that
  there is no prepared route for a non-linear-but-Leibniz map out of `⋀^n`.
  **Both remain true after this file.** A wedge is not a `d`: having the
  product does not give the derivation.

The structure that does exist:

* `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean:74`
      `abbrev exteriorPower : Submodule R (ExteriorAlgebra R M) :=
         LinearMap.range (ι R) ^ n`
  so `⋀[R]^n M` is a SUBMODULE of the exterior algebra, not a free-standing
  quotient.
* `Mathlib/LinearAlgebra/ExteriorAlgebra/Grading.lean:41`
      `instance : SetLike.GradedMonoid fun i : ℕ ↦ ⋀[R]^i M`
  and `:68` the full `GradedAlgebra` instance.

So multiplication in the exterior algebra already respects the grading, and
`SetLike.mul_mem_graded` turns it into exactly the wedge
`⋀^p × ⋀^q → ⋀^{p+q}`. The near-assertion "step 2 cannot even be *written*"
was one directory away from being believed, which is why it is recorded.

What the pricing note got RIGHT, and this file does not change:
`exteriorPower.alternatingMapLinearEquiv` does not apply to `d`, because it
yields an `S`-linear map while `d` is only `R`-linear with Leibniz over `S`;
and no `Derivation` into an exterior power exists in mathlib. **The missing
object is the derivation extending `d₀`, not the wedge.**

## What is here

On `Form R S n = ⋀[S]^n (KaehlerDifferential R S)` from
`PF/AlgebraicDeRhamAffineForms_r343.lean`:

* `wedge : Form p → Form q → Form (p + q)`, via graded multiplication;
* bilinearity in each argument, and vanishing against zero;
* **`wedge_self_degree_one : ω ∧ ω = 0`** for every 1-form, from
  `⋀^1 = range ι` together with `ExteriorAlgebra.ι_sq_zero`;
* hence `d₀ a ∧ d₀ a = 0` — the degree-1 shadow of `d ∘ d = 0`, and the first
  instance of that identity available without constructing `d₁`.

## What is and is not claimed

**Claimed.** The wedge product on algebraic differential forms exists, is
bilinear, and is alternating in degree 1; and the square of any exact 1-form
vanishes.

**Not claimed.**

1. `d_n` for `n ≥ 1`. Still absent, and therefore `d ∘ d = 0` is NOT proved in
   any degree above the shadow above. The route remains the one the pricing
   note names: define `d` on the free module of the Kähler presentation and
   descend, using that `Mathlib/RingTheory/Kaehler/Basic.lean` (628, 654)
   proves the kernel of `⊕ₓ B dx ↠ Ω_{B/R}` is SPANNED by the image of the
   relations. With the wedge now in hand, that construction is expressible;
   it is not done here.
2. Graded antisymmetry **in general**, i.e. `ω ∧ η = (-1)^{pq} η ∧ ω` for
   arbitrary degrees. That needs the graded-commutator machinery and is a
   separate piece of work. The DEGREE-1 case is proved
   (`wedge_antisymm_degree_one`) — an earlier draft of this header listed it
   here as unproved, which was true of the general statement and false of the
   degree-1 one, the only case `d₁` needs.
3. No complex, no cohomology, nothing global, nothing about the Hodge
   conjecture. Unchanged from r343, and for the same measured reasons:
   quasi-coherent sheaves, sheaf cohomology, hypercohomology and spectral
   sequences all count ZERO files in mathlib at this pin.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-24.
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Tactic
import PF.AlgebraicDeRhamAffineForms_r343

namespace PrincipiaTractalis
namespace AlgebraicDeRhamAffine

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-! ## §1 — The wedge product -/

/-- **The wedge product of algebraic differential forms.**

`⋀[S]^n` is a submodule of `ExteriorAlgebra S (Ω[S⁄R])`
(`ExteriorAlgebra/Basic.lean:74`), and multiplication there respects the
grading (`Grading.lean:41`), so the product of a `p`-form and a `q`-form is a
`(p+q)`-form. `SetLike.mul_mem_graded` supplies the membership proof. -/
noncomputable def wedge {p q : ℕ} (ω : Form R S p) (η : Form R S q) :
    Form R S (p + q) :=
  ⟨(ω : ExteriorAlgebra S (KaehlerDifferential R S)) *
     (η : ExteriorAlgebra S (KaehlerDifferential R S)),
   SetLike.mul_mem_graded ω.2 η.2⟩

/-- The underlying element of a wedge is the product in the exterior algebra,
by construction. -/
@[simp]
theorem wedge_coe {p q : ℕ} (ω : Form R S p) (η : Form R S q) :
    ((wedge R S ω η : Form R S (p + q)) :
        ExteriorAlgebra S (KaehlerDifferential R S))
      = (ω : ExteriorAlgebra S (KaehlerDifferential R S)) *
        (η : ExteriorAlgebra S (KaehlerDifferential R S)) :=
  rfl

/-! ## §2 — Bilinearity -/

theorem wedge_add_left {p q : ℕ} (ω₁ ω₂ : Form R S p) (η : Form R S q) :
    wedge R S (ω₁ + ω₂) η = wedge R S ω₁ η + wedge R S ω₂ η := by
  apply Subtype.ext
  simp only [wedge_coe, Submodule.coe_add, add_mul]

theorem wedge_add_right {p q : ℕ} (ω : Form R S p) (η₁ η₂ : Form R S q) :
    wedge R S ω (η₁ + η₂) = wedge R S ω η₁ + wedge R S ω η₂ := by
  apply Subtype.ext
  simp only [wedge_coe, Submodule.coe_add, mul_add]

theorem wedge_zero_left {p q : ℕ} (η : Form R S q) :
    wedge R S (0 : Form R S p) η = 0 := by
  apply Subtype.ext
  simp only [wedge_coe, Submodule.coe_zero, zero_mul]

theorem wedge_zero_right {p q : ℕ} (ω : Form R S p) :
    wedge R S ω (0 : Form R S q) = 0 := by
  apply Subtype.ext
  simp only [wedge_coe, Submodule.coe_zero, mul_zero]

theorem wedge_smul_left {p q : ℕ} (c : S) (ω : Form R S p) (η : Form R S q) :
    wedge R S (c • ω) η = c • wedge R S ω η := by
  apply Subtype.ext
  simp only [wedge_coe, Submodule.coe_smul_of_tower, smul_mul_assoc]

/-! ## §3 — The alternating property in degree 1, and `d₀ a ∧ d₀ a = 0` -/

/-- Every 1-form is `ι` of a Kähler differential: `⋀^1 = (range ι)^1 = range ι`.

The hypothesis type is written out in the POWER form rather than taken as
`ω.2` directly: `⋀[S]^1 M` is a constant application, defeq to
`LinearMap.range ι ^ 1` but not syntactically equal to it, so `rw [pow_one]`
cannot fire on it. Stating the type explicitly gives `rw` a syntactic match,
and `ω.2` still typechecks against it because the abbrev is reducible. -/
theorem exists_iota_of_degree_one (ω : Form R S 1) :
    ∃ m : KaehlerDifferential R S,
      ExteriorAlgebra.ι S m = (ω : ExteriorAlgebra S (KaehlerDifferential R S)) := by
  have h : (ω : ExteriorAlgebra S (KaehlerDifferential R S)) ∈
      (LinearMap.range (ExteriorAlgebra.ι S :
        KaehlerDifferential R S →ₗ[S] ExteriorAlgebra S (KaehlerDifferential R S))) ^ 1 :=
    ω.2
  rw [pow_one] at h
  exact LinearMap.mem_range.mp h

/-- **★ `ω ∧ ω = 0` for every 1-form.**

The alternating property in the only degree where it is available without
constructing `d₁`. Reduces to `ExteriorAlgebra.ι_sq_zero`. -/
theorem wedge_self_degree_one (ω : Form R S 1) :
    wedge R S ω ω = 0 := by
  obtain ⟨m, hm⟩ := exists_iota_of_degree_one R S ω
  apply Subtype.ext
  rw [wedge_coe, Submodule.coe_zero, ← hm, ExteriorAlgebra.ι_sq_zero]

/-- **★★ `d₀ a ∧ d₀ a = 0`.**

The degree-1 shadow of `d ∘ d = 0`: the square of an exact 1-form vanishes.
This is the first instance of that identity obtainable before `d₁` exists, and
it is the statement whose higher-degree analogues the remaining construction
has to produce. -/
theorem d0_wedge_self (a : S) :
    wedge R S (d0 R S a) (d0 R S a) = 0 :=
  wedge_self_degree_one R S (d0 R S a)

/-- `d₀ a ∧ d₀ b` is a genuine 2-form; recorded so the target of `d₁` is
visible as an inhabited type rather than only as a definition. -/
noncomputable def d0_wedge_d0 (a b : S) : Form R S 2 :=
  wedge R S (d0 R S a) (d0 R S b)

/-- **★★ Antisymmetry in degree 1:** `ω ∧ η = -(η ∧ ω)`.

This needs no new machinery — it falls out of `wedge_self_degree_one` and the
bilinearity above, by expanding `(ω + η) ∧ (ω + η) = 0`:

    0 = ω∧ω + ω∧η + η∧ω + η∧η = ω∧η + η∧ω .

**Why this is the step-2 unblock and not a side lemma.** `Ω¹` is a quotient of
the free module `⊕ₓ S·dx` by the Kähler relations, so a candidate `d₁` is
defined on the free module by `a·dx ↦ d₀a ∧ d₀x` and must kill those
relations. The additive relation dies because `d₀` is additive; the
`algebraMap` relation dies because `d₀` kills constants. The LEIBNIZ relation
`1·d(xy) - x·dy - y·dx` maps to

    d₀ 1 ∧ d₀(xy) - d₀x ∧ d₀y - d₀y ∧ d₀x
      = 0 - (d₀x ∧ d₀y + d₀y ∧ d₀x)

using `d0_one`, and that vanishes **exactly** by this lemma. So degree-1
antisymmetry is the obstruction that stood between the wedge and `d₁`, and it
was already implied by what this file proves. -/
theorem wedge_antisymm_degree_one (ω η : Form R S 1) :
    wedge R S ω η = - wedge R S η ω := by
  have h := wedge_self_degree_one R S (ω + η)
  rw [wedge_add_left, wedge_add_right, wedge_add_right,
      wedge_self_degree_one, wedge_self_degree_one, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **The Leibniz obstruction vanishes.** The combination that the candidate
`d₁` must send to zero on the Kähler Leibniz relation, shown to be zero.

This is the computation spelled out in `wedge_antisymm_degree_one`'s docstring,
stated as a theorem so the next file can cite it rather than reprove it. -/
theorem d0_leibniz_obstruction_vanishes (x y : S) :
    wedge R S (d0 R S x) (d0 R S y) + wedge R S (d0 R S y) (d0 R S x) = 0 := by
  rw [wedge_antisymm_degree_one]
  exact neg_add_cancel _

/-! ## §4 — Capstone -/

/-- **Step 2's infrastructure.** The wedge exists, is bilinear, and squares to
zero on 1-forms; `d₀` composed with it gives the degree-1 shadow of `d ∘ d = 0`.

`d_n` for `n ≥ 1` is still absent — see this file's "Not claimed". -/
theorem affine_deRham_wedge_infrastructure :
    (∀ (p q : ℕ) (ω₁ ω₂ : Form R S p) (η : Form R S q),
        wedge R S (ω₁ + ω₂) η = wedge R S ω₁ η + wedge R S ω₂ η) ∧
    (∀ (p q : ℕ) (ω : Form R S p) (η₁ η₂ : Form R S q),
        wedge R S ω (η₁ + η₂) = wedge R S ω η₁ + wedge R S ω η₂) ∧
    (∀ ω : Form R S 1, wedge R S ω ω = 0) ∧
    (∀ a : S, wedge R S (d0 R S a) (d0 R S a) = 0) ∧
    (∀ ω η : Form R S 1, wedge R S ω η = - wedge R S η ω) ∧
    (∀ x y : S, wedge R S (d0 R S x) (d0 R S y)
        + wedge R S (d0 R S y) (d0 R S x) = 0) :=
  ⟨fun _ _ => wedge_add_left R S, fun _ _ => wedge_add_right R S,
   wedge_self_degree_one R S, d0_wedge_self R S,
   wedge_antisymm_degree_one R S, d0_leibniz_obstruction_vanishes R S⟩

end AlgebraicDeRhamAffine
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.wedge_add_left
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.wedge_add_right
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.wedge_smul_left
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.exists_iota_of_degree_one
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.wedge_self_degree_one
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d0_wedge_self
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.wedge_antisymm_degree_one
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d0_leibniz_obstruction_vanishes
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.affine_deRham_wedge_infrastructure
