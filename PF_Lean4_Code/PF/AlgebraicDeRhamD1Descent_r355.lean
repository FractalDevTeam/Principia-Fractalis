/-
# r355 — `d₁` descends to `Ω¹`, and `d ∘ d = 0`

★ 2026-10-25 — Grothendieck gluing arrow, affine de Rham step 2 COMPLETE ★

## What this closes

`codex/GROTHENDIECK_ROUTE_PRICED_2026-10-23.md` priced the affine route at four
steps and found that **one construction is the whole price**: its revised table
names `d_n` with `d∘d = 0` as *"the whole price, and harder than the equiv
suggested — must go through the Kaehler presentation and its spanned kernel,
not through `alternatingMapLinearEquiv`"*.

`r343` built `Form`/`d₀`, `r344` the wedge, `r345` the candidate `d₁` on the
free module plus `d1Free_kills_kerTotal`. This file performs the descent and
reads off `d ∘ d = 0`.

    d1Quot      (S →₀ S) ⧸ kerTotal →+ Ω²     the additive lift
    d1          Ω¹ →+ Ω²                      ★ the descent
    d1_smul_D   d₁(a · dy) = d₀a ∧ d₀y         the classical formula
    d1_D        d₁(dy) = 0
    dForm1_d0   d₁(d₀a) = 0                    ★★★ d ∘ d = 0

## The one structural fact that shaped this file

`Ω[S⁄R]` is **not** `(S →₀ S) ⧸ kerTotal`. mathlib defines it as
`(KaehlerDifferential.ideal R S).Cotangent` — that is `I/I²` for
`I = ker(S ⊗[R] S →ₐ[R] S)`. The finsupp presentation is a separate *theorem*,
`KaehlerDifferential.quotKerTotalEquiv`. So `r345`'s annihilation result cannot
descend directly; it descends onto the presentation and is then transported
across that equivalence. `d1` is the composite.

Two further facts make the lift possible at all, both measured rather than
assumed:

* `Submodule`'s quotient **is** `Quotient (QuotientAddGroup.leftRel
  p.toAddSubgroup)` definitionally, so an additive map can cross it even though
  `d₁` is not `S`-linear. `Submodule.liftQ` is itself built from
  `QuotientAddGroup.lift`, which is the existence proof.
* `QuotientAddGroup.lift N φ h ((kerTotal R S).mkQ x) = φ x` holds by **`rfl`**.
  Verified by compiler probe before this file was written, not hoped for.

`d₁` is additive and **not** `S`-linear — that is not a weakness, it is what a
derivation is. Making it `S`-linear would make it the zero map on exact forms
for the wrong reason.

## Why `d ∘ d = 0` is now cheap

`d₁(dy) = d₁(1 · dy) = d₀1 ∧ d₀y`, and `r343` proved `d0_one : d₀1 = 0` two
files ago. The hardest-sounding statement in the priced route is a corollary of
a lemma that was already sitting there. That is worth recording: the price was
in the *descent*, not in `d ∘ d = 0`.

## What is and is not claimed

**Claimed.** The five results above, for an arbitrary commutative `R`-algebra
`S`. No smoothness, no finiteness, no regularity hypotheses.

**NOT claimed.**

1. **`d_n` for general `n`.** Only `d₀` and `d₁` exist. The general
   `Ωⁿ → Ωⁿ⁺¹` is not built here, and `d∘d = 0` is proved only as
   `d₁ ∘ d₀ = 0`, not as a complex identity in all degrees.
2. **No `CochainComplex`.** Step 3 of the priced route — packaging these into a
   complex and taking cohomology — is not done. There is no de Rham *cohomology*
   in this file, only two differentials and one composite vanishing.
3. **AFFINE ONLY, and this is the honest headline.** The priced note's own
   SCOPE CORRECTION says it prices the affine case and that **gluing to a
   variety is unpriced with four pillars at zero** (`deRham`/`DeRham` = 0 files,
   and quasicoherent/coherent sheaves, sheaf cohomology, hypercohomology and
   spectral sequences all measured at 0 files). This file completes the *local
   building block*. It does not approach Hodge, and must not be written up as
   if it did.
4. **No Hodge consequence of any kind.** The Hodge axis remains blocked for
   every reason the blocking note gave.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-25.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic
import PF.AlgebraicDeRhamD1_r345

namespace PrincipiaTractalis
namespace AlgebraicDeRhamAffine

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-! ## §1 — The additive lift across the relation submodule -/

/-- **`d₁` on the finsupp presentation.**

`r345` proved `d1Free` annihilates `kerTotal`, which is exactly the hypothesis
`QuotientAddGroup.lift` needs. The lift is *additive* only: `d₁` is not
`S`-linear, and `Submodule.liftQ` would therefore not apply. It works because a
`Submodule` quotient is definitionally a `QuotientAddGroup` quotient by
`toAddSubgroup`. -/
noncomputable def d1Quot :
    ((S →₀ S) ⧸ KaehlerDifferential.kerTotal R S) →+ Form R S 2 :=
  QuotientAddGroup.lift (KaehlerDifferential.kerTotal R S).toAddSubgroup (d1Free R S)
    (fun _ hz => AddMonoidHom.mem_ker.mpr
      (d1Free_kills_kerTotal R S ((Submodule.mem_toAddSubgroup _).mp hz)))

/-- The lift computes on classes, definitionally. -/
@[simp] theorem d1Quot_mkQ (x : S →₀ S) :
    d1Quot R S ((KaehlerDifferential.kerTotal R S).mkQ x) = d1Free R S x := rfl

/-! ## §2 — Transport across mathlib's presentation theorem -/

/-- The presentation equivalence sends the class of `single y a` to `a · dy`. -/
theorem quotKerTotalEquiv_mkQ_single (y a : S) :
    KaehlerDifferential.quotKerTotalEquiv R S
        ((KaehlerDifferential.kerTotal R S).mkQ (Finsupp.single y a))
      = a • KaehlerDifferential.D R S y := by
  simp only [Submodule.mkQ_apply, KaehlerDifferential.quotKerTotalEquiv_apply]
  exact Finsupp.linearCombination_single S a y

/-- …hence its inverse sends `a · dy` back to that class. -/
theorem quotKerTotalEquiv_symm_smul_D (y a : S) :
    (KaehlerDifferential.quotKerTotalEquiv R S).symm (a • KaehlerDifferential.D R S y)
      = (KaehlerDifferential.kerTotal R S).mkQ (Finsupp.single y a) := by
  rw [LinearEquiv.symm_apply_eq, quotKerTotalEquiv_mkQ_single]

/-! ## §3 — `d₁` on `Ω¹` -/

/-- **★ The descended `d₁ : Ω¹ → Ω²`.**

The composite of `r345`'s lift with mathlib's presentation equivalence. This is
step 2 of the priced affine route, and the step the note called the whole
price. -/
noncomputable def d1 : KaehlerDifferential R S →+ Form R S 2 :=
  (d1Quot R S).comp
    (KaehlerDifferential.quotKerTotalEquiv R S).symm.toLinearMap.toAddMonoidHom

@[simp] theorem d1_apply (ω : KaehlerDifferential R S) :
    d1 R S ω = d1Quot R S ((KaehlerDifferential.quotKerTotalEquiv R S).symm ω) := rfl

/-- **★★ The classical formula `d(a dy) = da ∧ dy`.** -/
theorem d1_smul_D (y a : S) :
    d1 R S (a • KaehlerDifferential.D R S y) = wedge R S (d0 R S a) (d0 R S y) := by
  rw [d1_apply, quotKerTotalEquiv_symm_smul_D, d1Quot_mkQ, d1Free_single]

/-- **`d₁` kills exact one-forms.** `dy = 1 · dy`, and `d₀1 = 0` (`r343`). -/
theorem d1_D (y : S) : d1 R S (KaehlerDifferential.D R S y) = 0 := by
  rw [show KaehlerDifferential.D R S y = (1 : S) • KaehlerDifferential.D R S y from
        (one_smul S _).symm,
    d1_smul_D, d0_one, wedge_zero_left]

/-! ## §4 — `d ∘ d = 0`, in `Form` language -/

/-- `d₁` read through `r343`'s identification `Form¹ ≃ Ω¹`. -/
noncomputable def dForm1 : Form R S 1 →+ Form R S 2 :=
  (d1 R S).comp (formOneEquiv R S).toLinearMap.toAddMonoidHom

@[simp] theorem dForm1_apply (ω : Form R S 1) :
    dForm1 R S ω = d1 R S ((formOneEquiv R S) ω) := rfl

/-- **★★★ `d ∘ d = 0`.**

The target the priced route named as its whole cost, for an arbitrary
commutative `R`-algebra `S` — no smoothness, no finiteness. -/
theorem dForm1_d0 (a : S) : dForm1 R S (d0 R S a) = 0 := by
  rw [dForm1_apply, formOneEquiv_d0, d1_D]

/-- `d ∘ d = 0` stated as a composition of maps rather than pointwise. -/
theorem dForm1_comp_d0 : ∀ a : S, (dForm1 R S) (d0 R S a) = 0 := dForm1_d0 R S

/-! ## §5 — Capstone -/

/-- **Affine de Rham, step 2: complete.**

(1) `d₁ : Ω¹ → Ω²` exists as an additive map — the descent
(2) it computes as `d(a dy) = da ∧ dy` on generators
(3) `d ∘ d = 0`

Steps 3 (`CochainComplex` packaging) and 4 (gluing to a variety) are NOT done;
step 4 is unpriced with four pillars at zero files. See the header. -/
theorem affine_deRham_step2 :
    (∀ y a : S, d1 R S (a • KaehlerDifferential.D R S y)
        = wedge R S (d0 R S a) (d0 R S y)) ∧
    (∀ y : S, d1 R S (KaehlerDifferential.D R S y) = 0) ∧
    (∀ a : S, dForm1 R S (d0 R S a) = 0) :=
  ⟨d1_smul_D R S, d1_D R S, dForm1_d0 R S⟩

end AlgebraicDeRhamAffine
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d1Quot_mkQ
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.quotKerTotalEquiv_symm_smul_D
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d1_smul_D
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d1_D
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.dForm1_d0
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.affine_deRham_step2
