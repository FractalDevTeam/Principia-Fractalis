/-
# r343 — Algebraic differential forms on a smooth affine base: step 1 of the Grothendieck route

★ 2026-10-24 — the first brick of the spine's terminal arrow, built not estimated ★

## Where this sits

`codex/GROTHENDIECK_ROUTE_PRICED_2026-10-23.md` prices an algebraic de Rham
complex over Kähler differentials in four steps:

1. `Ω^n_{S/R} := exteriorPower n (Ω[S⁄R])` — assembly from present pieces
2. the exterior derivative `d_n : Ω^n → Ω^{n+1}` with `d ∘ d = 0` — the price
3. package as a `CochainComplex` — existing API
4. `H^n_dR` as its cohomology — existing API

**This file is step 1, plus `d₀`.** It is deliberately small and deliberately
honest about being small: the point of the exercise was to stop estimating and
start building, because the two measurements that produced this route both
overturned an estimate.

## What the measurements said, and why they matter here

Two results from 2026-10-24, both recorded in that note:

* **The cheap route to step 2 is refuted.** `exteriorPower.alternatingMapLinearEquiv`
  reduces a linear map out of an exterior power to an alternating map, which
  looked like it collapsed step 2 to assembly. It does not apply: that
  equivalence yields an `S`-linear map, and `d` is only `R`-linear with Leibniz
  over `S`. Confirmed by a second count: no `Derivation` into an exterior power
  exists anywhere in `Mathlib/LinearAlgebra/ExteriorPower/`.
* **The gluing is unpriced and sits behind four absent layers.** Going from an
  affine base to a variety needs quasi-coherent sheaves, sheaf cohomology,
  hypercohomology and spectral sequences, all of which count **zero** files in
  mathlib at this pin. So the four-step price above is the AFFINE price.

Both are reasons to build the affine block now and claim nothing beyond it.

## What is here

`Form R S n := ⋀[S]^n (KaehlerDifferential R S)`, the two edge identifications
`Form 0 ≃ S` and `Form 1 ≃ Ω[S⁄R]` from mathlib's `zeroEquiv`/`oneEquiv`, and
`d₀ : S → Form R S 1` as the universal derivation transported along the degree-1
identification, with its Leibniz rule and unit law proved.

`d₀` is deliberately NOT packaged as a `Derivation R S (Form R S 1)`.
`LinearMap.compDer` would give that, but it requires `[IsScalarTower R S N]` for
`N` the exterior power — i.e. an `R`-module structure on `⋀[S]^1`, which mathlib
does not propagate from the `S`-module structure at this pin. Transporting the
Leibniz identity directly needs only `S`-linearity of the equivalence, so that
is what is done. The obstruction is recorded rather than worked around silently:
it is a real item for anyone continuing to `d_n`.

## What is and is not claimed

**Claimed.** Algebraic differential `n`-forms exist as a definition over any
commutative `R`-algebra `S`; the degree-0 and degree-1 pieces are identified
with `S` and with the module of Kähler differentials; and the universal
derivation gives a `d₀ : S → Ω¹` satisfying `d₀(ab) = a·d₀b + b·d₀a` and
`d₀ 1 = 0`.

**Not claimed.**

1. `d_n` for `n ≥ 1`, and therefore not `d ∘ d = 0`, and therefore no complex
   and no cohomology. Steps 2–4 are untouched. The viable route for step 2 is
   the one the note names: define `d` on the free module of the Kähler
   presentation and descend, using that
   `Mathlib/RingTheory/Kaehler/Basic.lean` (lines 628, 654) proves the kernel of
   `⊕ₓ B dx ↠ Ω_{B/R}` is SPANNED by the image of the relations.
2. Smoothness is not used and not assumed anywhere here. The definition is made
   for every `R`-algebra `S`; it is only for smooth `S` that it computes
   algebraic de Rham cohomology, and that comparison is not stated.
3. Nothing global. No scheme, no sheaf, no variety — see the four zero-counts
   above.
4. Nothing about the Hodge conjecture. Chow groups, the cycle class map and
   intersection theory remain absent, so its content is not expressible here.
   This file must not be cited as progress on it.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-24.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace AlgebraicDeRhamAffine

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-! ## §1 — Algebraic differential forms -/

/-- **Algebraic differential `n`-forms** of `S` over `R`:

    `Ω^n_{S/R} := ⋀^n_S (Ω[S⁄R])`

the `n`-th exterior power, over `S`, of the module of Kähler differentials.
Step 1 of the four-step route, and the one step the pricing called pure
assembly — both ingredients are already in mathlib. -/
noncomputable abbrev Form (n : ℕ) : Type _ :=
  ⋀[S]^n (KaehlerDifferential R S)

/-! ## §2 — The two edge identifications -/

/-- **`Ω⁰ ≅ S`.** The zeroth exterior power is the base ring: functions are
`0`-forms. -/
noncomputable def formZeroEquiv : Form R S 0 ≃ₗ[S] S :=
  exteriorPower.zeroEquiv S (KaehlerDifferential R S)

/-- **`Ω¹ ≅ Ω[S⁄R]`.** The first exterior power is the module of Kähler
differentials itself, so degree 1 of this complex is the object the whole
construction is built on.

(Note: mathlib's docstring on `oneEquiv` states the equivalence in the opposite
direction to its own signature; the signature is what is used here.) -/
noncomputable def formOneEquiv : Form R S 1 ≃ₗ[S] KaehlerDifferential R S :=
  exteriorPower.oneEquiv S (KaehlerDifferential R S)

/-! ## §3 — `d₀`, the universal derivation in degree 0 -/

/-- **`d₀ : S → Ω¹`.** The universal derivation `D`, transported along the
degree-1 identification.

Not packaged as a `Derivation R S (Form R S 1)`: `LinearMap.compDer` would do
that but needs `[IsScalarTower R S (⋀[S]^1 _)]`, and mathlib does not propagate
an `R`-module structure onto the exterior power at this pin. The Leibniz
identity transports with only `S`-linearity, which is what §3 uses. -/
noncomputable def d0 (a : S) : Form R S 1 :=
  (formOneEquiv R S).symm (KaehlerDifferential.D R S a)

/-- `d₀` agrees with `D` under the degree-1 identification, by construction. -/
theorem formOneEquiv_d0 (a : S) :
    (formOneEquiv R S) (d0 R S a) = KaehlerDifferential.D R S a := by
  unfold d0
  exact (formOneEquiv R S).apply_symm_apply _

/-- **`d₀` is additive.** -/
theorem d0_add (a b : S) : d0 R S (a + b) = d0 R S a + d0 R S b := by
  unfold d0
  rw [map_add, map_add]

/-- **`d₀ 1 = 0`**: the unit is constant. -/
theorem d0_one : d0 R S 1 = 0 := by
  unfold d0
  rw [Derivation.map_one_eq_zero, map_zero]

/-- **★ Leibniz rule for `d₀`.** `d₀(ab) = a · d₀b + b · d₀a`.

This is the identity that makes `d₀` a derivation rather than merely additive,
and it is the reason step 2 cannot use `alternatingMapLinearEquiv`: `d` is
`S`-Leibniz, not `S`-linear. -/
theorem d0_leibniz (a b : S) :
    d0 R S (a * b) = a • d0 R S b + b • d0 R S a := by
  unfold d0
  rw [Derivation.leibniz, map_add, map_smul, map_smul]

/-- **`d₀` kills the image of the base ring**, for `r : R` acting on `1`.
Constants have zero differential, which is the degree-0 shadow of `d ∘ d = 0`
and the only part of that identity available at this stage. -/
theorem d0_algebraMap (r : R) : d0 R S (algebraMap R S r) = 0 := by
  unfold d0
  rw [Derivation.map_algebraMap, map_zero]

/-! ## §4 — Capstone -/

/-- **Step 1 of the Grothendieck route, as one statement.**

The forms exist, both edges are identified, and `d₀` is a derivation into
degree 1. Steps 2–4 — `d_n` for `n ≥ 1`, `d ∘ d = 0`, the complex, the
cohomology — are untouched; see this file's "Not claimed". -/
theorem affine_deRham_step_one :
    (∀ a b : S, d0 R S (a + b) = d0 R S a + d0 R S b) ∧
    (d0 R S 1 = 0) ∧
    (∀ a b : S, d0 R S (a * b) = a • d0 R S b + b • d0 R S a) ∧
    (∀ r : R, d0 R S (algebraMap R S r) = 0) ∧
    (∀ a : S, (formOneEquiv R S) (d0 R S a) = KaehlerDifferential.D R S a) :=
  ⟨d0_add R S, d0_one R S, d0_leibniz R S, d0_algebraMap R S, formOneEquiv_d0 R S⟩

end AlgebraicDeRhamAffine
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d0_add
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d0_one
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d0_leibniz
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d0_algebraMap
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.formOneEquiv_d0
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.affine_deRham_step_one
