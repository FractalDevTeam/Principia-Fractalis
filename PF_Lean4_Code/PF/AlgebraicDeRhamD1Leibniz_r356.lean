/-
# r356 — `d₁` is an `R`-linear Leibniz map, and that is exactly the obstruction

★ 2026-10-25 — Grothendieck gluing arrow, affine de Rham ★

## What this adds and why it is the right next brick

`r355` built `d₁ : Ω¹ → Ω²` and proved `d ∘ d = 0`. But `d₁` arrived as a bare
`AddMonoidHom`: additive, and nothing more was known about it. This file proves
the two structural facts that characterise it.

    d1_leibniz            d₁(a · ω) = d₀a ∧ ω + a · d₁ω          (all ω : Ω¹)
    d1_smul_algebraMap    d₁ is R-linear
    dForm1_leibniz        the same, in `Form` language

This is not decoration. `GROTHENDIECK_ROUTE_PRICED_2026-10-23.md` explains that
the obvious route to `d_n` — `exteriorPower.alternatingMapLinearEquiv` — **does
not apply**, and gives the reason:

> "That equivalence produces an `R`-LINEAR map, and the exterior derivative is
> **not** `S`-linear: `d(aω) = da ∧ ω + a·dω`, so `d` is only `R`-linear over
> the base and satisfies Leibniz over `S`."

`r343`'s own docstring on `d0_leibniz` says the same thing. Until now that was
an *observation about what `d` ought to be*. Here it becomes a **theorem about
the `d₁` actually constructed in `r355`**: the map really is `S`-Leibniz and
really is `R`-linear, so the diagnosis of why the cheap route fails is now
checked rather than asserted.

It is also the inductive hypothesis any construction of `d_n` must carry: an
anti-derivation of degree `+1` is built by extending exactly this identity.

## How the proof goes, and the one trick it reuses

`KaehlerDifferential.span_range_derivation` says `span S (range D) = ⊤`, so
every `ω : Ω¹` is reachable by span induction from the `D y`. Three of the four
cases are routine. The `smul` case is not provable for the plain predicate —
rescaling `ω` by `c` changes which scalar the statement is about — so the
induction runs on the **strengthened** predicate

    ∀ b, d₁(b · ω) = d₀b ∧ ω + b · d₁ω

and the `smul` case applies the hypothesis twice, at `b * c` and at `c`. This
is the same strengthening `r345` needed for `d1Free_kills_kerTotal`, for the
same underlying reason: the statement is about an `S`-structure while the map
is only additive. Worth noting that the trick recurs — it is characteristic of
descending non-linear maps along `S`-spans, not a one-off.

The `mem` case closes by `rfl`, because `d₀ y` is *defined* as
`(formOneEquiv).symm (D y)`.

## What is and is not claimed

**Claimed.** The three results above, for an arbitrary commutative `R`-algebra
`S`. No smoothness, no finiteness.

**NOT claimed.**

1. **`d_n` for `n ≥ 2` still does not exist.** Step 2 of the priced route is
   still incomplete. This file supplies the structural identity that a general
   construction must extend; it does not perform that construction. Anyone
   reading `d∘d = 0` (r355) plus Leibniz (here) as "the de Rham complex exists"
   would be wrong — there is no `d₂`.
2. **No `CochainComplex`, no de Rham cohomology.** Steps 3 and 4 untouched.
3. **AFFINE ONLY.** Gluing to a variety is unpriced with five pillars at zero
   files (`deRham`, quasicoherent/coherent sheaves, sheaf cohomology,
   hypercohomology, spectral sequences).
4. **No Hodge consequence.** Chow groups, the cycle class map and intersection
   theory are all absent, so the conjecture is not even stateable at this pin.
   This route does not touch its content.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-25.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic
import PF.AlgebraicDeRhamD1Descent_r355

namespace PrincipiaTractalis
namespace AlgebraicDeRhamAffine

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-! ## §1 — The degree-1 identification on generators -/

/-- `d₀ y` *is* `(formOneEquiv).symm (D y)`, by definition. Stated so the
induction below can rewrite with it. -/
@[simp] theorem formOneEquiv_symm_D (y : S) :
    (formOneEquiv R S).symm (KaehlerDifferential.D R S y) = d0 R S y := rfl

/-! ## §2 — Leibniz -/

/-- **★★★ `d₁` is `S`-Leibniz.**

`d₁(a · ω) = d₀a ∧ ω + a · d₁ω` for every `ω : Ω¹`.

This is the identity the priced note cites as the reason
`alternatingMapLinearEquiv` cannot define `d_n`, now proved for the `d₁` that
`r355` actually constructed.

The induction is on the strengthened predicate `∀ b, …` because the `smul`
case rescales `ω` and so needs the hypothesis at a different scalar; the plain
predicate's `smul` case is not provable. Same strengthening as `r345`. -/
theorem d1_leibniz (a : S) (ω : KaehlerDifferential R S) :
    d1 R S (a • ω)
      = wedge R S (d0 R S a) ((formOneEquiv R S).symm ω) + a • d1 R S ω := by
  have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  have key : ∀ b : S, d1 R S (b • ω)
      = wedge R S (d0 R S b) ((formOneEquiv R S).symm ω) + b • d1 R S ω := by
    induction hω using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        intro b
        rw [d1_smul_D, d1_D, smul_zero, add_zero, formOneEquiv_symm_D]
    | zero =>
        intro b
        simp [wedge_zero_right]
    | add x y _ _ ihx ihy =>
        intro b
        simp only [smul_add, map_add, ihx b, ihy b, wedge_add_right]
        abel
    | smul c x _ ih =>
        intro b
        rw [smul_smul, ih (b * c), ih c]
        simp only [d0_leibniz, map_smul, wedge_add_left, wedge_smul_left,
          wedge_smul_right, smul_add, smul_smul]
        abel
  exact key a

/-! ## §3 — `R`-linearity, as a corollary -/

/-- **★★ `d₁` is `R`-linear.**

Immediate from Leibniz and `r343`'s `d0_algebraMap`: constants have zero
differential, so the Leibniz term dies. Together with `d1_leibniz` this is the
exact structure — `R`-linear, `S`-Leibniz — that the priced note names. -/
theorem d1_smul_algebraMap (r : R) (ω : KaehlerDifferential R S) :
    d1 R S ((algebraMap R S r) • ω) = (algebraMap R S r) • d1 R S ω := by
  rw [d1_leibniz, d0_algebraMap, wedge_zero_left, zero_add]

/-! ## §4 — The same, in `Form` language -/

/-- **Leibniz for `dForm1`.** The degree-1 identification is `S`-linear, so the
identity transports with no extra content — but it is the form in which a
general `d_n` would state it, every argument a `Form`. -/
theorem dForm1_leibniz (a : S) (ω : Form R S 1) :
    dForm1 R S (a • ω) = wedge R S (d0 R S a) ω + a • dForm1 R S ω := by
  rw [dForm1_apply, map_smul, d1_leibniz, LinearEquiv.symm_apply_apply,
    dForm1_apply]

/-! ## §5 — Capstone -/

/-- **`d₁` is an `R`-linear Leibniz map of degree `+1` with `d ∘ d = 0`.**

(1) Leibniz over `S` — here
(2) `R`-linear — here
(3) `d₁ ∘ d₀ = 0` — `r355`

`d_n` for `n ≥ 2` does **not** exist, so this is not a complex. See the
header's "NOT claimed". -/
theorem d1_is_R_linear_Leibniz_with_d_squared_zero :
    (∀ (a : S) (ω : KaehlerDifferential R S),
      d1 R S (a • ω)
        = wedge R S (d0 R S a) ((formOneEquiv R S).symm ω) + a • d1 R S ω) ∧
    (∀ (r : R) (ω : KaehlerDifferential R S),
      d1 R S ((algebraMap R S r) • ω) = (algebraMap R S r) • d1 R S ω) ∧
    (∀ a : S, dForm1 R S (d0 R S a) = 0) :=
  ⟨d1_leibniz R S, d1_smul_algebraMap R S, dForm1_d0 R S⟩

end AlgebraicDeRhamAffine
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d1_leibniz
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d1_smul_algebraMap
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.dForm1_leibniz
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d1_is_R_linear_Leibniz_with_d_squared_zero
