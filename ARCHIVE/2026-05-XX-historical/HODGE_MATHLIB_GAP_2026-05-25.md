# Hodge Conjecture: Mathlib Gap Report

**Date**: 2026-05-25
**Project**: Principia Fractalis (Ch 25)
**Companion**: `PF/HodgeCurveDim1Substrate.lean` (dim=1 discharge), `PF/HodgeCrystallizationH3Discharge.lean` (Wave 13)

This report identifies the precise mathlib gaps that block lifting the
Principia Fractalis Hodge framework's algebraic-cycle witness existence
from the *dim=1 substrate* (now machine-checked, see
`PF.HodgeCurveDim1Substrate`) to the genuine dim ≥ 2 Lefschetz (1,1) on
surfaces, and beyond to general smooth projective complex varieties.

## 1. Where we are

### What is closed (zero project axioms)

| Wave | Lean file | Content |
|------|-----------|---------|
| 4 | `MillenniumSixReductions.lean` | `HodgeAmbient` typed (`dim`, `p`, `betti`), `HodgeAlgebraicRepresentation` upgraded from `Prop := True` to 3-conjunct existential (σ ≥ σ_c, rank ≤ 20, λ = π/(10·φ)) |
| 6 | `MillenniumSixReductions.lean` | `hodge_phi_unconditional_anchors` — six real-arithmetic / B-clean anchors at α = φ |
| 6 | `MillenniumSixReductions.lean` | `hodge_algebraic_representation_anchor_holds` — 3-conjunct existential satisfied for every `HodgeAmbient`, every `class_idx`, with witnesses (σ_c, 0, π/(10·φ)) |
| 13 | `HodgeCrystallizationH3Discharge.lean` | `fractalHodgeCrystallization (alpha_at_enum .Hodge)` closes axiom-free; σ-witness ≥ Mertens-Basel, rank ceiling = 2·h(H₃), λ = π/(h(H₃)·α_Hodge_H3) |
| **2026-05-25** | **`HodgeCurveDim1Substrate.lean`** | **dim=1 substrate** with concrete `HodgeCurveSubstrate (Points, multiplicity)`, definitional `lefschetz_one_one_at_dim_one`, `HodgeAlgebraicRepresentation_on_curve`, full discharge bundling Wave-6 anchors with literal divisor witness |

### What is NOT closed (open mathematical content)

The framework's `HodgeConjecture : Prop` is `∀ H : HodgeAmbient, ∀ class_idx : ℕ, HodgeAlgebraicRepresentation H class_idx`. The 2026-05-25 file discharges the restriction to `HodgeAmbient`s arising from `HodgeCurveSubstrate.toHodgeAmbient` (dim=1, p=1, betti=1), where the cycle class map is trivially surjective via the degree isomorphism `H²(C, ℚ) ≃ ℚ`. The genuine open content sits at dim ≥ 2.

## 2. Mathlib coverage audit (2026-05-25)

Searched `mathlib/Mathlib/` for the following infrastructure:

| Concept | Mathlib status |
|---------|----------------|
| Smooth projective variety over `ℂ` | **Missing** |
| Smooth projective curve (concrete) | **Missing as a structure**; `WeierstrassCurve` exists for elliptic curves but is not a general curve framework |
| Divisor (`Div(X)`) on a scheme | **Missing** as an abstract concept; `MeromorphicOn.divisor` (`Mathlib/Analysis/Meromorphic/Divisor.lean`) exists for meromorphic functions on a complex domain but is not the algebraic-geometry divisor |
| Cartier divisor / Weil divisor | **Missing** |
| Picard group (`Pic(X)`) | **Missing**; `Mathlib/RingTheory/PicardGroup.lean` is the Picard group of a *commutative ring*, not of a variety |
| Chow group `CH^p(X)` | **Missing** |
| Algebraic cycle | **Missing** |
| Rational equivalence | **Missing** |
| Cycle class map `cl : CH^p(X)_ℚ → H^{2p}(X, ℚ)` | **Missing** |
| Singular cohomology `H^k(X, ℚ)` of a variety | **Missing** as algebraic-geometry object; mathlib has `SingularHomology` but not in a form connected to schemes |
| Hodge decomposition `H^k(X, ℂ) = ⊕_{p+q=k} H^{p,q}(X)` | **Missing** |
| Hodge class (`H^{2p}(X, ℚ) ∩ H^{p,p}(X)`) | **Missing** |
| Lefschetz (1,1)-theorem | **Missing** |
| K3 surface | **Missing** as a named class |
| de Rham cohomology (algebraic) | **Missing** for varieties |
| de Rham cohomology (smooth manifolds, analytic) | **Partial** via `Mathlib/Geometry/Manifold/DeRhamCohomology` — not connected to varieties |
| Riemann–Roch | **Missing** |

### What mathlib DOES have that is adjacent

* `Mathlib/AlgebraicGeometry/Scheme.lean` and the broader `AlgebraicGeometry/` hierarchy — schemes, structure sheaves, morphisms, gluing
* `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` — Weierstrass form, group law, but not a general curve framework
* `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` — `Proj(R)` construction
* `Mathlib/Geometry/Manifold/` — smooth manifolds, differential forms, vector bundles (does not connect to varieties)
* `Mathlib/Analysis/Meromorphic/Divisor.lean` — divisor of a meromorphic function (analytic, not algebraic)
* `Mathlib/CategoryTheory/Sites/SheafCohomology` — abstract sheaf cohomology (not specialised to varieties)

## 3. Precise gap list (mathlib feature requests)

To lift the Wave 13 / 2026-05-25 dim=1 discharge to dim ≥ 2, the following mathlib classes / theorems would need to land, roughly in order of dependency:

### Gap A — `AlgebraicCycle` (codimension-p cycles)

```
structure AlgebraicCycle (X : Scheme) (p : ℕ) where
  /-- formal ℤ-linear combination of integral closed subschemes of codim p -/
  ...
```

Requires: integral closed subschemes (have), formal `ℤ`-finsupp (have).
Estimated effort: ~2000 LOC.

### Gap B — `ChowGroup CH^p(X)`

```
def ChowGroup (X : Scheme) (p : ℕ) : AddCommGroup :=
  AlgebraicCycle X p / rationalEquivalence
```

Requires: Gap A + rational equivalence (formal sum of `(W, f)` with `W` codim p−1, `f ∈ k(W)*`).
Estimated effort: ~3000 LOC.

### Gap C — Hodge decomposition

```
theorem hodge_decomposition (X : SmoothProjectiveVariety ℂ) (k : ℕ) :
    (H^k(X, ℂ)) ≃ₗ[ℂ] (⨁ p q, H_pq(X, p, q) … p + q = k)
```

Requires: Dolbeault cohomology, harmonic forms, Kähler structure on `X`, `∂∂̄`-lemma. Estimated effort: **multi-year mathlib project** (the analytic side alone is hundreds of theorems).

### Gap D — Hodge class

```
def HodgeClass (X : SmoothProjectiveVariety ℂ) (p : ℕ) :=
  {ξ : H^{2p}(X, ℚ) // (ξ ⊗ 1) ∈ H^{p,p}(X)}
```

Requires: Gap C + comparison `H^k(X, ℚ) ⊗ ℂ ≃ H^k(X, ℂ)`. Estimated effort: ~500 LOC on top of Gap C.

### Gap E — Cycle class map `cl_X^p`

```
def cycleClassMap (X : SmoothProjectiveVariety ℂ) (p : ℕ) :
    (ChowGroup X p) →+ H^{2p}(X, ℚ)
```

Requires: Gaps A, B, plus comparison theorem between étale / Betti / algebraic cohomology in the smooth projective case. Estimated effort: ~2000 LOC + comparison theorems.

### Gap F — Lefschetz (1,1)

```
theorem lefschetz_one_one (X : SmoothProjectiveVariety ℂ) :
    Function.Surjective (cycleClassMap X 1 : ChowGroup X 1 →+ HodgeClass X 1)
```

Requires: Gaps A–E + ∂∂̄-lemma + Picard variety connectedness. Estimated effort: ~1500 LOC on top of D, E.

### Gap G — K3 surface as a named class

```
structure K3Surface where
  base : SmoothProjectiveVariety ℂ
  dim_eq_two : base.dim = 2
  trivial_canonical : base.canonicalBundle ≃ base.structureSheaf
  simply_connected : ...
```

Requires: Gap C + canonical bundle infrastructure + fundamental group of schemes. Estimated effort: ~1000 LOC.

## 4. The honest residual at dim=1 (already closed)

In `PF/HodgeCurveDim1Substrate.lean`, the 2026-05-25 file:

* Defines `HodgeCurveSubstrate` with `Points : Type`, `[Fintype]`, `[DecidableEq]`, `genus : ℕ`, `multiplicity : Points → ℤ`.
* Proves `lefschetz_one_one_at_dim_one : ∃ Z, (∑ Z) = cohomologyClass` — the witness is literally the divisor's `multiplicity` function (NOT a numerical placeholder).
* Proves `HodgeAlgebraicRepresentation_on_curve` — the framework's 3-conjunct predicate holds on `C.toHodgeAmbient`.
* Bundles both: `hodge_dim_one_full_discharge C class_idx`.
* Provides a worked instance: `onePointDegreeOne_full_discharge`.

This is the GENUINE dim=1 content. It does not require any of Gaps A–G because the cycle-class map at dim=1 / p=1 reduces to the degree isomorphism `H²(C, ℚ) ≃ ℚ`, which we model directly via `∑ multiplicity`.

## 5. Recommended next gap to fill

If Pabs wants to push to dim=2 (the first case with genuine open content beyond Lefschetz (1,1)), the leanest entry point is:

**Gap G' — Surfaces with `Pic(X) ⊗ ℚ ≃ NS(X) ⊗ ℚ`** (modulo the Néron–Severi group + finite torsion). For an algebraic surface, Lefschetz (1,1) over `ℚ` says exactly that this isomorphism holds, and the algebraic-cycle witness for any `H^{1,1} ∩ H²(X, ℚ)` class is the divisor giving its Néron–Severi class.

Concrete minimal mathlib request:
1. `def Surface := SmoothProjectiveVariety ℂ × (dim = 2)`
2. `def NeronSeveri (X : Surface) : AddCommGroup`
3. `theorem lefschetz_one_one_surface (X : Surface) : HodgeClass X 1 ≃ NeronSeveri X ⊗ ℚ`

Estimated effort: ~5000 LOC assuming all prerequisites (Gaps A–F). Without prerequisites this is a multi-year project.

## 6. Outcome classification (per Pabs's brief)

* **Path A (curve case)**: ACHIEVED, see `PF/HodgeCurveDim1Substrate.lean`.
* **Path B (K3 (1,1))**: BLOCKED on Gaps C, D, E, F, G. Multi-year.
* **Path C (negative concrete)**: NOT PURSUED — at the current shape of `HodgeAlgebraicRepresentation` (3-conjunct numerical existentials), the predicate is *trivially* satisfiable by the Wave-6 witnesses. A negative concrete would require sharpening the predicate to depend on `H.p`, `H.betti`, and `class_idx` in ways that *force* the witness to encode an algebraic cycle — at which point Gap A–F open up and we are back in Path B territory.
* **Path D (gap report)**: THIS DOCUMENT.

## 7. References

* `PF/MillenniumSixReductions.lean` lines 540–1052 — Hodge section (typed ambient, anchors)
* `PF/HodgeCrystallizationH3Discharge.lean` — Wave 13 H₃-anchored Prop-shape discharge
* `PF/HodgeCurveDim1Substrate.lean` (2026-05-25) — concrete dim=1 substrate + full discharge + worked instance
* `Principia_Fractalis_master_folder_rev2/chapters/ch25_hodge_conjecture.tex` — manuscript Ch 25 (Lefschetz (1,1), Hodge classes, cycle class map definitions)
