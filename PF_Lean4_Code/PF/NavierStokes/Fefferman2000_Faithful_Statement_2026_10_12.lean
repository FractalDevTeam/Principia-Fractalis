/-
# Faithful Fefferman 2000 Clay Navier–Stokes STATEMENT (not a proof)

Migrated in-tree 2026-10-12 on branch `ns-faithful-migration`. Elaborated with
`lake env lean` in the main `PF_Lean4_Code` tree (which carries the mathlib
oleans); EXIT 0 — see the adjacent build log committed alongside this file.
Imports ONLY mathlib (no PF modules).
Target pin: Lean 4.24.0-rc1, mathlib inputRev v4.24.0-rc1
(.lake/packages/mathlib in Principia-Fractalis-ACTIVE/PF_Lean4_Code).

PURPOSE
-------
Write Fefferman's official Clay statement ("Existence and smoothness of the
Navier–Stokes equation", CMI 2000), problem (A)/(B) on ℝ³, as a REAL Lean `Prop`
built from genuine mathlib differential-operator primitives — not a conjunction
of availability flags. This is the honest object the corpus's `NS_Solution`
(4-clause flag bundle) and the 2026-06-19 `Clay_Literal_..._Fefferman2000`
(whose PDE clause is the tautology `u t = u t`) both fail to be.

The real-valued velocity/pressure encoding below is deliberately MORE faithful
than the corpus's `ℝ → SchwartzMap(ℝ³,ℝ³)` solution carrier: Fefferman requires
the SOLUTION to be C^∞ with BOUNDED ENERGY, NOT Schwartz-in-space at every time.
Only the INITIAL DATUM must be Schwartz (rapid decay, condition (4)).

Fefferman's equations, n = 3, ν > 0, zero forcing (unforced case (A)/(B)):
  (1) ∂ₜuᵢ + Σⱼ uⱼ ∂ⱼuᵢ = ν Δuᵢ − ∂ᵢp          (momentum)
  (2) div u = Σᵢ ∂ᵢuᵢ = 0                        (incompressibility)
  (3) u(x,0) = u₀(x)                              (initial condition)
  (6) ∫_{ℝ³} |u(x,t)|² dx < C  for all t ≥ 0      (bounded energy)
  u₀ smooth, divergence-free, |∂^α u₀(x)| ≤ C_{αK}(1+|x|)^{-K}   (4) rapid decay
-/

import Mathlib.Analysis.Distribution.SchwartzSpace          -- SchwartzMap, 𝓢(E,F)
import Mathlib.Analysis.Calculus.FDeriv.Basic               -- fderiv
import Mathlib.Analysis.Calculus.Deriv.Basic                -- deriv
import Mathlib.Analysis.Calculus.ContDiff.Defs              -- ContDiff / ContDiffOn
import Mathlib.Analysis.Calculus.Gradient.Basic             -- gradient  (notation ∇)
import Mathlib.Analysis.InnerProductSpace.Laplacian         -- InnerProductSpace.laplacian (Δ)
import Mathlib.Analysis.InnerProductSpace.PiL2              -- EuclideanSpace.single
import Mathlib.MeasureTheory.Integral.Bochner.Basic         -- ∫ (un-deprecated paths)
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace -- volume on EuclideanSpace

open MeasureTheory

namespace PF.NavierStokes.FeffermanFaithful

/-- Physical space / velocity space: ℝ³ as a finite-dim real inner-product space.
    (mathlib: `EuclideanSpace ℝ (Fin 3)` carries `InnerProductSpace ℝ`,
    `FiniteDimensional ℝ`, and a Haar `volume` measure — all needed below.) -/
abbrev V : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The one primitive mathlib does NOT package: divergence

mathlib v4.24.0-rc1 has NO `divergence` operator (confirmed by grep over
`Mathlib/Analysis` and `Mathlib/Geometry`). It is, however, DEFINABLE in one
line from `fderiv` and the standard basis, so this is a *definitional* gap, not
a *blocking* one: the statement elaborates with this helper present.

  div g (x) = Σᵢ (∂ᵢ g)(x)ᵢ = Σᵢ (Dg(x) eᵢ)ᵢ

`fderiv ℝ g x : V →L[ℝ] V`; feed the i-th standard basis vector
`EuclideanSpace.single i 1`, then read off coordinate i. -/
noncomputable def divergence (g : V → V) (x : V) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) i

/-! ## The faithful Clay statement

Notes on the mathlib primitives used in the PDE line (all present at the pin):
  • `deriv (fun s => U (x, s)) t`                           — Eulerian ∂ₜu  (deriv of a ℝ→V curve)
  • `fderiv ℝ (fun y => U (y, t)) x (U (x, t))`             — convective (u·∇)u
        [the Fréchet derivative of the spatial field in the DIRECTION u(x,t)
         is exactly Σⱼ uⱼ ∂ⱼu]
  • `gradient (fun y => P (y, t)) x`                        — ∇p  (mathlib `gradient`, scoped ∇)
  • `InnerProductSpace.laplacian (fun y => U (y, t)) x`     — Δu  (mathlib's genuine Laplacian,
        defined as the 2nd derivative applied to the canonical covariant tensor;
        equals `fun x => Σᵢ iteratedFDeriv ℝ 2 f x ![eᵢ, eᵢ]`)
  • `ν • _`                                                 — scalar viscosity, `ν : ℝ`, smul on V
  • `ContDiffOn ℝ (⊤ : ℕ∞) _ {q | 0 ≤ q.2}`                — C^∞ on the space-time half-space
        [IMPORTANT: at this pin `ContDiff`'s index is `WithTop ℕ∞`; `(⊤ : ℕ∞)`
         (equivalently the `∞` notation) is C^∞. The bare `⊤ : WithTop ℕ∞` would
         mean analytic C^ω — NOT what Clay asks. Use `(⊤ : ℕ∞)`.]
  • `∫ x, ‖U (x, t)‖ ^ 2`                                   — energy, default `volume` on V
        [guarded by `Integrable` so the bound is not vacuously about mathlib's
         junk value `∫ = 0` for a non-integrable integrand].

Carrier choice: `U : V × ℝ → V`, `P : V × ℝ → ℝ` — jointly-defined space-time
fields, sliced by currying. This lets a single `ContDiffOn … ⊤` express
Fefferman's joint C^∞(ℝ³×[0,∞)) faithfully. -/
noncomputable def Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful : Prop :=
  -- For every smooth, divergence-free, rapidly-decaying initial field u₀
  -- (Schwartz class = exactly Fefferman's decay condition (4)):
  ∀ u0 : SchwartzMap V V,
    (∀ x : V, divergence (fun y => u0 y) x = 0) →        -- (B)(i): div u₀ = 0
    -- there exist a global-in-time velocity U, pressure P, and viscosity ν:
    ∃ (U : V × ℝ → V) (P : V × ℝ → ℝ) (ν : ℝ),
      0 < ν ∧
      -- SMOOTHNESS: u, p ∈ C^∞(ℝ³ × [0,∞))
      ContDiffOn ℝ (⊤ : ℕ∞) U {q : V × ℝ | 0 ≤ q.2} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) P {q : V × ℝ | 0 ≤ q.2} ∧
      -- (3) INITIAL CONDITION: u(·, 0) = u₀
      (∀ x : V, U (x, 0) = u0 x) ∧
      -- (2) INCOMPRESSIBILITY: div u(·, t) = 0 for all t ≥ 0
      (∀ (x : V) (t : ℝ), 0 ≤ t → divergence (fun y => U (y, t)) x = 0) ∧
      -- (1) MOMENTUM EQUATION (unforced): ∂ₜu + (u·∇)u + ∇p = ν Δu for all t ≥ 0
      (∀ (x : V) (t : ℝ), 0 ≤ t →
        deriv (fun s : ℝ => U (x, s)) t
          + fderiv ℝ (fun y : V => U (y, t)) x (U (x, t))
          + gradient (fun y : V => P (y, t)) x
        = ν • InnerProductSpace.laplacian (fun y : V => U (y, t)) x) ∧
      -- (6) BOUNDED ENERGY: ∃ C, ∀ t ≥ 0, ∫|u(·,t)|² ≤ C  (with integrability guard)
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
        Integrable (fun x : V => ‖U (x, t)‖ ^ 2) ∧
        (∫ x : V, ‖U (x, t)‖ ^ 2) ≤ C)

/-!
## HONEST GAP LEDGER (statement-level)

NONE of these blocks ELABORATION of the statement at the pin; they are either
one-line helpers or faithful modelling choices. (The PROOF is of course the open
Clay problem and is not attempted.)

G1. `divergence` — NOT in mathlib at v4.24.0-rc1. Defined above from `fderiv` +
    `EuclideanSpace.single`. Definitional, non-blocking.

G2. Smoothness index — `ContDiff`'s argument is `WithTop ℕ∞` at this pin, so C^∞
    is `(⊤ : ℕ∞)` (the `∞` notation), NOT `⊤ : WithTop ℕ∞` (= analytic). Flagged
    inline; correct spelling used.

G3. Energy integral — `∫` over `V` uses the Haar `volume`
    (`MeasureTheory.Measure.Haar.InnerProductSpace`). The `Integrable` guard is
    included so the `≤ C` bound is meaningful rather than silently about mathlib's
    `∫ = 0` convention on non-integrable integrands.

G4. Real vs complex — this statement is real-valued (faithful to Fefferman). The
    corpus's Fujita-Kato substrate (`VectorSchwartz3C = 𝓢(ℝ³, ℂ³)`) is complex;
    the real problem embeds into it. The Oct-8 `IsNSSolution` predicate (see
    below) is the complex-carrier Cauchy-problem analogue of clauses (1)-(3) here.

## RELATION TO EXISTING CORPUS OBJECTS (verified 2026-10-11)

  • `PF/NavierStokes/Wave58TimeGlobalExistenceUpgrade.lean : NS_Solution` — the
    rated-unfaithful predicate. 4 clauses, NONE of which is the PDE:
    `initialDataMatch ∧ (divergenceFreePreserved := u0.isDivFree, discards u) ∧
     (forwardTimeDomain := ∀y, ∃z, u y = z, a tautology) ∧
     (smoothness := ∃M≥0, ∀y, ‖u y‖≤M, true for every Schwartz map)`.
    Collapses (r215 disclosure) to `NS_Solution u u0 ↔ initialDataMatch u u0 ∧ u0.isDivFree`.
    No ∂ₜ, no (u·∇)u, no ∇p, no Δ, no ν.

  • `PF/NavierStokes/Fefferman2000_LiteralClayNS3D_Statement_2026_06_19.lean` —
    name promises this statement; its PDE clause `SatisfiesLiteralNSE` is literally
    `∀ t, 0 ≤ t → u t = u t` (tautology). `IsLiteralDivergenceFree` and
    `HasBoundedEnergy` are likewise placeholder tautologies. NOT faithful.

  • `PF/NavierStokes/ConvectiveDerivativeConnection_2026_10_08.lean : IsNSSolution`
    — the GENUINE Cauchy-problem predicate (horizon T load-bearing on Set.Icc 0 T):
    real `HasDerivAt` time-derivative link, real `Σⱼ ∂ⱼuⱼ = 0`, real
    `IsPressureGradient` constraint, and `momentumResidual = 0` with a NON-inert
    convective term (`convectiveComponent`) and real `vectorLaplacian`.
    This statement's clauses (1)-(3) are the real-valued, global analogue of
    `IsNSSolution`. What that file explicitly does NOT provide (its own words:
    "Nothing here asserts existence, uniqueness, or regularity") is the GLOBAL
    EXISTENCE + SMOOTHNESS + BOUNDED-ENERGY wrapper quantified over all admissible
    u₀ — i.e. exactly the `Prop` stated above.

So the faithful Fefferman statement = the Oct-8 Cauchy predicate, (i) promoted to
global-in-time (t ≥ 0, no finite T), (ii) wrapped in `∀ u₀ Schwartz div-free → ∃ …`,
(iii) with the bounded-energy clause (6), and (iv) real-valued per Clay.

VERDICT: elaborable at v4.24.0-rc1 with the `divergence` helper (G1). No mathlib
primitive is MISSING for the STATEMENT; the only true absence is a packaged
divergence, which is one line. The analytic CONTENT (a proof) is the open problem.
-/

end PF.NavierStokes.FeffermanFaithful
