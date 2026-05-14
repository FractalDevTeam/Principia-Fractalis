/-
# Bochner-Minlos Theorem for Nuclear Spaces
The infinite-dimensional generalization of Bochner's theorem.

THEOREM (Bochner-Minlos): Let S be a real nuclear locally convex topological
vector space. Let C : S → ℂ be a continuous function such that:
1. C(0) = 1 (normalization)
2. C is positive definite: ∑ᵢⱼ zᵢ · conj(zⱼ) · C(sᵢ - sⱼ) ≥ 0

Then there exists a unique probability measure μ on the dual space S'
(with the cylindrical σ-algebra) such that for all s ∈ S:
  C(s) = ∫_{S'} exp(i⟨ω,s⟩) dμ(ω)

This theorem is fundamental for constructive quantum field theory, as it
allows construction of path integral measures on infinite-dimensional spaces.

Reference: Gel'fand-Vilenkin, Generalized Functions Vol. 4, Ch. IV
          Principia Fractalis, Chapter 23 (Yang-Mills framework)
-/

import PF.NuclearSpaces
import PF.CylindricalMeasures
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace PrincipiaTractalis

/-! ## Minlos' Condition -/

/- `minlos_sigma_additivity` — orphaned theorem deleted 2026-05-11.

   The classical Minlos statement (every cylindrical measure on a nuclear
   space is σ-additive) WAS asserted here, with a "proof" that witnessed
   `∃ ν, IsProbabilityMeasure ν ∧ ...` by Dirac at 0 — relying on the
   `isSigmaAdditive` predicate's cylinder-agreement clause being a `True`
   placeholder. With the placeholder upgraded to the genuine pushforward
   equality (2026-05-11), the Dirac-at-0 witness no longer satisfies the
   statement for arbitrary μ; a real proof requires the full Kolmogorov
   extension argument on nuclear projective limits.

   Deletion is the honest move per the rigor mandate: a "theorem" whose
   proof was an artefact of a placeholder clause carried no verified
   content. There are zero downstream consumers in PF/ (grep verified),
   so removing it is structurally safe. The retirement path when Minlos
   becomes load-bearing is the same multi-week formalization Reed-Simon
   §IX.2 calls for. -/

/-! ## Main Bochner-Minlos Theorem -/

/-- A measure on S' is a probability measure if it assigns mass 1 to S'. -/
structure ProbabilityMeasureOnDual (d : ℕ) where
  measure : MeasureTheory.Measure (TemperedDistribution d)
  is_prob : MeasureTheory.IsProbabilityMeasure measure

/- BOCHNER-MINLOS THEOREM (Existence): previously asserted as an axiom
   for any characteristic functional C : S(R^d) → ℂ (positive definite,
   normalized, continuous at 0), claiming `∃ μ probability measure on
   S'(R^d) with C(f) = ∫ exp(i⟨ω, f⟩) dμ(ω)`.

   Proof outline (Reed-Simon §IX.2):
   1. C determines finite-dimensional distributions via finite-dim Bochner.
   2. These form a consistent family → cylindrical measure.
   3. Nuclearity of S → σ-additivity (Minlos' condition).
   4. σ-additive cylindrical measure = genuine measure.

   `bochner_minlos_existence` — axiom retired 2026-05-14 (Stage 30) by deletion.

   The classical Bochner-Minlos existence statement (every continuous PD
   normalized characteristic functional on Schwartz space arises from a
   probability measure on the dual) was previously an axiom with three
   downstream consumers: `gaussian_measure_exists`, `qft_measure_foundation`,
   and `yang_mills_measure_exists_proven`. Each of those was a top-level
   "showcase" theorem with **zero internal downstream consumers** —
   isolated assertions of measure existence, not building blocks for
   the framework's headline results (P ≠ NP and Riemann Hypothesis).
   The two transitive consumers in GaussianModel.lean
   (`free_scalar_measure_exists`, `gaussian_yang_mills_complete`) were
   similarly orphan.

   Deletion of all five orphan theorems + the axiom is the honest move
   per the rigor mandate (same precedent as the prior orphan deletions
   of `bochner_minlos_uniqueness`, `finite_dim_bochner`,
   `minlos_sigma_additivity`, the in-house nuclear-spaces block, plus
   ~15 yang_mills_*/spectral_*/T3_* orphans across the cleanup arc).

   The framework no longer makes claims about Yang-Mills/QFT measure
   existence in Lean. When the classical Bochner-Minlos theorem is
   eventually formalized (Reed-Simon §IX.2, multi-week via Riesz-Markov
   + Lévy continuity), the consumer theorems can be reinstated as real
   theorems of the formalized analysis, not axiom-dependent placeholders. -/

/- `bochner_minlos_uniqueness` — axiom retired 2026-05-10 by deletion.

   The classical Bochner-Minlos uniqueness statement (probability measures
   on S'(ℝ^d) with the same characteristic functional are equal) WAS asserted
   here as an axiom, but it had **zero actual proof consumers** in the
   codebase — only doc-comment references at lines 113, 116 below
   (in `bochner_minlos_bijection`'s docstring noting that the bijection is
   structurally tautological and `bochner_minlos_uniqueness` carries the
   "real content" but isn't actually invoked).

   Deletion is the honest move per the referee-grade rigor mandate: an axiom
   whose claimed content isn't load-bearing in any verified proof is worse
   than no axiom (it claims content without doing the verification work).

   When the codebase grows to a point where infinite-dim Bochner-Minlos
   uniqueness becomes load-bearing (e.g., for full Yang-Mills measure
   uniqueness or QFT correlation-function uniqueness), the retirement path is:
   - Equip `TemperedDistribution d` with a real `PseudoEMetricSpace`,
     `BorelSpace`, `CompleteSpace`, `SecondCountableTopology` (multi-week
     infrastructure: topologize SchwartzFunction first, then take continuous
     dual with weak-* topology).
   - Apply mathlib's `Measure.ext_of_charFunDual` (the Hilbert-pair variant
     suitable for non-Hilbert duals like S'). -/

/- `bochner_minlos_bijection` — deleted 2026-05-13 as orphan with
   tautological injectivity. The theorem claimed a bijection
   `CharacteristicFunctional d ≃ ProbabilityMeasureOnDual d`, but its
   "injectivity" arm derived `C₁ = C₂` from `Φ C₁ = Φ C₂` purely by
   `congrArg (·.measure)` + pointwise rewriting on `hΦ` — a tautology
   that did not invoke any genuine Fourier-injectivity. Zero downstream
   consumers in PF/. Same orphan-deletion precedent as
   `bochner_minlos_uniqueness` (b056bf1), `finite_dim_bochner` (183dd20),
   `minlos_sigma_additivity` (fa3e9ed), and the in-house nuclear-spaces
   block (55ff0cd). When the real Bochner-Minlos bijection becomes
   load-bearing, it will follow from `bochner_minlos_existence` + a
   genuine uniqueness statement built on mathlib's
   `Measure.ext_of_charFunDual`. -/

/-! ## Applications to Specific Characteristic Functionals -/

/-- Gaussian characteristic functional:
    C(f) = exp(-½ Q(f,f))
    where Q is a positive quadratic form on S.
-/
structure GaussianCharacteristic (d : ℕ) where
  /-- The covariance quadratic form Q : S × S → ℝ -/
  covariance : SchwartzFunction d → SchwartzFunction d → ℝ
  /-- Q is symmetric -/
  symmetric : ∀ f g, covariance f g = covariance g f
  /-- Q is positive semi-definite -/
  positive : ∀ f, 0 ≤ covariance f f
  /-- Q is continuous as a bilinear form `S × S → ℝ`.
      Refactored 2026-05-13 from `True` placeholder to mathlib's
      `Continuous` on the uncurried covariance. -/
  continuous : Continuous (Function.uncurry covariance)
  /-- Q(0,0) = 0 (required for normalization of the Gaussian characteristic).
      Added 2026-04-22 to enable elimination of the `gaussian_is_characteristic`
      axiom without assuming additional structure. -/
  zero_covariance : covariance 0 0 = 0
  /-- The resulting functional exp(-½ Q(f,f)) is positive definite.
      Added 2026-04-22; carries the Schoenberg-theorem content as a
      constructor obligation rather than an axiom. -/
  functional_pd : IsPositiveDefinite
    (fun f => Complex.exp (-(1/2 : ℂ) * covariance f f))
  /-- The resulting functional is continuous at 0 (Added 2026-04-22). -/
  functional_continuous : IsContinuousAtZero
    (fun f => Complex.exp (-(1/2 : ℂ) * covariance f f))

/-- The Gaussian characteristic functional exp(-½ Q(f,f)). -/
noncomputable def GaussianCharacteristic.toFun {d : ℕ}
    (G : GaussianCharacteristic d) (f : SchwartzFunction d) : ℂ :=
  Complex.exp (-(1/2 : ℂ) * G.covariance f f)

/-- THEOREM: Gaussian characteristic functionals satisfy the Bochner-Minlos conditions.
    Axiom → theorem (2026-04-22): trivial after adding `zero_covariance`,
    `functional_pd`, `functional_continuous` as fields of
    `GaussianCharacteristic`. Extracts each field directly. -/
theorem gaussian_is_characteristic {d : ℕ} (G : GaussianCharacteristic d) :
    ∃ (C : CharacteristicFunctional d), C.toFun = G.toFun := by
  refine ⟨{
    toFun := G.toFun
    normalized := by
      simp [GaussianCharacteristic.toFun, G.zero_covariance]
    positive_definite := G.functional_pd
    continuous_at_zero := G.functional_continuous
  }, rfl⟩

/- `gaussian_measure_exists` — deleted 2026-05-14 (Stage 30) with the
   `bochner_minlos_existence` axiom retirement. Was an orphan top-level
   theorem with only 2 internal consumers (`free_scalar_measure_exists`
   and `gaussian_yang_mills_complete`), both also orphan top-level
   theorems with no downstream uses. Deletion removes the axiom-
   dependent QFT-measure-existence chain.

   Reinstatement path: when classical Bochner-Minlos is formalized
   (Reed-Simon §IX.2), `gaussian_measure_exists` can be re-introduced
   as a genuine theorem. -/

/-! ## Nuclearity is Essential -/

-- NOTE (2026-04-22, refreshed 2026-05-13): `nuclearity_essential` was
-- removed as latently unsound. The full in-house nuclear-spaces
-- infrastructure (Seminorm', SeminormFamily, LocallyConvexSpace,
-- NuclearSpace, traceNorm, IsNuclear, schwartz_is_nuclear,
-- gauge_field_space_nuclear) was subsequently deleted on 2026-05-12
-- (commit 55ff0cd) as orphan scaffolding. When real Grothendieck
-- nuclearity is needed for Bochner-Minlos's *existence* proof, the
-- load-bearing replacement will be mathlib's `LocallyConvexSpace ℝ`
-- instance on `SchwartzMap`, plus nuclear typeclasses (forthcoming
-- in mathlib's distribution-theory infrastructure). The
-- "nuclearity is essential" claim — that for non-nuclear Banach
-- spaces some characteristic functionals fail to extend to measures —
-- becomes a meaningful theorem once a real `IsNuclear` predicate is
-- in scope.

/- `EuclideanFieldMeasure` and `qft_measure_foundation` — deleted
   2026-05-14 (Stage 30) with the `bochner_minlos_existence` axiom
   retirement. Both were orphan top-level definitions/theorems with
   zero downstream consumers in PF/. The QFT-measure-foundation
   claim was conditional on the now-deleted axiom; without it, the
   theorem collapses. Reinstatement path: when classical
   Bochner-Minlos is formalized, both can be reintroduced as
   genuine definitions/theorems. -/

end PrincipiaTractalis
