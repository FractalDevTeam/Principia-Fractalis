/-
# H_NP as a Concrete Mathlib Operator: Construction Certificate

This file is the NP-class counterpart of `HPOperatorConstruction.lean`,
delivering the same construction certificate for `H_NP` on the
`Lp ℂ 2 μ` substrate.

The manuscript's `H_NP` is the integral kernel operator with the
*same* fractal-kernel structure `V_P(x,y) = Σ a^(-n) cos(π α^n d(x,y))`
as `H_P`, but with the resonance frequency **swapped from
`α = √2` (P-class) to `α = φ + 1/4` (NP-class)**. Both operators
are instances of the parameterised family `H_P_at α a` constructed in
`HPGeneralOperator.lean` via `kernelOperator (fractalKernel α a)`.

## What this file delivers (NO SORRY)

1. **`H_NP_construction`** — the concrete `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`
   operator, defined as `H_P_at (φ + 1/4) a`.
2. **`H_NP_construction_isSelfAdjoint`** — self-adjointness, inherited
   from `H_P_at_isSelfAdjoint` (the kernel is real-valued, hence
   conjugate-symmetric, for *any* real `α`).
3. **`H_NP_zeroRank`** — the rank-0 (zero) operator, trivial base case
   for the finite-rank tower.
4. **`H_NP_zeroRank_isSelfAdjoint`** / **`H_NP_zeroRank_isCompactOperator`**
   — proved via `IsSelfAdjoint.zero` and `isCompactOperator_zero`.
5. **Closure-under-sums lemmas** (`add_isCompactOperator_NP`,
   `add_isSelfAdjoint_NP`) — wrappers around the Mathlib API.
6. **`H_NP_finiteRankTower`** — the finite-rank-tower predicate for
   `H_NP_construction` (sequence of self-adjoint compact CLMs
   converging in operator norm).
7. **`H_NP_construction_isCompactOperator_of_finiteRankTower`** —
   compactness from a tower via `isCompactOperator_of_tendsto`.
8. **`GroundStateEigenvalueTargetNP`** — the formal Prop expressing
   the manuscript's NP-class ground-state identification

     `λ_0(H_NP) = π / (10 · (φ + 1/4))`,

   ready for discharge by the polylog conjecture machinery.
9. **`H_NP_construction_axiom_retirement_certificate`** — bundling
   theorem certifying that, given the spectral hypothesis content,
   the H_NP operator construction discharges the NP analogue of
   Input #5.
10. **`H_NP_construction_full_chain`** — the FULL Clay-grade chain
    (operator + self-adjointness + compactness + ground-state).

## Bridge to `HPSpectralFormula`

At `α = φ + 1/4`, the general formula `HPSpectralFormula α λ := λ = π/(10·α)`
specialises to `λ = π / (10 · (φ + 1/4)) = lambda_0_NP`. We provide
`GroundStateEigenvalueFormulaNP_iff_HPSpectralFormula` mirroring the
H_P bridge.

## NOT delivered (open conjectural content)

* **Tower existence**: the analytic content of `OPEN_PROBLEMS.md`
  Problem 1 (NP-side Mercer decomposition + uniform L² convergence).
* **Ground-state eigenvalue equation discharge**: NP-side analogue
  of Problems 1 + 2 (eigenvector identification + Riemann-sheet
  selection for the polylog at `α = φ + 1/4`).

The construction itself is **maximally tractable**: every theorem
below is proved axiom-free using existing Mathlib `IsCompactOperator`
API plus the project's existing `H_P_at` infrastructure.

Stage L5-NP — H_NP operator construction certificate (mirror of
Input #5 for the NP-class).
-/

import PF.Analytic.HPOperatorConstruction
import PF.IntervalArithmetic
import Mathlib.Analysis.Normed.Operator.Compact

namespace PrincipiaTractalis.Analytic

open Real MeasureTheory
open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.IntegralKernel

variable {K : Type*} [PseudoMetricSpace K] [MeasurableSpace K]
  [SecondCountableTopology K] [OpensMeasurableSpace K]
  {μ : Measure K} [SFinite μ] [IsFiniteMeasure μ]

/-! ## The concrete H_NP operator instance -/

/-- **`H_NP_construction`** — the concrete `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`
    instance of `H_NP` on the Cantor (or any `IsFiniteMeasure`) substrate.

    Defined as `H_P_at (φ + 1/4) a`, i.e. the parameterised family
    `kernelOperator (fractalKernel α a)` with the NP-class resonance
    frequency `α = φ + 1/4` swapped in for the P-class `α = √2`.

    With `kernelOperator` providing the boundedness witness via the
    Hilbert-Schmidt L²-bound, `H_NP_construction` is a genuine instance
    of the Mathlib `ContinuousLinearMap` API. -/
noncomputable def H_NP_construction {a : ℝ} (ha : 1 < a) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  H_P_at (μ := μ) (phi + 1/4) ha

/-- **`H_NP_construction` is self-adjoint** (`a > 1`).

    Inherits directly from `H_P_at_isSelfAdjoint` at `α = φ + 1/4`.
    The proof chain is identical to the H_P case:
    * `fractalKernel (φ+1/4) a` is conjugate-symmetric (real-valued
      ⟹ `conj V(x,y) = V(y,x) = V(x,y)`).
    * `isSelfAdjoint_of_kernel_conjSymm` lifts kernel-level
      conjugate-symmetry to operator-level self-adjointness.

    Note: conjugate symmetry of the fractal kernel holds for ANY
    real `α` — the swap from `√2` to `φ + 1/4` preserves it. -/
theorem H_NP_construction_isSelfAdjoint {a : ℝ} (ha : 1 < a) :
    IsSelfAdjoint (H_NP_construction (μ := μ) ha) :=
  H_P_at_isSelfAdjoint (μ := μ) (α := phi + 1/4) ha

/-! ## Rank-0 (zero) operator: trivial base case for the finite-rank tower

The Mathlib `IsCompactOperator` API provides `isCompactOperator_zero`,
which gives compactness of the zero operator. This is the trivial
base case of the finite-rank tower used to build `H_NP` as a norm-limit
of compact operators.
-/

/-- **`H_NP_zeroRank`** — the rank-0 (zero) operator on `Lp ℂ 2 μ`.

    This is the trivial base case of the finite-rank approximation
    tower for the NP construction. -/
noncomputable def H_NP_zeroRank : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := 0

omit [PseudoMetricSpace K] [SecondCountableTopology K]
  [OpensMeasurableSpace K] [SFinite μ] [IsFiniteMeasure μ] in
/-- **`H_NP_zeroRank` is self-adjoint** (immediate: `IsSelfAdjoint 0`). -/
theorem H_NP_zeroRank_isSelfAdjoint :
    IsSelfAdjoint (H_NP_zeroRank (μ := μ)) := by
  unfold H_NP_zeroRank
  exact _root_.IsSelfAdjoint.zero _

omit [PseudoMetricSpace K] [SecondCountableTopology K]
  [OpensMeasurableSpace K] [SFinite μ] [IsFiniteMeasure μ] in
/-- **`H_NP_zeroRank` is a compact operator** (immediate: the zero
    operator is compact in any normed space, via Mathlib's
    `isCompactOperator_zero`). -/
theorem H_NP_zeroRank_isCompactOperator :
    IsCompactOperator (H_NP_zeroRank (μ := μ)) := by
  unfold H_NP_zeroRank
  exact isCompactOperator_zero

/-! ## Closure under sums (for building the finite-rank tower) -/

omit [PseudoMetricSpace K] [SecondCountableTopology K]
  [OpensMeasurableSpace K] [SFinite μ] [IsFiniteMeasure μ] in
/-- **Sum of compact operators is compact** — wrapper around
    `IsCompactOperator.add` (NP-side). -/
theorem add_isCompactOperator_NP
    {T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hT_K : IsCompactOperator T) (hS_K : IsCompactOperator S) :
    IsCompactOperator (T + S) :=
  hT_K.add hS_K

omit [PseudoMetricSpace K] [SecondCountableTopology K]
  [OpensMeasurableSpace K] [SFinite μ] [IsFiniteMeasure μ] in
/-- **Sum of self-adjoint operators is self-adjoint** — wrapper around
    `IsSelfAdjoint.add` (NP-side). -/
theorem add_isSelfAdjoint_NP
    {T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hT_sa : IsSelfAdjoint T) (hS_sa : IsSelfAdjoint S) :
    IsSelfAdjoint (T + S) :=
  hT_sa.add hS_sa

/-! ## The finite-rank tower predicate (NP-side) -/

/-- **Finite-rank tower** for `H_NP_construction`: a sequence of
    self-adjoint compact operators `T_N : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`
    converging to `H_NP_construction a` in the operator-norm topology.

    Existence of such a tower would prove compactness of
    `H_NP_construction` via `isCompactOperator_of_tendsto`. -/
def H_NP_finiteRankTower {a : ℝ} (ha : 1 < a) : Prop :=
  ∃ (T : ℕ → (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)),
    (∀ N, IsSelfAdjoint (T N)) ∧
    (∀ N, IsCompactOperator (T N)) ∧
    Filter.Tendsto T Filter.atTop (nhds (H_NP_construction (μ := μ) ha))

/-- **Compactness from a finite-rank tower** (NP-side) — the standard
    `isCompactOperator_of_tendsto` packaging.

    If `H_NP_construction` admits a finite-rank tower (sequence of
    self-adjoint compact operators converging to it in operator norm),
    then `H_NP_construction` itself is compact.

    This is the **load-bearing step** for invoking the spectral theorem
    on H_NP: compactness ⟹ discrete real spectrum ⟹ countable
    eigenvalues bounded away from 0 only at the origin. -/
theorem H_NP_construction_isCompactOperator_of_finiteRankTower
    {a : ℝ} (ha : 1 < a)
    (hTower : H_NP_finiteRankTower (μ := μ) ha) :
    IsCompactOperator (H_NP_construction (μ := μ) ha) := by
  obtain ⟨T, _, hT_K, hT_tendsto⟩ := hTower
  exact isCompactOperator_of_tendsto hT_tendsto
    (Filter.Eventually.of_forall hT_K)

/-! ## Ground-state eigenvalue target (NP-side)

The manuscript identifies `λ_0(H_NP) = π / (10 · (φ + 1/4))` (the
canonical NP-class spectral value at `α = φ + 1/4`). The formal
statement is wrapped here as `GroundStateEigenvalueTargetNP`, ready
for discharge by the polylog conjecture chain (`OPEN_PROBLEMS.md`
Problems 1 + 2 evaluated at the NP-side parameter).
-/

/-- **`GroundStateEigenvalueTargetNP`** — the formal Prop expressing the
    manuscript's identification of the NP-class ground-state eigenvalue:

      `∃ (f : Lp ℂ 2 μ), f ≠ 0 ∧
         H_NP_construction a f = (π / (10·(φ+1/4)) : ℂ) • f`. -/
def GroundStateEigenvalueTargetNP {a : ℝ} (ha : 1 < a) : Prop :=
  ∃ (f : Lp ℂ 2 μ), f ≠ 0 ∧
    H_NP_construction (μ := μ) ha f =
      ((Real.pi / (10 * (phi + 1/4)) : ℝ) : ℂ) • f

/-- **`GroundStateEigenvalueFormulaNP`** — the structured predicate
    asserting that `lambda` is the manuscript's NP-class ground-state
    eigenvalue:

      `lambda = π / (10 · (φ + 1/4))`. -/
def GroundStateEigenvalueFormulaNP (lambda : ℝ) : Prop :=
  lambda = Real.pi / (10 * (phi + 1/4))

/-- **Bridge to `HPSpectralFormula`**: at `α = φ + 1/4`, the general
    formula `HPSpectralFormula α λ := λ = π/(10·α)` specialises to
    `GroundStateEigenvalueFormulaNP λ := λ = π/(10·(φ+1/4))`. -/
theorem GroundStateEigenvalueFormulaNP_iff_HPSpectralFormula
    (lambda : ℝ) :
    GroundStateEigenvalueFormulaNP lambda ↔
      HPSpectralFormula (phi + 1/4) lambda := by
  unfold GroundStateEigenvalueFormulaNP HPSpectralFormula
  rfl

/-! ## The axiom-retirement certificate (NP-side)

The bundling theorem certifying that the H_NP operator construction
discharges the NP analogue of Input #5: given (i) the operator
instance, (ii) self-adjointness, and (iii) a route to compactness
(the finite-rank tower), the structural piece is in place; the
remaining work is the analytic discharge of the tower's existence
(Mercer decomposition + uniform L² convergence at α = φ + 1/4 —
`OPEN_PROBLEMS.md` Problem 1, NP-side).
-/

/-- **`H_NP_construction_axiom_retirement_certificate`** — NP-side
    Input #5 certificate: the H_NP operator construction is in place,
    self-adjoint, and compact *given a finite-rank tower*. -/
theorem H_NP_construction_axiom_retirement_certificate
    {a : ℝ} (ha : 1 < a)
    (hTower : H_NP_finiteRankTower (μ := μ) ha) :
    -- (i) the operator exists as a concrete Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ
    ∃ (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ),
    -- (ii) it is self-adjoint
    IsSelfAdjoint T ∧
    -- (iii) it is a compact operator
    IsCompactOperator T ∧
    -- (iv) it equals the canonical H_NP_construction at this `a`
    T = H_NP_construction (μ := μ) ha := by
  refine ⟨H_NP_construction (μ := μ) ha,
          H_NP_construction_isSelfAdjoint ha,
          H_NP_construction_isCompactOperator_of_finiteRankTower ha hTower,
          rfl⟩

/-! ## Full statement: H_NP operator + ground-state eigenvalue chain

The Clay-grade target on the NP-side: with both Input #5-NP
(operator construction with compactness) AND the NP ground-state
eigenvalue identification, the manuscript's
`λ_0(H_NP) = π/(10·(φ+1/4))` becomes a theorem about the concrete
Mathlib operator instance.
-/

/-- **`H_NP_construction_full_chain`** — the FULL Clay-grade chain
    (NP-side):

    Given (i) finite-rank tower (⟹ compactness of `H_NP_construction`),
    AND (ii) the NP ground-state eigenvalue identification, we get the
    final manuscript claim: `H_NP_construction a` is a self-adjoint
    compact operator whose ground-state eigenvalue equals
    `π/(10·(φ+1/4))`.

    The two hypotheses are the **two open mathematical inputs** that
    the polylog conjecture chain (`OPEN_PROBLEMS.md` Problems 1 + 2,
    evaluated at `α = φ + 1/4`) would discharge. With both in hand,
    the manuscript's formula `λ_0(H_NP) = π/(10·(φ+1/4))` becomes a
    complete theorem about the concrete operator construction defined
    here. -/
theorem H_NP_construction_full_chain
    {a : ℝ} (ha : 1 < a)
    (hTower : H_NP_finiteRankTower (μ := μ) ha)
    (hGround : GroundStateEigenvalueTargetNP (μ := μ) ha) :
    -- the operator
    (∃ (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ),
      IsSelfAdjoint T ∧ IsCompactOperator T ∧
      T = H_NP_construction (μ := μ) ha) ∧
    -- the ground-state eigenvalue equals π/(10·(φ+1/4))
    (∃ (f : Lp ℂ 2 μ), f ≠ 0 ∧
      H_NP_construction (μ := μ) ha f =
        ((Real.pi / (10 * (phi + 1/4)) : ℝ) : ℂ) • f) :=
  ⟨H_NP_construction_axiom_retirement_certificate ha hTower, hGround⟩

/-! ## Cross-class bridge: H_P vs H_NP at the operator level

Both `H_P_construction` and `H_NP_construction` are instances of
the same parameterised family `H_P_at α a` — they differ ONLY by
the choice of `α` (the resonance frequency). The bridge theorem
makes this explicit at the operator level.
-/

/-- **Bridge**: `H_NP_construction` is `H_P_at` evaluated at the NP
    resonance frequency `α = φ + 1/4`. -/
theorem H_NP_construction_eq_H_P_at_phi_plus_quarter
    {a : ℝ} (ha : 1 < a) :
    H_NP_construction (μ := μ) ha = H_P_at (μ := μ) (phi + 1/4) ha := rfl

/-- **Bridge**: `H_P_construction` (= `H_P_canonical`) coincides with
    `H_P_at` at `α = √2`. This re-exports `H_P_at_sqrt2_eq_canonical`
    framed for the construction interface. -/
theorem H_P_construction_eq_H_P_at_sqrt2
    {a : ℝ} (ha : 1 < a) :
    H_P_construction (μ := μ) ha = H_P_at (μ := μ) (Real.sqrt 2) ha :=
  (H_P_at_sqrt2_eq_canonical (μ := μ) ha).symm

/-! ## Documentation: gap to full spectral construction (NP-side)

What this file delivers (NO SORRY):

1. ✓ `H_NP_construction` defined as a Mathlib `ContinuousLinearMap`
   on `Lp ℂ 2 μ` (= `H_P_at (φ+1/4) a` from existing infrastructure).
2. ✓ `H_NP_construction_isSelfAdjoint` proved (inherited from
   `H_P_at_isSelfAdjoint`).
3. ✓ Rank-0 (zero) operator as trivial base case, with both
   self-adjointness AND compactness PROVED axiom-free.
4. ✓ Closure under sums proved (operator-level building blocks for
   the finite-rank tower).
5. ✓ `H_NP_finiteRankTower` predicate defined.
6. ✓ `H_NP_construction_isCompactOperator_of_finiteRankTower`:
   compactness of H_NP from the tower (via Mathlib's
   `isCompactOperator_of_tendsto`).
7. ✓ `GroundStateEigenvalueTargetNP` Prop ready for discharge.
8. ✓ Axiom-retirement certificate bundling the structural pieces.
9. ✓ Full chain bundling NP-Input #5 + ground-state identification.
10. ✓ Cross-class bridges (`H_NP_construction = H_P_at (φ+¼) a`,
    `H_P_construction = H_P_at √2 a`) — making the *only* difference
    between the two operators the single scalar `α`.

What this file does NOT deliver:

* **The finite-rank tower existence itself** at `α = φ + 1/4`.
  Same analytic content as the P-side (`OPEN_PROBLEMS.md` Problem 1)
  but evaluated at the NP-class resonance frequency.
* **The ground-state eigenvalue equation discharge** at `α = φ + 1/4`.
  NP-side of `OPEN_PROBLEMS.md` Problems 1 + 2.

The construction is **maximally tractable**: every theorem above is
proved axiom-free using existing Mathlib `IsCompactOperator` API +
the project's existing `H_P_at` infrastructure. The remaining inputs
(`hTower`, `hGround`) are precisely the NP-side analogues of the
named open conjectures from `OPEN_PROBLEMS.md`.

Combined with `HPOperatorConstruction.lean`, this completes the
operator-level construction of BOTH `H_P` and `H_NP` as concrete
Mathlib instances, ready for the spectral separation
`λ_0(H_P) > λ_0(H_NP)` (proved algebraically in `SpectralGap.lean`)
to be lifted to a statement about the operators themselves.
-/

end PrincipiaTractalis.Analytic
