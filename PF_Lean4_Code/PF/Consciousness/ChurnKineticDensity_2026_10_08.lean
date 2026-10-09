/-
# Churn as a Kinetic Density — Layer 1 (Lean mathematics only)

## Purpose

Gives `PrincipiaTractalis.Consciousness.FrobeniusChurn.churnFrobenius`
its first *consumer*.

Measured fact that motivated this file (2026-10-08):
`grep -rln 'churnFrobenius' PF_Lean4_Code/PF` returned exactly one path —
`PF/Consciousness/FrobeniusChurn.lean` itself. The observable was a leaf
of the whole corpus: defined, given its T1–T4 properties, and then never
used by anything. This file consumes it.

## What is proved here

Let `ρ : ℝ → Matrix (Fin (3^k)) (Fin (3^k)) ℂ` be a curve of complex
matrices that is *entrywise* differentiable at `t`, with entrywise
derivative matrix `ρ'`. Then, as `dt → 0` along `dt ≠ 0`,

    churnFrobenius (ρ t) (ρ (t + dt)) / dt ^ 2  ⟶  (1/2) · ∑_{i,j} ‖ρ' i j‖²

(`churnFrobenius_div_sq_tendsto`). That is: churn, rescaled by `dt²`, has
a finite limit, and that limit is `½` times the sum of squared entry
norms of the velocity matrix.

The shape `½ · (velocity)²` is the shape of a kinetic density. The file
earns the right to *say* so by proving the limit, rather than asserting
a correspondence.

`CanonicallyNormalized ρ'` is the condition `∑_{i,j} ‖ρ' i j‖² = 1`.
Under it the limit is exactly `1/2` (`churnFrobenius_div_sq_tendsto_half`).
The condition is exhibited with data, not merely named: two concrete
satisfying matrices (`witnessOne` at `k = 0`, `witnessUniform` at `k = 1`)
and one concrete failing matrix (`witnessUnnormalized` at `k = 1`), each
with a proof.

`linearCurve` + `linearCurve_hasDerivAt` show the differentiability
hypothesis of the main theorem is satisfiable, so the theorem is not
vacuous; `linearCurve_witnessUniform_churn_tendsto_half` is a completely
concrete instance in which the limit `1/2` is actually attained by an
actual curve.

## Epistemic status — what is NOT claimed

This file is Layer 1 (Lean mathematics) only, in the same sense as
`FrobeniusChurn.lean`.

- The theorems here are statements about limits of real-valued functions
  built from a differentiable curve of complex matrices. Nothing more.
- NO claim is made that `ρ` is a physical state, that `t` is physical
  time, that the limit IS the kinetic term of any particular action, or
  that any particular physical ansatz is correct. The limit theorem is
  true for every entrywise-differentiable matrix curve, which is exactly
  why it is safe: it does not depend on, and does not select among,
  physical ansätze.
- In particular `CanonicallyNormalized` is a normalization *condition on
  a matrix*, supplied as an explicit hypothesis. It is not asserted to
  hold of anything physical.
- Layers 2 (EEG → ρ(t) construction) and 3 (experimental protocol) are
  not here and are not implied by anything here.

## Norm convention

Inherited from `FrobeniusChurn.lean`: `frobeniusSqDist` is the explicit
sum of squared entry norms, NOT the ambient `Matrix.norm` instance
(which in pinned mathlib is the entrywise sup norm). Every sum in this
file is likewise written out entrywise, so no ambient matrix-norm
instance is ever consulted.

## Provenance

New file, 2026-10-08. No existing file was modified; nothing is
registered in `PF.lean`.
-/

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Topology.Algebra.Monoid
import PF.Consciousness.FrobeniusChurn

namespace PrincipiaTractalis.Consciousness.ChurnKineticDensity

open scoped BigOperators
open Filter
open PrincipiaTractalis.Consciousness.FrobeniusChurn

/-! ## Section 1 — the exact algebraic rewriting of `churn / dt²`

The whole analytic content of the main theorem is in `tendsto_slope_zero`;
this lemma is the bookkeeping that puts `churnFrobenius ⋯ / dt ^ 2` into
difference-quotient form. It is an *identity*, valid for every `dt`
including `dt = 0` (both sides are then `0`, by the `0⁻¹ = 0`
convention), so no `dt ≠ 0` hypothesis is needed. -/

/-- `churnFrobenius (ρ t) (ρ (t + dt)) / dt ^ 2` is exactly `1/2` times the
sum of the squared norms of the entrywise difference quotients. -/
theorem churnFrobenius_div_sq_eq_sum_slope_sq {k : ℕ}
    (ρ : ℝ → Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) (t dt : ℝ) :
    churnFrobenius (ρ t) (ρ (t + dt)) / dt ^ 2
      = (1 / 2) * ∑ i, ∑ j, ‖dt⁻¹ • (ρ (t + dt) i j - ρ t i j)‖ ^ 2 := by
  have hentry : ∀ i j, ‖dt⁻¹ • (ρ (t + dt) i j - ρ t i j)‖ ^ 2
      = (dt ^ 2)⁻¹ * ‖ρ (t + dt) i j - ρ t i j‖ ^ 2 := by
    intro i j
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]
  rw [churnFrobenius_symm]
  simp only [churnFrobenius, frobeniusSqDist, hentry, ← Finset.mul_sum]
  ring

/-! ## Section 2 — the kinetic-density limit -/

/-- **Churn is a kinetic density.**

If the matrix curve `ρ` is entrywise differentiable at `t` with entrywise
derivative `ρ'`, then churn divided by `dt ^ 2` converges, as `dt → 0`
with `dt ≠ 0`, to `(1/2) * ∑ i, ∑ j, ‖ρ' i j‖ ^ 2`.

This is the `½ · (velocity)²` shape: churn's leading small-`dt` behaviour
is quadratic, with coefficient one half of the squared Frobenius velocity. -/
theorem churnFrobenius_div_sq_tendsto {k : ℕ}
    (ρ : ℝ → Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) (t : ℝ)
    (ρ' : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ)
    (hρ : ∀ i j, HasDerivAt (fun s => ρ s i j) (ρ' i j) t) :
    Filter.Tendsto (fun dt => churnFrobenius (ρ t) (ρ (t + dt)) / dt ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((1 / 2) * ∑ i, ∑ j, ‖ρ' i j‖ ^ 2)) := by
  -- Entrywise: the squared norm of the difference quotient converges.
  have hentry : ∀ i j, Filter.Tendsto
      (fun dt : ℝ => ‖dt⁻¹ • (ρ (t + dt) i j - ρ t i j)‖ ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (‖ρ' i j‖ ^ 2)) := by
    intro i j
    exact ((hρ i j).tendsto_slope_zero.norm).pow 2
  -- Sum over the column index, then over the row index.
  have hinner : ∀ i, Filter.Tendsto
      (fun dt : ℝ => ∑ j, ‖dt⁻¹ • (ρ (t + dt) i j - ρ t i j)‖ ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (∑ j, ‖ρ' i j‖ ^ 2)) := fun i =>
    tendsto_finset_sum Finset.univ fun j _ => hentry i j
  have houter : Filter.Tendsto
      (fun dt : ℝ => ∑ i, ∑ j, ‖dt⁻¹ • (ρ (t + dt) i j - ρ t i j)‖ ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (∑ i, ∑ j, ‖ρ' i j‖ ^ 2)) :=
    tendsto_finset_sum Finset.univ fun i _ => hinner i
  have hmul := (tendsto_const_nhds (x := (1 / 2 : ℝ))
    (f := nhdsWithin (0 : ℝ) {0}ᶜ)).mul houter
  exact hmul.congr fun dt => (churnFrobenius_div_sq_eq_sum_slope_sq ρ t dt).symm

/-! ## Section 3 — canonical normalization, with data -/

/-- A velocity matrix is *canonically normalized* when its squared
Frobenius norm (written out entrywise, per the file's norm convention)
equals `1`. This is a condition **supplied as a hypothesis**; it is not
asserted of anything. -/
def CanonicallyNormalized {k : ℕ}
    (ρ' : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) : Prop :=
  ∑ i, ∑ j, ‖ρ' i j‖ ^ 2 = 1

/-- Under canonical normalization of the velocity, the kinetic-density
limit is exactly `1/2`. -/
theorem churnFrobenius_div_sq_tendsto_half {k : ℕ}
    (ρ : ℝ → Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) (t : ℝ)
    (ρ' : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ)
    (hρ : ∀ i j, HasDerivAt (fun s => ρ s i j) (ρ' i j) t)
    (hnorm : CanonicallyNormalized ρ') :
    Filter.Tendsto (fun dt => churnFrobenius (ρ t) (ρ (t + dt)) / dt ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) := by
  have hn : ∑ i, ∑ j, ‖ρ' i j‖ ^ 2 = 1 := hnorm
  have h := churnFrobenius_div_sq_tendsto ρ t ρ' hρ
  rwa [hn, mul_one] at h

/-! ### Non-vacuity witnesses for `CanonicallyNormalized`

The condition is neither empty nor trivial: it is satisfied by concrete
matrices and violated by concrete matrices. -/

/-- Witness at `k = 0`: the `1 × 1` matrix with entry `1`. -/
noncomputable def witnessOne : Matrix (Fin (3 ^ 0)) (Fin (3 ^ 0)) ℂ :=
  fun _ _ => 1

/-- `witnessOne` **satisfies** `CanonicallyNormalized`. -/
theorem witnessOne_canonicallyNormalized : CanonicallyNormalized witnessOne := by
  norm_num [CanonicallyNormalized, witnessOne]

/-- Witness at `k = 1`: the `3 × 3` matrix every one of whose nine entries
is `1/3`, so that the nine squared norms sum to `9 · (1/9) = 1`. -/
noncomputable def witnessUniform : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ :=
  fun _ _ => (1 / 3 : ℂ)

/-- `witnessUniform` **satisfies** `CanonicallyNormalized`. -/
theorem witnessUniform_canonicallyNormalized :
    CanonicallyNormalized witnessUniform := by
  have h3 : ‖(1 / 3 : ℂ)‖ = 1 / 3 := by
    rw [norm_div, norm_one]
    norm_num
  simp only [CanonicallyNormalized, witnessUniform, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h3]
  norm_num

/-- Counter-witness at `k = 1`: the `3 × 3` all-ones matrix. Its nine
squared norms sum to `9`, not `1`. It is nonzero, so the failure is a
genuine normalization failure and not just "the velocity vanishes". -/
noncomputable def witnessUnnormalized : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ :=
  fun _ _ => 1

/-- `witnessUnnormalized` **fails** `CanonicallyNormalized`. -/
theorem witnessUnnormalized_not_canonicallyNormalized :
    ¬ CanonicallyNormalized witnessUnnormalized := by
  simp only [CanonicallyNormalized, witnessUnnormalized, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_one]
  norm_num

/-! ## Section 4 — the differentiability hypothesis is satisfiable

Without this section the main theorem could in principle be vacuous
(hypotheses unsatisfiable). It is not: here is an explicit curve. -/

/-- The straight-line curve `s ↦ s · W` (entrywise scalar multiple). -/
noncomputable def linearCurve {k : ℕ}
    (W : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    ℝ → Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ :=
  fun s i j => (s : ℂ) * W i j

/-- `linearCurve W` is entrywise differentiable everywhere, with entrywise
derivative matrix `W`. -/
theorem linearCurve_hasDerivAt {k : ℕ}
    (W : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) (t : ℝ) :
    ∀ i j, HasDerivAt (fun s => linearCurve W s i j) (W i j) t := by
  intro i j
  have h0 : HasDerivAt (fun s : ℝ => Complex.ofRealCLM s)
      (Complex.ofRealCLM 1) t := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by simpa using h0
  simpa [linearCurve] using h1.mul_const (W i j)

/-- A concrete, non-vacuous instance of the kinetic-density limit. -/
theorem linearCurve_churn_tendsto {k : ℕ}
    (W : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) (t : ℝ) :
    Filter.Tendsto
      (fun dt => churnFrobenius (linearCurve W t) (linearCurve W (t + dt)) / dt ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((1 / 2) * ∑ i, ∑ j, ‖W i j‖ ^ 2)) :=
  churnFrobenius_div_sq_tendsto (linearCurve W) t W (linearCurve_hasDerivAt W t)

/-- Fully concrete end-to-end instance: along the straight-line curve with
canonically normalized velocity `witnessUniform` (at `k = 1`), churn
divided by `dt ^ 2` converges to exactly `1/2`. -/
theorem linearCurve_witnessUniform_churn_tendsto_half (t : ℝ) :
    Filter.Tendsto
      (fun dt => churnFrobenius (linearCurve witnessUniform t)
        (linearCurve witnessUniform (t + dt)) / dt ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) :=
  churnFrobenius_div_sq_tendsto_half (linearCurve witnessUniform) t witnessUniform
    (linearCurve_hasDerivAt witnessUniform t) witnessUniform_canonicallyNormalized

/-! ## Section 5 — the limit filter is non-degenerate

A `Filter.Tendsto f ⊥ l` statement is vacuously true. The convergence
theorems above are therefore only meaningful because the filter they use
is not `⊥`. That is recorded here as a checked theorem rather than left
to the reader. -/

/-- `nhdsWithin 0 {0}ᶜ` on `ℝ` (the punctured-neighbourhood filter at `0`)
is not the trivial filter. Hence the `Tendsto` statements in Sections 2–4
are not vacuous. -/
theorem punctured_nhds_zero_neBot : (nhdsWithin (0 : ℝ) {0}ᶜ).NeBot :=
  inferInstance

/-! ## Section 6 — audit

The `#check` commands print the elaborated statements, so the shipped
statements can be read off the elaborator rather than off the source.
The `#print axioms` commands re-run on every elaboration of this file;
each must report exactly `[propext, Classical.choice, Quot.sound]`. -/

#check @churnFrobenius_div_sq_tendsto
#check @churnFrobenius_div_sq_tendsto_half
#check @CanonicallyNormalized

#print axioms churnFrobenius_div_sq_eq_sum_slope_sq
#print axioms churnFrobenius_div_sq_tendsto
#print axioms churnFrobenius_div_sq_tendsto_half
#print axioms witnessOne_canonicallyNormalized
#print axioms witnessUniform_canonicallyNormalized
#print axioms witnessUnnormalized_not_canonicallyNormalized
#print axioms linearCurve_hasDerivAt
#print axioms linearCurve_churn_tendsto
#print axioms linearCurve_witnessUniform_churn_tendsto_half
#print axioms punctured_nhds_zero_neBot

end PrincipiaTractalis.Consciousness.ChurnKineticDensity
