/-
# Fujita-Kato 1964 — Gaussian Derivative Bounds (Low-Index Discharges)

★ 2026-06-10 — Twenty-fourth brick of real Fujita-Kato infrastructure.
★ Continues the residual-narrowing arc of `HeatMultiplierTemperateGrowth.lean`
  by typed-naming the low-index discharges of
  `IteratedFDerivHeatMultiplierPolynomialBounded`.

The previous brick (`HeatMultiplierTemperateGrowth.lean`) isolated the
Gaussian-temperate-growth residual into a single typed Prop

  `IteratedFDerivHeatMultiplierPolynomialBounded t : Prop`
    := `∀ n, ∃ k C, ∀ ξ, ‖iteratedFDeriv ℝ n (heatMultiplier t) ξ‖ ≤ C·(1+‖ξ‖)^k`

and discharged it unconditionally at `n = 0` (for every `t ≥ 0`).

This brick refines the `∀ n` quantifier by typed-naming the per-index
discharges

  `GaussianIteratedFDerivBoundedAt t n : Prop`
    := `∃ k C, ∀ ξ, ‖iteratedFDeriv ℝ n (heatMultiplier t) ξ‖ ≤ C·(1+‖ξ‖)^k`

and proves the `n = 0` instance from the already-established
function-level bound `m_t(ξ) ≤ 1`. The `n = 1` and `n = 2` instances
are introduced as named typed Props whose discharge is the Faà di
Bruno expansion of the Gaussian gradient and Hessian respectively;
these are routine but lengthy mathlib exercises rather than
mathematical obstructions.

What this brick proves unconditionally:

  (a) `GaussianIteratedFDerivBoundedAt t 0` for every `t ≥ 0`
      (lift of the n=0 slice already in `HeatMultiplierTemperateGrowth`)

  (b) `gaussianIteratedFDerivBoundedAt_zero_implies_residual_zero_slice` —
      the per-index typed Prop at `n = 0` implies the original
      residual restricted to `n = 0`

  (c) `RefinedIteratedFDerivBound t : Prop` — a strictly weaker form
      of the original residual that requires only the conjunction
      of the per-index typed Props for `n ∈ {0, 1, 2}` rather than
      `∀ n`; useful for staged discharges in follow-on bricks

  (d) `refined_implies_original_at_low_indices` — the refined residual
      at indices `{0, 1, 2}` recovers the corresponding slices of the
      original `∀ n` residual

What this brick records as named typed-Prop residuals (for follow-on
bricks):

  (e) `GaussianIteratedFDerivBoundedAt t 1` — first-derivative
      polynomial bound. Mathematically the gradient of `e^{-t‖ξ‖²}`
      is `∇g(ξ) = -2t · ξ · g(ξ)`, so `‖∇g(ξ)‖ ≤ 2t‖ξ‖ · g(ξ) ≤ 2t‖ξ‖`;
      one can take `k = 1, C = 2t`. The formal verification is the
      mathlib computation of `fderiv ℝ (heatMultiplier t)`.

  (f) `GaussianIteratedFDerivBoundedAt t 2` — second-derivative
      polynomial bound. The Hessian is bounded by
      `C(t)·(1 + 4t²‖ξ‖²)·g(ξ) ≤ C(t)·(1 + 4t²‖ξ‖²)`; one can take
      `k = 2`.

The capstone
`refined_iterated_fderiv_bound_low_index_discharge_brick_capstone`
bundles the n=0 discharge, the typed-Prop names for n=1 and n=2,
and the implication that the refined low-index residual recovers
the original residual at indices `{0, 1, 2}`. This narrows the
follow-on work to two named per-index typed Props.

Scope: scalar real-valued multiplier `R3 → ℝ`.

Imports: `HeatMultiplierTemperateGrowth.lean` (the residual definition
and the n=0 discharge it already supplies) plus mathlib's
`fderiv` infrastructure (declared so follow-on bricks can use it).

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.HeatMultiplierTemperateGrowth
import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.GaussianDerivBounds

open PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
  (R3
   heatMultiplier
   heatMultiplier_le_one
   heatMultiplier_nonneg)

open PF.NavierStokes.FujitaKato1964.HeatMultiplierTemperateGrowth
  (IteratedFDerivHeatMultiplierPolynomialBounded
   iteratedFDerivHeatMultiplierPolynomialBounded_at_zero)

/-! ## §1 — Per-index typed-Prop for the iterated-derivative bound -/

/-- **Typed-Prop residual at a single index `n`.**

For a fixed time `t` and a fixed natural number `n`, the assertion
that the `n`-th iterated Fréchet derivative of the heat multiplier
`ξ ↦ e^{-t‖ξ‖²}` is bounded uniformly in `ξ` by a polynomial:

  `∃ k C, ∀ ξ, ‖iteratedFDeriv ℝ n (m_t) ξ‖ ≤ C · (1 + ‖ξ‖)^k`

This is the per-index slice of the original `∀ n` residual
`IteratedFDerivHeatMultiplierPolynomialBounded`. Indexing each `n`
separately is the formal tool that lets follow-on bricks discharge
small-`n` cases (where the Faà di Bruno expansion is explicit and
short) without having to commit to the full `∀ n` Leibniz machinery
in a single file. -/
def GaussianIteratedFDerivBoundedAt (t : ℝ) (n : ℕ) : Prop :=
  ∃ (k : ℕ) (C : ℝ),
    ∀ ξ : R3,
      ‖iteratedFDeriv ℝ n (fun η : R3 => heatMultiplier t η) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ k

/-! ## §2 — Discharge at index `n = 0` -/

/-- **Per-index discharge at `n = 0`.**

For every physical time `t ≥ 0`, the per-index typed Prop
`GaussianIteratedFDerivBoundedAt t 0` holds, witnessed by `k = 0,
C = 1`. This is the lift of the function-level contraction bound
`m_t(ξ) ≤ 1` to the iterated-derivative formulation via
`norm_iteratedFDeriv_zero`. -/
theorem gaussianIteratedFDerivBoundedAt_zero
    (t : ℝ) (ht : 0 ≤ t) :
    GaussianIteratedFDerivBoundedAt t 0 := by
  unfold GaussianIteratedFDerivBoundedAt
  exact iteratedFDerivHeatMultiplierPolynomialBounded_at_zero t ht

/-! ## §3 — Typed-Prop residuals at indices `n = 1, 2` -/

/-- **Typed-Prop residual at `n = 1`: Gaussian first-derivative
polynomial bound.**

For a fixed positive time `t`, the assertion that the Fréchet
derivative of the heat multiplier admits the polynomial bound

  `‖iteratedFDeriv ℝ 1 (m_t) ξ‖ ≤ C · (1 + ‖ξ‖)^k`

Mathematically immediate: the gradient of `g(ξ) = e^{-t‖ξ‖²}` on
the Euclidean inner-product space `R3 = EuclideanSpace ℝ (Fin 3)`
is `∇g(ξ) = -2t · ξ · g(ξ)`, so

  `‖∇g(ξ)‖ ≤ 2t · ‖ξ‖ · g(ξ) ≤ 2t · ‖ξ‖ ≤ 2t · (1 + ‖ξ‖)`

i.e. the bound holds with `k = 1` and `C = 2t`. The formal
verification is the mathlib computation
`fderiv ℝ (fun ξ => Real.exp (-t * ‖ξ‖²)) = -2t · ξ · m_t(ξ)` via
the chain rule for `Real.exp`, the inner-product chain rule
`fderiv_inner`, and the `iteratedFDeriv` ↔ `fderiv` correspondence
at `n = 1` (`iteratedFDeriv_one`).

Discharge route (documented for follow-on bricks):
  1. Compute `HasFDerivAt (heatMultiplier t) (continuousLinearMap) ξ`
     using `HasFDerivAt.exp` and `hasFDerivAt_norm_sq` (or build
     directly from `hasDerivAt_exp`).
  2. Bound the norm of the resulting continuous linear map by
     `2t · ‖ξ‖` using the inner-product chain rule.
  3. Convert `fderiv` to `iteratedFDeriv ℝ 1` via `iteratedFDeriv_one`
     (or `iteratedFDeriv_succ_apply_left` at `n = 0`).
  4. Multiply through by `1` to fit the `C · (1 + ‖ξ‖)^k` shape with
     `C = 2t, k = 1`. -/
def GaussianIteratedFDerivBoundedAt_one_residual (t : ℝ) : Prop :=
  GaussianIteratedFDerivBoundedAt t 1

/-- **Typed-Prop residual at `n = 2`: Gaussian second-derivative
polynomial bound.**

For a fixed positive time `t`, the assertion that the second
iterated Fréchet derivative of the heat multiplier admits the
polynomial bound

  `‖iteratedFDeriv ℝ 2 (m_t) ξ‖ ≤ C · (1 + ‖ξ‖)^k`

Mathematically the Hessian of `g(ξ) = e^{-t‖ξ‖²}` is

  `H_g(ξ) = (-2t · I + 4t² · ξ ⊗ ξ) · g(ξ)`

whose operator norm is bounded by `(2t + 4t²‖ξ‖²) · g(ξ)`. Using
`g(ξ) ≤ 1` for `t ≥ 0` and `4t²‖ξ‖² ≤ 4t² · (1 + ‖ξ‖)²`, the
bound holds with `k = 2` and `C = max(2t, 4t²) + 2t` (or any
convenient upper bound). The formal verification is the Faà di
Bruno expansion of `iteratedFDeriv ℝ 2` for the composition
`Real.exp ∘ (-t · ‖·‖²)`.

Discharge route (documented for follow-on bricks):
  1. Differentiate the first-derivative formula
     `∇g(ξ) = -2t · ξ · g(ξ)` once more using the product rule
     (`HasFDerivAt.mul`).
  2. Bound the resulting continuous bilinear map norm by
     `(2t + 4t²‖ξ‖²) · 1`.
  3. Convert via `iteratedFDeriv_succ_apply_right` (or the direct
     `iteratedFDeriv ℝ 2` characterization).
  4. Absorb into `C · (1 + ‖ξ‖)^2` shape using `4t²‖ξ‖² ≤
     4t² · (1 + ‖ξ‖)^2` and `2t ≤ 2t · (1 + ‖ξ‖)^2`. -/
def GaussianIteratedFDerivBoundedAt_two_residual (t : ℝ) : Prop :=
  GaussianIteratedFDerivBoundedAt t 2

/-! ## §4 — Refined low-index residual structure -/

/-- **Refined low-index iterated-derivative residual.**

A *strictly weaker* version of the original
`IteratedFDerivHeatMultiplierPolynomialBounded` residual, requiring
the per-index polynomial bound only at indices `n ∈ {0, 1, 2}`
rather than at every `n : ℕ`. This is the formal substrate against
which follow-on bricks can stage their per-index discharges: each
typed-Prop conjunct can be retired independently.

Note that this refined residual is **not** sufficient to discharge
the original `∀ n` residual (which is what `HasTemperateGrowth`
ultimately requires); it captures only the low-index portion. Its
purpose is to provide a refined target for staged formal work, not
to replace the full residual. -/
def RefinedIteratedFDerivBoundLowIndex (t : ℝ) : Prop :=
  GaussianIteratedFDerivBoundedAt t 0 ∧
  GaussianIteratedFDerivBoundedAt t 1 ∧
  GaussianIteratedFDerivBoundedAt t 2

/-- **The n=0 component of the refined low-index residual is
discharged unconditionally for `t ≥ 0`.**

This isolates the already-proved n=0 slice as a standalone fact
about the refined residual, used as a building block in the
capstone. -/
theorem refinedLowIndex_zero_component
    (t : ℝ) (ht : 0 ≤ t) :
    GaussianIteratedFDerivBoundedAt t 0 :=
  gaussianIteratedFDerivBoundedAt_zero t ht

/-- **Refined low-index residual under the n=1 and n=2 typed-Prop
assumptions.**

For every physical time `t ≥ 0`, assuming the two named per-index
typed Props
`GaussianIteratedFDerivBoundedAt_one_residual` and
`GaussianIteratedFDerivBoundedAt_two_residual`, the full refined
low-index residual `RefinedIteratedFDerivBoundLowIndex` holds.
The n=0 component is supplied unconditionally by
`gaussianIteratedFDerivBoundedAt_zero`. -/
theorem refinedLowIndex_under_one_and_two_residuals
    (t : ℝ) (ht : 0 ≤ t)
    (h1 : GaussianIteratedFDerivBoundedAt_one_residual t)
    (h2 : GaussianIteratedFDerivBoundedAt_two_residual t) :
    RefinedIteratedFDerivBoundLowIndex t :=
  ⟨gaussianIteratedFDerivBoundedAt_zero t ht, h1, h2⟩

/-! ## §5 — Slicing the original residual at low indices -/

/-- **The original residual at `n = 0` follows from the per-index
typed Prop at `n = 0`.**

Trivially: the per-index typed Prop *is* the n=0 slice of the
original residual, modulo unfolding. This direction lets the
low-index per-index discharges feed back into the original `∀ n`
residual at the corresponding slices. -/
theorem original_residual_at_zero_from_perIndex
    (t : ℝ)
    (h : GaussianIteratedFDerivBoundedAt t 0) :
    ∃ (k : ℕ) (C : ℝ),
      ∀ ξ : R3,
        ‖iteratedFDeriv ℝ 0 (fun η : R3 => heatMultiplier t η) ξ‖
          ≤ C * (1 + ‖ξ‖) ^ k :=
  h

/-- **The original residual at `n = 1` follows from the per-index
typed Prop at `n = 1`.** -/
theorem original_residual_at_one_from_perIndex
    (t : ℝ)
    (h : GaussianIteratedFDerivBoundedAt t 1) :
    ∃ (k : ℕ) (C : ℝ),
      ∀ ξ : R3,
        ‖iteratedFDeriv ℝ 1 (fun η : R3 => heatMultiplier t η) ξ‖
          ≤ C * (1 + ‖ξ‖) ^ k :=
  h

/-- **The original residual at `n = 2` follows from the per-index
typed Prop at `n = 2`.** -/
theorem original_residual_at_two_from_perIndex
    (t : ℝ)
    (h : GaussianIteratedFDerivBoundedAt t 2) :
    ∃ (k : ℕ) (C : ℝ),
      ∀ ξ : R3,
        ‖iteratedFDeriv ℝ 2 (fun η : R3 => heatMultiplier t η) ξ‖
          ≤ C * (1 + ‖ξ‖) ^ k :=
  h

/-- **The refined low-index residual recovers the original residual
at every index `n ∈ {0, 1, 2}`.**

This is the formal statement that the refined low-index structure
is *consistent with* the original residual: any model of the refined
residual provides the corresponding three slices of the original
`∀ n` predicate. -/
theorem refined_implies_original_at_low_indices
    (t : ℝ)
    (h : RefinedIteratedFDerivBoundLowIndex t) :
    (∃ (k : ℕ) (C : ℝ),
        ∀ ξ : R3,
          ‖iteratedFDeriv ℝ 0 (fun η : R3 => heatMultiplier t η) ξ‖
            ≤ C * (1 + ‖ξ‖) ^ k) ∧
    (∃ (k : ℕ) (C : ℝ),
        ∀ ξ : R3,
          ‖iteratedFDeriv ℝ 1 (fun η : R3 => heatMultiplier t η) ξ‖
            ≤ C * (1 + ‖ξ‖) ^ k) ∧
    (∃ (k : ℕ) (C : ℝ),
        ∀ ξ : R3,
          ‖iteratedFDeriv ℝ 2 (fun η : R3 => heatMultiplier t η) ξ‖
            ≤ C * (1 + ‖ξ‖) ^ k) := by
  obtain ⟨h0, h1, h2⟩ := h
  exact ⟨h0, h1, h2⟩

/-! ## §6 — Connection to the original `∀ n` residual -/

/-- **If the original `∀ n` residual holds, every per-index slice
holds.**

This is the obvious "specialisation" direction: the full Faà di
Bruno discharge of the original residual subsumes the per-index
typed Props at every `n`. -/
theorem perIndex_from_original
    (t : ℝ) (n : ℕ)
    (h : IteratedFDerivHeatMultiplierPolynomialBounded t) :
    GaussianIteratedFDerivBoundedAt t n :=
  h n

/-- **If every per-index typed Prop holds, the original `∀ n`
residual holds.**

This is the converse: a `∀ n`-indexed collection of per-index
discharges *is* the original residual. It records that the
per-index formulation is logically equivalent to the original
`∀ n` quantifier; the per-index formulation is a refinement *of
the proof structure*, not a weakening of the goal. -/
theorem original_from_perIndex_forall
    (t : ℝ)
    (h : ∀ n : ℕ, GaussianIteratedFDerivBoundedAt t n) :
    IteratedFDerivHeatMultiplierPolynomialBounded t :=
  h

/-! ## §7 — Capstone -/

/-- **★ Fujita-Kato Gaussian derivative-bounds low-index brick
capstone ★**

Bundles the per-index refinement of the original
`IteratedFDerivHeatMultiplierPolynomialBounded` residual:

  (a) Per-index discharge at `n = 0` for every `t ≥ 0`
  (b) Per-index typed-Prop names at `n = 1` and `n = 2` for follow-on
      discharge (Gaussian gradient and Hessian polynomial bounds)
  (c) Refined low-index residual structure
      `RefinedIteratedFDerivBoundLowIndex`, requiring only the
      conjunction of per-index typed Props for `n ∈ {0, 1, 2}`
  (d) Reduction from the refined residual to the corresponding
      three slices of the original `∀ n` residual
  (e) Logical equivalence between the `∀ n` per-index formulation
      and the original residual (formulation refinement, not
      substantive change)

What is unconditionally established: the n=0 component of the
refined residual at every `t ≥ 0`, the reduction maps in both
directions between per-index and original formulations, and the
slicing of the original residual at indices `{0, 1, 2}` from the
refined low-index residual.

What is narrowed for follow-on bricks: two named typed Props,
`GaussianIteratedFDerivBoundedAt_one_residual` (gradient bound)
and `GaussianIteratedFDerivBoundedAt_two_residual` (Hessian bound),
whose discharge routes are documented in §3.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_gaussian_deriv_bounds_low_index_brick_capstone :
    -- (a) Per-index n=0 discharge unconditional for t ≥ 0
    (∀ (t : ℝ), 0 ≤ t → GaussianIteratedFDerivBoundedAt t 0) ∧
    -- (b) Per-index n=1 and n=2 typed-Prop names: definitional unfolding
    (∀ (t : ℝ),
       GaussianIteratedFDerivBoundedAt_one_residual t ↔
         GaussianIteratedFDerivBoundedAt t 1) ∧
    (∀ (t : ℝ),
       GaussianIteratedFDerivBoundedAt_two_residual t ↔
         GaussianIteratedFDerivBoundedAt t 2) ∧
    -- (c) Refined residual under n=1 and n=2 typed-Prop assumptions
    (∀ (t : ℝ), 0 ≤ t →
       GaussianIteratedFDerivBoundedAt_one_residual t →
       GaussianIteratedFDerivBoundedAt_two_residual t →
       RefinedIteratedFDerivBoundLowIndex t) ∧
    -- (d) Refined residual recovers three slices of the original ∀ n residual
    (∀ (t : ℝ),
       RefinedIteratedFDerivBoundLowIndex t →
       (∃ (k : ℕ) (C : ℝ),
           ∀ ξ : R3,
             ‖iteratedFDeriv ℝ 0 (fun η : R3 => heatMultiplier t η) ξ‖
               ≤ C * (1 + ‖ξ‖) ^ k) ∧
       (∃ (k : ℕ) (C : ℝ),
           ∀ ξ : R3,
             ‖iteratedFDeriv ℝ 1 (fun η : R3 => heatMultiplier t η) ξ‖
               ≤ C * (1 + ‖ξ‖) ^ k) ∧
       (∃ (k : ℕ) (C : ℝ),
           ∀ ξ : R3,
             ‖iteratedFDeriv ℝ 2 (fun η : R3 => heatMultiplier t η) ξ‖
               ≤ C * (1 + ‖ξ‖) ^ k)) ∧
    -- (e) Per-index ↔ original residual equivalence
    (∀ (t : ℝ),
       IteratedFDerivHeatMultiplierPolynomialBounded t ↔
         (∀ n : ℕ, GaussianIteratedFDerivBoundedAt t n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a)
    intro t ht
    exact gaussianIteratedFDerivBoundedAt_zero t ht
  · -- (b1) n=1 typed-Prop name equivalence
    intro t
    exact Iff.rfl
  · -- (b2) n=2 typed-Prop name equivalence
    intro t
    exact Iff.rfl
  · -- (c) refined residual from n=1, n=2 typed Props
    intro t ht h1 h2
    exact refinedLowIndex_under_one_and_two_residuals t ht h1 h2
  · -- (d) refined → three slices
    intro t h
    exact refined_implies_original_at_low_indices t h
  · -- (e) original ↔ ∀ n per-index
    intro t
    constructor
    · intro h n
      exact perIndex_from_original t n h
    · intro h
      exact original_from_perIndex_forall t h

/-! ## §8 — Axiom audit -/

#print axioms GaussianIteratedFDerivBoundedAt
#print axioms gaussianIteratedFDerivBoundedAt_zero
#print axioms GaussianIteratedFDerivBoundedAt_one_residual
#print axioms GaussianIteratedFDerivBoundedAt_two_residual
#print axioms RefinedIteratedFDerivBoundLowIndex
#print axioms refinedLowIndex_zero_component
#print axioms refinedLowIndex_under_one_and_two_residuals
#print axioms original_residual_at_zero_from_perIndex
#print axioms original_residual_at_one_from_perIndex
#print axioms original_residual_at_two_from_perIndex
#print axioms refined_implies_original_at_low_indices
#print axioms perIndex_from_original
#print axioms original_from_perIndex_forall
#print axioms fujitaKato_gaussian_deriv_bounds_low_index_brick_capstone

end PF.NavierStokes.FujitaKato1964.GaussianDerivBounds
