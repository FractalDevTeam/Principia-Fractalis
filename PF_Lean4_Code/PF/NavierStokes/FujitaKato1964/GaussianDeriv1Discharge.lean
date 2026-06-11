/-
# Fujita-Kato 1964 — Gaussian Derivative Bound at n=1 (Unconditional Discharge)

★ 2026-06-10 — Twenty-eighth brick of real Fujita-Kato infrastructure.
★ Discharges, *without* any auxiliary hypothesis, the n=1 typed-Prop
  residual `GaussianIteratedFDerivBoundedAt t 1` left open by
  `GaussianDerivBounds.lean`.

The previous brick (`GaussianDerivBounds.lean`) refined the
Gaussian-temperate-growth residual into per-index typed Props

  `GaussianIteratedFDerivBoundedAt t n : Prop`
    := `∃ k C, ∀ ξ, ‖iteratedFDeriv ℝ n (m_t) ξ‖ ≤ C·(1+‖ξ‖)^k`

and discharged the `n = 0` slice via `m_t(ξ) ≤ 1`. The `n = 1` slice
was recorded as a typed-Prop residual with a documented mathlib
discharge route through `HasFDerivAt.exp`, `HasFDerivAt.norm_sq`, and
the inner-product chain rule. This brick *executes* that route and
lands the n=1 discharge unconditionally for every `t ≥ 0`.

Mathematical content. For the heat-multiplier symbol

  `g(ξ) := e^{-t ‖ξ‖²}`

on `R3 = EuclideanSpace ℝ (Fin 3)`, the gradient is

  `∇g(ξ) = (-2 t) · g(ξ) · innerSL ℝ ξ`

i.e. the Fréchet derivative is the continuous linear map

  `Dg(ξ)(v) = (-2 t) · g(ξ) · ⟪ξ, v⟫`

Its operator norm is

  `‖Dg(ξ)‖ = |2 t| · g(ξ) · ‖ξ‖ ≤ 2 t · ‖ξ‖`

(using `g(ξ) ≤ 1` for `t ≥ 0` and `t ≥ 0` to drop the absolute
value). Using `‖ξ‖ ≤ 1 + ‖ξ‖`, this gives the witnesses
`k = 1, C = 2 t` for the polynomial bound

  `‖iteratedFDeriv ℝ 1 (m_t) ξ‖ ≤ 2 t · (1 + ‖ξ‖)^1`

after converting `‖iteratedFDeriv ℝ 1 f‖ = ‖fderiv ℝ f‖` via
`norm_iteratedFDerivWithin_one` + `iteratedFDerivWithin_univ`.

What this brick proves unconditionally:

  (a) `hasFDerivAt_heatMultiplier` — the explicit Fréchet derivative
      of `heatMultiplier t` at every `ξ : R3`, expressed as the
      continuous linear map
      `g(ξ) • ((-t) • (2 • innerSL ℝ ξ))`.

  (b) `norm_fderiv_heatMultiplier_le` — the operator-norm bound
      `‖fderiv ℝ (heatMultiplier t) ξ‖ ≤ 2 t · ‖ξ‖` for `t ≥ 0`.

  (c) `iteratedFDeriv_one_heatMultiplier_norm_le` — the same bound
      lifted to `‖iteratedFDeriv ℝ 1 (heatMultiplier t) ξ‖`.

  (d) `iteratedFDeriv_heatMultiplier_one_polynomial_bound` — the
      polynomial-bound shape `C · (1 + ‖ξ‖)^k` with `C = 2 t, k = 1`.

  (e) `gaussianIteratedFDerivBoundedAt_one` — the per-index typed
      Prop at `n = 1` is discharged.

  (f) `fujitaKato_gaussian_deriv_one_discharge_brick_capstone` —
      bundle of all five.

Scope: scalar real-valued multiplier `R3 → ℝ`.

Imports: the per-index Prop and the heat-multiplier definition from
the preceding bricks, plus mathlib's `HasFDerivAt.exp` and the
inner-product calculus.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.GaussianDerivBounds
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.GaussianDeriv1Discharge

open PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
  (R3
   heatMultiplier
   heatMultiplier_le_one
   heatMultiplier_nonneg)

open PF.NavierStokes.FujitaKato1964.GaussianDerivBounds
  (GaussianIteratedFDerivBoundedAt
   GaussianIteratedFDerivBoundedAt_one_residual)

/-! ## §1 — Fréchet derivative of the heat multiplier -/

/-- **Explicit Fréchet derivative of the heat-multiplier at `ξ`.**

For every real time `t` and every frequency `ξ : R3 = EuclideanSpace
ℝ (Fin 3)`, the Gaussian multiplier `g(ξ) = e^{-t ‖ξ‖²}` is Fréchet
differentiable at `ξ` with derivative

  `g(ξ) • ((-t) • (2 • innerSL ℝ ξ))`

i.e. the continuous linear map `v ↦ (-2 t) · g(ξ) · ⟪ξ, v⟫`. The
proof is the chain `HasFDerivAt.exp` ∘ `HasFDerivAt.const_smul (-t)`
∘ `HasFDerivAt.norm_sq` (applied to `hasFDerivAt_id`). -/
theorem hasFDerivAt_heatMultiplier (t : ℝ) (ξ : R3) :
    HasFDerivAt (fun η : R3 => heatMultiplier t η)
      (heatMultiplier t ξ • ((-t) • (2 • innerSL ℝ ξ))) ξ := by
  -- Step 1: derivative of ‖·‖² at ξ is `2 • innerSL ℝ ξ`.
  have h_ns : HasFDerivAt (fun η : R3 => ‖η‖ ^ 2)
      (2 • (innerSL ℝ ξ)) ξ := by
    have := (hasFDerivAt_id (𝕜 := ℝ) ξ).norm_sq
    -- `HasFDerivAt.norm_sq` produces
    -- `HasFDerivAt (‖·‖ ^ 2) (2 • (innerSL ℝ ξ).comp (id : R3 →L[ℝ] R3)) ξ`
    -- which simplifies (`.comp id = ·`).
    simpa using this
  -- Step 2: multiply by the scalar `(-t)`.
  have h_neg :
      HasFDerivAt (fun η : R3 => (-t) • (‖η‖ ^ 2))
        ((-t) • (2 • (innerSL ℝ ξ))) ξ :=
    h_ns.const_smul (-t)
  -- Recast `(-t) • r = -t * r` (smul on ℝ is multiplication).
  have h_inner : HasFDerivAt (fun η : R3 => -t * ‖η‖ ^ 2)
      ((-t) • (2 • (innerSL ℝ ξ))) ξ := by
    have hfun : (fun η : R3 => (-t) • (‖η‖ ^ 2)) =
        (fun η : R3 => -t * ‖η‖ ^ 2) := by
      funext η; simp [smul_eq_mul]
    rw [← hfun]
    exact h_neg
  -- Step 3: outer composition with `Real.exp`.
  have h_exp := h_inner.exp
  -- Unfold `heatMultiplier`.
  unfold heatMultiplier
  exact h_exp

/-! ## §2 — Operator-norm bound on the Fréchet derivative -/

/-- **Norm bound on the Gaussian Fréchet derivative for `t ≥ 0`.**

For every physical time `t ≥ 0` and every `ξ`,

  `‖fderiv ℝ (heatMultiplier t) ξ‖ ≤ 2 t · ‖ξ‖`.

Proof: convert the `fderiv` to the explicit form supplied by
`hasFDerivAt_heatMultiplier`; chain norms via `norm_smul`; use
`heatMultiplier t ξ ≤ 1`, `0 ≤ heatMultiplier t ξ`, `0 ≤ t`, and
`‖innerSL ℝ ξ‖ = ‖ξ‖`. The natural-number action `(2 : ℕ) • (innerSL
ℝ ξ)` on the continuous-linear-map space contributes a factor `2 ·
‖innerSL ℝ ξ‖`. -/
theorem norm_fderiv_heatMultiplier_le
    (t : ℝ) (ht : 0 ≤ t) (ξ : R3) :
    ‖fderiv ℝ (fun η : R3 => heatMultiplier t η) ξ‖ ≤ 2 * t * ‖ξ‖ := by
  -- Rewrite `fderiv` via the explicit form.
  have hfd := (hasFDerivAt_heatMultiplier t ξ).fderiv
  rw [hfd]
  -- The explicit form: `g(ξ) • ((-t) • (2 • innerSL ℝ ξ))`.
  -- Step 1: outer real-scalar smul.
  rw [norm_smul]
  -- Now `‖g(ξ)‖ * ‖(-t) • (2 • innerSL ℝ ξ)‖`.
  rw [norm_smul]
  -- Now `‖g(ξ)‖ * (‖-t‖ * ‖(2 : ℕ) • innerSL ℝ ξ‖)`.
  -- The natural-number smul: `(2 : ℕ) • L = L + L`, with norm bounded
  -- by `(2 : ℝ) * ‖L‖`. We use `norm_nsmul_le` (or direct rewriting).
  -- Simpler: rewrite `(2 : ℕ) • L = ((2 : ℕ) : ℝ) • L` via
  -- `Nat.cast_smul_eq_nsmul`, then `norm_smul`.
  have hnsmul_norm :
      ‖(2 : ℕ) • (innerSL ℝ ξ : R3 →L[ℝ] ℝ)‖
        = 2 * ‖(innerSL ℝ ξ : R3 →L[ℝ] ℝ)‖ := by
    rw [show ((2 : ℕ) • (innerSL ℝ ξ : R3 →L[ℝ] ℝ))
            = ((2 : ℕ) : ℝ) • (innerSL ℝ ξ : R3 →L[ℝ] ℝ) from
          (Nat.cast_smul_eq_nsmul ℝ 2 _).symm]
    rw [norm_smul]
    simp
  rw [hnsmul_norm]
  -- Now `‖g(ξ)‖ * (‖-t‖ * (2 * ‖innerSL ℝ ξ‖))`.
  rw [innerSL_apply_norm]
  -- Now `‖g(ξ)‖ * (‖-t‖ * (2 * ‖ξ‖))`.
  -- Bound `‖g(ξ)‖ = g(ξ) ≤ 1` (using nonneg + le_one), `‖-t‖ = t`.
  have hg_nonneg : 0 ≤ heatMultiplier t ξ := heatMultiplier_nonneg t ξ
  have hg_le_one : heatMultiplier t ξ ≤ 1 := heatMultiplier_le_one t ht ξ
  have hg_norm : ‖heatMultiplier t ξ‖ = heatMultiplier t ξ :=
    Real.norm_of_nonneg hg_nonneg
  have hneg_t_norm : ‖(-t : ℝ)‖ = t := by
    rw [norm_neg, Real.norm_of_nonneg ht]
  rw [hg_norm, hneg_t_norm]
  -- Now `g(ξ) * (t * (2 * ‖ξ‖)) ≤ 2 * t * ‖ξ‖`.
  -- Bound `g(ξ) ≤ 1` and `t * (2 * ‖ξ‖) ≥ 0`.
  have hrhs_nonneg : 0 ≤ t * (2 * ‖ξ‖) := by
    have : 0 ≤ 2 * ‖ξ‖ := by positivity
    exact mul_nonneg ht this
  calc heatMultiplier t ξ * (t * (2 * ‖ξ‖))
      ≤ 1 * (t * (2 * ‖ξ‖)) :=
        mul_le_mul_of_nonneg_right hg_le_one hrhs_nonneg
    _ = 2 * t * ‖ξ‖ := by ring

/-! ## §3 — Lifting to `iteratedFDeriv ℝ 1` -/

/-- **The iterated-derivative norm at `n = 1` agrees with the
Fréchet-derivative norm.** A specialisation of
`norm_iteratedFDerivWithin_one` to the whole space, using
`iteratedFDerivWithin_univ` to translate to the global
`iteratedFDeriv`. -/
theorem norm_iteratedFDeriv_one_eq_fderiv
    (f : R3 → ℝ) (ξ : R3) :
    ‖iteratedFDeriv ℝ 1 f ξ‖ = ‖fderiv ℝ f ξ‖ := by
  rw [← iteratedFDerivWithin_univ]
  rw [norm_iteratedFDerivWithin_one f (uniqueDiffOn_univ ξ (Set.mem_univ _))]
  rw [fderivWithin_univ]

/-- **Norm bound on the `iteratedFDeriv ℝ 1` of the heat-multiplier
for `t ≥ 0`.** -/
theorem iteratedFDeriv_one_heatMultiplier_norm_le
    (t : ℝ) (ht : 0 ≤ t) (ξ : R3) :
    ‖iteratedFDeriv ℝ 1 (fun η : R3 => heatMultiplier t η) ξ‖
      ≤ 2 * t * ‖ξ‖ := by
  rw [norm_iteratedFDeriv_one_eq_fderiv]
  exact norm_fderiv_heatMultiplier_le t ht ξ

/-! ## §4 — Polynomial-bound shape `C · (1 + ‖ξ‖)^k` at `n = 1` -/

/-- **Polynomial bound at `n = 1`.**

The Fréchet derivative of the heat-multiplier admits the polynomial
bound `2 t · (1 + ‖ξ‖)^1` for every `t ≥ 0`. This is the shape
required by `GaussianIteratedFDerivBoundedAt`.

The proof chains `iteratedFDeriv_one_heatMultiplier_norm_le` with
`‖ξ‖ ≤ 1 + ‖ξ‖`. -/
theorem iteratedFDeriv_heatMultiplier_one_polynomial_bound
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ ξ : R3,
      ‖iteratedFDeriv ℝ 1 (fun η : R3 => heatMultiplier t η) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ 1 := by
  refine ⟨2 * t, ?_⟩
  intro ξ
  have h1 := iteratedFDeriv_one_heatMultiplier_norm_le t ht ξ
  have h2t_nonneg : 0 ≤ 2 * t := by positivity
  have hxi_le : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  calc ‖iteratedFDeriv ℝ 1 (fun η : R3 => heatMultiplier t η) ξ‖
      ≤ 2 * t * ‖ξ‖ := h1
    _ = (2 * t) * ‖ξ‖ := by ring
    _ ≤ (2 * t) * (1 + ‖ξ‖) :=
        mul_le_mul_of_nonneg_left hxi_le h2t_nonneg
    _ = 2 * t * (1 + ‖ξ‖) ^ 1 := by ring

/-! ## §5 — Discharge of the n=1 per-index typed Prop -/

/-- **Unconditional discharge of `GaussianIteratedFDerivBoundedAt t
1` for every `t ≥ 0`.**

The per-index typed Prop at `n = 1` is witnessed by `k = 1, C = 2 t`,
with the explicit polynomial bound supplied by
`iteratedFDeriv_heatMultiplier_one_polynomial_bound`. -/
theorem gaussianIteratedFDerivBoundedAt_one
    (t : ℝ) (ht : 0 ≤ t) :
    GaussianIteratedFDerivBoundedAt t 1 := by
  unfold GaussianIteratedFDerivBoundedAt
  obtain ⟨C, hC⟩ := iteratedFDeriv_heatMultiplier_one_polynomial_bound t ht
  exact ⟨1, C, hC⟩

/-- **The named residual `GaussianIteratedFDerivBoundedAt_one_residual`
is unconditionally discharged for `t ≥ 0`.** Unfolding-only
corollary that exposes the discharge of the typed-Prop name from
`GaussianDerivBounds.lean`. -/
theorem gaussianIteratedFDerivBoundedAt_one_residual_discharged
    (t : ℝ) (ht : 0 ≤ t) :
    GaussianIteratedFDerivBoundedAt_one_residual t :=
  gaussianIteratedFDerivBoundedAt_one t ht

/-! ## §6 — Capstone -/

/-- **★ Fujita-Kato Gaussian n=1 derivative-bound discharge brick
capstone ★**

Bundles the unconditional discharge of the n=1 typed-Prop residual
left open by `GaussianDerivBounds.lean`:

  (a) `hasFDerivAt_heatMultiplier` — explicit form of the gradient
      of `e^{-t ‖ξ‖²}` at every `ξ`.

  (b) `norm_fderiv_heatMultiplier_le` — operator-norm bound
      `‖fderiv ℝ (m_t) ξ‖ ≤ 2 t · ‖ξ‖` for `t ≥ 0`.

  (c) `iteratedFDeriv_one_heatMultiplier_norm_le` — lift to
      `‖iteratedFDeriv ℝ 1 (m_t) ξ‖ ≤ 2 t · ‖ξ‖`.

  (d) Polynomial-bound shape with `k = 1, C = 2 t`.

  (e) `GaussianIteratedFDerivBoundedAt t 1` discharged for every
      `t ≥ 0` (and equivalently the named residual
      `GaussianIteratedFDerivBoundedAt_one_residual`).

With this brick, the n=1 slice of the refined low-index residual
`RefinedIteratedFDerivBoundLowIndex t` of `GaussianDerivBounds.lean`
is unconditionally landed; the only remaining typed-Prop residual at
low indices is `GaussianIteratedFDerivBoundedAt t 2` (Hessian
polynomial bound).

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_gaussian_deriv_one_discharge_brick_capstone :
    -- (a) Explicit gradient HasFDerivAt
    (∀ (t : ℝ) (ξ : R3),
       HasFDerivAt (fun η : R3 => heatMultiplier t η)
         (heatMultiplier t ξ • ((-t) • (2 • innerSL ℝ ξ))) ξ) ∧
    -- (b) Operator-norm bound on fderiv for t ≥ 0
    (∀ (t : ℝ), 0 ≤ t → ∀ (ξ : R3),
       ‖fderiv ℝ (fun η : R3 => heatMultiplier t η) ξ‖ ≤ 2 * t * ‖ξ‖) ∧
    -- (c) Norm bound on iteratedFDeriv ℝ 1
    (∀ (t : ℝ), 0 ≤ t → ∀ (ξ : R3),
       ‖iteratedFDeriv ℝ 1 (fun η : R3 => heatMultiplier t η) ξ‖
         ≤ 2 * t * ‖ξ‖) ∧
    -- (d) Polynomial-bound shape at n = 1
    (∀ (t : ℝ), 0 ≤ t →
       ∃ C : ℝ, ∀ ξ : R3,
         ‖iteratedFDeriv ℝ 1 (fun η : R3 => heatMultiplier t η) ξ‖
           ≤ C * (1 + ‖ξ‖) ^ 1) ∧
    -- (e) GaussianIteratedFDerivBoundedAt t 1 discharged for t ≥ 0
    (∀ (t : ℝ), 0 ≤ t → GaussianIteratedFDerivBoundedAt t 1) ∧
    -- (e') The named residual unconditionally discharged
    (∀ (t : ℝ), 0 ≤ t → GaussianIteratedFDerivBoundedAt_one_residual t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ξ; exact hasFDerivAt_heatMultiplier t ξ
  · intro t ht ξ; exact norm_fderiv_heatMultiplier_le t ht ξ
  · intro t ht ξ; exact iteratedFDeriv_one_heatMultiplier_norm_le t ht ξ
  · intro t ht; exact iteratedFDeriv_heatMultiplier_one_polynomial_bound t ht
  · intro t ht; exact gaussianIteratedFDerivBoundedAt_one t ht
  · intro t ht; exact gaussianIteratedFDerivBoundedAt_one_residual_discharged t ht

/-! ## §7 — Axiom audit -/

#print axioms hasFDerivAt_heatMultiplier
#print axioms norm_fderiv_heatMultiplier_le
#print axioms norm_iteratedFDeriv_one_eq_fderiv
#print axioms iteratedFDeriv_one_heatMultiplier_norm_le
#print axioms iteratedFDeriv_heatMultiplier_one_polynomial_bound
#print axioms gaussianIteratedFDerivBoundedAt_one
#print axioms gaussianIteratedFDerivBoundedAt_one_residual_discharged
#print axioms fujitaKato_gaussian_deriv_one_discharge_brick_capstone

end PF.NavierStokes.FujitaKato1964.GaussianDeriv1Discharge
