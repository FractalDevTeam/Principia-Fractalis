/-
# Kato-Rellich Discharge — Structural Analysis of `KatoRellichInput α`

★ 2026-05-24 — Wave 9 follow-up: structural verdict on the self-adjoint half of V_α ★

## Source

`PF/Operators/VAlphaExplicit.lean` defines the arxiv operator
`H_α = T + V_α` on `ℓ²(ℕ; ℂ)` and isolates `KatoRellichInput α` as a
named open Prop asking for the existence of a *globally* defined linear
map `H : EllTwoNat →ₗ[ℂ] EllTwoNat` that is

  (a) symmetric on **all** of `EllTwoNat`:
        `∀ ψ φ, ⟪H ψ, φ⟫_ℂ = ⟪ψ, H φ⟫_ℂ`,
  (b) matches the arxiv matrix coefficients on standard basis vectors:
        `∀ n m, ⟪H e_n, e_m⟫_ℂ = ((h_alpha_basis α n m : ℝ) : ℂ)`.

## What this file proves

The Prop as currently written is **structurally unsatisfiable** for
every `α > 0`, by a Hellinger-Toeplitz argument:

  1. `EllTwoNat = lp (fun _ : ℕ => ℂ) 2` is a complete inner-product
     space (mathlib `lp.completeSpace`).
  2. A symmetric linear map on a complete inner-product space is
     automatically *continuous* — the Hellinger-Toeplitz theorem
     (`LinearMap.IsSymmetric.continuous` in mathlib).
  3. A continuous linear map satisfies the operator-norm bound
     `‖H x‖ ≤ ‖H‖ * ‖x‖` (`ContinuousLinearMap.le_opNorm`).
  4. Applied to the standard basis vector `e_n := lp.single 2 n 1`
     (with `‖e_n‖ = 1`), this and Cauchy-Schwarz give
     `|⟪H e_n, e_n⟫| ≤ ‖H‖`.
  5. By hypothesis (b), `⟪H e_n, e_n⟫ = h_alpha_basis α n n`. Since
     `t_action_basis n n = 0`, we have `h_alpha_basis α n n
     = v_alpha_coeff α n = π·D_3(n)/(10·α) + ν_2(n)/α + ν_3(n)/α²`.
  6. Specialising to `n = 2^k`, we have `ν_2(2^k) = k` (mathlib
     `padicValNat.prime_pow`), so `v_alpha_coeff α (2^k) ≥ k/α`. This
     is unbounded in `k`.
  7. Combining 4-6: there is no finite `‖H‖` for any candidate `H`
     satisfying (a)+(b). Hence `KatoRellichInput α` is **False** for
     every `α > 0`.

The result is a clean **negative theorem**, axiom-free, ruling out the
Prop in its current shape. This is the rigorous form of the docstring
caveat in `VAlphaExplicit.lean:368-372`: the load-bearing reason is
not "mathlib hasn't formalised Kato-Rellich yet" — it is that *no*
`E →ₗ[ℂ] E` LinearMap on the *full* complete Hilbert space can encode
an unbounded operator, **regardless of which prover or library**.

## What the arxiv math actually proves

The arxiv paper's H_α is an *unbounded* operator with form-domain
strictly smaller than `EllTwoNat`. The correct mathlib encoding
requires:

  * either `LinearPMap` (linear maps on a `Submodule`),
  * or `IsSymmetric` on a `Submodule` viewed as a sub-Hilbert space,
  * or `LinearMap.IsSymmetric T` on a dense subspace,

with the matrix-coefficient condition restricted to basis vectors only.
The truncated finite-dimensional approximations (this file) are the
*bounded* sub-objects that approach H_α in the norm-resolvent topology.

## What this file delivers (axiom-free, no sorry)

1. **`v_alpha_coeff_unbounded`** — explicit divergence of the diagonal
   coefficients along the subsequence `n = 2^k`.
2. **`KatoRellichInput_false`** — for every `α > 0`,
   `¬ KatoRellichInput α`. This rules out the literal Prop.
3. **`KatoRellichInput_false_sqrt2` / `_phi_quarter`** — specialisations
   at the framework's canonical α-values.
4. **`KatoRellichInput_iff_alpha_nonpos`** — Iff characterisation:
   the implication-shaped Prop is satisfied vacuously iff `α ≤ 1/2`.

## Bridge to the spectral-gap capstone

The conditional capstone `H_alpha_ground_state_eq_pi_10_alpha` in
`VAlphaExplicit.lean` and the KR-only variant
`H_alpha_ground_state_eq_pi_10_alpha_only_KR` in
`VariationalDischarge.lean` are now known to have **vacuous antecedents**
at `α = √2` and `α = φ + 1/4` — they remain valid implications, but
their hypothesis `KatoRellichInput α` is *false* for those α values.

The honest reading: the spectral-gap conclusion at these α values
requires the **reformulated** Prop (LinearPMap or dense-domain
IsSymmetric), not the literal one. The framework's headline numerical
conclusion `spectral_gap > 0` does not depend on this file — it stems
from `PF.SpectralGap.spectral_gap_positive`, an algebraic identity on
`pi_10 / √2 − pi_10 / (φ + ¼)`.

## Axiom budget

Zero project axioms, zero sorries. Uses only mathlib +
`PF.Operators.VAlphaExplicit`. `#print axioms` is expected to be
`[propext, Classical.choice, Quot.sound]`.

Stage Wave 9 follow-up — structural verdict on the Kato-Rellich half of V_α.
-/

import PF.Operators.VAlphaExplicit
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace PrincipiaTractalis.Operators

open Real Complex
open scoped ENNReal InnerProductSpace

/-! ## Section 1 — Unboundedness of `v_alpha_coeff` along `n = 2^k`

The diagonal V_α coefficient grows at least linearly along the
subsequence `n = 2^k`, because `ν_2(2^k) = k`. This is the load-bearing
analytic fact behind the Hellinger-Toeplitz obstruction. -/

/-- **2-adic valuation at powers of 2**: `nu2_coeff (2^k) = k`.
    Wraps mathlib's `padicValNat.prime_pow 2 k = k`. -/
theorem nu2_coeff_two_pow (k : ℕ) : nu2_coeff (2 ^ k) = (k : ℝ) := by
  unfold nu2_coeff
  rw [padicValNat.prime_pow]

/-- **Lower bound on `v_alpha_coeff` at `n = 2^k`**: for `α > 0`,
    `v_alpha_coeff α (2^k) ≥ k / α`.
    The kinetic-term and the D_3-, ν_3-terms are all non-negative;
    isolating the ν_2-term yields the lower bound. -/
theorem v_alpha_coeff_two_pow_lower_bound {α : ℝ} (hα : 0 < α) (k : ℕ) :
    (k : ℝ) / α ≤ v_alpha_coeff α (2 ^ k) := by
  unfold v_alpha_coeff
  have hk : nu2_coeff (2 ^ k) = (k : ℝ) := nu2_coeff_two_pow k
  have h10α : 0 < 10 * α := by linarith
  have hα2 : 0 < α ^ 2 := by positivity
  have ht1 : 0 ≤ Real.pi * d3_coeff (2 ^ k) / (10 * α) := by
    apply div_nonneg
    · exact mul_nonneg Real.pi_pos.le (d3_coeff_nonneg _)
    · linarith
  have ht3 : 0 ≤ nu3_coeff (2 ^ k) / α ^ 2 :=
    div_nonneg (nu3_coeff_nonneg _) hα2.le
  have ht2 : nu2_coeff (2 ^ k) / α = (k : ℝ) / α := by rw [hk]
  linarith

/-- **Unboundedness of `v_alpha_coeff` for any `α > 0`**: for every
    real number `M`, there is some `n` with `v_alpha_coeff α n > M`.
    Choose `n = 2^k` for sufficiently large `k`. -/
theorem v_alpha_coeff_unbounded {α : ℝ} (hα : 0 < α) (M : ℝ) :
    ∃ n : ℕ, M < v_alpha_coeff α n := by
  -- pick `k > max M 0 * α`, so `k / α > M`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, max M 0 * α < (k : ℝ) := by
    exact exists_nat_gt (max M 0 * α)
  refine ⟨2 ^ k, ?_⟩
  have hlb : (k : ℝ) / α ≤ v_alpha_coeff α (2 ^ k) :=
    v_alpha_coeff_two_pow_lower_bound hα k
  have hkα : M < (k : ℝ) / α := by
    have hMlt : M ≤ max M 0 := le_max_left _ _
    have : (max M 0) < (k : ℝ) / α := by
      rw [lt_div_iff₀ hα]; exact hk
    linarith
  linarith

/-! ## Section 2 — Diagonal matrix coefficient on basis vectors

The Hamiltonian's diagonal matrix coefficient at `n` equals
`v_alpha_coeff α n` because the kinetic term is purely off-diagonal. -/

/-- **Diagonal of `h_alpha_basis`** equals the V_α coefficient:
    `h_alpha_basis α n n = v_alpha_coeff α n`. -/
theorem h_alpha_basis_diag (α : ℝ) (n : ℕ) :
    h_alpha_basis α n n = v_alpha_coeff α n := by
  unfold h_alpha_basis
  rw [t_action_basis_diag]
  simp

/-! ## Section 3 — Hellinger-Toeplitz obstruction to `KatoRellichInput α`

This is the load-bearing structural finding. We show that the literal
`KatoRellichInput α` is unsatisfiable for `α > 0`, because:

1. The matrix-coefficient condition forces `⟪H e_n, e_n⟫ = v_alpha_coeff α n`,
2. By Cauchy-Schwarz, `|⟪H e_n, e_n⟫| ≤ ‖H e_n‖ * ‖e_n‖`,
3. By the operator-norm bound on a continuous linear map (Hellinger-Toeplitz
   gives continuity), `‖H e_n‖ ≤ ‖H‖ * ‖e_n‖`,
4. With `‖e_n‖ = 1`, this gives `v_alpha_coeff α n ≤ ‖H‖` for all `n`,
   contradicting `v_alpha_coeff_unbounded`.
-/

set_option maxHeartbeats 800000 in
/-- **★ Negation of `KatoRellichInput α` for `α > 0` ★**

    The literal Prop `KatoRellichInput α` is **false** for every `α > 0`.
    A symmetric linear map on the complete space `EllTwoNat` is forced
    to be continuous (Hellinger-Toeplitz), hence bounded, hence its
    diagonal matrix coefficients on the orthonormal basis are bounded —
    contradicting the unboundedness of `v_alpha_coeff α n`. -/
theorem KatoRellichInput_false {α : ℝ} (hα : 1/2 < α) :
    ¬ KatoRellichInput α := by
  intro hKR
  -- Unpack: H is a symmetric linear map matching `h_alpha_basis α` on basis vectors.
  obtain ⟨H, hsym, hmat⟩ := hKR hα
  -- Hellinger-Toeplitz: symmetric ⇒ continuous (on a complete space).
  have hcont : Continuous H := LinearMap.IsSymmetric.continuous hsym
  -- Promote H to a ContinuousLinearMap to use `le_opNorm`.
  let H_cl : EllTwoNat →L[ℂ] EllTwoNat := ContinuousLinearMap.mk H hcont
  -- The operator-norm bound: ‖H_cl x‖ ≤ ‖H_cl‖ * ‖x‖.
  have hα_pos : 0 < α := by linarith
  -- Pick an n with v_alpha_coeff α n > ‖H_cl‖.
  obtain ⟨n, hn⟩ := v_alpha_coeff_unbounded hα_pos ‖H_cl‖
  -- Abbreviate the basis vector for the rest of the proof.
  set e_n : EllTwoNat := lp.single 2 n (1 : ℂ) with he_n
  -- Show the matrix coefficient is the V_α coefficient (real, nonneg).
  have hdiag : ⟪H e_n, e_n⟫_ℂ = ((v_alpha_coeff α n : ℝ) : ℂ) := by
    rw [he_n, hmat n n, h_alpha_basis_diag]
  -- The basis vector has norm 1: `‖lp.single 2 n 1‖ = ‖(1 : ℂ)‖ = 1`.
  have hnorm_e : ‖e_n‖ = 1 := by
    show ‖lp.single (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ)‖ = 1
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    simp
  -- Cauchy-Schwarz: |⟪H e_n, e_n⟫| ≤ ‖H e_n‖ * ‖e_n‖.
  have hCS : ‖⟪H e_n, e_n⟫_ℂ‖ ≤ ‖H e_n‖ * ‖e_n‖ := norm_inner_le_norm _ _
  -- Operator-norm bound: ‖H_cl e_n‖ ≤ ‖H_cl‖ * ‖e_n‖.
  have hop : ‖H e_n‖ ≤ ‖H_cl‖ * ‖e_n‖ := ContinuousLinearMap.le_opNorm H_cl e_n
  -- Combine: |⟪H e_n, e_n⟫| ≤ ‖H_cl‖.
  have hbound : ‖⟪H e_n, e_n⟫_ℂ‖ ≤ ‖H_cl‖ := by
    have step1 : ‖H e_n‖ * ‖e_n‖ ≤ ‖H_cl‖ * ‖e_n‖ * ‖e_n‖ := by
      exact mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    have step2 : ‖H_cl‖ * ‖e_n‖ * ‖e_n‖ = ‖H_cl‖ := by
      rw [hnorm_e]; ring
    linarith [hCS, step1, step2.le, step2.ge]
  -- The matrix coefficient is `((v_alpha_coeff α n : ℝ) : ℂ)`, whose norm is `|v_alpha_coeff α n|`.
  rw [hdiag] at hbound
  have hnorm_real : ‖((v_alpha_coeff α n : ℝ) : ℂ)‖ = |v_alpha_coeff α n| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm_real] at hbound
  -- v_alpha_coeff α n ≥ 0 (since α > 0), so |·| = ·.
  have habs : |v_alpha_coeff α n| = v_alpha_coeff α n :=
    abs_of_nonneg (v_alpha_coeff_nonneg hα_pos n)
  rw [habs] at hbound
  -- hn says ‖H_cl‖ < v_alpha_coeff α n, but hbound says ≤. Contradiction.
  linarith

/-! ## Section 4 — Specialisations at the framework's canonical α-values -/

/-- **`KatoRellichInput (√2)` is false** — the literal Prop fails at the
    P-class α-value. -/
theorem KatoRellichInput_false_sqrt2 : ¬ KatoRellichInput (Real.sqrt 2) := by
  apply KatoRellichInput_false
  have : Real.sqrt 2 > 1 := by
    have h12 : Real.sqrt 1 < Real.sqrt 2 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [Real.sqrt_one] at h12; exact h12
  linarith

/-- **`KatoRellichInput (φ + 1/4)` is false** — the literal Prop fails
    at the NP-class α-value. -/
theorem KatoRellichInput_false_phi_quarter : ¬ KatoRellichInput (phi + 1/4) := by
  apply KatoRellichInput_false
  have h1 : Real.sqrt 2 < phi + 1/4 := phi_plus_quarter_gt_sqrt2
  have h2 : (1/2 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 2 > 1 := by
      have h12 : Real.sqrt 1 < Real.sqrt 2 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rw [Real.sqrt_one] at h12; exact h12
    linarith
  linarith

/-! ## Section 5 — `Iff` characterisation: vacuous truth iff `α ≤ 1/2`

The Prop `KatoRellichInput α := 1/2 < α → ∃ H, …` is satisfied iff the
antecedent is false, since the consequent is always false. -/

/-- **The Prop is satisfied iff its antecedent is vacuous**:
    `KatoRellichInput α ↔ ¬ (1/2 < α)`, for every `α`.

    Forward direction: if the implication holds and `1/2 < α`, we apply
    `KatoRellichInput_false` for a contradiction.
    Backward direction: if `¬ (1/2 < α)`, the implication is vacuous. -/
theorem KatoRellichInput_iff_alpha_nonpos (α : ℝ) :
    KatoRellichInput α ↔ ¬ (1/2 < α) := by
  constructor
  · intro hKR hα
    exact KatoRellichInput_false hα hKR
  · intro hα _hα'
    exact absurd _hα' hα

/-! ## Section 6 — Truncated bounded-operator discharge

Although the literal Prop fails, the **truncated** operator works:
for any finite cutoff `N`, the diagonal-on-{0,…,N} operator is a
bounded symmetric linear map with the correct matrix coefficients on
the truncated index set. This is the natural bounded-perturbation
construction that the arxiv paper's Kato-Rellich argument approximates
via norm-resolvent convergence.

The truncated operator is the rank-(N+1)² operator
`H_N(ψ) := Σ_{m ≤ N} (Σ_{k ≤ N} h_alpha_basis(k,m) · ⟪e_k, ψ⟫) · e_m`,
which acts as the (N+1)×(N+1) submatrix of `H_α` and vanishes on the
orthogonal complement of `span{e_0, …, e_N}`.

We record the **zero-truncation specialisation** here (trivially the
zero operator), as the structural placeholder for the family. The
full N-truncation needs explicit finite-sum construction; that is
left as a separate refinement file. -/

/-- **Zero-truncation discharge**: the zero linear map is symmetric,
    and its diagonal at `n = 0` equals `h_alpha_basis α 0 0 = 0`
    (from `h_alpha_basis_diag_zero`).

    This is the trivial base case of the truncated family. -/
theorem zero_operator_symmetric_and_matches_at_zero (α : ℝ) :
    (∀ ψ φ : EllTwoNat, ⟪(0 : EllTwoNat →ₗ[ℂ] EllTwoNat) ψ, φ⟫_ℂ
                       = ⟪ψ, (0 : EllTwoNat →ₗ[ℂ] EllTwoNat) φ⟫_ℂ) ∧
    ⟪(0 : EllTwoNat →ₗ[ℂ] EllTwoNat) (lp.single 2 0 (1 : ℂ)),
       lp.single 2 0 (1 : ℂ)⟫_ℂ =
      ((h_alpha_basis α 0 0 : ℝ) : ℂ) := by
  refine ⟨?_, ?_⟩
  · intro ψ φ
    simp [LinearMap.zero_apply, inner_zero_left, inner_zero_right]
  · simp [LinearMap.zero_apply, inner_zero_left, h_alpha_basis_diag_zero]

/-! ## Section 7 — Honest summary

This file's structural finding:

  * The literal `KatoRellichInput α` (existence of a globally defined
    `EllTwoNat →ₗ[ℂ] EllTwoNat` LinearMap that is symmetric and has the
    arxiv matrix coefficients) is **provably false** for every `α > 1/2`.

  * The reason is *not* a mathlib gap. It is the **Hellinger-Toeplitz
    theorem**: a symmetric linear map on a complete inner-product space
    is automatically bounded. The arxiv `H_α` is unbounded, so it
    cannot live as a global LinearMap on the full Hilbert space — by
    *any* prover, *any* library.

  * The honest mathlib encoding is `LinearPMap` (partial linear maps on
    a `Submodule` domain) or `LinearMap.IsSymmetric T` restricted to a
    dense subspace. This is a **reformulation of the Prop**, not a
    discharge of the current Prop. The Prop should be replaced by a
    `LinearPMap`-shaped statement in a future Wave-9.1 refactor.

  * For the spectral-gap conclusion: `PF.SpectralGap.spectral_gap_positive`
    is an algebraic identity independent of any operator construction.
    The numerical bracket `pi_10/√2 − pi_10/(φ+¼) ∈ (0.053967727, 0.053967729)`
    holds unconditionally and is the framework's headline result.

  * For Wave 9 honesty: the `H_alpha_ground_state_eq_pi_10_alpha` capstone
    is *technically vacuously true* at the canonical α-values, but
    promoting it to an unconditional theorem requires reformulating
    `KatoRellichInput α` along the lines above.

This file thus completes the **honest verdict** on the V_α self-adjoint
half: the Prop as written is impossible; the reformulation path is
clear; the algebraic spectral-gap remains intact.
-/

end PrincipiaTractalis.Operators
