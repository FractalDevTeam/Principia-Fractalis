/-
# Fujita-Kato 1964 — Leray Image is Fourier-Divergence-Free

★ 2026-06-10 — Bridge brick: the WHOLE POINT of the Leray
projector at the frequency level is that its image lands in the
divergence-free subspace. This file proves it.

For any vector Schwartz field `u : ℝ³ → ℂ³`, the frequency-domain
Leray image

  `lerayProjectFreq u : R3 → C3`

is **Fourier-divergence-free** in the genuine Hermitian sense of
`FourierDivFree.lean`:

  `∀ ξ ≠ 0,   ⟨complexifyVec ξ, lerayProjectFreq u ξ⟩_ℂ = 0`.

This is the literal divergence-free condition at the Fourier
symbol level — the frequency-domain encoding of `div(P u) = 0`.

The proof rests on two ingredients:

  (A) The complex inner-product self-pairing identity
      `⟨complexifyVec ξ, complexifyVec ξ⟩_ℂ = ((‖ξ‖² : ℝ) : ℂ)`,
      proved from `inner_self_eq_norm_sq_to_K` plus the
      componentwise norm-preservation
      `‖complexifyVec ξ‖² = ‖ξ‖²`.

  (B) The pointwise perpendicularity of the complex Leray symbol
      `⟨complexifyVec ξ, lerayFourierSymbolC ξ w⟩_ℂ = 0` for
      `ξ ≠ 0`, obtained by unfolding the symbol's `ξ ≠ 0` branch,
      applying `inner_sub_right` + `inner_smul_right`, and
      cancelling via (A) using `((‖ξ‖² : ℝ) : ℂ) ≠ 0`.

Bricks landed here:

  §1 — Complex inner-product self-pairing on `complexifyVec`.
  §2 — Pointwise perpendicularity of `lerayFourierSymbolC`.
  §3 — Bridge: `lerayProjectFreq u` is `IsFourierDivFree`.
  §4 — Zero-input consequence.
  §5 — Capstone bundling §3 + §4.
  §6 — `#print axioms` audit (kernel-only).

Axiom-free; depends only on `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.FourierDivFree
import PF.NavierStokes.FujitaKato1964.LerayProjectorOperator

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.LerayImageIsDivFree

open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 C3 VectorSchwartz3C)
open PF.NavierStokes.FujitaKato1964.LerayProjectorOperator
  (complexifyVec lerayFourierSymbolC lerayProjectFreq
   lerayFourierSymbolC_zero_field lerayProjectFreq_zero)
open PF.NavierStokes.FujitaKato1964.FourierDivFree
  (IsFourierDivFree isFourierDivFree_zero)

/-! ## §1 — Complex inner-product self-pairing on `complexifyVec` -/

/-- **Squared norm of the complexified frequency vector equals the
squared norm of the real frequency vector.** Both sides expand to
`∑ i, (ξ i)²` via `EuclideanSpace.norm_sq_eq`, and the componentwise
identity `‖((ξ i : ℝ) : ℂ)‖ = |ξ i|` (i.e. `Complex.norm_ofReal`)
followed by `sq_abs` collapses the complex sum onto the real one. -/
theorem complexifyVec_norm_sq (ξ : R3) :
    ‖complexifyVec ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro i _
  -- complexifyVec ξ i = ((ξ i : ℝ) : ℂ); take its complex norm
  -- and use `Complex.norm_real` then `sq_abs`.
  show ‖(complexifyVec ξ) i‖ ^ 2 = ‖ξ i‖ ^ 2
  -- `complexifyVec ξ i` reduces to `((ξ i : ℝ) : ℂ)` by `toLp_apply`
  have hcoord : (complexifyVec ξ) i = ((ξ i : ℝ) : ℂ) := rfl
  rw [hcoord]
  rw [Complex.norm_real]

/-- **★ Complex Hermitian self-pairing of the complexified
frequency vector.**

  `⟨complexifyVec ξ, complexifyVec ξ⟩_ℂ = ((‖ξ‖² : ℝ) : ℂ)`.

This is the complex-codomain analogue of `‖ξ‖² = ⟨ξ, ξ⟩` for the
real frequency vector. The proof goes through
`inner_self_eq_norm_sq_to_K`, which gives
`⟨v, v⟩ = ((‖v‖ : ℂ))²` for any vector `v ∈ C3`, then specialises
to `v = complexifyVec ξ` and uses §1's
`complexifyVec_norm_sq`. -/
theorem complexifyVec_inner_self (ξ : R3) :
    inner ℂ (complexifyVec ξ) (complexifyVec ξ)
      = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  -- `inner_self_eq_norm_sq_to_K : ⟪v, v⟫ = ((‖v‖ : 𝕜))²`
  rw [inner_self_eq_norm_sq_to_K]
  -- Goal: ((‖complexifyVec ξ‖ : ℂ))² = ((‖ξ‖² : ℝ) : ℂ)
  -- Push the RHS cast inside via `Complex.ofReal_pow` so that both
  -- sides have the shape `((·: ℝ) : ℂ) ^ 2`.
  rw [Complex.ofReal_pow]
  -- Goal: ((‖complexifyVec ξ‖ : ℂ)) ^ 2 = ((‖ξ‖ : ℝ) : ℂ) ^ 2
  -- Reduce to ‖complexifyVec ξ‖ = ‖ξ‖ via `congr` + norm-square
  -- bijection on ℝ≥0.
  have h : ‖complexifyVec ξ‖ ^ 2 = ‖ξ‖ ^ 2 := complexifyVec_norm_sq ξ
  have h_nn₁ : (0 : ℝ) ≤ ‖complexifyVec ξ‖ := norm_nonneg _
  have h_nn₂ : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have h_norm : ‖complexifyVec ξ‖ = ‖ξ‖ :=
    (pow_left_inj₀ h_nn₁ h_nn₂ (by norm_num : (2 : ℕ) ≠ 0)).mp h
  rw [h_norm]
  rfl

/-! ## §2 — Pointwise perpendicularity of `lerayFourierSymbolC` -/

/-- **★ Complex Leray symbol kills the parallel-to-ξ component.**

For any `ξ ≠ 0` and any `w ∈ C3`,

  `⟨complexifyVec ξ, lerayFourierSymbolC ξ w⟩_ℂ = 0`.

Computationally: unfold the `ξ ≠ 0` branch of `lerayFourierSymbolC`,
expand the inner product against the difference using
`inner_sub_right` + `inner_smul_right`, then cancel via
`complexifyVec_inner_self`. The cancellation requires the divisor
`((‖ξ‖² : ℝ) : ℂ)` to be nonzero, which follows from `ξ ≠ 0`. -/
theorem lerayFourierSymbolC_inner_eq_zero
    (ξ : R3) (hξ : ξ ≠ 0) (w : C3) :
    inner ℂ (complexifyVec ξ) (lerayFourierSymbolC ξ w) = 0 := by
  -- Unfold the symbol on the ξ ≠ 0 branch
  unfold lerayFourierSymbolC
  rw [if_neg hξ]
  -- Goal:
  --   ⟨complexifyVec ξ,
  --      w - (⟨complexifyVec ξ, w⟩ / ((‖ξ‖² : ℝ) : ℂ)) • complexifyVec ξ⟩
  --     = 0
  rw [inner_sub_right, inner_smul_right]
  -- Goal:
  --   ⟨complexifyVec ξ, w⟩
  --   - (⟨complexifyVec ξ, w⟩ / ((‖ξ‖² : ℝ) : ℂ))
  --     * ⟨complexifyVec ξ, complexifyVec ξ⟩
  --   = 0
  rw [complexifyVec_inner_self]
  -- The divisor is nonzero because ξ ≠ 0
  have hξ_ne : (‖ξ‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hξsq_ne : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h2 : (‖ξ‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hξ_ne
    exact_mod_cast h2
  field_simp
  ring

/-! ## §3 — Bridge: `lerayProjectFreq u` is Fourier-divergence-free -/

/-- **★★★ THE HEADLINE THEOREM ★★★**

For any vector Schwartz field `u : ℝ³ → ℂ³`, the frequency-domain
Leray image `lerayProjectFreq u : R3 → C3` is Fourier-divergence-
free:

  `∀ ξ ≠ 0,   ⟨complexifyVec ξ, lerayProjectFreq u ξ⟩_ℂ = 0`.

This is the literal Fourier-side encoding of `div (P u) = 0`. The
Leray projector EARNS its name here: its image is the
divergence-free part of the input field, at every nonzero
frequency.

Proof: unfold `lerayProjectFreq u ξ = lerayFourierSymbolC ξ (û ξ)`
and apply §2's `lerayFourierSymbolC_inner_eq_zero` to the
particular complex vector `w := (fourierTransformCLM ℂ u) ξ`. -/
theorem lerayProjectFreq_isFourierDivFree (u : VectorSchwartz3C) :
    IsFourierDivFree (lerayProjectFreq u) := by
  intro ξ hξ
  unfold lerayProjectFreq
  exact lerayFourierSymbolC_inner_eq_zero ξ hξ _

/-! ## §4 — Zero-input consequence -/

/-- **The Leray image of the zero field IS Fourier-divergence-free
via the zero-field route.** Independent re-derivation of
`IsFourierDivFree (lerayProjectFreq 0)`: the zero field's Leray
image is identically zero (`lerayProjectFreq_zero`), and the zero
field is trivially divergence-free (`isFourierDivFree_zero`). This
is a sanity check on the bridge: §3 also proves it, but the route
via §4 does not invoke §2. -/
theorem lerayProjectFreq_zero_isFourierDivFree :
    IsFourierDivFree (lerayProjectFreq (0 : VectorSchwartz3C)) := by
  intro ξ hξ
  rw [lerayProjectFreq_zero ξ]
  exact inner_zero_right _

/-! ## §5 — Capstone -/

/-- **★★★ Leray-image-is-divergence-free brick capstone ★★★**

Bundles the headline bridge result with the zero-input sanity
check:

  (a) **HEADLINE**: For every vector Schwartz field `u`, the
      frequency-domain Leray image `lerayProjectFreq u` satisfies
      `IsFourierDivFree`. This is the whole point of the Leray
      projector — it lands in the divergence-free subspace.

  (b) **Specialisation**: The Leray image of the zero field is
      divergence-free (a special case of (a), but provable
      independently via `lerayProjectFreq_zero` +
      `isFourierDivFree_zero`).

Together: the frequency-domain Leray projector is a well-defined
map into the Fourier-divergence-free subspace.

Axiom-free: `[propext, Classical.choice, Quot.sound]` only. -/
theorem leray_image_is_div_free_brick_capstone :
    -- (a) HEADLINE bridge
    (∀ u : VectorSchwartz3C,
       IsFourierDivFree (lerayProjectFreq u)) ∧
    -- (b) Zero-input specialisation
    IsFourierDivFree (lerayProjectFreq (0 : VectorSchwartz3C)) :=
  ⟨lerayProjectFreq_isFourierDivFree,
   lerayProjectFreq_zero_isFourierDivFree⟩

/-! ## §6 — Axiom audit -/

#print axioms complexifyVec_norm_sq
#print axioms complexifyVec_inner_self
#print axioms lerayFourierSymbolC_inner_eq_zero
#print axioms lerayProjectFreq_isFourierDivFree
#print axioms lerayProjectFreq_zero_isFourierDivFree
#print axioms leray_image_is_div_free_brick_capstone

end PF.NavierStokes.FujitaKato1964.LerayImageIsDivFree
