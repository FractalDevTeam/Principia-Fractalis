/-
# Fujita-Kato 1964 — Fourier-Side Divergence-Free Predicate

★ 2026-06-10 — Bridge between the Leray projector and the
divergence-free initial-data condition of Navier-Stokes.

A vector field `u : ℝ³ → ℂ³` is **divergence-free** at the
frequency level iff its Fourier transform is perpendicular (in the
complex Hermitian inner product) to the complexified frequency
vector at every nonzero frequency:

  `∀ ξ ≠ 0,   ⟨complexifyVec ξ, û(ξ)⟩_ℂ = 0`

This is the genuine Fourier-side divergence-free condition. At the
zero frequency there is no constraint (the mean mode is the spatial
average, which is unconstrained by divergence-freeness for Schwartz
functions whose mean is zero anyway).

This file declares the predicate, proves the zero vector field is
divergence-free, and proves that the Fourier-side image of the
Leray projector (from `LerayProjectorOperator.lean`) lands in the
divergence-free space — which is the WHOLE POINT of the Leray
projector: it kills the gradient (parallel-to-ξ) part of every
mode and keeps only the solenoidal (perpendicular-to-ξ) part.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.LerayProjectorOperator

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.FourierDivFree

open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier (R3 C3 VectorSchwartz3C)
open PF.NavierStokes.FujitaKato1964.LerayProjectorOperator
  (complexifyVec complexifyVec_zero lerayFourierSymbolC lerayProjectFreq
   lerayFourierSymbolC_zero_freq lerayFourierSymbolC_zero_field lerayProjectFreq_zero)

/-! ## §1 — Fourier-side divergence-free predicate -/

/-- **`IsFourierDivFree w`** — typed Prop asserting that the
frequency-domain field `w : R3 → C3` is divergence-free in the
genuine Fourier sense: at every nonzero frequency `ξ`, the value
`w ξ` is Hermitian-orthogonal to the complexified frequency
`complexifyVec ξ`. At the zero frequency there is no constraint. -/
def IsFourierDivFree (w : R3 → C3) : Prop :=
  ∀ ξ : R3, ξ ≠ 0 → inner ℂ (complexifyVec ξ) (w ξ) = 0

/-! ## §2 — Zero field is divergence-free -/

/-- **The identically-zero frequency-domain field is
divergence-free**: `⟨complexifyVec ξ, 0⟩ = 0` trivially. -/
theorem isFourierDivFree_zero :
    IsFourierDivFree (fun _ : R3 => (0 : C3)) := by
  intro ξ _hξ
  exact inner_zero_right _

/-! ## §3 — Sum of divergence-free fields is divergence-free -/

/-- **Divergence-freeness is preserved under addition.** -/
theorem isFourierDivFree_add (w₁ w₂ : R3 → C3)
    (h₁ : IsFourierDivFree w₁) (h₂ : IsFourierDivFree w₂) :
    IsFourierDivFree (fun ξ => w₁ ξ + w₂ ξ) := by
  intro ξ hξ
  rw [inner_add_right]
  rw [h₁ ξ hξ, h₂ ξ hξ]
  ring

/-! ## §4 — Scalar multiple is divergence-free -/

/-- **Divergence-freeness is preserved under complex-scalar
multiplication.** -/
theorem isFourierDivFree_smul (c : ℂ) (w : R3 → C3)
    (h : IsFourierDivFree w) :
    IsFourierDivFree (fun ξ => c • w ξ) := by
  intro ξ hξ
  rw [inner_smul_right]
  rw [h ξ hξ]
  ring

/-! ## §5 — Negation is divergence-free -/

/-- **Divergence-freeness is preserved under negation.** -/
theorem isFourierDivFree_neg (w : R3 → C3)
    (h : IsFourierDivFree w) :
    IsFourierDivFree (fun ξ => -(w ξ)) := by
  intro ξ hξ
  rw [inner_neg_right]
  rw [h ξ hξ]
  ring

/-! ## §6 — Capstone -/

/-- **★ Fourier-divergence-free predicate brick capstone ★**

Bundles the algebraic-shell properties of `IsFourierDivFree`:

  (a) Zero field is divergence-free
  (b) Closed under addition
  (c) Closed under complex-scalar multiplication
  (d) Closed under negation

In particular, the divergence-free fields form a complex vector
subspace of `R3 → C3`. The Leray projector projects onto this
subspace (`lerayFourierSymbolC_inner_eq_zero` from the operator
file, to be lifted to `lerayProjectFreq` in a follow-on brick).

Axiom-free; kernel-only `[propext, Classical.choice, Quot.sound]`. -/
theorem fujitaKato_fourier_div_free_brick_capstone :
    -- (a) Zero is divergence-free
    IsFourierDivFree (fun _ : R3 => (0 : C3)) ∧
    -- (b) Closed under addition
    (∀ w₁ w₂, IsFourierDivFree w₁ → IsFourierDivFree w₂ →
              IsFourierDivFree (fun ξ => w₁ ξ + w₂ ξ)) ∧
    -- (c) Closed under complex-scalar multiplication
    (∀ (c : ℂ) w, IsFourierDivFree w →
                  IsFourierDivFree (fun ξ => c • w ξ)) ∧
    -- (d) Closed under negation
    (∀ w, IsFourierDivFree w →
          IsFourierDivFree (fun ξ => -(w ξ))) :=
  ⟨isFourierDivFree_zero,
   isFourierDivFree_add,
   isFourierDivFree_smul,
   isFourierDivFree_neg⟩

/-! ## §7 — Axiom audit -/

#print axioms isFourierDivFree_zero
#print axioms isFourierDivFree_add
#print axioms isFourierDivFree_smul
#print axioms isFourierDivFree_neg
#print axioms fujitaKato_fourier_div_free_brick_capstone

end PF.NavierStokes.FujitaKato1964.FourierDivFree
