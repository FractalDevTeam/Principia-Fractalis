/-
# r365: `exp(-βH)` is a positive-definite weight — step 3 of the dynamics gate

★ 2026-10-28 r365 — the Gibbs state exists at every inverse temperature ★

## What this adds, and the lemma mathlib does not have

r364 proved that a **positive-definite** weight gives a state satisfying the
KMS identity. The physical weight is `exp(-βH)` for Hermitian `H`, with `β` the
inverse temperature. To connect the two, one needs:

> `H` Hermitian ⟹ `exp H` is positive definite.

**That lemma is absent from mathlib.** Measured at this pin: `Matrix.IsHermitian.exp`
gives only `(exp 𝕂 A).IsHermitian`, and a search for `PosDef` of an exponential
returns nothing. So it is proved here, as `posDef_exp_of_isHermitian`.

The proof avoids the spectral theorem entirely, which is what makes it cheap:

* `exp A = (exp(A/2))^2` by `Matrix.exp_nsmul`, since `2 • (A/2) = A`;
* `exp(A/2)` is **Hermitian** when `A` is (`Matrix.IsHermitian.exp`), so that
  square is `Sᴴ * S` with `S = exp(A/2)`, hence positive **semi**definite by
  `posSemidef_conjTranspose_mul_self`;
* `exp` of a matrix is always a **unit** (`Matrix.isUnit_exp`);
* positive semidefinite + unit = positive definite
  (`PosSemidef.posDef_iff_isUnit`).

Halving is the whole trick: it turns "exponential of a Hermitian" into "`Sᴴ S`"
without ever diagonalising anything. This lemma looks like a reasonable mathlib
candidate on its own.

One practical note for anyone extending this file. The general
`NormedSpace.exp_add_of_commute` is **not** directly usable on matrices: it
needs `NormedRing`/`NormedAlgebra`/`CompleteSpace` on the matrix type, and
mathlib deliberately keeps those behind *scoped* instances because no matrix
norm is canonical (`Matrix.normedAddCommGroup`, `frobenius…`, `linftyOp…` are
all defensible). mathlib's own matrix lemmas are proved with
`open scoped Norms.Operator in …`. The clean route — taken here — is to use the
**matrix-namespace** versions (`Matrix.exp_nsmul`, `Matrix.exp_add_of_commute`,
`Matrix.isUnit_exp`), which carry the instance choice internally. Note that
`Matrix.exp_add_of_commute` takes its two matrices **explicitly**, and that
having both `Matrix` and `NormedSpace` open makes the bare name ambiguous.

## The payoff

`gibbsWeight β H = exp(-βH)` is positive definite for every real `β` and every
Hermitian `H`, so by r364 it carries a genuine state, and by r363 that state
satisfies the KMS identity against its own modular automorphism:

* `gibbsWeight_posDef` — the weight is positive definite;
* **`gibbsWeight_kms_state`** — unital, positive, and KMS, at **every** inverse
  temperature `β`.

This is the first point in the build where `β` means inverse temperature and
the object is physics rather than algebra. Note what it does **not** need: no
restriction on `β`, no positivity of `H`, no trace condition. Any Hermitian
generator gives a KMS state at every temperature, at finite level.

## What is NOT claimed

Not claimed here: the real-time one-parameter group `α_t(a) = e^{itH} a e^{-itH}`,
the identification of the modular automorphism with imaginary-time evolution
`α_{iβ}`, strong continuity, analytic elements, the strip boundary condition,
anything about `T_∞`, or any tower limit. Those are step 4 onward; this file
stops where the weight is shown to be positive definite so that the exponential
facts and the dynamics facts stay in separate files.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.KMS.GibbsStateFiniteLevel_r364
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

set_option autoImplicit false

namespace PF.KMS

open Matrix
open NormedSpace -- for `exp`
open scoped ComplexOrder

variable {n : ℕ}

/-! ## §1 — The exponential of a Hermitian matrix is positive definite

Absent from mathlib at this pin; proved here without the spectral theorem. -/

/-- A real multiple of a Hermitian matrix is Hermitian. -/
lemma isHermitian_real_smul {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (r : ℝ) : (r • A).IsHermitian := by
  show (r • A)ᴴ = r • A
  rw [Matrix.conjTranspose_smul, star_trivial, hA.eq]

/-- **★★★ r365: `H` Hermitian ⟹ `exp H` positive definite ★★★**

Proved by halving: `exp H = Sᴴ S` with `S = exp(H/2)` Hermitian, so `exp H` is
positive semidefinite, and it is a unit because `exp H * exp(-H) = 1`. -/
theorem posDef_exp_of_isHermitian {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) : (exp ℂ A).PosDef := by
  -- the half, and that it is Hermitian
  have hhalf : (((2:ℝ)⁻¹) • A).IsHermitian := isHermitian_real_smul hA _
  have hS : (exp ℂ (((2:ℝ)⁻¹) • A)).IsHermitian := hhalf.exp (𝕂 := ℂ)
  have h2 : (2 : ℕ) • (((2:ℝ)⁻¹) • A) = A := by
    rw [two_nsmul, ← add_smul]
    norm_num
  -- exp A = Sᴴ * S, via `exp A = (exp (A/2))^2`
  have hsplit : exp ℂ A
      = (exp ℂ (((2:ℝ)⁻¹) • A))ᴴ * exp ℂ (((2:ℝ)⁻¹) • A) := by
    rw [hS.eq, ← pow_two, ← Matrix.exp_nsmul, h2]
  have hpsd : (exp ℂ A).PosSemidef := by
    rw [hsplit]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  -- `exp` of a matrix is always a unit
  exact (hpsd.posDef_iff_isUnit).mpr (Matrix.isUnit_exp ℂ A)

/-! ## §2 — The Gibbs weight at inverse temperature β -/

/-- `exp(-βH)`, the Gibbs weight at inverse temperature `β`. -/
noncomputable def gibbsWeight (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  exp ℂ ((-β) • H)

/-- The Gibbs weight is positive definite, for every real `β` and every
Hermitian generator. -/
theorem gibbsWeight_posDef (β : ℝ) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) : (gibbsWeight β H).PosDef :=
  posDef_exp_of_isHermitian (isHermitian_real_smul hH (-β))

/-! ## §3 — The Gibbs state, at every temperature -/

/-- **★★★ r365: the finite-level Gibbs KMS state ★★★**

For any Hermitian generator `H` and any inverse temperature `β`, the functional
`ω(a) = Tr(exp(-βH) a)/Tr(exp(-βH))` is unital, positive, and satisfies the KMS
identity against the modular automorphism of its own weight.

No condition on `β`, none on `H` beyond Hermitian. -/
theorem gibbsWeight_kms_state [Nonempty (Fin n)] (β : ℝ)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) :
    gibbsFunctional (gibbsWeight β H) 1 = 1
    ∧ (∀ a : Matrix (Fin n) (Fin n) ℂ,
        0 ≤ gibbsFunctional (gibbsWeight β H) (aᴴ * a))
    ∧ (∀ a b : Matrix (Fin n) (Fin n) ℂ,
        gibbsFunctional (gibbsWeight β H) (a * b)
          = gibbsFunctional (gibbsWeight β H)
              (b * modularAut (gibbsWeight β H) a)) :=
  gibbs_kms_state (gibbsWeight_posDef β hH)

/-- The infinite-temperature degeneration: at `β = 0` the weight is `1`, whose
modular automorphism is the identity by r363 — so the `β → 0` end of the family
is exactly the tracial case that supplies no dynamics. -/
theorem gibbsWeight_zero (H : Matrix (Fin n) (Fin n) ℂ) :
    gibbsWeight 0 H = 1 := by
  rw [gibbsWeight, neg_zero, zero_smul, exp_zero]

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.isHermitian_real_smul
#print axioms PF.KMS.posDef_exp_of_isHermitian
#print axioms PF.KMS.gibbsWeight_posDef
#print axioms PF.KMS.gibbsWeight_kms_state
#print axioms PF.KMS.gibbsWeight_zero
