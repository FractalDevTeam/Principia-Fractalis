/-
# r364: a positive-definite weight gives a STATE — step 2 of the dynamics gate

★ 2026-10-28 r364 — the Gibbs functional is positive and unital ★

## What this adds to r363

r363 proved the KMS identity `ω_X(a b) = ω_X(b · σ_X(a))` under the single
hypothesis `IsUnit X.det`. That is the pure algebra: nothing there says `ω_X`
is a **state**, and r363's header recorded that positivity was deliberately
deferred so nothing was smuggled in.

This file supplies it. For a **positive-definite** weight `X`:

* `posDef_isUnit_det` — `PosDef X` gives `IsUnit X.det`, so every result of
  r363 applies to a positive-definite weight without further hypotheses;
* `gibbs_unital` — `ω_X(1) = 1`;
* `gibbs_numerator_nonneg` — `0 ≤ Tr(X aᴴ a)`;
* `gibbs_denominator_pos` — `0 < Tr(X)`;
* **`gibbs_nonneg`** — `0 ≤ ω_X(aᴴ a)`.

Unital and positive is what "state" means, so with r363's identity the pair
(`σ_X`, `ω_X`) is a genuine modular-automorphism/KMS-state pair at finite
level. Positive-definiteness is exactly the property `exp(-βH)` has for
Hermitian `H`, which is why this is the right hypothesis to carry rather than
invertibility alone.

Ordering note: `0 ≤ z` and `0 < z` are taken in `ComplexOrder`, where they mean
"`z` is a real number, and it is nonnegative / positive". `open scoped
ComplexOrder` does not cross an import, so it is repeated here — the same thing
that cost a build cycle in r362.

## What is NOT claimed

Still not claimed: the general KMS condition, a one-parameter automorphism
group, strong continuity, analytic elements, the strip boundary condition,
anything about `T_∞` itself, any tower limit, or `X = exp(-βH)`. The matrix
exponential is step 3; this file stops at "positive-definite weights give
states" so that the exponential's own facts are not mixed into the proof.

`Nonempty (Fin n)` is required and real: at `n = 0` the matrix algebra is
trivial, `Tr(X) = 0`, and the normalisation is undefined. Every substrate level
`M_{3^k}` has `3^k ≥ 1`, so the hypothesis always holds where it is used.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.KMS.ModularAutomorphismFiniteLevel_r363
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false

namespace PF.KMS

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-! ## §1 — A positive-definite weight satisfies r363's hypothesis -/

/-- `PosDef X` gives `IsUnit X.det`, so all of r363 applies. -/
lemma posDef_isUnit_det {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosDef) :
    IsUnit X.det :=
  (isUnit_iff_ne_zero).mpr (ne_of_gt hX.det_pos)

/-! ## §2 — Unitality -/

/-- `0 < Tr(X)` for a positive-definite weight on a nonempty index. -/
lemma gibbs_denominator_pos [Nonempty (Fin n)]
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosDef) :
    0 < X.trace :=
  hX.trace_pos

/-- `ω_X(1) = 1`: the Gibbs functional is unital. -/
theorem gibbs_unital [Nonempty (Fin n)]
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosDef) :
    gibbsFunctional X 1 = 1 := by
  have h : X.trace ≠ 0 := ne_of_gt (gibbs_denominator_pos hX)
  simp only [gibbsFunctional, mul_one]
  exact div_self h

/-! ## §3 — Positivity

`Tr(X aᴴ a) = Tr(a X aᴴ)` by cyclicity, and `a X aᴴ` is positive semidefinite
because `X` is. So the numerator is a nonnegative real. -/

/-- `0 ≤ Tr(X aᴴ a)`. -/
theorem gibbs_numerator_nonneg {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosDef)
    (a : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ (X * (aᴴ * a)).trace := by
  -- `a X aᴴ` is positive semidefinite
  have hpsd : (a * X * aᴴ).PosSemidef := by
    have := hX.posSemidef.conjTranspose_mul_mul_same (B := aᴴ)
    simpa [conjTranspose_conjTranspose] using this
  have htr : (0 : ℂ) ≤ (a * X * aᴴ).trace := hpsd.trace_nonneg
  -- and its trace is the numerator, by cyclicity
  have hcyc : (a * X * aᴴ).trace = (X * (aᴴ * a)).trace := by
    calc (a * X * aᴴ).trace
        = (aᴴ * (a * X)).trace := Matrix.trace_mul_comm (a * X) aᴴ
      _ = (X * (aᴴ * a)).trace := by
            have e : aᴴ * (a * X) = (aᴴ * a) * X := by noncomm_ring
            rw [e, Matrix.trace_mul_comm]
  rwa [hcyc] at htr

/-- A nonnegative real divided by a positive real is a nonnegative real,
stated in `ComplexOrder`. -/
private lemma complex_div_nonneg {p q : ℂ} (hp : 0 ≤ p) (hq : 0 < q) :
    0 ≤ p / q := by
  obtain ⟨hpr, hpi⟩ := Complex.le_def.mp hp
  obtain ⟨hqr, hqi⟩ := Complex.lt_def.mp hq
  simp only [Complex.zero_re, Complex.zero_im] at hpr hpi hqr hqi
  have hpe : p = (p.re : ℂ) := Complex.ext rfl (by simp [hpi.symm])
  have hqe : q = (q.re : ℂ) := Complex.ext rfl (by simp [hqi.symm])
  rw [hpe, hqe, ← Complex.ofReal_div]
  exact Complex.zero_le_real.mpr (div_nonneg hpr hqr.le)

/-- **★★★ r364: the Gibbs functional is positive ★★★**

`0 ≤ ω_X(aᴴ a)`. With `gibbs_unital`, `ω_X` is a state. -/
theorem gibbs_nonneg [Nonempty (Fin n)]
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosDef)
    (a : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ gibbsFunctional X (aᴴ * a) :=
  complex_div_nonneg (gibbs_numerator_nonneg hX a) (gibbs_denominator_pos hX)

/-! ## §4 — The pair, assembled

With r363's identity and the two properties above, a positive-definite weight
gives a unital positive functional satisfying the modular condition. -/

/-- **The finite-level KMS pair.** For a positive-definite weight: `ω_X` is
unital, positive, and satisfies the KMS identity against `σ_X`. -/
theorem gibbs_kms_state [Nonempty (Fin n)]
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosDef) :
    gibbsFunctional X 1 = 1
    ∧ (∀ a : Matrix (Fin n) (Fin n) ℂ, 0 ≤ gibbsFunctional X (aᴴ * a))
    ∧ (∀ a b : Matrix (Fin n) (Fin n) ℂ,
        gibbsFunctional X (a * b)
          = gibbsFunctional X (b * modularAut X a)) :=
  ⟨gibbs_unital hX, fun a => gibbs_nonneg hX a,
   fun a b => gibbs_kms X (posDef_isUnit_det hX) a b⟩

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.posDef_isUnit_det
#print axioms PF.KMS.gibbs_denominator_pos
#print axioms PF.KMS.gibbs_unital
#print axioms PF.KMS.gibbs_numerator_nonneg
#print axioms PF.KMS.gibbs_nonneg
#print axioms PF.KMS.gibbs_kms_state
