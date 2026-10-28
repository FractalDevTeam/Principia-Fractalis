/-
# r363: the KMS identity at finite level — step 1 of the dynamics gate

★ 2026-10-28 r363 — the first file of the KMS build ★

## Why this file exists, and why it starts here

`codex/TOE_GATE_PRICED_2026-10-28.md` prices gate (A) of
`THE_MAP_2026-10-11.md` §5: deriving the substrate→observable dictionary needs
**a dynamics / KMS state on `T_∞`**, and that was measured at **0 files in PF
and 0 files in mathlib** — no KMS states, no Tomita–Takesaki modular
automorphism group, no one-parameter automorphism group of a C\*-algebra. The
gap is in the formal library, so the library has to be built.

This is the first brick, and it is deliberately the **finite-dimensional**
case, for a structural reason rather than convenience:

> `T_∞` is the inductive limit of the matrix tower `M_{3^k}`
> (`SubstrateDirectLimit.lean:176`), and r359 proves every element already
> lives at some finite level. So **every level of the substrate is a matrix
> algebra**, and a product-type dynamics on `T_∞` is assembled from
> level-wise data. The finite level is not a toy here; it is the building
> block.

In finite dimensions the whole analytic apparatus of the KMS condition —
strong continuity, entire analytic elements, analytic continuation to the strip
— is **unnecessary**: imaginary-time evolution is conjugation by a matrix, and
the KMS identity is trace cyclicity. That is why this brick is cheap and the
general case is not.

## What is proved

For an invertible weight `X`, with `σ_X(a) = X a X⁻¹` and
`ω_X(a) = Tr(X a)/Tr(X)`:

* `modularAut_mul`, `modularAut_one` — `σ_X` is a unital multiplicative map,
  i.e. the conjugation really is an algebra automorphism, not just a function;
* **`gibbs_kms`** — the KMS identity `ω_X(a b) = ω_X(b · σ_X(a))`. This is the
  finite-level, imaginary-time form of the modular condition;
* **`modularAut_of_scalar`** and **`gibbs_tracial_of_scalar`** — if `X` is a
  scalar `c • 1`, then `σ_X = id` and `ω_X` is **tracial**: `ω(ab) = ω(ba)`.

That last pair is the point of contact with the TOE gate. `THE MAP` §0 asserts,
in prose, that *"the modular group of a trace is trivial. Time evolution is NOT
determined by (A, τ)."* `modularAut_of_scalar` is that statement proved at
finite level: the tracial weight generates the **identity** automorphism, so a
trace supplies no dynamics. A dynamics requires a **non-scalar** weight, and
then `ω_X` is no longer tracial — which is exactly why the substrate's *unique*
tracial state cannot be the state a dictionary derivation runs through.

## What is NOT claimed

This is **not** the KMS condition in its general form. Not claimed here:
a one-parameter automorphism group, strong continuity, analytic elements,
the strip boundary condition, any statement about `T_∞` itself, any infinite
tower limit, positivity of `ω_X`, or that `ω_X` is a state. `IsUnit X.det` is
the only hypothesis; positive-definiteness of the weight (which is what makes
`ω_X` a state, and what `exp(-βH)` supplies) is deliberately deferred so that
this file's content is the pure algebraic identity and nothing is smuggled in.

Gate (A) is not advanced by one file. This is step 1 of a long build, recorded
as such.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

namespace PF.KMS

open Matrix

variable {n : ℕ}

/-! ## §1 — The modular automorphism of a weight

Conjugation by `X`. In the physical case `X = exp(-βH)` this is evolution by
imaginary time `iβ`; here `X` is an arbitrary invertible weight, so the content
is algebraic. -/

/-- `σ_X(a) = X a X⁻¹`, the modular automorphism of the weight `X`. -/
noncomputable def modularAut (X a : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  X * a * X⁻¹

@[simp] lemma modularAut_one (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsUnit X.det) :
    modularAut X 1 = 1 := by
  simp [modularAut, Matrix.mul_nonsing_inv X hX]

/-- `σ_X` is multiplicative: the conjugation is an algebra map, not merely a
function. -/
lemma modularAut_mul (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsUnit X.det)
    (a b : Matrix (Fin n) (Fin n) ℂ) :
    modularAut X (a * b) = modularAut X a * modularAut X b := by
  have h : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hX
  simp only [modularAut]
  calc X * (a * b) * X⁻¹
      = X * a * (X⁻¹ * X) * b * X⁻¹ := by rw [h]; noncomm_ring
    _ = X * a * X⁻¹ * (X * b * X⁻¹) := by noncomm_ring

/-! ## §2 — The Gibbs functional of a weight -/

/-- `ω_X(a) = Tr(X a) / Tr(X)`. For `X = exp(-βH)` this is the Gibbs state at
inverse temperature `β`; here it is the functional attached to a weight. -/
noncomputable def gibbsFunctional (X a : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (X * a).trace / X.trace

/-! ## §3 — The KMS identity

The finite-level, imaginary-time modular condition. The proof is two
applications of trace cyclicity; no analysis appears. -/

/-- **★★★ r363: the KMS identity at finite level ★★★**

`ω_X(a b) = ω_X(b · σ_X(a))`. -/
theorem gibbs_kms (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsUnit X.det)
    (a b : Matrix (Fin n) (Fin n) ℂ) :
    gibbsFunctional X (a * b) = gibbsFunctional X (b * modularAut X a) := by
  have h : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hX
  -- the two matrix rearrangements, kept separate from the trace
  have e1 : X * (b * (X * a * X⁻¹)) = (X * b * X * a) * X⁻¹ := by noncomm_ring
  have e2 : X⁻¹ * (X * b * X * a) = b * (X * a) := by
    have e : X⁻¹ * (X * b * X * a) = (X⁻¹ * X) * (b * (X * a)) := by noncomm_ring
    rw [e, h, one_mul]
  have key : (X * (b * (X * a * X⁻¹))).trace = (X * (a * b)).trace := by
    rw [e1, Matrix.trace_mul_comm (X * b * X * a) X⁻¹, e2,
        Matrix.trace_mul_comm b (X * a), mul_assoc]
  simp only [gibbsFunctional, modularAut]
  congr 1
  exact key.symm

/-! ## §4 — A trace supplies no dynamics

`THE MAP` §0 says, in prose, that the modular group of a trace is trivial and
that time evolution is therefore not determined by `(A, τ)`. At finite level
that is this section. -/

/-- A scalar weight generates the **identity** automorphism: a trace has
trivial modular automorphism. -/
theorem modularAut_of_scalar (c : ℂ) (hc : c ≠ 0) (a : Matrix (Fin n) (Fin n) ℂ) :
    modularAut (c • (1 : Matrix (Fin n) (Fin n) ℂ)) a = a := by
  have hinv : (c • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹
      = c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [modularAut, hinv, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Consequently the scalar-weight functional is **tracial**: `ω(ab) = ω(ba)`.
So the tracial state generates no dynamics — the dictionary derivation cannot
run through it, and needs a non-scalar weight. -/
theorem gibbs_tracial_of_scalar (c : ℂ) (hc : c ≠ 0)
    (a b : Matrix (Fin n) (Fin n) ℂ) :
    gibbsFunctional (c • (1 : Matrix (Fin n) (Fin n) ℂ)) (a * b)
      = gibbsFunctional (c • (1 : Matrix (Fin n) (Fin n) ℂ)) (b * a) := by
  have hdet : IsUnit (c • (1 : Matrix (Fin n) (Fin n) ℂ)).det := by
    simp only [Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero).mpr (pow_ne_zero _ hc)
  have h := gibbs_kms (c • (1 : Matrix (Fin n) (Fin n) ℂ)) hdet a b
  rwa [modularAut_of_scalar c hc a] at h

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.modularAut_one
#print axioms PF.KMS.modularAut_mul
#print axioms PF.KMS.gibbs_kms
#print axioms PF.KMS.modularAut_of_scalar
#print axioms PF.KMS.gibbs_tracial_of_scalar
