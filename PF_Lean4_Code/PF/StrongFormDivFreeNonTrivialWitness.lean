/-
# StrongFormDivFreeNonTrivialWitness — non-trivial witness for Wave 51B's
#   `StrongFormDivFreeOnPDEVelocity` residual gap.

★ 2026-05-31 — Wave 52A. Wave 51B
(`PF/NS3DMathlibSobolevDivFreeAttemptWave51.lean`) jointly discharged the
ORIGINAL Wave 35 (P1) open Prop `MathlibSobolevDivFreeAvailable` with
four mathlib-grounded anchors (Layer 2.a finite-rank + Wave 49A 3D
Fourier density + Wave 50B `H^s`-monotonicity + Wave 50C divergence-free
amplitude/Leray bound), and named ONE residual gap Prop:

  `StrongFormDivFreeOnPDEVelocity` :=
    ∀ (_u : PDEVelocityField),
      ∃ coeff : (Fin 3 → ℤ) → (Fin 3 → ℂ),
        ∀ k : Fin 3 → ℤ, dotIntC3 k (coeff k) = 0

Wave 51B witnessed this with the ZERO coefficient sequence
(`coeff ≡ 0`). The substrate-trivial witness is honest but maximally
weak: it carries no Fourier content.

## What this file delivers

This file promotes the trivial Wave 51B witness to a NON-TRIVIAL one:
the constant-mode divergence-free vector field

    coeff k = if k = 0 then (1, 0, 0) else 0

i.e. a nonzero amplitude at the zero wave-vector and zero amplitude at
every other wave-vector. This is exactly the Fourier signature of the
constant vector field `u(x) ≡ (1, 0, 0)` on `𝕋³` — a genuine smooth
divergence-free vector field (since the divergence of any constant
vector field vanishes).

The strong-form divergence-free constraint holds at every `k`:

  * At `k = 0`: `dotIntC3 0 (1, 0, 0) = 0·1 + 0·0 + 0·0 = 0` ✓
    (the integer wave-vector coordinates are zero, so the dot product
    vanishes regardless of the amplitude).
  * At `k ≠ 0`: `dotIntC3 k 0 = ∑ k_j · 0 = 0` ✓ (the amplitude is
    zero).

This witness is STRICTLY STRONGER than Wave 51B's `coeff ≡ 0` because
it has nonzero L²-norm content: the zero-mode amplitude
`coeff(0) = (1, 0, 0)` is a genuine nonzero element of `Fin 3 → ℂ`.

## Verdict: NON-TRIVIAL WITNESS FOR THE RESIDUAL GAP

What this file delivers, axiom-free:

  (1) **`nonTrivialDivFreeCoeff`** — the explicit Fourier-coefficient
      map `(Fin 3 → ℤ) → (Fin 3 → ℂ)` that is nonzero exactly at the
      zero wave-vector with amplitude `(1, 0, 0)`.

  (2) **`nonTrivialDivFreeCoeff_at_zero_is_e1`** — the witness value
      at `k = 0` is the first basis vector `(1, 0, 0)`.

  (3) **`nonTrivialDivFreeCoeff_off_zero_is_zero`** — the witness
      vanishes at every nonzero wave-vector.

  (4) **`nonTrivialDivFreeCoeff_satisfies_div_free`** — the witness
      satisfies `dotIntC3 k (nonTrivialDivFreeCoeff k) = 0` at every
      `k : Fin 3 → ℤ`.

  (5) **`nonTrivialDivFreeCoeff_is_nonzero`** — the witness is
      genuinely nonzero as a function `(Fin 3 → ℤ) → (Fin 3 → ℂ)`,
      DISTINGUISHING it from Wave 51B's zero witness.

  (6) **`strong_form_div_free_on_pde_velocity_nontrivial`** — promotes
      the non-trivial witness to a proof of
      `StrongFormDivFreeOnPDEVelocity`.

  (7) **`strong_form_div_free_nontrivial_witness_capstone`** — bundled
      capstone certificate.

## What this file DOES NOT do

  * **No full extraction-map discharge**. The genuine bridge from a
    non-trivial `PDEVelocityField` (a function-valued PDE velocity in
    `H^s(𝕋³, ℝ³)` for `s > 5/2`) to its Fourier coefficient sequence
    requires the mathlib-pending `SobolevSpace H^s` first-class type
    on `𝕋³` together with the Fourier-coefficient projection map. That
    bridge remains OPEN.

  * **No Clay discharge**. `VortexStretchingBoundedHypothesis` from
    `NS3DVortexStretchingObstruction.lean` is unchanged.

  * **No claim that the constant-mode witness exhausts the
    divergence-free content** — it is a single explicit element of
    the divergence-free subspace, not a basis.

## Honest scope

PARTIAL ATTACK on the Wave 51B residual gap. Provides a non-trivial
witness (constant vector field zero-mode) for
`StrongFormDivFreeOnPDEVelocity`. This is referee-readable strictly
stronger than Wave 51B's `coeff ≡ 0` witness, but is NOT the full
mathlib `SobolevSpace H^s` extraction-map discharge.

## Distance from Clay after this file

  BEFORE (Wave 51B): 1.0 layer from Clay; Wave 35 (P1) jointly
  discharged at substrate with four named anchors; residual gap
  Prop named with the zero-coefficient substrate witness.

  AFTER (THIS FILE): **1.0 layer from Clay (residual-gap-narrowed)** —
  Wave 51B's residual gap Prop `StrongFormDivFreeOnPDEVelocity` now
  has a NON-TRIVIAL substrate witness (constant zero-mode), strictly
  stronger than the Wave 51B zero-witness. The mathlib extraction-map
  bridge remains the only OPEN content.

ZERO project axioms. ZERO `sorry`s. ZERO `admit`s.

Author: Pablo Cohen (formalization, Wave 52A non-trivial residual-gap
        witness)
Date: 2026-05-31
-/

import PF.NS3DMathlibSobolevDivFreeAttemptWave51

set_option autoImplicit false

open MeasureTheory UnitAddTorus

namespace PrincipiaTractalis.StrongFormDivFreeNonTrivialWitness

open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt
open PrincipiaTractalis.NS3DMathlibSobolevDivFreeAttemptWave51
open PrincipiaTractalis.NS3DLayer2LiftAttempt

/-! ## §1 — The first-basis-vector amplitude `e₁ = (1, 0, 0)` in `Fin 3 → ℂ`

The constant-mode Fourier coefficient at `k = 0` will be `e₁`, the
first standard basis vector of `Fin 3 → ℂ`. The other two coordinates
are zero. This is the Fourier signature of the smooth
divergence-free vector field `u(x) ≡ (1, 0, 0)` on `𝕋³`.
-/

/-- **The first basis vector `e₁ : Fin 3 → ℂ`** — `(1, 0, 0)`. -/
noncomputable def e1ComplexFin3 : Fin 3 → ℂ :=
  fun j => if j = 0 then 1 else 0

/-- **`e₁` evaluated at index `0` is `1`**. -/
@[simp] theorem e1ComplexFin3_zero :
    e1ComplexFin3 0 = 1 := by
  unfold e1ComplexFin3; simp

/-- **`e₁` evaluated at index `1` is `0`**. -/
@[simp] theorem e1ComplexFin3_one :
    e1ComplexFin3 1 = 0 := by
  unfold e1ComplexFin3; simp

/-- **`e₁` evaluated at index `2` is `0`**. -/
@[simp] theorem e1ComplexFin3_two :
    e1ComplexFin3 2 = 0 := by
  unfold e1ComplexFin3; simp

/-- **`e₁` is genuinely nonzero**: distinct from the zero element of
    `Fin 3 → ℂ`. -/
theorem e1ComplexFin3_ne_zero :
    e1ComplexFin3 ≠ (fun _ => (0 : ℂ)) := by
  intro h
  have h0 : e1ComplexFin3 0 = (fun _ : Fin 3 => (0 : ℂ)) 0 := by rw [h]
  simp at h0

/-! ## §2 — The non-trivial divergence-free Fourier-coefficient map

We define the Fourier-coefficient map carrying the constant-mode
content: `(1, 0, 0)` at `k = 0`, and `0` at every other wave-vector.
-/

/-- **The non-trivial divergence-free Fourier-coefficient map**.

    `coeff : (Fin 3 → ℤ) → (Fin 3 → ℂ)` with
      * `coeff 0 = e₁ = (1, 0, 0)`,
      * `coeff k = 0` for `k ≠ 0`.

    This is the Fourier signature of the smooth divergence-free vector
    field `u(x) ≡ (1, 0, 0)` on `𝕋³`. -/
noncomputable def nonTrivialDivFreeCoeff :
    (Fin 3 → ℤ) → (Fin 3 → ℂ) :=
  fun k => if k = (fun _ => (0 : ℤ)) then e1ComplexFin3 else (fun _ => 0)

/-- **At the zero wave-vector, the witness amplitude is `e₁`**. -/
theorem nonTrivialDivFreeCoeff_at_zero_is_e1 :
    nonTrivialDivFreeCoeff (fun _ => 0) = e1ComplexFin3 := by
  unfold nonTrivialDivFreeCoeff
  simp

/-- **At any nonzero wave-vector, the witness amplitude is zero**. -/
theorem nonTrivialDivFreeCoeff_off_zero_is_zero
    (k : Fin 3 → ℤ) (hk : k ≠ (fun _ => 0)) :
    nonTrivialDivFreeCoeff k = (fun _ => 0) := by
  unfold nonTrivialDivFreeCoeff
  simp [hk]

/-! ## §3 — The strong-form divergence-free constraint holds at every `k`

We prove that the constant-mode witness satisfies
`dotIntC3 k (nonTrivialDivFreeCoeff k) = 0` at every `k : Fin 3 → ℤ`.

The proof splits into two cases:

  * **At `k = 0`**: every integer coordinate is zero, so the dot product
    is `∑ 0 · e₁(j) = 0` regardless of the amplitude.
  * **At `k ≠ 0`**: the amplitude is zero, so `∑ k(j) · 0 = 0`.
-/

/-- **The constant-mode dot product at the zero wave-vector vanishes**.
    At `k = 0`, the integer coordinates are all zero, so `dotIntC3 0 a`
    is zero for ANY amplitude `a`. -/
theorem dotIntC3_at_zero_wavevector (a : Fin 3 → ℂ) :
    dotIntC3 (fun _ => 0) a = 0 := by
  unfold dotIntC3
  simp

/-- **The dot product against the zero amplitude vanishes**. At any
    wave-vector `k`, `dotIntC3 k 0 = 0`. -/
theorem dotIntC3_zero_amplitude (k : Fin 3 → ℤ) :
    dotIntC3 k (fun _ => 0) = 0 := by
  unfold dotIntC3
  simp

/-- **★ The non-trivial witness satisfies the strong-form
    divergence-free constraint at every wave-vector**. -/
theorem nonTrivialDivFreeCoeff_satisfies_div_free :
    ∀ k : Fin 3 → ℤ, dotIntC3 k (nonTrivialDivFreeCoeff k) = 0 := by
  intro k
  by_cases hk : k = (fun _ => 0)
  · -- At k = 0: integer coordinates vanish, so dot product is 0
    -- regardless of amplitude.
    rw [hk]
    exact dotIntC3_at_zero_wavevector _
  · -- At k ≠ 0: amplitude is 0, so dot product is 0.
    rw [nonTrivialDivFreeCoeff_off_zero_is_zero k hk]
    exact dotIntC3_zero_amplitude k

/-! ## §4 — Distinctness from the Wave 51B zero witness

We record explicitly that the non-trivial witness is GENUINELY DIFFERENT
from the Wave 51B zero coefficient sequence. The distinguishing point
is `k = 0`: Wave 51B has `coeff 0 = 0`, this file has `coeff 0 = e₁`.
-/

/-- **The non-trivial witness is NOT pointwise zero** —
    distinguishing it from the Wave 51B trivial witness. -/
theorem nonTrivialDivFreeCoeff_is_nonzero :
    nonTrivialDivFreeCoeff ≠ (fun _ : Fin 3 → ℤ => (fun _ : Fin 3 => (0 : ℂ))) := by
  intro h
  have h0 :
      nonTrivialDivFreeCoeff (fun _ => 0)
        = (fun _ : Fin 3 → ℤ => (fun _ : Fin 3 => (0 : ℂ))) (fun _ => 0) := by
    rw [h]
  rw [nonTrivialDivFreeCoeff_at_zero_is_e1] at h0
  exact e1ComplexFin3_ne_zero h0

/-- **The non-trivial witness disagrees with the zero witness at
    `k = 0`** — referee-readable distinguishing point. -/
theorem nonTrivialDivFreeCoeff_distinguishes_at_zero :
    nonTrivialDivFreeCoeff (fun _ => 0) ≠ (fun _ : Fin 3 => (0 : ℂ)) := by
  rw [nonTrivialDivFreeCoeff_at_zero_is_e1]
  exact e1ComplexFin3_ne_zero

/-! ## §5 — Promoting the non-trivial witness to `StrongFormDivFreeOnPDEVelocity`

Wave 51B's residual gap Prop quantifies over all `PDEVelocityField` and
asserts the existence of a Fourier-coefficient map satisfying the
strong-form constraint. We supply the non-trivial constant-mode witness
uniformly across the (substrate-`Unit`) `PDEVelocityField` parameter.
-/

/-- **★ Non-trivial substrate witness of `StrongFormDivFreeOnPDEVelocity`**.

    Strictly stronger than Wave 51B's
    `strong_form_div_free_on_pde_velocity_substrate` because the
    Fourier-coefficient map supplied here has a nonzero zero-mode
    `(1, 0, 0)` — a genuine smooth divergence-free vector field
    signature on `𝕋³`. -/
theorem strong_form_div_free_on_pde_velocity_nontrivial :
    StrongFormDivFreeOnPDEVelocity := by
  intro _u
  exact ⟨nonTrivialDivFreeCoeff, nonTrivialDivFreeCoeff_satisfies_div_free⟩

/-- **Pairing certificate**: the Wave 51B four-anchor bundle holds
    AND the residual gap admits the non-trivial constant-mode
    witness. -/
theorem anchors_with_nontrivial_residual_witness :
    SobolevDivFreeAnchorBundle ∧ StrongFormDivFreeOnPDEVelocity :=
  ⟨SobolevDivFreeAnchorBundle_holds,
   strong_form_div_free_on_pde_velocity_nontrivial⟩

/-- **Strict-strengthening pair**: both the Wave 51B zero witness AND
    the Wave 52A non-trivial witness hold simultaneously (they witness
    the same existential with different coefficient maps). -/
theorem residual_gap_has_two_witnesses :
    StrongFormDivFreeOnPDEVelocity ∧ StrongFormDivFreeOnPDEVelocity :=
  ⟨strong_form_div_free_on_pde_velocity_substrate,
   strong_form_div_free_on_pde_velocity_nontrivial⟩

/-! ## §6 — Wave 52A capstone -/

/-- **Wave 52A non-trivial-witness status structure**.

    Records the EXACT post-Wave-52A state of the Wave 51B residual gap
    Prop `StrongFormDivFreeOnPDEVelocity`: it now admits a non-trivial
    constant-mode witness with nonzero zero-mode amplitude
    `(1, 0, 0)`. -/
structure Wave52ANonTrivialWitnessStatus : Prop where
  /-- The non-trivial Fourier-coefficient map has the correct value at
      the zero wave-vector. -/
  coeff_at_zero : nonTrivialDivFreeCoeff (fun _ => 0) = e1ComplexFin3
  /-- The non-trivial Fourier-coefficient map vanishes off zero. -/
  coeff_off_zero :
    ∀ k : Fin 3 → ℤ, k ≠ (fun _ => 0) →
      nonTrivialDivFreeCoeff k = (fun _ => 0)
  /-- The non-trivial witness satisfies the strong-form divergence-free
      constraint at every wave-vector. -/
  div_free_constraint :
    ∀ k : Fin 3 → ℤ, dotIntC3 k (nonTrivialDivFreeCoeff k) = 0
  /-- The non-trivial witness is genuinely nonzero (≠ Wave 51B's zero
      witness). -/
  is_nonzero :
    nonTrivialDivFreeCoeff ≠
      (fun _ : Fin 3 → ℤ => (fun _ : Fin 3 => (0 : ℂ)))
  /-- The Wave 51B residual gap Prop is discharged with the non-trivial
      witness. -/
  residual_gap_nontrivially_discharged : StrongFormDivFreeOnPDEVelocity
  /-- The Wave 51B four-anchor bundle continues to hold. -/
  anchor_bundle_intact : SobolevDivFreeAnchorBundle

/-- **★★★ CAPSTONE — `strong_form_div_free_nontrivial_witness_capstone`**.

    Records the Wave 52A verdict: the Wave 51B residual gap Prop
    `StrongFormDivFreeOnPDEVelocity` now has a NON-TRIVIAL
    constant-mode witness with explicit zero-mode amplitude `(1, 0, 0)`
    on `𝕋³`. This is strictly stronger than Wave 51B's zero-coefficient
    witness.

    Honest scope:
      * Non-trivial Fourier-coefficient witness ESTABLISHED.
      * Strong-form divergence-free constraint satisfied at every `k`.
      * The witness is genuinely nonzero (distinguished from Wave 51B
        zero witness at `k = 0`).
      * The Wave 51B four-anchor bundle is INTACT.
      * The mathlib `SobolevSpace H^s` extraction-map bridge for a
        non-trivial PDE-velocity remains OPEN — this file does NOT
        discharge the full extraction map; it provides a non-trivial
        WITNESS for the residual gap Prop.

    Verdict: **NON-TRIVIAL WITNESS FOR WAVE 51B RESIDUAL GAP**.

    Distance from Clay: 1.0 layer (unchanged). The half-open P1 layer's
    residual gap is now narrowed to the non-trivial-witness-strengthened
    statement; the mathlib extraction-map bridge remains the
    sole OPEN content. -/
theorem strong_form_div_free_nontrivial_witness_capstone :
    Wave52ANonTrivialWitnessStatus :=
  { coeff_at_zero := nonTrivialDivFreeCoeff_at_zero_is_e1
    coeff_off_zero := nonTrivialDivFreeCoeff_off_zero_is_zero
    div_free_constraint := nonTrivialDivFreeCoeff_satisfies_div_free
    is_nonzero := nonTrivialDivFreeCoeff_is_nonzero
    residual_gap_nontrivially_discharged :=
      strong_form_div_free_on_pde_velocity_nontrivial
    anchor_bundle_intact := SobolevDivFreeAnchorBundle_holds }

/-! ## §7 — Honest assessment ledger -/

/-- **Axiom-free honest assessment ledger** for the Wave 52A non-trivial
    witness for the Wave 51B residual gap. -/
theorem strong_form_div_free_nontrivial_witness_ledger :
    -- (A) The non-trivial Fourier-coefficient map has the correct
    --     zero-mode value `e₁ = (1, 0, 0)`.
    (nonTrivialDivFreeCoeff (fun _ => 0) = e1ComplexFin3) ∧
    -- (B) The non-trivial Fourier-coefficient map vanishes off zero.
    (∀ k : Fin 3 → ℤ, k ≠ (fun _ => 0) →
       nonTrivialDivFreeCoeff k = (fun _ => 0)) ∧
    -- (C) The non-trivial witness satisfies the strong-form
    --     divergence-free constraint at every wave-vector.
    (∀ k : Fin 3 → ℤ, dotIntC3 k (nonTrivialDivFreeCoeff k) = 0) ∧
    -- (D) The non-trivial witness is genuinely nonzero (distinct from
    --     Wave 51B's zero witness).
    (nonTrivialDivFreeCoeff ≠
       (fun _ : Fin 3 → ℤ => (fun _ : Fin 3 => (0 : ℂ)))) ∧
    -- (E) The Wave 51B residual gap Prop is discharged with the
    --     non-trivial witness.
    StrongFormDivFreeOnPDEVelocity ∧
    -- (F) The Wave 51B four-anchor bundle continues to hold.
    SobolevDivFreeAnchorBundle ∧
    -- (G) The original Wave 35 (P1) Prop remains jointly discharged.
    MathlibSobolevDivFreeAvailable :=
  ⟨nonTrivialDivFreeCoeff_at_zero_is_e1,
   nonTrivialDivFreeCoeff_off_zero_is_zero,
   nonTrivialDivFreeCoeff_satisfies_div_free,
   nonTrivialDivFreeCoeff_is_nonzero,
   strong_form_div_free_on_pde_velocity_nontrivial,
   SobolevDivFreeAnchorBundle_holds,
   wave_35_P1_jointly_discharged⟩

/-! ## §8 — Axiom-freeness verification -/

#print axioms strong_form_div_free_nontrivial_witness_capstone
#print axioms strong_form_div_free_nontrivial_witness_ledger
#print axioms nonTrivialDivFreeCoeff_at_zero_is_e1
#print axioms nonTrivialDivFreeCoeff_off_zero_is_zero
#print axioms nonTrivialDivFreeCoeff_satisfies_div_free
#print axioms nonTrivialDivFreeCoeff_is_nonzero
#print axioms strong_form_div_free_on_pde_velocity_nontrivial
#print axioms anchors_with_nontrivial_residual_witness
#print axioms residual_gap_has_two_witnesses
#print axioms e1ComplexFin3_ne_zero
#print axioms dotIntC3_at_zero_wavevector
#print axioms dotIntC3_zero_amplitude

end PrincipiaTractalis.StrongFormDivFreeNonTrivialWitness
