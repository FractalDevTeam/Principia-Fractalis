/-
# r366: the modular automorphism IS the flow at imaginary time — step 4

★ 2026-10-28 r366 — the KMS condition's actual content at finite level ★

## Why this file is the one that matters

r363–r365 built an *algebraic* object: a weight `X`, its conjugation `σ_X`, and
a functional `ω_X` satisfying `ω_X(ab) = ω_X(b σ_X(a))`. Nothing there explains
why that identity deserves the name **KMS**. The name comes from a second fact,
which this file proves:

> the modular automorphism of the Gibbs weight at inverse temperature `β` is
> the system's own **time evolution**, analytically continued to imaginary time
> `iβ`.

That is the Kubo–Martin–Schwinger condition. Without it one has a conjugation
identity; with it one has thermal equilibrium, because the same one-parameter
family that moves the system in real time also produces the state's modular
structure when the time argument is rotated.

## What is proved

* `expScaled H c = exp(c·H)`, with `expScaled_mul_neg` giving
  `exp(cH) · exp(−cH) = 1`, hence `expScaled_inv`;
* `flowBy H c a = exp(cH) · a · exp(−cH)` — the flow with a **complex**
  coefficient, which is what lets real and imaginary time be the same object;
* `flowBy_zero`, `flowBy_mul`, `flowBy_one` — each `flowBy H c` is a unital
  multiplicative map, i.e. an algebra automorphism;
* `flowBy_add` — the **group law** `flowBy H (c+d) = flowBy H c ∘ flowBy H d`;
* `heisenbergFlow H t = flowBy H (i·t)` for real `t`, with
  `heisenbergFlow_zero` and `heisenbergFlow_add`: the genuine real-time
  one-parameter group of automorphisms;
* **`modularAut_gibbsWeight_eq_flowBy`** — `σ_{exp(-βH)} = flowBy H (-β)`;
* **`modularAut_eq_heisenbergFlow_imaginaryTime`** — and `-β = i·(iβ)`, so
  `σ_{exp(-βH)}` is `heisenbergFlow` at time `iβ`. **This is the KMS
  identification.**

## The β = 0 reading, which closes the arc of the build

At `β = 0` the identification says the modular automorphism is the flow at time
`0`, which is the identity — matching r363's `modularAut_of_scalar` reached from
the other direction. So the three facts now agree: the substrate's unique trace
sits at `β = 0`, generates no dynamics, and the KMS family moves off it exactly
as `β` moves off zero. That is the structural reason gate (A) needs a
**non-tracial** state, and it is now proved rather than asserted.

## What is NOT claimed

Not claimed: strong continuity of `t ↦ heisenbergFlow H t` in any topology,
analyticity in the strip, the boundary-value formulation of KMS (the one that
makes sense in infinite dimensions where `α_z` need not exist for complex `z`),
anything about `T_∞`, or any tower limit. In finite dimensions `exp(cH)` is
entire in `c`, which is precisely why this identification is available here by
bare computation and is hard in general. Finite level is the whole scope.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.KMS.GibbsWeightExp_r365

set_option autoImplicit false

namespace PF.KMS

open Matrix
open NormedSpace -- for `exp`

variable {n : ℕ}

/-! ## §0 — Real and complex scalars on a complex matrix agree -/

lemma real_smul_eq_complex_smul (r : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) :
    r • M = ((r : ℂ)) • M := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-! ## §1 — `exp(c·H)` and its inverse -/

/-- `exp(c·H)` for a complex coefficient `c`. -/
noncomputable def expScaled (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  exp ℂ (c • H)

lemma expScaled_zero (H : Matrix (Fin n) (Fin n) ℂ) : expScaled H 0 = 1 := by
  rw [expScaled, zero_smul, exp_zero]

/-- Scalar multiples of one matrix commute. -/
lemma commute_smul_smul (H : Matrix (Fin n) (Fin n) ℂ) (c d : ℂ) :
    Commute (c • H) (d • H) := by
  show (c • H) * (d • H) = (d • H) * (c • H)
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    smul_smul, smul_smul, mul_comm c d]

/-- `exp(cH) · exp(dH) = exp((c+d)H)`. -/
lemma expScaled_mul (H : Matrix (Fin n) (Fin n) ℂ) (c d : ℂ) :
    expScaled H c * expScaled H d = expScaled H (c + d) := by
  rw [expScaled, expScaled, expScaled, add_smul,
    Matrix.exp_add_of_commute _ _ _ (commute_smul_smul H c d)]

lemma expScaled_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    expScaled H c * expScaled H (-c) = 1 := by
  rw [expScaled_mul, add_neg_cancel, expScaled_zero]

/-- Hence the inverse of `exp(cH)` is `exp(-cH)`. -/
lemma expScaled_inv (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    (expScaled H c)⁻¹ = expScaled H (-c) :=
  Matrix.inv_eq_right_inv (expScaled_mul_neg H c)

/-! ## §2 — The flow with a complex coefficient -/

/-- `flowBy H c a = exp(cH) · a · exp(−cH)`. Real time is `c = i·t`; imaginary
time `iβ` is `c = −β`. -/
noncomputable def flowBy (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  expScaled H c * a * expScaled H (-c)

@[simp] lemma flowBy_zero (H : Matrix (Fin n) (Fin n) ℂ)
    (a : Matrix (Fin n) (Fin n) ℂ) : flowBy H 0 a = a := by
  simp [flowBy, expScaled_zero]

@[simp] lemma flowBy_one (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    flowBy H c 1 = 1 := by
  rw [flowBy, mul_one, expScaled_mul_neg]

/-- Each `flowBy H c` is multiplicative: it is an algebra automorphism. -/
lemma flowBy_mul (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (a b : Matrix (Fin n) (Fin n) ℂ) :
    flowBy H c (a * b) = flowBy H c a * flowBy H c b := by
  simp only [flowBy]
  calc expScaled H c * (a * b) * expScaled H (-c)
      = expScaled H c * a * (expScaled H (-c) * expScaled H c) * b
          * expScaled H (-c) := by
        rw [show expScaled H (-c) * expScaled H c = 1 by
          rw [← expScaled_mul_neg H (-c), neg_neg]]
        noncomm_ring
    _ = expScaled H c * a * expScaled H (-c)
          * (expScaled H c * b * expScaled H (-c)) := by noncomm_ring

/-- **The group law.** -/
lemma flowBy_add (H : Matrix (Fin n) (Fin n) ℂ) (c d : ℂ)
    (a : Matrix (Fin n) (Fin n) ℂ) :
    flowBy H (c + d) a = flowBy H c (flowBy H d a) := by
  have h : -(c + d) = -d + -c := by ring
  simp only [flowBy]
  rw [← expScaled_mul H c d, h, ← expScaled_mul H (-d) (-c)]
  noncomm_ring

/-! ## §3 — Real-time dynamics -/

/-- The real-time one-parameter group `α_t(a) = e^{itH} a e^{-itH}`. -/
noncomputable def heisenbergFlow (H : Matrix (Fin n) (Fin n) ℂ) (t : ℂ)
    (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  flowBy H (Complex.I * t) a

@[simp] lemma heisenbergFlow_zero (H : Matrix (Fin n) (Fin n) ℂ)
    (a : Matrix (Fin n) (Fin n) ℂ) : heisenbergFlow H 0 a = a := by
  simp [heisenbergFlow]

/-- `α_{s+t} = α_s ∘ α_t`: a genuine one-parameter group of automorphisms. -/
lemma heisenbergFlow_add (H : Matrix (Fin n) (Fin n) ℂ) (s t : ℂ)
    (a : Matrix (Fin n) (Fin n) ℂ) :
    heisenbergFlow H (s + t) a = heisenbergFlow H s (heisenbergFlow H t a) := by
  simp only [heisenbergFlow, mul_add]
  exact flowBy_add H _ _ a

/-! ## §4 — The KMS identification -/

/-- The Gibbs weight written with a complex coefficient. -/
lemma gibbsWeight_eq_expScaled (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    gibbsWeight β H = expScaled H (-(β : ℂ)) := by
  rw [gibbsWeight, expScaled, real_smul_eq_complex_smul]
  norm_num

/-- **★★★ r366: the modular automorphism is the flow at coefficient `−β` ★★★** -/
theorem modularAut_gibbsWeight_eq_flowBy (β : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    modularAut (gibbsWeight β H) a = flowBy H (-(β : ℂ)) a := by
  rw [modularAut, gibbsWeight_eq_expScaled, flowBy, expScaled_inv]

/-- **★★★ r366: THE KMS IDENTIFICATION ★★★**

The modular automorphism of the Gibbs state at inverse temperature `β` is the
real-time dynamics evaluated at **imaginary time** `iβ`. -/
theorem modularAut_eq_heisenbergFlow_imaginaryTime (β : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    modularAut (gibbsWeight β H) a
      = heisenbergFlow H (Complex.I * (β : ℂ)) a := by
  rw [modularAut_gibbsWeight_eq_flowBy, heisenbergFlow]
  congr 1
  rw [← mul_assoc, Complex.I_mul_I]
  ring

/-- At `β = 0` the identification degenerates to the identity, agreeing with
r363's `modularAut_of_scalar`: the trace generates no dynamics. -/
theorem modularAut_gibbsWeight_zero (H : Matrix (Fin n) (Fin n) ℂ)
    (a : Matrix (Fin n) (Fin n) ℂ) :
    modularAut (gibbsWeight 0 H) a = a := by
  rw [modularAut_eq_heisenbergFlow_imaginaryTime]
  norm_num

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.real_smul_eq_complex_smul
#print axioms PF.KMS.expScaled_inv
#print axioms PF.KMS.flowBy_mul
#print axioms PF.KMS.flowBy_add
#print axioms PF.KMS.heisenbergFlow_add
#print axioms PF.KMS.modularAut_gibbsWeight_eq_flowBy
#print axioms PF.KMS.modularAut_eq_heisenbergFlow_imaginaryTime
#print axioms PF.KMS.modularAut_gibbsWeight_zero
