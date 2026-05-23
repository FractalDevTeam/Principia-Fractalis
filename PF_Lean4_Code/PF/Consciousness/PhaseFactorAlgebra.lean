/-
# Phase Factor Algebra in α (Brick C)

Algebraic identities for `phaseFactor α n = exp(I·π·α·D_3(n))` as
α varies, per Agent 4 audit (2026-05-22):

  * **Periodicity**: `phaseFactor (α + 2) n = phaseFactor α n` (since
    `exp(2π·I·D_3(n)) = 1` for natural D_3(n)).
  * **Multiplicativity**: `phaseFactor (α + β) n = phaseFactor α n · phaseFactor β n`
    (additive in α corresponds to multiplicative in the phase).
  * **Conjugation**: `phaseFactor (-α) n = star(phaseFactor α n)`.

## Why this matters

Periodicity + multiplicativity together imply
`fractalResonance (α+2) s = fractalResonance α s` — the relevant
α-domain for R_f is the fundamental period **[0, 2)**, which contains
all 8 Millennium α-values except NS = 3π/2 ≈ 4.71. (NS sits in
[2, 4) — period-2-shifted equivalent to 3π/2 - 2 ≈ 2.71 in [2, 4),
then to ≈ 0.71 after another shift.)

This narrows the structural domain of analysis and provides cleanup
identities for downstream proofs.

## Status

Axiom-free. Pure algebra on complex exponentials.

Stage L6 (Brick C) — phaseFactor algebra in α.
-/

import PF.Consciousness.FractalResonance

namespace PrincipiaTractalis.Consciousness

open Complex Real
open PrincipiaTractalis.TuringEncoding

/-! ## Multiplicativity: `phaseFactor (α + β) n = phaseFactor α n · phaseFactor β n` -/

/-- **Additivity in α corresponds to multiplicativity in the phase**.
    `exp(I·π·(α+β)·D_3(n)) = exp(I·π·α·D_3(n)) · exp(I·π·β·D_3(n))`. -/
theorem phaseFactor_add (α β : ℝ) (n : ℕ) :
    phaseFactor (α + β) n = phaseFactor α n * phaseFactor β n := by
  unfold phaseFactor
  -- exp(I·π·(α+β)·D_3) = exp(I·π·α·D_3 + I·π·β·D_3) = exp(...) · exp(...)
  rw [show (Complex.I * (Real.pi : ℂ) * ((α + β : ℝ) : ℂ) * ((digitalSum3 n : ℝ) : ℂ))
        = Complex.I * (Real.pi : ℂ) * ((α : ℝ) : ℂ) * ((digitalSum3 n : ℝ) : ℂ)
        + Complex.I * (Real.pi : ℂ) * ((β : ℝ) : ℂ) * ((digitalSum3 n : ℝ) : ℂ) from by
    push_cast; ring]
  exact Complex.exp_add _ _

/-! ## Periodicity: `phaseFactor (α + 2) n = phaseFactor α n` -/

/-- **At `α = 2`, the phase factor is identically 1** (local copy from
    `RfAtAlphaTwoIsZeta` to keep this file self-contained on the algebra
    side without circular dependency). -/
private theorem phaseFactor_two (n : ℕ) : phaseFactor 2 n = 1 := by
  unfold phaseFactor
  have h_rewrite :
      Complex.I * (Real.pi : ℂ) * ((2 : ℝ) : ℂ) * ((digitalSum3 n : ℝ) : ℂ)
      = ((digitalSum3 n : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h_rewrite, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I]
  exact one_pow _

/-- **Period-2 periodicity of `phaseFactor` in α**:
    `phaseFactor (α + 2) n = phaseFactor α n` for all real α and natural n.

    Direct consequence of multiplicativity + `phaseFactor 2 n = 1`. -/
theorem phaseFactor_period_two (α : ℝ) (n : ℕ) :
    phaseFactor (α + 2) n = phaseFactor α n := by
  rw [phaseFactor_add α 2 n, phaseFactor_two, mul_one]

/-- **General even-shift periodicity**: `phaseFactor (α + 2k) n = phaseFactor α n`
    for any natural `k`. -/
theorem phaseFactor_period_two_nat (α : ℝ) (k : ℕ) (n : ℕ) :
    phaseFactor (α + 2 * k) n = phaseFactor α n := by
  induction k with
  | zero =>
    rw [show α + 2 * (0 : ℕ) = α from by push_cast; ring]
  | succ k ih =>
    -- phaseFactor (α + 2·(k+1)) = phaseFactor ((α + 2·k) + 2) = phaseFactor (α + 2·k) = phaseFactor α
    have h_rewrite : α + 2 * ((k + 1 : ℕ) : ℝ) = (α + 2 * (k : ℕ)) + 2 := by
      push_cast; ring
    rw [h_rewrite, phaseFactor_period_two, ih]

/-! ## Negation identity: `phaseFactor (-α) n · phaseFactor α n = 1`

    Direct algebraic identity from `phaseFactor_add` + `phaseFactor 0 = 1`:

      `phaseFactor (-α) n · phaseFactor α n = phaseFactor (-α + α) n
                                            = phaseFactor 0 n = 1`. -/

/-- **Negation cancels via multiplication**: `phaseFactor (-α) n · phaseFactor α n = 1`. -/
theorem phaseFactor_neg_mul_self (α : ℝ) (n : ℕ) :
    phaseFactor (-α) n * phaseFactor α n = 1 := by
  rw [← phaseFactor_add]
  rw [show -α + α = 0 from by ring]
  exact phaseFactor_alpha_zero n

/-- **Symmetric version**: `phaseFactor α n · phaseFactor (-α) n = 1`. -/
theorem phaseFactor_mul_neg_self (α : ℝ) (n : ℕ) :
    phaseFactor α n * phaseFactor (-α) n = 1 := by
  rw [← phaseFactor_add]
  rw [show α + (-α) = 0 from by ring]
  exact phaseFactor_alpha_zero n

end PrincipiaTractalis.Consciousness
