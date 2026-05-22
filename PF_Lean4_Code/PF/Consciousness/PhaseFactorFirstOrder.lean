/-
# First-Order Taylor Expansion of `phaseFactor` at α = 0

Brick 5a in the attack on `Ch3LeadingOrderResonance`. The foundational
analytic step that any leading-order analysis of `R_f(α, 1)` near α = 0
must build on.

## The result proved (axiom-free)

For each fixed `n : ℕ`, the function

  `α ↦ phaseFactor α n = exp(I·π·α·D_3(n))`

has derivative at `α = 0` equal to `I·π·D_3(n)`. Equivalently:

  **phaseFactor α n = 1 + α · (I·π·D_3(n)) + o(α)** as α → 0.

This is the first-order term in the Taylor expansion. Combined with
absolute convergence of the resulting termwise-derivative series for
`Re(s) > 1`, this leads (Brick 5b, future) to the linear correction
formula

  **R_f(α, s) = ζ(s) + I·π·α · L(s) + O(α²)**  for `Re(s) > 1`

where `L(s) := Σ D_3(n)/n^s` (the "Dirichlet series of D_3").

## Status

Axiom-free. Foundational piece for the eventual derivation of
`Ch3LeadingOrderResonance` (or its disproof).

Stage L5a — phaseFactor first-order Taylor.
-/

import PF.Consciousness.FractalResonance
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace PrincipiaTractalis.Consciousness

open Complex Real
open PrincipiaTractalis.TuringEncoding

/-! ## First-order derivative of `phaseFactor` at `α = 0` -/

/-- **First-order derivative of `phaseFactor` in α.** For each fixed `n : ℕ`,

      `d/dα [exp(I·π·α·D_3(n))] |_{α = 0}  =  I · π · D_3(n)`.

    Proof: chain rule. The function is the composition `exp ∘ f` where
    `f(α) = I·π·α·D_3(n)` is linear in α with derivative
    `I·π·D_3(n)`. By `Complex.hasDerivAt_exp` and the linear-coercion
    derivative `hasDerivAt_id'`, the composition's derivative at α = 0
    is `exp(0) · (I·π·D_3(n)) = 1 · (I·π·D_3(n)) = I·π·D_3(n)`. -/
theorem phaseFactor_hasDerivAt_zero (n : ℕ) :
    HasDerivAt (fun α : ℝ => phaseFactor α n)
      (Complex.I * Real.pi * (digitalSum3 n : ℝ)) 0 := by
  -- Define f(α) := I·π·α·D_3(n) as a function ℝ → ℂ.
  -- Its derivative at any α is I·π·D_3(n).
  have h_f_deriv :
      HasDerivAt (fun α : ℝ => Complex.I * Real.pi * (α : ℂ) * (digitalSum3 n : ℝ))
        (Complex.I * Real.pi * (digitalSum3 n : ℝ)) 0 := by
    -- The function is (Complex.I * π * D_3(n)) · (α : ℂ) — a constant times
    -- the coercion of α. Use hasDerivAt_const_mul + the coercion derivative.
    have h_coe : HasDerivAt (fun α : ℝ => (α : ℂ)) (1 : ℂ) 0 :=
      Complex.ofRealCLM.hasDerivAt
    -- Then multiply by Complex.I * π * D_3(n) on the left.
    have h_const :
        HasDerivAt (fun α : ℝ => Complex.I * Real.pi * (α : ℂ) * (digitalSum3 n : ℝ))
          ((Complex.I * Real.pi * (digitalSum3 n : ℝ)) * 1) 0 := by
      have h_mul : HasDerivAt
          (fun α : ℝ => (Complex.I * Real.pi * (α : ℂ) * (digitalSum3 n : ℝ) : ℂ))
          ((Complex.I * Real.pi * (digitalSum3 n : ℝ)) * 1) 0 := by
        -- Rewrite f(α) = (I·π·D_3(n)) · α.
        have h_rewrite : ∀ α : ℝ,
            Complex.I * Real.pi * (α : ℂ) * (digitalSum3 n : ℝ) =
            (Complex.I * Real.pi * (digitalSum3 n : ℝ)) * (α : ℂ) := by
          intro α; ring
        simp_rw [h_rewrite]
        exact h_coe.const_mul _
      exact h_mul
    simpa using h_const
  -- Compose with Complex.exp using its derivative at 0: exp(0) = 1.
  have h_exp_at_zero :
      HasDerivAt Complex.exp 1 (Complex.I * Real.pi * (0 : ℂ) * (digitalSum3 n : ℝ)) := by
    have h_arg : Complex.I * Real.pi * (0 : ℂ) * (digitalSum3 n : ℝ) = 0 := by ring
    rw [h_arg]
    have h := Complex.hasDerivAt_exp 0
    rw [Complex.exp_zero] at h
    exact h
  -- Compose: exp(f(α)) has derivative exp(f(0)) · f'(0) = 1 · (I·π·D_3(n)).
  have h_comp := h_exp_at_zero.comp 0 h_f_deriv
  -- The result: derivative is 1 * (I·π·D_3(n)) = I·π·D_3(n).
  have h_simp : (1 : ℂ) * (Complex.I * Real.pi * (digitalSum3 n : ℝ)) =
                Complex.I * Real.pi * (digitalSum3 n : ℝ) := by ring
  rw [h_simp] at h_comp
  -- Match unfold: phaseFactor α n = exp(I·π·α·D_3(n))
  convert h_comp using 1

/-- **First-order derivative at general α**: same formula scaled by the
    phase factor.

      `d/dα [exp(I·π·α·D_3(n))]  =  I·π·D_3(n) · exp(I·π·α·D_3(n))`

    By the chain rule. -/
theorem phaseFactor_hasDerivAt (α : ℝ) (n : ℕ) :
    HasDerivAt (fun α : ℝ => phaseFactor α n)
      (Complex.I * Real.pi * (digitalSum3 n : ℝ) * phaseFactor α n) α := by
  have h_f_deriv :
      HasDerivAt (fun α : ℝ => Complex.I * Real.pi * (α : ℂ) * (digitalSum3 n : ℝ))
        (Complex.I * Real.pi * (digitalSum3 n : ℝ)) α := by
    have h_coe : HasDerivAt (fun α : ℝ => (α : ℂ)) (1 : ℂ) α :=
      Complex.ofRealCLM.hasDerivAt
    have h_rewrite : ∀ α : ℝ,
        Complex.I * Real.pi * (α : ℂ) * (digitalSum3 n : ℝ) =
        (Complex.I * Real.pi * (digitalSum3 n : ℝ)) * (α : ℂ) := by
      intro α; ring
    simp_rw [h_rewrite]
    have h := h_coe.const_mul (Complex.I * Real.pi * (digitalSum3 n : ℝ))
    simpa using h
  have h_exp_at :
      HasDerivAt Complex.exp
        (Complex.exp (Complex.I * Real.pi * (α : ℂ) * (digitalSum3 n : ℝ)))
        (Complex.I * Real.pi * (α : ℂ) * (digitalSum3 n : ℝ)) :=
    Complex.hasDerivAt_exp _
  have h_comp := h_exp_at.comp α h_f_deriv
  -- Rearrange: result = exp(f(α)) · (I·π·D_3(n)) = (I·π·D_3(n)) · exp(f(α))
  --                   = (I·π·D_3(n)) · phaseFactor α n
  have h_simp :
      Complex.exp (Complex.I * Real.pi * (α : ℂ) * (digitalSum3 n : ℝ)) *
        (Complex.I * Real.pi * (digitalSum3 n : ℝ))
      = Complex.I * Real.pi * (digitalSum3 n : ℝ) * phaseFactor α n := by
    unfold phaseFactor
    ring
  rw [h_simp] at h_comp
  convert h_comp using 1

end PrincipiaTractalis.Consciousness
