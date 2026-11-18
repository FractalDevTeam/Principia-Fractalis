import PF.DirichletEtaExtraFamilyStructure_2026_11_18
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The extra-zero family of `dirichletEtaExt` lies on `Re s = 1`

The family `s_k = 1 + 2π i k / Complex.log 2` for `k : ℤ` has
`Re(s_k) = 1` for every `k`.

```
extraFamily_re (k : ℤ) : (extraFamily k).re = 1
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Proof

`Complex.log 2` is real (its `.im = 0` and `.re = Real.log 2 > 0`),
so dividing a pure-imaginary numerator `2π i k` by it keeps the
quotient pure imaginary. Adding `1` preserves real part `1`.

Explicit route: `log 2 ≠ 0` lets us use `Complex.div_re` directly,
and the algebraic fact `Complex.log 2 = ((Real.log 2 : ℝ) : ℂ)`
reduces `log 2` to its real-part form.
-/

namespace PrincipiaTractalis.DirichletEtaExtraFamilyOnCriticalLine_2026_11_18

open Complex
open PrincipiaTractalis.DirichletEtaExtraFamilyStructure_2026_11_18
  (extraFamily)

/-- `Complex.log 2` has zero imaginary part. -/
private theorem complex_log_two_im_zero : (Complex.log 2).im = 0 := by
  have h : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    have hcast : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_cast
    rw [← hcast, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h, Complex.ofReal_im]

/-- `Complex.log 2` has real part `Real.log 2`. -/
private theorem complex_log_two_re : (Complex.log 2).re = Real.log 2 := by
  have h : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    have hcast : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_cast
    rw [← hcast, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h, Complex.ofReal_re]

/-- **The extra family lives on the critical line `Re s = 1`.** -/
theorem extraFamily_re (k : ℤ) : (extraFamily k).re = 1 := by
  unfold extraFamily
  have h_im_zero : (Complex.log 2).im = 0 := complex_log_two_im_zero
  have h_re_pos : 0 < (Complex.log 2).re := by
    rw [complex_log_two_re]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h_log_ne : Complex.log 2 ≠ 0 := by
    intro h
    have : (Complex.log 2).re = 0 := by rw [h]; simp
    linarith
  -- Compute the real part of `2 π I k / log 2`.
  -- Numerator `2 π I k` has `.re = 0` and `.im = 2 π k`.
  -- Divisor `log 2` has `.im = 0`.
  -- So quotient's real part is `(0 · log_re + 2πk · 0) / (log_re² + 0) = 0`.
  -- Adding to 1 gives 1.
  rw [Complex.add_re, Complex.one_re, Complex.div_re]
  rw [Complex.mul_re, Complex.mul_im, Complex.mul_re, Complex.mul_im,
      Complex.mul_re, Complex.mul_im]
  simp [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        h_im_zero, Complex.intCast_re, Complex.intCast_im]

#print axioms extraFamily_re

end PrincipiaTractalis.DirichletEtaExtraFamilyOnCriticalLine_2026_11_18
