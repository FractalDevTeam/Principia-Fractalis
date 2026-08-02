/-
# PF.DuplicationFormula_r178

★★★ 2026-08-01 — THE LAST PER-CURVE OBLIGATION, DISCHARGED UNIVERSALLY ★★★

r177 reduced the whole canonical-height construction to **one** hypothesis per
curve: that `Φ/Ψ` computes doubling on `x`-coordinates.  This stone proves that
hypothesis for *every* Weierstrass curve over *any* field, against mathlib's own
`addX`/`slope`.

## The two facts

**1. The denominator is a perfect square.**  On the curve,

  `Ψ(x) = 4x³ + b₂x² + 2b₄x + b₆ = (y − negY x y)² = (2y + a₁x + a₃)²`

which is why the duplication map has a square denominator at all, and why the
naive-height estimates come out in powers of four rather than eight.

**2. The duplication formula.**  With `ℓ = slope x x y y`,

  `addX x x ℓ = Φ(x) / Ψ(x)`.

Clearing denominators, this is a polynomial identity modulo the curve equation
with a startlingly small certificate: the multiplier is just `−(b₂ + 8x)`.
Found by division in sympy (`codex/duplication_formula_cert.py` logic inlined in
the r178 commit message), then checked by `linear_combination`.

**3. Homogenisation.**  `Φ(X,Y) = Y⁴·φ(X/Y)` and `Ψ(X,Y) = Y⁴·ψ(X/Y)`, so the
`Y⁴` cancels and r176's `dblQ` is exactly `φ/ψ`.

## What this closes

r174 content → r175 size → r176 heights → r177 `HeightWindow` → r171 canonical
height → r173 uniqueness, and now r178 supplies r177's `hx` from mathlib's group
law rather than by hand.  Nothing in the chain is curve-specific any more.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-01.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.Tactic.LinearCombination
import PF.DuplicationHeightUniversal_r176

set_option linter.unusedSectionVars false

namespace PrincipiaTractalis.DuplicationFormula

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- Dehomogenised duplication numerator. -/
def phiX (x : F) : F := x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈

/-- Dehomogenised duplication denominator. -/
def psiX (x : F) : F := 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆

variable {W}

/-- **The denominator is a perfect square on the curve.** -/
theorem psiX_eq_sq {x y : F} (h : W.Equation x y) :
    psiX W x = (y - W.negY x y) ^ 2 := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [psiX, WeierstrassCurve.Affine.negY, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination (-4 : F) * h

/-- **The duplication formula**, against mathlib's own `addX` and `slope`. -/
theorem addX_self_eq {x y : F} (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) = phiX W x / psiX W x := by
  have hD : y - W.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hPsi : psiX W x = (y - W.negY x y) ^ 2 := psiX_eq_sq h
  rw [WeierstrassCurve.Affine.equation_iff] at h
  -- The identity with denominators already cleared.  `-(b₂ + 8x)` is the whole
  -- certificate; found by polynomial division against the curve equation.
  have hnum : phiX W x
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
        + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (y - W.negY x y)
        - (W.a₂ + 2 * x) * (y - W.negY x y) ^ 2 := by
    simp only [phiX, WeierstrassCurve.Affine.negY, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) * h
  rw [W.slope_of_Y_ne rfl hy, hPsi, hnum]
  simp only [WeierstrassCurve.Affine.addX]
  field_simp
  ring

end PrincipiaTractalis.DuplicationFormula

/-! ## Homogenisation: r176's `dblQ` is the dehomogenised formula -/

namespace PrincipiaTractalis.DuplicationHeight

open PrincipiaTractalis.DuplicationBezout PrincipiaTractalis.DuplicationFormula

variable {b₂ b₄ b₆ b₈ : ℤ} {W : WeierstrassCurve.Affine ℚ}

/-- `Φ(X,Y) = Y⁴ · φ(X/Y)`. -/
theorem Phi_eq_den_pow_mul (hb₄ : (b₄ : ℚ) = W.b₄) (hb₆ : (b₆ : ℚ) = W.b₆)
    (hb₈ : (b₈ : ℚ) = W.b₈) (x : ℚ) :
    (Phi b₄ b₆ b₈ x.num (x.den : ℤ) : ℚ) = (x.den : ℚ) ^ 4 * phiX W x := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_ne_zero x
  -- Derived, not rewritten: any `rw` on `x` also hits the `x` inside `x.den`.
  have hnum : x * (x.den : ℚ) = (x.num : ℚ) :=
    ((div_eq_iff hd).mp (Rat.num_div_den x)).symm
  simp only [Phi, phiX]
  push_cast
  rw [hb₄, hb₆, hb₈, ← hnum]
  ring

/-- `Ψ(X,Y) = Y⁴ · ψ(X/Y)`. -/
theorem Psi_eq_den_pow_mul (hb₂ : (b₂ : ℚ) = W.b₂) (hb₄ : (b₄ : ℚ) = W.b₄)
    (hb₆ : (b₆ : ℚ) = W.b₆) (x : ℚ) :
    (Psi b₂ b₄ b₆ x.num (x.den : ℤ) : ℚ) = (x.den : ℚ) ^ 4 * psiX W x := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_ne_zero x
  -- Derived, not rewritten: any `rw` on `x` also hits the `x` inside `x.den`.
  have hnum : x * (x.den : ℚ) = (x.num : ℚ) :=
    ((div_eq_iff hd).mp (Rat.num_div_den x)).symm
  simp only [Psi, psiX]
  push_cast
  rw [hb₂, hb₄, hb₆, ← hnum]
  ring

/-- **`dblQ` is the dehomogenised duplication map.**  The `Y⁴` cancels. -/
theorem dblQ_eq_phiX_div_psiX (hb₂ : (b₂ : ℚ) = W.b₂) (hb₄ : (b₄ : ℚ) = W.b₄)
    (hb₆ : (b₆ : ℚ) = W.b₆) (hb₈ : (b₈ : ℚ) = W.b₈) (x : ℚ) :
    dblQ b₂ b₄ b₆ b₈ x = phiX W x / psiX W x := by
  have hd : ((x.den : ℚ)) ^ 4 ≠ 0 := by
    have : (x.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_ne_zero x
    positivity
  rw [dblQ, Phi_eq_den_pow_mul hb₄ hb₆ hb₈ x, Psi_eq_den_pow_mul hb₂ hb₄ hb₆ x,
    mul_div_mul_left _ _ hd]

/-- **The chain closes.**  For any Weierstrass curve over ℚ whose `b`-invariants
are the given integers, `dblQ` computes mathlib's `addX` at a doubled point —
which is exactly r177's remaining hypothesis `hx`. -/
theorem addX_self_eq_dblQ (hb₂ : (b₂ : ℚ) = W.b₂) (hb₄ : (b₄ : ℚ) = W.b₄)
    (hb₆ : (b₆ : ℚ) = W.b₆) (hb₈ : (b₈ : ℚ) = W.b₈)
    {x y : ℚ} (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) = dblQ b₂ b₄ b₆ b₈ x := by
  rw [dblQ_eq_phiX_div_psiX hb₂ hb₄ hb₆ hb₈ x]
  exact addX_self_eq h hy

end PrincipiaTractalis.DuplicationHeight

#print axioms PrincipiaTractalis.DuplicationFormula.psiX_eq_sq
#print axioms PrincipiaTractalis.DuplicationFormula.addX_self_eq
#print axioms PrincipiaTractalis.DuplicationHeight.dblQ_eq_phiX_div_psiX
#print axioms PrincipiaTractalis.DuplicationHeight.addX_self_eq_dblQ
