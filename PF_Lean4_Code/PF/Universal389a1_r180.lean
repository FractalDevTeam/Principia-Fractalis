/-
# PF.Universal389a1_r180

★★★ 2026-08-01 — THE UNIVERSAL CHAIN, EXERCISED ON A REAL POINT GROUP ★★★

r174–r179 build the canonical height for any rational Weierstrass curve without
rational 2-torsion.  Until it is instantiated somewhere it is only *claimed* to
be usable — and checking that claim once already exposed r177's unsatisfiable
hypothesis (fixed in r179).  This file instantiates it end to end on
`E389a1.toAffine.Point`, mathlib's actual point group, and derives
`HeightWindow` with **no hand-built duplication estimates at all**.

## What it confirms

r147 built the 389a1 window by hand, over seven stones, reaching
`|lognh (R+R) − 4·lognh R| ≤ log 1728`.  The universal chain reaches the same
statement with `κ = max(CU, CL)` from the coefficients alone.

A pleasant check fell out: r143's hand-written

  `f x = x⁴ + 4x² − 2x + 3`     `g x = 4x³ + 4x² − 8x + 1`

are *exactly* `φ` and `ψ` at `(b₂,b₄,b₆,b₈) = (4,−4,1,−3)`.  The hand computation
and the universal one agree on the nose, which is the strongest evidence the
abstraction is faithful rather than merely type-correct.

## The three obligations, and where each is discharged

* `hxo : X 0 = 0`   — r143 defines `X .zero = 0`, so this is `rfl`.
* `hΨ`              — r143's `g_ne_zero`, which is 389a1 having no rational
                      2-torsion.  It holds unconditionally here, so we prove it
                      for *all* `R`, not just `R ≠ 0`.
* `hx`              — r143's `dbl_x`, which is `Point.add_self_of_Y_ne` plus the
                      duplication formula; r178 shows that formula is `φ/ψ`.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-01.
-/
import PF.DuplicationLogWindowFixed_r179
import PF.DuplicationFormula_r178
import PF.E389a1RankOne_r143

namespace PrincipiaTractalis.Universal389a1

open PrincipiaTractalis.DuplicationBezout PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight PrincipiaTractalis.DuplicationLogWindow
open PrincipiaTractalis.DuplicationFormula
open PrincipiaTractalis.E389a1RankOne
open WeierstrassCurve WeierstrassCurve.Affine

/-! ### The b-invariants of 389a1 -/

theorem b₂_eq : ((4 : ℤ) : ℚ) = (E389a1.toAffine).b₂ := by
  norm_num [WeierstrassCurve.b₂, E389a1]

theorem b₄_eq : ((-4 : ℤ) : ℚ) = (E389a1.toAffine).b₄ := by
  norm_num [WeierstrassCurve.b₄, E389a1]

theorem b₆_eq : ((1 : ℤ) : ℚ) = (E389a1.toAffine).b₆ := by
  norm_num [WeierstrassCurve.b₆, E389a1]

theorem b₈_eq : ((-3 : ℤ) : ℚ) = (E389a1.toAffine).b₈ := by
  norm_num [WeierstrassCurve.b₈, E389a1]

/-! ### r143's hand-written `f`, `g` are the universal `φ`, `ψ` -/

theorem phiX_eq_f (x : ℚ) : phiX (E389a1.toAffine) x = f x := by
  simp only [phiX, f, ← b₄_eq, ← b₆_eq, ← b₈_eq]
  push_cast
  ring

theorem psiX_eq_g (x : ℚ) : psiX (E389a1.toAffine) x = g x := by
  simp only [psiX, g, ← b₂_eq, ← b₄_eq, ← b₆_eq]
  push_cast
  ring

theorem dblQ_eq_fg (x : ℚ) : dblQ 4 (-4) 1 (-3) x = f x / g x := by
  rw [dblQ_eq_phiX_div_psiX b₂_eq b₄_eq b₆_eq b₈_eq x, phiX_eq_f, psiX_eq_g]

/-! ### The three obligations -/

theorem hxo : X 0 = 0 := rfl

/-- `Ψ ≠ 0` — for 389a1 this is `g_ne_zero`, i.e. no rational 2-torsion.
It holds for every point, `0` included. -/
theorem hΨ (R : E389a1.toAffine.Point) :
    Psi 4 (-4) 1 (X R).num ((X R).den : ℤ) ≠ 0 := by
  intro h0
  have hcast := Psi_eq_den_pow_mul b₂_eq b₄_eq b₆_eq (X R)
  rw [h0, psiX_eq_g] at hcast
  have hd : ((X R).den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_ne_zero (X R)
  have : ((X R).den : ℚ) ^ 4 * g (X R) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 hd) (g_ne_zero (X R))
  exact this (by exact_mod_cast hcast.symm)

/-- `X` intertwines doubling with `dblQ`, away from the point at infinity. -/
theorem hx (R : E389a1.toAffine.Point) (hR : R ≠ 0) :
    X (R + R) = dblQ 4 (-4) 1 (-3) (X R) := by
  cases R with
  | zero => exact absurd rfl hR
  | some h =>
      obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
      rw [hadd]
      show x' = _
      rw [hx', dblQ_eq_fg]
      rfl

/-! ### The payoff -/

/-- **`HeightWindow` for 389a1, from the coefficients alone.**

No hand-built duplication estimate is used: `CU` and `CL` come from r175, the
content bound from r174, the crossing from r176, and the group law from r178. -/
theorem window389a1 :
    CanonicalHeightGeneric.HeightWindow
      (fun R : E389a1.toAffine.Point => lognh (X R))
      (kappa 4 (-4) 1 (-3) : ℝ) :=
  heightWindow_of_xdbl_ne_zero
    (by decide) (by rw [disc_389a1]; decide) X hxo (fun R _ => hΨ R) hx

/-- The canonical height's doubling law for 389a1, via the universal chain. -/
theorem canheight_dbl389a1 (R : E389a1.toAffine.Point) :
    CanonicalHeightGeneric.canheight
        (fun S : E389a1.toAffine.Point => lognh (X S)) (R + R)
      = 4 * CanonicalHeightGeneric.canheight
        (fun S : E389a1.toAffine.Point => lognh (X S)) R :=
  CanonicalHeightGeneric.canheight_dbl window389a1 R

end PrincipiaTractalis.Universal389a1

#print axioms PrincipiaTractalis.Universal389a1.phiX_eq_f
#print axioms PrincipiaTractalis.Universal389a1.hx
#print axioms PrincipiaTractalis.Universal389a1.window389a1
#print axioms PrincipiaTractalis.Universal389a1.canheight_dbl389a1
