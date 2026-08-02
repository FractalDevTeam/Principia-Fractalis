/-
# PF.DuplicationLogWindowFixed_r179

★★★ 2026-08-01 — CORRECTION TO r177, AND THE USABLE FORM ★★★

## What was wrong with r177

`heightWindow_of_xdbl` asks for

  `hx : ∀ R : G, xco (R + R) = dblQ b₂ b₄ b₆ b₈ (xco R)`

quantified over **all** `R`, including the point at infinity.  The convention
r147/r156 use — and the only sensible one — is `x(O) = 0`, so at `R = O` the
hypothesis demands `0 = dblQ 0 = Φ(0,1)/Ψ(0,1) = −b₈/b₆`.  That is false:

  389a1  `−b₈/b₆ = 3`        5077a1  `−b₈/b₆ = 49/25`

So r177's theorem is *true but vacuous* for an actual point group — its
hypothesis cannot be discharged.  I claimed in the r177 commit that "nothing in
the chain is curve-specific any more"; that claim was premature.  r177 is left
in place (it is not false, and r178 still discharges the interesting part of it),
but **this file supersedes it for use**.

## The fix

Quantify away from zero, and handle `O` by the convention that gives it height
one:

  `hxo : xco 0 = 0`   — whence `nh 0 = max 0 1 = 1` and `lognh 0 = log 1 = 0`
  `hx  : ∀ R ≠ 0, xco (R + R) = dblQ … (xco R)`
  `hΨ  : ∀ R ≠ 0, Ψ(…) ≠ 0`

At `R = O` both sides of the window are zero, so it holds with room to spare.
Away from `O` it is r176/r177 unchanged.

## The honest residue

`hΨ` is genuinely per-curve: `Ψ(x) = 0` says `x` is the `x`-coordinate of a
rational 2-torsion point, so `hΨ` *is* the statement that the curve has no
rational 2-torsion.  That is a real hypothesis about the curve, not an artifact
— 389a1 and 5077a1 satisfy it (r147's `g_ne_zero`, r166b's `D_ne_zero`), and a
curve with rational 2-torsion needs the per-step variant instead.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-01.
-/
import PF.DuplicationLogWindow_r177

namespace PrincipiaTractalis.DuplicationLogWindow

open PrincipiaTractalis.DuplicationBezout PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.CanonicalHeightGeneric

variable {b₂ b₄ b₆ b₈ : ℤ}

@[simp] theorem nh_zero : nh (0 : ℚ) = 1 := by decide

@[simp] theorem lognh_zero : lognh (0 : ℚ) = 0 := by
  simp only [lognh, nh_zero]
  norm_num

theorem log_kappa_nonneg (b₂ b₄ b₆ b₈ : ℤ) :
    0 ≤ Real.log (kappa b₂ b₄ b₆ b₈) := by
  refine Real.log_nonneg ?_
  have : (1 : ℤ) ≤ kappa b₂ b₄ b₆ b₈ :=
    le_trans (one_le_CU b₂ b₄ b₆ b₈) (le_max_left _ _)
  exact_mod_cast this

/-- **`HeightWindow`, in the form that can actually be discharged.**

Supersedes `heightWindow_of_xdbl`, whose `hx` was quantified over all `R`
including the point at infinity and so could never be supplied. -/
theorem heightWindow_of_xdbl_ne_zero {G : Type} [AddCommGroup G]
    (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) (hΔ : Disc b₂ b₄ b₆ b₈ ≠ 0)
    (xco : G → ℚ) (hxo : xco 0 = 0)
    (hΨ : ∀ R : G, R ≠ 0 → Psi b₂ b₄ b₆ (xco R).num ((xco R).den : ℤ) ≠ 0)
    (hx : ∀ R : G, R ≠ 0 → xco (R + R) = dblQ b₂ b₄ b₆ b₈ (xco R)) :
    HeightWindow (fun R : G => lognh (xco R)) (kappa b₂ b₄ b₆ b₈ : ℝ) where
  nonneg R := lognh_nonneg _
  one_le := by
    have : (1 : ℤ) ≤ kappa b₂ b₄ b₆ b₈ :=
      le_trans (one_le_CU b₂ b₄ b₆ b₈) (le_max_left _ _)
    exact_mod_cast this
  window R := by
    by_cases h : R = 0
    · -- At the point at infinity both sides vanish.
      subst h
      rw [add_zero, hxo, lognh_zero]
      simpa using log_kappa_nonneg b₂ b₄ b₆ b₈
    · rw [hx R h]
      exact abs_lognh_dblQ_sub_le hrel hΔ (xco R) (hΨ R h)

/-- The canonical height and its doubling law, for any such group. -/
theorem canheight_dbl_of_xdbl {G : Type} [AddCommGroup G]
    (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) (hΔ : Disc b₂ b₄ b₆ b₈ ≠ 0)
    (xco : G → ℚ) (hxo : xco 0 = 0)
    (hΨ : ∀ R : G, R ≠ 0 → Psi b₂ b₄ b₆ (xco R).num ((xco R).den : ℤ) ≠ 0)
    (hx : ∀ R : G, R ≠ 0 → xco (R + R) = dblQ b₂ b₄ b₆ b₈ (xco R)) (R : G) :
    canheight (fun S : G => lognh (xco S)) (R + R)
      = 4 * canheight (fun S : G => lognh (xco S)) R :=
  canheight_dbl (heightWindow_of_xdbl_ne_zero hrel hΔ xco hxo hΨ hx) R

/-- …and it is the unique such function, by r173. -/
theorem canheight_window_of_xdbl {G : Type} [AddCommGroup G]
    (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) (hΔ : Disc b₂ b₄ b₆ b₈ ≠ 0)
    (xco : G → ℚ) (hxo : xco 0 = 0)
    (hΨ : ∀ R : G, R ≠ 0 → Psi b₂ b₄ b₆ (xco R).num ((xco R).den : ℤ) ≠ 0)
    (hx : ∀ R : G, R ≠ 0 → xco (R + R) = dblQ b₂ b₄ b₆ b₈ (xco R)) (R : G) :
    |canheight (fun S : G => lognh (xco S)) R - lognh (xco R)|
      ≤ Real.log (kappa b₂ b₄ b₆ b₈) / 3 :=
  canheight_window (heightWindow_of_xdbl_ne_zero hrel hΔ xco hxo hΨ hx) R

end PrincipiaTractalis.DuplicationLogWindow

#print axioms PrincipiaTractalis.DuplicationLogWindow.heightWindow_of_xdbl_ne_zero
#print axioms PrincipiaTractalis.DuplicationLogWindow.canheight_dbl_of_xdbl
#print axioms PrincipiaTractalis.DuplicationLogWindow.canheight_window_of_xdbl
