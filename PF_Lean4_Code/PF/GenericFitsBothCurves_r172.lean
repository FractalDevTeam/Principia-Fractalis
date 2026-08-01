/-
# PF.GenericFitsBothCurves_r172

★★★ 2026-07-31 — r171's ABSTRACTION FITS BOTH CURVES ★★★

r171 claims that the whole canonical-height construction needs only a
`HeightWindow`: nonnegativity plus `|lognh(R+R) − 4·lognh R| ≤ log κ`.  A claim
like that is worth nothing until it is checked against the instances it was
abstracted from, so this file does exactly that, for **both** curves built by
hand:

  * `window389  : HeightWindow (389a1's lognh) 1728`
  * `window5077 : HeightWindow (5077a1's lognh) 105754`

Each is three fields, and every one is already a theorem in r147 / r156.  If the
abstraction had been drawn in the wrong place, this file would not typecheck.

It also gives, for free and with no new proof, the generic construction's
outputs specialised back to each curve — `canheight_dbl`, the window, the shifted
window — which agree with the hand-built ones.

This validates the design rather than the mathematics: the mathematics is
r147/r156's.  What it establishes is that a third curve needs only its
`lognh_dbl_window`, and gets the rest.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import PF.CanonicalHeightGeneric_r171
import PF.CanonicalHeight389a1_r147
import PF.CanonicalHeight5077a1_r156

namespace PrincipiaTractalis.GenericFitsBothCurves

open PrincipiaTractalis.CanonicalHeightGeneric

/-- 389a1 satisfies r171's hypothesis, with `κ = 1728`. -/
theorem window389 :
    HeightWindow (PrincipiaTractalis.CanonicalHeight389a1.lognh) 1728 where
  nonneg := PrincipiaTractalis.CanonicalHeight389a1.lognh_nonneg
  one_le := by norm_num
  window := PrincipiaTractalis.CanonicalHeight389a1.lognh_dbl_window

/-- 5077a1 satisfies r171's hypothesis, with `κ = 105754`. -/
theorem window5077 :
    HeightWindow (PrincipiaTractalis.CanonicalHeight5077a1.lognh) 105754 where
  nonneg := PrincipiaTractalis.CanonicalHeight5077a1.lognh_nonneg
  one_le := by norm_num
  window := PrincipiaTractalis.CanonicalHeight5077a1.lognh_dbl_window

/-! ## The generic outputs, specialised back -/

theorem dbl389 (R : PrincipiaTractalis.E389a1RankOne.E389a1.toAffine.Point) :
    canheight PrincipiaTractalis.CanonicalHeight389a1.lognh (R + R)
      = 4 * canheight PrincipiaTractalis.CanonicalHeight389a1.lognh R :=
  canheight_dbl window389 R

theorem dbl5077 (R : PrincipiaTractalis.E5077a1RankOne.E5077a1.toAffine.Point) :
    canheight PrincipiaTractalis.CanonicalHeight5077a1.lognh (R + R)
      = 4 * canheight PrincipiaTractalis.CanonicalHeight5077a1.lognh R :=
  canheight_dbl window5077 R

theorem shift5077 (R : PrincipiaTractalis.E5077a1RankOne.E5077a1.toAffine.Point)
    (n : ℕ) :
    |canheight PrincipiaTractalis.CanonicalHeight5077a1.lognh R
        - hseq PrincipiaTractalis.CanonicalHeight5077a1.lognh R n|
      ≤ Real.log 105754 / 3 / 4 ^ n :=
  canheight_window_shift window5077 R n

end PrincipiaTractalis.GenericFitsBothCurves

#print axioms PrincipiaTractalis.GenericFitsBothCurves.window389
#print axioms PrincipiaTractalis.GenericFitsBothCurves.window5077
#print axioms PrincipiaTractalis.GenericFitsBothCurves.dbl5077
#print axioms PrincipiaTractalis.GenericFitsBothCurves.shift5077
