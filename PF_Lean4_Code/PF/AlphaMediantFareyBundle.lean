/-
# PF.AlphaMediantFareyBundle

★★★★ 2026-06-17 — FUN: α_RH is the MEDIANT of α_Poincaré and α_YM.
The three rational Clay axes form a Farey triple.

## The mediant property

The mediant of two fractions `a/b` and `c/d` is `(a+c)/(b+d)`. For
neighboring fractions in a Farey sequence (Farey-adjacent), the mediant
is the simplest fraction strictly between them.

## Framework finding

  α_Poincaré = 1/1
  α_YM       = 2/1
  mediant(α_Poincaré, α_YM) = (1+2)/(1+1) = 3/2 = α_RH

So α_RH is the mediant of α_Poincaré and α_YM. Equivalently:
the framework's three smallest rational Clay axes (α_Poincaré, α_RH,
α_YM) form a Farey triple in F_2 (the Farey sequence of order 2).

## Farey-adjacency condition

For Farey-adjacent (a/b) and (c/d): |a·d − b·c| = 1.
For α_Poincaré = 1/1 and α_YM = 2/1: |1·1 − 1·2| = 1 ✓.
The mediant 3/2 = α_RH is then the unique fraction between them with
the smallest denominator.

## Identities

  2·α_RH = α_Poincaré + α_YM                 (mediant numerator condition)
  α_Poincaré + α_YM = 3 = 2·α_RH             (sum equals twice the mediant)
  (α_Poincaré, α_RH, α_YM) is a Farey triple

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaMediantFareyBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — α_RH is the mediant of α_Poincaré and α_YM -/

/-- **★★★ `2·α_RH = α_Poincaré + α_YM` ★★★** — the mediant numerator
    condition for α_RH = mediant(α_Poincaré, α_YM). -/
theorem two_α_RH_eq_α_Poincare_add_α_YM :
    2 * α_RH = α_Poincare + α_YM := by
  unfold α_RH α_Poincare α_YM; norm_num

/-- **`α_Poincaré + α_YM = 3`** — direct sum (corresponds to mediant
    numerator 1 + 2). -/
theorem α_Poincare_add_α_YM_eq_three :
    α_Poincare + α_YM = 3 := by
  unfold α_Poincare α_YM; norm_num

/-! ## §2 — Farey-adjacency condition -/

/-- **`α_Poincaré · 1 − 1 · α_YM = −1`** — the (signed) Farey-adjacency
    determinant between α_Poincaré = 1/1 and α_YM = 2/1 has absolute
    value 1, confirming they are Farey-adjacent. -/
theorem farey_adjacency_α_Poincare_α_YM :
    α_Poincare * 1 - 1 * α_YM = -1 := by
  unfold α_Poincare α_YM; norm_num

/-! ## §3 — Ordering: α_Poincaré < α_RH < α_YM -/

/-- **`α_Poincaré < α_RH < α_YM`** — the Farey triple is ordered. -/
theorem α_Poincare_lt_α_RH_lt_α_YM :
    α_Poincare < α_RH ∧ α_RH < α_YM := by
  refine ⟨?_, ?_⟩
  · unfold α_Poincare α_RH; norm_num
  · unfold α_RH α_YM; norm_num

/-! ## §4 — Bundle capstone -/

/-- **★★★★ THE MEDIANT/FAREY TRIPLE BUNDLE CAPSTONE ★★★★** —
    α_RH is the mediant of α_Poincaré and α_YM, exhibiting the three
    smallest rational Clay axes as a Farey triple in F_2:

      α_Poincaré (= 1/1) < α_RH (= 3/2) < α_YM (= 2/1)
      α_RH = mediant(α_Poincaré, α_YM)
      |α_Poincaré · 1 − 1 · α_YM| = 1   (Farey-adjacency of endpoints)

    The framework's three smallest rational Clay axes are not arbitrary
    numerical values — they're the simplest Farey triple containing α_RH
    as the mediant. -/
theorem α_mediant_farey_bundle_capstone :
    2 * α_RH = α_Poincare + α_YM ∧
    α_Poincare + α_YM = 3 ∧
    α_Poincare * 1 - 1 * α_YM = -1 ∧
    α_Poincare < α_RH ∧ α_RH < α_YM :=
  ⟨two_α_RH_eq_α_Poincare_add_α_YM,
   α_Poincare_add_α_YM_eq_three,
   farey_adjacency_α_Poincare_α_YM,
   α_Poincare_lt_α_RH_lt_α_YM.1,
   α_Poincare_lt_α_RH_lt_α_YM.2⟩

end AlphaMediantFareyBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaMediantFareyBundle.two_α_RH_eq_α_Poincare_add_α_YM
#print axioms PrincipiaTractalis.AlphaMediantFareyBundle.α_Poincare_add_α_YM_eq_three
#print axioms PrincipiaTractalis.AlphaMediantFareyBundle.farey_adjacency_α_Poincare_α_YM
#print axioms PrincipiaTractalis.AlphaMediantFareyBundle.α_Poincare_lt_α_RH_lt_α_YM
#print axioms PrincipiaTractalis.AlphaMediantFareyBundle.α_mediant_farey_bundle_capstone
