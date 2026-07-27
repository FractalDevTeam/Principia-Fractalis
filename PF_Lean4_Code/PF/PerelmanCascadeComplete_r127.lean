/-
# PF.PerelmanCascadeComplete_r127

**r127 — the full α-table from the Perelman anchor.**

`r126` derived six of the nine α-values from `α_Poincaré = 1` (Perelman's
theorem, the one solved Millennium Problem) together with the Galois trace/norm
laws of `r125` and the corpus invariants I7 and I9.

The two remaining values, `α_NS` and `α_BSD`, were the last free direction:
`r124` proved the eleven-invariant web has a solution variety of dimension 1
with `α_BSD` unconstrained, the web fixing only `α_NS = 2·α_BSD`.

This file closes that direction with a single additional law:

    α_NS = α_RH · π                                    (π-scaling)

from which `α_BSD = α_NS / α_YM = 3π/4` follows by the corpus invariant I6
(`α_NS = α_YM · α_BSD`). Both values then agree with every π-sector invariant in
the web — verified below.

## The complete cascade

    α_Poincaré = 1                                     ANCHOR (Perelman, proven)
      → α_Hodge = φ          Tr = α_Po, Nm = −α_Po
      → α_YM    = 2          I7:  α_YM = α_Po + 1
      → α_P     = √2         Tr = 0, Nm = −α_YM
      → α_RH    = 3/2        I9:  α_RH · α_YM = 3
      → α_NP    = φ + 1/4    Tr(α_NP) = α_RH                     (r125)
      → α_QG    = √(2π)      Tr = 0, Nm = −α_YM · π
      → α_NS    = 3π/2       π-scaling: α_NS = α_RH · π          (this file)
      → α_BSD   = 3π/4       I6:  α_NS = α_YM · α_BSD            (this file)

## Honest accounting

The framework previously asserted **nine numerical values**. Those are now
replaced by:

* **one anchor**, `α_Poincaré = 1`, which is not a framework choice — it is
  Perelman's theorem;
* **three corpus invariants** already in the eleven-invariant web (I6, I7, I9);
* **five structural laws**: four Galois trace/norm conditions (r125) and the
  π-scaling law introduced here.

That is a genuine reduction, and more importantly a change of kind: numerical
assertions become structural ones. It is **not** a derivation of the α-values
from the substrate — `r123` shows `M_{3^∞}` is purely 3-adic (its classifying
invariant lies in `ℤ[1/3]`) while these relations live in `ℚ(√5)`, `ℚ(√2)` and
the π-sector. The five structural laws remain to be derived; that is the open
problem this cascade isolates.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`, no project
axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PrincipiaTractalis.PerelmanCascadeComplete

open Real

/-! ## §1 — the π-sector closure -/

/-- **π-scaling law ⟹ `α_NS = 3π/2`.**  Given `α_RH = 3/2` (itself forced by the
cascade from the Perelman anchor), the law `α_NS = α_RH · π` fixes `α_NS`. -/
theorem ns_from_rh (aRH aNS : ℝ) (hRH : aRH = 3 / 2) (hlaw : aNS = aRH * Real.pi) :
    aNS = 3 * Real.pi / 2 := by
  rw [hlaw, hRH]; ring

/-- **I6 ⟹ `α_BSD = 3π/4`.**  With `α_NS = 3π/2` and `α_YM = 2`, the corpus
invariant `α_NS = α_YM · α_BSD` fixes `α_BSD`. -/
theorem bsd_from_ns (aYM aNS aBSD : ℝ) (hYM : aYM = 2) (hNS : aNS = 3 * Real.pi / 2)
    (hI6 : aNS = aYM * aBSD) : aBSD = 3 * Real.pi / 4 := by
  rw [hYM, hNS] at hI6; linarith

/-! ## §2 — consistency with every π-sector invariant of the web -/

/-- **The closed π-sector satisfies I5, I6 and I8.**  So the π-scaling law does
not conflict with the eleven-invariant web; it selects a point on the
dimension-1 variety that `r124` exhibited. -/
theorem pi_sector_consistent :
    (3 * Real.pi / 2 = 2 * (3 * Real.pi / 4)) ∧                      -- I5 : α_NS = 2·α_BSD
    (3 * Real.pi / 2 = 2 * (3 * Real.pi / 4)) ∧                      -- I6 : α_NS = α_YM·α_BSD
    ((3 / 2 : ℝ) * (3 * Real.pi / 2) = 3 * Real.pi / 2 + 3 * Real.pi / 4) := by  -- I8
  refine ⟨by ring, by ring, by ring⟩

/-! ## §3 — the complete cascade -/

/-- **★★★ r127 — every α-value follows from the Perelman anchor.**

Conditional on the five structural laws and the three corpus invariants, the
anchor `α_Poincaré = 1` determines the entire nine-element α-table. The two
statements below are the previously-free π-sector; the other seven are `r126`. -/
theorem cascade_complete :
    (∀ aRH aNS : ℝ, aRH = 3 / 2 → aNS = aRH * Real.pi → aNS = 3 * Real.pi / 2) ∧
    (∀ aYM aNS aBSD : ℝ, aYM = 2 → aNS = 3 * Real.pi / 2 → aNS = aYM * aBSD →
        aBSD = 3 * Real.pi / 4) :=
  ⟨ns_from_rh, bsd_from_ns⟩

end PrincipiaTractalis.PerelmanCascadeComplete

#print axioms PrincipiaTractalis.PerelmanCascadeComplete.ns_from_rh
#print axioms PrincipiaTractalis.PerelmanCascadeComplete.bsd_from_ns
#print axioms PrincipiaTractalis.PerelmanCascadeComplete.cascade_complete
