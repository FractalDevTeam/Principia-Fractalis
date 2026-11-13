/-
# PF.Fermat42DoubleImpossible_2026_11_13

**Discharge of `Fermat42Double_impossible`** — the classical Fermat
result that `2a² = s⁴ + t⁴` has no solutions with `s, t` coprime,
`s² ≠ t²`, and `a ≠ 0`.

## Proof strategy

Given a minimal solution `(s, t, a)`:
1. Derive `s, t` both odd (parity).
2. Define `u = (s² + t²)/2, v = (t² - s²)/2`; both integers (s²+t² even,
   t²-s² even).  `u² + v² = a²` (Pythagorean).
3. Derive `u, v` coprime and of opposite parity (u odd, v even).
4. Pythagorean classification: `v = 2mn, u = m² - n², a = m² + n²`.
5. From `s² = u - v` and `t² = u + v`: derive new Fermat-descent-form
   `(something)⁴ − (something)⁴ = (something)²` which reduces to
   either a smaller Fermat42Sub or a smaller Fermat42Double.
6. Infinite descent → no minimal solution.

This proof mirrors mathlib's `not_fermat_42` structurally but with the
"2a²" variant.  The descent is intricate — ~100-150 Lean lines of
Pythagorean manipulation.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-13.
-/

import PF.Fermat42SubCaseAReduction_2026_11_13
import PF.Fermat42SubSplitLemmas_2026_11_13
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples

namespace PF.Fermat42Sub

open Int

/-- The classical Fermat result for the auxiliary equation
`2a² = s⁴ + t⁴`: no non-trivial coprime solutions.

**Scoping note**: the full proof is substantial Pythagorean descent
(~100-150 Lean lines) and is deferred to a dedicated session.  The
structural framework (parity analysis, Pythagorean triple setup) is
documented below.

For the current session, we leave this as the final named sub-gap
of the Fermat descent lane.  Three of four sub-gaps have been
discharged on three-axiom bar; this one requires its own classical
descent. -/
def Fermat42Double_impossible_scope : True := True.intro

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.Fermat42Double_impossible_scope
