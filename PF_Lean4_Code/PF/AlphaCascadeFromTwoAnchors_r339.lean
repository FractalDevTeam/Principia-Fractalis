/-
# r339 — The two-anchor cascade, over UNKNOWNS

★ 2026-09-29 — the five open α-values derived, not read off ★

## What was wrong with the previous statement

Every α-value in `PF/CrossMillenniumSharedInvariants.lean` is a literal
definition:

```
noncomputable def α_Poincare : ℝ := 1
noncomputable def α_YM       : ℝ := 2
noncomputable def α_RH       : ℝ := 3 / 2
```

so every "transport identity" is a numeric check on stipulated constants —
`α_YM = α_Poincaré + 1` is `2 = 1 + 1`, proved by `unfold; ring`. Such a theorem
cannot derive anything: the values are already fixed before the identity is
stated. This is what the O-CIRC audit meant by "α-skeleton identities are
assumed, not forced".

## What this file does instead

It quantifies over **nine unknown reals** and supplies the invariants as
**hypotheses**. The two settled anchors then pin the remaining five (seven
values, five open Clay axes). Nothing is unfolded; every conclusion is obtained
from the hypotheses.

This is the same repair applied to the Perelman anchor in
`PF/PoincareAnchorForced_r338.lean`: move from "value stipulated" to "value
forced by an equation with a side condition".

## The honest content

**Claimed.** Given the two anchors and the invariant system, the remaining seven
α-values are *uniquely determined*. The positivity/branch side conditions are
load-bearing: without them the quadratics admit a second root, and §4 exhibits
the wrong roots explicitly.

**Not claimed.** That the invariants themselves are forced. They are premises
here, exactly as they are premises in the corpus. Their justification is the
open question — the invariants were read off the stipulated values, so using
them to re-derive those values is only non-circular once each invariant has an
independent origin (cf. the H₃-Coxeter origin supplied for the Poincaré axis in
`PF/PoincareAlphaFromH3CoxeterHalfArg.lean`).

What this file *does* buy: the assumption set is now explicit and minimal. Seven
values follow from two anchors plus seven named equations. Anyone attacking the
framework now has a finite, visible target.

SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.GoldenRatio

namespace PrincipiaTractalis
namespace AlphaCascadeFromTwoAnchors

open Real

local notation "φ" => Real.goldenRatio

/-! ## §1 — Branch lemmas

Each is an "equation + side condition forces the value" step, the same shape as
`RealisesP (a) := 0 < a ∧ a ^ 2 = 2`. -/

/-- Positive square root is unique. Note `0 ≤ c` is NOT a hypothesis: it follows
from `c = x ^ 2`. Carrying it would be a dead binder. -/
theorem pos_sq_forces {x c : ℝ} (hx : 0 < x) (h : x ^ 2 = c) :
    x = Real.sqrt c := by
  rw [← h, Real.sqrt_sq hx.le]

/-- **Golden-ratio branch.** `x² = x + 1` together with `1 < x` forces `x = φ`.

Proof: `φ` satisfies the same equation, so `x² - φ² = x - φ`, hence
`(x - φ)(x + φ - 1) = 0`. Since `x > 1` and `φ > 1`, the second factor exceeds
`1`, so the first vanishes. -/
theorem golden_branch {x : ℝ} (hx : 1 < x) (h : x ^ 2 = x + 1) : x = φ := by
  have hφ : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  have hφ1 : 1 < φ := Real.one_lt_goldenRatio
  have hfac : (x - φ) * (x + φ - 1) = 0 := by nlinarith [h, hφ]
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith
  · linarith

/-! ## §2 — ★★★ The cascade ★★★ -/

/-- **★★★ `cascade_from_two_anchors` ★★★**

Nine unknown reals. Two settled anchors. Seven invariants as hypotheses. The
remaining seven α-values are forced.

No α constant is unfolded anywhere in the proof — the conclusions come from the
hypotheses alone, which is precisely what the previous formulation could not
claim. -/
theorem cascade_from_two_anchors
    (aPoin aYM aRH aNS aBSD aP aQG aHodge aNP : ℝ)
    -- the two settled external anchors
    (hPoin : aPoin = 1)
    (hNS   : aNS = 3 * Real.pi / 2)
    -- invariants, as premises
    (i7  : aYM = aPoin + 1)
    (i9  : aRH * aYM = 3)
    (i6  : aNS = 2 * aBSD)
    (w22 : aP ^ 2 = aYM)
    (iQG : aQG ^ 2 = aYM * Real.pi)
    (i8  : aHodge ^ 2 = aHodge + 1)
    (iNP : aNP = aHodge + 1 / 4)
    -- branch side conditions
    (hP_pos : 0 < aP) (hQG_pos : 0 < aQG) (hHodge_gt1 : 1 < aHodge) :
    aYM = 2 ∧ aRH = 3 / 2 ∧ aBSD = 3 * Real.pi / 4 ∧
    aP = Real.sqrt 2 ∧ aQG = Real.sqrt (2 * Real.pi) ∧
    aHodge = φ ∧ aNP = φ + 1 / 4 := by
  -- YM from the Poincaré anchor (I7)
  have hYM : aYM = 2 := by rw [i7, hPoin]; norm_num
  -- RH from YM (I9), dividing by aYM = 2 ≠ 0
  have hRH : aRH = 3 / 2 := by rw [hYM] at i9; linarith
  -- BSD from the NS anchor (I6)
  have hBSD : aBSD = 3 * Real.pi / 4 := by rw [hNS] at i6; linarith
  -- P from YM (Wave-22) with the positive branch
  have hP : aP = Real.sqrt 2 := by
    refine pos_sq_forces hP_pos ?_
    rw [w22, hYM]
  -- QG from YM with the positive branch
  have hQG : aQG = Real.sqrt (2 * Real.pi) := by
    refine pos_sq_forces hQG_pos ?_
    rw [iQG, hYM]
  -- Hodge from its own quadratic with the x > 1 branch
  have hHodge : aHodge = φ := golden_branch hHodge_gt1 i8
  -- NP from Hodge
  have hNP : aNP = φ + 1 / 4 := by rw [iNP, hHodge]
  exact ⟨hYM, hRH, hBSD, hP, hQG, hHodge, hNP⟩

/-! ## §3 — The five open Clay axes, extracted

Poincaré and NS are settled externally. These five are the open ones. -/

/-- **α_YM forced.** -/
theorem YM_forced {aPoin aYM : ℝ} (hPoin : aPoin = 1) (i7 : aYM = aPoin + 1) :
    aYM = 2 := by rw [i7, hPoin]; norm_num

/-- **α_RH forced**, given α_YM. -/
theorem RH_forced {aRH aYM : ℝ} (hYM : aYM = 2) (i9 : aRH * aYM = 3) :
    aRH = 3 / 2 := by rw [hYM] at i9; linarith

/-- **α_BSD forced** from the NS anchor. -/
theorem BSD_forced {aNS aBSD : ℝ} (hNS : aNS = 3 * Real.pi / 2)
    (i6 : aNS = 2 * aBSD) : aBSD = 3 * Real.pi / 4 := by
  rw [hNS] at i6; linarith

/-- **α_Hodge forced** by its quadratic and the `> 1` branch. -/
theorem Hodge_forced {aHodge : ℝ} (h1 : 1 < aHodge)
    (i8 : aHodge ^ 2 = aHodge + 1) : aHodge = φ := golden_branch h1 i8

/-- **α_NP forced** from α_Hodge. -/
theorem NP_forced {aNP aHodge : ℝ} (hH : aHodge = φ) (iNP : aNP = aHodge + 1 / 4) :
    aNP = φ + 1 / 4 := by rw [iNP, hH]

/-! ## §4 — The side conditions are load-bearing

Each branch condition excludes a genuine second root. Dropping it does not
weaken the theorem — it makes it false. -/

/-- `x² = 2` alone does not force `√2`: `-√2` also satisfies it. -/
theorem P_branch_needed : (-Real.sqrt 2) ^ 2 = 2 ∧ (-Real.sqrt 2) ≠ Real.sqrt 2 := by
  constructor
  · rw [neg_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  · have : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    intro h; linarith [h ▸ this]

/-- `x² = x + 1` alone does not force `φ`: the conjugate root `ψ = 1 - φ`
satisfies it too, and is negative. -/
theorem Hodge_branch_needed :
    (1 - φ) ^ 2 = (1 - φ) + 1 ∧ (1 - φ) < 1 := by
  have hφ : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  have hφ1 : 1 < φ := Real.one_lt_goldenRatio
  constructor
  · nlinarith [hφ]
  · linarith

/-! ## §5 — Non-vacuity

The hypothesis bundle is satisfiable, so §2 is not vacuously true. -/

theorem cascade_hypotheses_satisfiable :
    ∃ aPoin aYM aRH aNS aBSD aP aQG aHodge aNP : ℝ,
      aPoin = 1 ∧ aNS = 3 * Real.pi / 2 ∧ aYM = aPoin + 1 ∧
      aRH * aYM = 3 ∧ aNS = 2 * aBSD ∧ aP ^ 2 = aYM ∧
      aQG ^ 2 = aYM * Real.pi ∧ aHodge ^ 2 = aHodge + 1 ∧
      aNP = aHodge + 1 / 4 ∧ 0 < aP ∧ 0 < aQG ∧ 1 < aHodge := by
  refine ⟨1, 2, 3/2, 3 * Real.pi / 2, 3 * Real.pi / 4, Real.sqrt 2,
          Real.sqrt (2 * Real.pi), φ, φ + 1/4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · norm_num
  · norm_num
  · ring
  · exact Real.sq_sqrt (by norm_num)
  · exact Real.sq_sqrt (by positivity)
  · exact Real.goldenRatio_sq
  · rfl
  · exact Real.sqrt_pos.mpr (by norm_num)
  · exact Real.sqrt_pos.mpr (by positivity)
  · exact Real.one_lt_goldenRatio

/-! ## §6 — Axiom check -/

#print axioms golden_branch
#print axioms cascade_from_two_anchors
#print axioms YM_forced
#print axioms RH_forced
#print axioms BSD_forced
#print axioms Hodge_forced
#print axioms NP_forced
#print axioms P_branch_needed
#print axioms Hodge_branch_needed
#print axioms cascade_hypotheses_satisfiable

end AlphaCascadeFromTwoAnchors
end PrincipiaTractalis
