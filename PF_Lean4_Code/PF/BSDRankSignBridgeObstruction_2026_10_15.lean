/-
# PF.BSDRankSignBridgeObstruction_2026_10_15

**The rank-sign bridge's defect is the statistic, not the `Unit` carrier —
and the bridge Prop is FALSE for every curve. Machine-checked.**

Rio's 2026-10-15 directive asked to replace `E_11a1 : Type := Unit`
(`BSDRankSignBridge.lean:116`) with a real rank-1 curve via the curve-A
template. Two facts block that as stated, and a third makes it beside the
point:

1. **`E_11a1` is the rank-ZERO curve.** `BSDRankSignBridge.lean:101` says so
   itself: `E_11a1 (rank 0): M_log^Re = +0.170 → predicts rank 0 ✓`, and
   :114 calls it "the smallest rank-0 elliptic curve". Curve 11a1 is
   `y² + y = x³ − x²`, whose Mordell–Weil group is `ℤ/5ℤ` — pure torsion.
   The template concludes `rank ≥ 1` from a NON-torsion point, so on this
   curve it would prove something false. Verified by exact rational
   arithmetic: `(0,0)` has order exactly 5, with orbit
   `(0,0) → (1,−1) → (1,0) → (0,−1) → O`.

2. **The rank-1 cohort is already covered.** `E37a1` (r134), `E43a1` (r135),
   `E53a1` (r136), `E61a1` (r137), `E79a1` (r138), `E83a1` (r139), `E89a1`
   (r140), `E101a1` (r141), `E106a1` (r142), `E389a1` (r143), `E5077a1`
   (r144), plus `curveA` (2026-10-15) — twelve `_rank_ge_one` theorems.
   Another instance would duplicate, not advance.

3. **The real defect is upstream of the carrier.**
   `BSDRankSignBridge.lean:75` reads
   `def M_log_Re_BSD_statistic (E : Type) (X : ℕ) : ℝ := 0`.
   It is a constant function of a bare `Type`, so it cannot depend on any
   curve's arithmetic. Replacing `Unit` by a genuine `WeierstrassCurve ℚ`
   would change no value and discharge no obligation — it would only make
   the file read as repaired.

## What this file proves instead

* `statistic_const_zero` — the statistic is `0` at every `(E, X)`, by `rfl`.
* **`not_fractalBSDRankSignBridge`** — `¬ fractalBSDRankSignBridge E` for
  EVERY `E`. The rank-0 branch demands `0 < M_log^Re = 0`. So the bridge Prop
  is unsatisfiable as defined, and `partial_BSD_via_rank_sign_bridge` is
  vacuously true: its hypothesis has no instances.
* `evidence_prop_is_rfl` — `E_11a1_rank_zero_evidence` is literally `0 = 0`,
  true by `rfl`. Its own source comment says `-- placeholder: real value
  0.170`, and the docstring above it asserts the bracket
  `0.16 ≤ M_log^Re(E_11a1, 2000) ≤ 0.18`. A Prop that is true only because
  its subject is a stub, while documenting a value that would make it false.
* `evidence_contradicts_its_own_bracket` — the documented bracket and the
  Prop as written cannot both hold.

## And the carrier replaced properly

`E11a1 : WeierstrassCurve ℚ := ⟨0, -1, 1, 0, 0⟩` with `P_11a1 = (0,0)` a
genuine nonsingular rational point — real arithmetic in the target language,
in place of a `Unit`. This is offered as the honest replacement for the
placeholder; it is deliberately NOT wired into the statistic, because the
statistic ignores its argument.

## Scope

Nothing here claims `rank(11a1) = 0` — that is classical but needs a descent
UPPER bound, which neither this machinery nor mathlib provides at this pin.
Nothing here claims anything about `L(E,s)`: mathlib has no elliptic-curve
L-function at `eed770a4`, so `ord_{s=1} L(E,s)` is not statable. **No part of
BSD is claimed, proved, or discharged.**

This file DELETES nothing and RENAMES nothing. It is an obstruction/audit
file in the established pattern of `Ch21CompactnessGapObstruction.lean`:
it makes a latent defect into a theorem so it cannot be re-asserted.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-15.
-/

import PF.BSDRankSignBridge
import PF.MordellWeilRankLowerBound_r129

set_option autoImplicit false

namespace PrincipiaTractalis
namespace BSDRankSignBridgeObstruction20261015

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.BSD

noncomputable section

/-! ## §1 — the statistic is a constant -/

/-- **The statistic is identically `0`.** Directly from its definition at
`BSDRankSignBridge.lean:75`. It takes a bare `Type`, so it cannot depend on
any curve's Hecke eigenvalues. -/
theorem statistic_const_zero (E : Type) (X : ℕ) :
    M_log_Re_BSD_statistic E X = 0 := rfl

/-! ## §2 — the bridge Prop is false for every curve -/

/-- **★ `fractalBSDRankSignBridge E` is FALSE for every `E`. ★**

Its rank-0 branch requires `0 < M_log^Re(E, X)` for all large `X`, but the
statistic is constantly `0`, so it requires `0 < 0`. -/
theorem not_fractalBSDRankSignBridge (E : Type) :
    ¬ fractalBSDRankSignBridge E := by
  intro h
  obtain ⟨hzero, _⟩ := h 0
  obtain ⟨X₀, hX⟩ := hzero rfl
  have hpos := hX X₀ le_rfl
  rw [statistic_const_zero] at hpos
  exact lt_irrefl 0 hpos

/-- **Consequence: `partial_BSD_via_rank_sign_bridge` is vacuous.** Its
hypothesis `fractalBSDRankSignBridge E` has no instances, so the theorem
quantifies over an empty set of premises and transmits no BSD content. -/
theorem partial_BSD_hypothesis_unsatisfiable (E : Type) :
    ¬ ∃ _ : fractalBSDRankSignBridge E, True := by
  intro ⟨h, _⟩
  exact not_fractalBSDRankSignBridge E h

/-! ## §3 — the "evidence" Prop is `0 = 0` -/

/-- **The rank-0 evidence Prop is true by `rfl`** — it unfolds to `0 = 0`,
not to anything about curve 11a1. -/
theorem evidence_prop_is_rfl : E_11a1_rank_zero_evidence := rfl

/-- **The documented bracket and the Prop as written are inconsistent.** The
docstring at `BSDRankSignBridge.lean:114-115` asserts
`0.16 ≤ M_log^Re(E_11a1, 2000) ≤ 0.18`, while the Prop beneath it asserts that
same quantity `= 0`. No real number satisfies both. -/
theorem evidence_contradicts_its_own_bracket :
    ¬ ((16 : ℝ) / 100 ≤ M_log_Re_BSD_statistic E_11a1 2000
        ∧ M_log_Re_BSD_statistic E_11a1 2000 ≤ 18 / 100) := by
  intro ⟨hlo, _⟩
  rw [statistic_const_zero] at hlo
  norm_num at hlo

/-! ## §4 — the carrier, replaced by a genuine curve -/

/-- **Curve 11a1 as a real mathlib curve:** `y² + y = x³ − x²`. This is the
honest replacement for `def E_11a1 : Type := Unit`. -/
def E11a1 : WeierstrassCurve ℚ := ⟨0, -1, 1, 0, 0⟩

@[simp] lemma E11a1_a₁ : E11a1.a₁ = 0 := rfl
@[simp] lemma E11a1_a₂ : E11a1.a₂ = -1 := rfl
@[simp] lemma E11a1_a₃ : E11a1.a₃ = 1 := rfl
@[simp] lemma E11a1_a₄ : E11a1.a₄ = 0 := rfl
@[simp] lemma E11a1_a₆ : E11a1.a₆ = 0 := rfl

/-- The affine equation of 11a1 reads `y² + y = x³ − x²`. -/
lemma E11a1_equation_iff (x y : ℚ) :
    E11a1.toAffine.Equation x y ↔ y ^ 2 + y = x ^ 3 - x ^ 2 := by
  rw [Affine.equation_iff]
  show y ^ 2 + 0 * x * y + 1 * y = x ^ 3 + -1 * x ^ 2 + 0 * x + 0 ↔ _
  constructor <;> intro h <;> linarith

/-- `(0,0)` is a nonsingular rational point of 11a1: `a₆ = 0` and
`a₃ = 1 ≠ 0`. -/
theorem P_11a1_nonsingular : E11a1.toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  refine ⟨rfl, Or.inl ?_⟩
  show (1 : ℚ) ≠ 0
  norm_num

/-- **The 5-torsion generator** `P_11a1 = (0,0) ∈ 11a1(ℚ)`. Its order is 5,
with orbit `(0,0) → (1,−1) → (1,0) → (0,−1) → O` (verified by exact rational
arithmetic; the Lean proof of the order is not attempted here). -/
def P_11a1 : E11a1.toAffine.Point := Point.some P_11a1_nonsingular

/-- `negY` on 11a1 is `−y − 1`, so `−(0,0) = (0,−1)` — the fourth multiple of
the generator, which is why `5·(0,0) = O`. -/
lemma E11a1_negY (x y : ℚ) : E11a1.toAffine.negY x y = -y - 1 := by
  show -y - 0 * x - 1 = -y - 1
  ring

/-- `(1,−1)` — the double of the generator — is also a genuine point. -/
theorem two_P_11a1_on_curve : E11a1.toAffine.Equation 1 (-1) := by
  rw [E11a1_equation_iff]
  norm_num

/-- `(0,−1) = −(0,0)` is a genuine point: the fourth multiple. -/
theorem four_P_11a1_on_curve : E11a1.toAffine.Equation 0 (-1) := by
  rw [E11a1_equation_iff]
  norm_num

end

/-! ## §Axiom check -/

#print axioms statistic_const_zero
#print axioms not_fractalBSDRankSignBridge
#print axioms partial_BSD_hypothesis_unsatisfiable
#print axioms evidence_prop_is_rfl
#print axioms evidence_contradicts_its_own_bracket
#print axioms E11a1_equation_iff
#print axioms P_11a1_nonsingular
#print axioms E11a1_negY
#print axioms two_P_11a1_on_curve
#print axioms four_P_11a1_on_curve

end BSDRankSignBridgeObstruction20261015
end PrincipiaTractalis
