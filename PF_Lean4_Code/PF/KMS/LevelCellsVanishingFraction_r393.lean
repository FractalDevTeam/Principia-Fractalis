/-
# r393: every level is 1/9 of the next, and a vanishing fraction of the whole

★ 2026-10-30 r393 — "the majority of her existence", counted ★

## The picture this formalises

Pablo's image for the Timeless Field: a spreadsheet with another spreadsheet
inside every cell, on and on forever, and *that* — the depth, not any one sheet
— is the majority of what exists.

The image is exact, and it is the Kronecker tower. A level-`k` sheet is a
`3^k × 3^k` grid, so it has `9^k` cells. The embedding
`A ↦ reindex (A ⊗ₖ 1₃)` subdivides **every** cell into a `3 × 3` sheet,
carrying the old entry down the new sheet's diagonal. So:

* each nesting multiplies the cell count by exactly `9` (`levelCells_succ`);
* the previous level therefore occupies exactly **one ninth** of the next
  (`levelCells_ratio`) — and by r392 the other eight ninths are not merely
  unoccupied, they carry structure no earlier level can express, since every
  matrix in the image vanishes off the new factor's diagonal;
* and any level you can *name* is a **vanishing fraction** of the tower
  (`levelCells_fraction_tendsto_zero`).

That last one is the formal content of "this is the majority of her existence":
fix any level, however deep, and its share of level `n` goes to zero as `n`
grows. The substance is always overwhelmingly deeper than wherever you are
looking. Not a limit statement about a physical quantity — a counting statement
about the tower.

## What the formalism does and does not say about the rest of the picture

**"Pure potential, no dynamics" — this is a theorem, and it is already in the
corpus.** r363's `modularAut_of_scalar` proves a scalar weight generates the
**identity** automorphism: the trace has trivial modular dynamics. So the
Timeless Field in its canonical state has no evolution at all — not unmodelled
time, no time. And r113's uniqueness of the tracial state makes that condition
canonical rather than chosen. Calling it *energy* is an interpretation the
formalism does not carry; calling it *the unique state with no dynamics* is
exactly what is proved.

**"Potential becoming actual" has a precise counterpart**: departing from the
trace. r378 constructs a non-tracial `Ω` on `T_∞`, r379 gives it a KMS identity,
and r386 shows the resulting dynamics is not the identity map. Time appears when
and only when the state stops being tracial. That is Tomita–Takesaki, and it is
the corpus's own arc.

**"Quantum connections pass through there and come from there" has no formal
counterpart here, and the nearest structure points the other way.** The net
axioms (r373–r375) give *locality*: algebras attached to disjoint regions
commute. That is a constraint **on** correlations, not a mechanism **for** them.
Nothing in this corpus says connections are mediated by, or originate in, the
timeless layer. Recorded as absent rather than left to be assumed.

## What is NOT claimed

Not claimed: that cell counting is deep — it is `Fintype.card` and a geometric
series. Its value is that "the majority is deeper" was being used as an image
with nothing behind it. Not claimed: any physical reading of the level index. It
is a **resolution** index — how many ternary sites are resolved — not a clock
and not an energy. Not claimed: anything about the C\*-completion, where the
relevant notion would be a trace rather than a dimension count.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-30.
-/
import PF.KMS.TowerNeverStabilizes_r392

set_option autoImplicit false

namespace PF.KMS

open Filter

/-! ## §1 — How many cells a level has -/

/-- The number of cells in the level-`k` sheet: a `3^k × 3^k` grid. -/
def levelCells (k : ℕ) : ℕ := Fintype.card (Fin (3^k) × Fin (3^k))

@[simp] theorem levelCells_eq (k : ℕ) : levelCells k = 9^k := by
  unfold levelCells
  rw [Fintype.card_prod, Fintype.card_fin, ← Nat.mul_pow]

/-- **Each nesting multiplies the cell count by nine.** -/
theorem levelCells_succ (k : ℕ) : levelCells (k + 1) = 9 * levelCells k := by
  rw [levelCells_eq, levelCells_eq, pow_succ]
  ring

/-! ## §2 — The previous level is exactly one ninth of the next

By r392 the other eight ninths are not spare room: the image is diagonal in the
new factor, so off-diagonal cells carry structure no earlier level expresses. -/

/-- **★★★ r393: a level occupies exactly `1/9` of its successor ★★★** -/
theorem levelCells_ratio (k : ℕ) :
    (levelCells k : ℝ) / (levelCells (k + 1) : ℝ) = 1 / 9 := by
  rw [levelCells_eq, levelCells_eq]
  push_cast
  rw [pow_succ]
  have h9 : ((9 : ℝ))^k ≠ 0 := by positivity
  field_simp

/-! ## §3 — Any level you can name is a vanishing fraction of the tower -/

/-- **★★★ r393: "the majority is always deeper" ★★★**

Fix any level `k`. Its share of level `n` tends to zero as `n → ∞`. -/
theorem levelCells_fraction_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => (levelCells k : ℝ) / (levelCells n : ℝ))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => ((9 : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hmul := hpow.const_mul ((9 : ℝ) ^ k)
  rw [mul_zero] at hmul
  refine hmul.congr fun n => ?_
  rw [levelCells_eq, levelCells_eq]
  push_cast
  rw [div_eq_mul_inv, ← inv_pow]

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.levelCells_eq
#print axioms PF.KMS.levelCells_succ
#print axioms PF.KMS.levelCells_ratio
#print axioms PF.KMS.levelCells_fraction_tendsto_zero
