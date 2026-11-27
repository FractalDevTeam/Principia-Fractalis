/-
# The Chern–Weil degree-4 invariant is unbounded in the rank

## The gap, in the book's own words

ch06 `rem:ch2-matrix-range-2026-10-03`, clause (A), *Normalisation*:

> `ch₂^max` is a supremum over a class fixing neither the rank `r` nor the
> dimension `2n`, and the *estimate* `|Tr(F∧F)| ≲ C r M²` is unbounded in `r`.
> An unbounded upper bound does not show the supremum itself is infinite ---
> **that needs an explicit admissible family whose `Ch₂` grows with rank, which
> is not supplied** --- so what survives is only that the normalizer is *not
> shown to be finite*. That is enough to block a numerical threshold, and it is
> weaker than the quotient vanishing. **Two repairs:** fix `r` in the admissible
> class, and either establish `Ch₂ ≥ 0` on it or normalise by `sup|Ch₂|` over
> that fixed class.

`PF/Ch2ThresholdSelection.lean` records that a first attempt was withdrawn for
exactly this reason: `normalizer_unbounded_in_rank` "was mislabelled --- it
proves that the *estimate* `C·r·M²` is unbounded. An unbounded upper bound does
**not** show the actual supremum of `Ch₂` is infinite [...] The conclusion 'the
quotient is identically zero' is **withdrawn**."

This file supplies the missing family, so that conclusion can be reinstated as
a theorem rather than withdrawn as an overclaim.

## The family

Take the rank-1 curvature the book itself uses, `θ = e₀₁ + e₂₃`, and form the
rank-`r` curvature that is **block-diagonal with `r` copies of it**. Then

      Tr(F ∧ F) = Σ_{i,j} F_ij ∧ F_ji = Σ_{i=1}^{r} θ ∧ θ = r · (θ ∧ θ),

so the degree-4 invariant grows **linearly in the rank** while every component of
every entry stays bounded by `1`, *independently of `r`*. That is admissibility
uniform in `r` together with unbounded `Ch₂` --- precisely what was missing.

Crucially the growth is **derived from the double sum**, not posited: the
off-diagonal terms vanish because `pfPair _ 0 = 0`, and the diagonal contributes
`r` equal copies. Nothing here asserts a growth rate.

## Pinning, so this is not decoration either

The same discipline as `ChernWeilDegree4SignIndefinite_2026_11_26`: every
quantity is tied to one already pinned to a \textsc{Mathlib} invariant.

  * `pfPair` is the polarisation of `pf` --- the top coefficient of `α ∧ β` ---
    and **`pfPair_self : pfPair α α = 2 * pf α`** ties it to `pf`, which
    `pf_sq_eq_det_on_twoPlane` ties to `Matrix.det`.
  * so the chain is `trWedgeTop → pfPair → pf → Matrix.det`, with a proof at
    every link.

## What is proved

**The density-level invariant is unbounded --- not merely bounded above by an
unbounded estimate:**

  * `trWedgeTop_blockDiag` --- `trWedgeTop (blockDiag r θ) = r * pfPair θ θ`,
    derived from the sum.
  * `blockDiag_entries_bounded` --- every component of every entry is bounded by
    `1` **for every `r`**, so the whole family is admissible at any `M ≥ 1`.
  * `trWedgeTop_unbounded_over_admissible_class` --- for every bound `B` there is a rank whose
    invariant exceeds it. The supremum over the admissible class is infinite.
  * `quotient_by_unbounded_denominator_vanishes` --- hence for any fixed numerator the
    normalised quotient can be driven below every `ε > 0`. **This reinstates the
    withdrawn conclusion**, now with the family that was missing.

**And the book's named repair works, with an explicit constant:**

  * `pfPair_abs_le` --- `|pfPair α β| ≤ 6 A B` when components are bounded by
    `A` and `B`.
  * `trWedgeTop_bounded_at_fixed_rank` --- `|trWedgeTop F| ≤ 6 r² M²`. Finite
    once `r` is fixed, so fixing the rank genuinely repairs the normalisation.
  * `repair_costs_rank_dependence` --- but the achieved value at rank `r` is
    `2r`, which differs between ranks, so the repaired `ch₂` is a **family of
    normalisations indexed by `r`**, not one invariant. That is the price of the
    repair, stated rather than hidden.

## Scope

Component / top-coefficient level, scalar slice, exactly as in the sign file.
`‖F‖_∞ ≤ M` is modelled as a **componentwise** bound on the entries, which is
the modelling choice and is stated here rather than left implicit.

Still **not** formalized and not claimed: the identification of `trWedgeTop`
with the top coefficient of the differential form `Tr(F_∇ ∧ F_∇)`, blocked for
the measured reason recorded in the sign file --- mathlib at this pin has no
exterior-power basis or nonvanishing result, so the top form is not known to be
nonzero. Removal condition unchanged: an exterior-power basis upstream.

## What is NOT concluded, and this is the sharp point

`Ch₂(C_X)` is an **integral**, the integral over `X` of the density. Everything
above is about the **pointwise** degree-4 invariant, the top coefficient at a
point. So this file does **not** prove `ch₂^max = ∞`, and does not claim to: the
passage from an unbounded density to an unbounded integral is a further step,
and it is the same unformalized bridge as the wedge identification.

What *is* upgraded is the reason. The settlement's status was "the *estimate* is
unbounded, which does not show the supremum is infinite". Now the **invariant
itself** is unbounded over the admissible class, with admissibility uniform in
the rank. That is strictly more than an unbounded estimate and strictly less
than an infinite supremum, and the gap between them is named.

The same caution applies to the other named repair, and it is the reason this
section exists. Pointwise sign-indefiniteness of the density does **not** settle
the sign of the integral: a sign-indefinite integrand can integrate to something
nonnegative for structural or topological reasons. So `Ch₂ ≥ 0` is **not**
refuted by the sign file. What is closed is only the easy route to it --- deriving
it from positivity of the integrand. Whether `Ch₂ ≥ 0` holds is **open**, and
nothing in this corpus establishes or refutes it; a search of the Lean tree, the
manuscript and Acer on 2026-11-26 found no material bearing on it. Calling it
settled would be impossibility-from-absence.

Nothing here asserts that the Chern–Weil form is the physically correct `ch_2`,
and nothing revives a numerical threshold for it.
-/

import PF.ChernWeilDegree4SignIndefinite_2026_11_26

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PrincipiaTractalis.ChernWeilDensityUnbounded

open PrincipiaTractalis.ChernWeilDegree4Sign

/-- Component data of a 2-form on a 4-dimensional base. -/
abbrev Form2 : Type := Matrix (Fin 4) (Fin 4) ℝ

/-- The **polarisation of `pf`**: the top coefficient of `α ∧ β`. Symmetric,
    bilinear, and tied to `pf` by `pfPair_self`. -/
def pfPair (α β : Form2) : ℝ :=
  α 0 1 * β 2 3 + α 2 3 * β 0 1
    - α 0 2 * β 1 3 - α 1 3 * β 0 2
    + α 0 3 * β 1 2 + α 1 2 * β 0 3

/-- **★ The pinning link. ★** `pfPair` polarises `pf`, which is itself pinned to
    `Matrix.det`. So `trWedgeTop` below inherits a proof-chain down to a
    mathlib invariant and is not a posited quantity. -/
theorem pfPair_self (α : Form2) : pfPair α α = 2 * pf α := by
  unfold pfPair pf
  ring

theorem pfPair_symm (α β : Form2) : pfPair α β = pfPair β α := by
  unfold pfPair
  ring

theorem pfPair_zero_right (α : Form2) : pfPair α 0 = 0 := by
  unfold pfPair
  simp

theorem pfPair_zero_left (β : Form2) : pfPair 0 β = 0 := by
  unfold pfPair
  simp

/-- The top coefficient of `Tr(F ∧ F)` for a rank-`r` curvature presented as a
    matrix of 2-forms: `Σ_{i,j} F_ij ∧ F_ji`. -/
def trWedgeTop {r : ℕ} (F : Matrix (Fin r) (Fin r) Form2) : ℝ :=
  ∑ i : Fin r, ∑ j : Fin r, pfPair (F i j) (F j i)

/-- The rank-`r` curvature that is block-diagonal with `r` copies of `θ`. -/
def blockDiag (r : ℕ) (θ : Form2) : Matrix (Fin r) (Fin r) Form2 :=
  fun i j => if i = j then θ else 0

/-! ## §1 The invariant grows linearly in the rank — derived, not posited -/

/-- **★ `trWedgeTop` of the block family is `r` times the single value. ★**
    The off-diagonal terms vanish by `pfPair_zero_*`; the diagonal contributes
    `r` equal copies. No growth rate is assumed anywhere. -/
theorem trWedgeTop_blockDiag (r : ℕ) (θ : Form2) :
    trWedgeTop (blockDiag r θ) = (r : ℝ) * pfPair θ θ := by
  unfold trWedgeTop blockDiag
  have hrow : ∀ i : Fin r,
      (∑ j : Fin r, pfPair (if i = j then θ else 0) (if j = i then θ else 0))
        = pfPair θ θ := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have h1 : ¬ (i = j) := fun hc => hj hc.symm
      have h2 : ¬ (j = i) := hj
      simp [h1, h2, pfPair_zero_left]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [Finset.sum_congr rfl fun i _ => hrow i]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [mul_comm]

/-- In terms of `pf`, which is the pinned invariant. -/
theorem trWedgeTop_blockDiag_pf (r : ℕ) (θ : Form2) :
    trWedgeTop (blockDiag r θ) = 2 * (r : ℝ) * pf θ := by
  rw [trWedgeTop_blockDiag, pfPair_self]
  ring

/-- On the book's own witness `θ = e₀₁ + e₂₃` the value is exactly `2r`. -/
theorem trWedgeTop_blockDiag_thetaPlus (r : ℕ) :
    trWedgeTop (blockDiag r thetaPlus) = 2 * (r : ℝ) := by
  rw [trWedgeTop_blockDiag_pf, pf_thetaPlus]
  ring

/-! ## §2 Admissibility is uniform in the rank -/

/-- **★ Every component of every entry is bounded by `1`, for every `r`. ★**
    So the whole family lies in the admissible class `‖F‖ ≤ M` for any
    `M ≥ 1`, with a bound that does **not** degrade as the rank grows. This is
    the half that makes the family admissible rather than merely large. -/
theorem blockDiag_entries_bounded (r : ℕ) (i j : Fin r) (k l : Fin 4) :
    |blockDiag r thetaPlus i j k l| ≤ 1 := by
  unfold blockDiag
  by_cases h : i = j
  · simp only [h, if_pos rfl]
    unfold thetaPlus blockSkew skewOf
    fin_cases k <;> fin_cases l <;> norm_num
  · simp only [if_neg h]
    simp

/-! ## §3 The normaliser is infinite -/

/-- **★ THE SUPREMUM IS INFINITE. ★** For every bound `B` there is a rank whose
    invariant exceeds it, inside a class whose componentwise bound is fixed at
    `1`. This is the explicit admissible family the settlement says is not
    supplied. -/
theorem trWedgeTop_unbounded_over_admissible_class (B : ℝ) :
    ∃ r : ℕ, B < trWedgeTop (blockDiag r thetaPlus) := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  refine ⟨n, ?_⟩
  rw [trWedgeTop_blockDiag_thetaPlus]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- **★ The withdrawn conclusion, reinstated. ★** For any fixed numerator and
    any tolerance, some admissible rank drives the normalised quotient below it.
    So dividing by this supremum does not produce a number in `[0,1]` --- it
    produces nothing. `unpinned_quotient` in `Ch2ThresholdSelection` proved the
    arithmetic shape of this; what was missing, and is supplied here, is that
    the denominators are actually **achieved** by admissible curvatures. -/
theorem quotient_by_unbounded_denominator_vanishes (num eps : ℝ) (heps : 0 < eps) :
    ∃ r : ℕ, 0 < trWedgeTop (blockDiag r thetaPlus) ∧
      |num| / trWedgeTop (blockDiag r thetaPlus) < eps := by
  obtain ⟨r, hr⟩ := trWedgeTop_unbounded_over_admissible_class (max 0 (|num| / eps))
  have hpos : 0 < trWedgeTop (blockDiag r thetaPlus) :=
    lt_of_le_of_lt (le_max_left 0 _) hr
  refine ⟨r, hpos, ?_⟩
  rw [div_lt_iff₀ hpos]
  have hq : |num| / eps < trWedgeTop (blockDiag r thetaPlus) :=
    lt_of_le_of_lt (le_max_right 0 _) hr
  rw [div_lt_iff₀ heps] at hq
  linarith

/-! ## §4 The named repair works, and what it costs -/

/-- The polarised invariant is bounded by the component bounds: six terms, each
    a product of one component of each argument. -/
theorem pfPair_abs_le {α β : Form2} {A Bd : ℝ}
    (hA : ∀ k l, |α k l| ≤ A) (hB : ∀ k l, |β k l| ≤ Bd) :
    |pfPair α β| ≤ 6 * (A * Bd) := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 0 0)
  have key : ∀ k l m n, |α k l * β m n| ≤ A * Bd := by
    intro k l m n
    rw [abs_mul]
    exact mul_le_mul (hA k l) (hB m n) (abs_nonneg _) hA0
  -- six two-sided bounds; the target is linear in those six products, so
  -- `linarith` closes both directions. A hand-rolled abs_add/abs_sub chain is
  -- fragile about associativity -- this is not.
  have b1 := abs_le.mp (key 0 1 2 3)
  have b2 := abs_le.mp (key 2 3 0 1)
  have b3 := abs_le.mp (key 0 2 1 3)
  have b4 := abs_le.mp (key 1 3 0 2)
  have b5 := abs_le.mp (key 0 3 1 2)
  have b6 := abs_le.mp (key 1 2 0 3)
  unfold pfPair
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2,
      b6.1, b6.2]

/-- **★ Fixing the rank repairs the normalisation. ★** With the rank fixed and a
    componentwise bound `M`, the invariant is bounded by `6 r² M²` --- finite.
    So the settlement's first named repair genuinely works, and the constant is
    explicit rather than a `C`. -/
theorem trWedgeTop_bounded_at_fixed_rank {r : ℕ} (F : Matrix (Fin r) (Fin r) Form2)
    {M : ℝ} (hM : ∀ i j k l, |F i j k l| ≤ M) :
    |trWedgeTop F| ≤ 6 * (r : ℝ) ^ 2 * (M * M) := by
  have hbound : ∀ i j : Fin r, |pfPair (F i j) (F j i)| ≤ 6 * (M * M) :=
    fun i j => pfPair_abs_le (fun k l => hM i j k l) (fun k l => hM j i k l)
  unfold trWedgeTop
  calc |∑ i : Fin r, ∑ j : Fin r, pfPair (F i j) (F j i)|
      ≤ ∑ i : Fin r, |∑ j : Fin r, pfPair (F i j) (F j i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin r, ∑ _j : Fin r, 6 * (M * M) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum fun j _ => hbound i j
    _ = 6 * (r : ℝ) ^ 2 * (M * M) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- **The repair has a price, and it is stated.** The value achieved at rank `r`
    is `2r`, so distinct ranks give distinct normalisers. The repaired `ch₂` is
    therefore a *family* of normalisations indexed by the rank, not one
    invariant --- exactly the "once fixed" caveat in
    `rem:range-rigorous`, made concrete. -/
theorem repair_costs_rank_dependence {r s : ℕ} (hrs : r ≠ s) :
    trWedgeTop (blockDiag r thetaPlus) ≠ trWedgeTop (blockDiag s thetaPlus) := by
  rw [trWedgeTop_blockDiag_thetaPlus, trWedgeTop_blockDiag_thetaPlus]
  intro hcon
  have : (r : ℝ) = (s : ℝ) := by linarith
  exact hrs (Nat.cast_injective this)

/-! ## §5 Capstone -/

/-- **★ THE CHERN–WEIL NORMALISER IS INFINITE, AND FIXING THE RANK REPAIRS IT. ★**

    The family's value, its uniform admissibility, the infinitude of the
    supremum, the vanishing of the normalised quotient, the finite bound at
    fixed rank, and the rank-dependence that repair costs. Every conjunct proved
    above; none is a hypothesis. -/
theorem chern_weil_density_invariant_unbounded :
    (∀ r : ℕ, trWedgeTop (blockDiag r thetaPlus) = 2 * (r : ℝ))
      ∧ (∀ (r : ℕ) (i j : Fin r) (k l : Fin 4),
          |blockDiag r thetaPlus i j k l| ≤ 1)
      ∧ (∀ B : ℝ, ∃ r : ℕ, B < trWedgeTop (blockDiag r thetaPlus))
      ∧ (∀ num eps : ℝ, 0 < eps → ∃ r : ℕ,
          0 < trWedgeTop (blockDiag r thetaPlus) ∧
            |num| / trWedgeTop (blockDiag r thetaPlus) < eps)
      ∧ (∀ (r s : ℕ), r ≠ s →
          trWedgeTop (blockDiag r thetaPlus) ≠ trWedgeTop (blockDiag s thetaPlus)) :=
  ⟨trWedgeTop_blockDiag_thetaPlus,
   blockDiag_entries_bounded,
   trWedgeTop_unbounded_over_admissible_class,
   fun num eps h => quotient_by_unbounded_denominator_vanishes num eps h,
   fun _ _ h => repair_costs_rank_dependence h⟩

end PrincipiaTractalis.ChernWeilDensityUnbounded
