/-
# Fujita-Kato 1964 — Small-Data Ball in the Real Ḣ^{1/2} Seminorm

★ 2026-06-10 — Smallness predicate on vector Schwartz fields using
the real Fourier-based vector Sobolev seminorm.

The Fujita-Kato 1964 theorem requires the initial data `u₀` to lie
in a small ball of the homogeneous `Ḣ^{1/2}(ℝ³)` seminorm. This file
defines that small-data ball at the REAL seminorm level (using
`vectorHomogeneousH12SeminormSq` from `SobolevSeminormVector.lean`)
and provides axiom-free witnesses for the contraction argument:

  - The zero field lies in every positive-radius ball.
  - Monotonicity in radius.
  - Quadratic compatibility with the scaling identity.

This replaces the structural-surrogate `SmallH12Ball` predicate
from `FujitaKato1964HomogeneousSobolev.lean` (which used a pointwise
`L^∞` surrogate rather than the integrated Sobolev seminorm) with a
predicate that bites the REAL seminorm.

Axiom-free; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.SobolevSeminormVector

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

/-! ## §1 — Small-data ball predicate -/

/-- **`SmallDataInH12Sq ε u`** — typed Prop encoding the Fujita-Kato
1964 smallness hypothesis at the REAL seminorm level:

  `‖u‖²_{Ḣ^{1/2}} ≤ ε²  ∧  ε > 0`

This is the integrated-Sobolev-seminorm-squared smallness condition,
NOT a pointwise `L^∞` surrogate. Using `vectorHomogeneousH12SeminormSq`
from `SobolevSeminormVector.lean`. -/
def SmallDataInH12Sq (ε : ℝ) (u : VectorSchwartz3C) : Prop :=
  0 < ε ∧ vectorHomogeneousH12SeminormSq u ≤ ε ^ 2

/-! ## §2 — Zero field witness -/

/-- **The zero vector field lies in every positive-radius small-data
ball**: `‖0‖²_{Ḣ^{1/2}} = 0 ≤ ε²`. -/
theorem smallDataInH12Sq_zero (ε : ℝ) (hε : 0 < ε) :
    SmallDataInH12Sq ε (0 : VectorSchwartz3C) := by
  refine ⟨hε, ?_⟩
  rw [vectorHomogeneousH12SeminormSq_zero]
  exact sq_nonneg _

/-! ## §3 — Monotonicity in radius -/

/-- **Enlarging the ball preserves smallness**: if `u` lies in the
`ε`-ball and `ε ≤ ε'`, then `u` lies in the `ε'`-ball. -/
theorem smallDataInH12Sq_mono
    (ε ε' : ℝ) (u : VectorSchwartz3C)
    (hle : ε ≤ ε') (h : SmallDataInH12Sq ε u) :
    SmallDataInH12Sq ε' u := by
  obtain ⟨hε, hball⟩ := h
  have hε' : 0 < ε' := lt_of_lt_of_le hε hle
  have hε_nn : 0 ≤ ε := le_of_lt hε
  refine ⟨hε', ?_⟩
  have hsq : ε ^ 2 ≤ ε' ^ 2 := by
    have hle_nn : 0 ≤ ε' := le_of_lt hε'
    nlinarith [hε_nn, hle]
  linarith

/-! ## §4 — Scaling shrinks the ball -/

/-- **Scaling by `c` with `‖c‖ ≤ 1` keeps the small-data condition**:
if `u` lies in the `ε`-ball and `‖c‖ ≤ 1`, then `c • u` also lies
in the `ε`-ball. -/
theorem smallDataInH12Sq_smul_contract
    (c : ℂ) (ε : ℝ) (u : VectorSchwartz3C)
    (hc : ‖c‖ ≤ 1) (h : SmallDataInH12Sq ε u) :
    SmallDataInH12Sq ε (c • u) := by
  obtain ⟨hε, hball⟩ := h
  refine ⟨hε, ?_⟩
  rw [vectorHomogeneousH12SeminormSq_smul]
  have hnorm_nn : 0 ≤ ‖c‖ := norm_nonneg _
  have hsemi_nn : 0 ≤ vectorHomogeneousH12SeminormSq u :=
    vectorHomogeneousH12SeminormSq_nonneg u
  have hc_sq_le : ‖c‖ ^ 2 ≤ 1 := by nlinarith [hnorm_nn, hc]
  calc ‖c‖ ^ 2 * vectorHomogeneousH12SeminormSq u
      ≤ 1 * vectorHomogeneousH12SeminormSq u :=
        mul_le_mul_of_nonneg_right hc_sq_le hsemi_nn
    _ = vectorHomogeneousH12SeminormSq u := by ring
    _ ≤ ε ^ 2 := hball

/-! ## §5 — Capstone -/

/-- **★ Small-data ball brick capstone ★**

Bundles:
  (a) Zero field is in every positive-radius ball
  (b) Monotonicity in radius
  (c) Scaling by `‖c‖ ≤ 1` keeps the small-data condition

This is the smallness predicate the Fujita-Kato 1964 Picard
contraction operates on. The full contraction proof requires the
bilinear estimate (forthcoming) plus this small-data shell. -/
theorem fujitaKato_small_data_brick_capstone :
    -- (a) Zero in any positive ball
    (∀ ε : ℝ, 0 < ε → SmallDataInH12Sq ε (0 : VectorSchwartz3C)) ∧
    -- (b) Monotonicity in radius
    (∀ ε ε' u, ε ≤ ε' → SmallDataInH12Sq ε u → SmallDataInH12Sq ε' u) ∧
    -- (c) ‖c‖ ≤ 1 shrinks (preserves) the ball
    (∀ (c : ℂ) (ε : ℝ) (u : VectorSchwartz3C),
       ‖c‖ ≤ 1 → SmallDataInH12Sq ε u → SmallDataInH12Sq ε (c • u)) :=
  ⟨smallDataInH12Sq_zero,
   smallDataInH12Sq_mono,
   smallDataInH12Sq_smul_contract⟩

/-! ## §6 — Axiom audit -/

#print axioms smallDataInH12Sq_zero
#print axioms smallDataInH12Sq_mono
#print axioms smallDataInH12Sq_smul_contract
#print axioms fujitaKato_small_data_brick_capstone

end PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
