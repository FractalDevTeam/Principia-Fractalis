/-
# Consciousness relativity: the response is ONE-SIDED, and the corpus model is not

**Spine arrow.** `emergent locality -> modified relativity -> churn`. This file
is the kinematic content of the middle arrow: what the consciousness sector
contributes to the modified field equation as a function of *realized* rather
than nominal potential.

## The stated structure

Pablo Cohen, 2026-11-26, stating the central idea of consciousness relativity:

> Human consciousness, if it doesn't get carried to its fullest expression, is
> a waste of energy. Essentially a human that didn't reach maximum potential,
> it was not allowed to gain acceleration in order to build force. And
> eventually gravity acting like mass or mass acting like gravity. Going
> backwards also leads to nothing. But when you do the positive side, maybe
> there's an unexpected, serendipitous event.

Read as a specification on the response function, that is three branches:

  * unrealized potential  (`ch2 = 0`)  -> no contribution
  * reversed              (`ch2 < 0`)  -> **also** no contribution
  * realized              (`ch2 > 0`)  -> strict contribution, unbounded above

A function with those three branches is **one-sided**: it is neither odd nor
even, and it is identically zero on a half-line.

## The finding

The corpus does not implement that specification, and this is not a matter of
taste --- the two disagree on the entire negative branch, provably.
`Wave58.T_consciousness_density` is

    T(ch2) = ch2 * (78 * pi * 0.95 * 1.1875)

which is **linear, hence ODD**: `T(-x) = -T(x)` for every `x`
(`density_is_odd` below). And `Wave58.G_munu_modified` is strictly decreasing
in its consciousness slot. So under the model as written:

  * `ch2 > 0` lowers the modified-Einstein residual  (already proved upstream,
    `GeneralRelativityContentful.consciousness_strictly_modifies_residual`)
  * `ch2 = 0` leaves it unchanged                    (already proved upstream)
  * `ch2 < 0` *raises* it, by exactly the mirror amount
    (`linear_model_rewards_backwards` below)

The third branch is the defect. Going backwards does not "lead to nothing"
under the linear model; it produces a strictly opposite effect of equal size.
A model that is odd cannot express a specification that is one-sided.

## What is proved here

`realizedDensity` is the rectified carrier: the same coupling, applied to the
*expressed* potential `max ch2 0`. It satisfies the specification exactly, and
it is NOT a weakening of the existing model --- `realizedDensity_eq_of_nonneg`
shows the two agree on the whole forward branch, where all of the upstream
results live. Nothing proved upstream is lost. What changes is only the branch
the upstream results never covered.

The separation is exhibited, not assumed: `models_differ_at_minus_one` gives an
explicit point where the two carriers disagree, so the choice between them is
substantive rather than cosmetic.

The last theorem is the serendipity clause, and it is the sharpest statement in
the file. `forward_gain_unbounded` says the forward branch reaches *every* level
below: for any target `L` there is a realization whose residual undercuts it.
`backward_reaches_exactly_one_value` says the backward branch attains a single
value and never anything lower. So the asymmetry is not decorative --- one
branch is cofinal downward and the other is a point.

## Scope, stated plainly

The rectification is an **ASSERTED structural hypothesis** --- Pablo's, quoted
above --- not a derived result. Nothing here derives it from the substrate, and
nothing here is evidence about consciousness, which the book records as
EMPIRICAL / UNTESTED. What *is* proved is the mathematics: that the
specification and the corpus model are incompatible on the negative branch,
that the rectified carrier meets the specification, that it agrees with the
existing model wherever the existing results apply, and that the two branches
differ in reachability. Those are theorems about the two functions, and they
hold whatever one believes about the physics.

No pseudo-Riemannian geometry is used or needed: every statement is about the
scalar slice, which is why this arrow is reachable at a mathlib pin that has
Lorentzian 0 files, PseudoRiemannian 0, LeviCivita 0, RicciTensor 0 and
MetricTensor 0 (measured 2026-11-26).
-/

import PF.GeneralRelativityContentful_2026_10_08

set_option autoImplicit false

namespace PrincipiaTractalis.ConsciousnessRelativityAsymmetry

open Real

/-! ## §0 The coupling constant, isolated -/

/-- The consciousness coupling appearing in `Wave58.T_consciousness_density`,
    named so that its positivity can be used rather than re-derived. -/
noncomputable def consciousnessCoupling : ℝ := 78 * Real.pi * 0.95 * 1.1875

theorem consciousnessCoupling_pos : 0 < consciousnessCoupling := by
  unfold consciousnessCoupling
  positivity

/-- The upstream density is exactly `ch2` times that coupling. Definitional. -/
theorem density_eq (ch2 : ℝ) :
    Wave58.T_consciousness_density ch2 = ch2 * consciousnessCoupling := rfl

/-! ## §1 The corpus model is ODD, so it cannot be one-sided -/

/-- **The existing model is odd.** `T(-x) = -T(x)`, for every `x`. This is the
    obstruction: an odd function is zero at the origin and then strictly
    antisymmetric, so it can never be identically zero on a half-line unless it
    is identically zero everywhere. -/
theorem density_is_odd (ch2 : ℝ) :
    Wave58.T_consciousness_density (-ch2) = -(Wave58.T_consciousness_density ch2) := by
  rw [density_eq, density_eq]
  ring

/-- Under the existing model a reversed potential gives a strictly negative
    contribution --- not nothing. -/
theorem density_neg_of_neg {ch2 : ℝ} (h : ch2 < 0) :
    Wave58.T_consciousness_density ch2 < 0 := by
  rw [density_eq]
  exact mul_neg_of_neg_of_pos h consciousnessCoupling_pos

/-! ## §2 The rectified carrier -/

/-- **The realized-potential density.** The same coupling, applied to the
    expressed potential. Potential that is not carried to expression
    contributes nothing, and neither does reversal. -/
noncomputable def realizedDensity (ch2 : ℝ) : ℝ :=
  Wave58.T_consciousness_density (max ch2 0)

/-- **Nothing is lost.** On the whole forward branch the rectified carrier IS
    the existing model, so every upstream result --- all of which assume
    `0 < ch2` or `ch2 = 0` --- transfers unchanged. This is what makes the
    rectification a repair rather than a replacement. -/
theorem realizedDensity_eq_of_nonneg {ch2 : ℝ} (h : 0 ≤ ch2) :
    realizedDensity ch2 = Wave58.T_consciousness_density ch2 := by
  unfold realizedDensity
  rw [max_eq_left h]

/-- **Going backwards leads to nothing.** The specification's second branch. -/
theorem realizedDensity_eq_zero_of_nonpos {ch2 : ℝ} (h : ch2 ≤ 0) :
    realizedDensity ch2 = 0 := by
  unfold realizedDensity
  rw [max_eq_right h, density_eq, zero_mul]

/-- Unrealized potential contributes nothing. The specification's first branch,
    and a special case of the second. -/
theorem realizedDensity_zero : realizedDensity 0 = 0 :=
  realizedDensity_eq_zero_of_nonpos le_rfl

/-- Realized potential contributes strictly. The specification's third
    branch. -/
theorem realizedDensity_pos_of_pos {ch2 : ℝ} (h : 0 < ch2) :
    0 < realizedDensity ch2 := by
  rw [realizedDensity_eq_of_nonneg h.le, density_eq]
  exact mul_pos h consciousnessCoupling_pos

/-- **The rectified carrier is NOT odd**, so it is a genuinely different
    object from the one the corpus uses, and the difference is structural
    rather than a sign convention. -/
theorem realizedDensity_not_odd :
    ¬ (∀ ch2 : ℝ, realizedDensity (-ch2) = -(realizedDensity ch2)) := by
  intro h
  have h1 := h 1
  rw [realizedDensity_eq_zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)] at h1
  have hpos : 0 < realizedDensity 1 := realizedDensity_pos_of_pos (by norm_num)
  linarith

/-- **The two carriers genuinely differ**, exhibited at an explicit point, so
    none of the statements below is conditional on a possibly-empty
    distinction. -/
theorem models_differ_at_minus_one :
    realizedDensity (-1) ≠ Wave58.T_consciousness_density (-1) := by
  have h0 : realizedDensity (-1) = 0 :=
    realizedDensity_eq_zero_of_nonpos (by norm_num)
  have hneg : Wave58.T_consciousness_density (-1) < 0 :=
    density_neg_of_neg (by norm_num)
  rw [h0]
  intro hcon
  rw [← hcon] at hneg
  exact lt_irrefl 0 hneg

/-! ## §3 The residual: three branches, and the corpus defect -/

/-- **Realized potential strictly lowers the residual.** -/
theorem forward_strictly_gains (Gc Tc : ℝ) {ch2 : ℝ} (h : 0 < ch2) :
    Wave58.G_munu_modified Gc Tc (realizedDensity ch2)
      < Wave58.G_munu_modified Gc Tc (realizedDensity 0) := by
  have hpos : 0 < realizedDensity ch2 := realizedDensity_pos_of_pos h
  have hpi : (0 : ℝ) < 8 * Real.pi := by positivity
  unfold Wave58.G_munu_modified
  rw [realizedDensity_zero]
  nlinarith [hpos, hpi]

/-- **Going backwards is indistinguishable from never starting.** Under the
    rectified carrier the reversed branch and the unrealized branch give the
    *same* residual. This is the specification's claim that going backwards
    leads to nothing, and it is exactly what the corpus model denies. -/
theorem backward_gains_nothing (Gc Tc : ℝ) {ch2 : ℝ} (h : ch2 ≤ 0) :
    Wave58.G_munu_modified Gc Tc (realizedDensity ch2)
      = Wave58.G_munu_modified Gc Tc (realizedDensity 0) := by
  rw [realizedDensity_eq_zero_of_nonpos h, realizedDensity_zero]

/-- **★ THE DEFECT, as a theorem. ★** Under the model the corpus actually
    uses, going backwards does NOT lead to nothing: it strictly *raises* the
    modified-Einstein residual. So `Wave58.T_consciousness_density` contradicts
    the stated specification on the entire negative branch. -/
theorem linear_model_rewards_backwards (Gc Tc : ℝ) {ch2 : ℝ} (h : ch2 < 0) :
    Wave58.G_munu_modified Gc Tc 0
      < Wave58.G_munu_modified Gc Tc (Wave58.T_consciousness_density ch2) := by
  have hneg : Wave58.T_consciousness_density ch2 < 0 := density_neg_of_neg h
  have hpi : (0 : ℝ) < 8 * Real.pi := by positivity
  unfold Wave58.G_munu_modified
  nlinarith [hneg, hpi]

/-- More realization, strictly more effect, on the forward branch. -/
theorem forward_strict_mono (Gc Tc : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Wave58.G_munu_modified Gc Tc (realizedDensity b)
      < Wave58.G_munu_modified Gc Tc (realizedDensity a) := by
  have hb : 0 ≤ b := le_trans ha hab.le
  have hlt : realizedDensity a < realizedDensity b := by
    rw [realizedDensity_eq_of_nonneg ha, realizedDensity_eq_of_nonneg hb,
      density_eq, density_eq]
    exact mul_lt_mul_of_pos_right hab consciousnessCoupling_pos
  have hpi : (0 : ℝ) < 8 * Real.pi := by positivity
  unfold Wave58.G_munu_modified
  nlinarith [hlt, hpi]

/-! ## §4 The serendipity clause: the branches differ in reachability -/

/-- **★ The forward branch is cofinal downward. ★** For ANY target level `L`
    there is a realized potential whose residual undercuts it. This is the
    precise content of "on the positive side there may be an unexpected
    event": no bound on the achievable gain exists. -/
theorem forward_gain_unbounded (Gc Tc L : ℝ) :
    ∃ ch2 : ℝ, 0 < ch2 ∧ Wave58.G_munu_modified Gc Tc (realizedDensity ch2) < L := by
  have hKpos : 0 < consciousnessCoupling := consciousnessCoupling_pos
  have hpi : (0 : ℝ) < 8 * Real.pi := by positivity
  set M : ℝ := max ((Gc - L) / (8 * Real.pi) - Tc) 0 with hM
  have hnum : 0 < M + 1 := by
    have h := le_max_right ((Gc - L) / (8 * Real.pi) - Tc) 0
    rw [← hM] at h
    linarith
  refine ⟨(M + 1) / consciousnessCoupling, div_pos hnum hKpos, ?_⟩
  have hr : realizedDensity ((M + 1) / consciousnessCoupling) = M + 1 := by
    rw [realizedDensity_eq_of_nonneg (div_pos hnum hKpos).le, density_eq]
    field_simp
  have hle : (Gc - L) / (8 * Real.pi) - Tc ≤ M := by
    rw [hM]; exact le_max_left _ _
  have hmul : 8 * Real.pi * ((Gc - L) / (8 * Real.pi) - Tc) ≤ 8 * Real.pi * M :=
    mul_le_mul_of_nonneg_left hle hpi.le
  have hexp : 8 * Real.pi * ((Gc - L) / (8 * Real.pi) - Tc)
      = (Gc - L) - 8 * Real.pi * Tc := by
    field_simp
  rw [hexp] at hmul
  unfold Wave58.G_munu_modified
  rw [hr]
  have hring : Gc - 8 * Real.pi * (Tc + (M + 1))
      = (Gc - 8 * Real.pi * Tc - 8 * Real.pi * M) - 8 * Real.pi := by ring
  rw [hring]
  linarith

/-- **The backward branch attains exactly one value**, and never anything
    below it. Together with `forward_gain_unbounded` this is the asymmetry:
    one branch is cofinal downward, the other is a single point. -/
theorem backward_reaches_exactly_one_value (Gc Tc : ℝ) {ch2 : ℝ} (h : ch2 ≤ 0) :
    Wave58.G_munu_modified Gc Tc (realizedDensity ch2)
      = Gc - 8 * Real.pi * Tc := by
  rw [realizedDensity_eq_zero_of_nonpos h]
  unfold Wave58.G_munu_modified
  ring

/-- No reversed potential can undercut the unrealized level. -/
theorem backward_never_gains (Gc Tc : ℝ) {ch2 : ℝ} (h : ch2 ≤ 0) :
    ¬ (Wave58.G_munu_modified Gc Tc (realizedDensity ch2)
        < Wave58.G_munu_modified Gc Tc (realizedDensity 0)) := by
  rw [backward_gains_nothing Gc Tc h]
  exact lt_irrefl _

/-! ## §5 Capstone -/

/-- **★ CONSCIOUSNESS RELATIVITY IS ONE-SIDED. ★**

    The three branches of the specification, the incompatibility of the corpus
    model with it, and the reachability asymmetry, in one statement. Every
    conjunct is proved above; none is a hypothesis. -/
theorem consciousness_relativity_is_one_sided (Gc Tc : ℝ) :
    -- the three branches of the specification
    (realizedDensity 0 = 0)
      ∧ (∀ ch2 : ℝ, ch2 ≤ 0 →
          Wave58.G_munu_modified Gc Tc (realizedDensity ch2)
            = Wave58.G_munu_modified Gc Tc (realizedDensity 0))
      ∧ (∀ ch2 : ℝ, 0 < ch2 →
          Wave58.G_munu_modified Gc Tc (realizedDensity ch2)
            < Wave58.G_munu_modified Gc Tc (realizedDensity 0))
      -- the corpus model violates the second branch
      ∧ (∀ ch2 : ℝ, ch2 < 0 →
          Wave58.G_munu_modified Gc Tc 0
            < Wave58.G_munu_modified Gc Tc (Wave58.T_consciousness_density ch2))
      -- and the two carriers are genuinely distinct
      ∧ (realizedDensity (-1) ≠ Wave58.T_consciousness_density (-1))
      -- the forward branch reaches every level below
      ∧ (∀ L : ℝ, ∃ ch2 : ℝ, 0 < ch2 ∧
          Wave58.G_munu_modified Gc Tc (realizedDensity ch2) < L) :=
  ⟨realizedDensity_zero,
   fun _ h => backward_gains_nothing Gc Tc h,
   fun _ h => forward_strictly_gains Gc Tc h,
   fun _ h => linear_model_rewards_backwards Gc Tc h,
   models_differ_at_minus_one,
   fun L => forward_gain_unbounded Gc Tc L⟩

end PrincipiaTractalis.ConsciousnessRelativityAsymmetry
