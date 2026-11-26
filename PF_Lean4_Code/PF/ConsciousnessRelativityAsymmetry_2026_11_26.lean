/-
# Consciousness relativity: the gate and the density, finally composed

**Spine arrow.** `emergent locality -> modified relativity -> churn`.

## This file CORRECTS its own previous version (`e419a1d3`)

The first version of this module rectified the consciousness density at **0**
(`max ch2 0`) and framed `Wave58.T_consciousness_density` as *violating* a
one-sidedness specification. Checking the manuscript showed both of those to be
wrong, and the correction is recorded here rather than quietly dropped:

1. **The threshold is `19/20`, not `0`.** Chapter 8's Definition
   "Consciousness Stress-Energy" (`def:consciousness-stress`, ch08:80) reads
   `C^{mu nu} = integral <w| T^{mu nu} |w> * Theta(ch_2(w) - 0.95) * R_f(a,s) dmu(w)`,
   with a **Heaviside gate at 0.95**. Rectifying at 0 was an under-reading of
   the book by the whole interval `(0, 0.95)`.

2. **`T_consciousness_density` is not the gated tensor and never claimed to
   be.** It is the *density factor inside the integrand*, and its own docstring
   names the Heaviside explicitly ("the Ch 08 Section 2.2 crystallisation
   threshold `ch_2 > 0.95`, manuscript line 80, inside the Heaviside"). Its
   linearity is therefore by design, not a defect. Calling it odd and calling
   that a contradiction was wrong.

So the book was ahead of the companion, as it usually is. What is *true* is
narrower and more useful.

## The actual gap: two halves, never multiplied

Both halves of ch08's `C^{mu nu}` already exist in Lean, in different
directories, and **nothing composed them**:

  * the gate --- `thresholdGate x = if 19/20 <= x then 1 else 0`, in
    `PF/Cosmology/VortexCavitationBridgeChecks.lean`, with the docstring
    "The Heaviside gate `Theta(ch_2 - 0.95)` of ch08";
  * the density --- `Wave58.T_consciousness_density ch2 = ch2 * (78*pi*0.95*1.1875)`,
    in `PF/Wave58/Ch08FieldEquationsConcrete.lean`.

A corpus scan of every module mentioning the density found **zero** gate
references outside one docstring. This file supplies the composition and proves
what it does. That is the same defect shape as the churn result (`0744f26a`)
and the modified-GR shadow (`f0b1ce27`): as the corpus accumulates parts, the
characteristic flaw stops being *missing* pieces and becomes *unjoined* ones.

## What the composition proves

`gatedDensity ch2 = thresholdGate ch2 * T_consciousness_density ch2` has exactly
the three branches the manuscript describes, now at the manuscript's own
threshold:

  * `ch2 < 19/20` --- identically **zero**. This single statement covers
    reversal (`ch2 < 0`), no consciousness (`ch2 = 0`), AND partial
    realisation (`0 < ch2 < 19/20`). Potential not carried to the
    crystallisation threshold contributes nothing at all.
  * `19/20 <= ch2` --- strictly positive, and equal to the ungated density
    there, so nothing proved about the density on that branch is lost.
  * the forward branch is **cofinal downward** in the modified-Einstein
    residual while the sub-threshold branch attains exactly **one** value.

`density_is_odd` is retained, with its meaning corrected: an odd density
*cannot* be one-sided on its own, which is precisely **why** ch08 puts a
Heaviside in front of it. The gate is load-bearing, and
`gate_changes_the_density` exhibits a point where composing changes the answer.

## Scope

Stated by the book and not weakened here: `C^{mu nu}` "cannot be evaluated as
written" --- neither the stress operator nor the measure on `T_infinity` is
constructed anywhere in the corpus, so it is a schema, and no number in the book
comes from it (ch08's 2026-11-24 note, item 4). This file is the **scalar
slice** only, like the Wave58 module it builds on. It asserts no physics, and
consciousness remains EMPIRICAL / UNTESTED in the book's own ledger.

Two further facts the book already records and this file does not re-litigate:
`ch_2` denotes five different quantities in this corpus with different ranges
(ch08 note, item 1); and under the *matrix* form the gate is identically closed
(item 2), already kernel-verified upstream as `ch2Matrix_lt_threshold` and
`thresholdGate_ch2Matrix_eq_zero` --- re-exported below rather than reproved.

No pseudo-Riemannian geometry is used, which is why this arrow is reachable at a
pin with Lorentzian, PseudoRiemannian, SemiRiemannian, LeviCivita, RicciTensor
and MetricTensor all at 0 files (measured 2026-11-26).
-/

import PF.Cosmology.VortexCavitationBridgeChecks
import PF.Wave58.Ch08FieldEquationsConcrete

set_option autoImplicit false

namespace PrincipiaTractalis.ConsciousnessRelativityAsymmetry

open Real

/-- Abbreviation for the manuscript's crystallisation threshold, `0.95`. -/
noncomputable def crystallisationThreshold : ℝ := 19 / 20

/-- The consciousness coupling appearing in `Wave58.T_consciousness_density`,
    named so its positivity is used rather than re-derived. -/
noncomputable def consciousnessCoupling : ℝ := 78 * Real.pi * 0.95 * 1.1875

theorem consciousnessCoupling_pos : 0 < consciousnessCoupling := by
  unfold consciousnessCoupling
  positivity

/-- The upstream density is exactly `ch2` times that coupling. Definitional. -/
theorem density_eq (ch2 : ℝ) :
    Wave58.T_consciousness_density ch2 = ch2 * consciousnessCoupling := rfl

/-! ## §1 Why a gate is needed at all

The density factor is linear, hence odd. An odd function is zero only at the
origin and antisymmetric around it, so it can never vanish on a half-line
unless it vanishes everywhere. One-sidedness therefore cannot come from the
density; it must come from a separate factor. That factor is ch08's Heaviside. -/

/-- The density factor is **odd**: `T(-x) = -T(x)`. Not a defect --- this is
    the reason the manuscript's definition carries a Heaviside. -/
theorem density_is_odd (ch2 : ℝ) :
    Wave58.T_consciousness_density (-ch2) = -(Wave58.T_consciousness_density ch2) := by
  rw [density_eq, density_eq]
  ring

/-- Below the threshold the *ungated* density is nonzero whenever `ch2 ≠ 0`, so
    the ungated factor alone does not implement the manuscript's gate. -/
theorem ungated_density_ne_zero_of_ne_zero {ch2 : ℝ} (h : ch2 ≠ 0) :
    Wave58.T_consciousness_density ch2 ≠ 0 := by
  rw [density_eq]
  exact mul_ne_zero h (ne_of_gt consciousnessCoupling_pos)

/-! ## §2 The composition ch08 actually specifies -/

/-- **★ ch08's gated consciousness density. ★** The Heaviside factor of
    `def:consciousness-stress` times the scalar density, i.e. the two halves
    that existed separately in `PF/Cosmology/` and `PF/Wave58/` and were never
    multiplied together. -/
noncomputable def gatedDensity (ch2 : ℝ) : ℝ :=
  Cosmology.VortexCavitationBridge.thresholdGate ch2 *
    Wave58.T_consciousness_density ch2

/-- **Branch 1 --- below crystallisation, nothing.** One statement covering
    reversal (`ch2 < 0`), absence (`ch2 = 0`) and partial realisation
    (`0 < ch2 < 19/20`): potential not carried to the threshold contributes
    exactly zero. -/
theorem gatedDensity_eq_zero_of_lt_threshold {ch2 : ℝ}
    (h : ch2 < crystallisationThreshold) : gatedDensity ch2 = 0 := by
  unfold gatedDensity Cosmology.VortexCavitationBridge.thresholdGate
  rw [crystallisationThreshold] at h
  rw [if_neg (not_le.mpr h), zero_mul]

/-- **Branch 2 --- at or above crystallisation, the full density.** Nothing
    proved upstream about the density on this branch is lost. -/
theorem gatedDensity_eq_density_of_threshold_le {ch2 : ℝ}
    (h : crystallisationThreshold ≤ ch2) :
    gatedDensity ch2 = Wave58.T_consciousness_density ch2 := by
  unfold gatedDensity Cosmology.VortexCavitationBridge.thresholdGate
  rw [crystallisationThreshold] at h
  rw [if_pos h, one_mul]

/-- **Branch 3 --- above crystallisation it is strictly positive.** -/
theorem gatedDensity_pos_of_threshold_le {ch2 : ℝ}
    (h : crystallisationThreshold ≤ ch2) : 0 < gatedDensity ch2 := by
  rw [gatedDensity_eq_density_of_threshold_le h, density_eq]
  have hc : 0 < ch2 := by
    have : (0:ℝ) < crystallisationThreshold := by
      unfold crystallisationThreshold; norm_num
    linarith
  exact mul_pos hc consciousnessCoupling_pos

/-- Reversal and absence are indistinguishable, which is the manuscript's
    one-sidedness: both give the same (zero) contribution. -/
theorem reversal_indistinguishable_from_absence {ch2 : ℝ} (h : ch2 ≤ 0) :
    gatedDensity ch2 = gatedDensity 0 := by
  have h0 : (0:ℝ) < crystallisationThreshold := by
    unfold crystallisationThreshold; norm_num
  rw [gatedDensity_eq_zero_of_lt_threshold (by linarith),
    gatedDensity_eq_zero_of_lt_threshold h0]

/-- **The gate is load-bearing**, exhibited at a point: composing changes the
    answer, so `gatedDensity` is not a renaming of the density. -/
theorem gate_changes_the_density :
    gatedDensity (-1) ≠ Wave58.T_consciousness_density (-1) := by
  have h0 : gatedDensity (-1) = 0 := by
    apply gatedDensity_eq_zero_of_lt_threshold
    unfold crystallisationThreshold; norm_num
  have hne : Wave58.T_consciousness_density (-1) ≠ 0 :=
    ungated_density_ne_zero_of_ne_zero (by norm_num)
  rw [h0]
  exact fun hcon => hne hcon.symm

/-! ## §3 The modified-Einstein residual, by branch -/

/-- Sub-threshold, the residual is exactly the unsourced one: a potential that
    never reached crystallisation leaves the field equation untouched. -/
theorem residual_unchanged_below_threshold (Gc Tc : ℝ) {ch2 : ℝ}
    (h : ch2 < crystallisationThreshold) :
    Wave58.G_munu_modified Gc Tc (gatedDensity ch2)
      = Gc - 8 * Real.pi * Tc := by
  rw [gatedDensity_eq_zero_of_lt_threshold h]
  unfold Wave58.G_munu_modified
  ring

/-- Above crystallisation the residual is strictly lowered. -/
theorem residual_strictly_lowered_above_threshold (Gc Tc : ℝ) {ch2 : ℝ}
    (h : crystallisationThreshold ≤ ch2) :
    Wave58.G_munu_modified Gc Tc (gatedDensity ch2)
      < Gc - 8 * Real.pi * Tc := by
  have hpos : 0 < gatedDensity ch2 := gatedDensity_pos_of_threshold_le h
  have hpi : (0:ℝ) < 8 * Real.pi := by positivity
  unfold Wave58.G_munu_modified
  nlinarith [hpos, hpi]

/-- More realisation above the threshold, strictly more effect. -/
theorem residual_strict_mono_above_threshold (Gc Tc : ℝ) {a b : ℝ}
    (ha : crystallisationThreshold ≤ a) (hab : a < b) :
    Wave58.G_munu_modified Gc Tc (gatedDensity b)
      < Wave58.G_munu_modified Gc Tc (gatedDensity a) := by
  have hb : crystallisationThreshold ≤ b := le_trans ha hab.le
  have hlt : gatedDensity a < gatedDensity b := by
    rw [gatedDensity_eq_density_of_threshold_le ha,
      gatedDensity_eq_density_of_threshold_le hb, density_eq, density_eq]
    exact mul_lt_mul_of_pos_right hab consciousnessCoupling_pos
  have hpi : (0:ℝ) < 8 * Real.pi := by positivity
  unfold Wave58.G_munu_modified
  nlinarith [hlt, hpi]

/-! ## §4 The branches differ in reachability -/

/-- **★ The realised branch is cofinal downward. ★** For any target level there
    is a crystallised state whose residual undercuts it: no bound on the
    achievable effect exists above the threshold. -/
theorem forward_gain_unbounded (Gc Tc L : ℝ) :
    ∃ ch2 : ℝ, crystallisationThreshold ≤ ch2 ∧
      Wave58.G_munu_modified Gc Tc (gatedDensity ch2) < L := by
  have hK : 0 < consciousnessCoupling := consciousnessCoupling_pos
  have hpi : (0:ℝ) < 8 * Real.pi := by positivity
  set M : ℝ := max ((Gc - L) / (8 * Real.pi) - Tc) 0 with hM
  have hM0 : 0 ≤ M := by rw [hM]; exact le_max_right _ _
  set c : ℝ := max crystallisationThreshold ((M + 1) / consciousnessCoupling) with hc
  have hc1 : crystallisationThreshold ≤ c := by rw [hc]; exact le_max_left _ _
  refine ⟨c, hc1, ?_⟩
  have hgd : gatedDensity c = c * consciousnessCoupling := by
    rw [gatedDensity_eq_density_of_threshold_le hc1, density_eq]
  have h2 : (M + 1) / consciousnessCoupling ≤ c := by rw [hc]; exact le_max_right _ _
  have hcK : M + 1 ≤ c * consciousnessCoupling := by
    calc M + 1 = ((M + 1) / consciousnessCoupling) * consciousnessCoupling := by
          field_simp
      _ ≤ c * consciousnessCoupling := mul_le_mul_of_nonneg_right h2 hK.le
  have hle : (Gc - L) / (8 * Real.pi) - Tc ≤ M := by rw [hM]; exact le_max_left _ _
  have hmul : 8 * Real.pi * ((Gc - L) / (8 * Real.pi) - Tc) ≤ 8 * Real.pi * M :=
    mul_le_mul_of_nonneg_left hle hpi.le
  have hexp : 8 * Real.pi * ((Gc - L) / (8 * Real.pi) - Tc)
      = (Gc - L) - 8 * Real.pi * Tc := by field_simp
  rw [hexp] at hmul
  unfold Wave58.G_munu_modified
  rw [hgd]
  nlinarith [hmul, hcK, hpi, hM0]

/-- **The sub-threshold branch attains exactly one value**, never anything
    lower. With the previous theorem this is the asymmetry: one branch reaches
    every level below, the other is a single point. -/
theorem subthreshold_never_gains (Gc Tc : ℝ) {ch2 : ℝ}
    (h : ch2 < crystallisationThreshold) :
    ¬ (Wave58.G_munu_modified Gc Tc (gatedDensity ch2) < Gc - 8 * Real.pi * Tc) := by
  rw [residual_unchanged_below_threshold Gc Tc h]
  exact lt_irrefl _

/-! ## §5 The matrix-form consequence, re-exported not reproved

The book's own note (ch08, 2026-11-24, item 2) records that under the *matrix*
form of `ch_2` the gate is identically closed. That is already kernel-verified
upstream; these are the upstream theorems themselves, wired by inferred type so
they cannot drift from what was proved. -/

-- The binders are explicit because these upstream results carry an implicit
-- `{n} [Fintype n]`; with an inferred-type `def` and no binders the instance
-- is a metavariable and the elaborator is stuck. Explicit binders keep the
-- inferred type (nothing is transcribed) while pinning the instance.

/-- `ch2Matrix` never reaches the gate. -/
def matrix_form_never_reaches_gate {n : Type*} [Fintype n] (W : Matrix n n ℝ) :=
  Cosmology.VortexCavitationBridge.ch2Matrix_lt_threshold W

/-- Hence the gate is identically closed under the matrix form. -/
def matrix_form_closes_the_gate {n : Type*} [Fintype n] (W : Matrix n n ℝ) :=
  Cosmology.VortexCavitationBridge.thresholdGate_ch2Matrix_eq_zero W

/-- Hence any gated source vanishes for every velocity gradient. -/
def matrix_form_gated_source_vanishes {n : Type*} [Fintype n]
    (W : Matrix n n ℝ) (T : ℝ) :=
  Cosmology.VortexCavitationBridge.gated_source_eq_zero W T

/-! ## §6 Capstone -/

/-- **★ CH08'S CONSCIOUSNESS SOURCE IS ONE-SIDED, AT 19/20. ★**

    The three branches of `def:consciousness-stress`, the load-bearing gate, and
    the reachability asymmetry, in one statement. Every conjunct is proved
    above; none is a hypothesis. -/
theorem ch08_consciousness_source_is_one_sided (Gc Tc : ℝ) :
    -- below crystallisation: identically nothing, reversal included
    (∀ ch2 : ℝ, ch2 < crystallisationThreshold → gatedDensity ch2 = 0)
      -- at or above: the full density, strictly positive
      ∧ (∀ ch2 : ℝ, crystallisationThreshold ≤ ch2 →
          gatedDensity ch2 = Wave58.T_consciousness_density ch2 ∧ 0 < gatedDensity ch2)
      -- the residual is untouched below and strictly lowered above
      ∧ (∀ ch2 : ℝ, ch2 < crystallisationThreshold →
          Wave58.G_munu_modified Gc Tc (gatedDensity ch2) = Gc - 8 * Real.pi * Tc)
      ∧ (∀ ch2 : ℝ, crystallisationThreshold ≤ ch2 →
          Wave58.G_munu_modified Gc Tc (gatedDensity ch2) < Gc - 8 * Real.pi * Tc)
      -- the gate is doing work
      ∧ (gatedDensity (-1) ≠ Wave58.T_consciousness_density (-1))
      -- and the realised branch reaches every level below
      ∧ (∀ L : ℝ, ∃ ch2 : ℝ, crystallisationThreshold ≤ ch2 ∧
          Wave58.G_munu_modified Gc Tc (gatedDensity ch2) < L) :=
  ⟨fun _ h => gatedDensity_eq_zero_of_lt_threshold h,
   fun _ h => ⟨gatedDensity_eq_density_of_threshold_le h,
               gatedDensity_pos_of_threshold_le h⟩,
   fun _ h => residual_unchanged_below_threshold Gc Tc h,
   fun _ h => residual_strictly_lowered_above_threshold Gc Tc h,
   gate_changes_the_density,
   fun L => forward_gain_unbounded Gc Tc L⟩

end PrincipiaTractalis.ConsciousnessRelativityAsymmetry
