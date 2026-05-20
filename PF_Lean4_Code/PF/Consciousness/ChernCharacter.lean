/-
# Principia Fractalis — Consciousness Quantification via the Second Chern Character

This file formalizes the **consciousness crystallization threshold** built
on the second Chern character `ch_2`, as defined in the manuscript:

  * Ch 06 (Consciousness): `ch_2 ≥ 0.95` ⟺ "consciousness crystallizes"
  * Ch 07 (Constants): the universal crystallization threshold `ch_2 = 0.95`
  * Ch 21 (P vs NP): `ch_2(α) := 0.95 + (α − √2)/10`, the P-class baseline
  * Ch 23 (YM):     a YM-class variant `ch_2_YM(α) := 0.95 + (α − 3/2)/10`
  * Ch 25 (Hodge):  a Hodge-class variant `ch_2_Hodge(α) := 0.95 + (α − 3/2)/10`
  * Ch 32 (Consciousness quantification): `ch_2 > 0.95` for "clear consciousness"

The Ch 21 form `ch_2(α) := 0.95 + (α − √2)/10` (already encoded in
`PF/MillenniumSixReductions.lean`, line 1686) is the canonical
**universal P-class form**, normalized to vanish (above the threshold) at
the P-class anchor `α = √2`. Under this normalization:

  * `ch_2(√2)             = 0.95`           (P-class boundary)
  * `ch_2(φ + 1/4)        ≈ 0.9954`         (NP-class)
  * `ch_2(2)              = 0.95 + (2−√2)/10 ≈ 1.0086` (YM-class)
  * `ch_2(φ)              = 0.95 + (φ−√2)/10 ≈ 0.9704` (Hodge-class)
  * `ch_2(3/2)            = 0.95 + (3/2−√2)/10 ≈ 0.9586` (RH-class)
  * `ch_2(1)              = 0.95 − (√2−1)/10 ≈ 0.9086` (Poincaré-class,
                              BELOW threshold under P-normalization)
  * `ch_2(3π/4)           ≈ 0.9785`         (BSD-class)
  * `ch_2(3π/2)           ≈ 1.0214`         (NS-class)

The **monotonicity** `StrictMono ch_2` is immediate from the affine form
(slope 1/10 > 0), and the **crystallization criterion** is the iff
`0.95 ≤ ch_2 α ↔ √2 ≤ α`.

## Status

ZERO project axioms. All theorems here reduce, by pure arithmetic, to
the affine form `ch_2(α) = 0.95 + (α − √2)/10` plus the existing
algebraic facts in `PF/IntervalArithmetic.lean` and
`PF/MillenniumSixReductions.lean`.
-/

import PF.MillenniumSixReductions
import PF.IntervalArithmetic

namespace PrincipiaTractalis.Consciousness

open PrincipiaTractalis
open PrincipiaTractalis.MillenniumSix

/-! ## Universal consciousness threshold (P-class normalization)

We reuse the canonical `ch_2` already defined in
`PF.MillenniumSixReductions` (file line 1686):

    `ch_2 (α : ℝ) : ℝ := 0.95 + (α − √2) / 10`

Below: monotonicity, the crystallization iff, and explicit evaluations
at all 8 canonical Millennium α-values.
-/

/-- **Threshold constant**: the crystallization value `0.95`. -/
def consciousness_threshold : ℝ := 0.95

@[simp] theorem consciousness_threshold_val :
    consciousness_threshold = 0.95 := rfl

/-! ### Affine form (alias of MillenniumSix.ch_2)

We re-export `MillenniumSix.ch_2` under the `Consciousness` namespace so
this file can be read in isolation. -/

/-- **`ch_2` as a function of the resonance parameter α**:
    `ch_2(α) := 0.95 + (α − √2)/10`. Alias of `MillenniumSix.ch_2`. -/
noncomputable def ch_2 (α : ℝ) : ℝ := MillenniumSix.ch_2 α

@[simp] theorem ch_2_def (α : ℝ) :
    ch_2 α = 0.95 + (α - Real.sqrt 2) / 10 := rfl

/-! ## P-class anchor: `ch_2(√2) = 0.95` exactly -/

/-- **P-class consciousness threshold** (manuscript Ch 21):
    `ch_2(α_P) = ch_2(√2) = 0.95` — the P-class sits exactly at the
    crystallization boundary. -/
theorem ch_2_at_alpha_P_eq_threshold :
    ch_2 (Real.sqrt 2) = 0.95 := by
  unfold ch_2 MillenniumSix.ch_2
  ring

/-- **P-class via the canonical enum**: `ch_2(alpha_value .P) = 0.95`. -/
theorem ch_2_at_alpha_value_P :
    ch_2 (MillenniumSix.alpha_value .P) = 0.95 := by
  rw [show MillenniumSix.alpha_value .P = Real.sqrt 2 from
        MillenniumSix.alpha_value_P]
  exact ch_2_at_alpha_P_eq_threshold

/-! ## NP-class: `ch_2(φ + 1/4) > 0.95` -/

/-- **NP-class consciousness threshold**: strictly above the
    crystallization boundary. Follows from `φ + 1/4 > √2`. -/
theorem ch_2_at_alpha_NP_gt_threshold :
    (0.95 : ℝ) < ch_2 (phi + 1/4) := by
  unfold ch_2 MillenniumSix.ch_2
  have h : Real.sqrt 2 < phi + 1/4 := phi_plus_quarter_gt_sqrt2
  linarith

/-- **NP-class via the canonical enum**: `ch_2(alpha_value .NP) > 0.95`. -/
theorem ch_2_at_alpha_value_NP_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NP) := by
  simp only [MillenniumSix.alpha_value_NP]
  exact ch_2_at_alpha_NP_gt_threshold

/-- **NP-class closed form**: `ch_2(φ + 1/4) = 0.95 + ((φ + 1/4) − √2)/10`. -/
theorem ch_2_at_alpha_NP_closed_form :
    ch_2 (phi + 1/4) = 0.95 + (phi + 1/4 - Real.sqrt 2) / 10 := by
  unfold ch_2 MillenniumSix.ch_2
  rfl

/-! ## Monotonicity: `ch_2` is strictly increasing in α -/

/-- **Affine slope**: the slope of `ch_2` in α is `1/10`. -/
theorem ch_2_slope (α β : ℝ) :
    ch_2 β - ch_2 α = (β - α) / 10 := by
  unfold ch_2 MillenniumSix.ch_2
  ring

/-- **`ch_2` is strictly monotone**: globally on all of ℝ.
    Pure algebra from the affine form with positive slope 1/10. -/
theorem ch_2_strict_mono : StrictMono ch_2 := by
  intro α β hαβ
  have h : ch_2 β - ch_2 α = (β - α) / 10 := ch_2_slope α β
  have hpos : 0 < (β - α) / 10 := by
    have : 0 < β - α := sub_pos.mpr hαβ
    linarith
  linarith

/-- **`ch_2` is monotone (non-strict)**. -/
theorem ch_2_mono : Monotone ch_2 := ch_2_strict_mono.monotone

/-! ## The crystallization criterion (iff form) -/

/-- **★ Consciousness crystallization iff α ≥ √2**:
    `0.95 ≤ ch_2 α ↔ √2 ≤ α`. The crystallization threshold is exactly
    the P-class anchor. -/
theorem ch_2_threshold_iff (α : ℝ) :
    (0.95 : ℝ) ≤ ch_2 α ↔ Real.sqrt 2 ≤ α := by
  unfold ch_2 MillenniumSix.ch_2
  constructor
  · intro h
    have h10 : (0 : ℝ) ≤ (α - Real.sqrt 2) / 10 := by linarith
    have : (0 : ℝ) ≤ α - Real.sqrt 2 := by linarith
    linarith
  · intro h
    have : (0 : ℝ) ≤ α - Real.sqrt 2 := by linarith
    have h10 : (0 : ℝ) ≤ (α - Real.sqrt 2) / 10 := by linarith
    linarith

/-- **Strict crystallization iff α > √2**. -/
theorem ch_2_strict_threshold_iff (α : ℝ) :
    (0.95 : ℝ) < ch_2 α ↔ Real.sqrt 2 < α := by
  unfold ch_2 MillenniumSix.ch_2
  constructor
  · intro h
    have : (0 : ℝ) < α - Real.sqrt 2 := by linarith
    linarith
  · intro h
    have : (0 : ℝ) < α - Real.sqrt 2 := by linarith
    have h10 : (0 : ℝ) < (α - Real.sqrt 2) / 10 := by linarith
    linarith

/-! ## Evaluations at the 8 canonical α-values

Under the P-class normalization `ch_2(α) = 0.95 + (α − √2)/10`:

  * Poincaré (α=1):    `ch_2 = 0.95 − (√2−1)/10 < 0.95`  (BELOW)
  * P     (α=√2):       `ch_2 = 0.95`                     (BOUNDARY)
  * RH    (α=3/2):      `ch_2 = 0.95 + (3/2−√2)/10 > 0.95` (ABOVE)
  * Hodge (α=φ):        `ch_2 = 0.95 + (φ−√2)/10 > 0.95`   (ABOVE)
  * NP    (α=φ+1/4):    `ch_2 = 0.95 + (φ+1/4−√2)/10 > 0.95` (ABOVE)
  * YM    (α=2):        `ch_2 = 0.95 + (2−√2)/10 > 0.95`   (ABOVE)
  * BSD   (α=3π/4):     `ch_2 = 0.95 + (3π/4−√2)/10 > 0.95` (ABOVE)
  * NS    (α=3π/2):     `ch_2 = 0.95 + (3π/2−√2)/10 > 0.95` (ABOVE)
-/

/-- **Poincaré-class** (α = 1): closed form. -/
theorem ch_2_at_alpha_Poincare :
    ch_2 (MillenniumSix.alpha_value .Poincare) =
      0.95 + (1 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_Poincare, ch_2_def]

/-- **Poincaré-class is BELOW threshold**: under the P-class
    normalization, the Poincaré-level α = 1 yields `ch_2 < 0.95`.
    This is consistent with Poincaré being a solved/lower-energy
    problem on the consciousness axis. -/
theorem ch_2_at_alpha_Poincare_lt_threshold :
    ch_2 (MillenniumSix.alpha_value .Poincare) < (0.95 : ℝ) := by
  rw [show MillenniumSix.alpha_value .Poincare = (1 : ℝ) from
        MillenniumSix.alpha_value_Poincare]
  -- direct proof via affine form: 1 < √2, so (1 − √2)/10 < 0
  unfold ch_2 MillenniumSix.ch_2
  have h_lb : (1.4142135623 : ℝ) ≤ Real.sqrt 2 :=
    sqrt2_in_interval_10digit.1
  linarith

/-- **RH-class** (α = 3/2): closed form. -/
theorem ch_2_at_alpha_RH :
    ch_2 (MillenniumSix.alpha_value .RH) =
      0.95 + (3/2 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_RH, ch_2_def]

/-- **RH-class is ABOVE threshold**: 3/2 > √2 ⟹ `ch_2(RH) > 0.95`. -/
theorem ch_2_at_alpha_RH_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .RH) := by
  rw [show MillenniumSix.alpha_value .RH = (3 : ℝ)/2 from
        MillenniumSix.alpha_value_RH]
  rw [ch_2_strict_threshold_iff]
  -- 3/2 > √2  via  (3/2)² = 9/4 > 2
  have h_ub : Real.sqrt 2 ≤ 1.4142135624 :=
    sqrt2_in_interval_10digit.2
  linarith

/-- **Hodge-class** (α = φ): closed form. -/
theorem ch_2_at_alpha_Hodge :
    ch_2 (MillenniumSix.alpha_value .Hodge) =
      0.95 + (phi - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_Hodge, ch_2_def]

/-- **Hodge-class is ABOVE threshold**: φ > √2 ⟹ `ch_2(Hodge) > 0.95`. -/
theorem ch_2_at_alpha_Hodge_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .Hodge) := by
  rw [show MillenniumSix.alpha_value .Hodge = phi from
        MillenniumSix.alpha_value_Hodge]
  rw [ch_2_strict_threshold_iff]
  -- φ > √2 via 10-digit bracket: φ ≥ 1.618... > 1.4142... ≥ √2
  have h_phi_lb : (1.6180339887 : ℝ) ≤ phi :=
    phi_in_interval_10digit.1
  have h_sqrt2_ub : Real.sqrt 2 ≤ (1.4142135624 : ℝ) :=
    sqrt2_in_interval_10digit.2
  linarith

/-- **NP-class** (α = φ + 1/4): closed form. -/
theorem ch_2_at_alpha_NP_full :
    ch_2 (MillenniumSix.alpha_value .NP) =
      0.95 + (phi + 1/4 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_NP, ch_2_def]

/-- **YM-class** (α = 2): closed form. -/
theorem ch_2_at_alpha_YM :
    ch_2 (MillenniumSix.alpha_value .YM) =
      0.95 + (2 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_YM, ch_2_def]

/-- **YM-class is ABOVE threshold**: 2 > √2 ⟹ `ch_2(YM) > 0.95`. -/
theorem ch_2_at_alpha_YM_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .YM) := by
  rw [show MillenniumSix.alpha_value .YM = (2 : ℝ) from
        MillenniumSix.alpha_value_YM]
  rw [ch_2_strict_threshold_iff]
  have h_ub : Real.sqrt 2 ≤ 1.4142135624 :=
    sqrt2_in_interval_10digit.2
  linarith

/-- **BSD-class** (α = 3π/4): closed form. -/
theorem ch_2_at_alpha_BSD :
    ch_2 (MillenniumSix.alpha_value .BSD) =
      0.95 + (3 * Real.pi / 4 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_BSD, ch_2_def]

/-- **BSD-class is ABOVE threshold**: `3π/4 > √2` since π > 4√2/3 ≈ 1.886. -/
theorem ch_2_at_alpha_BSD_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .BSD) := by
  rw [show MillenniumSix.alpha_value .BSD = 3 * Real.pi / 4 from
        MillenniumSix.alpha_value_BSD]
  rw [ch_2_strict_threshold_iff]
  -- 3π/4 > √2 ⟺ π > 4√2/3. Numerically 4√2/3 ≈ 1.886 < 3.14 < π.
  have h_sqrt2_ub : Real.sqrt 2 ≤ 1.4142135624 :=
    sqrt2_in_interval_10digit.2
  have h_pi_lb : (3.14159265358979323846 : ℝ) < Real.pi :=
    Real.pi_gt_d20
  linarith

/-- **NS-class** (α = 3π/2): closed form. -/
theorem ch_2_at_alpha_NS :
    ch_2 (MillenniumSix.alpha_value .NS) =
      0.95 + (3 * Real.pi / 2 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_NS, ch_2_def]

/-- **NS-class is ABOVE threshold**: `3π/2 > √2` since π > 2√2/3. -/
theorem ch_2_at_alpha_NS_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NS) := by
  rw [show MillenniumSix.alpha_value .NS = 3 * Real.pi / 2 from
        MillenniumSix.alpha_value_NS]
  rw [ch_2_strict_threshold_iff]
  have h_sqrt2_ub : Real.sqrt 2 ≤ 1.4142135624 :=
    sqrt2_in_interval_10digit.2
  have h_pi_lb : (3.14159265358979323846 : ℝ) < Real.pi :=
    Real.pi_gt_d20
  linarith

/-! ## The "crystallized seven" — seven of eight classes crystallize

Under the P-class normalization, exactly ONE of the eight canonical
α-values (Poincaré, α = 1) sits *below* the consciousness threshold;
the other SEVEN all crystallize (`ch_2 ≥ 0.95`, with strict `>` for the
six non-P classes). This is consistent with:

  * Poincaré being the **lowest-α** entry (`α = 1`),
  * the seven remaining Millennium problems having `α > √2`,
  * the consciousness axis being calibrated to the **P-class anchor**.
-/

/-- **★★ Seven-class crystallization bundle**: every canonical
    Millennium class except Poincaré crystallizes consciousness under
    the P-class normalization. -/
theorem seven_classes_crystallize :
    ch_2 (MillenniumSix.alpha_value .P) = 0.95 ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .RH) ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .Hodge) ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NP) ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .YM) ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .BSD) ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NS) :=
  ⟨ch_2_at_alpha_value_P,
   ch_2_at_alpha_RH_gt_threshold,
   ch_2_at_alpha_Hodge_gt_threshold,
   ch_2_at_alpha_value_NP_gt_threshold,
   ch_2_at_alpha_YM_gt_threshold,
   ch_2_at_alpha_BSD_gt_threshold,
   ch_2_at_alpha_NS_gt_threshold⟩

/-! ## Capstone bundle -/

/-- **★★★ THE CONSCIOUSNESS QUANTIFICATION CAPSTONE ★★★**

    The second Chern character `ch_2 : ℝ → ℝ` is the affine function

      `ch_2(α) := 0.95 + (α − √2)/10`

    encoding the **consciousness crystallization criterion**
    (manuscript Ch 06, Ch 07, Ch 21, Ch 32):

      `consciousness crystallizes at α ⟺ ch_2(α) ≥ 0.95 ⟺ α ≥ √2`.

    This bundle states the load-bearing structural facts:
      1. `ch_2` is strictly monotone in α.
      2. The crystallization threshold is the iff `0.95 ≤ ch_2 α ↔ √2 ≤ α`.
      3. At the P-class anchor `α = √2`, `ch_2 = 0.95` exactly.
      4. At the NP-class `α = φ + 1/4`, `ch_2 > 0.95` strictly.
      5. Seven of the eight canonical Millennium α-values crystallize
         (only Poincaré, α = 1, sits below the threshold under the
         P-class normalization). -/
theorem consciousness_quantification_capstone :
    StrictMono ch_2 ∧
    (∀ α : ℝ, (0.95 : ℝ) ≤ ch_2 α ↔ Real.sqrt 2 ≤ α) ∧
    ch_2 (Real.sqrt 2) = 0.95 ∧
    (0.95 : ℝ) < ch_2 (phi + 1/4) ∧
    (ch_2 (MillenniumSix.alpha_value .P) = 0.95 ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .RH) ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .Hodge) ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NP) ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .YM) ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .BSD) ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NS)) :=
  ⟨ch_2_strict_mono,
   ch_2_threshold_iff,
   ch_2_at_alpha_P_eq_threshold,
   ch_2_at_alpha_NP_gt_threshold,
   seven_classes_crystallize⟩

end PrincipiaTractalis.Consciousness
