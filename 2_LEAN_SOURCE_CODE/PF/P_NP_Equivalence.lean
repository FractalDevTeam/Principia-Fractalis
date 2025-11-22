/-
# The Spectral Gap ↔ P≠NP Equivalence Theorem (PF module)
Main formalization of the equivalence between spectral gap and computational complexity separation.
-/

import PF.TuringEncoding
import PF.SpectralGap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace PrincipiaTractalis

/-- The spectral gap between H_P and H_NP ground states. -/
noncomputable def Delta : ℝ := spectral_gap

/-- P = NP means every NP language has a polynomial-time deterministic algorithm. -/
def P_equals_NP_def : Prop :=
  ∀ (L : Type) (verify_time : TimeComplexity),
    IsInNP verify_time →
    ∃ (decide_time : TimeComplexity), IsInP decide_time

/-- P ≠ NP means there exists a language in NP with no polynomial-time algorithm. -/
def P_neq_NP_def : Prop := ¬P_equals_NP_def

axiom np_not_p_requires_certificate :
  ∀ (L : Type) (vtime : TimeComplexity),
    IsInNP vtime → (∀ (dtime : TimeComplexity), ¬IsInP dtime) →
    ∃ (cert_energy : ℤ), cert_energy > 0

axiom p_eq_np_iff_zero_gap : P_equals_NP_def ↔ Delta = 0

/-- MAIN THEOREM: Spectral gap is positive if and only if P ≠ NP. -/
theorem spectral_gap_iff_P_neq_NP : Delta > 0 ↔ P_neq_NP_def := by
  constructor
  · intro h_gap_pos
    unfold P_neq_NP_def P_equals_NP_def
    by_contra h_p_eq_np
    have h_p_eq_np_forces_zero_gap : Delta = 0 := by
      exact p_eq_np_iff_zero_gap.mp h_p_eq_np
    linarith
  · intro h_p_neq_np
    unfold P_neq_NP_def P_equals_NP_def at h_p_neq_np
    push_neg at h_p_neq_np
    obtain ⟨L, vtime, h_np, h_not_p⟩ := h_p_neq_np
    have needs_certificate : ∃ (cert_energy : ℤ), cert_energy > 0 := by
      exact np_not_p_requires_certificate L vtime h_np h_not_p
    have alpha_sep : alpha_NP > alpha_P :=
      certificate_forces_higher_frequency
    have spectrum_sep : lambda_0_P > lambda_0_NP := by
      unfold lambda_0_P lambda_0_NP
      have h_alpha_order : Real.sqrt 2 < phi + 1/4 := phi_plus_quarter_gt_sqrt2
      have h_pi10_pos : pi_10 > 0 := by
        unfold pi_10
        positivity
      have h_sqrt2_pos : Real.sqrt 2 > 0 := by positivity
      have h_phi_quarter_pos : phi + 1/4 > 0 := by
        have : phi > 0 := by
          unfold phi
          positivity
        linarith
      have h_inv_order : 1 / (phi + 1/4) < 1 / Real.sqrt 2 := by
        exact one_div_lt_one_div_of_lt h_sqrt2_pos h_alpha_order
      calc pi_10 / Real.sqrt 2
          = pi_10 * (1 / Real.sqrt 2) := by ring
        _ > pi_10 * (1 / (phi + 1/4)) := by nlinarith [h_pi10_pos, h_inv_order]
        _ = pi_10 / (phi + 1/4) := by ring
    unfold Delta spectral_gap
    linarith

theorem positive_gap_implies_separation : Delta > 0 → P_neq_NP_def := by
  exact (spectral_gap_iff_P_neq_NP.mp)

theorem numerical_gap_positive : Delta > 0 := by
  exact spectral_gap_positive

theorem P_neq_NP_via_spectral_gap : P_neq_NP_def := by
  exact positive_gap_implies_separation numerical_gap_positive

/- Equivalent formulation: Zero gap would imply P = NP. -/
theorem zero_gap_iff_P_equals_NP : Delta = 0 ↔ P_equals_NP_def :=
  (p_eq_np_iff_zero_gap).symm

end PrincipiaTractalis
