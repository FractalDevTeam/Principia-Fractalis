import PF.Axioms
import PF.RH_Equivalence
import PF.YM_Equivalence
import PF.BSD_Equivalence
import PF.TuringEncoding
import PF.P_NP_Equivalence
import PF.ConsciousnessCore

namespace PF_L4L.Core

open PrincipiaTractalis

/--
Tags for groups of axioms used in the PF canonical development. This
is purely classificatory: PF_L4L does not introduce any new axioms, it
simply refers to existing PF constants.
-/
inductive PFAxiomTag where
  | P_vs_NP_prime_encoding
  | P_vs_NP_resonance_spectrum
  | P_vs_NP_numeric_certificates
  | UniversalFramework_consciousness
  | RH_operator_axioms
  | YM_pillar_axioms
  | BSD_pillar_axioms
  deriving DecidableEq, Repr

/--
For each tag, a predicate stating "this group of PF axioms is being
used". The right-hand sides are concrete PF canonical axiom statements
expressed as trivial equalities that explicitly reference the
underlying constants.
-/
noncomputable def uses_axiom (tag : PFAxiomTag) : Prop :=
  match tag with
  | PFAxiomTag.P_vs_NP_prime_encoding =>
      -- Complexity/encoding side of the P vs NP pillar (PF-level encoding axioms).
      (PrincipiaTractalis.nthPrime = PrincipiaTractalis.nthPrime) ∧
      (PrincipiaTractalis.nthPrime_is_prime =
        PrincipiaTractalis.nthPrime_is_prime) ∧
      (PrincipiaTractalis.nthPrime_increasing =
        PrincipiaTractalis.nthPrime_increasing) ∧
      (PrincipiaTractalis.nthPrime_zero =
        PrincipiaTractalis.nthPrime_zero) ∧
      (PrincipiaTractalis.nthPrime_one =
        PrincipiaTractalis.nthPrime_one) ∧
      (PrincipiaTractalis.encodeConfig_injective =
        PrincipiaTractalis.encodeConfig_injective) ∧
      (PrincipiaTractalis.nat_log = PrincipiaTractalis.nat_log) ∧
      (PrincipiaTractalis.encodeConfig_polynomial_time =
        PrincipiaTractalis.encodeConfig_polynomial_time) ∧
      (PrincipiaTractalis.encodeConfig_growth_bound =
        PrincipiaTractalis.encodeConfig_growth_bound)
  | PFAxiomTag.P_vs_NP_resonance_spectrum =>
      -- Resonance/spectral interface axioms for the P vs NP pillar.
      (PrincipiaTractalis.resonance_determines_spectrum =
        PrincipiaTractalis.resonance_determines_spectrum) ∧
      (PrincipiaTractalis.np_not_p_requires_certificate =
        PrincipiaTractalis.np_not_p_requires_certificate) ∧
      (PrincipiaTractalis.p_eq_np_iff_zero_gap =
        PrincipiaTractalis.p_eq_np_iff_zero_gap)
  | PFAxiomTag.P_vs_NP_numeric_certificates =>
      -- Numeric and interval-certification axioms underpinning the
      -- P vs NP spectral gap computation and resonance separation.
      (PrincipiaTractalis.sqrt2_in_interval_ultra =
        PrincipiaTractalis.sqrt2_in_interval_ultra) ∧
      (PrincipiaTractalis.phi_in_interval_ultra =
        PrincipiaTractalis.phi_in_interval_ultra) ∧
      (PrincipiaTractalis.sqrt2_lower =
        PrincipiaTractalis.sqrt2_lower) ∧
      (PrincipiaTractalis.sqrt2_upper =
        PrincipiaTractalis.sqrt2_upper) ∧
      (PrincipiaTractalis.phi_lower =
        PrincipiaTractalis.phi_lower) ∧
      (PrincipiaTractalis.phi_upper =
        PrincipiaTractalis.phi_upper) ∧
      (PrincipiaTractalis.phi_plus_quarter_gt_sqrt2 =
        PrincipiaTractalis.phi_plus_quarter_gt_sqrt2) ∧
      (PrincipiaTractalis.sqrt2_lt_1415 =
        PrincipiaTractalis.sqrt2_lt_1415) ∧
      (PrincipiaTractalis.phi_gt_16 =
        PrincipiaTractalis.phi_gt_16) ∧
      (PrincipiaTractalis.lambda_P_lower_certified =
        PrincipiaTractalis.lambda_P_lower_certified) ∧
      (PrincipiaTractalis.lambda_P_upper_certified =
        PrincipiaTractalis.lambda_P_upper_certified) ∧
      (PrincipiaTractalis.lambda_NP_lower_certified =
        PrincipiaTractalis.lambda_NP_lower_certified) ∧
      (PrincipiaTractalis.lambda_NP_upper_certified =
        PrincipiaTractalis.lambda_NP_upper_certified) ∧
      (PrincipiaTractalis.lambda_0_P_precise =
        PrincipiaTractalis.lambda_0_P_precise) ∧
      (PrincipiaTractalis.lambda_0_NP_precise =
        PrincipiaTractalis.lambda_0_NP_precise) ∧
      (PrincipiaTractalis.lambda_P_pi10_relation =
        PrincipiaTractalis.lambda_P_pi10_relation) ∧
      (PrincipiaTractalis.lambda_NP_pi10_relation =
        PrincipiaTractalis.lambda_NP_pi10_relation)
  | PFAxiomTag.UniversalFramework_consciousness =>
      -- Global consciousness/framework assumptions, now tied to PF-level
      -- consciousness constants in `PF.ConsciousnessCore` that summarize
      -- the ch₂ pattern across the four PF pillars.
      (PrincipiaTractalis.ch2_universal_threshold =
        PrincipiaTractalis.ch2_universal_threshold) ∧
      (PrincipiaTractalis.ch2_P_vs_NP =
        PrincipiaTractalis.ch2_P_vs_NP) ∧
      (PrincipiaTractalis.ch2_RH =
        PrincipiaTractalis.ch2_RH) ∧
      (PrincipiaTractalis.ch2_YM =
        PrincipiaTractalis.ch2_YM) ∧
      (PrincipiaTractalis.ch2_BSD =
        PrincipiaTractalis.ch2_BSD)
  | PFAxiomTag.RH_operator_axioms =>
      -- Operator-theoretic assumptions entering the RH pillar.
      (PrincipiaTractalis.LogHilbertSpace =
        PrincipiaTractalis.LogHilbertSpace) ∧
      (PrincipiaTractalis.T3_self_adjoint =
        PrincipiaTractalis.T3_self_adjoint) ∧
      (PrincipiaTractalis.T3_compact =
        PrincipiaTractalis.T3_compact) ∧
      (PrincipiaTractalis.eigenvalue_convergence_rate =
        PrincipiaTractalis.eigenvalue_convergence_rate) ∧
      (PrincipiaTractalis.T3_eigenvalues_real =
        PrincipiaTractalis.T3_eigenvalues_real) ∧
      (PrincipiaTractalis.eigenvalue_zero_bijection =
        PrincipiaTractalis.eigenvalue_zero_bijection) ∧
      (PrincipiaTractalis.spectral_bijection_iff_RH =
        PrincipiaTractalis.spectral_bijection_iff_RH)
  | PFAxiomTag.YM_pillar_axioms =>
      -- QFT/measure-theoretic assumptions for the Yang–Mills pillar.
      (PrincipiaTractalis.GaugeGroup = PrincipiaTractalis.GaugeGroup) ∧
      (PrincipiaTractalis.FieldStrength = PrincipiaTractalis.FieldStrength) ∧
      (PrincipiaTractalis.standard_YM_action =
        PrincipiaTractalis.standard_YM_action) ∧
      (PrincipiaTractalis.mass_gap_property =
        PrincipiaTractalis.mass_gap_property) ∧
      (PrincipiaTractalis.R_f_at_alpha_2 =
        PrincipiaTractalis.R_f_at_alpha_2) ∧
      (PrincipiaTractalis.resonance_coefficient =
        PrincipiaTractalis.resonance_coefficient) ∧
      (PrincipiaTractalis.omega_critical_is_zero =
        PrincipiaTractalis.omega_critical_is_zero) ∧
      (PrincipiaTractalis.omega_critical_is_first_zero =
        PrincipiaTractalis.omega_critical_is_first_zero) ∧
      (PrincipiaTractalis.omega_critical_numerical_precision =
        PrincipiaTractalis.omega_critical_numerical_precision) ∧
      (PrincipiaTractalis.mass_gap_numerical_value =
        PrincipiaTractalis.mass_gap_numerical_value) ∧
      (PrincipiaTractalis.fractal_YM_action =
        PrincipiaTractalis.fractal_YM_action) ∧
      (PrincipiaTractalis.fractal_action_properties =
        PrincipiaTractalis.fractal_action_properties) ∧
      (PrincipiaTractalis.NuclearSpace =
        PrincipiaTractalis.NuclearSpace) ∧
      (PrincipiaTractalis.minlos_theorem =
        PrincipiaTractalis.minlos_theorem) ∧
      (PrincipiaTractalis.YM_measure_exists =
        PrincipiaTractalis.YM_measure_exists) ∧
      (PrincipiaTractalis.WilsonLoop =
        PrincipiaTractalis.WilsonLoop) ∧
      (PrincipiaTractalis.wilson_loop_expectation =
        PrincipiaTractalis.wilson_loop_expectation) ∧
      (PrincipiaTractalis.string_tension_value =
        PrincipiaTractalis.string_tension_value) ∧
      (PrincipiaTractalis.area_law_confinement =
        PrincipiaTractalis.area_law_confinement) ∧
      (PrincipiaTractalis.mass_gap_iff_YM =
        PrincipiaTractalis.mass_gap_iff_YM) ∧
      (PrincipiaTractalis.YM_perfect_consciousness =
        PrincipiaTractalis.YM_perfect_consciousness) ∧
      (PrincipiaTractalis.confinement_via_measurement =
        PrincipiaTractalis.confinement_via_measurement)
  | PFAxiomTag.BSD_pillar_axioms =>
      -- Spectral and algorithmic assumptions for the BSD pillar.
      (PrincipiaTractalis.RationalPoints =
        PrincipiaTractalis.RationalPoints) ∧
      (PrincipiaTractalis.algebraic_rank =
        PrincipiaTractalis.algebraic_rank) ∧
      (PrincipiaTractalis.trace_of_frobenius =
        PrincipiaTractalis.trace_of_frobenius) ∧
      (PrincipiaTractalis.conductor =
        PrincipiaTractalis.conductor) ∧
      (PrincipiaTractalis.L_function =
        PrincipiaTractalis.L_function) ∧
      (PrincipiaTractalis.L_function_order_at_1 =
        PrincipiaTractalis.L_function_order_at_1) ∧
      (PrincipiaTractalis.BSD_strong_conjecture =
        PrincipiaTractalis.BSD_strong_conjecture) ∧
      (PrincipiaTractalis.BSD_proven_rank_0_1 =
        PrincipiaTractalis.BSD_proven_rank_0_1) ∧
      (PrincipiaTractalis.fractal_L_function =
        PrincipiaTractalis.fractal_L_function) ∧
      (PrincipiaTractalis.T_E =
        PrincipiaTractalis.T_E) ∧
      (PrincipiaTractalis.T_E_self_adjoint =
        PrincipiaTractalis.T_E_self_adjoint) ∧
      (PrincipiaTractalis.spectral_concentration =
        PrincipiaTractalis.spectral_concentration) ∧
      (PrincipiaTractalis.rank_equals_multiplicity =
        PrincipiaTractalis.rank_equals_multiplicity) ∧
      (PrincipiaTractalis.fractal_rank_algorithm_complexity =
        PrincipiaTractalis.fractal_rank_algorithm_complexity) ∧
      (PrincipiaTractalis.L_function_formula_iff_BSD =
        PrincipiaTractalis.L_function_formula_iff_BSD) ∧
      (PrincipiaTractalis.BSD_highest_consciousness =
        PrincipiaTractalis.BSD_highest_consciousness)

/-- Convenience predicates indicating which tags a given pillar uses. -/
noncomputable def uses_P_vs_NP_axioms (tag : PFAxiomTag) : Prop :=
  tag = PFAxiomTag.P_vs_NP_prime_encoding ∨
  tag = PFAxiomTag.P_vs_NP_resonance_spectrum ∨
  tag = PFAxiomTag.P_vs_NP_numeric_certificates ∨
  tag = PFAxiomTag.UniversalFramework_consciousness

noncomputable def uses_RH_axioms (tag : PFAxiomTag) : Prop :=
  tag = PFAxiomTag.RH_operator_axioms ∨
  tag = PFAxiomTag.UniversalFramework_consciousness

noncomputable def uses_YM_axioms (tag : PFAxiomTag) : Prop :=
  tag = PFAxiomTag.YM_pillar_axioms ∨
  tag = PFAxiomTag.UniversalFramework_consciousness

noncomputable def uses_BSD_axioms (tag : PFAxiomTag) : Prop :=
  tag = PFAxiomTag.BSD_pillar_axioms ∨
  tag = PFAxiomTag.UniversalFramework_consciousness

lemma ch2_pillars_in_band_PF_L4L (c : ℝ)
  (h : c = ch2_P_vs_NP ∨ c = ch2_RH ∨ c = ch2_YM ∨ c = ch2_BSD) :
  0.90 ≤ c ∧ c ≤ 1.25 :=
  PrincipiaTractalis.ch2_pillars_in_band c h

end PF_L4L.Core
