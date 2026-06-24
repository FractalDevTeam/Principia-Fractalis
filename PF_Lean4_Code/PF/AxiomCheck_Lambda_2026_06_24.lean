import PF.Cosmology.LambdaEffParameterFreeCapstone
import PF.Cosmology.E6ChernIndex78pi

/-!
# Axiom-set verification for the §4.4 cosmological-constant centerpiece (paper 2026-06-24)

Produces `#print axioms` output for the five theorems §4.4 of the clean paper
cites by name. A reader running `lake build PF.AxiomCheck_Lambda_2026_06_24`
on a clean clone receives the verbatim kernel report, confirming that the
§4.4 derivation chain is kernel-only beyond the three Lean kernel axioms.

Expected output (verbatim at HEAD `a1d86f5`):

  Lambda_eff_exponent_product_rational_form
    depends on axioms: [propext, Classical.choice, Quot.sound]

  Lambda_eff_exponent_product_sharp_bracket
    depends on axioms: [propext, Classical.choice, Quot.sound]

  Lambda_eff_parameter_free_capstone
    depends on axioms: [propext, Classical.choice, Quot.sound]

  capstone_step2_N_eq_78pi
    depends on axioms: [propext, Classical.choice, Quot.sound]

  capstone_step1_E6_dim
    does not depend on any axioms

The first four reach `pi_gt_d6` / `pi_lt_d6` from mathlib, which carry the
three Lean kernel axioms; the fifth is pure arithmetic on `ℕ` discharged
by `decide`, hence no axiom dependency at all.

This file is the audit trail for the paper's claim that the §4.4
substrate-internal cosmological-constant derivation chain is kernel-only.
ZERO project axioms enter anywhere in the chain.
-/

#print axioms PrincipiaTractalis.Cosmology.Lambda_eff_exponent_product_rational_form
#print axioms PrincipiaTractalis.Cosmology.Lambda_eff_exponent_product_sharp_bracket
#print axioms PrincipiaTractalis.Cosmology.Lambda_eff_parameter_free_capstone
#print axioms PrincipiaTractalis.Cosmology.capstone_step2_N_eq_78pi
#print axioms PrincipiaTractalis.Cosmology.capstone_step1_E6_dim
