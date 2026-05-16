(* Axiom-dependency audit for PF/SpectralGap.v.
   All theorems should depend ONLY on Coq stdlib classical
   foundation - NO project axioms. *)

Require Import PrincipiaTractalis.SpectralGap.

Print Assumptions lambda_P_pi10_relation.
Print Assumptions lambda_NP_pi10_relation.
Print Assumptions universal_pi_10_coupling.
Print Assumptions lambda_0_P_pos.
Print Assumptions lambda_0_NP_pos.
Print Assumptions lambda_0_NP_lt_lambda_0_P.
Print Assumptions spectral_gap_pos.
Print Assumptions P_neq_NP_via_spectral_gap.
