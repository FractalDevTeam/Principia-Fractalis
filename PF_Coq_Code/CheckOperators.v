(* Axiom-dependency audit for PF/TuringEncoding/Operators.v.
   Each derived theorem should depend on:
     * alpha_class_polylog_eigenvalue_conjecture  (the single project axiom)
     * Language, ClassP, ClassNP                (opaque parameters)
     * alpha_of_class                           (opaque parameter)
     * Coq stdlib classical foundation
   Nothing else (no other project axioms). *)

Require Import PrincipiaTractalis.TuringEncoding.Operators.

Print Assumptions alpha_at_ClassP_eq_sqrt2.
Print Assumptions alpha_at_ClassNP_eq_phi_plus_quarter.
Print Assumptions alpha_of_class_pos_at_ClassP.
Print Assumptions alpha_of_class_pos_at_ClassNP.
Print Assumptions alpha_class_distinct.
Print Assumptions alpha_class_separation_lt.
Print Assumptions p_eq_np_spectrum_collapse.
Print Assumptions P_eq_NP_implies_same_ground_energy.
Print Assumptions P_neq_NP_from_spectral_gap.
