(*
  === SHAPE INDEX ONLY — NO MATHEMATICAL CONTENT ===
  Every theorem in this file is `True`, proved by `exact I`. Nothing here is
  verified mathematics. This file records Lean declaration names and file
  dependency shape only.
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # NS3D_NonlinearBilinear -- NS nonlinear bilinear form
     B(u, v) = P((u . grad) v) on a finite mode set
  COQ STRUCTURAL-SHAPE PARITY MIRROR

  Cross-prover STRUCTURAL-SHAPE parity mirror of the Lean file:
    `PF_Lean4_Code/PF/NS3D_NonlinearBilinear.lean`.

  Lean namespace mirrored:
    `PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField`
  encoded here as Coq Module `NS3D_NonlinearBilinear`.

  ## Status

  Structural-shape Coq parity ONLY. The Lean side carries the
  mathlib-wired axiom-free content (bilinearCore on a finite mode
  set, Leray projection, bilinearity, scalar homogeneity, image
  in divergence-free subspace). This Coq mirror records the
  THEOREM and DEFINITION NAMES at parity granularity using
  `Prop := True` definitions and `exact I.` proofs.

  Mirrored Lean definitions and theorems:
    - convIndex                       (def)
    - mem_convIndex_iff               (theorem)
    - bilinearCore                    (def)
    - bilinearCoreFn                  (def)
    - bilinearCore_zero_left          (theorem)
    - bilinearCore_zero_right         (theorem)
    - bilinearCore_add_left           (theorem)
    - bilinearCore_add_right          (theorem)
    - bilinearCore_smul_left          (theorem)
    - bilinearCore_smul_right         (theorem)
    - nsBilinear                      (def)
    - nsBilinear_div_free             (theorem)
    - nsBilinear_add_left             (theorem)
    - nsBilinear_add_right            (theorem)
    - nsBilinear_smul_left            (theorem)
    - nsBilinear_smul_right           (theorem)
    - concrete_div_free_ns_bilinear_capstone (capstone)

  ## Coq libraries used
  - `Stdlib.Init` (trivial Props as True markers)
*)

Module NS3D_NonlinearBilinear.

(** ## Section 1 -- Convolution-style index set *)

Theorem convIndex : True.
Proof. exact I. Qed.

Theorem mem_convIndex_iff : True.
Proof. exact I. Qed.

(** ## Section 2 -- Pre-projection bilinear core *)

Theorem bilinearCore : True.
Proof. exact I. Qed.

Theorem bilinearCoreFn : True.
Proof. exact I. Qed.

(** ## Section 3 -- Vanishing on zero arguments *)

Theorem bilinearCore_zero_left : True.
Proof. exact I. Qed.

Theorem bilinearCore_zero_right : True.
Proof. exact I. Qed.

(** ## Section 4 -- Bilinearity *)

Theorem bilinearCore_add_left : True.
Proof. exact I. Qed.

Theorem bilinearCore_add_right : True.
Proof. exact I. Qed.

Theorem bilinearCore_smul_left : True.
Proof. exact I. Qed.

Theorem bilinearCore_smul_right : True.
Proof. exact I. Qed.

(** ## Section 5 -- Leray-projected NS bilinear form *)

Theorem nsBilinear : True.
Proof. exact I. Qed.

Theorem nsBilinear_div_free : True.
Proof. exact I. Qed.

Theorem nsBilinear_add_left : True.
Proof. exact I. Qed.

Theorem nsBilinear_add_right : True.
Proof. exact I. Qed.

Theorem nsBilinear_smul_left : True.
Proof. exact I. Qed.

Theorem nsBilinear_smul_right : True.
Proof. exact I. Qed.

(** ## Section 6 -- Capstone

    The NS NONLINEAR BILINEAR FORM CAPSTONE bundles five conjuncts:
    (B1) image in div-free subspace
    (B2) additivity in left slot
    (B2) additivity in right slot
    (B3) scalar homogeneity in left slot
    (B3) scalar homogeneity in right slot *)

Theorem concrete_div_free_ns_bilinear_capstone : True.
Proof. exact I. Qed.

(** ## Section 7 -- Honest-scope marker *)

Definition honest_scope_coq_parity_only_not_a_clay_discharge : Prop := True.
Theorem honest_scope_marker :
  honest_scope_coq_parity_only_not_a_clay_discharge.
Proof. exact I. Qed.

End NS3D_NonlinearBilinear.

(*
  ## File-level honest-scope commentary

  1. Coq structural-shape parity ONLY. The Lean side composes
     axiom-free content (convIndex, bilinearCore, Leray projection,
     bilinearity, scalar homogeneity) by exact name. This Coq mirror
     records the namespace + def/theorem names using True markers.

  2. The bilinear form B(u,v) = P((u . grad) v) is the substrate-
     level NS advective nonlinearity at the Fourier level. Combined
     with the linear heat semigroup infrastructure, it supports the
     NS-Galerkin mild-solution formula
       u(t) = e^{-tA} u_0 - integral_0^t e^{-(t-s)A} B(u(s),u(s)) ds.

  3. ZERO project axioms on the Lean side; kernel-only
     `[propext, Classical.choice, Quot.sound]`.

  4. Same veracity standard as other Wave 51B Coq mirrors:
     cross-prover structural shape, mathlib content lives in Lean.
*)
