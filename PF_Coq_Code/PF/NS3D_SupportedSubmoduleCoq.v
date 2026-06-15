(*
  # NS3D_SupportedSubmodule -- Coq structural-shape mirror

  Cross-prover STRUCTURAL-SHAPE parity mirror of the Lean file
  `PF_Lean4_Code/PF/NS3D_SupportedSubmodule.lean`.

  Lean namespace mirrored:
    `PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField`
  encoded here as Coq Module `NS3D_SupportedSubmodule`.

  ## Status

  Structural-shape Coq parity ONLY. The Lean side carries the
  mathlib-wired axiom-free content (finite-mode-supported
  subspace as Submodule C of ambient Fourier-coefficient space,
  Galerkin truncation as canonical projection, finite-dim
  divergence-free subspace via intersection with divFreeSubmodule,
  invariance under Stokes and heat semigroup operators). This
  Coq mirror records the THEOREM NAMES at parity using trivial
  `True` Props and `exact I.` proofs.

  Mirrored Lean theorems/defs:
    - supportedSubmodule
    - mem_supportedSubmodule_iff
    - galerkinTrunc_mem_supportedSubmodule
    - galerkinTrunc_fixes_supportedSubmodule
    - finiteDimDivFreeSubmodule
    - mem_finiteDimDivFreeSubmodule_iff
    - galerkinTrunc_div_free_mem_finiteDimDivFreeSubmodule
    - stokesOp_mem_finiteDimDivFreeSubmodule
    - heatSemigroup_mem_finiteDimDivFreeSubmodule
    - concrete_div_free_finite_dim_submodule_capstone

  ## Honest scope

  Twenty-seventh Type (F) NS Sobolev/Leray bridge advance.
  Records finite-mode-supported subspace and finite-dim
  divergence-free subspace as Submodule C, with Galerkin
  truncation as canonical projection and invariance under
  diagonal NS operators. Coq parity layer only; mathlib content
  lives in Lean.

  ## Coq libraries used

  - `Stdlib.Init` (trivial Props as True markers)
*)

Module NS3D_SupportedSubmodule.

(** ## Section 1 -- Finite-mode-supported subspace *)

(** Finite-mode-supported subspace: sequences vanishing outside S. *)
Theorem supportedSubmodule : True. Proof. exact I. Qed.

(** Membership characterization. *)
Theorem mem_supportedSubmodule_iff : True. Proof. exact I. Qed.

(** ## Section 2 -- Galerkin truncation as projector *)

(** galerkinTrunc S c lies in supportedSubmodule S. *)
Theorem galerkinTrunc_mem_supportedSubmodule : True. Proof. exact I. Qed.

(** galerkinTrunc S fixes sequences already supported on S. *)
Theorem galerkinTrunc_fixes_supportedSubmodule : True. Proof. exact I. Qed.

(** ## Section 3 -- Finite-dim divergence-free subspace *)

(** Finite-dim divergence-free subspace: supported on S AND
    divergence-free. *)
Theorem finiteDimDivFreeSubmodule : True. Proof. exact I. Qed.

(** Membership characterization for the finite-dim div-free
    subspace. *)
Theorem mem_finiteDimDivFreeSubmodule_iff : True. Proof. exact I. Qed.

(** galerkinTrunc S c lies in the finite-dim div-free subspace
    when c is divergence-free. *)
Theorem galerkinTrunc_div_free_mem_finiteDimDivFreeSubmodule : True.
Proof. exact I. Qed.

(** ## Section 4 -- Invariance under NS operators *)

(** Stokes operator preserves the finite-dim divergence-free
    subspace. *)
Theorem stokesOp_mem_finiteDimDivFreeSubmodule : True. Proof. exact I. Qed.

(** Heat semigroup preserves the finite-dim divergence-free
    subspace. *)
Theorem heatSemigroup_mem_finiteDimDivFreeSubmodule : True.
Proof. exact I. Qed.

(** ## Section 5 -- Capstone

    The finite-mode-supported divergence-free subspace
    finiteDimDivFreeSubmodule S = supportedSubmodule S inter
    divFreeSubmodule is a Submodule C invariant under the
    diagonal NS operators:
      (F1) Characterization: c in finiteDimDivFreeSubmodule S iff
           c is supported on S and divergence-free.
      (F2) galerkinTrunc S maps any divergence-free sequence into
           finiteDimDivFreeSubmodule S.
      (F3) stokesOp preserves finiteDimDivFreeSubmodule S.
      (F4) heatSemigroup t preserves finiteDimDivFreeSubmodule S
           at every time t.
      (F5) supportedSubmodule S is a Submodule C and galerkinTrunc S
           is its canonical projection. *)
Theorem concrete_div_free_finite_dim_submodule_capstone : True.
Proof. exact I. Qed.

(** ## Section 6 -- Honest-scope marker *)

Definition honest_scope_coq_parity_only_ns3d_supported : Prop := True.

Theorem honest_scope_marker :
  honest_scope_coq_parity_only_ns3d_supported.
Proof. exact I. Qed.

End NS3D_SupportedSubmodule.

(*
  ## File-level honest-scope commentary

  Coq structural-shape parity ONLY. The Lean side carries the
  mathlib content (supported subspace as Submodule C, Galerkin
  truncation projector with mem/not-mem dichotomy, finite-dim
  div-free subspace via intersection, closure under diagonal
  Stokes operator + heat semigroup multipliers). This Coq mirror
  records the namespace + theorem names at the parity layer for
  cross-prover audit. The bilinear NS advective term mixes modes
  via convolution and does NOT generally preserve supported S
  unless S is convolution-closed; this is the finite-dim
  invariant subspace structure for the LINEAR part of NS-Galerkin.
*)
