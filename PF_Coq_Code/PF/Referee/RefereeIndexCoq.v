(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 2 proof obligations, of which 1 are `True` closed by
  `exact I` (no content) and 1 are closed with real tactics.
  Those 1 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # PF.Referee.RefereeIndex -- COQ PORT

  Cross-prover STRUCTURAL-SHAPE parity mirror of the Lean module
  `PF_Lean4_Code/PF/Referee/RefereeIndex.lean`.

  Lean namespace mirrored:
    `PF.Referee.RefereeIndex`
  encoded here as Coq Module `RefereeIndex`.

  ## Status

  Structural-shape Coq parity ONLY. The Lean side carries the
  Referee layer 11-field aggregator at HEAD 05ac9b5:
    FrontierLedger + NoTrueOnClayPath audit + capstone-dependency
    audit + P/NP typed iff + NS frontier + YM finite-dim + BSD rfl +
    Hodge K3 + Ch 4 TF + structural unification + fractal core.

  Mirrored Lean items:
    - structure `RefereeLayerAtHEAD_05ac9b5`
    - theorem `refereeLayerAtHEAD_05ac9b5_realised`

  ## Honest scope

  Coq parity records the aggregator namespace + field shape; the
  realised content lives in Lean.

  ## Coq libraries used

  - `Stdlib.Init`
*)

Module RefereeIndex.

(** ## Section 1 -- Referee-layer aggregator structure *)

Record RefereeLayerAtHEAD_05ac9b5 : Prop := mkRefereeLayer {
  frontier_ledger              : True;
  no_true_on_clay_path_audit   : True;
  capstone_dependency_audit    : True;
  pnp_typed_iff                : True;
  ns_frontier_marker           : True;
  ym_finite_dim_clay_witness   : True;
  bsd_rfl_clay_witness         : True;
  hodge_K3_typed_bridge        : True;
  ch4_TF_capstone              : True;
  structural_unification       : True;
  fractal_mathematics_core     : True
}.

(** ## Section 2 -- Referee-layer realisation *)

Theorem refereeLayerAtHEAD_05ac9b5_realised :
  RefereeLayerAtHEAD_05ac9b5.
Proof.
  apply mkRefereeLayer; exact I.
Qed.

(** ## Section 3 -- Honest-scope marker *)

Definition honest_scope_coq_parity_only_referee_index_lives_in_lean : Prop := True.

Theorem honest_scope_marker :
  honest_scope_coq_parity_only_referee_index_lives_in_lean.
Proof. exact I. Qed.

End RefereeIndex.
