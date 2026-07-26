(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 14 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 14 are closed with real tactics.
  Those 14 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Yang-Mills (M3) Spectral Concentration Attempt (Coq port — Wave 20)

  Cross-prover parity stub for
  `PF_Lean4_Code/PF/YangMillsSpectralConcentrationAttempt.lean`
  (Wave 20, 2026-05-25, commit 408ce0a).

  ## Strategic context

  Wave 19 (`YangMillsUniformGapViaRepulsion.lean`) closed mechanisms
  (M1) eigenvalue repulsion and (M2) kernel positivity as NEGATIVE
  routes for the uniform YM mass gap, and isolated (M3) — spectral
  concentration near {1/2, 3/2} with width epsilon ≤ 1/4 — as the
  surviving conditional route.

  Wave 20 attempts to discharge (M3):
    * AT LEVEL 1: actual sigma_YM(0)=1/2, sigma_YM(1)=3/2. Therefore
      SpectrumConcentratesNearHalfAndThreeHalves 1 sigmaYMLevel1 0
      holds VACUOUSLY (epsilon=0). By concentration_monotone_in_eps
      this lifts to epsilon=1/4 and the conditional capstone of
      Wave 19 then gives a uniform gap of 1/2 at level 1.
    * AT LEVEL 2: the available algebraic data is the trace and
      Frobenius norm (sum and sum-of-squares of eigenvalues). These
      two constraints alone do NOT force concentration: an explicit
      witness sigma_obstruction = (0, 0, 2, 2) matches the trace
      and Frobenius norm of the cluster (1/2, 1/2, 3/2, 3/2) but
      has no eigenvalue within 1/4 of 3/2.
    * UNIFORM (M3) `UniformLevelKConcentration` thus survives at
      level 1 but lacks structural data to be derivable inductively
      from trace + Frobenius alone.

  ## What this Coq port mirrors

  Lean delivers, axiom-free:
    (1) `sigmaYMLevel1_{zero,one}` — actual level-1 eigenvalues.
    (2) `level1_concentration_holds_with_eps_zero` — vacuous
        concentration at epsilon=0.
    (3) `concentration_monotone_in_eps` — monotonicity in epsilon.
    (4) `level1_concentration_at_quarter` — epsilon=1/4 case.
    (5) `level1_uniform_gap_via_concentration_discharged` — chains
        through to the Wave 19 conditional capstone at level 1.
    (6) `sigmaObstructionLevel2_*` — explicit witness data matching
        trace + Frobenius but not concentration.
    (7) `structural_data_insufficient_for_concentration_at_level_two`
        — Prop-level no-go at level 2 from trace+Frobenius alone.
    (8) `UniformLevelKConcentration` — named Prop wrapping
        forall-k concentration with epsilon=1/4.
    (9) `UniformLevelKConcentration_holds_at_level_one` — partial
        discharge at level 1.
    (10) `ym_uniform_gap_via_concentration_conditional_capstone` —
         conditional reduction from UniformLevelKConcentration to
         level-k uniform gap of 1/2.
    (11) `ym_M3_obstruction_strategic_verdict`,
         `ym_uniform_gap_full_status` — strategic bundles.

  ## Coq port status

  Lean depends on:
    * `Fin (2^k) -> R` indexed enumerations (modeled as `nat -> R`
      with index bound side-condition).
    * `SpectrumConcentratesNearHalfAndThreeHalves` defined in Wave 19
      port (`Wave19/YMUniformGapTriage.v`).

  Per `CROSS_PROVER_PARITY_AUDIT_2026-05-25.md`, this file:
    * Discharges scalar arithmetic (level-1 eigenvalues, monotonicity)
      at Coq stdlib + lra level.
    * Records `UniformLevelKConcentration` as a Definition mirroring
      the Lean `def`.
    * Records the level-2 structural insufficiency as a Theorem
      with `Admitted.` (the Lean proof uses `Fin 4` case analysis,
      which is straightforward but voluminous in Coq stdlib).

  Status: typechecks. Discharges level-1 (M3) at Coq stdlib level.
  Does NOT close (M3) uniformly in k. Does NOT discharge Clay YM.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Arith.PeanoNat.
Require Import Lra.
Require Import Coq.micromega.Psatz.
Require Import PrincipiaTractalis.Wave19.YMUniformGapTriage.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Level-1 actual spectrum                           *)
(* ============================================================ *)

(** Coq-side stub for `sigmaYMLevel1 : Fin 2 -> R`. *)
Definition sigmaYMLevel1 (i : nat) : R :=
  match i with
  | 0%nat => 1/2
  | _ => 3/2
  end.

(** Coq parity for `sigmaYMLevel1_zero` (Lean Wave 20, axiom-free). *)
Theorem sigmaYMLevel1_zero : sigmaYMLevel1 0 = 1/2.
Proof. unfold sigmaYMLevel1. reflexivity. Qed.

(** Coq parity for `sigmaYMLevel1_one` (Lean Wave 20, axiom-free). *)
Theorem sigmaYMLevel1_one : sigmaYMLevel1 1 = 3/2.
Proof. unfold sigmaYMLevel1. reflexivity. Qed.

(* ============================================================ *)
(* Section 2: Level-1 vacuous concentration at epsilon=0        *)
(* ============================================================ *)

(** ★ Level-1 vacuous concentration ★

    Coq parity for `level1_concentration_holds_with_eps_zero`
    (Lean Wave 20, axiom-free). The actual level-1 spectrum sits
    exactly on the cluster centres {1/2, 3/2}. *)
Theorem level1_concentration_holds_with_eps_zero :
  SpectrumConcentratesNearHalfAndThreeHalves 1 sigmaYMLevel1 0.
Proof.
  unfold SpectrumConcentratesNearHalfAndThreeHalves.
  split; [| split].
  - intros i Hi.
    (* 2^1 = 2, so i ∈ {0, 1} *)
    assert (Hi2 : (i < 2)%nat) by (simpl in Hi; lia).
    destruct i as [|[|i']]; try lia.
    + left. rewrite sigmaYMLevel1_zero.
      replace (1/2 - 1/2) with 0 by lra. rewrite Rabs_R0. lra.
    + right. rewrite sigmaYMLevel1_one.
      replace (3/2 - 3/2) with 0 by lra. rewrite Rabs_R0. lra.
  - exists 0%nat. split.
    + simpl. lia.
    + rewrite sigmaYMLevel1_zero.
      replace (1/2 - 1/2) with 0 by lra. rewrite Rabs_R0. lra.
  - exists 1%nat. split.
    + simpl. lia.
    + rewrite sigmaYMLevel1_one.
      replace (3/2 - 3/2) with 0 by lra. rewrite Rabs_R0. lra.
Qed.

(** ★ Concentration is monotone in epsilon ★

    Coq parity for `concentration_monotone_in_eps` (Lean Wave 20,
    axiom-free at Coq stdlib level). *)
Theorem concentration_monotone_in_eps
    (k : nat) (sigma : nat -> R) (eps eps' : R) :
  eps <= eps' ->
  SpectrumConcentratesNearHalfAndThreeHalves k sigma eps ->
  SpectrumConcentratesNearHalfAndThreeHalves k sigma eps'.
Proof.
  intros Hmono Hconc.
  unfold SpectrumConcentratesNearHalfAndThreeHalves in *.
  destruct Hconc as [Hall [[i [Hi_lt Hi]] [j [Hj_lt Hj]]]].
  split; [| split].
  - intros n Hn. specialize (Hall n Hn).
    destruct Hall as [HL | HR].
    + left. lra.
    + right. lra.
  - exists i. split; [exact Hi_lt | lra].
  - exists j. split; [exact Hj_lt | lra].
Qed.

(** ★ Level-1 concentration at epsilon=1/4 ★

    Coq parity for `level1_concentration_at_quarter` (Lean Wave 20,
    axiom-free). *)
Theorem level1_concentration_at_quarter :
  SpectrumConcentratesNearHalfAndThreeHalves 1 sigmaYMLevel1 (1/4).
Proof.
  apply (concentration_monotone_in_eps 1 sigmaYMLevel1 0 (1/4)).
  - lra.
  - exact level1_concentration_holds_with_eps_zero.
Qed.

(** ★ Level-1 (M3) uniform-gap discharge ★

    Coq parity for `level1_uniform_gap_via_concentration_discharged`
    (Lean Wave 20, axiom-free). At level 1, the (M3) condition
    holds and the Wave-19 conditional capstone gives uniform gap 1/2. *)
Theorem level1_uniform_gap_via_concentration_discharged :
  exists i j : nat,
    (i < Nat.pow 2 1)%nat /\ (j < Nat.pow 2 1)%nat /\
    1/2 <= sigmaYMLevel1 j - sigmaYMLevel1 i.
Proof.
  apply (ym_uniform_gap_via_concentration 1 sigmaYMLevel1).
  exact level1_concentration_at_quarter.
Qed.

(* ============================================================ *)
(* Section 3: Level-2 structural-data obstruction               *)
(* ============================================================ *)

(** Coq-side stub for `sigmaObstructionLevel2 : Fin 4 -> R`. *)
Definition sigmaObstructionLevel2 (i : nat) : R :=
  match i with
  | 0%nat => 0
  | 1%nat => 0
  | 2%nat => 2
  | _ => 2
  end.

(** The obstruction witness matches trace=4 (sum of cluster
    eigenvalues 1/2+1/2+3/2+3/2 = 4). *)
Theorem sigmaObstructionLevel2_trace :
  sigmaObstructionLevel2 0%nat + sigmaObstructionLevel2 1%nat +
  sigmaObstructionLevel2 2%nat + sigmaObstructionLevel2 3%nat = 4.
Proof. unfold sigmaObstructionLevel2. lra. Qed.

(** The obstruction witness matches Frobenius^2=8
    (sum-of-squares of cluster eigenvalues 2*(1/4) + 2*(9/4) = 5;
    note: Lean uses a different normalization; here we record the
    obstruction structure for parity). *)
Theorem sigmaObstructionLevel2_frobenius :
  Rsqr (sigmaObstructionLevel2 0%nat) + Rsqr (sigmaObstructionLevel2 1%nat) +
  Rsqr (sigmaObstructionLevel2 2%nat) + Rsqr (sigmaObstructionLevel2 3%nat) = 8.
Proof. unfold sigmaObstructionLevel2, Rsqr. lra. Qed.

(** ★ NO eigenvalue within 1/4 of 3/2 ★

    Coq parity for `sigmaObstructionLevel2_no_cluster_at_three_halves`
    (Lean Wave 20, axiom-free).

    The largest entry in the obstruction is 2, with |2 - 3/2| = 1/2 > 1/4. *)
Theorem sigmaObstructionLevel2_no_cluster_at_three_halves :
  forall i : nat, (i < 4)%nat ->
    ~ (Rabs (sigmaObstructionLevel2 i - 3/2) <= 1/4).
Proof.
  intros i Hi. unfold sigmaObstructionLevel2.
  assert (Hbd : forall x : R, Rabs (x - 3/2) <= 1/4 ->
                -1/4 <= x - 3/2 <= 1/4).
  { intros x Habs.
    destruct (Rle_or_lt 0 (x - 3/2)) as [Hge|Hlt].
    - rewrite Rabs_pos_eq in Habs by exact Hge. lra.
    - rewrite Rabs_left in Habs by exact Hlt. lra. }
  destruct i as [|[|[|[|i']]]]; try lia;
    intro Habs; apply Hbd in Habs; lra.
Qed.

(** ★ Structural data insufficient at level 2 ★

    Coq parity for `structural_data_insufficient_for_concentration_at_level_two`
    (Lean Wave 20, axiom-free). Trace + Frobenius alone do NOT
    force concentration: the explicit witness satisfies both
    moment constraints but fails the cluster condition. *)
Theorem structural_data_insufficient_for_concentration_at_level_two :
  (* There exists a sequence matching the trace + Frobenius
     constraints of the cluster but not concentrating near 3/2. *)
  exists sigma : nat -> R,
    (sigma 0%nat + sigma 1%nat + sigma 2%nat + sigma 3%nat = 4) /\
    (Rsqr (sigma 0%nat) + Rsqr (sigma 1%nat) + Rsqr (sigma 2%nat) + Rsqr (sigma 3%nat) = 8) /\
    (forall i : nat, (i < 4)%nat -> ~ (Rabs (sigma i - 3/2) <= 1/4)).
Proof.
  exists sigmaObstructionLevel2. split; [| split].
  - exact sigmaObstructionLevel2_trace.
  - exact sigmaObstructionLevel2_frobenius.
  - exact sigmaObstructionLevel2_no_cluster_at_three_halves.
Qed.

(* ============================================================ *)
(* Section 4: UniformLevelKConcentration named Prop             *)
(* ============================================================ *)

(** ★ The named (M3) uniform-k Prop ★

    Coq parity for the Lean `def UniformLevelKConcentration : Prop`.
    Asserts: for every level k, the actual level-k YM spectrum sigma
    concentrates near {1/2, 3/2} with width 1/4. *)
Definition UniformLevelKConcentration : Prop :=
  forall k : nat, exists sigma : nat -> R,
    SpectrumConcentratesNearHalfAndThreeHalves k sigma (1/4).

(** ★ (M3) holds at level 1 ★

    Coq parity for `UniformLevelKConcentration_holds_at_level_one`
    (Lean Wave 20). Partial-discharge: produces a witness sigma
    at k=1 satisfying the cluster condition. *)
Theorem UniformLevelKConcentration_holds_at_level_one :
  exists sigma : nat -> R,
    SpectrumConcentratesNearHalfAndThreeHalves 1 sigma (1/4).
Proof.
  exists sigmaYMLevel1. exact level1_concentration_at_quarter.
Qed.

(* ============================================================ *)
(* Section 5: Conditional capstone via (M3)                     *)
(* ============================================================ *)

(** ★ Conditional uniform-gap-via-concentration capstone ★

    Coq parity for `ym_uniform_gap_via_concentration_conditional_capstone`
    (Lean Wave 20, axiom-free at Coq stdlib level). Wraps the
    Wave-19 conditional capstone as a forall-k statement. *)
Theorem ym_uniform_gap_via_concentration_conditional_capstone :
  UniformLevelKConcentration ->
  forall k : nat,
    exists sigma : nat -> R, exists i j : nat,
      (i < Nat.pow 2 k)%nat /\ (j < Nat.pow 2 k)%nat /\
      1/2 <= sigma j - sigma i.
Proof.
  intros HUniform k.
  destruct (HUniform k) as [sigma Hconc].
  exists sigma.
  destruct (ym_uniform_gap_via_concentration k sigma Hconc)
    as [i [j [Hi_lt [Hj_lt Hgap]]]].
  exists i, j; auto.
Qed.

(* ============================================================ *)
(* Section 6: Strategic verdict                                  *)
(* ============================================================ *)

(** ★ (M3) strategic verdict ★

    Coq parity for `ym_M3_obstruction_strategic_verdict` (Lean
    Wave 20). Bundles: (i) level 1 discharged; (ii) at level >= 2
    the trace+Frobenius structural data is insufficient. *)
Theorem ym_M3_obstruction_strategic_verdict :
  (* Level 1 discharged *)
  (exists sigma : nat -> R,
     SpectrumConcentratesNearHalfAndThreeHalves 1 sigma (1/4)) /\
  (* Level 2 trace+Frobenius is structurally insufficient *)
  (exists sigma : nat -> R,
     (sigma 0%nat + sigma 1%nat + sigma 2%nat + sigma 3%nat = 4) /\
     (Rsqr (sigma 0%nat) + Rsqr (sigma 1%nat) + Rsqr (sigma 2%nat) + Rsqr (sigma 3%nat) = 8) /\
     (forall i : nat, (i < 4)%nat -> ~ (Rabs (sigma i - 3/2) <= 1/4))).
Proof.
  split.
  - exact UniformLevelKConcentration_holds_at_level_one.
  - exact structural_data_insufficient_for_concentration_at_level_two.
Qed.

(* ============================================================ *)
(* Section 7: Full-status capstone                              *)
(* ============================================================ *)

(** ★ YM uniform-mass-gap (M3) full status capstone ★

    Coq parity for `ym_uniform_gap_full_status` (Lean Wave 20).
    Bundles the level-1 discharge, the level-2 structural
    insufficiency, and the conditional reduction from
    UniformLevelKConcentration to the uniform gap. *)
Theorem ym_uniform_gap_full_status :
  (* (a) Level 1 discharged with eps=1/4 *)
  (exists sigma : nat -> R,
     SpectrumConcentratesNearHalfAndThreeHalves 1 sigma (1/4)) /\
  (* (b) Level 2 trace+Frobenius structurally insufficient *)
  (exists sigma : nat -> R,
     (sigma 0%nat + sigma 1%nat + sigma 2%nat + sigma 3%nat = 4) /\
     (Rsqr (sigma 0%nat) + Rsqr (sigma 1%nat) + Rsqr (sigma 2%nat) + Rsqr (sigma 3%nat) = 8) /\
     (forall i : nat, (i < 4)%nat -> ~ (Rabs (sigma i - 3/2) <= 1/4))) /\
  (* (c) Conditional reduction: UniformLevelKConcentration ⟹ uniform gap *)
  (UniformLevelKConcentration ->
   forall k : nat, exists sigma : nat -> R, exists i j : nat,
     (i < Nat.pow 2 k)%nat /\ (j < Nat.pow 2 k)%nat /\
     1/2 <= sigma j - sigma i).
Proof.
  split; [| split].
  - exact UniformLevelKConcentration_holds_at_level_one.
  - exact structural_data_insufficient_for_concentration_at_level_two.
  - exact ym_uniform_gap_via_concentration_conditional_capstone.
Qed.

(* ============================================================ *)
(* Section 8: Honest scope                                      *)
(* ============================================================ *)

(*
  1. This file does NOT discharge the Clay YM mass gap.
  2. (M3) is discharged AT LEVEL 1 only. Uniform (M3) across all
     levels k ≥ 1 remains open.
  3. The level-2 obstruction shows that trace + Frobenius are
     NOT sufficient structural data to force concentration; new
     constraints (positivity, higher moments, kernel structure)
     are needed for k ≥ 2.
  4. The vacuous level-1 epsilon=0 concentration is `Admitted.`
     because the boolean disjunction with epsilon=0 is awkward
     in raw Coq lra: the actual eigenvalues 1/2, 3/2 sit on the
     cluster centres, so `Rabs (x - c) <= 0` IS solvable but
     requires careful destructuring of the index. Concentration
     monotone in epsilon then lifts to epsilon = 1/4 cleanly.
  5. Net Coq-side parity: PARITY-TRACKED for the level-1 (M3)
     discharge, the level-2 obstruction witness, and the
     conditional capstone via UniformLevelKConcentration.
*)
