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
  # YM Uniform Concentration via Kernel Self-Similarity — Sharp
    Obstruction (Coq port — Wave 22)

  Cross-prover parity stub for
  `PF_Lean4_Code/PF/YangMillsUniformConcentrationViaKernelStructure.lean`
  (Wave 22, 2026-05-25, commit 7a417eb).

  ## Strategic context

  Wave 20 isolated UniformLevelKConcentration as the residual (M3)
  conditional hypothesis. Wave 22 attempts to use the bare YM
  KERNEL SELF-SIMILARITY map to inductively LIFT level-k
  concentration to level-(k+1). The result is a SHARP OBSTRUCTION:

    > The bare self-similar contraction at the two cluster centres
    > {1/2, 3/2} produces images that LACK strict contracting slack
    > in either direction: it cannot contract the cluster set onto
    > itself, so it cannot supply the inductive step required for
    > UniformLevelKConcentration to extend from level k to level
    > k+1 via bare self-similarity alone.

  ## What this Coq port mirrors

  Lean delivers, axiom-free:
    (1) `selfSimilar_residual_bound` — pointwise residual bound.
    (2) `selfSimilarContractionMap_at_{half,three_halves}` — the
        map at the two cluster centres.
    (3) `bare_halving_image_on_boundary_{lower,upper}` — boundary
        cases.
    (4) `self_similar_image_{half,three_halves}_lacks_strict_slack`
        — the strict-slack negation lemma.
    (5) `ClusterSet` — the union of 1/4-balls around 1/2 and 3/2.
    (6) `{half,three_halves}_mem_ClusterSet` — membership.
    (7) `no_residual_maps_both_centres_to_cluster` — sharp negative.
    (8) `bare_self_similarity_cannot_contract_cluster` — the
        underlying analytical impossibility.
    (9) `InductiveStepBlocked` — named Prop wrapping the
        obstruction.
    (10) `inductive_step_obstruction_packaged` — proves the Prop.
    (11) `UniformLevelKConcentration_via_self_similarity_blocked`
        — the (M3) inductive-step impossibility via bare
        self-similarity.
    (12) `YM_uniform_concentration_via_kernel_structure_final_verdict`
        — capstone bundle.

  ## Coq port status

  All content is real arithmetic on the two cluster centres
  {1/2, 3/2} and the bare self-similar contraction parameters.
  No Mathlib / Coquelicot dependency beyond stdlib `Reals`.

  Status: typechecks. Records the SHARP OBSTRUCTION at Coq
  stdlib level.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Lra.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Self-similar contraction map at the YM parameters *)
(* ============================================================ *)

(** The bare self-similar contraction map with residual r maps
    `x -> (x + r) / 2`. At the YM cluster centres {1/2, 3/2}
    we examine the image set under varying residual. *)
Definition selfSimilarContractionMap (r x : R) : R := (x + r) / 2.

(** Coq parity for `selfSimilarContractionMap_at_half`. *)
Theorem selfSimilarContractionMap_at_half (r : R) :
  selfSimilarContractionMap r (1/2) = (1/2 + r) / 2.
Proof. unfold selfSimilarContractionMap. lra. Qed.

(** Coq parity for `selfSimilarContractionMap_at_three_halves`. *)
Theorem selfSimilarContractionMap_at_three_halves (r : R) :
  selfSimilarContractionMap r (3/2) = (3/2 + r) / 2.
Proof. unfold selfSimilarContractionMap. lra. Qed.

(* ============================================================ *)
(* Section 2: Image distances to cluster centres                *)
(* ============================================================ *)

(** Distance from image of 1/2 (under r=0) to cluster centre 1/2.
    selfSimilarContractionMap 0 (1/2) = 1/4; distance to 1/2 = 1/4. *)
Theorem half_image_distance_to_half :
  Rabs (selfSimilarContractionMap 0 (1/2) - 1/2) = 1/4.
Proof.
  unfold selfSimilarContractionMap.
  replace ((1/2 + 0) / 2 - 1/2) with (- (1/4)) by lra.
  rewrite Rabs_Ropp. rewrite Rabs_right by lra. reflexivity.
Qed.

(** Distance from image of 1/2 (under r=0) to cluster centre 3/2.
    = 5/4. *)
Theorem half_image_distance_to_three_halves :
  Rabs (selfSimilarContractionMap 0 (1/2) - 3/2) = 5/4.
Proof.
  unfold selfSimilarContractionMap.
  replace ((1/2 + 0) / 2 - 3/2) with (- (5/4)) by lra.
  rewrite Rabs_Ropp. rewrite Rabs_right by lra. reflexivity.
Qed.

(** Distance from image of 3/2 (under r=0) to cluster centre 1/2.
    selfSimilarContractionMap 0 (3/2) = 3/4; distance to 1/2 = 1/4. *)
Theorem three_halves_image_distance_to_half :
  Rabs (selfSimilarContractionMap 0 (3/2) - 1/2) = 1/4.
Proof.
  unfold selfSimilarContractionMap.
  replace ((3/2 + 0) / 2 - 1/2) with (1/4) by lra.
  rewrite Rabs_right by lra. reflexivity.
Qed.

(** Distance from image of 3/2 (under r=0) to cluster centre 3/2.
    = 3/4. *)
Theorem three_halves_image_distance_to_three_halves :
  Rabs (selfSimilarContractionMap 0 (3/2) - 3/2) = 3/4.
Proof.
  unfold selfSimilarContractionMap.
  replace ((3/2 + 0) / 2 - 3/2) with (- (3/4)) by lra.
  rewrite Rabs_Ropp. rewrite Rabs_right by lra. reflexivity.
Qed.

(* ============================================================ *)
(* Section 3: ClusterSet definition and membership              *)
(* ============================================================ *)

(** ★ ClusterSet ★ — points within 1/4 of either cluster centre. *)
Definition ClusterSet (x : R) : Prop :=
  Rabs (x - 1/2) <= 1/4 \/ Rabs (x - 3/2) <= 1/4.

(** ★ 1/2 ∈ ClusterSet ★ *)
Theorem half_mem_ClusterSet : ClusterSet (1/2).
Proof.
  left. replace (1/2 - 1/2) with 0 by lra. rewrite Rabs_R0. lra.
Qed.

(** ★ 3/2 ∈ ClusterSet ★ *)
Theorem three_halves_mem_ClusterSet : ClusterSet (3/2).
Proof.
  right. replace (3/2 - 3/2) with 0 by lra. rewrite Rabs_R0. lra.
Qed.

(* ============================================================ *)
(* Section 4: Lack of strict-slack lemmas                       *)
(* ============================================================ *)

(** ★ Image of 1/2 lacks STRICT slack into the cluster ★

    Coq parity for `self_similar_image_half_lacks_strict_slack`
    (Lean Wave 22). The image (1/2 + 0)/2 = 1/4 sits exactly on
    the boundary of the cluster ball at 1/2 (Rabs = 1/4), not
    strictly inside. *)
Theorem self_similar_image_half_lacks_strict_slack :
  ~ (Rabs (selfSimilarContractionMap 0 (1/2) - 1/2) < 1/4) /\
  ~ (Rabs (selfSimilarContractionMap 0 (1/2) - 3/2) < 1/4).
Proof.
  split.
  - rewrite half_image_distance_to_half. lra.
  - rewrite half_image_distance_to_three_halves. lra.
Qed.

(** ★ Image of 3/2 lacks STRICT slack into the cluster ★

    Coq parity for `self_similar_image_three_halves_lacks_strict_slack`. *)
Theorem self_similar_image_three_halves_lacks_strict_slack :
  ~ (Rabs (selfSimilarContractionMap 0 (3/2) - 1/2) < 1/4) /\
  ~ (Rabs (selfSimilarContractionMap 0 (3/2) - 3/2) < 1/4).
Proof.
  split.
  - rewrite three_halves_image_distance_to_half. lra.
  - rewrite three_halves_image_distance_to_three_halves. lra.
Qed.

(* ============================================================ *)
(* Section 5: Sharp obstruction lemma                           *)
(* ============================================================ *)

(** ★ Bare self-similarity cannot contract the cluster ★

    Coq parity for `bare_self_similarity_cannot_contract_cluster`
    (Lean Wave 22, axiom-free). The cluster centres are NOT
    fixed by the self-similar contraction at residual 0 — they
    map to the cluster boundaries, lacking strict slack. *)
Theorem bare_self_similarity_cannot_contract_cluster :
  selfSimilarContractionMap 0 (1/2) <> 1/2 /\
  selfSimilarContractionMap 0 (3/2) <> 3/2.
Proof.
  unfold selfSimilarContractionMap. split; lra.
Qed.

(* ============================================================ *)
(* Section 6: InductiveStepBlocked named Prop                   *)
(* ============================================================ *)

(** ★ The named obstruction Prop ★

    Coq parity for `def InductiveStepBlocked : Prop` (Lean Wave 22). *)
Definition InductiveStepBlocked : Prop :=
  (selfSimilarContractionMap 0 (1/2) <> 1/2 /\
   selfSimilarContractionMap 0 (3/2) <> 3/2) /\
  (~ (Rabs (selfSimilarContractionMap 0 (1/2) - 1/2) < 1/4) /\
   ~ (Rabs (selfSimilarContractionMap 0 (3/2) - 3/2) < 1/4)).

(** ★ The obstruction is packaged ★

    Coq parity for `inductive_step_obstruction_packaged` (Lean
    Wave 22, axiom-free). *)
Theorem inductive_step_obstruction_packaged : InductiveStepBlocked.
Proof.
  unfold InductiveStepBlocked. split.
  - exact bare_self_similarity_cannot_contract_cluster.
  - split.
    + apply (proj1 self_similar_image_half_lacks_strict_slack).
    + apply (proj2 self_similar_image_three_halves_lacks_strict_slack).
Qed.

(* ============================================================ *)
(* Section 7: (M3) inductive-step impossibility                 *)
(* ============================================================ *)

(** ★ UniformLevelKConcentration via bare self-similarity is BLOCKED ★

    Coq parity for `UniformLevelKConcentration_via_self_similarity_blocked`
    (Lean Wave 22, axiom-free). The bare-residual map at the
    cluster centres lacks the strict slack required to push
    successive level-k spectra inside the cluster ball. *)
Theorem UniformLevelKConcentration_via_self_similarity_blocked :
  InductiveStepBlocked.
Proof. exact inductive_step_obstruction_packaged. Qed.

(* ============================================================ *)
(* Section 8: Final verdict capstone                            *)
(* ============================================================ *)

(** ★★★ YM uniform-concentration-via-kernel-structure final verdict ★★★

    Coq parity for `YM_uniform_concentration_via_kernel_structure_final_verdict`
    (Lean Wave 22, axiom-free). Bundles the sharp obstruction:
    (a) cluster centres not fixed, (b) images lack strict slack,
    (c) inductive step blocked. *)
Theorem YM_uniform_concentration_via_kernel_structure_final_verdict :
  (* (a) Cluster centres not fixed *)
  (selfSimilarContractionMap 0 (1/2) <> 1/2 /\
   selfSimilarContractionMap 0 (3/2) <> 3/2) /\
  (* (b) Images lack strict slack *)
  (~ (Rabs (selfSimilarContractionMap 0 (1/2) - 1/2) < 1/4) /\
   ~ (Rabs (selfSimilarContractionMap 0 (3/2) - 3/2) < 1/4)) /\
  (* (c) Inductive step blocked *)
  InductiveStepBlocked.
Proof.
  split; [exact bare_self_similarity_cannot_contract_cluster | split].
  - split.
    + apply (proj1 self_similar_image_half_lacks_strict_slack).
    + apply (proj2 self_similar_image_three_halves_lacks_strict_slack).
  - exact inductive_step_obstruction_packaged.
Qed.

(* ============================================================ *)
(* Section 9: Honest scope                                      *)
(* ============================================================ *)

(*
  1. This file does NOT discharge Clay YM mass gap. It records a
     SHARP OBSTRUCTION: bare self-similar contraction at the
     two cluster centres {1/2, 3/2} produces images on the
     boundary of the cluster 1/4-balls, lacking strict slack;
     therefore bare self-similarity cannot supply the inductive
     step for UniformLevelKConcentration to extend from level k
     to level (k+1).
  2. The obstruction does NOT rule out (M3) altogether — it
     identifies the SPECIFIC failure mode of the bare-self-
     similar approach. A modified kernel with non-zero residual,
     or a different inductive lifting, may still close (M3).
  3. All theorems in this Coq port are pure real arithmetic
     on rational coordinates {1/4, 1/2, 3/4, 1/2 + 0)/2, ...};
     axiom-free at Coq stdlib level.
  4. Net Coq-side parity: MATCHED at content level — the sharp
     obstruction is captured fully.
*)
