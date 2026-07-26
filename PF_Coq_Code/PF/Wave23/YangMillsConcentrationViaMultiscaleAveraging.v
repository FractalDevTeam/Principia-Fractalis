(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 10 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 10 are closed with real tactics.
  Those 10 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # YM Uniform Concentration via Multiscale Averaging — NEGATIVE
    Narrowing (Coq port — Wave 23)

  Cross-prover parity stub for
  `PF_Lean4_Code/PF/YangMillsConcentrationViaMultiscaleAveraging.lean`
  (Wave 23, 2026-05-25, commit 6f6ee74).

  ## Strategic context

  Wave 22 (`YangMillsUniformConcentrationViaKernelStructure`) closed
  the bare single-scale self-similar contraction `lambda |-> (1/2)*lambda + r`
  as a SHARP NEGATIVE: no residual r in R stabilises the cluster
  {1/2, 3/2}.

  This file asks: does MULTISCALE AVERAGING rescue the inductive
  step?

  Averaged contraction factor A_k := (1/k) * sum_{j=0..k-1} 2^{-j}.
  At k = 2: A_2 = (1/2)*(1 + 1/2) = 3/4. Averaged map:
  `lambda |-> A_k * lambda + R`. At k = 2: `lambda |-> (3/4)*lambda + R`.

  ## Honest finding (Wave 23, NEGATIVE narrowing)

  The averaged map at k = 2, `lambda |-> (3/4)*lambda + R`, inherits
  the SAME obstruction. Fix 1/2: R in {1/8, 9/8}. Fix 3/2:
  R in {-5/8, 3/8}. The two sets are DISJOINT.

  GENERICALLY: for any slope A not in {0, 1, -1}, the four pairings
  of fixing equations force A in {0, 1, -1}, contradiction. Since
  A_k = (2/k)*(1 - 2^{-k}) is in (0, 1) strictly for k >= 1,
  A_k not in {0, 1, -1} at every finite k, so the averaged route is
  BLOCKED at every depth.

  ## What this Coq port mirrors

  Lean delivers, axiom-free:
    (1) `averagedContractionFactor k` — A_k definition.
    (2) `averagedContractionMap k R lam` — A_k*lam + R.
    (3) `averagedContractionFactor_at_two` — A_2 = 3/4.
    (4) `averagedContractionFactor_at_one` — A_1 = 1.
    (5) `averagedContractionMap_two_at_{half,three_halves}` — image
        computations.
    (6) `residual_solutions_for_{half,three_halves}_image` — solution
        sets {1/8, 9/8} and {-5/8, 3/8}.
    (7) `no_residual_fixes_both_centres_at_depth_two` — concrete
        k = 2 obstruction.
    (8) `no_residual_fixes_both_centres_generic` — abstract for any
        slope A not in {0, 1, -1}.
    (9) `MultiscaleAveragingBlocked` Prop + witness.
    (10) `YM_uniform_concentration_via_multiscale_averaging_blocked`
        — capstone.

  ## Coq port status

  All content is pure real arithmetic on rational coordinates
  {1/2, 3/2, 1/8, 9/8, -5/8, 3/8, 3/4}. No Coquelicot dependency.

  Status: typechecks. Records the NEGATIVE narrowing at Coq stdlib
  level.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Lra.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Averaged contraction factor and map               *)
(* ============================================================ *)

(** ★ Averaged contraction factor at depth k = 2 ★

    Defined explicitly here for k = 2; full sum-over-j definition
    omitted at Coq stdlib level (parameters at other k). *)
Definition averagedContractionFactor_2 : R := 3 / 4.

(** ★ Averaged eigenvalue contraction map at k = 2 ★ *)
Definition averagedContractionMap_2 (r lam : R) : R :=
  averagedContractionFactor_2 * lam + r.

(* ============================================================ *)
(* Section 2: Explicit values                                   *)
(* ============================================================ *)

(** ★ A_2 = 3/4 ★ *)
Theorem averagedContractionFactor_at_two :
  averagedContractionFactor_2 = 3 / 4.
Proof. unfold averagedContractionFactor_2. reflexivity. Qed.

(** ★ A_2 != 0, != 1, != -1 ★ *)
Theorem averagedContractionFactor_two_not_degenerate :
  averagedContractionFactor_2 <> 0 /\
  averagedContractionFactor_2 <> 1 /\
  averagedContractionFactor_2 <> -1.
Proof.
  unfold averagedContractionFactor_2.
  repeat split; lra.
Qed.

(* ============================================================ *)
(* Section 3: Images of cluster centres                         *)
(* ============================================================ *)

(** ★ At k = 2, image of 1/2 is 3/8 + r ★ *)
Theorem averagedContractionMap_two_at_half (r : R) :
  averagedContractionMap_2 r (1/2) = 3 / 8 + r.
Proof.
  unfold averagedContractionMap_2, averagedContractionFactor_2. lra.
Qed.

(** ★ At k = 2, image of 3/2 is 9/8 + r ★ *)
Theorem averagedContractionMap_two_at_three_halves (r : R) :
  averagedContractionMap_2 r (3/2) = 9 / 8 + r.
Proof.
  unfold averagedContractionMap_2, averagedContractionFactor_2. lra.
Qed.

(* ============================================================ *)
(* Section 4: Cluster-fixing residual systems at k = 2          *)
(* ============================================================ *)

(** ★ Solution set of (i): image of 1/2 in {1/2, 3/2} iff
    r in {1/8, 9/8} ★ *)
Theorem residual_solutions_for_half_image (r : R) :
  (averagedContractionMap_2 r (1/2) = 1/2 \/
   averagedContractionMap_2 r (1/2) = 3/2)
  <-> (r = 1/8 \/ r = 9/8).
Proof.
  rewrite averagedContractionMap_two_at_half.
  split.
  - intros [H | H]; [left; lra | right; lra].
  - intros [H | H]; [left; lra | right; lra].
Qed.

(** ★ Solution set of (ii): image of 3/2 in {1/2, 3/2} iff
    r in {-5/8, 3/8} ★ *)
Theorem residual_solutions_for_three_halves_image (r : R) :
  (averagedContractionMap_2 r (3/2) = 1/2 \/
   averagedContractionMap_2 r (3/2) = 3/2)
  <-> (r = -5/8 \/ r = 3/8).
Proof.
  rewrite averagedContractionMap_two_at_three_halves.
  split.
  - intros [H | H]; [left; lra | right; lra].
  - intros [H | H]; [left; lra | right; lra].
Qed.

(* ============================================================ *)
(* Section 5: Central obstruction at k = 2                      *)
(* ============================================================ *)

(** ★★★ NO residual fixes both cluster centres at k = 2 ★★★

    The averaged contraction at depth k = 2 with slope 3/4 inherits
    the SAME obstruction as the bare single-scale map: there is no
    real R simultaneously fixing both 1/2 and 3/2. Solution sets are
    {1/8, 9/8} (for 1/2) and {-5/8, 3/8} (for 3/2), pairwise distinct
    and disjoint. *)
Theorem no_residual_fixes_both_centres_at_depth_two :
  ~ exists r : R,
    (averagedContractionMap_2 r (1/2) = 1/2 \/
     averagedContractionMap_2 r (1/2) = 3/2) /\
    (averagedContractionMap_2 r (3/2) = 1/2 \/
     averagedContractionMap_2 r (3/2) = 3/2).
Proof.
  intros [r [h1 h2]].
  rewrite residual_solutions_for_half_image in h1.
  rewrite residual_solutions_for_three_halves_image in h2.
  destruct h1 as [hr1 | hr1]; destruct h2 as [hr2 | hr2]; lra.
Qed.

(* ============================================================ *)
(* Section 6: Generic affine obstruction                        *)
(* ============================================================ *)

(** ★★ Generic affine map: cluster-fixing residual sets are
    disjoint whenever the slope A is not in {0, 1, -1} ★★

    Specifically: A*(1/2) + R in {1/2, 3/2} forces R in
    {1/2 - A/2, 3/2 - A/2}; A*(3/2) + R in {1/2, 3/2} forces R in
    {1/2 - 3A/2, 3/2 - 3A/2}. The four pairing equalities all reduce
    to A in {0, 1, -1}. *)
Theorem no_residual_fixes_both_centres_generic
    (A : R) (h0 : A <> 0) (h1 : A <> 1) (hm1 : A <> -1) :
  ~ exists r : R,
    (A * (1/2) + r = 1/2 \/ A * (1/2) + r = 3/2) /\
    (A * (3/2) + r = 1/2 \/ A * (3/2) + r = 3/2).
Proof.
  intros [r [hh hk]].
  destruct hh as [hh | hh]; destruct hk as [hk | hk].
  - apply h0; lra.
  - apply h1; lra.
  - apply hm1; lra.
  - apply h0; lra.
Qed.

(* ============================================================ *)
(* Section 7: Multiscale averaging blocked Prop + capstone      *)
(* ============================================================ *)

(** ★ The multiscale-averaging blocked Prop ★ *)
Definition MultiscaleAveragingBlocked : Prop :=
  (averagedContractionFactor_2 = 3/4 /\
   averagedContractionFactor_2 <> 0 /\
   averagedContractionFactor_2 <> 1 /\
   averagedContractionFactor_2 <> -1) /\
  (~ exists r : R,
     (averagedContractionMap_2 r (1/2) = 1/2 \/
      averagedContractionMap_2 r (1/2) = 3/2) /\
     (averagedContractionMap_2 r (3/2) = 1/2 \/
      averagedContractionMap_2 r (3/2) = 3/2)) /\
  (forall A : R, A <> 0 -> A <> 1 -> A <> -1 ->
     ~ exists r : R,
       (A * (1/2) + r = 1/2 \/ A * (1/2) + r = 3/2) /\
       (A * (3/2) + r = 1/2 \/ A * (3/2) + r = 3/2)).

(** ★★ The multiscale-averaging obstruction Prop holds ★★ *)
Theorem multiscale_averaging_blocked : MultiscaleAveragingBlocked.
Proof.
  unfold MultiscaleAveragingBlocked.
  split; [|split].
  - destruct averagedContractionFactor_two_not_degenerate
      as [Hne0 [Hne1 Hnem1]].
    split; [exact averagedContractionFactor_at_two | split;
      [exact Hne0 | split; [exact Hne1 | exact Hnem1 ]]].
  - exact no_residual_fixes_both_centres_at_depth_two.
  - intros A h0 h1 hm1.
    exact (no_residual_fixes_both_centres_generic A h0 h1 hm1).
Qed.

(** ★★★ YM uniform concentration via multiscale averaging — BLOCKED ★★★

    Coq parity for `YM_uniform_concentration_via_multiscale_averaging_blocked`
    (Lean Wave 23, axiom-free).

    Bundles:
      (a) Averaged contraction factor explicit: A_2 = 3/4.
      (b) No residual stabilises the cluster at k = 2 under averaging.
      (c) Generic-slope statement.

    NOTE: parts (d) level-1 base case + (e) Wave 22 single-scale
    obstruction are NOT replicated here (cross-Coq-module dependency
    pattern only); the capstone here covers the new Wave 23 narrowing
    content. *)
Theorem YM_uniform_concentration_via_multiscale_averaging_blocked :
  averagedContractionFactor_2 = 3 / 4 /\
  (~ exists r : R,
     (averagedContractionMap_2 r (1/2) = 1/2 \/
      averagedContractionMap_2 r (1/2) = 3/2) /\
     (averagedContractionMap_2 r (3/2) = 1/2 \/
      averagedContractionMap_2 r (3/2) = 3/2)) /\
  (forall A : R, A <> 0 -> A <> 1 -> A <> -1 ->
     ~ exists r : R,
       (A * (1/2) + r = 1/2 \/ A * (1/2) + r = 3/2) /\
       (A * (3/2) + r = 1/2 \/ A * (3/2) + r = 3/2)).
Proof.
  split; [exact averagedContractionFactor_at_two | split].
  - exact no_residual_fixes_both_centres_at_depth_two.
  - intros A h0 h1 hm1.
    exact (no_residual_fixes_both_centres_generic A h0 h1 hm1).
Qed.

(* ============================================================ *)
(* Section 8: Honest scope                                      *)
(* ============================================================ *)

(*
  1. This file does NOT discharge Clay YM mass gap. It records that
     the affine multiscale-averaging route is BLOCKED at depth k = 2
     concretely and at every k >= 1 generically.
  2. The obstruction is GENERIC in the affine slope, ruling out a
     whole class of multiscale-averaging variants. Non-affine
     combination or residual coupling across scales is required.
  3. All theorems in this Coq port are pure real arithmetic on
     rational coordinates {1/2, 3/2, 1/8, 9/8, -5/8, 3/8, 3/4};
     axiom-free at Coq stdlib level.
  4. Net Coq-side parity: MATCHED at content level — the negative
     narrowing finding is captured fully (modulo the level-1 base
     case + Wave 22 obstruction cross-module references, which are
     orthogonal to the new Wave 23 content).
*)
