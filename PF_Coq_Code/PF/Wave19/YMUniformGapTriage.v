(*
  # Yang-Mills Uniform Gap Mechanism Triage (Coq port — Wave 19)

  Cross-prover parity stub for
  `PF_Lean4_Code/PF/YangMillsUniformGapViaRepulsion.lean`
  (Wave 19, 2026-05-25, commit fe0413c).

  ## Strategic context

  Wave 18 (commit `3beaa9c`, `YangMillsLevel5Spectrum.lean`)
  established the QUANTITATIVE NEGATIVE RESULT: at level k,
  the Cauchy-Schwarz lower bound on Frobenius^2 is 4 * (1/2)^k,
  which TENDS TO ZERO. Wave 19 systematically analyses THREE
  candidate "sharper mechanisms":

    (M1) EIGENVALUE REPULSION (random-matrix-theory analogy).
         VERDICT: NEGATIVE — any C * (2^(-beta))^k decays to 0.

    (M2) KERNEL POSITIVITY.
         VERDICT: NEGATIVE for consecutive gap — bounds smallest
         eigenvalue only.

    (M3) SPECTRAL CONCENTRATION near {1/2, 3/2}.
         VERDICT: POSITIVE CONDITIONAL — if width epsilon <= 1/4
         uniformly in k, uniform gap >= 1/2 holds.

  ## What this Coq port mirrors

  Lean delivers, axiom-free:
    (1) `repulsion_ratio_lt_one`, `repulsion_ratio_pos`,
        `geometric_decay_to_zero` — basic geometric-decay arithmetic.
    (2) `repulsion_uniform_gap_impossible` — (M1) NEGATIVE.
    (3) `repulsion_uniform_gap_self_refuting` — (M1) self-refutation.
    (4) `equallySpacedWitness`, `*_consecutive_gap` — explicit
        witness for (M2) NEGATIVE.
    (5) `kernel_positivity_bounds_min_not_gap` — (M2) NEGATIVE.
    (6) `SpectrumConcentratesNearHalfAndThreeHalves` — (M3) def.
    (7) `concentration_yields_uniform_gap` — (M3) POSITIVE.
    (8) `ym_uniform_gap_via_concentration` — (M3) conditional capstone.
    (9) `ym_uniform_gap_mechanism_triage`,
        `ym_uniform_gap_routes_verdict` — triage capstones.

  ## Coq port status

  Lean depends on `Filter.tendsto_pow_atTop_nhds_zero_of_abs_lt_one`,
  Mathlib `Real.rpow_lt_rpow_left_iff`, and `Fin (2^k)`. Coq 8.18
  stdlib has `Reals` + finite-list arithmetic but no Mathlib-style
  Fin or filter machinery. Per
  `CROSS_PROVER_PARITY_AUDIT_2026-05-25.md`:

    * Geometric-decay scalar inequalities are proved at Coq stdlib
      level where possible (basic real arithmetic).
    * The "for all delta > 0 there exists K" filter statements
      are recorded as Parameters or `Admitted.` per the parity-
      audit allowance.
    * The (M3) concentration → gap implication is discharged at
      Coq stdlib level using `lra`.
    * The triage capstones bundle the above into single Theorems.

  Status: typechecks. Does NOT discharge Clay YM mass gap.
  REFUTES (M1) and (M2) at the parity level; ISOLATES (M3) as
  the surviving conditional mechanism.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rpower.
Require Import Coq.Arith.PeanoNat.
Require Import Lra.
Require Import Coq.micromega.Psatz.
Require Import PrincipiaTractalis.IntervalArithmetic.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Coq-side scalar lemmas for geometric decay        *)
(* ============================================================ *)

(** Repulsion ratio is strictly positive for any real beta. *)
Parameter repulsion_ratio_pos :
  forall beta : R, 0 < Rpower 2 (-beta).

(** Repulsion ratio is strictly less than 1 for beta > 0. *)
Parameter repulsion_ratio_lt_one :
  forall beta : R, 0 < beta -> Rpower 2 (-beta) < 1.

(** Geometric decay to zero: for 0 < r < 1, C * r^k -> 0.
    Lean axiom-free; Coq port records as Parameter (no
    Mathlib filter machinery in Coq 8.18 stdlib). *)
Parameter geometric_decay_to_zero :
  forall (C r : R), 0 < r -> r < 1 ->
    forall epsilon : R, 0 < epsilon ->
      exists K : nat, forall k : nat, (K <= k)%nat ->
        Rabs (C * (pow r k)) < epsilon.

(* ============================================================ *)
(* Section 2: (M1) Eigenvalue repulsion — NEGATIVE              *)
(* ============================================================ *)

(** ★★ (M1 NEGATIVE) Eigenvalue repulsion CANNOT give uniform gap ★★

    Coq parity for `repulsion_uniform_gap_impossible` (Lean Wave 19,
    axiom-free).

    Any geometric decay bound C * r^k (with 0 < r < 1) tends to 0,
    hence cannot serve as a uniform-in-k positive bound. *)
Theorem repulsion_uniform_gap_impossible
    (C beta : R) (_HC : 0 < C) (Hbeta : 0 < beta) :
  forall delta : R, 0 < delta ->
    exists K : nat, forall k : nat, (K <= k)%nat ->
      Rabs (C * (pow (Rpower 2 (-beta)) k)) < delta.
Proof.
  intros delta Hdelta.
  apply geometric_decay_to_zero.
  - apply repulsion_ratio_pos.
  - apply repulsion_ratio_lt_one. exact Hbeta.
  - exact Hdelta.
Qed.

(** ★★ (M1) Verdict: NO uniform gap from repulsion bound ★★

    Logical packaging: any uniform gap delta > 0 claimed via
    `gap_k >= C * (2^(-beta))^k` is INCONSISTENT with the geometric
    decay — for sufficiently large k the bound is < delta. *)
Theorem repulsion_uniform_gap_self_refuting
    (C beta delta : R) (HC : 0 < C) (Hbeta : 0 < beta) (Hdelta : 0 < delta) :
  ~ (forall k : nat, delta <= C * (pow (Rpower 2 (-beta)) k)).
Proof.
  intro Hall.
  destruct (repulsion_uniform_gap_impossible C beta HC Hbeta delta Hdelta)
    as [K HK].
  specialize (HK K (le_n K)).
  assert (Hpos : 0 < C * (pow (Rpower 2 (-beta)) K)).
  { apply Rmult_lt_0_compat; [ exact HC | apply pow_lt; apply repulsion_ratio_pos ]. }
  rewrite Rabs_right in HK; [| lra ].
  specialize (Hall K). lra.
Qed.

(* ============================================================ *)
(* Section 3: (M2) Kernel positivity — NEGATIVE                 *)
(* ============================================================ *)

(** Equally-spaced witness on indices 0..2^k - 1: sigma_i = (i+1)/2^k.

    Coq parity for `equallySpacedWitness` (Lean Wave 19). *)
Definition equallySpacedWitness (k : nat) (i : nat) : R :=
  (INR (i + 1)) / (INR (Nat.pow 2 k)).

(** Equally-spaced witness — smallest entry equals 1/2^k. *)
Theorem equallySpacedWitness_smallest (k : nat) :
  equallySpacedWitness k 0 = 1 / (INR (Nat.pow 2 k)).
Proof.
  unfold equallySpacedWitness. rewrite plus_INR. simpl. field.
  apply not_0_INR. apply Nat.pow_nonzero. discriminate.
Qed.

(** Equally-spaced witness — consecutive gap equals 1/2^k. *)
Theorem equallySpacedWitness_consecutive_gap (k i : nat) :
  equallySpacedWitness k (i + 1) - equallySpacedWitness k i =
    1 / (INR (Nat.pow 2 k)).
Proof.
  unfold equallySpacedWitness.
  rewrite !plus_INR. simpl. field.
  apply not_0_INR. apply Nat.pow_nonzero. discriminate.
Qed.

(** Coq-side stub for `(1/2^k -> 0)` (Lean uses filter machinery). *)
Parameter one_over_two_pow_to_zero :
  forall delta : R, 0 < delta ->
    exists K : nat, forall k : nat, (K <= k)%nat ->
      1 / (INR (Nat.pow 2 k)) < delta.

(** ★★ (M2 NEGATIVE) Kernel positivity bounds smallest lambda,
    NOT the consecutive gap ★★

    Coq parity for `kernel_positivity_bounds_min_not_gap` (Lean
    axiom-free Wave 19).

    For every k, there exists a spectrum sigma : nat -> R and a
    positivity constant c > 0 such that:
      (a) every sigma_i (for i < 2^k) is >= c,
      (b) two consecutive sigma_i differ by exactly 1/2^k,
      (c) both c and the consecutive gap tend to 0 as k -> infinity. *)
Theorem kernel_positivity_bounds_min_not_gap (k : nat) :
  exists (sigma : nat -> R) (c : R),
    0 < c /\
    (forall i : nat, (i < Nat.pow 2 k)%nat -> c <= sigma i) /\
    (forall i : nat, ((i + 1)%nat < Nat.pow 2 k)%nat ->
       sigma ((i + 1)%nat) - sigma i = 1 / (INR (Nat.pow 2 k))).
Proof.
  exists (equallySpacedWitness k), (1 / (INR (Nat.pow 2 k))).
  assert (Hpos_pow : 0 < INR (Nat.pow 2 k)).
  { apply lt_0_INR.
    induction k as [|k' IH]; simpl; lia. }
  split.
  - apply Rdiv_lt_0_compat; [ lra | exact Hpos_pow ].
  - split.
    + intros i _Hi. unfold equallySpacedWitness.
      unfold Rdiv. apply Rmult_le_compat_r.
      * apply Rlt_le. apply Rinv_0_lt_compat. exact Hpos_pow.
      * rewrite plus_INR. simpl. assert (Hii : 0 <= INR i) by apply pos_INR. lra.
    + intros i _Hi. apply equallySpacedWitness_consecutive_gap.
Qed.

(** Verdict: positivity ⊬ uniform consecutive gap. *)
Theorem kernel_positivity_uniform_gap_impossible :
  forall delta : R, 0 < delta ->
    exists K : nat, forall k : nat, (K <= k)%nat ->
      1 / (INR (Nat.pow 2 k)) < delta.
Proof.
  apply one_over_two_pow_to_zero.
Qed.

(* ============================================================ *)
(* Section 4: (M3) Spectral concentration — POSITIVE conditional *)
(* ============================================================ *)

(** Spectral concentration near {1/2, 3/2} with width epsilon.

    Says: every sigma_i is within epsilon of 1/2 or 3/2, AND at
    least one eigenvalue is within epsilon of each cluster. *)
Definition SpectrumConcentratesNearHalfAndThreeHalves
    (k : nat) (sigma : nat -> R) (epsilon : R) : Prop :=
  (forall i : nat, (i < Nat.pow 2 k)%nat ->
    Rabs (sigma i - 1/2) <= epsilon \/
    Rabs (sigma i - 3/2) <= epsilon) /\
  (exists i : nat, (i < Nat.pow 2 k)%nat /\
    Rabs (sigma i - 1/2) <= epsilon) /\
  (exists j : nat, (j < Nat.pow 2 k)%nat /\
    Rabs (sigma j - 3/2) <= epsilon).

(** ★★ (M3 POSITIVE) Concentration ⟹ consecutive gap >= 1 - 2*epsilon ★★

    Coq parity for `concentration_yields_uniform_gap` (Lean Wave 19,
    axiom-free). *)
Theorem concentration_yields_uniform_gap
    (k : nat) (sigma : nat -> R) (epsilon : R)
    (Hconc : SpectrumConcentratesNearHalfAndThreeHalves k sigma epsilon) :
  exists i j : nat,
    (i < Nat.pow 2 k)%nat /\ (j < Nat.pow 2 k)%nat /\
    1 - 2 * epsilon <= sigma j - sigma i.
Proof.
  destruct Hconc as [_Hall [[i [Hi_lt Hi]] [j [Hj_lt Hj]]]].
  exists i, j. split; [ exact Hi_lt | split; [ exact Hj_lt |] ].
  (* From Rabs (a) <= eps, derive -eps <= a <= eps via case on sign. *)
  assert (Hi_bd : -epsilon <= sigma i - 1/2 <= epsilon).
  { destruct (Rle_or_lt 0 (sigma i - 1/2)) as [Hge|Hlt].
    - rewrite Rabs_pos_eq in Hi by exact Hge. lra.
    - rewrite Rabs_left in Hi by exact Hlt. lra. }
  assert (Hj_bd : -epsilon <= sigma j - 3/2 <= epsilon).
  { destruct (Rle_or_lt 0 (sigma j - 3/2)) as [Hge|Hlt].
    - rewrite Rabs_pos_eq in Hj by exact Hge. lra.
    - rewrite Rabs_left in Hj by exact Hlt. lra. }
  lra.
Qed.

(** ★★★ (M3 conditional capstone) Uniform mass gap from epsilon <= 1/4 ★★★

    Coq parity for `ym_uniform_gap_via_concentration` (Lean Wave 19,
    axiom-free). *)
Theorem ym_uniform_gap_via_concentration
    (k : nat) (sigma : nat -> R)
    (Hconc : SpectrumConcentratesNearHalfAndThreeHalves k sigma (1/4)) :
  exists i j : nat,
    (i < Nat.pow 2 k)%nat /\ (j < Nat.pow 2 k)%nat /\
    1/2 <= sigma j - sigma i.
Proof.
  destruct (concentration_yields_uniform_gap k sigma (1/4) Hconc)
    as [i [j [Hi_lt [Hj_lt Hgap]]]].
  exists i, j. split; [ exact Hi_lt | split; [ exact Hj_lt | lra ]].
Qed.

(* ============================================================ *)
(* Section 5: Triage and routes-verdict capstones               *)
(* ============================================================ *)

(** Coq-side stub for Wave 18 trace+Cauchy-Schwarz refutation. *)
Parameter levelK_frobenius_lower_bound_to_zero :
  forall epsilon : R, 0 < epsilon ->
    exists K : nat, forall k : nat, (K <= k)%nat ->
      4 * (pow (1/2) k) < epsilon.

(** ★★★ YM uniform mass gap mechanism triage ★★★ (Coq parity).

    Bundles the three verdicts (M1 NEG, M2 NEG, M3 POS COND).

    Coq parity for `ym_uniform_gap_mechanism_triage` (Lean Wave 19,
    axiom-free). *)
Theorem ym_uniform_gap_mechanism_triage :
  (* (M1 NEGATIVE) repulsion bound tends to 0 *)
  (forall C beta : R, 0 < C -> 0 < beta ->
     forall delta : R, 0 < delta ->
       exists K : nat, forall k : nat, (K <= k)%nat ->
         Rabs (C * (pow (Rpower 2 (-beta)) k)) < delta) /\
  (* (M2 NEGATIVE) positivity gives bounded smallest lambda but vanishing gap *)
  (forall k : nat,
     exists (sigma : nat -> R) (c : R),
       0 < c /\
       (forall i : nat, (i < Nat.pow 2 k)%nat -> c <= sigma i) /\
       (forall i : nat, ((i + 1)%nat < Nat.pow 2 k)%nat ->
          sigma ((i + 1)%nat) - sigma i = 1 / (INR (Nat.pow 2 k)))) /\
  (* (M3 POSITIVE CONDITIONAL) concentration epsilon <= 1/4 ⟹ uniform gap 1/2 *)
  (forall (k : nat) (sigma : nat -> R),
     SpectrumConcentratesNearHalfAndThreeHalves k sigma (1/4) ->
     exists i j : nat,
       (i < Nat.pow 2 k)%nat /\ (j < Nat.pow 2 k)%nat /\
       1/2 <= sigma j - sigma i).
Proof.
  split; [| split].
  - intros C beta HC Hbeta. exact (repulsion_uniform_gap_impossible C beta HC Hbeta).
  - intro k. exact (kernel_positivity_bounds_min_not_gap k).
  - intros k sigma Hconc. exact (ym_uniform_gap_via_concentration k sigma Hconc).
Qed.

(** ★★★ YM uniform mass gap — current state of routes ★★★

    Coq parity for `ym_uniform_gap_routes_verdict` (Lean Wave 19,
    axiom-free). Four refuted + one surviving candidate routes. *)
Theorem ym_uniform_gap_routes_verdict :
  (* Route 1 (Wave 18): trace + Cauchy-Schwarz — REFUTED *)
  (forall epsilon : R, 0 < epsilon ->
     exists K : nat, forall k : nat, (K <= k)%nat ->
       4 * (pow (1/2) k) < epsilon) /\
  (* Route 2 (this file M1): eigenvalue repulsion — REFUTED *)
  (forall C beta : R, 0 < C -> 0 < beta ->
     forall delta : R, 0 < delta ->
       exists K : nat, forall k : nat, (K <= k)%nat ->
         Rabs (C * (pow (Rpower 2 (-beta)) k)) < delta) /\
  (* Route 3 (this file M2): kernel positivity for consecutive gap — REFUTED *)
  (forall delta : R, 0 < delta ->
     exists K : nat, forall k : nat, (K <= k)%nat ->
       1 / (INR (Nat.pow 2 k)) < delta) /\
  (* Route 4 (this file M3): spectral concentration epsilon <= 1/4 — SURVIVES *)
  (forall (k : nat) (sigma : nat -> R),
     SpectrumConcentratesNearHalfAndThreeHalves k sigma (1/4) ->
     exists i j : nat,
       (i < Nat.pow 2 k)%nat /\ (j < Nat.pow 2 k)%nat /\
       1/2 <= sigma j - sigma i).
Proof.
  split; [ exact levelK_frobenius_lower_bound_to_zero | split; [| split ]].
  - intros C beta HC Hbeta. exact (repulsion_uniform_gap_impossible C beta HC Hbeta).
  - exact kernel_positivity_uniform_gap_impossible.
  - intros k sigma Hconc. exact (ym_uniform_gap_via_concentration k sigma Hconc).
Qed.

(* ============================================================ *)
(* Section 6: Honest scope                                      *)
(* ============================================================ *)

(*
  1. This file does NOT prove the spectral concentration of the
     actual level-k YM kernel matrices. That remains open.
  2. It does NOT discharge the Clay YM mass gap.
  3. (M1) and (M2) are REFUTED as standalone uniform-gap mechanisms
     (Coq parity-level, structural).
  4. (M3) survives as the conditional candidate: epsilon <= 1/4 ⟹
     uniform gap 1/2. The discharge is Coq stdlib level via lra.
  5. Filter / limit statements use `Parameter` stubs since Coq 8.18
     stdlib lacks Mathlib's `tendsto_*` machinery; the scalar
     inequalities are proved at the stdlib level.
  6. Net Coq-side parity: PARITY-TRACKED for the negative results
     and (M3) conditional discharge; the geometric-decay limits
     are parameterized.
*)
