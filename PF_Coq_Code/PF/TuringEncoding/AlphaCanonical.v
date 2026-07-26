(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 6 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 6 are closed with real tactics.
  Those 6 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Canonical α Values - Direct Algebraic Identities (Coq port)
  Coq counterpart of `PF_Lean4_Code/PF/TuringEncoding/AlphaCanonical.lean`.

  Provides axiom-free proofs of the algebraic identities for the canonical
  α values:
    α_P  = √2          satisfies   α² = 2
    α_NP = φ + 1/4     satisfies   16·α² − 24·α − 11 = 0

  Port notes:
  * Lean's `Real.sq_sqrt` → Coq's `sqrt_def` (combined with manual squaring)
  * Lean's `nlinarith` → Coq's `nra`
  * Uses `phi`, `sqrt5_sq`, `sqrt5_nonneg` from IntervalArithmetic.v
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.
Require Import Coq.micromega.Psatz.
Require Import PrincipiaTractalis.IntervalArithmetic.

Open Scope R_scope.

(* ============================================================ *)
(* Identity 1: (√2)² = 2                                         *)
(* ============================================================ *)

(** The P-class algebraic identity, axiom-free. *)
Theorem alpha_P_sq : (sqrt 2) ^ 2 = 2.
Proof.
  unfold pow. rewrite Rmult_1_r.
  apply sqrt2_sq.
Qed.

(* ============================================================ *)
(* Identity 2: φ² = φ + 1                                        *)
(* ============================================================ *)

(** The golden ratio's defining quadratic. *)
Theorem phi_sq_eq : phi ^ 2 = phi + 1.
Proof.
  unfold phi.
  unfold pow. rewrite Rmult_1_r.
  pose proof sqrt5_sq as Hsq.
  pose proof sqrt5_nonneg as Hnn.
  (* (1 + √5)/2 * ((1 + √5)/2) = (1 + √5)/2 + 1
     Expand LHS: (1 + 2·√5 + (√5)²)/4 = (1 + 2·√5 + 5)/4 = (6 + 2·√5)/4
     RHS: (1 + √5)/2 + 1 = (1 + √5 + 2)/2 = (3 + √5)/2 = (6 + 2·√5)/4  ✓ *)
  nra.
Qed.

(* ============================================================ *)
(* Identity 3: 16·(φ + 1/4)² − 24·(φ + 1/4) − 11 = 0              *)
(* ============================================================ *)

(** The NP-class quadratic, axiom-free.

    Derivation: expand 16·(φ + 1/4)² = 16φ² + 8φ + 1. Using
    φ² = φ + 1, this is 16(φ + 1) + 8φ + 1 = 24φ + 17.
    And 24·(φ + 1/4) = 24φ + 6. So
    16α² − 24α − 11 = (24φ + 17) − (24φ + 6) − 11 = 0. *)
Theorem alpha_NP_quadratic :
    16 * (phi + 1/4) ^ 2 - 24 * (phi + 1/4) - 11 = 0.
Proof.
  pose proof phi_sq_eq as Hsq.
  unfold pow in *. rewrite Rmult_1_r in *.
  nra.
Qed.

(* ============================================================ *)
(* Positivity facts                                              *)
(* ============================================================ *)

(** sqrt 2 > 0 — for identifying √2 as the unique positive root. *)
Theorem alpha_P_pos : 0 < sqrt 2.
Proof.
  apply sqrt_lt_R0. lra.
Qed.

(** φ + 1/4 > 0 — for identifying φ + 1/4 as the positive root. *)
Theorem alpha_NP_pos : 0 < phi + 1/4.
Proof.
  pose proof phi_in_interval_10digit as [Hlo _].
  lra.
Qed.

(* ============================================================ *)
(* Canonical algebraic pair (axiom-free analog of the axiom)     *)
(* ============================================================ *)

(** The pair (√2, φ + 1/4) jointly satisfies the algebraic system,
    AS A DIRECT FACT, not as an axiom about an opaque function. *)
Theorem canonical_alpha_algebraic_pair :
    ((sqrt 2) ^ 2 = 2 /\ 0 < sqrt 2) /\
    (16 * (phi + 1/4) ^ 2 - 24 * (phi + 1/4) - 11 = 0 /\ 0 < phi + 1/4).
Proof.
  split; split.
  - exact alpha_P_sq.
  - exact alpha_P_pos.
  - exact alpha_NP_quadratic.
  - exact alpha_NP_pos.
Qed.
