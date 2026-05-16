(*
  # Interval Arithmetic with Ultra-Precision Bounds (Coq port)
  Coq counterpart of `PF_Lean4_Code/PF/IntervalArithmetic.lean`.

  High-precision numerical bounds for fundamental constants used in
  spectral gap calculations. Bounds are certified by external
  verification (mpmath / PARI / SageMath at 100-digit precision).

  Lean → Coq translation notes:
  * `Real.sqrt`        → `sqrt`   (from `Coq.Reals.R_sqrt`)
  * `Real.pi`          → `PI`     (from `Coq.Reals.Rtrigo1`)
  * `Real.mul_self_sqrt` → `sqrt_def` (`sqrt(x)² = x` for `0 ≤ x`)
  * `nlinarith` tactic   → `nra`  (nonlinear real arithmetic)
  * `noncomputable def`  → `Definition` (Reals are noncomputable in both)
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.
Require Import Coq.micromega.Psatz.

Open Scope R_scope.

(* ============================================================ *)
(* Definitions                                                  *)
(* ============================================================ *)

(** The golden ratio φ = (1 + √5) / 2. *)
Definition phi : R := (1 + sqrt 5) / 2.

(** Universal coupling constant π/10. *)
Definition pi_10 : R := PI / 10.

(* ============================================================ *)
(* Lemmas: nonnegativity and squares                            *)
(* ============================================================ *)

Lemma sqrt2_nonneg : 0 <= sqrt 2.
Proof. apply sqrt_pos. Qed.

Lemma sqrt2_sq : sqrt 2 * sqrt 2 = 2.
Proof. apply sqrt_def. lra. Qed.

Lemma sqrt5_nonneg : 0 <= sqrt 5.
Proof. apply sqrt_pos. Qed.

Lemma sqrt5_sq : sqrt 5 * sqrt 5 = 5.
Proof. apply sqrt_def. lra. Qed.

(* ============================================================ *)
(* √2 bounds at 8-digit precision                               *)
(* ============================================================ *)

(** √2 lower bound (8 decimal places). Mirrors `sqrt2_lower` in Lean. *)
Theorem sqrt2_lower : 1.41421356 <= sqrt 2.
Proof.
  pose proof sqrt2_sq as Hsq.
  pose proof sqrt2_nonneg as Hnn.
  nra.
Qed.

(** √2 upper bound (8 decimal places). *)
Theorem sqrt2_upper : sqrt 2 <= 1.41421357.
Proof.
  pose proof sqrt2_sq as Hsq.
  pose proof sqrt2_nonneg as Hnn.
  nra.
Qed.

(** √2 at 10-digit precision: 1.4142135623 ≤ √2 ≤ 1.4142135624. *)
Theorem sqrt2_in_interval_10digit :
  1.4142135623 <= sqrt 2 /\ sqrt 2 <= 1.4142135624.
Proof.
  pose proof sqrt2_sq as Hsq.
  pose proof sqrt2_nonneg as Hnn.
  split; nra.
Qed.

(* ============================================================ *)
(* √5 bounds                                                    *)
(* ============================================================ *)

(** √5 at 10-digit precision: 2.2360679774 ≤ √5 ≤ 2.2360679775. *)
Theorem sqrt5_in_interval_10digit :
  2.2360679774 <= sqrt 5 /\ sqrt 5 <= 2.2360679775.
Proof.
  pose proof sqrt5_sq as Hsq.
  pose proof sqrt5_nonneg as Hnn.
  split; nra.
Qed.

(* ============================================================ *)
(* φ bounds                                                     *)
(* ============================================================ *)

(** φ at 8-digit precision: 1.61803398 ≤ φ ≤ 1.61803399. *)
Theorem phi_lower : 1.61803398 <= phi.
Proof.
  unfold phi.
  pose proof sqrt5_sq as Hsq.
  pose proof sqrt5_nonneg as Hnn.
  nra.
Qed.

Theorem phi_upper : phi <= 1.61803399.
Proof.
  unfold phi.
  pose proof sqrt5_sq as Hsq.
  pose proof sqrt5_nonneg as Hnn.
  nra.
Qed.

(** φ at 10-digit precision: 1.6180339887 ≤ φ ≤ 1.6180339888. *)
Theorem phi_in_interval_10digit :
  1.6180339887 <= phi /\ phi <= 1.6180339888.
Proof.
  unfold phi.
  pose proof sqrt5_sq as Hsq.
  pose proof sqrt5_nonneg as Hnn.
  split; nra.
Qed.

(* ============================================================ *)
(* Positivity                                                   *)
(* ============================================================ *)

Theorem phi_pos : 0 < phi.
Proof.
  pose proof phi_lower. lra.
Qed.

Theorem pi_10_pos : 0 < pi_10.
Proof.
  unfold pi_10. pose proof PI_RGT_0. lra.
Qed.

(* ============================================================ *)
(* Key downstream inequality: φ + 1/4 > √2                      *)
(* ============================================================ *)

(** **`φ + 1/4 > √2`** — the foundational inequality establishing
    `α_NP > α_P` in the framework.

    Numerical: 1.86803... > 1.41421...

    Proof via lower bound `√5 > 2` (since 2² = 4 < 5):
    * `φ + 1/4 = (3 + 2√5)/4 > (3 + 2·2)/4 = 7/4 = 1.75`
    * `√2 < 1.415` (since 1.415² = 2.002225 > 2)
    * Therefore `φ + 1/4 > 1.75 > 1.415 > √2`. *)
Theorem phi_plus_quarter_gt_sqrt2 : sqrt 2 < phi + 1/4.
Proof.
  unfold phi.
  (* Step 1: √5 > 2 *)
  assert (Hsqrt5_gt_2 : 2 < sqrt 5).
  {
    rewrite <- (sqrt_square 2 ltac:(lra)).
    apply sqrt_lt_1_alt. split; lra.
  }
  (* Step 2: √2 < 1.415 (since 1.415² = 2.002225 > 2) *)
  assert (Hsqrt2_lt_1415 : sqrt 2 < 1.415).
  {
    rewrite <- (sqrt_square 1.415 ltac:(lra)).
    apply sqrt_lt_1_alt. split; [lra | nra].
  }
  (* Step 3: combine *)
  (* (1 + √5)/2 + 1/4 = (3 + 2√5)/4 > (3 + 2·2)/4 = 1.75 > 1.415 > √2 *)
  pose proof sqrt5_nonneg.
  lra.
Qed.

(** **`√2 < 1.415`** — conservative upper bound, useful downstream. *)
Theorem sqrt2_lt_1415 : sqrt 2 < 1.415.
Proof.
  rewrite <- (sqrt_square 1.415 ltac:(lra)).
  apply sqrt_lt_1_alt. split; [lra | nra].
Qed.

(** **`φ > 1.6`** — conservative lower bound. *)
Theorem phi_gt_16 : 1.6 < phi.
Proof.
  unfold phi.
  pose proof sqrt5_sq as Hsq.
  pose proof sqrt5_nonneg as Hnn.
  nra.
Qed.

(* ============================================================ *)
(* Documentation: remaining ports                               *)
(*                                                              *)
(* The Lean file continues with:                                *)
(*   * lambda_P_{lower,upper}_certified (π/(10·√2) bounds)      *)
(*   * lambda_NP_{lower,upper}_certified (π·(√5−1)/(30·√2))     *)
(*   * lambda_0_P_precise / lambda_0_NP_precise (10-digit)      *)
(*   * Real.pi_gt_d20 / Real.pi_lt_d20 (used for precision)     *)
(*   * Q_3_gt_Q_2 (radix economy ordering)                      *)
(*                                                              *)
(* These need Coq's high-precision π bounds (via               *)
(* `Coq.Reals.Rtrigo_def` or `Coquelicot`). To be ported in     *)
(* subsequent commits.                                          *)
(* ============================================================ *)
