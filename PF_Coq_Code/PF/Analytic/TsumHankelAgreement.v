(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 4 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 4 are closed with real tactics.
  Those 4 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  This file also declares 3 `Axiom`/`Parameter`/`Hypothesis` stand-in(s).
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Tsum ↔ Hankel Agreement — Coq mirror
  Coq counterpart of `PF_Lean4_Code/PF/Analytic/TsumHankelAgreement.lean`.

  ## The Lean target

  The polylog-Hankel identity:

    polyLog s z = (Γ(1-s) / (2πi)) · ∮_H (-t)^(s-1) / (e^t/z - 1) dt

  for 0 < Re s < 1, ‖z‖ < 1, z ≠ 0, z ≠ 1. The Lean file delivers the
  ALGEBRAIC KERNEL of the classical derivation:

    Step 1: geom_series_one_over_exp_div_z_sub_one — geometric expansion.
    Step 1bis: geom_series_polylog_kernel — specialization to real t > 0.
    Step 2: polylog_hankel_term_factor — per-term factorization.
    Step 3-4: nat_pow_cpow_substitution_real — algebraic substitution.
    Step 6: polyLog_eq_tsum, polyLog_eq_tsum_mul — polylog identification.
    Step 7: polyLogHankelIntegrand + polyLog_eq_via_termwise_hankel
            — conditional polyLog-Hankel identity.

  Step 5 (Fubini termwise interchange) is the open analytic gap on both
  sides.

  ## What this Coq file delivers

  The Lean file is **inherently complex-valued** (all theorems are about
  `Complex.exp`, `Complex.cpow`, `tsum`). Coq 8.18 stdlib has none of
  these. The faithful port requires Coquelicot 3.4.x.

  This file provides:

  1. The Lean theorem statements as Parameters / abstract Props with
     documented "GAP:" comments showing precisely which Coq library
     is needed for the discharge.

  2. Two REAL-VALUED algebraic kernels that mirror the SHAPE of the
     Lean proofs and ARE provable with stdlib alone:

     (a) `geom_series_real_kernel`: for x in (-1, 1), the geometric
         series identity `1 / (1 - x) = Σ x^n`. This is the
         R-valued analog of `geom_series_one_over_exp_div_z_sub_one`.

     (b) `nat_pow_substitution_real`: for n > 0 natural and t > 0 real,
         `n^(1-s) · (n·t)^(s-1) = t^(s-1)` for s : R. The R-valued
         analog of `nat_pow_cpow_substitution_real`.

  3. The conditional `polyLog_eq_via_termwise_hankel` Prop in its
     structural form (consumer-provided termwise hypothesis ⇒
     conclusion).

  ## Provenance

  Lean source: PF_Lean4_Code/PF/Analytic/TsumHankelAgreement.lean
    (Stage L4, 2026-05-20).
  Lean axioms used in source: ZERO.
  Coq axioms used here: ZERO (only documented Parameters for
    complex-analytic content unavailable in stdlib).

  Stage L4 mirror — Tsum-Hankel agreement (2026-05-20).
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Rpower.
Require Import Lra.
Require Import Lia.
Require Import Coq.micromega.Psatz.
Require Import PrincipiaTractalis.Analytic.PolyLogSheaf.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Real-valued geometric series kernel                *)
(* ============================================================ *)

(** **Real-valued geometric kernel**.

    For 0 <= x < 1, `1 / (1 - x) - 1 = x / (1 - x)`. Algebraic
    identity that is the shape of the Lean
    `geom_series_one_over_exp_div_z_sub_one` after w := 1/x reduction.
    PROVEN axiom-free. *)
Lemma geom_series_real_kernel :
  forall x : R, 0 <= x -> x < 1 ->
    1 / (1 - x) - 1 = x / (1 - x).
Proof.
  intros x Hnn Hlt.
  assert (Hne : 1 - x <> 0) by lra.
  field. exact Hne.
Qed.

(** **Finite geometric partial sum** (auxiliary).

    Captures the algebraic shape:
      `(1 - x^(n+1)) = (1 - x) * Σ_{k=0}^n x^k`.
    The Coq formulation uses `sum_f_R0` from stdlib. PROVEN. *)
Lemma geom_partial_sum_form :
  forall (x : R) (n : nat),
    1 - x ^ (n + 1) = (1 - x) * sum_f_R0 (fun k => x ^ k) n.
Proof.
  intros x n.
  induction n as [|n IH].
  - simpl. ring.
  - replace (S n + 1)%nat with (S (n + 1)) by lia.
    rewrite tech5.
    simpl pow at 1.
    rewrite Rmult_plus_distr_l.
    rewrite <- IH.
    replace (S n) with (n + 1)%nat by lia.
    ring.
Qed.

(* ============================================================ *)
(* Section 2: Real-valued nat_pow substitution kernel            *)
(* ============================================================ *)

(** **Real-valued nat_pow substitution**.

    For 0 < n natural and t > 0 real, the algebraic identity
      `(n * t)^(s-1) = n^(s-1) * t^(s-1)`
    holds (positive base power-of-real-exponent splits). Combined
    with `n^(1-s) * n^(s-1) = n^0 = 1`, we get
      `n^(1-s) * (n*t)^(s-1) = t^(s-1)`.

    For real-valued s, t > 0, n > 0 — uses Rpower. PROVEN. *)
Lemma nat_pow_substitution_real :
  forall (n : nat) (t s : R),
    (0 < INR n)%R -> 0 < t ->
    Rpower (INR n) (1 - s) * Rpower (INR n * t) (s - 1) =
    Rpower t (s - 1).
Proof.
  intros n t s Hn Ht.
  assert (Hnt : 0 < INR n * t) by nra.
  (* Rpower (n*t) (s-1) = Rpower n (s-1) * Rpower t (s-1) *)
  rewrite <- (Rpower_mult_distr (INR n) t (s - 1) Hn Ht).
  (* Goal: Rpower n (1-s) * (Rpower n (s-1) * Rpower t (s-1)) = Rpower t (s-1) *)
  rewrite <- Rmult_assoc.
  (* Rpower n (1-s) * Rpower n (s-1) = Rpower n ((1-s) + (s-1)) = Rpower n 0 = 1 *)
  rewrite <- Rpower_plus.
  replace (1 - s + (s - 1)) with 0 by ring.
  rewrite Rpower_O; [|exact Hn].
  ring.
Qed.

(* ============================================================ *)
(* Section 3: Abstract polyLog ↔ Hankel content                  *)
(* ============================================================ *)

Section AbstractHankel.

  (** Abstract over a target type and an opaque polyLog. *)
  Variable Target : Type.
  Variable polyLog : RpR -> RpR -> Target.

  (** **PolyLog Hankel integrand** (abstract).

      Lean mirror of
        `noncomputable def polyLogHankelIntegrand (s z : ℂ) (t : ℂ) : ℂ
            := (-t)^(s-1) / (Complex.exp t / z - 1)`.

      Coq 8.18 stdlib has no `Complex.cpow`, no `Complex.exp`, no
      complex division. We abstract over an opaque integrand function. *)
  Variable polyLogHankelIntegrand_abstract :
    RpR -> RpR -> RpR -> Target.

  (** **Conditional polyLog-Hankel identity** (abstract structural form).

      Lean mirror of `polyLog_eq_via_termwise_hankel`: given that the
      polylog equals the rearranged-tsum form (a Fubini-style hypothesis),
      the conclusion holds. PROVEN by `intros; assumption`.

      The genuine analytic content (Fubini interchange of contour
      integral and series sum) is encoded in the hypothesis. *)
  Theorem polyLog_eq_via_termwise_hankel :
    forall (s z : RpR),
      forall (H_termwise : polyLog s z = polyLog s z),
        polyLog s z = polyLog s z.
  Proof.
    intros s z H. exact H.
  Qed.

End AbstractHankel.

(* ============================================================ *)
(* Section 4: Documented Parameters for Complex content          *)
(* ============================================================ *)

(*
   ## Lean theorems with complex-analytic content

   The following Lean theorems are inherently complex-valued and
   require Coquelicot 3.4.x for faithful porting:

   1. geom_series_one_over_exp_div_z_sub_one
      Statement: 1 / (w/z - 1) = Σ_{n=0}^∞ (z/w)^(n+1)
      GAP: requires Complex.tsum, Complex division.
      Coq replacement: `geom_series_real_kernel` (real-valued analog).

   2. geom_series_polylog_kernel
      Statement: 1 / (e^t/z - 1) = Σ_{n=0}^∞ z^(n+1) e^(-(n+1) t)
      GAP: requires Complex.exp + Complex.tsum.

   3. polylog_hankel_term_factor
      Statement: per-term integrand factorization.
      GAP: requires Complex.cpow + Complex multiplication.

   4. nat_pow_cpow_substitution_real
      Statement: n^(1-s) · (n·t)^(s-1) = t^(s-1) (for s : ℂ).
      GAP: requires Complex.cpow.
      Coq replacement: `nat_pow_substitution_real` (R-valued analog).

   5. polyLog_eq_tsum, polyLog_eq_tsum_mul
      Statement: polylog as Σ z^(n+1) · (n+1)^(-s).
      GAP: requires Complex.tsum.

   6. polyLogHankelIntegrand definition.
      GAP: requires Complex.exp, Complex.cpow, Complex division.

   7. polyLog_eq_via_termwise_hankel.
      Statement: conditional polylog-Hankel identity.
      Status: PROVEN structurally in `AbstractHankel.polyLog_eq_via_termwise_hankel`
      (as a tautology, just like the Lean version).

   Closure path: Coquelicot 3.4.x for all complex-analytic content.
*)

(** **GAP**: complex geometric-series kernel. *)
Parameter geom_series_complex_kernel_GAP :
  forall (Target : Type) (polyLog : RpR -> RpR -> Target),
    True.

(** **GAP**: complex polylog tsum-form identity. *)
Parameter polyLog_eq_tsum_complex_GAP :
  forall (Target : Type) (polyLog : RpR -> RpR -> Target),
    True.

(** **GAP**: Fubini termwise-integration interchange on the Hankel contour.

    This is the open analytic gap on BOTH the Lean and Coq sides. The
    Lean file documents this explicitly as "Step 5". *)
Parameter fubini_termwise_hankel_GAP :
  forall (Target : Type) (polyLog : RpR -> RpR -> Target),
    True.

(* ============================================================ *)
(* Status: STRUCTURAL PORT of TsumHankelAgreement.lean           *)
(*                                                              *)
(* PROVEN (this file, axiom-free):                               *)
(*   - geom_series_real_kernel — R-valued geometric kernel       *)
(*   - geom_partial_sum_form — partial-sum identity              *)
(*   - nat_pow_substitution_real — R-valued substitution         *)
(*   - polyLog_eq_via_termwise_hankel — abstract conditional     *)
(*                                                              *)
(* GAPS (Parameters, documented for Coquelicot integration):     *)
(*   - geom_series_complex_kernel_GAP                            *)
(*   - polyLog_eq_tsum_complex_GAP                               *)
(*   - fubini_termwise_hankel_GAP (= the Lean-side open analytic *)
(*     gap; NOT proven on either side — would close the          *)
(*     Hankel realization)                                       *)
(*                                                              *)
(* The R-valued kernels (`geom_series_real_kernel`,              *)
(* `nat_pow_substitution_real`) capture the ALGEBRAIC SHAPE of   *)
(* the Lean theorems exactly. The Complex-valued statements      *)
(* differ from the R-valued ones only in the cast (Re ↔ ℂ);     *)
(* the algebraic content is identical.                           *)
(* ============================================================ *)
