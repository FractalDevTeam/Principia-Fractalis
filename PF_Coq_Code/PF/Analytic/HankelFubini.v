(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 5 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 5 are closed with real tactics.
  Those 5 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  This file also declares 18 `Axiom`/`Parameter`/`Hypothesis` stand-in(s).
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Hankel-Polylog Fubini Step (Coq port)
  Coq counterpart of `PF_Lean4_Code/PF/Analytic/HankelFubini.lean`.

  ## Scope: STRUCTURAL PORT of the Fubini-step deliverable

  This file mirrors the Lean Stage L4 Fubini-interchange deliverable
  for the polylog-Hankel identity. The Lean side proves, for
  0 < Re s, |z| < 1, z /= 0:

      Sum_{n=0..} integral_(0, inf) (-t)^(s-1) z^(n+1) e^(-(n+1) t) dt
        = integral_(0, inf) (-t)^(s-1) Sum_{n=0..} z^(n+1) e^(-(n+1) t) dt
        = integral_(0, inf) t^(s-1) / (e^t / z - 1) dt

  via mathlib's
  `MeasureTheory.integral_tsum_of_summable_integral_norm` and the
  Gamma-integrand norm bound. Mathlib provides termwise
  integral/tsum interchange; Coq stdlib does NOT (no
  `MeasureTheory`, no Bochner integral on Banach spaces, no
  Lebesgue measure on R-sets like `Ioi 0`).

  We therefore port this file as a STRUCTURAL Prop framework with
  the Complex-dependent and measure-theoretic content declared as
  Parameter, the four PROVEN downstream re-export theorems
  expressed via `polylogHankelTerm` abstractions, and the capstone
  identity expressed as the conditional reduction.

  ## What is PROVED here (axiom-free over the documented Parameters)

    * Per-term integrability predicate (abstract).
    * Termwise norm closed-form Prop.
    * Summability of the L^1 norm series (abstract Prop).
    * Termwise tsum-integral interchange Prop.
    * Capstone identity Prop.

  All five are stated as Props mirroring the Lean theorems, with the
  re-export pattern preserved exactly.

  ## What requires Parameter (documented gaps)

    * `polylogHankelTerm`, `polylogHankelTerm_integrable`,
      `polylogHankelTerm_integral_norm_eq`,
      `summable_integral_norm_polylogHankel`,
      `polylogHankel_tsum_integral_eq_integral_tsum`,
      `polylogHankel_termwise_interchange_capstone` —
      Complex-valued integrand + Lebesgue measure on Ioi 0.
      Coq stdlib lacks Complex, Bochner integral, integral_tsum,
      Real.Gamma, etc.
    * `IntegrableOnIoi`, `SummableNat`, `IntegralIoi`, `TSumNat` —
      structural Prop predicates abstracting the missing Mathlib
      MeasureTheory / topology infrastructure.

  ## Provenance

  Lean source: PF_Lean4_Code/PF/Analytic/HankelFubini.lean
  Lean axioms used in source: ZERO (depends on
    PF/Analytic/HankelTermwiseInterchange.lean for the substantive
    proofs).
  Coq axioms used here: documented Parameters for Complex / Bochner
    integral / MeasureTheory content unavailable in stdlib.

  Stage L4 mirror — Hankel-polylog Fubini step (2026-05-20).
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.
Require Import PrincipiaTractalis.Analytic.PolyLogSheaf.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Abstract MeasureTheory / Bochner integral skeleton *)
(* ============================================================ *)

(** Abstract "integrable on (0, infinity)" predicate.

    GAP: Lean Mathlib has `IntegrableOn f (Ioi 0) MeasureSpace.volume`
    which requires Bochner integral + Lebesgue measure on R. Coq
    stdlib has neither. *)
Parameter IntegrableOnIoi : (R -> RpR) -> Prop.

(** Abstract Lebesgue integral over (0, infinity) of an RpR-valued
    function.

    GAP: requires Bochner integral on Lebesgue measure, not in
    Coq stdlib. *)
Parameter IntegralIoi : (R -> RpR) -> RpR.

(** Abstract "summable nat-indexed family" predicate (Mathlib's
    `Summable` on nat).

    GAP: Coq stdlib's `infinite_sum` is reals-only; complex
    summability requires extending or invoking Coquelicot. *)
Parameter SummableNat : (nat -> RpR) -> Prop.

(** Abstract tsum over a nat-indexed family. *)
Parameter TSumNat : (nat -> RpR) -> RpR.

(** Abstract norm on RpR. Mirror of `Complex.norm`. *)
Parameter cnormRpR : RpR -> R.

(** Abstract Real.Gamma. GAP: stdlib has no Gamma function. *)
Parameter GammaReal : R -> R.

(** Abstract Complex.exp. GAP: stdlib has no Complex.exp. *)
Parameter cexp : RpR -> RpR.

(** Abstract Complex.cpow (t : R, s : C) |-> t^s. *)
Parameter cpowR : R -> RpR -> RpR.

(* ============================================================ *)
(* Section 2: The per-term polylog-Hankel integrand              *)
(* ============================================================ *)

(** The per-term polylog-Hankel integrand:
    F_n(t) := t^(s-1) * z^(n+1) * e^(-(n+1)*t).

    GAP: requires Complex.cpow and Complex.exp. *)
Parameter polylogHankelTerm : RpR -> RpR -> nat -> R -> RpR.

(** **Per-term integrand re-export**:
    `integrand s z n t := polylogHankelTerm s z n t`. *)
Definition integrand (s z : RpR) (n : nat) (t : R) : RpR :=
  polylogHankelTerm s z n t.

(* ============================================================ *)
(* Section 3: Per-term integrability                             *)
(* ============================================================ *)

(** **Per-term integrability**: F_n is integrable on (0, inf) for
    0 < Re s.

    GAP: requires Lebesgue measure + Bochner integral. Mirror of
    Lean `polylogHankelTerm_integrable`. *)
Parameter polylogHankelTerm_integrable :
  forall (s : RpR), 0 < cre s ->
  forall (z : RpR) (n : nat),
    IntegrableOnIoi (integrand s z n).

(** **Per-term integrability re-export**.
    Mirror of Lean `HankelFubini.integrand_integrable_per_term`. *)
Theorem integrand_integrable_per_term :
  forall (s : RpR), 0 < cre s ->
  forall (z : RpR) (n : nat),
    IntegrableOnIoi (integrand s z n).
Proof.
  intros s Hs z n.
  exact (polylogHankelTerm_integrable s Hs z n).
Qed.

(* ============================================================ *)
(* Section 4: Per-term norm-integral closed form                 *)
(* ============================================================ *)

(** Helper: nat-to-R conversion. *)
Definition INR_succ (n : nat) : R := INR n + 1.

(** GAP: real power with real exponent (Coq stdlib has Rpower,
    but only for positive base). We expose it as a parameter for
    parity with the Lean side's `(n + 1)^(-Re s)`. *)
Parameter RpowMinus : R -> R -> R.

(** GAP: closed form for the per-term L1 norm integral.
    `integral_(0, inf) ||F_n(t)|| dt =
       ||z||^(n+1) * (n+1)^(-Re s) * Gamma(Re s)`. *)
Parameter polylogHankelTerm_integral_norm_eq :
  forall (s : RpR), 0 < cre s ->
  forall (z : RpR) (n : nat),
    IntegralIoi (fun t => (cnormRpR (integrand s z n t), 0)) =
    (cnormRpR z ^ (n + 1) *
       (RpowMinus (INR_succ n) (- cre s) * GammaReal (cre s)), 0).

(** **Per-term norm-integral re-export**.
    Mirror of Lean `HankelFubini.integral_norm_per_term`. *)
Theorem integral_norm_per_term :
  forall (s : RpR), 0 < cre s ->
  forall (z : RpR) (n : nat),
    IntegralIoi (fun t => (cnormRpR (integrand s z n t), 0)) =
    (cnormRpR z ^ (n + 1) *
       (RpowMinus (INR_succ n) (- cre s) * GammaReal (cre s)), 0).
Proof.
  intros s Hs z n.
  exact (polylogHankelTerm_integral_norm_eq s Hs z n).
Qed.

(* ============================================================ *)
(* Section 5: Summability of the L1 norm series                  *)
(* ============================================================ *)

(** GAP: the summable-majorant content.
    Mirror of Lean `summable_integral_norm_polylogHankel`. *)
Parameter summable_integral_norm_polylogHankel :
  forall (s : RpR), 0 < cre s ->
  forall (z : RpR), cnormRpR z < 1 ->
    SummableNat (fun n : nat =>
      IntegralIoi (fun t => (cnormRpR (integrand s z n t), 0))).

(** **Summable majorant re-export**.
    Mirror of Lean `HankelFubini.summable_integral_norm`. *)
Theorem summable_integral_norm :
  forall (s : RpR), 0 < cre s ->
  forall (z : RpR), cnormRpR z < 1 ->
    SummableNat (fun n : nat =>
      IntegralIoi (fun t => (cnormRpR (integrand s z n t), 0))).
Proof.
  intros s Hs z Hz.
  exact (summable_integral_norm_polylogHankel s Hs z Hz).
Qed.

(* ============================================================ *)
(* Section 6: The Fubini termwise interchange                    *)
(* ============================================================ *)

(** GAP: the termwise tsum/integral interchange — load-bearing
    Mathlib `MeasureTheory.integral_tsum_of_summable_integral_norm`.
    Coq stdlib lacks this entirely; the residual lemma is named
    here.

    Mirror of Lean `polylogHankel_tsum_integral_eq_integral_tsum`. *)
Parameter polylogHankel_tsum_integral_eq_integral_tsum :
  forall (s : RpR), 0 < cre s ->
  forall (z : RpR), cnormRpR z < 1 ->
    TSumNat (fun n : nat => IntegralIoi (integrand s z n)) =
    IntegralIoi (fun t => TSumNat (fun n : nat => integrand s z n t)).

(** **Termwise tsum/integral interchange re-export** — the primary
    deliverable.

    Mirror of Lean `HankelFubini.tsum_integral_eq_integral_tsum`. *)
Theorem tsum_integral_eq_integral_tsum :
  forall (s : RpR), 0 < cre s ->
  forall (z : RpR), cnormRpR z < 1 ->
    TSumNat (fun n : nat => IntegralIoi (integrand s z n)) =
    IntegralIoi (fun t => TSumNat (fun n : nat => integrand s z n t)).
Proof.
  intros s Hs z Hz.
  exact (polylogHankel_tsum_integral_eq_integral_tsum s Hs z Hz).
Qed.

(* ============================================================ *)
(* Section 7: Identification with the kernel form (capstone)     *)
(* ============================================================ *)

(** Abstract complex division. *)
Parameter cdiv : RpR -> RpR -> RpR.

(** Abstract complex subtraction. *)
Parameter csub : RpR -> RpR -> RpR.

(** Abstract complex multiplication. *)
Parameter cmul : RpR -> RpR -> RpR.

(** Complex 1. *)
Definition Cone : RpR := (1, 0).

(** GAP: the capstone identity reducing the tsum-of-integrals to the
    integral against the Hankel kernel `1 / (e^t / z - 1)`.

    Mirror of Lean `polylogHankel_termwise_interchange_capstone`. *)
Parameter polylogHankel_termwise_interchange_capstone :
  forall (s : RpR), 0 < cre s ->
  forall (z : RpR), cnormRpR z < 1 -> z <> (0, 0) ->
    TSumNat (fun n : nat => IntegralIoi (integrand s z n)) =
    IntegralIoi (fun t =>
      cmul (cpowR t (csub s Cone))
           (cdiv Cone (csub (cdiv (cexp (t, 0)) z) Cone))).

(** **Capstone re-export**.
    Mirror of Lean `HankelFubini.capstone`. *)
Theorem capstone :
  forall (s : RpR), 0 < cre s ->
  forall (z : RpR), cnormRpR z < 1 -> z <> (0, 0) ->
    TSumNat (fun n : nat => IntegralIoi (integrand s z n)) =
    IntegralIoi (fun t =>
      cmul (cpowR t (csub s Cone))
           (cdiv Cone (csub (cdiv (cexp (t, 0)) z) Cone))).
Proof.
  intros s Hs z Hz Hne.
  exact (polylogHankel_termwise_interchange_capstone s Hs z Hz Hne).
Qed.

(* ============================================================ *)
(* Status: STRUCTURAL PORT of Lean HankelFubini.lean             *)
(*                                                              *)
(* PROVEN (this file, axiom-free over the documented Parameters):*)
(*   * integrand_integrable_per_term (re-export, one-liner)      *)
(*   * integral_norm_per_term (re-export)                        *)
(*   * summable_integral_norm (re-export)                        *)
(*   * tsum_integral_eq_integral_tsum (re-export)                *)
(*   * capstone (re-export)                                      *)
(*                                                              *)
(* GAPS (Parameters, documented):                                *)
(*   * IntegrableOnIoi, IntegralIoi, SummableNat, TSumNat        *)
(*     (Bochner integral + tsum infrastructure; Coq stdlib gap)  *)
(*   * cnormRpR, GammaReal, cexp, cpowR, RpowMinus, cdiv, csub,  *)
(*     cmul (Complex.norm + Real.Gamma + Complex.exp + cpow      *)
(*     not in stdlib)                                            *)
(*   * polylogHankelTerm — the per-term integrand                *)
(*   * polylogHankelTerm_integrable                              *)
(*   * polylogHankelTerm_integral_norm_eq                        *)
(*   * summable_integral_norm_polylogHankel                      *)
(*   * polylogHankel_tsum_integral_eq_integral_tsum              *)
(*     (Mathlib's integral_tsum_of_summable_integral_norm)       *)
(*   * polylogHankel_termwise_interchange_capstone               *)
(*                                                              *)
(* Closure path: Coquelicot 3.4.x (provides C, Cexp, integral)   *)
(* + a Coq-side port of Real.Gamma + a Coq-side port of          *)
(* MeasureTheory.integral_tsum_of_summable_integral_norm         *)
(* (which is itself nontrivial — requires Bochner integration    *)
(* on Banach spaces, currently a multi-month formalization).     *)
(* ============================================================ *)
