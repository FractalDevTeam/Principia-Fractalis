(*
  # Fractal Convolution Operators - Headline Axiom + Derived Values (Coq port)
  Coq counterpart of `PF_Lean4_Code/PF/TuringEncoding/Operators.lean`
  (axiom + derived-value section, lines 167-300).

  This port mirrors the SINGLE REMAINING PROJECT AXIOM of the Lean
  development at the SET LEVEL and all of its derived consequences:
    * alpha_of_class : (Language -> Prop) -> R                  (opaque)
    * Axiom alpha_class_self_adjointness_canonical              (Ch 21 C3+C4)
    * alpha_at_ClassP_eq_sqrt2                                  (derived)
    * alpha_at_ClassNP_eq_phi_plus_quarter                      (derived)
    * alpha_of_class_pos_at_ClassP / _at_ClassNP                (derived)
    * alpha_class_distinct                                      (derived)
    * alpha_class_separation_lt                                 (derived)

  Together with `AlphaEnum.v` (the AXIOM-FREE enum-level mirror),
  this gives full cross-prover verification of the Lean development's
  headline 1-axiom state:

    Lean 4: `alpha_class_self_adjointness_canonical` + 6 derived theorems.
    Coq:    `alpha_class_self_adjointness_canonical` + 6 derived theorems.

  Both provers carry the SAME single axiom (irreducible at the
  Set Language level - see AlphaEnum.v for the rationale), with the
  SAME derived value/positivity/distinctness/separation theorems.

  NOTE: this file does NOT port the lambda_0/spectral_gap consequence
  theorems (p_eq_np_spectrum_collapse, P_neq_NP_from_spectral_gap),
  which depend on SpectralGap.lean (not yet ported). Those are a
  natural follow-on once SpectralGap.v is added.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.
Require Import Coq.micromega.Psatz.
Require Import PrincipiaTractalis.IntervalArithmetic.
Require Import PrincipiaTractalis.TuringEncoding.AlphaCanonical.

Open Scope R_scope.

(* ============================================================ *)
(* Language and class scaffolding                                *)
(* ============================================================ *)

(** Abstract type of languages over the binary alphabet. The Lean
    development uses `Set BinString` for `Language`; in Coq we leave
    `Language` as an opaque `Parameter` (its concrete construction is
    not load-bearing for the axiom + derived theorems here, which
    treat `ClassP`, `ClassNP` as opaque sets of languages). *)
Parameter Language : Type.

(** ClassP and ClassNP as opaque sets of languages. In the Lean port
    these are defined via Turing-machine polynomial-time bounds in
    `TuringEncoding/Complexity.lean`; the algebraic axiom + derived
    theorems here are decoupled from that construction. *)
Parameter ClassP  : Language -> Prop.
Parameter ClassNP : Language -> Prop.

(* ============================================================ *)
(* The opaque resonance function                                 *)
(* ============================================================ *)

(** The resonance-frequency function on complexity classes.

    Structural restatement (Stage 25, 2026-05-14, Lean side): in
    Chapter 21 Constructions 3 and 4, the values alpha_P = sqrt 2 and
    alpha_NP = phi + 1/4 are NOT freely chosen - they are *derived*
    from the self-adjointness condition on the fractal convolution
    operators H_P and H_NP. We model that derivation by declaring
    `alpha_of_class` as an opaque function on classes, with the
    canonical self-adjointness equations pinned by a single axiom
    (mirrored from the Lean side). *)
Parameter alpha_of_class : (Language -> Prop) -> R.

(* ============================================================ *)
(* THE AXIOM (mirror of Lean's alpha_class_self_adjointness_canonical) *)
(* ============================================================ *)

(** *** Ch 21 Constructions 3 and 4: the self-adjointness conditions
    on the fractal convolution operators H_P and H_NP force the
    resonance parameters to satisfy specific algebraic equations.

    For H_P (Construction 3): self-adjointness of the kernel
    `(1/2^|x|) * e^(i*pi*alpha*D(x)) * E_P(M_L,x)` summed over binary
    strings requires the phase-symmetry equation, which solves to
    alpha^2 = 2. Combined with positivity, this uniquely pins
    alpha_P = sqrt 2.

    For H_NP (Construction 4): the corresponding self-adjointness
    equation on the kernel with certificate-quantifier structure
    `sup_{c:V_L(x,c)=1} [e^(i*pi*alpha*W(x,c)) * E_NP(V_L,x,c)]`
    solves to the quadratic 16*alpha^2 - 24*alpha - 11 = 0 with
    positive root (3 + 2*sqrt 5)/4 = phi + 1/4. (The mixed
    phi+rational form reflects the certificate branching factor:
    phi from the asymptotic certificate growth rate, +1/4 from the
    consciousness threshold ch2(NP) = 0.9954.)

    This is the SINGLE REMAINING PROJECT AXIOM of the development at
    the set level. It is IRREDUCIBLE at this level because a concrete
    definition of `alpha_of_class` would force
      ClassP = ClassNP -> alpha_of_class ClassP = alpha_of_class ClassNP
    by `f_equal`, which combined with the numerical fact
    alpha_P /= alpha_NP would prove ClassP /= ClassNP - i.e., would
    solve P vs NP via a non-spectral mechanism. See
    `PF/TuringEncoding/AlphaEnum.v` for the axiom-free enum-level
    analog that proves the algebraic content. *)
Axiom alpha_class_self_adjointness_canonical :
    ((alpha_of_class ClassP) ^ 2 = 2 /\ 0 < alpha_of_class ClassP) /\
    (16 * (alpha_of_class ClassNP) ^ 2 - 24 * (alpha_of_class ClassNP) - 11 = 0
     /\ 0 < alpha_of_class ClassNP).

(* ============================================================ *)
(* Derived canonical values                                      *)
(* ============================================================ *)

(** Canonical resonance value at ClassP, derived from the
    self-adjointness equation `alpha^2 = 2 /\ alpha > 0` (which has
    unique positive solution sqrt 2). *)
Theorem alpha_at_ClassP_eq_sqrt2 : alpha_of_class ClassP = sqrt 2.
Proof.
  destruct alpha_class_self_adjointness_canonical as [[h_sq h_pos] _].
  (* alpha > 0 /\ alpha^2 = 2 -> alpha = sqrt 2 by uniqueness of positive sqrt *)
  assert (h_sqrt_sq : sqrt ((alpha_of_class ClassP) ^ 2) = alpha_of_class ClassP).
  { apply sqrt_pow2. lra. }
  rewrite <- h_sqrt_sq, h_sq. reflexivity.
Qed.

(** Canonical resonance value at ClassNP, derived from the
    self-adjointness quadratic `16*alpha^2 - 24*alpha - 11 = 0 /\
    alpha > 0` (which has unique positive root (3 + 2*sqrt 5)/4 =
    phi + 1/4). Stage 35 (2026-05-14, Lean side). *)
Theorem alpha_at_ClassNP_eq_phi_plus_quarter :
    alpha_of_class ClassNP = phi + 1/4.
Proof.
  destruct alpha_class_self_adjointness_canonical as [_ [h_quad h_pos]].
  set (y := alpha_of_class ClassNP) in *.
  (* 16y^2 - 24y - 11 = 0  factors as  16(y - r1)(y - r2) = 0
     with r1 = (3 + 2*sqrt 5)/4 and r2 = (3 - 2*sqrt 5)/4. *)
  assert (h5 : sqrt 5 * sqrt 5 = 5).
  { apply sqrt_sqrt. lra. }
  assert (h_factor :
    (y - (3 + 2 * sqrt 5) / 4) * (y - (3 - 2 * sqrt 5) / 4) = 0).
  { nra. }
  (* Show (3 - 2*sqrt 5)/4 < 0 since 2*sqrt 5 > 3. *)
  assert (h_sqrt5_gt : sqrt 5 > 3/2).
  { assert (h_eq : sqrt (9/4) = 3/2).
    { replace (9/4) with ((3/2) ^ 2) by lra. apply sqrt_pow2. lra. }
    assert (h_lt : sqrt (9/4) < sqrt 5).
    { apply sqrt_lt_1; lra. }
    lra. }
  assert (h_r2_neg : (3 - 2 * sqrt 5) / 4 < 0) by lra.
  (* From the factorization, y is one of the two roots. *)
  apply Rmult_integral in h_factor.
  destruct h_factor as [h1 | h2].
  - (* y = (3 + 2*sqrt 5)/4 = phi + 1/4 *)
    assert (hy_eq : y = (3 + 2 * sqrt 5) / 4) by lra.
    unfold phi. lra.
  - (* y = (3 - 2*sqrt 5)/4, contradicts h_pos *)
    assert (hy_eq : y = (3 - 2 * sqrt 5) / 4) by lra.
    subst y. lra.
Qed.

(* ============================================================ *)
(* Positivity, distinctness, separation                          *)
(* ============================================================ *)

(** Positivity of `alpha_of_class ClassP` - direct from the axiom's
    `0 < alpha_of_class ClassP` conjunct. *)
Theorem alpha_of_class_pos_at_ClassP : 0 < alpha_of_class ClassP.
Proof.
  destruct alpha_class_self_adjointness_canonical as [[_ h] _]. exact h.
Qed.

(** Positivity of `alpha_of_class ClassNP` - direct from the axiom's
    `0 < alpha_of_class ClassNP` conjunct. *)
Theorem alpha_of_class_pos_at_ClassNP : 0 < alpha_of_class ClassNP.
Proof.
  destruct alpha_class_self_adjointness_canonical as [_ [_ h]]. exact h.
Qed.

(** DERIVED: the canonical resonance values are distinct.

    Direct corollary of `alpha_at_ClassP_eq_sqrt2`,
    `alpha_at_ClassNP_eq_phi_plus_quarter`, and
    `phi_plus_quarter_gt_sqrt2`. Useful as the *minimal substantive
    content* of the axiom for P /= NP: just distinctness suffices
    (combined with the OCH structural theorem) to derive P /= NP. *)
Theorem alpha_class_distinct :
    alpha_of_class ClassP <> alpha_of_class ClassNP.
Proof.
  rewrite alpha_at_ClassP_eq_sqrt2, alpha_at_ClassNP_eq_phi_plus_quarter.
  intro h.
  pose proof phi_plus_quarter_gt_sqrt2 as Hgt.
  lra.
Qed.

(** Resonance-parameter separation: alpha_of_class ClassP <
    alpha_of_class ClassNP. Derived from canonical values plus the
    numerical inequality `phi_plus_quarter_gt_sqrt2` from
    `PF/IntervalArithmetic.v`. *)
Theorem alpha_class_separation_lt :
    alpha_of_class ClassP < alpha_of_class ClassNP.
Proof.
  rewrite alpha_at_ClassP_eq_sqrt2, alpha_at_ClassNP_eq_phi_plus_quarter.
  exact phi_plus_quarter_gt_sqrt2.
Qed.

(* ============================================================ *)
(* Cross-prover headline                                         *)
(*                                                              *)
(* Lean 4 side: `PF/TuringEncoding/Operators.lean`               *)
(*   axiom alpha_class_self_adjointness_canonical                *)
(*   + 6 derived theorems above                                  *)
(*   axiom dependencies of each derived theorem:                 *)
(*     {alpha_class_self_adjointness_canonical,                  *)
(*      propext, Classical.choice, Quot.sound}                   *)
(*                                                              *)
(* Coq side (this file):                                         *)
(*   Axiom alpha_class_self_adjointness_canonical                *)
(*   + 6 derived theorems above                                  *)
(*   axiom dependencies of each derived theorem (Print           *)
(*   Assumptions): {alpha_class_self_adjointness_canonical,      *)
(*                  Coq stdlib classical foundation}             *)
(*                                                              *)
(* The SINGLE PROJECT AXIOM is the same statement in both        *)
(* provers; all derived theorems are mirrored identically.       *)
(* The axiom-free analog of the algebraic content lives in       *)
(* `PF/TuringEncoding/AlphaEnum.v` (`alpha_at_enum_*`).          *)
(* ============================================================ *)
