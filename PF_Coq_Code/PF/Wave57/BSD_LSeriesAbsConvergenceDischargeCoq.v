(*
  # BSD L-Series Absolute Convergence Discharge — Wave 57-BSD (A3)
    Upgrade — COQ PORT (Wave 58, 2026-06-02)

  Cross-prover REAL-CONTENT port of
  `PF_Lean4_Code/PF/BSD_LSeriesAbsConvergenceDischarge.lean`.

  Lean sub-namespace mirrored:
  `PrincipiaTractalis.BSD_LSeriesAbsConvergenceDischarge`
  (matched here via Coq Module of the same final name).

  ## Status

  This is NOT a parity-marker stub. The file delivers REAL Coq theorems
  via Coquelicot:

    * The generic Hasse-type coefficient bound is encoded over the REAL
      sequence `|a_n|` as a `Prop` of concrete numerical shape.
    * The structural theorem
      `HasseTypeCoefficientBound → LSeriesAbsConverges`
      is proved AXIOM-FREE via Coquelicot's `ex_series_le` (the abstract
      comparison test for series in a `CompleteNormedModule`).
    * The pure real-Dirichlet `p`-series convergence
      `∑ 1/n^s, s > 1` is encoded as a `Hypothesis`-level predicate
      `PSeriesConvergesAbovePoleOne`, NOT as `Admitted`. This is the
      precise mathlib gap on the Coq side: Coquelicot has no off-the-
      shelf `∑ 1/n^p, p > 1` lemma (mathlib has it; the Lean upgrade
      uses it directly via `LSeriesSummable_of_le_const_mul_rpow`).
    * The intersection-over-ε statement and the strict open-halfplane
      `Re s > 3/2` derivation are both proved AXIOM-FREE inside the
      Coq port via real arithmetic.
    * Composition with the original Wave 57-BSD (A3) `Prop` (encoded
      as `True` in the Lean scaffold) is recorded.

  ## Real-content surface (axiom-free without Coquelicot dependence on
      mathlib-only p-series result)

  1. `HasseTypeCoefficientBound f x C` — `forall n, n <> 0 ->
     Rabs (f n) <= C * Rpower (INR n) (x - 1)`.
  2. `PSeriesConvergesAbovePoleOne` — the (Coquelicot-gap) input:
     `forall p : R, p > 1 -> ex_series (fun n => Rpower (INR n + 1) (-p))`.
     This is the precise content of `Real.summable_one_div_nat_rpow`
     in mathlib, which is NOT yet ported to Coquelicot.
  3. `hasseBound_implies_LSeriesAbsConverges` — STRUCTURAL THEOREM:
     under the Hasse bound, `LSeriesAbsConvergesOnReGreaterThan f x`.
     PROVED via `ex_series_le` + scalar `ex_series_scal`. NO admit, NO
     axiom, but conditional on `PSeriesConvergesAbovePoleOne`.
  4. `lSeriesAbsConvergence_for_elliptic_curve_coefficient_bound` —
     concrete instantiation at `x = 3/2 + ε`.
  5. `wave57BSD_A3_strengthened` — universal ε-form.
  6. `lSeriesSummable_of_hasseTower_on_open_halfplane` — strict
     `Re s > 3/2` via ε = (Re s - 3/2)/2, real-arithmetic proof.
  7. `wave57BSD_A3_strengthened_implies_original` — mechanically
     trivial (original is `True`-shaped).

  ## Honest scope

  Identical to the Lean version:

    1. CLASSICAL Dirichlet-series convergence theorem parametrised by
       the coefficient bound `|a_n| <= C * n^(x-1)`.
    2. The Hasse-derived bound `|a_n| <= C_ε * n^(1/2+ε)` REMAINS
       encoded as a HYPOTHESIS, NOT proved here. Wave 47F gap G3
       (multiplicativity / divisor-function estimate) unchanged.
    3. Hits `Re s > 3/2 + ε` for every `ε > 0`, not literally
       `Re s > 3/2` — but the intersection statement recovers the open
       halfplane axiom-free.
    4. NOT a Clay BSD discharge.

  ## Coq libraries used

  - `Coq.Reals.Reals` (Rpower, INR, Rabs, real arithmetic)
  - `Coquelicot.Series` (`ex_series`, `ex_series_le`,
     `ex_series_scal_l`)
  - `Coquelicot.ElemFct` / `Hierarchy` (transitively for Rpower)
  - `Lra` for trivial real-arithmetic side conditions
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rpower.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.
Require Import Coq.micromega.Psatz.

(* Coquelicot real-analysis infrastructure *)
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Series.

Open Scope R_scope.

(** Mirror Lean sub-namespace
    `PrincipiaTractalis.BSD_LSeriesAbsConvergenceDischarge`. *)
Module BSD_LSeriesAbsConvergenceDischarge.

(* ============================================================ *)
(* Section 1: Real-content predicates                            *)
(* ============================================================ *)

(** **Hasse-type coefficient bound** — for some constant `C`, the real
    sequence `|f n|` satisfies `|f n| <= C * n^(x-1)` for nonzero `n`.

    On the Lean side `f : nat -> Complex`; we strip to the absolute
    value over the reals, which is sufficient for the comparison
    argument and matches the SHAPE of mathlib's
    `LSeriesSummable_of_le_const_mul_rpow` hypothesis. *)
Definition HasseTypeCoefficientBound
  (f : nat -> R) (x C : R) : Prop :=
  forall n : nat, (n <> 0)%nat ->
    Rabs (f n) <= C * Rpower (INR n) (x - 1).

(** **Absolute convergence on `Re s > x`** of the (real-projected)
    L-series.

    On the Lean side this universal-quantifies over complex `s` with
    `s.re > x`. The Coq port works at the real-`σ` level (`σ = Re s`),
    which is what comparison reduces to: the convergence of
    `∑ Rabs (f n) / n^σ`. We expose the predicate as a `forall σ > x,
    ex_series (n => Rabs (f n) * Rpower (INR n + 1) (-σ))`. The `+1`
    shift moves the natural-number index to avoid `Rpower 0 _` issues. *)
Definition LSeriesAbsConvergesOnReGreaterThan
  (f : nat -> R) (x : R) : Prop :=
  forall sigma : R, x < sigma ->
    ex_series (fun n : nat =>
                 Rabs (f (S n)) * Rpower (INR (S n)) (- sigma)).

(** **Coquelicot mathlib-gap predicate** — `∑_{n≥1} 1/n^p` converges
    whenever `p > 1`. Mathlib has `Real.summable_one_div_nat_rpow`;
    Coquelicot does NOT have a direct off-the-shelf lemma. We carry
    this as a HYPOTHESIS at exactly the gap point.

    NOTE: this is the *only* analytic input we do not prove
    axiom-free in this file. Every theorem in §3+ takes
    `PSeriesConvergesAbovePoleOne` as a hypothesis explicitly. *)
Definition PSeriesConvergesAbovePoleOne : Prop :=
  forall p : R, 1 < p ->
    ex_series (fun n : nat => Rpower (INR (S n)) (- p)).

(* ============================================================ *)
(* Section 2: Auxiliary real lemmas                              *)
(* ============================================================ *)

(** `INR (S n) >= 1` for all `n`. *)
Lemma INR_S_ge_one : forall n : nat, 1 <= INR (S n).
Proof.
  intro n. rewrite S_INR.
  generalize (pos_INR n). lra.
Qed.

(** `INR (S n) > 0`. *)
Lemma INR_S_pos : forall n : nat, 0 < INR (S n).
Proof.
  intro n. generalize (INR_S_ge_one n). lra.
Qed.

(** Pointwise nonnegativity used by the comparison test. *)
Lemma scaled_nonneg :
  forall (f : nat -> R) (sigma : R) (n : nat),
    0 <= Rabs (f (S n)) * Rpower (INR (S n)) (- sigma).
Proof.
  intros f sigma n.
  apply Rmult_le_pos.
  - apply Rabs_pos.
  - left. apply exp_pos.
Qed.

(** Rpower of positive base is positive. *)
Lemma Rpower_pos_S : forall (n : nat) (y : R), 0 < Rpower (INR (S n)) y.
Proof. intros. apply exp_pos. Qed.

(** Key algebraic identity used in the comparison bound:
    `Rpower x (a-1) * Rpower x (-σ) = Rpower x (a - 1 - σ)`,
    for `x > 0`. *)
Lemma Rpower_mul_combine :
  forall (x a sigma : R),
    0 < x ->
    Rpower x (a - 1) * Rpower x (- sigma) =
    Rpower x ((a - 1) + (- sigma)).
Proof.
  intros x a sigma Hx.
  rewrite <- Rpower_plus. reflexivity.
Qed.

(* ============================================================ *)
(* Section 3: ★ STRUCTURAL THEOREM ★                             *)
(*                                                                *)
(*   HasseTypeCoefficientBound f x C                              *)
(*   + PSeriesConvergesAbovePoleOne                               *)
(*   ⇒ LSeriesAbsConvergesOnReGreaterThan f x                     *)
(* ============================================================ *)

(** **★ STRUCTURAL THEOREM ★** — Hasse-type coefficient bound implies
    absolute convergence on `Re s > x`.

    PROOF outline: pick `σ > x`. Bound

      Rabs (f (S n)) * Rpower (INR (S n)) (- σ)
        <= C * Rpower (INR (S n)) (x - 1) * Rpower (INR (S n)) (- σ)
        =  C * Rpower (INR (S n)) ((x - 1) - σ).

    The exponent `(x - 1) - σ < (x - 1) - x = -1`, so the dominating
    series is `∑ C * Rpower (INR (S n)) (-p)` with `p = σ - (x - 1) > 1`.
    By `PSeriesConvergesAbovePoleOne` plus `ex_series_scal_l`, the
    dominating series converges. Apply `ex_series_le`. *)
Theorem hasseBound_implies_LSeriesAbsConverges
  (f : nat -> R) (x C : R)
  (hPS : PSeriesConvergesAbovePoleOne)
  (hBound : HasseTypeCoefficientBound f x C) :
  LSeriesAbsConvergesOnReGreaterThan f x.
Proof.
  unfold LSeriesAbsConvergesOnReGreaterThan.
  intros sigma Hsig.
  set (p := sigma - (x - 1)).
  assert (Hp : 1 < p).
  { unfold p. lra. }
  (* Dominating series: n |-> Rabs C * Rpower (INR (S n)) (- p). *)
  set (dom := fun n : nat => Rabs C * Rpower (INR (S n)) (- p)).
  assert (Hdom : ex_series dom).
  { unfold dom.
    apply (ex_series_scal_l (V := R_NormedModule) (Rabs C)
             (fun n : nat => Rpower (INR (S n)) (- p))).
    apply hPS. exact Hp. }
  apply (@ex_series_le R_AbsRing R_CompleteNormedModule
           (fun n : nat =>
              Rabs (f (S n)) * Rpower (INR (S n)) (- sigma))
           dom).
  - intro n.
    (* Comparison: |a_{n+1}| * (n+1)^(-σ) <= C * (n+1)^(x-1) * (n+1)^(-σ)
                                         = C * (n+1)^((x-1) - σ)
                                         = C * (n+1)^(-p). *)
    assert (HnNZ : (S n <> 0)%nat) by lia.
    specialize (hBound (S n) HnNZ).
    assert (HpowPos : 0 < Rpower (INR (S n)) (- sigma)) by apply exp_pos.
    (* Step 1: bound Rabs(f) * pow <= C * pow_{x-1} * pow_{-σ}. *)
    assert (Step1 :
      Rabs (f (S n)) * Rpower (INR (S n)) (- sigma) <=
      C * Rpower (INR (S n)) (x - 1) * Rpower (INR (S n)) (- sigma)).
    { apply Rmult_le_compat_r; [ lra | exact hBound ]. }
    (* Step 2: combine exponents. *)
    assert (Step2 :
      C * Rpower (INR (S n)) (x - 1) * Rpower (INR (S n)) (- sigma) =
      C * Rpower (INR (S n)) (- p)).
    { unfold p.
      rewrite Rmult_assoc.
      rewrite Rpower_mul_combine by apply INR_S_pos.
      f_equal. f_equal. ring. }
    rewrite Step2 in Step1.
    (* Goal: norm (Rabs (f (S n)) * pow) <= dom n.
       Norm on R is Rabs; the LHS is nonneg so its Rabs equals itself. *)
    simpl.
    rewrite Rabs_right.
    + eapply Rle_trans; [ exact Step1 |].
      unfold dom.
      apply Rmult_le_compat_r.
      * left. apply exp_pos.
      * apply Rle_abs.
    + apply Rle_ge.
      apply Rmult_le_pos; [ apply Rabs_pos | left; apply exp_pos ].
  - exact Hdom.
Qed.

(* ============================================================ *)
(* Section 4: Concrete instantiation at the elliptic-curve       *)
(*            Hasse-Weil bound `|a_n| <= C_ε * n^(1/2 + ε)`      *)
(* ============================================================ *)

(** **Hasse-Weil-derived bound at level ε** — the form satisfied by
    the elliptic-curve coefficient sequence via Hasse + divisor-
    function. *)
Definition EllipticCurveHasseEpsBound
  (f : nat -> R) (epsilon C : R) : Prop :=
  HasseTypeCoefficientBound f (3 / 2 + epsilon) C.

(** **★ Elliptic-curve abs convergence at level ε ★** — direct
    corollary of the structural theorem. *)
Theorem lSeriesAbsConvergence_for_elliptic_curve_coefficient_bound
  (f : nat -> R) (epsilon C : R)
  (hPS : PSeriesConvergesAbovePoleOne)
  (hBound : EllipticCurveHasseEpsBound f epsilon C) :
  LSeriesAbsConvergesOnReGreaterThan f (3 / 2 + epsilon).
Proof.
  exact (hasseBound_implies_LSeriesAbsConverges f (3 / 2 + epsilon) C
           hPS hBound).
Qed.

(* ============================================================ *)
(* Section 5: Universal ε-form (the strengthened (A3) Prop)      *)
(* ============================================================ *)

(** **Wiles-ε Hasse tower** — for every `ε > 0`, the Hasse-derived
    bound at level ε holds with some constant `C_ε`. This is the
    ε-tower content of the Hasse-Weil bound. *)
Definition WilesEpsilonHasseTowerHolds (f : nat -> R) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists C : R, EllipticCurveHasseEpsBound f epsilon C.

(** **★ WAVE 57-BSD (A3) STRENGTHENED ★** — universal ε-form of the
    analytic discharge. *)
Theorem wave57BSD_A3_strengthened
  (f : nat -> R)
  (hPS : PSeriesConvergesAbovePoleOne)
  (hTower : WilesEpsilonHasseTowerHolds f) :
  forall epsilon : R, 0 < epsilon ->
    LSeriesAbsConvergesOnReGreaterThan f (3 / 2 + epsilon).
Proof.
  intros epsilon Heps.
  destruct (hTower epsilon Heps) as [C hBound].
  exact (lSeriesAbsConvergence_for_elliptic_curve_coefficient_bound
           f epsilon C hPS hBound).
Qed.

(* ============================================================ *)
(* Section 6: Open halfplane Re s > 3/2 via ε = (σ - 3/2)/2      *)
(* ============================================================ *)

(** **★ Strict `σ > 3/2` from the ε-tower ★** — for any real `σ > 3/2`,
    absolute convergence follows by choosing `ε = (σ - 3/2)/2`.

    AXIOM-FREE: pure real arithmetic + `wave57BSD_A3_strengthened`. *)
Theorem lSeriesSummable_of_hasseTower_on_open_halfplane
  (f : nat -> R)
  (hPS : PSeriesConvergesAbovePoleOne)
  (hTower : WilesEpsilonHasseTowerHolds f)
  (sigma : R) (Hsig : 3 / 2 < sigma) :
  ex_series (fun n : nat =>
               Rabs (f (S n)) * Rpower (INR (S n)) (- sigma)).
Proof.
  set (epsilon := (sigma - 3 / 2) / 2).
  assert (Heps_pos : 0 < epsilon).
  { unfold epsilon. apply Rdiv_lt_0_compat; lra. }
  assert (Heps_lt : 3 / 2 + epsilon < sigma).
  { unfold epsilon. lra. }
  pose proof (wave57BSD_A3_strengthened f hPS hTower epsilon Heps_pos)
       as Hconv.
  unfold LSeriesAbsConvergesOnReGreaterThan in Hconv.
  apply Hconv. exact Heps_lt.
Qed.

(* ============================================================ *)
(* Section 7: Bridge to the original Wave 57-BSD (A3) Prop       *)
(* ============================================================ *)

(** **Lean-side original (A3) Prop** — encoded as `True` in
    `BSD_LSeriesConvergenceScaffold`. We mirror as a Coq `Prop`. *)
Definition LSeriesAbsConvergenceForReSGreaterThanThreeHalves : Prop := True.

(** **The strengthened (A3) implies the original `True`-shaped (A3)**.
    Trivial, recorded for parity with the Lean discharge. *)
Theorem wave57BSD_A3_strengthened_implies_original
  (f : nat -> R)
  (_hStrengthened :
     forall epsilon : R, 0 < epsilon ->
       LSeriesAbsConvergesOnReGreaterThan f (3 / 2 + epsilon)) :
  LSeriesAbsConvergenceForReSGreaterThanThreeHalves.
Proof. exact I. Qed.

(** **The strengthened (A3) feeds the four-input Wave 57-BSD cascade**. *)
Theorem wave57BSD_strengthened_A3_yields_original_A3_via_eps_tower
  (f : nat -> R)
  (hPS : PSeriesConvergesAbovePoleOne)
  (hTower : WilesEpsilonHasseTowerHolds f) :
  LSeriesAbsConvergenceForReSGreaterThanThreeHalves.
Proof.
  apply (wave57BSD_A3_strengthened_implies_original f).
  apply wave57BSD_A3_strengthened; assumption.
Qed.

(* ============================================================ *)
(* Section 8: Honest-scope marker + capstone                     *)
(* ============================================================ *)

(** **Honest-scope marker**. *)
Theorem bsd_lSeriesAbsConvergence_discharge_honest_scope : True.
Proof. exact I. Qed.

(** **★ BSD L-SERIES ABS CONVERGENCE DISCHARGE CAPSTONE ★** —
    six-clause bundle mirroring the Lean capstone.

    Under the (Coquelicot-gap) hypothesis
    `PSeriesConvergesAbovePoleOne`, all six clauses hold AXIOM-FREE
    in Coq. *)
Theorem bsd_lSeriesAbsConvergence_discharge_capstone
  (hPS : PSeriesConvergesAbovePoleOne) :
  (* (D2) Generic structural theorem. *)
  (forall (f : nat -> R) (x C : R),
     HasseTypeCoefficientBound f x C ->
     LSeriesAbsConvergesOnReGreaterThan f x)
  /\
  (* (D3) Concrete elliptic-curve instance. *)
  (forall (f : nat -> R) (epsilon C : R),
     EllipticCurveHasseEpsBound f epsilon C ->
     LSeriesAbsConvergesOnReGreaterThan f (3 / 2 + epsilon))
  /\
  (* (D4) Strengthened (A3) Prop. *)
  (forall (f : nat -> R),
     WilesEpsilonHasseTowerHolds f ->
     forall epsilon : R, 0 < epsilon ->
       LSeriesAbsConvergesOnReGreaterThan f (3 / 2 + epsilon))
  /\
  (* (D5) Strict open-halfplane convergence σ > 3/2. *)
  (forall (f : nat -> R),
     WilesEpsilonHasseTowerHolds f ->
     forall sigma : R, 3 / 2 < sigma ->
       ex_series (fun n : nat =>
                    Rabs (f (S n)) * Rpower (INR (S n)) (- sigma)))
  /\
  (* (D6) Strengthened form implies original `True`-shaped (A3). *)
  (forall (f : nat -> R),
     WilesEpsilonHasseTowerHolds f ->
     LSeriesAbsConvergenceForReSGreaterThanThreeHalves).
Proof.
  split; [| split; [| split; [| split]]].
  - intros f x C hB. exact (hasseBound_implies_LSeriesAbsConverges f x C hPS hB).
  - intros f epsilon C hB.
    exact (lSeriesAbsConvergence_for_elliptic_curve_coefficient_bound
             f epsilon C hPS hB).
  - intros f hT epsilon Heps.
    exact (wave57BSD_A3_strengthened f hPS hT epsilon Heps).
  - intros f hT sigma Hsig.
    exact (lSeriesSummable_of_hasseTower_on_open_halfplane f hPS hT sigma Hsig).
  - intros f hT.
    exact (wave57BSD_strengthened_A3_yields_original_A3_via_eps_tower
             f hPS hT).
Qed.

End BSD_LSeriesAbsConvergenceDischarge.

(* ============================================================ *)
(* Section 9: Honest scope                                       *)
(* ============================================================ *)

(*
  1. CLASSICAL Dirichlet-series absolute-convergence theorem
     parameterised by the coefficient bound |f n| <= C * n^(x-1).
     PROVED axiom-free via Coquelicot's `ex_series_le`, conditional
     on the single analytic input `PSeriesConvergesAbovePoleOne`
     (`forall p > 1, ex_series (n => (n+1)^(-p))`).

  2. `PSeriesConvergesAbovePoleOne` is mathlib's
     `Real.summable_one_div_nat_rpow`. Coquelicot does NOT carry
     this lemma off the shelf as of 3.4.4 — the precise mathlib
     gap on the Coq side. Carried as a hypothesis, NOT admitted.

  3. The Hasse-derived ε-bound |a_n| <= C_ε * n^(1/2 + ε) for
     elliptic-curve L-series coefficients remains encoded at the
     hypothesis level (Wave 47F gap G3). The PORT does not claim
     to construct it.

  4. Strict open-halfplane `Re s > 3/2` derived from the ε-tower
     via real arithmetic — same proof shape as Lean.

  5. NOT a Clay BSD discharge. This is the (A3) analytic input
     of Wave 57-BSD upgraded from `True`-placeholder to a real,
     Coquelicot-grounded theorem with one explicit analytic gap.
*)
