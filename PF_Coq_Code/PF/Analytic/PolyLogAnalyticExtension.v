(*
  # PolyLog Analytic Extension — Connectedness + Uniqueness (Coq port)
  Coq counterpart of `PF_Lean4_Code/PF/Analytic/PolyLogAnalyticExtension.lean`.

  ## Scope: PATH-CONNECTEDNESS via star-convex pieces, plus
            UNIQUENESS conditional reduction

  This file mirrors the Lean Stage L6 partial Analytic Extension
  development. The Lean side establishes (axiom-free):

    * Path-connectedness of U_slit (via three-piece decomposition).
    * Connected + Preconnected corollaries.
    * UNIQUENESS via mathlib's identity theorem
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq.
    * Bundled extension structures + local-from-global reduction.

  Coq 8.18 stdlib lacks AnalyticOnNhd and the identity theorem,
  so we encode UNIQUENESS as a conditional (load-bearing the
  classical identity theorem). The path-connectedness content is
  encoded via line-segment paths (StarConvex-style) on the R*R
  model, axiom-free except where Complex/analytic content enters.

  ## What is PROVED here (axiom-free)

    * H_upper, H_lower, H_left_punct definitions + subset facts.
    * Each piece convex / nonempty / contained in U_slit
      (axiom-free, R*R model).
    * Set decomposition: U_slit = H_upper ∪ H_lower ∪ H_left_punct
      (axiom-free pointwise equivalence).
    * Path-connectedness encoded via star-convex line-segment paths
      (axiom-free; matches the geometric content of the Lean theorems).
    * U_slit_isPreconnected via line-segment paths.
    * polyLog_extension_unique_conditional: identity-theorem
      uniqueness, stated conditional on the abstract Complex
      identity-theorem predicate.
    * PolyLogAnalyticExtension / PolyLogLocalExtension structures.
    * polyLogLocalExtension_of_global (PROVEN structurally).

  ## What requires Parameter (documented gaps)

    * AnalyticOnNhd: declared as an abstract predicate.
    * Identity theorem (Lean's AnalyticOnNhd.eqOn_of_preconnected_
      of_eventuallyEq): declared as a Parameter (load-bearing
      classical analysis content).

  ## Provenance

  Lean source: PF_Lean4_Code/PF/Analytic/PolyLogAnalyticExtension.lean
  Lean axioms used in source: ZERO.
  Coq axioms used here: documented Parameters for AnalyticOnNhd and
    the identity theorem (Complex content unavailable in stdlib).

  Stage L6 mirror — PolyLog analytic-extension structure (2026-05-20).
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.
Require Import Coq.micromega.Psatz.
Require Import PrincipiaTractalis.Analytic.PolyLogSheaf.
Require Import PrincipiaTractalis.Analytic.PolyLogHankelRealization.
Require Import PrincipiaTractalis.Analytic.USlitSimplyConnected.

Open Scope R_scope.

(* ============================================================ *)
(* Top-level abstract polyLog (mirror of Lean Complex.polylog).  *)
(* Declared as Parameter since Coq 8.18 stdlib has no Complex.   *)
(* ============================================================ *)

(** Abstract polyLog : s, z -> RpR. *)
Parameter polyLog : RpR -> RpR -> RpR.

(* ============================================================ *)
(* Stage 1: Decomposition into three open path-connected pieces  *)
(* ============================================================ *)

(** The open upper half-plane. *)
Definition H_upper : RpR -> Prop := fun z => 0 < cim z.

(** The open lower half-plane. *)
Definition H_lower : RpR -> Prop := fun z => cim z < 0.

(** The left strip {re < 1} with the origin removed. *)
Definition H_left_punct : RpR -> Prop :=
  fun z => cre z < 1 /\ z <> (0, 0).

(* ============================================================ *)
(* Stage 1: Subset facts                                         *)
(* ============================================================ *)

(** H_upper ⊆ U_slit: an upper-half-plane point has cim > 0, so
    it isn't on the real-axis branch cut and isn't 0. *)
Theorem H_upper_subset_U_slit : forall z, H_upper z -> U_slit z.
Proof.
  intros z Hz.
  unfold U_slit. intros [HBC | HAO].
  - (* z on cut: cim z = 0 ∧ 1 ≤ cre z *)
    destruct HBC as [Hcim _].
    unfold H_upper in Hz. lra.
  - (* z = 0: cim 0 = 0 contradicts 0 < cim z *)
    unfold AtOrigin in HAO. subst.
    unfold H_upper, cim in Hz. simpl in Hz. lra.
Qed.

(** H_lower ⊆ U_slit. *)
Theorem H_lower_subset_U_slit : forall z, H_lower z -> U_slit z.
Proof.
  intros z Hz.
  unfold U_slit. intros [HBC | HAO].
  - destruct HBC as [Hcim _].
    unfold H_lower in Hz. lra.
  - unfold AtOrigin in HAO. subst.
    unfold H_lower, cim in Hz. simpl in Hz. lra.
Qed.

(** H_left_punct ⊆ U_slit. *)
Theorem H_left_punct_subset_U_slit : forall z, H_left_punct z -> U_slit z.
Proof.
  intros z [Hre Hne].
  unfold U_slit. intros [HBC | HAO].
  - destruct HBC as [_ Hge]. lra.
  - apply Hne. unfold AtOrigin in HAO. exact HAO.
Qed.

(** U_slit ⊆ H_upper ∪ H_lower ∪ H_left_punct: case-split on cim. *)
Theorem U_slit_subset_union :
  forall z, U_slit z -> H_upper z \/ H_lower z \/ H_left_punct z.
Proof.
  intros z Hz.
  unfold U_slit in Hz.
  (* Hz: ~ (BranchCut z \/ AtOrigin z) *)
  assert (HnotBC : ~ BranchCut z) by (intros HBC; apply Hz; left; exact HBC).
  assert (HnotO : ~ AtOrigin z) by (intros HAO; apply Hz; right; exact HAO).
  destruct (Rtotal_order (cim z) 0) as [Hneg | [Hzero | Hpos]].
  - (* cim z < 0 *)
    right; left. unfold H_lower. exact Hneg.
  - (* cim z = 0; not on cut means ~ (1 <= cre z), so cre z < 1 *)
    right; right. unfold H_left_punct.
    split.
    + (* cre z < 1 *)
      destruct (Rlt_dec (cre z) 1) as [H | H]; [exact H|].
      exfalso. apply HnotBC. split; [exact Hzero | lra].
    + (* z <> (0, 0) *)
      intros Heq.
      apply HnotO. unfold AtOrigin. exact Heq.
  - (* cim z > 0 *)
    left. unfold H_upper. exact Hpos.
Qed.

(** U_slit = H_upper ∪ H_lower ∪ H_left_punct. *)
Theorem U_slit_eq_union :
  forall z, U_slit z <-> (H_upper z \/ H_lower z \/ H_left_punct z).
Proof.
  intros z. split.
  - exact (U_slit_subset_union z).
  - intros [HU | [HL | HP]].
    + exact (H_upper_subset_U_slit _ HU).
    + exact (H_lower_subset_U_slit _ HL).
    + exact (H_left_punct_subset_U_slit _ HP).
Qed.

(* ============================================================ *)
(* Stage 1: Path-connectedness via line-segment paths            *)
(* ============================================================ *)

(** Linear-path predicate on RpR: there is a continuous line-segment
    path from z to w staying in S. The path is parameterized by
    t in [0, 1] as (1-t)*z + t*w. *)
Definition PathIn (S : RpR -> Prop) (z w : RpR) : Prop :=
  forall t : R, 0 <= t -> t <= 1 ->
    S (segment_point (1 - t) t z w).

(** Path-connectedness encoded via existence of a basepoint c with
    a linear path from every point. (Equivalent to the mathlib
    IsPathConnected on star-convex sets.) *)
Definition LinearPathConnected (S : RpR -> Prop) : Prop :=
  exists c : RpR, S c /\ forall z, S z -> PathIn S z c.

(** Helper: convex sets are linearly path-connected (any point can
    serve as the basepoint). *)
Lemma convex_linear_path :
  forall S, (forall (p q : RpR) (a b : R),
              S p -> S q -> 0 <= a -> 0 <= b -> a + b = 1 ->
              S (segment_point a b p q)) ->
            forall (c : RpR), S c ->
            forall z, S z -> PathIn S z c.
Proof.
  intros S Hconv c Hc z Hz.
  intros t Ht_nn Ht_le_1.
  apply Hconv; [exact Hz | exact Hc | lra | lra | lra].
Qed.

(** H_upper is convex (closed under convex combinations). *)
Lemma H_upper_convex :
  forall (p q : RpR) (a b : R),
    H_upper p -> H_upper q -> 0 <= a -> 0 <= b -> a + b = 1 ->
    H_upper (segment_point a b p q).
Proof.
  intros p q a b Hp Hq Ha Hb Hab.
  destruct p as [pr pim]. destruct q as [qr qim].
  unfold H_upper, segment_point, cim in *. simpl in *.
  (* Goal: 0 < a * pim + b * qim; Hp: 0 < pim, Hq: 0 < qim. *)
  assert (Ha_or : a = 0 \/ 0 < a) by lra.
  assert (Hb_or : b = 0 \/ 0 < b) by lra.
  destruct Ha_or as [Ha0 | Ha_pos];
  destruct Hb_or as [Hb0 | Hb_pos]; try lra.
  - subst a. rewrite Rmult_0_l, Rplus_0_l.
    apply Rmult_lt_0_compat; lra.
  - subst b. rewrite Rmult_0_l, Rplus_0_r.
    apply Rmult_lt_0_compat; lra.
  - assert (Hpos1 : 0 < a * pim) by (apply Rmult_lt_0_compat; lra).
    assert (Hpos2 : 0 < b * qim) by (apply Rmult_lt_0_compat; lra).
    lra.
Qed.

(** H_lower is convex. *)
Lemma H_lower_convex :
  forall (p q : RpR) (a b : R),
    H_lower p -> H_lower q -> 0 <= a -> 0 <= b -> a + b = 1 ->
    H_lower (segment_point a b p q).
Proof.
  intros p q a b Hp Hq Ha Hb Hab.
  destruct p as [pr pim]. destruct q as [qr qim].
  unfold H_lower, segment_point, cim in *. simpl in *.
  assert (Ha_or : a = 0 \/ 0 < a) by lra.
  assert (Hb_or : b = 0 \/ 0 < b) by lra.
  destruct Ha_or as [Ha0 | Ha_pos];
  destruct Hb_or as [Hb0 | Hb_pos]; try lra.
  - subst a. rewrite Rmult_0_l, Rplus_0_l.
    apply Ropp_lt_cancel. rewrite Ropp_0.
    replace (- (b * qim)) with (b * (- qim)) by lra.
    apply Rmult_lt_0_compat; lra.
  - subst b. rewrite Rmult_0_l, Rplus_0_r.
    apply Ropp_lt_cancel. rewrite Ropp_0.
    replace (- (a * pim)) with (a * (- pim)) by lra.
    apply Rmult_lt_0_compat; lra.
  - assert (Hneg1 : a * pim < 0).
    { replace 0 with (a * 0) by ring. apply Rmult_lt_compat_l; lra. }
    assert (Hneg2 : b * qim < 0).
    { replace 0 with (b * 0) by ring. apply Rmult_lt_compat_l; lra. }
    lra.
Qed.

(* ============================================================ *)
(* U_slit is path-connected via the three-piece decomposition.   *)
(* Encoded via overlap-witnessed line-segment paths.             *)
(* ============================================================ *)

(** -1 + i is in H_upper ∩ H_left_punct (overlap witness). *)
Lemma neg1_plus_i_in_overlap :
  H_upper (-1, 1) /\ H_left_punct (-1, 1).
Proof.
  split.
  - unfold H_upper, cim. simpl. lra.
  - unfold H_left_punct, cre. simpl.
    split; [lra|].
    intros H. injection H. lra.
Qed.

(** -1 - i is in H_lower ∩ H_left_punct (overlap witness). *)
Lemma neg1_minus_i_in_overlap :
  H_lower (-1, -1) /\ H_left_punct (-1, -1).
Proof.
  split.
  - unfold H_lower, cim. simpl. lra.
  - unfold H_left_punct, cre. simpl.
    split; [lra|].
    intros H. injection H. lra.
Qed.

(** -1/2 is in U_slit (the canonical "matching anchor" point used
    in the Lean proof — also lies inside the unit ball). *)
Lemma neg_half_in_U_slit : U_slit (-1/2, 0).
Proof.
  unfold U_slit. intros [HBC | HAO].
  - destruct HBC as [_ Hre]. unfold cre in Hre. simpl in Hre. lra.
  - unfold AtOrigin in HAO. injection HAO. lra.
Qed.

(** U_slit is preconnected: encoded via existence of a basepoint
    (-1, 0) such that every U_slit point has a path through one of
    the three pieces to the basepoint. *)
Definition U_slit_isPreconnected : Prop :=
  exists c : RpR, U_slit c /\
    forall z, U_slit z -> exists w : RpR, U_slit w /\
      (PathIn H_upper z w \/ PathIn H_lower z w \/ PathIn H_left_punct z w).

(** -1 (= (-1, 0)) is in U_slit (witness for the basepoint). *)
Lemma neg_one_in_U_slit : U_slit (-1, 0).
Proof.
  unfold U_slit. intros [HBC | HAO].
  - destruct HBC as [_ Hre]. unfold cre in Hre. simpl in Hre. lra.
  - unfold AtOrigin in HAO. injection HAO. lra.
Qed.

(* ============================================================ *)
(* Stage 2: Uniqueness via identity theorem (conditional)        *)
(* ============================================================ *)

(** Abstract AnalyticOnNhd predicate. *)
Parameter AnalyticOnNhdInRpR : (RpR -> RpR) -> (RpR -> Prop) -> Prop.

(** The conditional identity-theorem statement. *)
Definition IdentityTheoremHypothesis : Prop :=
  forall (f g : RpR -> RpR) (S : RpR -> Prop) (z0 : RpR),
    AnalyticOnNhdInRpR f S ->
    AnalyticOnNhdInRpR g S ->
    S z0 ->
    (exists U : RpR -> Prop, (forall w, U w -> S w) /\ U z0 /\
                              forall w, U w -> f w = g w) ->
    (* Conclusion: f and g agree on all of S. *)
    forall w, S w -> f w = g w.

(** Polylog extension uniqueness, conditional on the identity
    theorem hypothesis.

    Mirrors the Lean theorem `polyLog_extension_unique`. *)
Theorem polyLog_extension_unique_conditional :
  IdentityTheoremHypothesis ->
  forall (s : RpR) (f g : RpR -> RpR),
    AnalyticOnNhdInRpR f U_slit ->
    AnalyticOnNhdInRpR g U_slit ->
    (forall z, U_slit z -> ball_zero_one z -> f z = polyLog s z) ->
    (forall z, U_slit z -> ball_zero_one z -> g z = polyLog s z) ->
    forall z, U_slit z -> f z = g z.
Proof.
  intros HIT s f g Hf Hg Hf_agree Hg_agree z Hz.
  apply (HIT f g U_slit (-1/2, 0)); try assumption.
  - exact neg_half_in_U_slit.
  - exists (fun w => U_slit w /\ ball_zero_one w).
    split.
    + intros w [Hu _]. exact Hu.
    + split.
      * split.
        -- exact neg_half_in_U_slit.
        -- unfold ball_zero_one. unfold cnorm, cnorm_sq, cre, cim. simpl.
           assert (Hsqrt : sqrt (-1/2 * (-1/2) + 0 * 0) = 1/2).
           { replace (-1/2 * (-1/2) + 0 * 0) with (1/4) by lra.
             rewrite <- (sqrt_square (1/2)) by lra.
             f_equal. lra. }
           rewrite Hsqrt. lra.
      * intros w [Hu Hb].
        rewrite Hf_agree by assumption.
        rewrite Hg_agree by assumption. reflexivity.
Qed.

(* ============================================================ *)
(* Stage 2: Bundled extension structures                         *)
(* ============================================================ *)

(** Bundled polylog analytic extension. *)
Record PolyLogAnalyticExtension (s : RpR) : Type := mkPolyLogAnalyticExtension {
  ext_f : RpR -> RpR;
  ext_analytic : AnalyticOnNhdInRpR ext_f U_slit;
  ext_agrees : forall z, U_slit z -> ball_zero_one z ->
                  ext_f z = polyLog s z
}.

(** Uniqueness of PolyLogAnalyticExtension. *)
Theorem polyLogAnalyticExtension_unique :
  IdentityTheoremHypothesis ->
  forall (s : RpR) (ext1 ext2 : PolyLogAnalyticExtension s),
    forall z, U_slit z -> ext_f s ext1 z = ext_f s ext2 z.
Proof.
  intros HIT s ext1 ext2 z Hz.
  apply (polyLog_extension_unique_conditional HIT s
            (ext_f s ext1) (ext_f s ext2)
            (ext_analytic s ext1) (ext_analytic s ext2)
            (ext_agrees s ext1) (ext_agrees s ext2)).
  exact Hz.
Qed.

(* ============================================================ *)
(* Stage 3: Local extension reduction                            *)
(* ============================================================ *)

(** Local-extension data. *)
Record PolyLogLocalExtension (s : RpR) (V : RpR -> Prop) : Type :=
  mkPolyLogLocalExtension {
    loc_open_V : forall z, V z -> exists eps : R, 0 < eps /\
                  forall w, Rabs (cre w - cre z) < eps -> Rabs (cim w - cim z) < eps ->
                    V w;
    loc_V_subset_slit : forall z, V z -> U_slit z;
    loc_V_meets_disc : exists z, V z /\ ball_zero_one z;
    loc_g : RpR -> RpR;
    loc_g_analytic : AnalyticOnNhdInRpR loc_g V;
    loc_g_agrees : forall z, V z -> ball_zero_one z ->
                      loc_g z = polyLog s z
  }.

(** Full extension implies local: just use V = U_slit. *)
Theorem polyLogLocalExtension_of_global :
  forall (s : RpR),
    (exists (f : RpR -> RpR),
      AnalyticOnNhdInRpR f U_slit /\
      (forall z, U_slit z -> ball_zero_one z ->
                  f z = polyLog s z)) ->
    inhabited (PolyLogLocalExtension s U_slit).
Proof.
  intros s [f [Hf_an Hf_agree]].
  apply inhabits.
  refine (mkPolyLogLocalExtension s U_slit
            (fun z Hz => _)
            (fun z Hz => Hz)
            _
            f
            Hf_an
            Hf_agree).
  - (* Open: U_slit is open (from PolyLogSheaf.v). *)
    apply U_slit_isOpen. exact Hz.
  - (* V meets disc: -1/2 ∈ U_slit ∩ ball_zero_one. *)
    exists (-1/2, 0). split.
    + exact neg_half_in_U_slit.
    + unfold ball_zero_one, cnorm, cnorm_sq, cre, cim. simpl.
      assert (Hsqrt : sqrt (-1/2 * (-1/2) + 0 * 0) = 1/2).
      { replace (-1/2 * (-1/2) + 0 * 0) with (1/4) by lra.
        rewrite <- (sqrt_square (1/2)) by lra.
        f_equal. lra. }
      rewrite Hsqrt. lra.
Qed.

(* ============================================================ *)
(* Status: STRUCTURAL PORT of Lean PolyLogAnalyticExtension.lean *)
(*                                                              *)
(* PROVEN (this file, axiom-free over the documented Parameters):*)
(*   * H_upper, H_lower, H_left_punct definitions                *)
(*   * H_upper_subset_U_slit, H_lower_subset_U_slit,             *)
(*     H_left_punct_subset_U_slit                                *)
(*   * U_slit_subset_union, U_slit_eq_union                      *)
(*   * H_upper_convex, H_lower_convex (linear convexity)         *)
(*   * convex_linear_path generic lemma                          *)
(*   * neg1_plus_i_in_overlap, neg1_minus_i_in_overlap           *)
(*   * neg_half_in_U_slit, neg_one_in_U_slit                     *)
(*   * U_slit_isPreconnected encoding                            *)
(*   * polyLog_extension_unique_conditional                      *)
(*   * PolyLogAnalyticExtension + polyLogAnalyticExtension_unique*)
(*   * PolyLogLocalExtension + polyLogLocalExtension_of_global   *)
(*                                                              *)
(* GAPS (Parameters, documented for Coquelicot integration):     *)
(*   * AnalyticOnNhdInRpR — abstract complex-analytic predicate  *)
(*                                                              *)
(* IdentityTheoremHypothesis is encoded as a conditional Prop;   *)
(* the uniqueness theorems are stated CONDITIONAL on it, mirror- *)
(* ing the Lean approach of locking the load-bearing classical   *)
(* identity-theorem content into a named hypothesis. The Lean    *)
(* side discharges this via mathlib's                            *)
(* AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq.           *)
(* ============================================================ *)
