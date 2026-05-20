(*
  # Sheaf-Theoretic Reformulation of polyLog — Grothendieck-Weil Approach
  Coq counterpart of `PF_Lean4_Code/PF/Analytic/PolyLogSheaf.lean`.

  ## Scope: BASIC DEFINITIONS + PROVEN STRUCTURAL THEOREMS

  This port covers the load-bearing structural skeleton:

    * Stage 1: `BranchCut` and `U_slit` definitions on a model
      complex plane `R*R` (since Coq 8.18 stdlib has no `C`).
    * Stage 1 theorem: `U_slit_isOpen` — the slit plane is open
      (encoded as a real-pair predicate on R*R).
    * Stage 4 theorem: `polyLogSheetIsRiemannSheet_holds` —
      structural identity that `polyLogSheet m s z = polyLog s z +
      polyLogMonodromyShift m s z` by definition (ring identity over
      a generic abelian-group target).

  ## What is NOT ported

  The Lean side's polylog sheaf framework consumes mathlib's full
  Complex / topology / sheaf infrastructure:

    * `Mathlib.Topology.Sheaves.SheafOfFunctions`
    * `Mathlib.Analysis.Complex.Basic`
    * `Mathlib.Analysis.Analytic.Basic`
    * `Complex.exp`, `Complex.log`, `Complex.continuous_re/im`

  Coq 8.18 stdlib provides NONE of these. The locally-installed
  Coquelicot (which has `C`, `Cexp`, `Cln`, etc.) is compiled
  against Coq 9.1 and is binary-incompatible with this project's
  Coq 8.18 build chain.

  ## Faithful Coq encoding via R*R model

  We model the complex plane as `R * R` (pair of reals) with the
  obvious projections `re := fst`, `im := snd`. This is faithful to
  the Lean Complex (which is `structure Complex := (re : ℝ) (im : ℝ)`)
  and lets us state and prove the OPEN-SET / CONTINUITY / IDENTITY
  content without needing complex multiplication, exp, or log.

  When Coquelicot 3.4.x (Coq 8.18-compatible) is added as a project
  dependency, the `RpR` alias below should be replaced by `C` and
  the definitions / theorems carry over identically.

  ## Provenance

  Lean source: PF_Lean4_Code/PF/Analytic/PolyLogSheaf.lean
    (lines 1-300, Stage L5 sheaf framework, 2026-05-20).
  Lean axioms used in source: ZERO.
  Coq axioms used here: ZERO.

  Stage L5 mirror — sheaf framework (2026-05-20).
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.

Open Scope R_scope.

(* ============================================================ *)
(* Model: complex plane as R * R                                 *)
(* ============================================================ *)

(** **Complex-plane model**: in this Coq 8.18 stdlib port we model
    the complex plane as `R * R`. The real and imaginary parts are
    extracted by `fst` and `snd`. *)
Definition RpR : Type := R * R.

Definition cre (z : RpR) : R := fst z.
Definition cim (z : RpR) : R := snd z.

(** Equality on RpR is pair equality (componentwise). *)
Lemma RpR_eq : forall z w : RpR, cre z = cre w -> cim z = cim w -> z = w.
Proof.
  intros [zr zi] [wr wi] H1 H2.
  unfold cre, cim in H1, H2. simpl in *.
  subst. reflexivity.
Qed.

(* ============================================================ *)
(* Stage 1: The slit plane as a subset of RpR                    *)
(* ============================================================ *)

(** **The principal branch cut**: `BranchCut := {z : im z = 0 ∧
    1 ≤ re z}`. polyLog has its standard branch cut along this ray. *)
Definition BranchCut : RpR -> Prop :=
  fun z => cim z = 0 /\ 1 <= cre z.

(** **Origin** {0} as a singleton subset of `RpR`. *)
Definition AtOrigin : RpR -> Prop :=
  fun z => z = (0, 0).

(** **The slit plane**: `U_slit := RpR \ (BranchCut ∪ {0})`. The
    open set on which polyLog admits a single-valued (principal-
    branch) representation. *)
Definition U_slit : RpR -> Prop :=
  fun z => ~ (BranchCut z \/ AtOrigin z).

(* ============================================================ *)
(* Stage 1 theorem: U_slit is "open"                             *)
(* ============================================================ *)

(** **`U_slit` is open** — encoded as: every `z ∈ U_slit` admits
    a small ball (epsilon-neighborhood, in the sup-metric on R*R)
    contained in `U_slit`.

    This is the elementary content of the Lean theorem
    `U_slit_isOpen : IsOpen U_slit`. The Lean proof uses mathlib's
    `IsClosed.union`, `isClosed_eq`, `Complex.continuous_im/re`;
    here we give the direct epsilon-delta version, which captures
    the same mathematical fact without needing a topology library.

    Statement: for any z ∈ U_slit, ∃ε > 0 such that any w with
    |re w - re z| < ε AND |im w - im z| < ε also lies in U_slit.

    Proof: split on (a) z not on cut (then either cim z ≠ 0 or
    cre z < 1; small ε keeps you off the cut), (b) z ≠ 0 (then
    |z| > 0; small ε keeps you off origin). Take ε = min of the
    obstructive distances. *)
Theorem U_slit_isOpen :
  forall z : RpR, U_slit z ->
    exists eps : R, 0 < eps /\
      forall w : RpR,
        Rabs (cre w - cre z) < eps -> Rabs (cim w - cim z) < eps ->
        U_slit w.
Proof.
  intros z Hz.
  unfold U_slit in *.
  (* Hz: ~ (BranchCut z \/ AtOrigin z), so both fail. *)
  assert (HnotBC : ~ BranchCut z) by (intros HBC; apply Hz; left; exact HBC).
  assert (HnotO : ~ AtOrigin z) by (intros HAO; apply Hz; right; exact HAO).
  (* The cut requires cim z = 0 AND 1 <= cre z. So z is off-cut iff
     cim z <> 0 OR cre z < 1. *)
  (* The origin is the single point (0,0). z is off-origin iff
     cre z <> 0 OR cim z <> 0. *)
  unfold BranchCut, AtOrigin in *.
  unfold cre, cim in *. destruct z as [zr zi]. simpl in *.
  (* Choose eps small enough to:
     (a) preserve being off the cut, and
     (b) preserve being off the origin.
     We give a uniform conservative choice. *)
  (* Case on whether zi = 0. *)
  destruct (Req_dec zi 0) as [Hzi | Hzi].
  - (* zi = 0. Then since ~BranchCut z, we have ~(1 <= zr), i.e. zr < 1.
       And since ~AtOrigin z, we have zr <> 0. *)
    assert (Hzr_lt_1 : zr < 1).
    { destruct (Rlt_dec zr 1) as [H|H]; [exact H|].
      exfalso. apply HnotBC. split; [exact Hzi | lra]. }
    assert (Hzr_ne_0 : zr <> 0).
    { intros Hzr_eq. apply HnotO. subst zr zi. reflexivity. }
    (* Choose eps = (1 - zr) / 2 if zr > 0, or = |zr|/2 if zr < 0.
       Take min((1 - zr)/2, |zr|/2). *)
    set (eps := Rmin ((1 - zr)/2) (Rabs zr / 2)).
    exists eps.
    assert (Heps_pos : 0 < eps).
    { unfold eps. apply Rmin_pos; [lra|].
      apply Rmult_lt_0_compat; [apply Rabs_pos_lt; exact Hzr_ne_0 | lra]. }
    split; [exact Heps_pos|].
    intros [wr wi] Hwr Hwi. unfold cre, cim in *; simpl in *.
    intros [HBC | HAO].
    + (* w on cut: wi = 0 and 1 <= wr *)
      destruct HBC as [Hwi0 Hwr1].
      (* But |wr - zr| < eps <= (1 - zr)/2, so wr < zr + (1-zr)/2 = (1+zr)/2 < 1 *)
      assert (Heps1 : eps <= (1 - zr)/2) by apply Rmin_l.
      assert (Hwr_lt_1 : wr < 1).
      { apply Rabs_def2 in Hwr. destruct Hwr. lra. }
      lra.
    + (* w = (0,0): wr = 0, wi = 0 *)
      injection HAO; intros Hwi0 Hwr0.
      (* But |wr - zr| < eps <= |zr|/2, so wr is close to zr, hence wr ≠ 0
         unless we can also bound. We use wr = 0 gives |zr| < eps <= |zr|/2,
         contradiction. *)
      assert (Heps2 : eps <= Rabs zr / 2) by apply Rmin_r.
      subst wr.
      replace (0 - zr) with (- zr) in Hwr by lra.
      rewrite Rabs_Ropp in Hwr.
      assert (Hpos : 0 < Rabs zr) by (apply Rabs_pos_lt; exact Hzr_ne_0).
      lra.
  - (* zi <> 0. Off-cut is automatic since cim z ≠ 0.
       Off-origin is automatic since zi ≠ 0. *)
    set (eps := Rabs zi / 2).
    assert (Heps_pos : 0 < eps).
    { unfold eps. apply Rmult_lt_0_compat;
      [apply Rabs_pos_lt; exact Hzi | lra]. }
    exists eps; split; [exact Heps_pos|].
    intros [wr wi] Hwr Hwi. unfold cre, cim in *; simpl in *.
    intros [HBC | HAO].
    + (* w on cut: wi = 0 and 1 <= wr. But |wi - zi| < eps = |zi|/2,
         and wi = 0 means |zi| < |zi|/2, contradiction. *)
      destruct HBC as [Hwi0 _].
      subst wi.
      replace (0 - zi) with (- zi) in Hwi by lra.
      rewrite Rabs_Ropp in Hwi.
      assert (Hpos : 0 < Rabs zi) by (apply Rabs_pos_lt; exact Hzi).
      unfold eps in Hwi. lra.
    + (* w = (0,0): wi = 0. Same contradiction as above. *)
      injection HAO; intros Hwi0 Hwr0.
      subst wi.
      replace (0 - zi) with (- zi) in Hwi by lra.
      rewrite Rabs_Ropp in Hwi.
      assert (Hpos : 0 < Rabs zi) by (apply Rabs_pos_lt; exact Hzi).
      unfold eps in Hwi. lra.
Qed.

(* ============================================================ *)
(* Stage 4 theorem: polyLogSheet structural identity             *)
(*                                                              *)
(* The Lean theorem `polyLogSheetIsRiemannSheet_holds` reduces   *)
(* by `unfold polyLogSheet; ring` — a pure ring identity over a  *)
(* generic complex-valued algebra. We mirror it abstractly:      *)
(* for any abelian-group-valued functions, the sheet-shift       *)
(* identity holds DEFINITIONALLY.                                *)
(* ============================================================ *)

(** **Abstract polyLog / polyLogSheet / polyLogMonodromyShift**.

    In the Lean source:
      `polyLogMonodromyShift m s z := 2πi·m·(log z)^(s-1) / Γ(s)`
      `polyLogSheet m s z := polyLog s z + polyLogMonodromyShift m s z`

    Here we abstract over the underlying target type and the three
    functions; the IDENTITY `polyLogSheet m s z = polyLog s z +
    polyLogMonodromyShift m s z` then holds DEFINITIONALLY (it is
    the definition of polyLogSheet), independent of the choice of
    Complex / polyLog encoding. *)

Section AbstractSheet.

  (** Abstract over: integer sheet index, complex parameter `s`,
      complex evaluation point `z`, and a target (e.g. C). *)
  Variable Target : Type.
  Variable PLAdd : Target -> Target -> Target.
  Variable polyLog : RpR -> RpR -> Target.   (* s, z -> Target *)
  Variable polyLogMonodromyShift : Z -> RpR -> RpR -> Target.

  Definition polyLogSheet (m : Z) (s z : RpR) : Target :=
    PLAdd (polyLog s z) (polyLogMonodromyShift m s z).

  (** **The Riemann-sheet identity holds definitionally**.

      Mirrors Lean `polyLogSheetIsRiemannSheet_holds`:
        polyLogSheet m s z = polyLog s z + polyLogMonodromyShift m s z

      The Lean proof is `unfold polyLogSheet; ring`. Ours is by
      `reflexivity` since `polyLogSheet` is *defined* as the sum. *)
  Theorem polyLogSheetIsRiemannSheet_holds :
    forall (m : Z) (s z : RpR),
      polyLogSheet m s z = PLAdd (polyLog s z) (polyLogMonodromyShift m s z).
  Proof. intros. reflexivity. Qed.

End AbstractSheet.

(* ============================================================ *)
(* Status: PROVEN content of Lean PolyLogSheaf.lean              *)
(*                                                              *)
(* This Coq mirror covers the two PROVEN theorems from the       *)
(* Lean Stage L5 sheaf framework:                                *)
(*   1. U_slit_isOpen — given here in elementary ε-δ form on     *)
(*      the R*R model.                                          *)
(*   2. polyLogSheetIsRiemannSheet_holds — given here as an      *)
(*      abstract definitional identity over any (Target, PLAdd)  *)
(*      pair.                                                    *)
(*                                                              *)
(* The Lean file additionally STATES (as `def ... : Prop`)       *)
(* several future-work propositions:                             *)
(*   * z_book_mem_U_slit_target                                   *)
(*   * IsPolyLogSheafSection (s : C) (f : C → C) : Prop          *)
(*   * PolyLogSheafSectionExists / Unique                        *)
(*   * PolyLogHankelRealization                                  *)
(*   * PolyLogSheetIsRiemannSheet (which IS proven as a Prop     *)
(*     instance — the proof is the theorem above)                *)
(*   * PolyLogSheafCocycle                                       *)
(*   * PolyLogSheafSection_at_z_book                             *)
(*                                                              *)
(* These are STATEMENTS (Lean `def P : Prop`), not proven        *)
(* theorems on the Lean side either. Porting them to Coq         *)
(* requires the Complex stack and so is deferred until           *)
(* Coquelicot-8.18 compatibility is restored.                    *)
(*                                                              *)
(* This file is axiom-free (uses no Parameter, no Admitted).     *)
(* ============================================================ *)
