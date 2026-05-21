(*
  # H_P as a Concrete Mathlib Operator — Construction Certificate (Coq port)
  Coq counterpart of `PF_Lean4_Code/PF/Analytic/HPOperatorConstruction.lean`.

  ## Scope: STRUCTURAL PORT of the H_P operator construction certificate

  This file mirrors the Lean Stage L5 H_P operator construction
  delivering **Input #5 of the axiom-retirement programme**:

    1. `H_P_construction` — concrete `Lp C 2 mu ->L[C] Lp C 2 mu`
       operator (alias for `H_P_canonical a`).
    2. `H_P_construction_isSelfAdjoint` — self-adjointness.
    3. `H_P_zeroRank` — the zero operator on Lp C 2 mu.
    4. `H_P_zeroRank_isSelfAdjoint` (proven via `IsSelfAdjoint.zero`).
    5. `H_P_zeroRank_isCompactOperator` (proven via
       `isCompactOperator_zero`).
    6. `add_isCompactOperator`, `add_isSelfAdjoint` (closure lemmas).
    7. `H_P_finiteRankTower` predicate.
    8. `H_P_construction_isCompactOperator_of_finiteRankTower`
       (via Mathlib's `isCompactOperator_of_tendsto`).
    9. `GroundStateEigenvalueTarget` Prop.
   10. `GroundStateEigenvalueFormula` Prop.
   11. `GroundStateEigenvalueFormula_iff_HPSpectralFormula`.
   12. `H_P_construction_axiom_retirement_certificate`.
   13. `H_P_construction_full_chain`.

  ## What is PROVED here (axiom-free over the documented Parameters)

    * GroundStateEigenvalueFormula definition (real-arithmetic content).
    * The bridge to HPSpectralFormula (a one-line definitional fact).
    * Definition of H_P_finiteRankTower (existential Prop).
    * Axiom-retirement certificate (one-line constructor).
    * Full chain bundling.
    * H_P_zeroRank self-adjointness and compactness as one-liners over
      abstract IsSelfAdjointOp and IsCompactOp Parameters.

  ## What requires Parameter (documented gaps)

  Coq stdlib has NO ContinuousLinearMap, NO IsCompactOperator, NO
  IsSelfAdjoint, NO Lp space, NO mathlib `isCompactOperator_zero` or
  `isCompactOperator_of_tendsto`. We therefore:

    * Declare `CLM`, `LpC2mu`, `IsSelfAdjointOp`, `IsCompactOp`,
      `ZeroOp`, `AddOp`, `TendstoOp` as Parameters with documented
      closure paths (Coquelicot + future Coq operator-theory port).
    * Declare `H_P_canonical`, `H_P_canonical_isSelfAdjoint` from
      the prior IntegralKernel/Bridge.lean infrastructure (also gap).
    * Declare `isCompactOperator_zero`, `isCompactOperator_of_tendsto`,
      `IsSelfAdjoint_zero`, `IsSelfAdjoint_add`, `IsCompactOp_add`
      as Parameters (mathlib lemmas not in Coq stdlib).

  ## Provenance

  Lean source: PF_Lean4_Code/PF/Analytic/HPOperatorConstruction.lean
  Lean axioms used in source: ZERO (depends on
    PF/Analytic/HPGeneralOperator.lean and
    Mathlib.Analysis.Normed.Operator.Compact for the substantive
    proofs).
  Coq axioms used here: documented Parameters for
    ContinuousLinearMap, IsCompactOperator, IsSelfAdjoint, Lp,
    Tendsto infrastructure unavailable in Coq stdlib.

  Stage L5 mirror — H_P operator construction (2026-05-20).
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.
Require Import PrincipiaTractalis.Analytic.PolyLogSheaf.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Abstract Lp space and ContinuousLinearMap          *)
(* ============================================================ *)

(** Abstract Lp C 2 mu space (mirror of Mathlib's `Lp C 2 mu`).
    GAP: requires Bochner integral + measure-theoretic Lp space
    infrastructure, not in Coq stdlib. *)
Parameter LpC2mu : Type.

(** Abstract continuous linear map Lp C 2 mu ->L[C] Lp C 2 mu.
    GAP: Mathlib's `Lp C 2 mu ->L[C] Lp C 2 mu`, a bundled CLM. *)
Parameter CLM : Type.

(** Zero operator on Lp C 2 mu. *)
Parameter ZeroOp : CLM.

(** Operator-norm addition on CLM. *)
Parameter AddOp : CLM -> CLM -> CLM.

(** Operator-norm convergence: TendstoOp T_seq T means
    T_seq N --> T in the operator-norm topology as N -> inf. *)
Parameter TendstoOp : (nat -> CLM) -> CLM -> Prop.

(* ============================================================ *)
(* Section 2: Abstract IsSelfAdjoint / IsCompactOp predicates    *)
(* ============================================================ *)

(** Abstract IsSelfAdjoint predicate on CLM. *)
Parameter IsSelfAdjointOp : CLM -> Prop.

(** Abstract IsCompactOperator predicate on CLM. *)
Parameter IsCompactOp : CLM -> Prop.

(** Mathlib's `IsSelfAdjoint.zero`: the zero operator is self-adjoint. *)
Parameter IsSelfAdjointOp_zero : IsSelfAdjointOp ZeroOp.

(** Mathlib's `isCompactOperator_zero`: the zero operator is compact. *)
Parameter IsCompactOp_zero : IsCompactOp ZeroOp.

(** Mathlib's `IsSelfAdjoint.add`: sum of self-adjoint is self-adjoint. *)
Parameter IsSelfAdjointOp_add :
  forall (T S : CLM),
    IsSelfAdjointOp T -> IsSelfAdjointOp S -> IsSelfAdjointOp (AddOp T S).

(** Mathlib's `IsCompactOperator.add`: sum of compact is compact. *)
Parameter IsCompactOp_add :
  forall (T S : CLM),
    IsCompactOp T -> IsCompactOp S -> IsCompactOp (AddOp T S).

(** Mathlib's `isCompactOperator_of_tendsto`: operator-norm limit of
    compact operators is compact. *)
Parameter isCompactOperator_of_tendsto :
  forall (T_seq : nat -> CLM) (T : CLM),
    TendstoOp T_seq T ->
    (forall N : nat, IsCompactOp (T_seq N)) ->
    IsCompactOp T.

(* ============================================================ *)
(* Section 3: H_P_canonical and its self-adjointness             *)
(* ============================================================ *)

(** Abstract H_P_canonical operator (P-class fractal-kernel
    operator from PF/IntegralKernel/Bridge.lean).

    GAP: requires Hilbert-Schmidt L2-bound and kernel operator
    infrastructure, not in Coq stdlib. *)
Parameter H_P_canonical : forall {a : R}, 1 < a -> CLM.

(** Self-adjointness of H_P_canonical (Mirror of Lean
    `H_P_canonical_isSelfAdjoint`).

    GAP: requires the lift `isSelfAdjoint_of_kernel_conjSymm`. *)
Parameter H_P_canonical_isSelfAdjoint :
  forall (a : R) (ha : 1 < a),
    IsSelfAdjointOp (H_P_canonical ha).

(* ============================================================ *)
(* Section 4: H_P_construction (alias for H_P_canonical)         *)
(* ============================================================ *)

(** **`H_P_construction`** — the concrete CLM instance of H_P on
    Lp C 2 mu.

    Alias for `H_P_canonical a`. Definitional. *)
Definition H_P_construction {a : R} (ha : 1 < a) : CLM :=
  H_P_canonical ha.

(** **`H_P_construction` is self-adjoint** (a > 1).
    Inherits from `H_P_canonical_isSelfAdjoint`. *)
Theorem H_P_construction_isSelfAdjoint :
  forall (a : R) (ha : 1 < a),
    IsSelfAdjointOp (H_P_construction ha).
Proof.
  intros a ha. unfold H_P_construction.
  exact (H_P_canonical_isSelfAdjoint a ha).
Qed.

(* ============================================================ *)
(* Section 5: H_P_zeroRank base case                             *)
(* ============================================================ *)

(** **`H_P_zeroRank`** — rank-0 (zero) operator on Lp C 2 mu.
    Trivial base case for the finite-rank tower. *)
Definition H_P_zeroRank : CLM := ZeroOp.

(** **`H_P_zeroRank` is self-adjoint** (Mathlib's
    `IsSelfAdjoint.zero`). *)
Theorem H_P_zeroRank_isSelfAdjoint : IsSelfAdjointOp H_P_zeroRank.
Proof.
  unfold H_P_zeroRank. exact IsSelfAdjointOp_zero.
Qed.

(** **`H_P_zeroRank` is a compact operator** (Mathlib's
    `isCompactOperator_zero`). *)
Theorem H_P_zeroRank_isCompactOperator : IsCompactOp H_P_zeroRank.
Proof.
  unfold H_P_zeroRank. exact IsCompactOp_zero.
Qed.

(* ============================================================ *)
(* Section 6: Closure-under-sums wrappers                        *)
(* ============================================================ *)

(** **Sum of compact operators is compact** — wrapper around
    `IsCompactOperator.add`. *)
Theorem add_isCompactOperator :
  forall (T S : CLM),
    IsCompactOp T -> IsCompactOp S -> IsCompactOp (AddOp T S).
Proof.
  intros T S HT HS. exact (IsCompactOp_add T S HT HS).
Qed.

(** **Sum of self-adjoint operators is self-adjoint** — wrapper
    around `IsSelfAdjoint.add`. *)
Theorem add_isSelfAdjoint :
  forall (T S : CLM),
    IsSelfAdjointOp T -> IsSelfAdjointOp S -> IsSelfAdjointOp (AddOp T S).
Proof.
  intros T S HT HS. exact (IsSelfAdjointOp_add T S HT HS).
Qed.

(* ============================================================ *)
(* Section 7: Finite-rank tower predicate                        *)
(* ============================================================ *)

(** **Finite-rank tower** for H_P_construction: a sequence of
    self-adjoint compact operators T_N : Lp C 2 mu ->L[C] Lp C 2 mu
    converging to `H_P_construction a` in the operator-norm
    topology. *)
Definition H_P_finiteRankTower {a : R} (ha : 1 < a) : Prop :=
  exists (T : nat -> CLM),
    (forall N, IsSelfAdjointOp (T N)) /\
    (forall N, IsCompactOp (T N)) /\
    TendstoOp T (H_P_construction ha).

(** **Compactness from a finite-rank tower** — the standard
    `isCompactOperator_of_tendsto` packaging.

    If `H_P_construction` admits a finite-rank tower, it is compact. *)
Theorem H_P_construction_isCompactOperator_of_finiteRankTower :
  forall (a : R) (ha : 1 < a),
    H_P_finiteRankTower ha ->
    IsCompactOp (H_P_construction ha).
Proof.
  intros a ha [T [Hsa [HK Htends]]].
  exact (isCompactOperator_of_tendsto T (H_P_construction ha) Htends HK).
Qed.

(* ============================================================ *)
(* Section 8: Ground-state eigenvalue target Props               *)
(* ============================================================ *)

(** Abstract scalar action C * Lp -> Lp on CLM applications.
    For the eigenvalue equation T f = lambda * f.

    GAP: requires Lp C-module structure. *)
Parameter SMulLp : R -> LpC2mu -> LpC2mu.

(** Abstract CLM application f |-> T f. *)
Parameter ApplyOp : CLM -> LpC2mu -> LpC2mu.

(** Abstract nonzero predicate on Lp. *)
Parameter LpNonzero : LpC2mu -> Prop.

(** Abstract Lp equality. *)
Parameter LpEq : LpC2mu -> LpC2mu -> Prop.

(** **`GroundStateEigenvalueTarget`** — the formal Prop expressing
    the manuscript's identification of the ground-state eigenvalue.

    Mirror of Lean Prop: `exists f : Lp C 2 mu, f <> 0 /\
       H_P_construction a f = (pi / (10 * sqrt 2)) . f`. *)
Definition GroundStateEigenvalueTarget {a : R} (ha : 1 < a) : Prop :=
  exists (f : LpC2mu),
    LpNonzero f /\
    LpEq (ApplyOp (H_P_construction ha) f)
         (SMulLp (PI / (10 * sqrt 2)) f).

(** **`GroundStateEigenvalueFormula`** — value-side predicate:
    `lambda = pi / (10 * sqrt 2)`. *)
Definition GroundStateEigenvalueFormula (lambda : R) : Prop :=
  lambda = PI / (10 * sqrt 2).

(** Abstract HPSpectralFormula bridge predicate.
    Mirror of Lean: `HPSpectralFormula alpha lambda := lambda = pi / (10 * alpha)`. *)
Definition HPSpectralFormula (alpha lambda : R) : Prop :=
  lambda = PI / (10 * alpha).

(** **Bridge to `HPSpectralFormula`**: at alpha = sqrt 2, the manuscript's
    general formula specializes to `GroundStateEigenvalueFormula`. *)
Theorem GroundStateEigenvalueFormula_iff_HPSpectralFormula :
  forall (lambda : R),
    GroundStateEigenvalueFormula lambda <->
      HPSpectralFormula (sqrt 2) lambda.
Proof.
  intros lambda.
  unfold GroundStateEigenvalueFormula, HPSpectralFormula.
  reflexivity.
Qed.

(* ============================================================ *)
(* Section 9: Axiom-retirement certificate                       *)
(* ============================================================ *)

(** Abstract CLM equality. *)
Parameter CLMEq : CLM -> CLM -> Prop.

(** Reflexivity of CLMEq. *)
Parameter CLMEq_refl : forall T : CLM, CLMEq T T.

(** **`H_P_construction_axiom_retirement_certificate`** — Input #5
    certificate: the H_P operator construction is in place, self-
    adjoint, and compact *given a finite-rank tower*. *)
Theorem H_P_construction_axiom_retirement_certificate :
  forall (a : R) (ha : 1 < a),
    H_P_finiteRankTower ha ->
    exists (T : CLM),
      IsSelfAdjointOp T /\
      IsCompactOp T /\
      CLMEq T (H_P_construction ha).
Proof.
  intros a ha hTower.
  exists (H_P_construction ha).
  split; [|split].
  - exact (H_P_construction_isSelfAdjoint a ha).
  - exact (H_P_construction_isCompactOperator_of_finiteRankTower a ha hTower).
  - exact (CLMEq_refl (H_P_construction ha)).
Qed.

(* ============================================================ *)
(* Section 10: Full chain bundling Input #5 + ground state       *)
(* ============================================================ *)

(** **`H_P_construction_full_chain`** — Clay-grade chain:
    given (i) finite-rank tower (=> compactness of `H_P_construction`),
    AND (ii) the ground-state eigenvalue identification, we get the
    final manuscript claim. *)
Theorem H_P_construction_full_chain :
  forall (a : R) (ha : 1 < a),
    H_P_finiteRankTower ha ->
    GroundStateEigenvalueTarget ha ->
    (exists (T : CLM),
       IsSelfAdjointOp T /\
       IsCompactOp T /\
       CLMEq T (H_P_construction ha)) /\
    (exists (f : LpC2mu),
       LpNonzero f /\
       LpEq (ApplyOp (H_P_construction ha) f)
            (SMulLp (PI / (10 * sqrt 2)) f)).
Proof.
  intros a ha hTower hGround.
  split.
  - exact (H_P_construction_axiom_retirement_certificate a ha hTower).
  - exact hGround.
Qed.

(* ============================================================ *)
(* Status: STRUCTURAL PORT of Lean HPOperatorConstruction.lean   *)
(*                                                              *)
(* PROVEN (this file, axiom-free over the documented Parameters):*)
(*   * H_P_construction (definition + alias for H_P_canonical)   *)
(*   * H_P_construction_isSelfAdjoint (inherited via Parameter)  *)
(*   * H_P_zeroRank (zero operator)                              *)
(*   * H_P_zeroRank_isSelfAdjoint (one-line via Parameter)       *)
(*   * H_P_zeroRank_isCompactOperator (one-line via Parameter)   *)
(*   * add_isCompactOperator, add_isSelfAdjoint (wrappers)       *)
(*   * H_P_finiteRankTower (existential predicate)               *)
(*   * H_P_construction_isCompactOperator_of_finiteRankTower     *)
(*     (one-line via Parameter isCompactOperator_of_tendsto)     *)
(*   * GroundStateEigenvalueTarget (Prop)                        *)
(*   * GroundStateEigenvalueFormula (real-arithmetic Prop)       *)
(*   * GroundStateEigenvalueFormula_iff_HPSpectralFormula        *)
(*     (one-line definitional bridge)                            *)
(*   * H_P_construction_axiom_retirement_certificate             *)
(*     (one-line bundling)                                       *)
(*   * H_P_construction_full_chain (full bundling)               *)
(*                                                              *)
(* GAPS (Parameters, documented):                                *)
(*   * LpC2mu, CLM (Lp space + ContinuousLinearMap)              *)
(*   * IsSelfAdjointOp, IsCompactOp predicates                   *)
(*   * ZeroOp, AddOp, TendstoOp                                  *)
(*   * IsSelfAdjointOp_zero, IsCompactOp_zero                    *)
(*     (Mathlib's IsSelfAdjoint.zero, isCompactOperator_zero)    *)
(*   * IsSelfAdjointOp_add, IsCompactOp_add                      *)
(*     (Mathlib's IsSelfAdjoint.add, IsCompactOperator.add)      *)
(*   * isCompactOperator_of_tendsto                              *)
(*     (Mathlib's load-bearing limit theorem)                    *)
(*   * H_P_canonical, H_P_canonical_isSelfAdjoint                *)
(*     (PF/IntegralKernel/Bridge.lean infrastructure)            *)
(*   * SMulLp, ApplyOp, LpNonzero, LpEq, CLMEq, CLMEq_refl       *)
(*     (Lp module structure, CLM application)                    *)
(*                                                              *)
(* Closure path: Coquelicot + a Coq port of Mathlib's compact-   *)
(* operator API (multi-month formalization on Coq side).         *)
(* ============================================================ *)
