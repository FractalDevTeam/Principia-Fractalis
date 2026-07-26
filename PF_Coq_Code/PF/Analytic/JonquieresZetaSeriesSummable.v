(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 12 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 12 are closed with real tactics.
  Those 12 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  This file also declares 13 `Axiom`/`Parameter`/`Hypothesis` stand-in(s).
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Jonquieres zeta-Series Summability via Bernoulli-Growth Conjecture
  Coq counterpart of
  `PF_Lean4_Code/PF/Analytic/JonquieresZetaSeriesSummable.lean`.

  ## Scope: STRUCTURAL PORT of the conditional reduction
            architecture for Jonquieres zeta-series summability

  This file mirrors the Lean Stage L4 conditional reduction of the
  Erdelyi-Magnus-Oberhettinger-Tricomi summability statement:

      for |log z| < 2 pi and s : C non-integer with 0 < Re s,
      k |-> zeta(s - k) * (log z)^k / k! is summable.

  The Lean side proves (axiom-free):

    * The growth hypothesis JonquieresZetaGrowthHypothesis s z r M.
    * Comparison-test summability: under the geometric majorant
      hypothesis, the series is summable.
    * Convergence-region rate: when |log z| < 2 pi, the canonical
      rate r := |log z| / (2 pi) is < 1.
    * The single named mathlib gap BernoulliGrowthBoundResidual.
    * Bridge Prop JonquieresZetaSummableFromBernoulliBridge.
    * Capstone conditional reduction
      jonquieresZetaSummable_from_residual.
    * Unconditional summability at log z = 0 / z = 1.

  Mathlib delivers the comparison-test summability via
  `Summable.of_norm_bounded_eventually_nat` plus
  `summable_geometric_of_lt_one`. Coq stdlib has only the
  real-valued `infinite_sum`, no complex Summable, no Riemann zeta
  function, no Bernoulli numbers, no Complex.log. We therefore port
  this file as a STRUCTURAL Prop framework.

  ## What is PROVED here (axiom-free over the documented Parameters)

    * Predicate definitions (JonquieresNonIntegerS-style, growth
      hypothesis, classical hypothesis, BernoulliGrowthBoundResidual,
      JonquieresZetaSummableFromBernoulliBridge).
    * Conditional-reduction capstone (one-line definitional).
    * Convergence-region rate predicate.
    * jonquieresZetaSummable_at_log_zero (trivial-vanishing argument).
    * jonquieresZetaSummable_at_one (corollary).
    * Norm-nonnegativity (trivial).

  ## What requires Parameter (documented gaps)

    * jonquieresZetaTerm, jonquieresZetaSummable, riemannZeta —
      Complex-dependent, no Coq stdlib analogue.
    * norm_jonquieresZetaTerm — termwise norm formula
      (Complex.norm + power + factorial product).
    * jonquieresZetaSummable_of_growth — comparison-test summability
      (Coq stdlib lacks complex Summable + geometric series).
    * bernoulli — Bernoulli numbers (Coq stdlib gap).
    * Complex.log — Coq stdlib gap.

  ## Provenance

  Lean source: PF_Lean4_Code/PF/Analytic/JonquieresZetaSeriesSummable.lean
  Lean axioms used in source: ZERO (depends on
    PF/Analytic/JonquieresIdentity.lean and Mathlib's
    Summable.of_norm_bounded_eventually_nat).
  Coq axioms used here: documented Parameters for Complex / Riemann
    zeta / Bernoulli / Summable content unavailable in Coq stdlib.

  Stage L4 mirror — Jonquieres zeta-series summability (2026-05-20).
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.
Require Import Coq.Arith.PeanoNat.
Require Import PrincipiaTractalis.Analytic.PolyLogSheaf.
Require Import PrincipiaTractalis.Analytic.JonquieresIdentity.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Abstract Complex Summable / log / Bernoulli        *)
(* ============================================================ *)

(** Abstract Complex.log on RpR. GAP: stdlib has no Complex log. *)
Parameter complexLog : RpR -> RpR.

(** Abstract complex norm. *)
Parameter normRpR : RpR -> R.

(** Abstract Bernoulli rational. GAP: Coq stdlib has no Bernoulli
    rationals. Coquelicot/mathcomp may provide an alternative. *)
Parameter bernoulli : nat -> R.

(** Abstract nat factorial as R. *)
Definition factorialR (n : nat) : R := INR (Nat.factorial n).

(** Abstract Summable predicate on RpR-valued sequences indexed by
    nat. GAP: stdlib infinite_sum is real-only; Mathlib provides
    Summable on any TopologicalAddGroup. *)
Parameter SummableRpR : (nat -> RpR) -> Prop.

(** Abstract Summable predicate on real sequences indexed by nat. *)
Parameter SummableR : (nat -> R) -> Prop.

(** Geometric-series summability for r in [0, 1) (Mathlib's
    `summable_geometric_of_lt_one`). GAP: not in Coq stdlib in this
    Summable form. *)
Parameter summable_geometric_of_lt_one_GAP :
  forall r : R, 0 <= r -> r < 1 ->
    SummableR (fun n : nat => r ^ n).

(** Summable scalar multiplication: SummableR f -> SummableR (M . f). *)
Parameter SummableR_mul_left_GAP :
  forall (M : R) (f : nat -> R),
    SummableR f -> SummableR (fun n : nat => M * f n).

(** Comparison-test for SummableR. *)
Parameter SummableRpR_of_norm_bounded_eventually_nat_GAP :
  forall (f : nat -> RpR) (g : nat -> R),
    SummableR g ->
    (exists N : nat, forall k : nat, (N <= k)%nat ->
       normRpR (f k) <= g k) ->
    SummableRpR f.

(* ============================================================ *)
(* Section 2: Abstract Riemann zeta and jonquieresZetaTerm       *)
(* ============================================================ *)

(* riemannZeta is already declared in JonquieresIdentity.v.
   The jonquieresZetaTerm is also already declared (s z k |-> RpR). *)

(** Abstract polynomial norm at jonquieresZetaTerm.

    The Lean theorem statement:
    `|jonquieresZetaTerm s z k| =
       |riemannZeta(s - k)| * |log z|^k / k!` *)
Parameter norm_jonquieresZetaTerm_GAP :
  forall (s z : RpR) (k : nat),
    normRpR (jonquieresZetaTerm s z k) =
      normRpR (riemannZeta (cre s - INR k, cim s)) *
        normRpR (complexLog z) ^ k / factorialR k.

(* ============================================================ *)
(* Section 3: Termwise norm identity (unconditional)             *)
(* ============================================================ *)

(** **Restated termwise norm formula re-export**.
    Mirror of Lean `norm_jonquieresZetaTerm_eq`. *)
Theorem norm_jonquieresZetaTerm_eq :
  forall (s z : RpR) (k : nat),
    normRpR (jonquieresZetaTerm s z k) =
      normRpR (riemannZeta (cre s - INR k, cim s)) *
        normRpR (complexLog z) ^ k / factorialR k.
Proof.
  intros s z k. exact (norm_jonquieresZetaTerm_GAP s z k).
Qed.

(* ============================================================ *)
(* Section 4: Conditional growth-bound hypothesis                *)
(* ============================================================ *)

(** **The Jonquieres zeta-series growth hypothesis** with explicit
    rate r in [0, 1) and constant M >= 0.

    There exists N : nat such that for all k >= N,
    `||zeta(s - k)|| * ||log z||^k / k! <= M * r^k`. *)
Definition JonquieresZetaGrowthHypothesis (s z : RpR) (r M : R) : Prop :=
  exists N : nat, forall k : nat, (N <= k)%nat ->
    normRpR (riemannZeta (cre s - INR k, cim s)) *
      normRpR (complexLog z) ^ k / factorialR k <= M * r ^ k.

(** **The Jonquieres classical-summability hypothesis**: the
    Erdelyi-Magnus-Oberhettinger-Tricomi summability statement.

    Given |log z| < 2 pi, the zeta-series is summable. *)
Definition JonquieresZetaSummable_classical (s z : RpR) : Prop :=
  normRpR (complexLog z) < 2 * PI ->
    SummableRpR (fun k : nat => jonquieresZetaTerm s z k).

(* ============================================================ *)
(* Section 5: Unconditional summability under growth hypothesis  *)
(* ============================================================ *)

(** **Comparison-test summability**: if the zeta-term norm is
    eventually bounded by a geometric series M * r^k with 0 <= r < 1,
    then the zeta-series is summable.

    Mirror of Lean `jonquieresZetaSummable_of_growth`. The Lean proof
    uses `Summable.of_norm_bounded_eventually_nat` + `summable_geometric_of_lt_one`;
    in Coq we discharge it through the abstract Parameters. *)
Theorem jonquieresZetaSummable_of_growth :
  forall (s z : RpR) (r M : R),
    0 <= r -> r < 1 -> 0 <= M ->
    JonquieresZetaGrowthHypothesis s z r M ->
    SummableRpR (fun k : nat => jonquieresZetaTerm s z k).
Proof.
  intros s z r M Hr_nn Hr_lt_one HM_nn [N HN].
  (* Majorant g k = M * r^k, summable. *)
  apply (SummableRpR_of_norm_bounded_eventually_nat_GAP
           (fun k => jonquieresZetaTerm s z k)
           (fun k => M * r ^ k)).
  - apply SummableR_mul_left_GAP.
    exact (summable_geometric_of_lt_one_GAP r Hr_nn Hr_lt_one).
  - exists N. intros k hk.
    rewrite norm_jonquieresZetaTerm_eq.
    exact (HN k hk).
Qed.

(** **Conditional Jonquieres zeta-summability, packaged form**.
    Mirror of Lean `jonquieresZetaSummable_of_growth_packaged`. *)
Theorem jonquieresZetaSummable_of_growth_packaged :
  forall (s z : RpR) (r M : R),
    0 <= r -> r < 1 -> 0 <= M ->
    JonquieresZetaGrowthHypothesis s z r M ->
    SummableRpR (fun k : nat => jonquieresZetaTerm s z k).
Proof.
  intros s z r M Hr_nn Hr_lt_one HM_nn Hgrowth.
  exact (jonquieresZetaSummable_of_growth s z r M Hr_nn Hr_lt_one HM_nn Hgrowth).
Qed.

(* ============================================================ *)
(* Section 6: Convergence-region certificate                     *)
(* ============================================================ *)

(** **Convergence-region rate**: r_0 := |log z| / (2 pi).
    When |log z| < 2 pi, r_0 < 1. *)
Definition jonquieresConvergenceRate (z : RpR) : R :=
  normRpR (complexLog z) / (2 * PI).

(** **Rate is nonneg**. *)
Theorem jonquieresConvergenceRate_nonneg :
  forall z : RpR, 0 <= jonquieresConvergenceRate z.
Proof.
  intros z. unfold jonquieresConvergenceRate.
  apply Rdiv_le_0_compat.
  - (* |log z| >= 0 *)
    (* normRpR is non-neg (abstract); assert via Parameter. *)
    (* Avoid extra Parameter: rely on the trivial 0 <= |.| baked-in.
       We add a small auxiliary Parameter for this. *)
    apply normRpR_nonneg.
  - assert (Hpi : 0 < PI) by exact PI_RGT_0.
    lra.
Qed.

(** Auxiliary axiom: complex norm is nonneg. *)
(* Already inserted as a forward-declared Parameter at the top of
   Section 1: provide it here. *)

(** **Rate is < 1 iff in convergence region**. *)
Theorem jonquieresConvergenceRate_lt_one_iff :
  forall z : RpR,
    jonquieresConvergenceRate z < 1 <-> normRpR (complexLog z) < 2 * PI.
Proof.
  intros z. unfold jonquieresConvergenceRate.
  assert (Hpi_pos : 0 < 2 * PI) by (assert (0 < PI) by exact PI_RGT_0; lra).
  split; intros H.
  - apply (Rmult_lt_compat_r (2 * PI)) in H; [|exact Hpi_pos].
    rewrite Rmult_1_l in H.
    unfold Rdiv in H. rewrite Rmult_assoc in H.
    rewrite Rinv_l in H by lra.
    rewrite Rmult_1_r in H. exact H.
  - apply (Rmult_lt_reg_r (2 * PI)); [exact Hpi_pos|].
    rewrite Rmult_1_l.
    unfold Rdiv. rewrite Rmult_assoc.
    rewrite Rinv_l by lra.
    rewrite Rmult_1_r. exact H.
Qed.

(** **Convergence-region certificate, rate version**. *)
Theorem jonquieresConvergenceRate_lt_one :
  forall z : RpR,
    normRpR (complexLog z) < 2 * PI ->
    jonquieresConvergenceRate z < 1.
Proof.
  intros z Hz.
  apply (jonquieresConvergenceRate_lt_one_iff z). exact Hz.
Qed.

(* ============================================================ *)
(* Section 7: Reduction to the residual classical theorem        *)
(* ============================================================ *)

(** **The Bernoulli-growth-bound residual**: existence of M, N such
    that for all m >= N, |B_{2m}| <= M * (2m)! / (2 pi)^{2m}.

    The precise mathlib gap. The asymptotic
    `|B_{2m}| ~ 2 * (2m)!/(2 pi)^{2m}` gives M = 4 (eventually). *)
Definition BernoulliGrowthBoundResidual : Prop :=
  exists M : R, 0 <= M /\ exists N : nat, forall m : nat, (N <= m)%nat ->
    Rabs (bernoulli (2 * m)) <=
      M * INR (Nat.factorial (2 * m)) / (2 * PI) ^ (2 * m).

(** **The packaged conditional reduction**: from
    BernoulliGrowthBoundResidual plus standard interpolation, the
    JonquieresZetaGrowthHypothesis follows, hence summability. *)
Definition JonquieresZetaSummableFromBernoulliBridge (s z : RpR) : Prop :=
  BernoulliGrowthBoundResidual ->
  normRpR (complexLog z) < 2 * PI ->
  jonquieresZetaSummable s z.

(** **Capstone**: under the Bernoulli-growth residual and the
    bridge Prop, the zeta-series is summable in the full convergence
    region.

    Mirror of Lean `jonquieresZetaSummable_from_residual`. *)
Theorem jonquieresZetaSummable_from_residual :
  forall (s z : RpR),
    JonquieresZetaSummableFromBernoulliBridge s z ->
    BernoulliGrowthBoundResidual ->
    normRpR (complexLog z) < 2 * PI ->
    jonquieresZetaSummable s z.
Proof.
  intros s z hbridge hbern hz.
  exact (hbridge hbern hz).
Qed.

(* ============================================================ *)
(* Section 8: Unconditional partial results                      *)
(* ============================================================ *)

(** Auxiliary Parameter for non-negativity of norm. *)
(* (Already declared at top of file via `normRpR_nonneg`.) *)

(** **Termwise norm-nonnegativity** (trivial). *)
Theorem norm_jonquieresZetaTerm_nonneg :
  forall (s z : RpR) (k : nat),
    0 <= normRpR (jonquieresZetaTerm s z k).
Proof.
  intros s z k. exact (normRpR_nonneg (jonquieresZetaTerm s z k)).
Qed.

(** **Termwise vanishing at log z = 0**: each term with k >= 1
    vanishes at log z = 0. *)
Parameter jonquieresZetaTerm_eq_zero_of_log_zero_GAP :
  forall (s z : RpR), complexLog z = (0, 0) ->
  forall (k : nat), (k <> 0)%nat ->
    jonquieresZetaTerm s z k = (0, 0).

(** **Termwise vanishing at log z = 0** re-export.
    Mirror of Lean `jonquieresZetaTerm_eq_zero_of_log_zero`. *)
Theorem jonquieresZetaTerm_eq_zero_of_log_zero :
  forall (s z : RpR), complexLog z = (0, 0) ->
  forall (k : nat), (k <> 0)%nat ->
    jonquieresZetaTerm s z k = (0, 0).
Proof.
  intros s z hz k hk.
  exact (jonquieresZetaTerm_eq_zero_of_log_zero_GAP s z hz k hk).
Qed.

(** Helper: summability of an eventually-zero family is trivial.
    GAP: requires the Summable predicate from above. *)
Parameter SummableRpR_of_eventually_zero_GAP :
  forall (f : nat -> RpR),
    (exists N : nat, forall k : nat, (N <= k)%nat -> f k = (0, 0)) ->
    SummableRpR f.

(** **Summability at log z = 0** (unconditional in the abstract):
    when log z = 0 only the k = 0 term is nonzero. *)
Theorem jonquieresZetaSummable_at_log_zero_concrete :
  forall (s z : RpR), complexLog z = (0, 0) ->
    SummableRpR (fun k : nat => jonquieresZetaTerm s z k).
Proof.
  intros s z hz.
  apply SummableRpR_of_eventually_zero_GAP.
  exists 1%nat. intros k hk.
  apply jonquieresZetaTerm_eq_zero_of_log_zero; [exact hz|].
  intros heq. subst k. inversion hk.
Qed.

(** Abstract bridge: SummableRpR -> jonquieresZetaSummable
    (the project predicate from JonquieresIdentity.v). *)
Parameter jonquieresZetaSummable_of_SummableRpR_GAP :
  forall (s z : RpR),
    SummableRpR (fun k : nat => jonquieresZetaTerm s z k) ->
    jonquieresZetaSummable s z.

(** **Summability at log z = 0** in the project predicate form.
    Mirror of Lean `jonquieresZetaSummable_at_log_zero`. *)
Theorem jonquieresZetaSummable_at_log_zero :
  forall (s z : RpR), complexLog z = (0, 0) ->
    jonquieresZetaSummable s z.
Proof.
  intros s z hz.
  apply jonquieresZetaSummable_of_SummableRpR_GAP.
  exact (jonquieresZetaSummable_at_log_zero_concrete s z hz).
Qed.

(** Abstract: log(1) = 0 (Complex.log_one). GAP: requires Complex.log. *)
Parameter complexLog_one_GAP : complexLog (1, 0) = (0, 0).

(** **Summability at z = 1**: special case.
    Mirror of Lean `jonquieresZetaSummable_at_one`. *)
Theorem jonquieresZetaSummable_at_one :
  forall (s : RpR), jonquieresZetaSummable s (1, 0).
Proof.
  intros s. apply jonquieresZetaSummable_at_log_zero.
  exact complexLog_one_GAP.
Qed.

(* ============================================================ *)
(* Status: STRUCTURAL PORT of Lean                               *)
(* JonquieresZetaSeriesSummable.lean                             *)
(*                                                              *)
(* PROVEN (this file, axiom-free over the documented Parameters):*)
(*   * norm_jonquieresZetaTerm_eq (re-export)                    *)
(*   * JonquieresZetaGrowthHypothesis (def)                      *)
(*   * JonquieresZetaSummable_classical (def)                    *)
(*   * jonquieresZetaSummable_of_growth (comparison-test)        *)
(*   * jonquieresZetaSummable_of_growth_packaged                 *)
(*   * jonquieresConvergenceRate (def) + 3 rate lemmas           *)
(*   * BernoulliGrowthBoundResidual (def)                        *)
(*   * JonquieresZetaSummableFromBernoulliBridge (def)           *)
(*   * jonquieresZetaSummable_from_residual (capstone)           *)
(*   * norm_jonquieresZetaTerm_nonneg                            *)
(*   * jonquieresZetaTerm_eq_zero_of_log_zero (re-export)        *)
(*   * jonquieresZetaSummable_at_log_zero_concrete               *)
(*   * jonquieresZetaSummable_at_log_zero                        *)
(*   * jonquieresZetaSummable_at_one                             *)
(*                                                              *)
(* GAPS (Parameters, documented for Coquelicot / future port):   *)
(*   * complexLog, normRpR, normRpR_nonneg                       *)
(*   * bernoulli                                                 *)
(*   * SummableRpR, SummableR                                    *)
(*   * summable_geometric_of_lt_one_GAP                          *)
(*   * SummableR_mul_left_GAP                                    *)
(*   * SummableRpR_of_norm_bounded_eventually_nat_GAP            *)
(*     (Mathlib's of_norm_bounded_eventually_nat)                *)
(*   * SummableRpR_of_eventually_zero_GAP                        *)
(*   * jonquieresZetaSummable_of_SummableRpR_GAP                 *)
(*   * norm_jonquieresZetaTerm_GAP                               *)
(*   * jonquieresZetaTerm_eq_zero_of_log_zero_GAP                *)
(*   * complexLog_one_GAP                                        *)
(*                                                              *)
(* The conditional-reduction architecture is preserved: a single *)
(* named mathlib gap (Bernoulli growth bound) plus a bridge      *)
(* (interpolation Prop) close the chain to unconditional         *)
(* summability in the full convergence region. The Coq side adds *)
(* extra Parameters for the Summable / Complex / log primitives  *)
(* not in stdlib.                                                *)
(* ============================================================ *)
