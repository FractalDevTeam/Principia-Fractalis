(*
  PF_Real/MatrixTraceFaithful.v

  REAL PROOF (not a shape mirror). Level-k trace faithfulness:

      \tr (M *m M^T) == 0   <->   M == 0

  over a real domain. This is the Rocq/mathcomp counterpart of the Lean
  theorem `normalized_matrix_trace_star_mul_self_eq_zero_iff`
  (PF_Lean4_Code/PF/SubstrateUHFTraceIsFaithful.lean), which is the
  foundation stone of the r102-r113 UHF faithfulness arc.

  Verified: `Print Assumptions trace_mulmx_tr_eq0` reports
  "Closed under the global context" (no axioms).

  Scope: finite-dimensional. The completion-tier results of the Lean arc
  are NOT covered here; Rocq/mathcomp has no C*-algebra theory.
*)
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma trace_mulmx_tr_eq_sum (F : numDomainType) (m n : nat)
    (M : 'M[F]_(m,n)) :
  \tr (M *m M^T) = \sum_i \sum_j (M i j) ^+ 2.
Proof.
rewrite /mxtrace; apply: eq_bigr => i _.
rewrite mxE; apply: eq_bigr => j _; by rewrite mxE -expr2.
Qed.

Lemma trace_mulmx_tr_eq0 (F : realDomainType) (m n : nat) (M : 'M[F]_(m,n)) :
  (\tr (M *m M^T) == 0) = (M == 0).
Proof.
rewrite trace_mulmx_tr_eq_sum.
apply/idP/idP => [H|/eqP ->]; last first.
  rewrite big1 ?eqxx // => i _; rewrite big1 // => j _.
  by rewrite mxE expr0n.
apply/eqP/matrixP => i j; rewrite mxE.
move: H; rewrite psumr_eq0; last first.
  by move=> i0 _; apply: sumr_ge0 => j0 _; exact: sqr_ge0.
move/allP => /(_ i (mem_index_enum i)); rewrite implyTb.
rewrite psumr_eq0; last by move=> j0 _; exact: sqr_ge0.
move/allP => /(_ j (mem_index_enum j)); rewrite implyTb sqrf_eq0.
by move/eqP.
Qed.
