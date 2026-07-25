(*
  PF_Real/MatrixTracialUnique.v

  REAL PROOF (not a shape mirror). Finite-dimensional uniqueness of the
  normalized matrix trace:

      phi additive + homogeneous + tracial + unital  ->  phi M = \tr M / n

  on 'M[F]_n.+1 over a field F. No positivity is assumed; the argument uses
  only linearity, the trace property phi (A *m B) = phi (B *m A), and
  unitality -- exactly as in the Lean counterpart.

  This is the Rocq/mathcomp counterpart of the Lean theorem
  `matrix_tracial_state_unique` (PF_Lean4_Code/PF/SubstrateTraceUniqueness.lean,
  r113 §1), the finite-dimensional keystone of the Glimm 3^oo unique-trace arc.

  Proof route (identical to the Lean one):
    - phi (delta_mx i j) = 0 for i != j    (off-diagonal units are commutators)
    - phi (delta_mx i i) = phi (delta_mx j j) for all i, j  (cyclic invariance)
    - M = \sum_i \sum_j M i j *: delta_mx i j  gives phi M = \tr M * d
    - unitality on 1%:M = \sum_i delta_mx i i pins d = (n.+1%:R)^-1.

  Verified: `Print Assumptions matrix_tracial_functional_unique` reports
  "Closed under the global context" (no axioms).

  Scope: finite-dimensional ONLY. The density/completion lift of the Lean arc
  (`tracialState_coe_level`, `substrate_UHF_trace_unique`) is NOT covered here;
  Rocq/mathcomp has no C*-algebra or UHF completion theory.

  Note on characteristic: the hypotheses are contradictory whenever
  n.+1%:R = 0 in F (unitality forces n.+1%:R * d = 1), so the theorem is
  stated unconditionally and the nonzero-characteristic fact is DERIVED, not
  assumed. The non-vacuity lemma at the end does need (n.+1%:R != 0), since
  the normalized trace only exists when n.+1 is invertible in F.
*)
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section TracialUnique.

Variable F : fieldType.
Variable n : nat.

Local Notation MF := 'M[F]_n.+1.

Variable phi : MF -> F.

Hypothesis phi_add  : forall A B : MF, phi (A + B) = phi A + phi B.
Hypothesis phi_smul : forall (c : F) (A : MF), phi (c *: A) = c * phi A.
Hypothesis phi_tr   : forall A B : MF, phi (A *m B) = phi (B *m A).
Hypothesis phi_one  : phi 1%:M = 1.

(* ------------------------------------------------------------------ *)
(* Step 0: phi 0 = 0 and phi commutes with finite sums.                *)
(* ------------------------------------------------------------------ *)

Lemma phi_zero : phi 0 = 0.
Proof. by move: (phi_smul 0 0); rewrite scale0r mul0r. Qed.

Lemma phi_sum (I : Type) (r : seq I) (P : pred I) (G : I -> MF) :
  phi (\sum_(i <- r | P i) G i) = \sum_(i <- r | P i) phi (G i).
Proof. exact: (big_morph phi phi_add phi_zero). Qed.

(* ------------------------------------------------------------------ *)
(* Step 1: off-diagonal matrix units are killed.                       *)
(*   E_ij = E_ij * E_jj   and   E_jj * E_ij = 0  when i <> j.          *)
(* ------------------------------------------------------------------ *)

Lemma phi_delta_off (i j : 'I_n.+1) : i != j -> phi (delta_mx i j) = 0.
Proof.
move=> hij.
rewrite -(mul_delta_mx j i j) phi_tr mul_delta_mx_cond.
by rewrite eq_sym (negPf hij) mulr0n phi_zero.
Qed.

(* ------------------------------------------------------------------ *)
(* Step 2: all diagonal matrix units get the same value.               *)
(*   E_ii = E_ij * E_ji   and   E_jj = E_ji * E_ij.                    *)
(* ------------------------------------------------------------------ *)

Lemma phi_delta_diag (i j : 'I_n.+1) :
  phi (delta_mx i i) = phi (delta_mx j j).
Proof. by rewrite -(mul_delta_mx j i i) phi_tr mul_delta_mx. Qed.

(* ------------------------------------------------------------------ *)
(* Step 3: expansion in the matrix-unit basis collapses to the trace.  *)
(* ------------------------------------------------------------------ *)

Lemma phi_eq_trace_scaled (M : MF) :
  phi M = \tr M * phi (delta_mx 0 0).
Proof.
rewrite [X in phi X]matrix_sum_delta phi_sum /mxtrace big_distrl /=.
apply: eq_bigr => i _.
rewrite phi_sum (bigD1 i) //= big1 => [|j hji].
  by rewrite addr0 phi_smul (phi_delta_diag i 0).
by rewrite phi_smul phi_delta_off ?mulr0 // eq_sym.
Qed.

(* ------------------------------------------------------------------ *)
(* Step 4: unitality pins the constant.                                *)
(* ------------------------------------------------------------------ *)

Lemma phi_unit_eq : (n.+1%:R : F) * phi (delta_mx 0 0) = 1.
Proof. by move: (phi_eq_trace_scaled 1%:M); rewrite phi_one mxtrace1 => <-. Qed.

(* The hypotheses are contradictory in characteristic dividing n.+1, so the
   invertibility of the dimension is DERIVED rather than assumed. *)
Lemma phi_dim_neq0 : (n.+1%:R : F) != 0.
Proof.
have : (n.+1%:R : F) * phi (delta_mx 0 0) != 0.
  by rewrite phi_unit_eq oner_neq0.
by rewrite mulf_eq0 negb_or => /andP[].
Qed.

Lemma phi_delta00 : phi (delta_mx 0 0) = (n.+1%:R : F)^-1.
Proof.
by apply: (mulfI phi_dim_neq0); rewrite phi_unit_eq (divff phi_dim_neq0).
Qed.

(* ------------------------------------------------------------------ *)
(* MAIN THEOREM                                                        *)
(* ------------------------------------------------------------------ *)

Theorem matrix_tracial_functional_unique (M : MF) :
  phi M = \tr M / n.+1%:R.
Proof. by rewrite phi_eq_trace_scaled phi_delta00. Qed.

End TracialUnique.

(* ------------------------------------------------------------------ *)
(* Non-vacuity: the normalized matrix trace really does satisfy all    *)
(* four hypotheses (whenever the dimension is invertible in F).        *)
(* Rocq counterpart of Lean's `uhf_trace_isTracialState`.              *)
(* ------------------------------------------------------------------ *)

Section NormalizedTraceIsTracial.

Variable F : fieldType.
Variable n : nat.
Hypothesis Hchar : (n.+1%:R : F) != 0.

Definition ntr (M : 'M[F]_n.+1) : F := \tr M / n.+1%:R.

Lemma ntr_add A B : ntr (A + B) = ntr A + ntr B.
Proof. by rewrite /ntr mxtraceD mulrDl. Qed.

Lemma ntr_smul c A : ntr (c *: A) = c * ntr A.
Proof. by rewrite /ntr mxtraceZ mulrA. Qed.

Lemma ntr_tracial A B : ntr (A *m B) = ntr (B *m A).
Proof. by rewrite /ntr mxtrace_mulC. Qed.

Lemma ntr_one : ntr 1%:M = 1.
Proof. by rewrite /ntr mxtrace1 divff. Qed.

(* And it is the unique such functional, by the main theorem. *)
Theorem normalized_trace_is_unique_tracial_functional :
  [/\ forall A B, ntr (A + B) = ntr A + ntr B,
      forall (c : F) A, ntr (c *: A) = c * ntr A,
      forall A B, ntr (A *m B) = ntr (B *m A),
      ntr 1%:M = 1
    & forall psi : 'M[F]_n.+1 -> F,
        (forall A B, psi (A + B) = psi A + psi B) ->
        (forall (c : F) A, psi (c *: A) = c * psi A) ->
        (forall A B, psi (A *m B) = psi (B *m A)) ->
        psi 1%:M = 1 ->
        forall M, psi M = ntr M].
Proof.
split.
- exact: ntr_add.
- exact: ntr_smul.
- exact: ntr_tracial.
- exact: ntr_one.
- move=> psi ha hs ht hu M.
  by rewrite /ntr (matrix_tracial_functional_unique ha hs ht hu).
Qed.

End NormalizedTraceIsTracial.

Print Assumptions matrix_tracial_functional_unique.
Print Assumptions normalized_trace_is_unique_tracial_functional.
