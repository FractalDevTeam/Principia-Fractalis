(*
  PF_Real/Base3Tower.v

  REAL PROOF (not a shape mirror). The finite-dimensional core of the
  base-3 substrate tower:

      A_k := 'M[F]_(3^k),   iota_k : A_k -> A_{k+1},   E_k : A_{k+1} -> A_k

  This is the Rocq/mathcomp counterpart of the Lean r28/r109 files
  PF_Lean4_Code/PF/SubstrateBase3Embed.lean and
  PF_Lean4_Code/PF/SubstrateConditionalExpectation.lean, specifically of

    substrateEmbedMatrix_{zero,add,smul,mul,one}   (r28)
    substrate_embedding_capstone                   (r28)
    partialTraceStep_substrateEmbedMatrix          (r109)
    partialTraceStep_trace                         (r109)
    partialTraceStep_normalized_trace              (r109)
    partialTraceStep_{add,smul,one}                (r109)

  Verified: every `Print Assumptions` at the bottom reports
  "Closed under the global context" (no axioms, no admits).

  SCOPE, stated plainly:
    * Finite-dimensional only.  There is NO C*-algebra, no completion, no
      inductive limit and no `T_infinity` here: Rocq/mathcomp has none of
      that theory.  Nothing below should be read as verifying the
      completion-tier results of the Lean arc.
    * The star / adjoint structure of the Lean file is NOT mirrored: we work
      over an arbitrary commutative ring / field, which carries no
      involution.  `substrateEmbedMatrix_star` therefore has no counterpart
      here.
    * The iterated maps (`partialTraceDown`, `condExp`) are not built; only
      the single tower step is, which is the load-bearing part.

  What IS proved:
    - an explicit bijection  'I_(3^k) * 'I_3  <->  'I_(3^(k+1));
    - the embedding  A |-> A (x) I_3  is additive, homogeneous,
      multiplicative and unital;
    - trace compatibility  \tr (embed A) = 3%:R * \tr A,  hence preservation
      of the NORMALIZED trace;
    - the partial trace back down is a retraction: ptrace (embed A) = A;
    - \tr (ptrace B) = \tr B / 3%:R, and the normalized trace is preserved.
*)
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(* Section 1.  The index pairing  'I_m * 'I_n.+1  <->  'I_(m * n.+1).  *)
(* This is the Rocq analogue of Lean's `levelStepEquiv`.               *)
(* ------------------------------------------------------------------ *)

Section IndexPairing.

Variables m n : nat.

Lemma pidx_proof (i : 'I_m) (t : 'I_n.+1) : (i * n.+1 + t < m * n.+1)%N.
Proof.
apply: (@leq_trans (i * n.+1 + n.+1)%N); first by rewrite ltn_add2l.
by rewrite -mulSnr leq_mul2r ltn_ord orbT.
Qed.

Definition pidx (i : 'I_m) (t : 'I_n.+1) : 'I_(m * n.+1) :=
  Ordinal (pidx_proof i t).

Lemma idx1_proof (p : 'I_(m * n.+1)) : (p %/ n.+1 < m)%N.
Proof. by rewrite ltn_divLR. Qed.

Definition idx1 (p : 'I_(m * n.+1)) : 'I_m := Ordinal (idx1_proof p).
Definition idx2 (p : 'I_(m * n.+1)) : 'I_n.+1 :=
  Ordinal (ltn_pmod p (ltn0Sn n)).

Lemma idx1K i t : idx1 (pidx i t) = i.
Proof. by apply/val_inj; rewrite /= divnMDl // divn_small ?addn0. Qed.

Lemma idx2K i t : idx2 (pidx i t) = t.
Proof. by apply/val_inj; rewrite /= modnMDl modn_small. Qed.

Lemma pidxK p : pidx (idx1 p) (idx2 p) = p.
Proof. by apply/val_inj; rewrite /= -divn_eq. Qed.

Lemma pidx_bij : bijective (fun x : 'I_m * 'I_n.+1 => pidx x.1 x.2).
Proof.
exists (fun p => (idx1 p, idx2 p)) => [[i t]|p] /=; last exact: pidxK.
by rewrite idx1K idx2K.
Qed.

Lemma pidx_eqE i j s t : (pidx i s == pidx j t) = (i == j) && (s == t).
Proof.
apply/idP/idP => [/eqP e|/andP[/eqP -> /eqP ->]]; last by rewrite eqxx.
have ei : i = j by rewrite -(idx1K i s) e idx1K.
have es : s = t by rewrite -(idx2K i s) e idx2K.
by rewrite ei es !eqxx.
Qed.

Lemma ord_pair_eqE p q :
  (p == q) = (idx1 p == idx1 q) && (idx2 p == idx2 q).
Proof. by rewrite -{1}(pidxK p) -{1}(pidxK q) pidx_eqE. Qed.

Lemma big_pidx (V : zmodType) (f : 'I_(m * n.+1) -> V) :
  \sum_(p < m * n.+1) f p = \sum_(i < m) \sum_(t < n.+1) f (pidx i t).
Proof.
rewrite pair_big /= (reindex (fun x : 'I_m * 'I_n.+1 => pidx x.1 x.2)) //.
exact/onW_bij/pidx_bij.
Qed.

End IndexPairing.

Arguments pidx {m n} i t.
Arguments idx1 {m n} p.
Arguments idx2 {m n} p.

(* ------------------------------------------------------------------ *)
(* Section 2.  The tensor-with-identity embedding  A |-> A (x) I_n.+1. *)
(* Lean counterpart: `substrateEmbedMatrix`.                           *)
(* ------------------------------------------------------------------ *)

Section Embedding.

Variable F : comRingType.
Variables m n : nat.

Definition embed (A : 'M[F]_m) : 'M[F]_(m * n.+1) :=
  \matrix_(p, q) (if idx2 p == idx2 q then A (idx1 p) (idx1 q) else 0).

Lemma embedE (A : 'M[F]_m) p q :
  embed A p q = if idx2 p == idx2 q then A (idx1 p) (idx1 q) else 0.
Proof. by rewrite mxE. Qed.

Lemma embed_pidx (A : 'M[F]_m) i j s t :
  embed A (pidx i s) (pidx j t) = if s == t then A i j else 0.
Proof. by rewrite mxE !idx1K !idx2K. Qed.

Lemma embed0 : embed 0 = 0.
Proof. by apply/matrixP=> p q; rewrite !mxE if_same. Qed.

Lemma embedD A B : embed (A + B) = embed A + embed B.
Proof. by apply/matrixP=> p q; rewrite !mxE; case: ifP => _; rewrite ?addr0. Qed.

Lemma embedZ (c : F) A : embed (c *: A) = c *: embed A.
Proof. by apply/matrixP=> p q; rewrite !mxE; case: ifP => _; rewrite ?mulr0. Qed.

Lemma embedN A : embed (- A) = - embed A.
Proof. by apply/matrixP=> p q; rewrite !mxE; case: ifP => _; rewrite ?oppr0. Qed.

Lemma embed1 : embed 1%:M = 1%:M.
Proof.
apply/matrixP=> p q; rewrite !mxE ord_pair_eqE.
by case: (idx2 p == idx2 q); rewrite ?andbT ?andbF.
Qed.

Lemma embedM_aux A B p q :
  (embed A *m embed B) p q
  = \sum_(k < m) \sum_(u < n.+1)
      ((if idx2 p == u then A (idx1 p) k else 0) *
       (if u == idx2 q then B k (idx1 q) else 0)).
Proof.
rewrite mxE big_pidx; apply: eq_bigr => k _; apply: eq_bigr => u _.
by rewrite !mxE !idx1K !idx2K.
Qed.

Lemma embedM A B : embed (A *m B) = embed A *m embed B.
Proof.
apply/matrixP=> p q; rewrite embedM_aux embedE mxE.
case: ifP => hpq.
  move/eqP: hpq => epq; rewrite -epq.
  apply: eq_bigr => k _.
  rewrite (bigD1 (idx2 p)) //= !eqxx /=.
  rewrite big1 ?addr0 // => u hu.
  by rewrite eq_sym (negPf hu) /= mul0r.
rewrite big1 // => k _; rewrite big1 // => u _.
case: ifP => [/eqP epu|_]; last by rewrite mul0r.
by rewrite -epu hpq /= mulr0.
Qed.

(* --- trace compatibility --- *)

Lemma mxtrace_embed A : \tr (embed A) = n.+1%:R * \tr A.
Proof.
rewrite /mxtrace big_pidx.
transitivity (\sum_(i < m) \sum_(t < n.+1) A i i).
  by apply: eq_bigr => i _; apply: eq_bigr => t _; rewrite embed_pidx eqxx.
rewrite mulr_natl -sumrMnl; apply: eq_bigr => i _.
by rewrite sumr_const card_ord.
Qed.

End Embedding.

Arguments embed {F m n} A.

(* ------------------------------------------------------------------ *)
(* Section 3.  The single-step partial trace (conditional expectation) *)
(* Lean counterpart: `partialTraceStep`.                               *)
(* ------------------------------------------------------------------ *)

Section PartialTrace.

Variable F : fieldType.
Variables m n : nat.
Hypothesis Hn : (n.+1%:R : F) != 0.

Definition ptrace (B : 'M[F]_(m * n.+1)) : 'M[F]_m :=
  (n.+1%:R)^-1 *: \matrix_(i, j) (\sum_(t < n.+1) B (pidx i t) (pidx j t)).

Lemma ptraceE B i j :
  ptrace B i j = (n.+1%:R)^-1 * \sum_(t < n.+1) B (pidx i t) (pidx j t).
Proof. by rewrite !mxE. Qed.

Lemma ptraceD B C : ptrace (B + C) = ptrace B + ptrace C.
Proof.
apply/matrixP=> i j; rewrite !ptraceE !mxE -mulrDr; congr (_ * _).
by rewrite -big_split /=; apply: eq_bigr => t _; rewrite mxE.
Qed.

Lemma ptraceZ (c : F) B : ptrace (c *: B) = c *: ptrace B.
Proof.
apply/matrixP=> i j; rewrite !ptraceE !mxE mulrCA; congr (_ * _).
by rewrite mulr_sumr; apply: eq_bigr => t _; rewrite mxE.
Qed.

Lemma ptrace1 : ptrace 1%:M = 1%:M.
Proof.
apply/matrixP=> i j; rewrite ptraceE mxE.
transitivity ((n.+1%:R : F)^-1 * \sum_(t < n.+1) ((i == j)%:R : F)).
  congr (_ * _); apply: eq_bigr => t _.
  by rewrite mxE pidx_eqE eqxx andbT.
by rewrite sumr_const card_ord -[X in _ * X]mulr_natl mulKf.
Qed.

(* --- retraction: the partial trace inverts the embedding --- *)

Theorem ptrace_embed (A : 'M[F]_m) : ptrace (embed (n := n) A) = A.
Proof.
apply/matrixP=> i j; rewrite ptraceE.
transitivity ((n.+1%:R : F)^-1 * \sum_(t < n.+1) A i j).
  by congr (_ * _); apply: eq_bigr => t _; rewrite embed_pidx eqxx.
by rewrite sumr_const card_ord -[X in _ * X]mulr_natl mulKf.
Qed.

(* --- trace relation --- *)

Theorem mxtrace_ptrace B : \tr (ptrace B) = \tr B / n.+1%:R.
Proof.
rewrite [RHS]mulrC /mxtrace (big_pidx (fun p : 'I_(m * n.+1) => B p p)).
rewrite mulr_sumr; apply: eq_bigr => i _.
exact: ptraceE.
Qed.

(* --- normalized-trace preservation, both directions --- *)

Theorem mxtrace_embed_normalized (A : 'M[F]_m) :
  \tr (embed (n := n) A) / (m * n.+1)%:R = \tr A / m%:R.
Proof.
by rewrite mxtrace_embed natrM invfM [_ * \tr A]mulrC mulrACA divff ?mulr1.
Qed.

Theorem mxtrace_ptrace_normalized B :
  \tr (ptrace B) / m%:R = \tr B / (m * n.+1)%:R.
Proof. by rewrite mxtrace_ptrace natrM invfM mulrA mulrAC. Qed.

End PartialTrace.

Arguments ptrace {F m n} B.

(* ------------------------------------------------------------------ *)
(* Section 4.  Cast lemmas: transporting along  3^k * 3 = 3^(k+1).     *)
(* ------------------------------------------------------------------ *)

Section CastFacts.

Variable F : comRingType.

Lemma castmxD (m1 m2 : nat) (e : m1 = m2) (A B : 'M[F]_m1) :
  castmx (e, e) (A + B) = castmx (e, e) A + castmx (e, e) B.
Proof. by case: m2 / e; rewrite !castmx_id. Qed.

Lemma castmxZ (m1 m2 : nat) (e : m1 = m2) (c : F) (A : 'M[F]_m1) :
  castmx (e, e) (c *: A) = c *: castmx (e, e) A.
Proof. by case: m2 / e; rewrite !castmx_id. Qed.

Lemma castmxM (m1 m2 : nat) (e : m1 = m2) (A B : 'M[F]_m1) :
  castmx (e, e) (A *m B) = castmx (e, e) A *m castmx (e, e) B.
Proof. by case: m2 / e; rewrite !castmx_id. Qed.

Lemma castmx1 (m1 m2 : nat) (e : m1 = m2) :
  castmx (e, e) (1%:M : 'M[F]_m1) = 1%:M.
Proof. by case: m2 / e; rewrite castmx_id. Qed.

Lemma mxtrace_castmx (m1 m2 : nat) (e : m1 = m2) (A : 'M[F]_m1) :
  \tr (castmx (e, e) A) = \tr A.
Proof. by case: m2 / e; rewrite castmx_id. Qed.

End CastFacts.

(* ------------------------------------------------------------------ *)
(* Section 5.  The base-3 tower proper.                                *)
(* ------------------------------------------------------------------ *)

Lemma pow3S k : (3 ^ k * 3)%N = (3 ^ k.+1)%N.
Proof. by rewrite expnS mulnC. Qed.

(* --- the level equivalence  'I_(3^k) * 'I_3 <-> 'I_(3^(k+1)) --- *)

Definition lvlidx k (x : 'I_(3 ^ k) * 'I_3) : 'I_(3 ^ k.+1) :=
  cast_ord (pow3S k) (pidx x.1 x.2).

Theorem lvlidx_bijective k : bijective (@lvlidx k).
Proof.
have [g hg1 hg2] := @pidx_bij (3 ^ k) 2.
exists (fun p => g (cast_ord (esym (pow3S k)) p)) => [x|p] /=.
  by rewrite /lvlidx cast_ordK hg1.
by rewrite /lvlidx hg2 cast_ordKV.
Qed.

Section Base3Tower.

Variable F : fieldType.
Hypothesis Hchar3 : (3%:R : F) != 0.

Lemma pow3_neq0 k : ((3 ^ k)%:R : F) != 0.
Proof. by rewrite natrX expf_neq0. Qed.

(* --- the tower maps --- *)

Definition emb3 k (A : 'M[F]_(3 ^ k)) : 'M[F]_(3 ^ k.+1) :=
  castmx (pow3S k, pow3S k) (embed A).

Definition ptr3 k (B : 'M[F]_(3 ^ k.+1)) : 'M[F]_(3 ^ k) :=
  ptrace (castmx (esym (pow3S k), esym (pow3S k)) B).

(* --- emb3 is a unital algebra map --- *)

Lemma emb3_add k (A B : 'M[F]_(3 ^ k)) :
  emb3 (A + B) = emb3 A + emb3 B.
Proof. by rewrite /emb3 embedD castmxD. Qed.

Lemma emb3_scale k (c : F) (A : 'M[F]_(3 ^ k)) :
  emb3 (c *: A) = c *: emb3 A.
Proof. by rewrite /emb3 embedZ castmxZ. Qed.

Lemma emb3_mul k (A B : 'M[F]_(3 ^ k)) :
  emb3 (A *m B) = emb3 A *m emb3 B.
Proof. by rewrite /emb3 embedM castmxM. Qed.

Lemma emb3_one k : emb3 (1%:M : 'M[F]_(3 ^ k)) = 1%:M.
Proof. by rewrite /emb3 embed1 castmx1. Qed.

(* --- trace behaviour of emb3 --- *)

Theorem emb3_trace k (A : 'M[F]_(3 ^ k)) : \tr (emb3 A) = 3%:R * \tr A.
Proof. by rewrite /emb3 mxtrace_castmx mxtrace_embed. Qed.

Theorem emb3_normalized_trace k (A : 'M[F]_(3 ^ k)) :
  \tr (emb3 A) / (3 ^ k.+1)%:R = \tr A / (3 ^ k)%:R.
Proof.
by rewrite emb3_trace -pow3S natrM invfM [_ * \tr A]mulrC mulrACA divff ?mulr1.
Qed.

(* --- ptr3 is linear, unital, and a retraction for emb3 --- *)

Lemma ptr3_add k (B C : 'M[F]_(3 ^ k.+1)) :
  ptr3 (B + C) = ptr3 B + ptr3 C.
Proof. by rewrite /ptr3 castmxD ptraceD. Qed.

Lemma ptr3_scale k (c : F) (B : 'M[F]_(3 ^ k.+1)) :
  ptr3 (c *: B) = c *: ptr3 B.
Proof. by rewrite /ptr3 castmxZ ptraceZ. Qed.

Lemma ptr3_one k : ptr3 (1%:M : 'M[F]_(3 ^ k.+1)) = 1%:M.
Proof. by rewrite /ptr3 castmx1 ptrace1. Qed.

Theorem ptr3_emb3 k (A : 'M[F]_(3 ^ k)) : ptr3 (emb3 A) = A.
Proof. by rewrite /ptr3 /emb3 castmxK ptrace_embed. Qed.

Theorem ptr3_trace k (B : 'M[F]_(3 ^ k.+1)) :
  \tr (ptr3 B) = \tr B / 3%:R.
Proof. by rewrite /ptr3 mxtrace_ptrace mxtrace_castmx. Qed.

Theorem ptr3_normalized_trace k (B : 'M[F]_(3 ^ k.+1)) :
  \tr (ptr3 B) / (3 ^ k)%:R = \tr B / (3 ^ k.+1)%:R.
Proof.
have h3 : ((3 ^ k.+1)%:R : F) = (3 ^ k)%:R * 3%:R by rewrite -pow3S natrM.
by rewrite ptr3_trace h3 invfM mulrA mulrAC.
Qed.

(* ------------------------------------------------------------------ *)
(* CAPSTONE                                                            *)
(* ------------------------------------------------------------------ *)

Theorem base3_tower_step_capstone k :
  [/\ (forall A B : 'M[F]_(3 ^ k), emb3 (A + B) = emb3 A + emb3 B)
        /\ (forall (c : F) (A : 'M[F]_(3 ^ k)), emb3 (c *: A) = c *: emb3 A)
        /\ (forall A B : 'M[F]_(3 ^ k), emb3 (A *m B) = emb3 A *m emb3 B)
        /\ emb3 (1%:M : 'M[F]_(3 ^ k)) = 1%:M,
      (forall A : 'M[F]_(3 ^ k), \tr (emb3 A) = 3%:R * \tr A)
        /\ (forall A : 'M[F]_(3 ^ k),
              \tr (emb3 A) / (3 ^ k.+1)%:R = \tr A / (3 ^ k)%:R),
      (forall B C : 'M[F]_(3 ^ k.+1), ptr3 (B + C) = ptr3 B + ptr3 C)
        /\ (forall (c : F) (B : 'M[F]_(3 ^ k.+1)),
              ptr3 (c *: B) = c *: ptr3 B)
        /\ ptr3 (1%:M : 'M[F]_(3 ^ k.+1)) = 1%:M,
      (forall A : 'M[F]_(3 ^ k), ptr3 (emb3 A) = A)
    & (forall B : 'M[F]_(3 ^ k.+1), \tr (ptr3 B) = \tr B / 3%:R)
        /\ (forall B : 'M[F]_(3 ^ k.+1),
              \tr (ptr3 B) / (3 ^ k)%:R = \tr B / (3 ^ k.+1)%:R)].
Proof.
split.
- by split; [exact: emb3_add | split; [exact: emb3_scale |
     split; [exact: emb3_mul | exact: emb3_one]]].
- by split; [exact: emb3_trace | exact: emb3_normalized_trace].
- by split; [exact: ptr3_add | split; [exact: ptr3_scale | exact: ptr3_one]].
- exact: ptr3_emb3.
- by split; [exact: ptr3_trace | exact: ptr3_normalized_trace].
Qed.

End Base3Tower.

Print Assumptions lvlidx_bijective.
Print Assumptions ptr3_emb3.
Print Assumptions emb3_normalized_trace.
Print Assumptions ptr3_normalized_trace.
Print Assumptions base3_tower_step_capstone.
