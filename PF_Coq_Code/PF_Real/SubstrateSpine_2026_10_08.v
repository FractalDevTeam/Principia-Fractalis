(*
  PF_Real/SubstrateSpine_2026_10_08.v

  REAL PROOF (not a shape mirror).  Additive extension of PF_Real/Base3Tower.v
  and PF_Real/MatrixTracialUnique.v from the SINGLE tower step to the WHOLE
  finite tower, and the coherence of the trace along it.

  Rocq 9.1.0 + mathcomp 2.5.0.  No Axiom, no Parameter, no Admitted, no
  `exact I`, no `: True`.  Every headline theorem is followed by
  `Print Assumptions`, which must read "Closed under the global context".

  ------------------------------------------------------------------------
  WHY THIS FILE EXISTS
  ------------------------------------------------------------------------

  `PF_Real/README.md` states, under "Additional scope limits":

      "Single tower step only.  emb3/ptr3 go level k <-> k+1; the iterated
       partialTraceDown / condExp are not built."

  and `codex/SEMANTIC_PARITY_MAP_2026-10-06.md` SS1 names, as a missing bridge
  of the substrate axis, "subsequence invariance".

  This file supplies the finite-dimensional part of both.  It builds the
  j-step tower maps

      embIter k j : 'M[F]_(3^k)     -> 'M[F]_(3^(k+j))
      ptrIter k j : 'M[F]_(3^(k+j)) -> 'M[F]_(3^k)

  by iteration of the single-step `emb3` / `ptr3` of Base3Tower.v, and proves:

    (S1) embIter is a unital algebra map (additive, homogeneous,
         multiplicative, unital) at every jump length j;
    (S2) trace scaling  \tr (embIter k j A) = (3^j)%:R * \tr A, hence
         preservation of the NORMALIZED trace across arbitrarily many levels;
    (S3) SUBSEQUENCE INVARIANCE / cocycle law:
             embIter (k+j) i o embIter k j  =  embIter k (j+i)
         up to the dimension cast 3^(k+(j+i)) = 3^((k+j)+i).  This is the
         statement that the tower is a directed system whose transition maps
         do not depend on how the levels are grouped -- i.e. passing to a
         subsequence of levels gives the same system.  It is the finite-level
         content of the "subsequence invariance" bridge;
    (S4) the iterated conditional expectation ptrIter is a retraction:
             ptrIter k j (embIter k j A) = A,
         and it preserves the normalized trace in the other direction;
    (S5) uniqueness of the normalized trace at ARBITRARY positive dimension d
         (not only at d = n.+1), derived from MatrixTracialUnique.v by a
         dimension cast -- this is a strict generalization of the existing
         result, not a restatement;
    (S6) THE CAPSTONE, `substrate_tower_trace_coherent`: ANY additive,
         homogeneous, tracial, unital functional on ANY level 3^(k+j) of the
         tower restricts, along the tower embedding, to the normalized trace
         at level 3^k.  So the tower carries exactly ONE coherent trace:
         there is nothing to choose, at any level, and the choices at
         different levels agree.  This is the finite-dimensional skeleton of
         the Lean `Substrate3Inf.trace_unique` conclusion.
    (S7) the characteristic condition is FORCED, not assumed: the mere
         existence of a tracial unital functional at one level 3^(k+1) of the
         tower implies 3%:R != 0 in F.  Mirrors the honest note in
         MatrixTracialUnique.v, now at tower level.

  Lean counterparts (PF_Lean4_Code/PF/):
      SubstrateBase3Embed.lean            substrateEmbedMatrix       (r28)
      SubstrateConditionalExpectation.lean partialTraceDown, condExp  (r109)
      SubstrateTraceUniqueness.lean       matrix_tracial_state_unique (r113)
      SubstrateRigidity.lean              T_infinity_rigidity         (r217)
                                          Substrate3Inf.trace_unique  (r337)

  ------------------------------------------------------------------------
  SCOPE, STATED PLAINLY -- read before citing
  ------------------------------------------------------------------------

  * FINITE-DIMENSIONAL ONLY.  There is no C*-algebra, no norm, no completion,
    no inductive limit and no `T_infinity` anywhere below.  Rocq/mathcomp has
    none of that theory.  This file does NOT verify, and must not be cited
    for, the completion-tier Lean results: faithfulness of tau_UHF on
    T_infinity, Glimm simplicity, uniqueness of the trace on the COMPLETION,
    or `T_infinity_rigidity` itself.  What is proved here is the finite
    skeleton those results are built on top of.
  * (S3) is subsequence invariance for the FINITE tower.  The parity map's
    bridge also asks for non-isomorphism ACROSS DISTINCT supernatural
    numbers, which needs a K_0 functor for C*-algebras.  That does not exist
    in Rocq/mathcomp and is NOT addressed here.  It remains open on this side
    and is a named research lane, not a gap in the proofs below.
  * No star / adjoint structure: the base is an arbitrary `fieldType`, which
    carries no involution.  The Lean `*_star` lemmas have no counterpart.
  * "Tracial" here means phi (A *m B) = phi (B *m A) with phi additive,
    homogeneous and unital.  No positivity is assumed anywhere -- and none is
    needed, exactly as in the Lean original.

  Author: Pablo Cohen + Claude Opus 5.  2026-10-08.
*)
From mathcomp Require Import all_ssreflect all_algebra.
From PFReal Require Import Base3Tower MatrixTracialUnique.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ================================================================== *)
(* SS0.  Exponent arithmetic.                                          *)
(* ================================================================== *)

(* Transparent on purpose: `pow3_eqn (erefl a)` must reduce to `erefl`. *)
Definition pow3_eqn (a b : nat) (e : a = b) : (3 ^ a)%N = (3 ^ b)%N :=
  f_equal (expn 3) e.

Lemma pow3_gt0 (a : nat) : (0 < 3 ^ a)%N.
Proof. by rewrite expn_gt0. Qed.

(* ================================================================== *)
(* SS1.  Level casts.  Transport along an equality of EXPONENTS.       *)
(* ================================================================== *)

Section LevelCast.

Variable F : fieldType.

Definition lvlcast (a b : nat) (e : a = b) (A : 'M[F]_(3 ^ a))
  : 'M[F]_(3 ^ b) := castmx (pow3_eqn e, pow3_eqn e) A.

(* The cast proof is irrelevant: nat is an eqType, so any two proofs of the
   same exponent equality give the same transport. *)
Lemma lvlcast_irr (a b : nat) (e e' : a = b) (A : 'M[F]_(3 ^ a)) :
  lvlcast e A = lvlcast e' A.
Proof. by rewrite (eq_irrelevance e e'). Qed.

Lemma lvlcast_id (a : nat) (e : a = a) (A : 'M[F]_(3 ^ a)) : lvlcast e A = A.
Proof.
by rewrite /lvlcast (eq_irrelevance (pow3_eqn e) (erefl (3 ^ a)%N)) castmx_id.
Qed.

Lemma lvlcast_trans (a b c : nat) (e1 : a = b) (e2 : b = c) (e3 : a = c)
    (A : 'M[F]_(3 ^ a)) :
  lvlcast e2 (lvlcast e1 A) = lvlcast e3 A.
Proof.
rewrite /lvlcast castmx_comp.
by rewrite (eq_irrelevance (etrans (pow3_eqn e1) (pow3_eqn e2)) (pow3_eqn e3)).
Qed.

Lemma lvlcastK (a b : nat) (e : a = b) (e' : b = a) (A : 'M[F]_(3 ^ a)) :
  lvlcast e' (lvlcast e A) = A.
Proof. by rewrite (lvlcast_trans e e' (erefl a)) lvlcast_id. Qed.

Lemma lvlcast_D (a b : nat) (e : a = b) (A B : 'M[F]_(3 ^ a)) :
  lvlcast e (A + B) = lvlcast e A + lvlcast e B.
Proof. exact: castmxD. Qed.

Lemma lvlcast_Z (a b : nat) (e : a = b) (c : F) (A : 'M[F]_(3 ^ a)) :
  lvlcast e (c *: A) = c *: lvlcast e A.
Proof. exact: castmxZ. Qed.

Lemma lvlcast_M (a b : nat) (e : a = b) (A B : 'M[F]_(3 ^ a)) :
  lvlcast e (A *m B) = lvlcast e A *m lvlcast e B.
Proof. exact: castmxM. Qed.

Lemma lvlcast_1 (a b : nat) (e : a = b) :
  lvlcast e (1%:M : 'M[F]_(3 ^ a)) = 1%:M.
Proof. exact: castmx1. Qed.

Lemma mxtrace_lvlcast (a b : nat) (e : a = b) (A : 'M[F]_(3 ^ a)) :
  \tr (lvlcast e A) = \tr A.
Proof. exact: mxtrace_castmx. Qed.

(* The single tower step commutes with level casts.  This is the one place
   where the dependent elimination actually happens; everything downstream
   is algebra. *)
Lemma emb3_lvlcast (a b : nat) (e : a = b) (f : a.+1 = b.+1)
    (A : 'M[F]_(3 ^ a)) :
  emb3 (lvlcast e A) = lvlcast f (emb3 A).
Proof. by move: f; case: b / e => f; rewrite !lvlcast_id. Qed.

End LevelCast.

Arguments lvlcast {F a b} e A.

(* ================================================================== *)
(* SS2.  The j-step tower maps.                                        *)
(* ================================================================== *)

Section TowerIterate.

Variable F : fieldType.

(* `Set Implicit Arguments` would make the level `k` implicit (it is
   inferable from the argument type), which breaks the recursive calls and
   every later statement.  Keep both indices explicit here. *)
Unset Implicit Arguments.

(* j steps UP from level k.  Lean: iterated `substrateEmbedMatrix`. *)
Fixpoint embIter (k j : nat) : 'M[F]_(3 ^ k) -> 'M[F]_(3 ^ (k + j)) :=
  match j return 'M[F]_(3 ^ k) -> 'M[F]_(3 ^ (k + j)) with
  | 0     => fun A => lvlcast (esym (addn0 k)) A
  | j'.+1 => fun A => lvlcast (esym (addnS k j')) (emb3 (embIter k j' A))
  end.

(* j steps DOWN to level k.  Lean: `partialTraceDown` / `condExp`. *)
Fixpoint ptrIter (k j : nat) : 'M[F]_(3 ^ (k + j)) -> 'M[F]_(3 ^ k) :=
  match j return 'M[F]_(3 ^ (k + j)) -> 'M[F]_(3 ^ k) with
  | 0     => fun B => lvlcast (addn0 k) B
  | j'.+1 => fun B => ptrIter k j' (ptr3 (lvlcast (addnS k j') B))
  end.

Set Implicit Arguments.

(* ---- (S1) embIter is a unital algebra map ---- *)

Lemma embIter_add (k j : nat) (A B : 'M[F]_(3 ^ k)) :
  embIter k j (A + B) = embIter k j A + embIter k j B.
Proof.
elim: j => [|j IH] /=; first exact: lvlcast_D.
by rewrite IH emb3_add lvlcast_D.
Qed.

Lemma embIter_scale (k j : nat) (c : F) (A : 'M[F]_(3 ^ k)) :
  embIter k j (c *: A) = c *: embIter k j A.
Proof.
elim: j => [|j IH] /=; first exact: lvlcast_Z.
by rewrite IH emb3_scale lvlcast_Z.
Qed.

Lemma embIter_mul (k j : nat) (A B : 'M[F]_(3 ^ k)) :
  embIter k j (A *m B) = embIter k j A *m embIter k j B.
Proof.
elim: j => [|j IH] /=; first exact: lvlcast_M.
by rewrite IH emb3_mul lvlcast_M.
Qed.

Lemma embIter_one (k j : nat) :
  embIter k j (1%:M : 'M[F]_(3 ^ k)) = 1%:M.
Proof.
elim: j => [|j IH] /=; first exact: lvlcast_1.
by rewrite IH emb3_one lvlcast_1.
Qed.

(* ---- (S2) trace behaviour ---- *)

Theorem embIter_trace (k j : nat) (A : 'M[F]_(3 ^ k)) :
  \tr (embIter k j A) = (3 ^ j)%:R * \tr A.
Proof.
elim: j => [|j IH] /=; first by rewrite mxtrace_lvlcast expn0 mul1r.
by rewrite mxtrace_lvlcast emb3_trace IH expnS natrM mulrA.
Qed.

Theorem embIter_normalized_trace (k j : nat) (h : ((3 ^ j)%:R : F) != 0)
    (A : 'M[F]_(3 ^ k)) :
  \tr (embIter k j A) / (3 ^ (k + j))%:R = \tr A / (3 ^ k)%:R.
Proof.
by rewrite embIter_trace expnD natrM invfM [_ * \tr A]mulrC mulrACA
           (divff h) mulr1.
Qed.

(* ---- embIter is natural in the jump length ---- *)

Lemma embIter_jcast (k j1 j2 : nat) (e : j1 = j2) (f : k + j1 = k + j2)
    (A : 'M[F]_(3 ^ k)) :
  embIter k j2 A = lvlcast f (embIter k j1 A).
Proof. by move: f; case: j2 / e => f; rewrite lvlcast_id. Qed.

(* Consistency with the existing single-step layer: one iteration IS emb3. *)
Lemma embIter_1 (k : nat) (f : k.+1 = k + 1) (A : 'M[F]_(3 ^ k)) :
  embIter k 1 A = lvlcast f (emb3 A).
Proof.
rewrite /= (emb3_lvlcast _ (f_equal S (esym (addn0 k)))).
by rewrite (lvlcast_trans _ _ f).
Qed.

(* ================================================================== *)
(* SS3.  (S3) SUBSEQUENCE INVARIANCE -- the cocycle law.               *)
(* ================================================================== *)

(* Going up j levels from k and then i levels from k+j is the same map as
   going up j+i levels from k.  Equivalently: the base-3 tower is a directed
   system whose transition maps are independent of how the levels are
   grouped, so restricting to a SUBSEQUENCE of levels yields the same
   system.  This is the finite-level content of the parity map's
   "subsequence invariance" bridge. *)
Theorem embIter_comp (k j i : nat) (e : (k + (j + i))%N = (k + j + i)%N)
    (A : 'M[F]_(3 ^ k)) :
  embIter (k + j) i (embIter k j A) = lvlcast e (embIter k (j + i) A).
Proof.
elim: i e => [|i IH] e /=.
  rewrite (embIter_jcast (esym (addn0 j))
                         (f_equal (addn k) (esym (addn0 j)))).
  by rewrite (lvlcast_trans _ _ (esym (addn0 (k + j)%N))).
(* collapse the LHS to a single cast of emb3 (embIter k (j+i) A) *)
rewrite (IH (addnA k j i)).
rewrite (emb3_lvlcast _ (f_equal S (addnA k j i))).
rewrite (lvlcast_trans _ _ (etrans (f_equal S (addnA k j i))
                                   (esym (addnS (k + j)%N i)))).
(* expand and collapse the RHS to a single cast of the same matrix *)
rewrite (embIter_jcast (esym (addnS j i))
                       (f_equal (addn k) (esym (addnS j i)))) /=.
rewrite (lvlcast_trans _ _ (etrans (esym (addnS k (j + i)%N))
                                   (f_equal (addn k) (esym (addnS j i))))).
rewrite (lvlcast_trans _ _ (etrans (etrans (esym (addnS k (j + i)%N))
                                           (f_equal (addn k)
                                              (esym (addnS j i)))) e)).
exact: lvlcast_irr.
Qed.

(* The one-step corollary: the (j+1)-step map is the single step `emb3` of
   Base3Tower.v applied on top of the j-step map. *)
Corollary embIter_succ (k j : nat) (e : ((k + j).+1)%N = (k + j.+1)%N)
    (A : 'M[F]_(3 ^ k)) :
  embIter k j.+1 A = lvlcast e (emb3 (embIter k j A)).
Proof. rewrite /=. exact: lvlcast_irr. Qed.

(* ================================================================== *)
(* SS4.  (S4) the iterated conditional expectation.                    *)
(* ================================================================== *)

Lemma ptrIter_add (k j : nat) (B C : 'M[F]_(3 ^ (k + j))) :
  ptrIter k j (B + C) = ptrIter k j B + ptrIter k j C.
Proof.
elim: j B C => [|j IH] B C /=; first exact: lvlcast_D.
by rewrite lvlcast_D ptr3_add IH.
Qed.

Lemma ptrIter_scale (k j : nat) (c : F) (B : 'M[F]_(3 ^ (k + j))) :
  ptrIter k j (c *: B) = c *: ptrIter k j B.
Proof.
elim: j B => [|j IH] B /=; first exact: lvlcast_Z.
by rewrite lvlcast_Z ptr3_scale IH.
Qed.

Theorem ptrIter_normalized_trace (k j : nat) (B : 'M[F]_(3 ^ (k + j))) :
  \tr (ptrIter k j B) / (3 ^ k)%:R = \tr B / (3 ^ (k + j))%:R.
Proof.
(* The dimension equalities are rewritten at SCALAR level: rewriting them in
   the matrix index would be a dependent rewrite and is rejected. *)
elim: j B => [|j IH] B /=.
  have e0 : ((3 ^ (k + 0))%:R : F) = (3 ^ k)%:R by rewrite addn0.
  by rewrite mxtrace_lvlcast e0.
have e1 : ((3 ^ (k + j.+1))%:R : F) = (3 ^ (k + j).+1)%:R by rewrite addnS.
by rewrite IH ptr3_normalized_trace mxtrace_lvlcast e1.
Qed.

(* ---- the retraction, i.e. condExp o embed = id, at every jump length ---- *)

Theorem ptrIter_embIter (k j : nat) (h3 : (3%:R : F) != 0)
    (A : 'M[F]_(3 ^ k)) :
  ptrIter k j (embIter k j A) = A.
Proof.
elim: j => [|j IH] /=; first exact: lvlcastK.
by rewrite (lvlcastK (esym (addnS k j))) (ptr3_emb3 h3) IH.
Qed.

End TowerIterate.

Arguments embIter {F} k j A.
Arguments ptrIter {F} k j B.

(* ================================================================== *)
(* SS5.  (S5) tracial uniqueness at ARBITRARY positive dimension.      *)
(* ================================================================== *)

(* MatrixTracialUnique.v states uniqueness on 'M[F]_n.+1.  The tower's
   dimensions are 3^k, which is positive but not syntactically a successor.
   Rather than restate the theorem we TRANSPORT it: the statement below is
   strictly more general and is derived from the existing one. *)

Section TracialUniqueAnyDim.

Variable F : fieldType.

Theorem tracial_functional_unique_dim (d : nat) (hd : (0 < d)%N)
    (phi : 'M[F]_d -> F)
    (phi_add  : forall A B : 'M[F]_d, phi (A + B) = phi A + phi B)
    (phi_smul : forall (c : F) (A : 'M[F]_d), phi (c *: A) = c * phi A)
    (phi_tr   : forall A B : 'M[F]_d, phi (A *m B) = phi (B *m A))
    (phi_one  : phi 1%:M = 1) (M : 'M[F]_d) :
  phi M = \tr M / d%:R.
Proof.
have e : d = d.-1.+1 by rewrite prednK.
pose psi (B : 'M[F]_(d.-1.+1)) := phi (castmx (esym e, esym e) B).
have hadd : forall B C, psi (B + C) = psi B + psi C.
  by move=> B C; rewrite /psi castmxD phi_add.
have hsmul : forall (c : F) B, psi (c *: B) = c * psi B.
  by move=> c B; rewrite /psi castmxZ phi_smul.
have htr : forall B C, psi (B *m C) = psi (C *m B).
  by move=> B C; rewrite /psi !castmxM phi_tr.
have hone : psi 1%:M = 1.
  by rewrite /psi castmx1 phi_one.
move: (matrix_tracial_functional_unique hadd hsmul htr hone
         (castmx (e, e) M)).
rewrite /psi castmxK mxtrace_castmx (prednK hd) => ->.
by [].
Qed.

(* ---- (S7) the characteristic condition is FORCED, not assumed ---- *)

(* Existence of one tracial unital functional at dimension d forces d to be
   invertible in F.  Rocq counterpart of the honest note in
   MatrixTracialUnique.v, now stated for arbitrary d. *)
Lemma tracial_dim_neq0 (d : nat) (hd : (0 < d)%N)
    (phi : 'M[F]_d -> F)
    (phi_add  : forall A B : 'M[F]_d, phi (A + B) = phi A + phi B)
    (phi_smul : forall (c : F) (A : 'M[F]_d), phi (c *: A) = c * phi A)
    (phi_tr   : forall A B : 'M[F]_d, phi (A *m B) = phi (B *m A))
    (phi_one  : phi 1%:M = 1) :
  (d%:R : F) != 0.
Proof.
have h1 := tracial_functional_unique_dim hd phi_add phi_smul phi_tr phi_one
             (1%:M : 'M[F]_d).
rewrite phi_one mxtrace1 in h1.
have h2 : (d%:R : F) * (d%:R)^-1 != 0 by rewrite -h1 oner_neq0.
by move: h2; rewrite mulf_eq0 negb_or => /andP[].
Qed.

End TracialUniqueAnyDim.

(* ================================================================== *)
(* SS6.  (S6) THE CAPSTONE -- the tower carries exactly one trace.     *)
(* ================================================================== *)

Section TowerTraceCoherence.

Variable F : fieldType.

(* Characteristic 3 is excluded automatically: a tracial unital functional at
   a level 3^(k+1) of the tower cannot exist unless 3%:R != 0. *)
Lemma tower_char3_forced (m : nat)
    (phi : 'M[F]_(3 ^ m.+1) -> F)
    (phi_add  : forall A B : 'M[F]_(3 ^ m.+1), phi (A + B) = phi A + phi B)
    (phi_smul : forall (c : F) (A : 'M[F]_(3 ^ m.+1)),
                  phi (c *: A) = c * phi A)
    (phi_tr   : forall A B : 'M[F]_(3 ^ m.+1), phi (A *m B) = phi (B *m A))
    (phi_one  : phi 1%:M = 1) :
  (3%:R : F) != 0.
Proof.
have h := tracial_dim_neq0 (pow3_gt0 m.+1) phi_add phi_smul phi_tr phi_one.
move: h; rewrite natrX; apply: contraNN => /eqP ->.
by rewrite expr0n.
Qed.

(* ------------------------------------------------------------------ *)
(* Every tracial unital functional at level k+j of the tower restricts, *)
(* THROUGH the tower embedding, to the normalized trace at level k.     *)
(* No positivity, no characteristic assumption: both are consequences.  *)
(* ------------------------------------------------------------------ *)

Theorem substrate_tower_trace_coherent (k j : nat)
    (phi : 'M[F]_(3 ^ (k + j)) -> F)
    (phi_add  : forall A B : 'M[F]_(3 ^ (k + j)), phi (A + B) = phi A + phi B)
    (phi_smul : forall (c : F) (A : 'M[F]_(3 ^ (k + j))),
                  phi (c *: A) = c * phi A)
    (phi_tr   : forall A B : 'M[F]_(3 ^ (k + j)), phi (A *m B) = phi (B *m A))
    (phi_one  : phi 1%:M = 1) (A : 'M[F]_(3 ^ k)) :
  phi (embIter k j A) = \tr A / (3 ^ k)%:R.
Proof.
have hd : ((3 ^ (k + j))%:R : F) != 0 :=
  tracial_dim_neq0 (pow3_gt0 (k + j)) phi_add phi_smul phi_tr phi_one.
have hj : ((3 ^ j)%:R : F) != 0.
  move: hd; rewrite expnD natrM mulf_eq0 negb_or => /andP[_].
  by [].
rewrite (tracial_functional_unique_dim (pow3_gt0 (k + j)) phi_add phi_smul
           phi_tr phi_one).
exact: embIter_normalized_trace.
Qed.

(* Two tracial unital functionals, at two DIFFERENT levels of the tower,
   necessarily agree on the common sub-level.  This is the compatibility
   that makes a single trace on the whole tower well defined. *)
Corollary substrate_tower_trace_levels_agree (k j1 j2 : nat)
    (phi : 'M[F]_(3 ^ (k + j1)) -> F) (psi : 'M[F]_(3 ^ (k + j2)) -> F)
    (pa : forall A B : 'M[F]_(3 ^ (k + j1)), phi (A + B) = phi A + phi B)
    (ps : forall (c : F) (A : 'M[F]_(3 ^ (k + j1))), phi (c *: A) = c * phi A)
    (pt : forall A B : 'M[F]_(3 ^ (k + j1)), phi (A *m B) = phi (B *m A))
    (po : phi 1%:M = 1)
    (qa : forall A B : 'M[F]_(3 ^ (k + j2)), psi (A + B) = psi A + psi B)
    (qs : forall (c : F) (A : 'M[F]_(3 ^ (k + j2))), psi (c *: A) = c * psi A)
    (qt : forall A B : 'M[F]_(3 ^ (k + j2)), psi (A *m B) = psi (B *m A))
    (qo : psi 1%:M = 1) (A : 'M[F]_(3 ^ k)) :
  phi (embIter k j1 A) = psi (embIter k j2 A).
Proof.
rewrite (substrate_tower_trace_coherent pa ps pt po).
by rewrite (substrate_tower_trace_coherent qa qs qt qo).
Qed.

(* ------------------------------------------------------------------ *)
(* BUNDLED CAPSTONE                                                    *)
(* ------------------------------------------------------------------ *)

Theorem substrate_spine_tower_capstone (k j : nat) (h3 : (3%:R : F) != 0) :
  [/\ (* (S1) unital algebra map at every jump length *)
      (forall A B : 'M[F]_(3 ^ k),
         embIter k j (A + B) = embIter k j A + embIter k j B)
      /\ (forall (c : F) (A : 'M[F]_(3 ^ k)),
            embIter k j (c *: A) = c *: embIter k j A)
      /\ (forall A B : 'M[F]_(3 ^ k),
            embIter k j (A *m B) = embIter k j A *m embIter k j B)
      /\ embIter k j (1%:M : 'M[F]_(3 ^ k)) = 1%:M,
      (* (S2) trace scaling and normalized-trace preservation *)
      (forall A : 'M[F]_(3 ^ k), \tr (embIter k j A) = (3 ^ j)%:R * \tr A)
      /\ (forall A : 'M[F]_(3 ^ k),
            \tr (embIter k j A) / (3 ^ (k + j))%:R = \tr A / (3 ^ k)%:R),
      (* (S3) subsequence invariance *)
      (forall (i : nat) (e : k + (j + i) = k + j + i) (A : 'M[F]_(3 ^ k)),
         embIter (k + j) i (embIter k j A) = lvlcast e (embIter k (j + i) A)),
      (* (S4) iterated conditional expectation is a retraction *)
      (forall A : 'M[F]_(3 ^ k), ptrIter k j (embIter k j A) = A)
      /\ (forall B : 'M[F]_(3 ^ (k + j)),
            \tr (ptrIter k j B) / (3 ^ k)%:R = \tr B / (3 ^ (k + j))%:R)
    & (* (S6) exactly one coherent trace on the tower *)
      (forall phi : 'M[F]_(3 ^ (k + j)) -> F,
         (forall A B, phi (A + B) = phi A + phi B) ->
         (forall (c : F) A, phi (c *: A) = c * phi A) ->
         (forall A B, phi (A *m B) = phi (B *m A)) ->
         phi 1%:M = 1 ->
         forall A : 'M[F]_(3 ^ k), phi (embIter k j A) = \tr A / (3 ^ k)%:R)].
Proof.
have hj : ((3 ^ j)%:R : F) != 0 by rewrite natrX expf_neq0.
split.
- split; [exact: embIter_add | split; [exact: embIter_scale |
    split; [exact: embIter_mul | exact: embIter_one]]].
- by split; [exact: embIter_trace |
             move=> A; exact: embIter_normalized_trace].
- move=> i e A; exact: embIter_comp.
- by split; [move=> A; exact: (ptrIter_embIter _ h3) |
             exact: ptrIter_normalized_trace].
- move=> phi pa ps pt po A.
  exact: (substrate_tower_trace_coherent pa ps pt po).
Qed.

End TowerTraceCoherence.

(* ================================================================== *)
(* AXIOM AUDIT.  Each must report "Closed under the global context".   *)
(* ================================================================== *)

Print Assumptions embIter_trace.
Print Assumptions embIter_normalized_trace.
Print Assumptions embIter_comp.
Print Assumptions ptrIter_embIter.
Print Assumptions ptrIter_normalized_trace.
Print Assumptions tracial_functional_unique_dim.
Print Assumptions tracial_dim_neq0.
Print Assumptions tower_char3_forced.
Print Assumptions substrate_tower_trace_coherent.
Print Assumptions substrate_tower_trace_levels_agree.
Print Assumptions substrate_spine_tower_capstone.
