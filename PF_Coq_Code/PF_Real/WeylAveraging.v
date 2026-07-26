(*
  PF_Real/WeylAveraging.v

  REAL PROOF (not a shape mirror).  Clock / shift (Weyl) matrices over a field
  containing a primitive n-th root of unity, character-sum orthogonality, and
  the Weyl averaging identities

      (1/n)   *: \sum_(a<n) C^a X (C^a)^-1                = diagonal part of X
      (1/n^2) *: \sum_(b<n) \sum_(a<n) W X W^-1           = (\tr X / n) *: 1
                                        with W = S^b C^a

  This is the Rocq/mathcomp counterpart of the Lean r104 file
  PF_Lean4_Code/PF/SubstrateMatrixUnitaryAveraging.lean.

  Verified: every `Print Assumptions` at the bottom reports
  "Closed under the global context" (no axioms, no admits).

  SCOPE, stated plainly -- READ BEFORE CITING THIS FILE:

    * Finite-dimensional linear algebra over an abstract `fieldType` that
      carries a primitive n-th root of unity.  There is NO C*-algebra, no
      unitary group, no operator norm and no positivity here: Rocq/mathcomp
      has none of that theory.  "Unitary averaging" in the Lean title is
      realised here as averaging over conjugation by the INVERTIBLE Weyl
      matrices; invertibility is all the algebraic argument uses, and it is
      PROVED explicitly (`clock_pow_inv`, `shift_pow_inv`) rather than
      assumed.  In particular the inverse of C^a is written concretely as
      C^(n-a) rather than via mathcomp's `invmx`.
    * The field is arbitrary, so "adjoint"/star structure is absent; the
      Lean statements about self-adjointness have no counterpart here.
    * n is written n'.+1 throughout, because mathcomp only equips 'M[F]_k
      with a ring structure for k of the form _.+1.
    * Nothing here says anything about the base-3 substrate tower or about
      T_infinity; this file is pure finite-dimensional Weyl-matrix algebra.

  Main results:
    geom_sum, char_sum        -- geometric sum / character orthogonality
    weyl_character_sum        -- \sum_(a<n) (w^i/w^j)^a = [i==j] * n
    clock_pow_inv             -- C^a *m C^(n-a) = 1
    shift_pow_inv             -- S^a *m S^(n-a) = 1
    weyl_commutation          -- S *m C = w *: (C *m S)
    clock_average             -- the clock average is the diagonal projection
    shift_average_diag        -- the shift average of a diagonal matrix
    weyl_average              -- the full two-index Weyl average
*)
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(* Section 1.  Geometric sums and character sums over a field.         *)
(* ------------------------------------------------------------------ *)

Section GeomSum.

Variable F : fieldType.

Lemma geom_sum (x : F) (N : nat) :
  (x - 1) * \sum_(a < N) x ^+ a = x ^+ N - 1.
Proof.
elim: N => [|N ih]; first by rewrite big_ord0 mulr0 expr0 subrr.
rewrite big_ord_recr /= mulrDr ih mulrBl mul1r -exprS.
by rewrite [x ^+ N.+1 - x ^+ N]addrC addrACA subrr add0r addrC.
Qed.

(* Orthogonality of characters, in its bare algebraic form: if x is an
   N-th root of unity then the sum of its powers is N or 0. *)
Lemma char_sum (x : F) (N : nat) :
  x ^+ N = 1 -> \sum_(a < N) x ^+ a = if x == 1 then N%:R else 0.
Proof.
move=> hx; case: ifPn => [/eqP ->|hx1].
  by under eq_bigr do rewrite expr1n; rewrite sumr_const card_ord.
have hne : x - 1 != 0 by rewrite subr_eq0.
have h : (x - 1) * \sum_(a < N) x ^+ a = 0 by rewrite geom_sum hx subrr.
by move: h => /eqP; rewrite mulf_eq0 (negPf hne) /= => /eqP.
Qed.

End GeomSum.

(* ------------------------------------------------------------------ *)
(* Section 2.  Clock and shift matrices at a primitive root of unity.  *)
(* ------------------------------------------------------------------ *)

Section Weyl.

Variable F : fieldType.
Variable n' : nat.
Local Notation n := n'.+1.
Variable w : F.
Hypothesis prim_w : n.-primitive_root w.

(* --- basic facts about w --- *)

Lemma wn : w ^+ n = 1.
Proof. exact: prim_expr_order prim_w. Qed.

Lemma w_neq0 : w != 0.
Proof. by rewrite (prim_root_eq0 prim_w). Qed.

Lemma nF_neq0 : (n%:R : F) != 0.
Proof. exact: prim_root_natf_neq0 prim_w. Qed.

Lemma wexp_mul_order (c : nat) : w ^+ (c * n) = 1.
Proof. by rewrite exprM exprAC wn expr1n. Qed.

(* --- the character chi_{ij}(a) = (w^i / w^j)^a --- *)

Definition chi (i j : 'I_n) : F := w ^+ i / w ^+ j.

Lemma chi_order (i j : 'I_n) : (chi i j) ^+ n = 1.
Proof. by rewrite /chi exprMn exprVn -!exprM !wexp_mul_order invr1 mulr1. Qed.

Lemma chi_eq1 (i j : 'I_n) : (chi i j == 1) = (i == j).
Proof.
have hj : (w ^+ j : F) != 0 by rewrite expf_neq0 ?w_neq0.
rewrite /chi.
apply/idP/idP => [/eqP h|/eqP hij]; last by rewrite hij divff.
have h2 : (w ^+ i : F) = w ^+ j by rewrite -[LHS](divfK hj) h mul1r.
apply/eqP/val_inj => /=.
by move/eqP: h2; rewrite (eq_prim_root_expr prim_w) !modn_small // => /eqP.
Qed.

(* --- CHARACTER-SUM ORTHOGONALITY --- *)

Theorem weyl_character_sum (i j : 'I_n) :
  \sum_(a < n) (chi i j) ^+ a = if i == j then n%:R else 0.
Proof. by rewrite (char_sum (chi_order i j)) chi_eq1. Qed.

(* --- the clock matrix and its powers --- *)

Definition clock : 'M[F]_n := \matrix_(i, j) (if i == j then w ^+ i else 0).

Definition clockpow (a : nat) : 'M[F]_n :=
  \matrix_(i, j) (if i == j then w ^+ (i * a) else 0).

Lemma clockE (i j : 'I_n) : clock i j = if i == j then w ^+ i else 0.
Proof. by rewrite mxE. Qed.

Lemma clock_diag (i : 'I_n) : clock i i = w ^+ i.
Proof. by rewrite clockE eqxx. Qed.

Lemma clock_off (i j : 'I_n) : i != j -> clock i j = 0.
Proof. by move=> h; rewrite clockE (negPf h). Qed.

Lemma clockpowE (a : nat) (i j : 'I_n) :
  clockpow a i j = if i == j then w ^+ (i * a) else 0.
Proof. by rewrite mxE. Qed.

Lemma clockpow_diag (a : nat) (i : 'I_n) : clockpow a i i = w ^+ (i * a).
Proof. by rewrite clockpowE eqxx. Qed.

Lemma clockpow_off (a : nat) (i j : 'I_n) : i != j -> clockpow a i j = 0.
Proof. by move=> h; rewrite clockpowE (negPf h). Qed.

Lemma clockpow0 : clockpow 0 = 1%:M.
Proof.
apply/matrixP=> i j; rewrite clockpowE mxE muln0 expr0.
by case: (i == j); rewrite ?mulr1n ?mulr0n.
Qed.

Lemma clockpow1 : clockpow 1 = clock.
Proof. by apply/matrixP=> i j; rewrite clockpowE clockE muln1. Qed.

Lemma clockpowM (a b : nat) : clockpow a *m clockpow b = clockpow (a + b).
Proof.
apply/matrixP=> i j; rewrite mxE (bigD1 i) //= clockpow_diag.
rewrite big1 ?addr0; last first.
  move=> k hk; have hik : i != k by rewrite eq_sym.
  by rewrite (clockpow_off a hik) mul0r.
rewrite !clockpowE; case: ifP => _; last by rewrite mulr0.
by rewrite -exprD -mulnDr.
Qed.

Lemma clockpow_order : clockpow n = 1%:M.
Proof.
apply/matrixP=> i j; rewrite clockpowE mxE.
by case: (i == j); rewrite ?wexp_mul_order ?mulr1n ?mulr0n.
Qed.

Lemma clock_pow (a : nat) : clock ^+ a = clockpow a.
Proof.
elim: a => [|a ih]; first by rewrite expr0 clockpow0.
by rewrite exprS ih -clockpow1 -mulmxE clockpowM.
Qed.

(* the clock matrix is invertible, with an explicit inverse *)
Theorem clock_pow_inv (a : nat) : (a <= n)%N ->
  clock ^+ a *m clock ^+ (n - a) = 1%:M.
Proof. by move=> ha; rewrite !clock_pow clockpowM subnKC // clockpow_order. Qed.

(* --- conjugation by clock powers, entrywise --- *)

Lemma clockpow_conj_entry (a b : nat) (X : 'M[F]_n) (i j : 'I_n) :
  (clockpow a *m X *m clockpow b) i j = w ^+ (i * a) * X i j * w ^+ (j * b).
Proof.
rewrite mxE (bigD1 j) //= clockpow_diag.
rewrite big1 ?addr0; last first.
  by move=> k hk; rewrite (clockpow_off b hk) mulr0.
congr (_ * _); rewrite mxE (bigD1 i) //= clockpow_diag.
rewrite big1 ?addr0 //.
move=> l hl; have hil : i != l by rewrite eq_sym.
by rewrite (clockpow_off a hil) mul0r.
Qed.

Lemma wexp_conj (a : nat) (i j : 'I_n) (ha : (a <= n)%N) :
  w ^+ (i * a) * w ^+ (j * (n - a)) = chi i j ^+ a.
Proof.
have hj : (w ^+ (j * a) : F) != 0 by rewrite expf_neq0 ?w_neq0.
apply: (mulIf hj).
rewrite /chi exprMn exprVn -!exprM divfK //.
by rewrite -mulrA -exprD -mulnDr subnK // wexp_mul_order mulr1.
Qed.

(* --- MAIN: the clock average is the diagonal projection --- *)

Definition diagpart (X : 'M[F]_n) : 'M[F]_n :=
  \matrix_(i, j) (if i == j then X i j else 0).

Theorem clock_average (X : 'M[F]_n) :
  (n%:R : F)^-1 *: \sum_(a < n) (clock ^+ a *m X *m clock ^+ (n - a))
  = diagpart X.
Proof.
apply/matrixP=> i j; rewrite mxE summxE [diagpart X i j]mxE.
transitivity ((n%:R : F)^-1 * ((\sum_(a < n) chi i j ^+ a) * X i j)).
  congr (_ * _); rewrite mulr_suml; apply: eq_bigr => a _.
  rewrite !clock_pow clockpow_conj_entry -mulrA [X i j * _]mulrC mulrA.
  by rewrite (@wexp_conj a i j (ltnW (ltn_ord a))).
rewrite weyl_character_sum; case: ifP => _; last by rewrite mul0r mulr0.
by rewrite (mulKf nF_neq0).
Qed.

(* --- the shift matrix --- *)

Definition omod (c : nat) : 'I_n := Ordinal (ltn_pmod c (ltn0Sn n')).

Lemma omodE (c : nat) : (omod c : nat) = (c %% n)%N.
Proof. by []. Qed.

Lemma omodK (i : 'I_n) : omod i = i.
Proof. by apply/val_inj; rewrite /= modn_small. Qed.

Definition sh (c : nat) : 'M[F]_n :=
  \matrix_(i, j) (if j == omod (i + c) then 1 else 0).

Definition shift : 'M[F]_n := sh 1.

Lemma shE (c : nat) (i j : 'I_n) :
  sh c i j = if j == omod (i + c) then 1 else 0.
Proof. by rewrite mxE. Qed.

Lemma sh_diag (c : nat) (i : 'I_n) : sh c i (omod (i + c)) = 1.
Proof. by rewrite shE eqxx. Qed.

Lemma sh_off (c : nat) (i j : 'I_n) : j != omod (i + c) -> sh c i j = 0.
Proof. by move=> h; rewrite shE (negPf h). Qed.

Lemma sh0 : sh 0 = 1%:M.
Proof.
apply/matrixP=> i j; rewrite shE mxE addn0 omodK eq_sym.
by case: (i == j); rewrite ?mulr1n ?mulr0n.
Qed.

Lemma shM (a b : nat) : sh a *m sh b = sh (a + b).
Proof.
apply/matrixP=> i j; rewrite mxE (bigD1 (omod (i + a))) //= sh_diag mul1r.
rewrite big1 ?addr0; last first.
  by move=> k hk; rewrite (sh_off hk) mul0r.
rewrite !shE.
have -> : omod (omod (i + a) + b) = omod (i + (a + b)).
  by apply/val_inj; rewrite /= modnDml addnA.
by [].
Qed.

Lemma sh_order : sh n = 1%:M.
Proof.
apply/matrixP=> i j; rewrite shE mxE.
have -> : omod (i + n) = i by apply/val_inj; rewrite /= modnDr modn_small.
by rewrite eq_sym; case: (i == j); rewrite ?mulr1n ?mulr0n.
Qed.

Lemma shift_pow (a : nat) : shift ^+ a = sh a.
Proof.
elim: a => [|a ih]; first by rewrite expr0 sh0.
by rewrite exprS ih /shift -mulmxE shM.
Qed.

(* the shift matrix is invertible, with an explicit inverse *)
Theorem shift_pow_inv (a : nat) : (a <= n)%N ->
  shift ^+ a *m shift ^+ (n - a) = 1%:M.
Proof. by move=> ha; rewrite !shift_pow shM subnKC // sh_order. Qed.

(* --- the Weyl commutation relation  S C = w (C S) --- *)

Theorem weyl_commutation : shift *m clock = w *: (clock *m shift).
Proof.
apply/matrixP=> i j; rewrite /shift !mxE.
rewrite (bigD1 (omod (i + 1))) //= sh_diag mul1r.
rewrite big1 ?addr0; last first.
  by move=> k hk; rewrite (sh_off hk) mul0r.
rewrite (bigD1 i) //= clock_diag.
rewrite big1 ?addr0; last first.
  move=> k hk; have hik : i != k by rewrite eq_sym.
  by rewrite (clock_off hik) mul0r.
rewrite clockE shE [j == omod (i + 1)]eq_sym.
case: ifP => _; last by rewrite mulr0 mulr0.
by rewrite mulr1 omodE (prim_expr_mod prim_w) addn1 exprS.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3.  The shift average of a diagonal matrix, and the full    *)
(* two-index Weyl average.                                             *)
(* ------------------------------------------------------------------ *)

Lemma omod_shiftK (b : nat) (hb : (b <= n)%N) (l : 'I_n) :
  omod (omod (l + b) + (n - b)) = l.
Proof.
apply/val_inj; rewrite /= modnDml -addnA subnKC //.
by rewrite modnDr modn_small.
Qed.

Lemma omod_shiftKV (b : nat) (hb : (b <= n)%N) (l : 'I_n) :
  omod (omod (l + (n - b)) + b) = l.
Proof.
apply/val_inj; rewrite /= modnDml -addnA subnK //.
by rewrite modnDr modn_small.
Qed.

(* conjugation by a shift power permutes the indices cyclically *)
Lemma sh_conj_entry (b : nat) (hb : (b <= n)%N) (D : 'M[F]_n) (i j : 'I_n) :
  (sh b *m D *m sh (n - b)) i j = D (omod (i + b)) (omod (j + b)).
Proof.
rewrite mxE (bigD1 (omod (j + b))) //=.
rewrite [sh (n - b) (omod (j + b)) j]shE (omod_shiftK hb) eqxx mulr1.
rewrite big1 ?addr0; last first.
  move=> l hl; rewrite [sh (n - b) l j]shE.
  case: ifP => [/eqP hj|_]; last by rewrite mulr0.
  by case/negP: hl; rewrite hj (omod_shiftKV hb) eqxx.
rewrite mxE (bigD1 (omod (i + b))) //= sh_diag mul1r.
rewrite big1 ?addr0 //.
by move=> k hk; rewrite (sh_off hk) mul0r.
Qed.

(* the cyclic reindexing bijection on 'I_n *)
Lemma omod_add_can (i : 'I_n) :
  cancel (fun b : 'I_n => omod (i + b)) (fun k : 'I_n => omod (k + (n - i))).
Proof.
have hi : (i <= n)%N := ltnW (ltn_ord i).
move=> b; apply/val_inj; rewrite /= modnDml -addnA [(b + (n - i))%N]addnC addnA.
by rewrite subnKC // modnDl modn_small.
Qed.

Lemma omod_add_can2 (i : 'I_n) :
  cancel (fun k : 'I_n => omod (k + (n - i))) (fun b : 'I_n => omod (i + b)).
Proof.
have hi : (i <= n)%N := ltnW (ltn_ord i).
move=> k; apply/val_inj; rewrite /= modnDmr addnA [(i + k)%N]addnC -addnA subnKC //.
by rewrite modnDr modn_small.
Qed.

Lemma omod_add_bij (i : 'I_n) : bijective (fun b : 'I_n => omod (i + b)).
Proof.
by exists (fun k : 'I_n => omod (k + (n - i)));
   [exact: omod_add_can | exact: omod_add_can2].
Qed.

Lemma sum_shift_trace (i : 'I_n) (X : 'M[F]_n) :
  \sum_(b < n) X (omod (i + b)) (omod (i + b)) = \tr X.
Proof.
rewrite /mxtrace [RHS](reindex (fun b : 'I_n => omod (i + b))) //.
exact/onW_bij/omod_add_bij.
Qed.

Lemma diagpart_diag (X : 'M[F]_n) (k : 'I_n) : diagpart X k k = X k k.
Proof. by rewrite mxE eqxx. Qed.

Lemma diagpart_off (X : 'M[F]_n) (k l : 'I_n) : k != l -> diagpart X k l = 0.
Proof. by move=> h; rewrite mxE (negPf h). Qed.

(* --- the shift average of a diagonal matrix --- *)

Theorem shift_average_diag (X : 'M[F]_n) :
  (n%:R : F)^-1 *: \sum_(b < n)
      (shift ^+ b *m diagpart X *m shift ^+ (n - b))
  = (\tr X / n%:R) *: 1%:M.
Proof.
apply/matrixP=> i j.
rewrite [LHS]mxE summxE [RHS]mxE [Y in _ = _ * Y]mxE.
transitivity ((n%:R : F)^-1 *
   \sum_(b < n) diagpart X (omod (i + b)) (omod (j + b))).
  congr (_ * _); apply: eq_bigr => b _.
  by rewrite !shift_pow (sh_conj_entry (ltnW (ltn_ord b))).
case: eqP => [->|hij].
  rewrite mulr1n mulr1.
  under eq_bigr do rewrite diagpart_diag.
  by rewrite sum_shift_trace mulrC.
rewrite mulr0n mulr0 big1 ?mulr0 // => b _.
apply: diagpart_off; apply/negP => /eqP h.
apply: hij; apply: (can_inj (omod_add_can b)).
by rewrite [((b : nat) + i)%N]addnC [((b : nat) + j)%N]addnC.
Qed.

(* --- FULL TWO-INDEX WEYL AVERAGE --- *)

Theorem weyl_average (X : 'M[F]_n) :
  ((n%:R : F) * n%:R)^-1 *:
    \sum_(b < n) \sum_(a < n)
      (shift ^+ b *m (clock ^+ a *m X *m clock ^+ (n - a)) *m shift ^+ (n - b))
  = (\tr X / n%:R) *: 1%:M.
Proof.
have hclock : \sum_(a < n) (clock ^+ a *m X *m clock ^+ (n - a))
            = n%:R *: diagpart X.
  by rewrite -clock_average scalerA (divff nF_neq0) scale1r.
have hstep : forall b : 'I_n,
   \sum_(a < n)
     (shift ^+ b *m (clock ^+ a *m X *m clock ^+ (n - a)) *m shift ^+ (n - b))
   = n%:R *: (shift ^+ b *m diagpart X *m shift ^+ (n - b)).
  move=> b.
  by rewrite -mulmx_suml -mulmx_sumr hclock -scalemxAr -scalemxAl.
under eq_bigr => b _ do rewrite hstep.
rewrite -scaler_sumr scalerA invfM (mulfVK nF_neq0).
exact: shift_average_diag.
Qed.

End Weyl.

Print Assumptions geom_sum.
Print Assumptions char_sum.
Print Assumptions weyl_character_sum.
Print Assumptions clock_pow_inv.
Print Assumptions clock_average.
Print Assumptions shift_pow_inv.
Print Assumptions weyl_commutation.
Print Assumptions shift_average_diag.
Print Assumptions weyl_average.
