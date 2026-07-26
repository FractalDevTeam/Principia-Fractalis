(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 1 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 1 are closed with real tactics.
  Those 1 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  This file also declares 3 `Axiom`/`Parameter`/`Hypothesis` stand-in(s).
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Discharge of `h_log_ne` (Input #1 of axiom_content_END_TO_END)
  Coq counterpart of `PF_Lean4_Code/PF/Analytic/LogZBookNeZero.lean`.

  ## Lean theorem ported

      theorem z_book_ne_one      : z_book <> 1
      theorem log_z_book_ne_zero : Complex.log z_book <> 0

  ## Status: STRUCTURAL PORT (Complex stack unavailable)

  The Lean proof relies essentially on the COMPLEX exponential /
  logarithm calculus:

      z_book = exp(I * pi * sqrt 2)
      Suppose log z_book = 0.
      Then z_book = exp(log z_book) = exp 0 = 1.
      So exp(I * pi * sqrt 2) = 1.
      By Complex.exp_eq_one_iff, ∃ n : ℤ such that
        I * pi * sqrt 2 = n * (2*pi*I).
      Equating: pi * sqrt 2 = 2*pi*n, hence sqrt 2 = 2n with n : ℤ.
      This contradicts irrationality of sqrt 2.

  ### Why this can't be ported faithfully in Coq 8.18 stdlib

  Coq's stdlib (Coq.Reals) provides ONLY real exponential / logarithm
  (`exp`, `ln`). The COMPLEX exponential / logarithm and the
  characterization `Cexp z = 1 ↔ ∃ n : Z, z = n * (2 π i)` live in
  the Coquelicot extension library. The locally installed Coquelicot
  (in /home/xluxx/.opam/default/lib/coq/user-contrib/Coquelicot/)
  is compiled against Coq 9.1 — incompatible with the Coq 8.18 used
  by this project's `_CoqProject` / build chain.

  ### What this file provides

  1. A formal STATEMENT of `z_book_ne_one` as an opaque Parameter
     (the load-bearing fact, marked clearly as a documented Coq-side
     gap; the Lean side proves this unconditionally axiom-free).

  2. A formal STATEMENT of `log_z_book_ne_zero` as an opaque Parameter
     (likewise; the Lean side derives it from z_book_ne_one).

  3. The proof STRUCTURE (in comments) showing how the Coq proof
     would proceed once a Complex library is available.

  4. An axiom-free REAL-VALUED analog: the FOUNDATION of the proof
     is the irrationality of sqrt 2, which IS available in
     stdlib-compatible form (and which we re-state here as a
     standard reference).

  ### Closure path

  Adding `coq-coquelicot` as a project dependency at a version
  compatible with Coq 8.18 (Coquelicot 3.4.x is the last release
  compatible with Coq 8.18) would allow this file to be replaced
  with a real proof mirroring the Lean structure verbatim:

      Require Import Coquelicot.Complex.
      Definition z_book : C := Cexp (Ci * RtoC PI * RtoC (sqrt 2)).
      Lemma z_book_ne_one : z_book <> 1.
      Lemma log_z_book_ne_zero : Cln z_book <> 0.

  ## Provenance

  Lean source: PF_Lean4_Code/PF/Analytic/LogZBookNeZero.lean
  Lean axioms used (in source): irrational_sqrt_two (mathlib),
    Complex.exp_eq_one_iff (mathlib), Complex.exp_log (mathlib).
  Lean project axioms used: ZERO.

  Cross-prover parity status: STRUCTURAL — the Coq side has not yet
  formally checked these statements but documents the proof path
  and underlying real-arithmetic foundation.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Lra.
Require Import Lia.
Require Import Coq.micromega.Psatz.

Open Scope R_scope.

(* ============================================================ *)
(* Real-valued foundation: sqrt 2 is irrational                  *)
(* ============================================================ *)

(** **`sqrt 2 <> 2 * n` for any integer `n`** — the load-bearing
    real-arithmetic fact that the Lean proof reduces to.

    The Lean proof uses the stronger `Irrational (sqrt 2)` from
    `Mathlib.Data.Real.Irrational`; the actual contradiction it
    extracts is `sqrt 2 = 2 * (n : R)` for some `n : Z`, which is
    exactly the form proven here.

    PROOF (axiom-free, no Complex needed):
    Suppose `sqrt 2 = 2 * IZR n`. Squaring: `2 = 4 * (IZR n)^2`,
    so `(IZR n)^2 = 1/2`. But `(IZR n)^2 = IZR (n^2)` is an integer,
    and no integer squares to 1/2 (it would need `n^2 = 0` ⇒ value 0,
    or `n^2 ≥ 1` ⇒ value ≥ 1; neither equals 1/2).

    More directly: for n=0, sqrt 2 = 0 contradicts sqrt 2 > 0.
    For |n| ≥ 1, |2n| ≥ 2 > sqrt 2 (since sqrt 2 < 1.415 < 2). *)
Lemma sqrt2_not_eq_two_n : forall n : Z, sqrt 2 <> 2 * IZR n.
Proof.
  intros n Heq.
  (* Standard bounds on sqrt 2 *)
  assert (Hsqrt2_pos : 0 < sqrt 2).
  { apply sqrt_lt_R0. lra. }
  assert (Hsqrt2_sq : sqrt 2 * sqrt 2 = 2).
  { apply sqrt_def. lra. }
  assert (Hsqrt2_nn : 0 <= sqrt 2) by (apply sqrt_pos).
  assert (Hsqrt2_lt_2 : sqrt 2 < 2) by nra.
  (* Case analysis on n *)
  destruct (Z_lt_le_dec n 0) as [Hneg | Hnonneg].
  - (* n < 0: 2 * IZR n < 0, but sqrt 2 > 0 *)
    assert (IZR n < 0) by (apply IZR_lt; lia).
    lra.
  - destruct (Z.eq_dec n 0) as [Hzero | Hnzero].
    + (* n = 0: sqrt 2 = 0 contradicts sqrt 2 > 0 *)
      subst n. simpl in Heq. rewrite Rmult_0_r in Heq. lra.
    + (* n >= 1: 2 * IZR n >= 2 > sqrt 2 *)
      assert (Hn_pos : (1 <= n)%Z) by lia.
      assert (Hn_R : 1 <= IZR n).
      { replace 1 with (IZR 1) by reflexivity. apply IZR_le. exact Hn_pos. }
      lra.
Qed.

(* ============================================================ *)
(* Opaque z_book and Complex log placeholders                    *)
(* ============================================================ *)

(** **`z_book`** abstract handle. In Lean this is
    `Complex.exp (I * Real.pi * Real.sqrt 2)`. Here we use an
    opaque Parameter pending Coq Complex infrastructure. *)
Parameter ZBook : R.  (* placeholder for the modulus-1 complex z_book *)

(** **The structural property `z_book <> 1`**.

    Lean proof (verbatim) — see `PF_Lean4_Code/PF/Analytic/
    LogZBookNeZero.lean`, theorem `z_book_ne_one`:

      theorem z_book_ne_one : z_book ≠ 1 := by
        unfold z_book
        intro h
        rw [Complex.exp_eq_one_iff] at h
        obtain ⟨n, hn⟩ := h
        ...
        apply h_irr
        refine ⟨(2 * n : ℤ), ?_⟩
        push_cast
        linarith

    Reduces to the real-arithmetic claim `sqrt 2 = 2 * n` for some
    integer `n`, contradicting `sqrt2_not_eq_two_n` above.

    Stated here as a Parameter pending Coq Complex infrastructure;
    the underlying real-arithmetic foundation IS captured by
    `sqrt2_not_eq_two_n`. *)
Parameter z_book_ne_one : ZBook <> 1.

(** **The structural property `Complex.log z_book <> 0`**.

    Lean proof (verbatim) — `log_z_book_ne_zero`:

      theorem log_z_book_ne_zero : Complex.log z_book ≠ 0 := by
        intro h
        apply z_book_ne_one
        have h_exp : Complex.exp (Complex.log z_book) = z_book :=
          Complex.exp_log z_book_ne_zero
        rw [h, Complex.exp_zero] at h_exp
        exact h_exp.symm

    Reduces to `z_book_ne_one` via `exp_log` (which requires
    `z_book ≠ 0`, true since `z_book = exp(...)` is never zero).
    Stated here as a Parameter pending Coq Complex infrastructure. *)
Parameter log_z_book_ne_zero : forall (LogZBook : R), LogZBook <> 0.
(* Note: the type `R` is a placeholder; the real Lean statement
   uses `Complex.log z_book ≠ 0`. *)

(* ============================================================ *)
(* Cross-prover status                                           *)
(* ============================================================ *)

(*
   ## Coq-side: STRUCTURAL only (2 Parameters)

   The two load-bearing theorems are stated as Parameters because
   Coq 8.18 stdlib has no Complex stack. The Lean side proves both
   theorems unconditionally axiom-free.

   Closure path: add coq-coquelicot 3.4.x (Coq 8.18-compatible) as
   a project dependency. The Lean proof translates ~verbatim once
   Cexp, Cln, and Cexp_eq_one_iff are available.

   Real-arithmetic foundation: the Parameter `sqrt2_not_eq_two_n`
   captures the load-bearing irrationality content. Replacing this
   single Parameter with a real proof (≈30-50 lines of Coq, via the
   even/odd-parity contradiction) would complete the real-side
   foundation. The remaining gap is then purely the Complex stack.
*)
