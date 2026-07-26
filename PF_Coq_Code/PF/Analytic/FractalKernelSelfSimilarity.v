(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 2 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 2 are closed with real tactics.
  Those 2 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Fractal Kernel Self-Similarity Identity (Coq port)

  Coq counterpart of `PF_Lean4_Code/PF/IntegralKernel/FractalKernelSelfSimilarity.lean`
  (Lean commit c0e80f0, 2026-05-22, Brick 1).

  The Ch 21 fractal kernel `K_α(t) = Σ a^(-n) cos(π·α^n·t)` viewed as
  a function of the scalar distance `t` satisfies the structural
  SELF-SIMILARITY:

    **K_α(t/α) = (1/a) · K_α(t) + cos(π·t/α)**

  This is the source of the 1/α factor in the conjectured ground-state
  formula λ_0(H_α) = π/(10·α).

  ## Coq-specific notes

  The Lean version uses `tsum` over ℕ (mathlib infinite sums). Coq
  stdlib has `Series` (a different presentation). Rather than wrestle
  with summability machinery, this port FORMALIZES THE FINITE PARTIAL
  SUMS of K_α and proves the self-similarity for them at the index-
  shift level. This captures the structural content: the kernel's
  arithmetic obeys the self-similar recursion at every truncation,
  hence (by uniform convergence on bounded a < α) at the limit.

  Specifically we prove:
    * `fractalKernelDistTerm α a t n` — pointwise summand
    * `fractalKernelDistTerm_succ_at_scaled` — INDEX-SHIFT identity:
        `term(α, a, t/α, n+1) = (1/a) · term(α, a, t, n)`

  The full tsum-level self-similarity follows from this index shift
  + summability + the n=0 residual = cos(π·t/α). The index-shift
  identity is the substantive algebraic content; that's what we
  port here.

  Status: axiom-free at the project level.
*)

Require Import Coq.Reals.Reals.
Require Import Lra.
Require Import Coq.micromega.Psatz.

Open Scope R_scope.

(* ============================================================ *)
(* The fractal kernel summand                                   *)
(* ============================================================ *)

(** **The fractal kernel summand at depth n** as a function of the
    scalar distance `t : R`. Coq stdlib has `pow` for nat-indexed
    powers; we use `INR n` for natural-number coercion to R. *)
Definition fractalKernelDistTerm (alpha a t : R) (n : nat) : R :=
  / (a ^ n) * cos (PI * (alpha ^ n) * t).

(* ============================================================ *)
(* Index-shift identity (the substantive content of Brick 1)    *)
(* ============================================================ *)

(** **Index-shift identity at scaled distance**:

      term(α, a, t/α, n+1) = (1/a) · term(α, a, t, n)

    Algebraic derivation:
      term(α, a, t/α, n+1)
        = (1/a^(n+1)) · cos(π·α^(n+1)·(t/α))
        = (1/a^(n+1)) · cos(π·α^n·t)         [α^(n+1)·(t/α) = α^n·t]
        = (1/a) · (1/a^n) · cos(π·α^n·t)
        = (1/a) · term(α, a, t, n).

    Requires `α ≠ 0` and `a ≠ 0`. *)
Theorem fractalKernelDistTerm_succ_at_scaled
    (alpha a t : R) (n : nat)
    (h_alpha : alpha <> 0) (h_a : a <> 0) :
  fractalKernelDistTerm alpha a (t / alpha) (S n) =
    (/ a) * fractalKernelDistTerm alpha a t n.
Proof.
  unfold fractalKernelDistTerm.
  (* LHS: (1/a^(n+1)) · cos(π·α^(n+1)·(t/α))
     RHS: (1/a) · (1/a^n) · cos(π·α^n·t)

     Key step: α^(n+1)·(t/α) = α^n·t, so cos arguments match. *)
  assert (h_cos_arg :
      alpha ^ (S n) * (t / alpha) = alpha ^ n * t).
  { simpl. field. exact h_alpha. }
  assert (h_pi_arg :
      PI * alpha ^ (S n) * (t / alpha) = PI * alpha ^ n * t).
  { rewrite Rmult_assoc, h_cos_arg, <- Rmult_assoc. reflexivity. }
  rewrite h_pi_arg.
  (* Now: (1/a^(n+1)) · cos(...) = (1/a) · (1/a^n) · cos(...) *)
  assert (h_pow_succ : a ^ (S n) = a * a ^ n).
  { simpl. reflexivity. }
  rewrite h_pow_succ.
  field.
  split.
  - apply pow_nonzero. exact h_a.
  - exact h_a.
Qed.

(* ============================================================ *)
(* Specialization at α = √2 (the P-class value)                 *)
(* ============================================================ *)

Require Import Coq.Reals.R_sqrt.

(** **Specialization at α = √2** — the canonical P-class resonance
    value (Ch 21). *)
Theorem fractalKernelDistTerm_succ_at_scaled_sqrt_two
    (a t : R) (n : nat) (h_a : a <> 0) :
  fractalKernelDistTerm (sqrt 2) a (t / sqrt 2) (S n) =
    (/ a) * fractalKernelDistTerm (sqrt 2) a t n.
Proof.
  apply fractalKernelDistTerm_succ_at_scaled.
  - apply Rgt_not_eq, sqrt_lt_R0. lra.
  - exact h_a.
Qed.
