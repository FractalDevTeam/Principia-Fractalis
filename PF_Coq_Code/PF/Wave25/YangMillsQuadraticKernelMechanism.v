(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 7 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 7 are closed with real tactics.
  Those 7 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Yang-Mills Quadratic Kernel Mechanism — NEGATIVE (Coq port — Wave 25)

  Cross-prover parity stub for
  `PF_Lean4_Code/PF/YangMillsQuadraticKernelMechanism.lean`
  (Wave 25, 2026-05-25, commit 3fe9934).

  ## Strategic context

  Wave 24 (`YangMillsNonAffineCoupledResidual`) showed the abstract
  quadratic class phi(lambda) = alpha*lambda^2 + beta*lambda + gamma
  is UNDERDETERMINED (2 eq, 3 unknowns) for fixing the YM cluster
  centres {1/2, 3/2}, with the load-bearing difference identity

    phi(3/2) - phi(1/2) = 2*alpha + beta in {-1, 0, 1}

  for cluster-fixing pairings.

  This file (Wave 25) asks: does the kernel-product Gram quadratic
  map phi_KK(lambda) := 2*lambda^2 (induced by M^2 where M is the
  level-1 cluster matrix [[2,-1],[-1,2]] with eigenvalues {1, 3} and
  cluster centres after the 1/2 rescaling at {1/2, 3/2}) hit the
  cluster-fixing set?

  ## Honest finding — NEGATIVE

  phi_KK(3/2) - phi_KK(1/2) = 2*c with c = 2 gives the difference 4,
  which is NOT in {-1, 0, 1}. The bare quadratic-in-K Gram mechanism
  M |-> M^2 does NOT produce a cluster-fixing quadratic.

  Similarly, the bare phi_K^2(lambda) := lambda^2 (c = 1) yields
  difference 2, also outside {-1, 0, 1}.

  General: for any monomial c*lambda^2 with c != 0, the difference
  is 2c; cluster-fixing requires c in {-1/2, 0, 1/2}, missing the
  natural kernel-induced c in {1, 2}.

  ## Strategic verdict (OUTCOME 5)

  NEGATIVE — bare quadratic-in-K Gram is INSUFFICIENT to reach the
  Wave 24 cluster-fix family. An affine combination a*M^2 + b*M + c*I
  is required (this is the Wave 26 follow-on YangMillsMixedOrderKernelCalculus).

  ## What this Coq port mirrors

  Lean delivers, axiom-free:
    (1) `kernelGramQuadratic c lam` definition.
    (2) `kernel_gram_quadratic_difference` (= 2c identity).
    (3) `kernel_gram_quadratic_bare_blocked` at c = 1.
    (4) `kernel_gram_quadratic_bare_blocked` at c = 2.
    (5) `quadratic_kernel_mechanism_narrowed` capstone (NEGATIVE).
*)

Require Import Coq.Reals.Reals.
Require Import Lia.
Require Import Lra.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: The bare kernel-Gram quadratic                     *)
(* ============================================================ *)

(** ★ Bare kernel-Gram quadratic ★

    Models the operator-level induced eigenvalue map
    lambda |-> c*lambda^2 where c is the kernel-induced rescaling
    (c = 1 for M^2 unrescaled, c = 2 for the natural cluster-scale
    Gram M^2/2 of [[2,-1],[-1,2]] with eigenvalues {1, 3}).

    Coq parity for `kernelGramQuadratic`. *)
Definition kernelGramQuadratic (c lam : R) : R :=
  c * lam ^ 2.

(** Evaluation at 1/2 and 3/2. *)
Theorem kernelGramQuadratic_at_half (c : R) :
  kernelGramQuadratic c (1/2) = c / 4.
Proof. unfold kernelGramQuadratic. lra. Qed.

Theorem kernelGramQuadratic_at_three_halves (c : R) :
  kernelGramQuadratic c (3/2) = 9 * c / 4.
Proof. unfold kernelGramQuadratic. lra. Qed.

(* ============================================================ *)
(* Section 2: Difference identity                                *)
(* ============================================================ *)

(** ★ Load-bearing difference identity ★

    phi(3/2) - phi(1/2) = 2c for the bare quadratic c*lambda^2.

    Coq parity for `kernel_gram_quadratic_difference`. *)
Theorem kernel_gram_quadratic_difference (c : R) :
  kernelGramQuadratic c (3/2) - kernelGramQuadratic c (1/2) = 2 * c.
Proof. unfold kernelGramQuadratic. lra. Qed.

(* ============================================================ *)
(* Section 3: NEGATIVE — kernel-induced c misses cluster set     *)
(* ============================================================ *)

(** ★ Cluster-fixing necessary condition: difference in {-1, 0, 1}. ★

    Equivalent to 2c in {-1, 0, 1}, i.e. c in {-1/2, 0, 1/2}. *)
Definition cluster_fixing_difference (d : R) : Prop :=
  d = -1 \/ d = 0 \/ d = 1.

(** ★ Bare M^2 (c = 1) — NEGATIVE. ★

    Difference 2 is not in {-1, 0, 1}.

    Coq parity for `kernel_gram_quadratic_bare_blocked_c1`. *)
Theorem kernel_gram_quadratic_bare_blocked_c1 :
  ~ cluster_fixing_difference
      (kernelGramQuadratic 1 (3/2) - kernelGramQuadratic 1 (1/2)).
Proof.
  rewrite kernel_gram_quadratic_difference.
  intros [H | [H | H]]; lra.
Qed.

(** ★ Natural cluster-scale c = 2 — NEGATIVE. ★

    Difference 4 is not in {-1, 0, 1}.

    Coq parity for `kernel_gram_quadratic_bare_blocked_c2`. *)
Theorem kernel_gram_quadratic_bare_blocked_c2 :
  ~ cluster_fixing_difference
      (kernelGramQuadratic 2 (3/2) - kernelGramQuadratic 2 (1/2)).
Proof.
  rewrite kernel_gram_quadratic_difference.
  intros [H | [H | H]]; lra.
Qed.

(** ★ Generic statement: cluster-fixing forces c in {-1/2, 0, 1/2}. ★

    Equivalently: for any c outside that finite set, the bare
    monomial c*lambda^2 fails to cluster-fix. *)
Theorem bare_quadratic_cluster_fixing_constrains_c (c : R) :
  cluster_fixing_difference
    (kernelGramQuadratic c (3/2) - kernelGramQuadratic c (1/2)) ->
  c = -1/2 \/ c = 0 \/ c = 1/2.
Proof.
  rewrite kernel_gram_quadratic_difference.
  intros [H | [H | H]].
  - left. lra.
  - right; left. lra.
  - right; right. lra.
Qed.

(* ============================================================ *)
(* Section 4: NEGATIVE capstone                                  *)
(* ============================================================ *)

(** ★ Quadratic kernel mechanism — narrowed-out Prop ★ *)
Definition QuadraticKernelMechanismNarrowed : Prop :=
  (~ cluster_fixing_difference
      (kernelGramQuadratic 1 (3/2) - kernelGramQuadratic 1 (1/2))) /\
  (~ cluster_fixing_difference
      (kernelGramQuadratic 2 (3/2) - kernelGramQuadratic 2 (1/2))).

(** ★★ Wave 25 NEGATIVE capstone ★★

    The bare quadratic-in-K Gram mechanism is INSUFFICIENT to fix
    the Wave 24 cluster centres for both natural kernel-induced
    rescalings c in {1, 2}.

    Coq parity for the Lean `quadratic_kernel_mechanism_narrowed`. *)
Theorem quadratic_kernel_mechanism_narrowed :
  QuadraticKernelMechanismNarrowed.
Proof.
  split.
  - exact kernel_gram_quadratic_bare_blocked_c1.
  - exact kernel_gram_quadratic_bare_blocked_c2.
Qed.

(* ============================================================ *)
(* Section 5: Honest scope                                       *)
(* ============================================================ *)

(*
  1. Pure real arithmetic on rationals at coordinates {1/2, 3/2, 1/4,
     9/4, 1, 2, 4}. Axiom-free at Coq stdlib level.
  2. NEGATIVE result — narrows the YM mechanism search; the bare
     quadratic-in-K Gram mechanism is now ruled out as a cluster-fix
     source.
  3. The natural next step (Wave 26): non-bare mixed-order kernel
     calculus a*M^2 + b*M + c*I — see
     `Wave26/YangMillsMixedOrderKernelCalculus.v`.
  4. NOT a discharge of any Millennium problem; this is a refinement
     of the mechanism search space.
  5. Net Coq-side parity: MATCHED.
*)
