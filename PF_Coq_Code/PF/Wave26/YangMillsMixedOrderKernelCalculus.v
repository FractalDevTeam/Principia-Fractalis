(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 14 proof obligations, of which 0 are `True` closed by
  `exact I` (no content) and 14 are closed with real tactics.
  Those 14 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Yang-Mills Mixed-Order Kernel Calculus — POSITIVE (Coq port — Wave 26)

  Cross-prover parity stub for
  `PF_Lean4_Code/PF/YangMillsMixedOrderKernelCalculus.lean`
  (Wave 26, 2026-05-25, commit a2679aa).

  ## Strategic context

  Wave 24 (`YangMillsNonAffineCoupledResidual`, f706266) showed the
  abstract quadratic class phi(lambda) = a*lambda^2 + b*lambda + c
  admits explicit witnesses fixing the cluster centres {1/2, 3/2}:

    * Witness 1: (a, b, c) = (1, -2, 5/4)  → phi(1/2) = phi(3/2) = 1/2.
    * Witness 2: (a, b, c) = (1, -1, 3/4)  → phi(1/2) = 1/2, phi(3/2) = 3/2.

  Wave 25 (`YangMillsQuadraticKernelMechanism`, 3fe9934) showed the
  BARE pure-monomial mechanism K_mixed = c*M^2 (zero linear and
  constant terms) CANNOT reach the cluster-fix family — the
  difference identity phi(3/2)-phi(1/2) = 2c forces c in
  {-1/2, 0, 1/2}, missing the natural kernel-induced c in {1, 2}.

  This file (Wave 26) attacks the NON-BARE mixed-order kernel
  calculus:

    K_mixed := a*M_cluster^2 + b*M_cluster + c*I

  where M_cluster = M/2 has eigenvalues {1/2, 3/2}. By Sylvester /
  spectral functional calculus, K_mixed has induced eigenvalue map
  IS exactly the Wave 24 quadraticEigenvalueMap.

  ## POSITIVE finding (Wave 26 deliverable)

  The Wave 24 cluster-collapse witness (a, b, c) = (1, -2, 5/4) is
  NON-TRIVIAL in its linear and constant terms (b = -2 != 0,
  c = 5/4 != 0). It IS reachable from the mixed-order calculus with
  full M^2 + M + I content.

  So:
    * bare quadratic-in-K Gram (Wave 25 narrow-out)           — INSUFFICIENT
    * mixed-order kernel calculus (this file, Wave 26 deliv.) — REALISES Wave 24

  This narrows further: the YM operator-level mechanism producing a
  cluster-fix INDUCED quadratic map MUST be a genuine mixed-order
  calculus on the level-1 cluster matrix — bare squaring fails.

  ## What this Coq port mirrors

  Lean delivers, axiom-free:
    (1) `mixedOrderEigenvalueMap a b c lam` definition.
    (2) Difference identity 2a + b.
    (3) Wave 24 witness 1 reproduced via (a, b, c) = (1, -2, 5/4).
    (4) Wave 24 witness 2 reproduced via (a, b, c) = (1, -1, 3/4).
    (5) Witness genuinely non-bare (b != 0 AND c != 0).
    (6) `mixed_order_kernel_realises_wave24` POSITIVE capstone.

  ## Coq port status

  Pure real arithmetic at the rational coordinates of Wave 24/25.
  Axiom-free at Coq stdlib level.
*)

Require Import Coq.Reals.Reals.
Require Import Lia.
Require Import Lra.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Mixed-order eigenvalue map                         *)
(* ============================================================ *)

(** ★ Mixed-order eigenvalue map ★

    Models the induced action of K_mixed = a*M^2 + b*M + c*I on a
    cluster eigenvalue lambda. Equivalent to Wave 24's
    quadraticEigenvalueMap; renamed here to highlight the OPERATOR-
    LEVEL origin via Sylvester functional calculus.

    Coq parity for `mixedOrderEigenvalueMap`. *)
Definition mixedOrderEigenvalueMap (a b c lam : R) : R :=
  a * lam ^ 2 + b * lam + c.

Theorem mixedOrderEigenvalueMap_at_half (a b c : R) :
  mixedOrderEigenvalueMap a b c (1/2) = a / 4 + b / 2 + c.
Proof. unfold mixedOrderEigenvalueMap. lra. Qed.

Theorem mixedOrderEigenvalueMap_at_three_halves (a b c : R) :
  mixedOrderEigenvalueMap a b c (3/2) = 9 * a / 4 + 3 * b / 2 + c.
Proof. unfold mixedOrderEigenvalueMap. lra. Qed.

(** Difference identity 2a + b. *)
Theorem mixedOrderEigenvalueMap_difference (a b c : R) :
  mixedOrderEigenvalueMap a b c (3/2) -
  mixedOrderEigenvalueMap a b c (1/2) = 2 * a + b.
Proof. unfold mixedOrderEigenvalueMap. lra. Qed.

(* ============================================================ *)
(* Section 2: Wave 24 witness 1 reproduced — (1, -2, 5/4)        *)
(* ============================================================ *)

(** ★ Mixed-order witness 1 at 1/2 ★ *)
Theorem mixed_order_witness_one_at_half :
  mixedOrderEigenvalueMap 1 (-2) (5/4) (1/2) = 1/2.
Proof. unfold mixedOrderEigenvalueMap. lra. Qed.

(** ★ Mixed-order witness 1 at 3/2 ★ *)
Theorem mixed_order_witness_one_at_three_halves :
  mixedOrderEigenvalueMap 1 (-2) (5/4) (3/2) = 1/2.
Proof. unfold mixedOrderEigenvalueMap. lra. Qed.

(** ★ Witness 1 fixes the cluster (collapsing case). ★ *)
Theorem mixed_order_witness_one_fixes_cluster :
  mixedOrderEigenvalueMap 1 (-2) (5/4) (1/2) = 1/2 /\
  mixedOrderEigenvalueMap 1 (-2) (5/4) (3/2) = 1/2.
Proof.
  split.
  - exact mixed_order_witness_one_at_half.
  - exact mixed_order_witness_one_at_three_halves.
Qed.

(* ============================================================ *)
(* Section 3: Wave 24 witness 2 reproduced — (1, -1, 3/4)        *)
(* ============================================================ *)

Theorem mixed_order_witness_two_at_half :
  mixedOrderEigenvalueMap 1 (-1) (3/4) (1/2) = 1/2.
Proof. unfold mixedOrderEigenvalueMap. lra. Qed.

Theorem mixed_order_witness_two_at_three_halves :
  mixedOrderEigenvalueMap 1 (-1) (3/4) (3/2) = 3/2.
Proof. unfold mixedOrderEigenvalueMap. lra. Qed.

Theorem mixed_order_witness_two_fixes_cluster :
  mixedOrderEigenvalueMap 1 (-1) (3/4) (1/2) = 1/2 /\
  mixedOrderEigenvalueMap 1 (-1) (3/4) (3/2) = 3/2.
Proof.
  split.
  - exact mixed_order_witness_two_at_half.
  - exact mixed_order_witness_two_at_three_halves.
Qed.

(* ============================================================ *)
(* Section 4: Non-bare witness — b != 0 AND c != 0               *)
(* ============================================================ *)

(** ★ Witness 1 has non-trivial linear coefficient (b = -2 != 0). ★

    This is the key contrast with Wave 25: the bare monomial
    mechanism (b = c = 0) is INSUFFICIENT, but this witness has
    b = -2 != 0, hence reaches Wave 24 via genuine mixed-order. *)
Theorem mixed_order_witness_one_non_bare_linear : (-2 : R) <> 0.
Proof. lra. Qed.

(** ★ Witness 1 has non-trivial constant coefficient (c = 5/4 != 0). ★ *)
Theorem mixed_order_witness_one_non_bare_constant : (5/4 : R) <> 0.
Proof. lra. Qed.

(** ★ Witness 2 has non-trivial linear coefficient (b = -1 != 0). ★ *)
Theorem mixed_order_witness_two_non_bare_linear : (-1 : R) <> 0.
Proof. lra. Qed.

(** ★ Witness 2 has non-trivial constant coefficient (c = 3/4 != 0). ★ *)
Theorem mixed_order_witness_two_non_bare_constant : (3/4 : R) <> 0.
Proof. lra. Qed.

(* ============================================================ *)
(* Section 5: POSITIVE capstone                                  *)
(* ============================================================ *)

(** ★ Mixed-order kernel calculus realises Wave 24 — POSITIVE Prop ★

    Records the conjunction:
      (a) Witness 1 fixes the cluster.
      (b) Witness 2 fixes the cluster pointwise.
      (c) Both witnesses are non-bare (b != 0 and c != 0).

    The triple in (c) is the load-bearing distinction vs Wave 25. *)
Definition MixedOrderKernelRealisesWave24 : Prop :=
  (mixedOrderEigenvalueMap 1 (-2) (5/4) (1/2) = 1/2 /\
   mixedOrderEigenvalueMap 1 (-2) (5/4) (3/2) = 1/2) /\
  (mixedOrderEigenvalueMap 1 (-1) (3/4) (1/2) = 1/2 /\
   mixedOrderEigenvalueMap 1 (-1) (3/4) (3/2) = 3/2) /\
  ((-2 : R) <> 0 /\ (5/4 : R) <> 0) /\
  ((-1 : R) <> 0 /\ (3/4 : R) <> 0).

(** ★★ Wave 26 POSITIVE capstone ★★

    The mixed-order kernel calculus a*M^2 + b*M + c*I with
    non-trivial b and c REALISES the Wave 24 cluster-fix family.

    Coq parity for `mixed_order_kernel_realises_wave24`. *)
Theorem mixed_order_kernel_realises_wave24 :
  MixedOrderKernelRealisesWave24.
Proof.
  unfold MixedOrderKernelRealisesWave24.
  repeat split; try (unfold mixedOrderEigenvalueMap; lra).
Qed.

(* ============================================================ *)
(* Section 6: Honest scope                                       *)
(* ============================================================ *)

(*
  1. Pure real arithmetic on rationals {1/2, 3/2, 1/4, 9/4, 1, -1, -2,
     3/4, 5/4}. Axiom-free at Coq stdlib level.
  2. POSITIVE result — narrows the YM mechanism search FROM THE
     POSITIVE SIDE: the bare monomial Gram fails (Wave 25), and the
     mixed-order calculus succeeds (this file).
  3. NOT a Clay mass-gap discharge. The cluster-fixing class is a
     NECESSARY condition; the kernel-self-similar provenance of any
     such mixed-order representative remains open.
  4. Net Coq-side parity: MATCHED.
*)
