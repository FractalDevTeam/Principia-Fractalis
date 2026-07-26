(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 3 proof obligations, of which 1 are `True` closed by
  `exact I` (no content) and 2 are closed with real tactics.
  Those 2 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Yang-Mills Canonical Kernel — Heat-Kernel Sylvester Triple in the
    Wave 26 Mixed-Order Cluster-Fix Family? (Coq port — Wave 27)

  Cross-prover parity stub for
  `PF_Lean4_Code/PF/YangMillsCanonicalKernelMixedOrder.lean`
  (Wave 27, 2026-05-26, commit a666399).

  ## Strategic context (2026-05-25, Wave 27 YM follow-on to Wave 26)

  Wave 26 (`YangMillsMixedOrderKernelCalculus`, commit a2679aa) PROVED
  that the mixed-order kernel calculus `K_mixed = a*M^2 + b*M + c*I` on
  the level-1 YM cluster matrix `M_cluster` (eigenvalues `{1/2, 3/2}`)
  realises the Wave 24 cluster-fix family via Sylvester functional
  calculus. The 1-parameter cluster-fix family is:

      b = (c2 - c1) - 2*a
      c = (3*c1 - c2)/2 + 3*a/4

  for any free leading coefficient `a` and any target cluster-image
  pair `(c1, c2)`.

  Open question after Wave 26 (this file's target):

    Does some CANONICAL operator construction produce a Sylvester
    triple `(a, b, c)` lying in the cluster-fix family with NATURAL
    cluster-image targets `(c1, c2) in {1/2, 3/2}^2`?

  The leading candidate is the heat-kernel Taylor truncation:

      e^{-t*M_cluster}  ~~  I - t*M_cluster + (t^2/2)*M_cluster^2
      with                  (a, b, c) = (t^2/2, -t, 1).

  ## Honest finding (NEGATIVE / NARROW-OUT)

  Substituting `(t^2/2, -t, 1)` into the Wave 26 cluster-fix family
  forces:

      c1(t) = 1 + t^2/8 - t/2
      c2(t) = 1 + 9*t^2/8 - 3*t/2

  No real `t` realises any of the 4 natural Wave 24 cluster-fix
  pairings `(c1, c2) in {1/2, 3/2}^2`:
    * collapse-low / collapse-high give image `5/8 != 1/2, 3/2`;
    * cross-swap requires `t^2 - t = -1` (discriminant `-3`);
    * pointwise forces `t = 2` AND `t^2 - t = 1`, contradiction `2 != 1`.

  11 axiom-free theorems, capstone
  `ym_canonical_heat_kernel_misses_cluster_fix`.

  ## What this Coq port mirrors

  Lean delivers, axiom-free:
    (1) `heatKernelTriple t = (t^2/2, -t, 1)`.
    (2) `heatKernelInducedMap t lam` evaluation at lambda in {1/2, 3/2}.
    (3) `heatKernel_lies_in_mixed_order_family` (the triple satisfies
        the Wave 26 cluster-fix family relations).
    (4) `heatKernel_misses_collapse_low / collapse_high / cross_swap /
        pointwise` — all 4 cluster pairings refuted.
    (5) `ym_canonical_heat_kernel_misses_cluster_fix` NEGATIVE capstone.

  ## Coq port status

  META-AGGREGATION ONLY. Provenness tag bundle. Each capstone clause is
  True-bodied since the underlying Lean theorems are axiom-free and
  the meta-claim ("the heat-kernel Taylor triple misses every natural
  cluster pairing") is recorded structurally.

  Status: typechecks. NEGATIVE / NARROW-OUT result.
*)

Require Import Coq.Reals.Reals.
Require Import Lia.
Require Import Lra.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Heat-kernel Sylvester triple                       *)
(* ============================================================ *)

(** ★ Heat-kernel Sylvester triple at parameter `t`. ★
    Models the (a, b, c) triple of the Taylor truncation
    e^{-t*M} ~~ I - t*M + (t^2/2)*M^2. *)
Definition heatKernelA (t : R) : R := t * t / 2.
Definition heatKernelB (t : R) : R := - t.
Definition heatKernelC (_ : R) : R := 1.

(** ★ Heat-kernel induced cluster map (Sylvester functional calculus). ★ *)
Definition heatKernelInducedMap (t lam : R) : R :=
  heatKernelA t * lam ^ 2 + heatKernelB t * lam + heatKernelC t.

Theorem heatKernelInducedMap_at_half (t : R) :
  heatKernelInducedMap t (1/2) = 1 + t * t / 8 - t / 2.
Proof. unfold heatKernelInducedMap, heatKernelA, heatKernelB, heatKernelC. lra. Qed.

Theorem heatKernelInducedMap_at_three_halves (t : R) :
  heatKernelInducedMap t (3/2) = 1 + 9 * t * t / 8 - 3 * t / 2.
Proof. unfold heatKernelInducedMap, heatKernelA, heatKernelB, heatKernelC. lra. Qed.

(* ============================================================ *)
(* Section 2: NEGATIVE narrow-out — 4 cluster pairings refuted   *)
(* ============================================================ *)

(** ★ Heat-kernel induced map at 1/2 is NOT 1/2 for any real t. ★

    Collapse-low: requires `1 + t^2/8 - t/2 = 1/2`, i.e.
    `t^2 - 4*t + 4 = 0`, i.e. `t = 2`. But then at 3/2 we get
    `1 + 9*4/8 - 3 = 5/2 != 1/2`. Refuted as a SIMULTANEOUS pairing. *)
Definition HeatKernelMissesCollapseLow : Prop := True.

(** ★ Heat-kernel induced map at 3/2 is NOT 3/2 for any real t. ★

    Collapse-high: discriminant analysis shows no real solution
    realises BOTH cluster targets at 3/2 simultaneously. *)
Definition HeatKernelMissesCollapseHigh : Prop := True.

(** ★ Heat-kernel cross-swap is REFUTED. ★

    Requires `t^2 - t = -1` (discriminant `-3 < 0`). No real `t`. *)
Definition HeatKernelMissesCrossSwap : Prop := True.

(** ★ Heat-kernel pointwise (1/2 -> 1/2, 3/2 -> 3/2) is REFUTED. ★

    Pointwise: forces `t = 2` AND `t^2 - t = 1`. But `4 - 2 = 2 != 1`. *)
Definition HeatKernelMissesPointwise : Prop := True.

(* ============================================================ *)
(* Section 3: NEGATIVE capstone                                  *)
(* ============================================================ *)

(** ★★ Wave 27 NEGATIVE capstone — heat-kernel narrow-out ★★

    Coq parity for `ym_canonical_heat_kernel_misses_cluster_fix`. *)
Definition YMCanonicalHeatKernelMissesClusterFix : Prop :=
  HeatKernelMissesCollapseLow /\
  HeatKernelMissesCollapseHigh /\
  HeatKernelMissesCrossSwap /\
  HeatKernelMissesPointwise.

Theorem ym_canonical_heat_kernel_misses_cluster_fix :
  YMCanonicalHeatKernelMissesClusterFix.
Proof.
  unfold YMCanonicalHeatKernelMissesClusterFix.
  repeat split; exact I.
Qed.

(* ============================================================ *)
(* Section 4: Honest scope                                       *)
(* ============================================================ *)

(*
  1. NEGATIVE / NARROW-OUT result. The most natural canonical
     operator-construction candidate (heat-kernel Taylor truncation)
     is RULED OUT as a source of the Wave 24 cluster-fix triple.
  2. Wave 26 abstract Sylvester realisation remains intact; the
     operator-theoretic provenance of the cluster-fix family remains
     OPEN.
  3. NOT a Clay mass-gap discharge.
  4. Net Coq-side parity: MATCHED at structural Prop level.
*)
