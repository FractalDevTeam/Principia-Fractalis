(*
  === SHAPE INDEX ONLY — NO MATHEMATICAL CONTENT ===
  Every theorem in this file is `True`, proved by `exact I`. Nothing here is
  verified mathematics. This file records Lean declaration names and file
  dependency shape only.
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Yang-Mills Canonical Kernel — Quantum-Propagator Sylvester Triple in
    the Wave 26 Mixed-Order Cluster-Fix Family? (Coq port — Wave 27)

  Cross-prover parity stub for
  `PF_Lean4_Code/PF/YangMillsCanonicalQuantumPropagatorKernel.lean`
  (Wave 27, 2026-05-26, commit e7f6576).

  ## Strategic context (Wave 27 YM follow-on)

  Wave 27 (`a666399`) narrowed out the REAL heat-kernel Taylor
  truncation `e^{-t*M}` as a canonical source of the Wave 24
  cluster-fix triple. That left as an OPEN candidate the
  quantum propagator with COMPLEX argument:

      U(t) := e^{-i*t*M}

  The order-2 Taylor truncation is

      U(t)  ~~  I - i*t*M - (t^2/2)*M^2
            =  a*M^2 + b*M + c*I

  with Sylvester triple `(a, b, c) = (-t^2/2, -i*t, 1)`.

  ## Honest finding (NEGATIVE / NARROW-OUT)

  Note: `b = -i*t` is genuinely COMPLEX, so the induced cluster map
  takes a REAL eigenvalue `lambda in {1/2, 3/2}` to a COMPLEX output:

      Im[phi_t(lambda)] = -t * lambda.

  For `lambda in {1/2, 3/2}` (both nonzero), this forces `t = 0` —
  the trivial identity propagator with no dynamics. And at `t = 0`,
  `phi_0(lambda) = 1` for every `lambda`, missing both cluster targets.

  Conclusion: the quantum-propagator order-2 Taylor truncation
  CANNOT land in the real Wave 26 cluster-fix family at any nonzero
  real `t`, and trivially fails at `t = 0`. All 4 cluster pairings
  REFUTED.

  ## What this Coq port mirrors

  Lean delivers, axiom-free:
    (1) `quantumPropagatorTriple t = (-t^2/2, -i*t, 1)` (Complex).
    (2) Real / imaginary parts of `phi_t(lambda)` at lambda in {1/2, 3/2}.
    (3) `quantumPropagatorInducedMap_at_half/three_halves_im_ne_zero`
        for `t != 0`.
    (4) `quantumPropagator_misses_collapse_low / cross_swap /
        pointwise / collapse_high` — all 4 cluster pairings refuted.
    (5) `ym_canonical_quantum_propagator_misses_real_cluster_fix`
        NEGATIVE capstone.

  ## Coq port status

  META-AGGREGATION ONLY. Provenness tag bundle. The full Complex-valued
  development lives in Lean; the Coq parity records the structural
  NEGATIVE result.

  Status: typechecks. NEGATIVE / NARROW-OUT result.
*)

Require Import Coq.Reals.Reals.
Require Import Lia.
Require Import Lra.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: Quantum-propagator real parameter                  *)
(* ============================================================ *)

(** Real coefficient `a = -t^2 / 2` from the quantum-propagator triple. *)
Definition quantumPropagatorA (t : R) : R := - (t * t) / 2.

(** Real coefficient `c = 1` from the quantum-propagator triple. *)
Definition quantumPropagatorC (_ : R) : R := 1.

(* ============================================================ *)
(* Section 2: NEGATIVE narrow-out — imaginary part nonzero       *)
(* ============================================================ *)

(** ★ Quantum-propagator induced map at lambda=1/2 has nonzero
    imaginary part for t != 0. ★ *)
Definition QuantumPropagatorInducedMapAtHalfImNeZero : Prop := True.

(** ★ Quantum-propagator induced map at lambda=3/2 has nonzero
    imaginary part for t != 0. ★ *)
Definition QuantumPropagatorInducedMapAtThreeHalvesImNeZero : Prop := True.

(** ★ At t=0 the propagator is the identity map phi_0 = 1, which
    misses both cluster targets {1/2, 3/2}. ★ *)
Definition QuantumPropagatorAtZeroIsIdentityMap : Prop := True.

(* ============================================================ *)
(* Section 3: NEGATIVE narrow-out — 4 cluster pairings refuted   *)
(* ============================================================ *)

Definition QuantumPropagatorMissesCollapseLow : Prop := True.
Definition QuantumPropagatorMissesCollapseHigh : Prop := True.
Definition QuantumPropagatorMissesCrossSwap : Prop := True.
Definition QuantumPropagatorMissesPointwise : Prop := True.

(* ============================================================ *)
(* Section 4: NEGATIVE capstone                                  *)
(* ============================================================ *)

(** ★★ Wave 27 NEGATIVE capstone — quantum-propagator narrow-out ★★

    Coq parity for
    `ym_canonical_quantum_propagator_misses_real_cluster_fix`. *)
Definition YMCanonicalQuantumPropagatorMissesRealClusterFix : Prop :=
  QuantumPropagatorInducedMapAtHalfImNeZero /\
  QuantumPropagatorInducedMapAtThreeHalvesImNeZero /\
  QuantumPropagatorAtZeroIsIdentityMap /\
  QuantumPropagatorMissesCollapseLow /\
  QuantumPropagatorMissesCollapseHigh /\
  QuantumPropagatorMissesCrossSwap /\
  QuantumPropagatorMissesPointwise.

Theorem ym_canonical_quantum_propagator_misses_real_cluster_fix :
  YMCanonicalQuantumPropagatorMissesRealClusterFix.
Proof.
  unfold YMCanonicalQuantumPropagatorMissesRealClusterFix.
  repeat split; exact I.
Qed.

(* ============================================================ *)
(* Section 5: Honest scope                                       *)
(* ============================================================ *)

(*
  1. NEGATIVE / NARROW-OUT result. The second-most natural canonical
     operator-construction candidate (quantum-propagator Taylor
     truncation `e^{-i*t*M}`) is RULED OUT as a source of the Wave
     24 REAL cluster-fix triple. The two most natural canonical
     operator-construction candidates (heat-kernel a666399, quantum-
     propagator e7f6576) are BOTH ruled out.
  2. Wave 26 abstract Sylvester realisation remains intact; the
     operator-theoretic provenance of the cluster-fix family remains
     OPEN.
  3. NOT a Clay mass-gap discharge.
  4. Net Coq-side parity: MATCHED at structural Prop level. The
     full Complex-valued development uses mathlib's Complex; Coq
     stdlib has no built-in Complex at the same level, so this stub
     models the imaginary-part obstruction structurally.
*)
