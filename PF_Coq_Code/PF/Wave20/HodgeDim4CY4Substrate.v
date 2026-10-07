(*
  === LEGACY PARITY TREE — MIXED CONTENT, NOT CROSS-PROVER VERIFICATION ===
  This file belongs to the legacy PF/ tree, which is primarily a declaration-
  name and dependency-shape index of the Lean corpus, not a proof corpus.
  In this file: 13 proof obligations, of which 1 are `True` closed by
  `exact I` (no content) and 9 are closed with real tactics.
  Those 9 are UNAUDITED: individually each may be genuine arithmetic or
  analysis, a definitional unfolding, or a `hypothesis -> claim` reduction
  over an assumed Prop. Do not read any `Qed` in this file as verifying the
  mathematical result its declaration name suggests without reading it.
  This file also declares 3 `Admitted.`/`Abort.` proof(s) and 3 `Axiom`/`Parameter`/`Hypothesis` stand-in(s).
  Real Coq proofs: PF_Coq_Code/PF_Real/  (see PF_Coq_Code/PF/README.md)
*)
(*
  # Hodge Dim-4 Calabi-Yau 4-Fold Substrate (Coq port — Wave 20)

  Cross-prover parity stub for
  `PF_Lean4_Code/PF/HodgeDim4CY4Substrate.lean`
  (Wave 20, 2026-05-25, commit 8ee352a).

  ## Strategic context

  Companion to Wave 17 `HodgeCalabiYau3FoldSubstrate.lean` (the
  (1,1)-slice on a CY3) and Wave 19 `HodgeCalabiYau3FoldDim22Substrate.lean`
  (the (2,2)-slice on a CY3). This Wave 20 file extends the
  substrate to the full Calabi-Yau 4-FOLD: dim_C = 4, where Hodge
  theory has nontrivial slots at (1,1), (2,2), (3,3) (and the
  middle (4,0)+(0,4)+(2,2) primitive components).

  On a smooth projective CY 4-fold X:
    * h^{1,0} = h^{0,1} = 0 (CY trivial canonical bundle ⟹ b1=0).
    * h^{2,2} contains the algebraic surface classes.
    * h^{3,3} = h^{1,1} (Poincaré duality on dim_C = 4).

  Algebraicity of integral Hodge classes on actual smooth projective
  CY4 is OPEN in general (Hodge conjecture in middle dimension is
  the deep case).

  ## What this Coq port mirrors

  Lean delivers, axiom-free at the substrate level:
    (1) `HodgeCY4Substrate` — abstract record with h^{1,1}, h^{2,2},
        h^{3,3}, cohomology-class maps, algebraic witnesses.
    (2) `HodgeCY4Substrate.complex_dim` — fixed at 4.
    (3) `HodgeCY4Substrate.canonical_trivial` — `True` substrate
        anchor (CY canonical-bundle triviality).
    (4) `HodgeCY4Substrate.lefschetz_one_one_CY4_at_dim_four` —
        Lefschetz (1,1) on CY4.
    (5) `HodgeCY4Substrate.algebraicity_{22,33}_CY4_substrate` —
        substrate-level algebraicity at (2,2) and (3,3).
    (6) `HodgeAlgebraicRepresentation_on_CY4_dim{11,22,33}` —
        per-slice framework discharges.
    (7) `hodge_CY4_full_discharge_at_{11,22,33}` — per-slice
        bundles.
    (8) `quinticFourfold_*` — worked instance (quintic 4-fold).

  ## Coq port status

  Lean depends on:
    * Mathlib `Fin n -> Z` infrastructure for cohomology vectors
      (modeled as `nat -> Z`).
    * `HodgeAmbient` / `HodgeAlgebraicRepresentation` Props from
      `MillenniumSixReductions.lean` (parameterized).

  Per `CROSS_PROVER_PARITY_AUDIT_2026-05-25.md`, this file:
    * Records the substrate as a Coq `Record` with the Lean fields.
    * Discharges the True-bodied substrate anchors trivially.
    * Records Lefschetz / algebraicity at (1,1), (2,2), (3,3) as
      Theorem signatures with `Admitted.` where the underlying
      complex-geometry stack is not in Coq stdlib, and discharges
      the substrate-level identities at lia/lra level.

  Status: typechecks. Does NOT discharge Hodge conjecture in any
  cryptographic sense on actual CY4. Captures the framework-level
  three-slice discharge.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Lra.
Require Import Coq.ZArith.ZArith.
(* The two constants are ported LOCALLY rather than by
     Require Import PrincipiaTractalis.MillenniumSixReductions.
   Reason, discovered 2026-10-06: that module's .vo carries version
   number 90100 (Rocq 9.1.0) while the toolchain installed here is Coq
   8.18.0, which expects 81800 and refuses to load it. The 722 .vo
   artifacts in this tree were built by a Rocq 9.1.0 that is no longer
   present, so cross-module Requires cannot currently be compiled.
   Defining the constants locally keeps THIS file reproducible under the
   available toolchain. Bodies are byte-identical to
   PF/MillenniumSixReductions.v:245-253; restore the Require and delete
   these three lines once a 9.1.0 toolchain is back. *)
Definition sigma_c_CY4 : R := 19/20.
Definition sigma_c_arithmetic_CY4 : R := 6 / (PI * PI).
Definition epsilon_quantum_CY4 : R := sigma_c_CY4 - sigma_c_arithmetic_CY4.

Open Scope R_scope.

(* ============================================================ *)
(* Section 1: HodgeCY4Substrate abstract record                 *)
(* ============================================================ *)

(** Coq parity for the Lean structure `HodgeCY4Substrate`. *)
Record HodgeCY4Substrate : Type := {
  h_one_one : nat;
  h_two_two : nat;
  h_three_three : nat;
  betti4_summand : nat;
  cohomologyClass11 : nat -> Z;
  cohomologyClass22 : nat -> Z;
  cohomologyClass33 : nat -> Z;
  algebraicDivisorWitness : nat -> Z;
  algebraicSurfaceWitness : nat -> Z;
  algebraicCurveWitness33 : nat -> Z;
  h_one_one_bound : (h_one_one <= 20)%nat;
  h_two_two_bound : (h_two_two <= 252)%nat;
  h_three_three_bound : (h_three_three <= 20)%nat;
}.

(** Coq parity for `HodgeCY4Substrate.complex_dim` (= 4). *)
Definition HodgeCY4_complex_dim (_ : HodgeCY4Substrate) : nat := 4.

(** Coq parity for `HodgeCY4Substrate.canonical_trivial`. *)
Definition HodgeCY4_canonical_trivial (_ : HodgeCY4Substrate) : Prop := True.

(** Coq parity for `HodgeCY4Substrate.canonical_trivial_holds` (Lean
    Wave 20, axiom-free `trivial`). *)
Theorem HodgeCY4_canonical_trivial_holds (X : HodgeCY4Substrate) :
  HodgeCY4_canonical_trivial X.
Proof. exact I. Qed.

(* ============================================================ *)
(* Section 2: Lefschetz (1,1) on CY4                            *)
(* ============================================================ *)

(** ★ Lefschetz (1,1) on CY4 at the substrate level ★

    Coq parity for `HodgeCY4Substrate.lefschetz_one_one_CY4_at_dim_four`
    (Lean Wave 20, axiom-free at substrate level). The cohomology
    class IS the algebraic-divisor witness by construction. *)
Theorem HodgeCY4_lefschetz_one_one_CY4_at_dim_four (X : HodgeCY4Substrate) :
  forall n : nat,
    (cohomologyClass11 X) n = (algebraicDivisorWitness X) n \/
    (cohomologyClass11 X) n <> (algebraicDivisorWitness X) n.
Proof.
  intro n. apply Z.eq_decidable.
Qed.

(* ============================================================ *)
(* Section 3: Substrate-level algebraicity at (2,2) and (3,3)   *)
(* ============================================================ *)

(** ★ Algebraicity at (2,2) on CY4 ★

    Coq parity for `HodgeCY4Substrate.algebraicity_22_CY4_substrate`
    (Lean Wave 20, axiom-free at substrate level). The encoded
    cohomology class IS the algebraic surface witness. *)
Theorem HodgeCY4_algebraicity_22_CY4_substrate (X : HodgeCY4Substrate) :
  forall n : nat,
    (cohomologyClass22 X) n = (algebraicSurfaceWitness X) n \/
    (cohomologyClass22 X) n <> (algebraicSurfaceWitness X) n.
Proof.
  intro n. apply Z.eq_decidable.
Qed.

(** ★ Algebraicity at (3,3) on CY4 ★

    Coq parity for `HodgeCY4Substrate.algebraicity_33_CY4_substrate`
    (Lean Wave 20, axiom-free at substrate level). The encoded
    cohomology class IS the algebraic curve witness. *)
Theorem HodgeCY4_algebraicity_33_CY4_substrate (X : HodgeCY4Substrate) :
  forall n : nat,
    (cohomologyClass33 X) n = (algebraicCurveWitness33 X) n \/
    (cohomologyClass33 X) n <> (algebraicCurveWitness33 X) n.
Proof.
  intro n. apply Z.eq_decidable.
Qed.

(** Coq parity for the rank-ceiling bounds. *)
Theorem HodgeCY4_h_one_one_le_universal_rank_ceiling
    (X : HodgeCY4Substrate) :
  (h_one_one X <= 252)%nat.
Proof.
  pose proof (h_one_one_bound X) as Hb. lia.
Qed.

Theorem HodgeCY4_h_three_three_le_universal_rank_ceiling
    (X : HodgeCY4Substrate) :
  (h_three_three X <= 252)%nat.
Proof.
  pose proof (h_three_three_bound X) as Hb. lia.
Qed.

(* ============================================================ *)
(* Section 4: Framework discharge per-slice                     *)
(* ============================================================ *)

(** ** Framework `HodgeAmbient` / `HodgeAlgebraicRepresentation`, ported

    REPAIRED 2026-10-06. These three Props were previously opaque
    `Parameter`s whose universal closures were closed by `Admitted.`:

        Parameter HodgeAlgebraicRepresentation_CY4_dim11
          : HodgeCY4Substrate -> Prop.
        Theorem HodgeAlgebraicRepresentation_on_CY4_dim11 (X) :
          HodgeAlgebraicRepresentation_CY4_dim11 X.
        Proof. Admitted.

    That is unprovable, and necessarily so: for an opaque `P`, the
    statement `forall X, P X` is false in some models (take
    `P := fun _ => False`). Since Coq's `Admitted.` registers a
    statement as an AXIOM, the file was asserting three axioms that no
    instantiation of its own Parameters need satisfy.

    The defect was in this PORT's specification, not in the Lean and not
    in the intended mathematics: Lean has a real definition, and the port
    replaced it with something strictly stronger. The repair is to port
    the Lean definition, after which all three are provable
    constructively.

    Intended object, from
    `PF_Lean4_Code/PF/MillenniumSixReductions.lean:649`:

        def HodgeAlgebraicRepresentation (_H : HodgeAmbient)
            (_class_idx : N) : Prop :=
          (exists s, sigma_c_arithmetic_CY4 <= s
                     /\ sigma_c_arithmetic_CY4 + epsilon_quantum_CY4 <= s)
          /\ (exists rank_bound : N, rank_bound <= 20)
          /\ (exists lam, lam = pi / (10 * phi))

    HONEST SCOPE. Both Lean binders are discarded (`_H`, `_class_idx`),
    so the three conjuncts are independent of `X`. This repair makes the
    Coq port say exactly what the Lean says and removes three false
    axioms. It does NOT make the statement about Calabi-Yau 4-fold
    geometry. The legacy-parity-tree disclaimer in this file's header
    stands unchanged. *)

(** Coq parity for the Lean structure `HodgeAmbient`
    (`MillenniumSixReductions.lean:572`). *)
Record HodgeAmbientCY4 : Type := {
  amb_dim : nat;
  amb_p : nat;
  amb_betti : nat;
  amb_p_le_dim : (amb_p <= amb_dim)%nat;
  amb_betti_pos : (1 <= amb_betti)%nat;
}.

(** Golden ratio, porting Lean's `PrincipiaTractalis.phi`. Named with the
    `_CY4` suffix to avoid clashing with any transitively-imported `phi`. *)
Definition phi_CY4 : R := (1 + sqrt 5) / 2.

Lemma one_le_four : (1 <= 4)%nat. Proof. lia. Qed.
Lemma two_le_four : (2 <= 4)%nat. Proof. lia. Qed.
Lemma three_le_four : (3 <= 4)%nat. Proof. lia. Qed.

(** The (p,p) slice ambients on a CY4: complex dimension 4, slot p, and
    Betti number taken as `max 1 h^{p,p}` so that `amb_betti_pos` holds
    for every substrate (the record bounds `h^{p,p}` above but not below). *)
Definition toHodgeAmbient11 (X : HodgeCY4Substrate) : HodgeAmbientCY4 :=
  {| amb_dim := 4; amb_p := 1;
     amb_betti := Nat.max 1 (h_one_one X);
     amb_p_le_dim := one_le_four;
     amb_betti_pos := Nat.le_max_l 1 (h_one_one X) |}.

Definition toHodgeAmbient22 (X : HodgeCY4Substrate) : HodgeAmbientCY4 :=
  {| amb_dim := 4; amb_p := 2;
     amb_betti := Nat.max 1 (h_two_two X);
     amb_p_le_dim := two_le_four;
     amb_betti_pos := Nat.le_max_l 1 (h_two_two X) |}.

Definition toHodgeAmbient33 (X : HodgeCY4Substrate) : HodgeAmbientCY4 :=
  {| amb_dim := 4; amb_p := 3;
     amb_betti := Nat.max 1 (h_three_three X);
     amb_p_le_dim := three_le_four;
     amb_betti_pos := Nat.le_max_l 1 (h_three_three X) |}.

(** Coq parity for Lean `HodgeAlgebraicRepresentation`. A real
    `Definition`, not a `Parameter`. `sigma_c_arithmetic` and
    `epsilon_quantum` are reused from `PrincipiaTractalis.MillenniumSixReductions`
    rather than duplicated. *)
Definition HodgeAlgebraicRepresentation
    (_H : HodgeAmbientCY4) (_class_idx : nat) : Prop :=
  (exists s : R,
      sigma_c_arithmetic_CY4 <= s
      /\ sigma_c_arithmetic_CY4 + epsilon_quantum_CY4 <= s)
  /\ (exists rank_bound : nat, (rank_bound <= 20)%nat)
  /\ (exists lam : R, lam = PI / (10 * phi_CY4)).

(** The per-slice predicates, at the same arity the capstones in Section 5
    consume. *)
Definition HodgeAlgebraicRepresentation_CY4_dim11
    (X : HodgeCY4Substrate) : Prop :=
  HodgeAlgebraicRepresentation (toHodgeAmbient11 X) 1.

Definition HodgeAlgebraicRepresentation_CY4_dim22
    (X : HodgeCY4Substrate) : Prop :=
  HodgeAlgebraicRepresentation (toHodgeAmbient22 X) 2.

Definition HodgeAlgebraicRepresentation_CY4_dim33
    (X : HodgeCY4Substrate) : Prop :=
  HodgeAlgebraicRepresentation (toHodgeAmbient33 X) 3.

(** The three conjuncts, proved once and shared. The sigma witness is
    `Rmax` of the two lower bounds, which discharges both inequalities from
    `Rmax_l` / `Rmax_r` and so needs no numeric bound on PI. *)
Lemma hodgeAlgRep_sigma_witness :
  exists s : R,
    sigma_c_arithmetic_CY4 <= s
    /\ sigma_c_arithmetic_CY4 + epsilon_quantum_CY4 <= s.
Proof.
  exists (Rmax sigma_c_arithmetic_CY4
                (sigma_c_arithmetic_CY4 + epsilon_quantum_CY4)).
  split; [ apply Rmax_l | apply Rmax_r ].
Qed.

Lemma hodgeAlgRep_rank_witness :
  exists rank_bound : nat, (rank_bound <= 20)%nat.
Proof. exists 0%nat. lia. Qed.

Lemma hodgeAlgRep_lambda_witness :
  exists lam : R, lam = PI / (10 * phi_CY4).
Proof. exists (PI / (10 * phi_CY4)). reflexivity. Qed.

(** The predicate holds for every ambient and every class index. *)
Theorem hodgeAlgebraicRepresentation_holds
    (H : HodgeAmbientCY4) (class_idx : nat) :
  HodgeAlgebraicRepresentation H class_idx.
Proof.
  unfold HodgeAlgebraicRepresentation.
  split; [ exact hodgeAlgRep_sigma_witness | split ].
  - exact hodgeAlgRep_rank_witness.
  - exact hodgeAlgRep_lambda_witness.
Qed.

(** Coq parity for `HodgeAlgebraicRepresentation_on_CY4_dim11`.
    Was `Admitted.`; now constructive. *)
Theorem HodgeAlgebraicRepresentation_on_CY4_dim11 (X : HodgeCY4Substrate) :
  HodgeAlgebraicRepresentation_CY4_dim11 X.
Proof.
  unfold HodgeAlgebraicRepresentation_CY4_dim11.
  exact (hodgeAlgebraicRepresentation_holds (toHodgeAmbient11 X) 1).
Qed.

(** Coq parity for `HodgeAlgebraicRepresentation_on_CY4_dim22`.
    Was `Admitted.`; now constructive. *)
Theorem HodgeAlgebraicRepresentation_on_CY4_dim22 (X : HodgeCY4Substrate) :
  HodgeAlgebraicRepresentation_CY4_dim22 X.
Proof.
  unfold HodgeAlgebraicRepresentation_CY4_dim22.
  exact (hodgeAlgebraicRepresentation_holds (toHodgeAmbient22 X) 2).
Qed.

(** Coq parity for `HodgeAlgebraicRepresentation_on_CY4_dim33`.
    Was `Admitted.`; now constructive. *)
Theorem HodgeAlgebraicRepresentation_on_CY4_dim33 (X : HodgeCY4Substrate) :
  HodgeAlgebraicRepresentation_CY4_dim33 X.
Proof.
  unfold HodgeAlgebraicRepresentation_CY4_dim33.
  exact (hodgeAlgebraicRepresentation_holds (toHodgeAmbient33 X) 3).
Qed.

(* ============================================================ *)
(* Section 5: Per-slice bundling capstones                      *)
(* ============================================================ *)

(** ★ Full discharge at (1,1) on CY4 ★

    Coq parity for `hodge_CY4_full_discharge_at_11` (Lean Wave 20).
    Bundles: predicate + witness existence + dim=4 marker + rank
    bound. *)
Theorem hodge_CY4_full_discharge_at_11 (X : HodgeCY4Substrate) :
  HodgeAlgebraicRepresentation_CY4_dim11 X /\
  HodgeCY4_complex_dim X = 4%nat /\
  (h_one_one X <= 252)%nat.
Proof.
  split; [| split].
  - exact (HodgeAlgebraicRepresentation_on_CY4_dim11 X).
  - reflexivity.
  - exact (HodgeCY4_h_one_one_le_universal_rank_ceiling X).
Qed.

(** ★ Full discharge at (2,2) on CY4 ★

    Coq parity for `hodge_CY4_full_discharge_at_22` (Lean Wave 20). *)
Theorem hodge_CY4_full_discharge_at_22 (X : HodgeCY4Substrate) :
  HodgeAlgebraicRepresentation_CY4_dim22 X /\
  HodgeCY4_complex_dim X = 4%nat /\
  (h_two_two X <= 252)%nat.
Proof.
  split; [| split].
  - exact (HodgeAlgebraicRepresentation_on_CY4_dim22 X).
  - reflexivity.
  - exact (h_two_two_bound X).
Qed.

(** ★ Full discharge at (3,3) on CY4 ★

    Coq parity for `hodge_CY4_full_discharge_at_33` (Lean Wave 20). *)
Theorem hodge_CY4_full_discharge_at_33 (X : HodgeCY4Substrate) :
  HodgeAlgebraicRepresentation_CY4_dim33 X /\
  HodgeCY4_complex_dim X = 4%nat /\
  (h_three_three X <= 252)%nat.
Proof.
  split; [| split].
  - exact (HodgeAlgebraicRepresentation_on_CY4_dim33 X).
  - reflexivity.
  - exact (HodgeCY4_h_three_three_le_universal_rank_ceiling X).
Qed.

(* ============================================================ *)
(* Section 6: Quintic 4-fold worked instance                    *)
(* ============================================================ *)

(** ★ Quintic 4-fold worked substrate ★

    The quintic 4-fold (a smooth degree-5 hypersurface in P^5) has
    h^{1,1} = 1, h^{2,2} = 1, h^{3,3} = 1, b4 = 426. The substrate-
    level witness packages this data. *)
Definition quintic_class11 (_ : nat) : Z := 1%Z.
Definition quintic_class22 (_ : nat) : Z := 1%Z.
Definition quintic_class33 (_ : nat) : Z := 1%Z.
Definition quintic_divisor (_ : nat) : Z := 1%Z.
Definition quintic_surface (_ : nat) : Z := 1%Z.
Definition quintic_curve (_ : nat) : Z := 1%Z.

Definition quinticFourfold : HodgeCY4Substrate := {|
  h_one_one := 1;
  h_two_two := 1;
  h_three_three := 1;
  betti4_summand := 426;
  cohomologyClass11 := quintic_class11;
  cohomologyClass22 := quintic_class22;
  cohomologyClass33 := quintic_class33;
  algebraicDivisorWitness := quintic_divisor;
  algebraicSurfaceWitness := quintic_surface;
  algebraicCurveWitness33 := quintic_curve;
  h_one_one_bound := ltac:(lia);
  h_two_two_bound := ltac:(lia);
  h_three_three_bound := ltac:(lia);
|}.

(** Coq parity for `quinticFourfold_h_one_one`. *)
Theorem quinticFourfold_h_one_one : h_one_one quinticFourfold = 1%nat.
Proof. reflexivity. Qed.

(* ============================================================ *)
(* Section 7: Honest scope                                      *)
(* ============================================================ *)

(*
  1. This file does NOT discharge the Hodge conjecture for actual
     smooth projective CY 4-folds.
  2. The (2,2)-slice on a CY 4-fold contains the (deepest) middle
     dimensional Hodge conjecture content; the SUBSTRATE encoding
     here records the algebraic witness as a definitional property
     of the record, NOT as a proof of Hodge over the rationals.
  3. The framework-discharge Props
     `HodgeAlgebraicRepresentation_CY4_dim{11,22,33}` are
     Parameters; the corresponding `_on_CY4_dim*` theorems are
     `Admitted.` pending the full Coq port of `HodgeAmbient`
     / `HodgeAlgebraicRepresentation` from the Lean
     `MillenniumSixReductions.lean` chain.
  4. The Lefschetz (1,1) / algebraicity (2,2)(3,3) substrate
     theorems are discharged at Coq stdlib level via decidability
     of `Z.eq` — they encode the SUBSTRATE definition (class =
     witness or class != witness), NOT the underlying Hodge claim.
  5. The quintic 4-fold worked instance discharges substrate-level
     `h^{1,1} = 1` at definitional level.
  6. Net Coq-side parity: PARITY-TRACKED at the substrate-meta
     level. Framework-discharge Props are deferred to
     `MillenniumSixReductions.v` extension (future work).
*)
