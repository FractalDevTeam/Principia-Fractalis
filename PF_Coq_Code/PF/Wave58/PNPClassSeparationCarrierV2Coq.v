(*
  # PNP Class Separation Carrier V2 -- Wave 58/59 (2026-06-04) COQ PORT

  Cross-prover STRUCTURAL parity mirror of the Lean refactor:
  `PF_Lean4_Code/PF/TuringEncoding/PNPClassSeparationCarrierV2.lean`.

  Lean namespace mirrored:
    `PrincipiaTractalis.PNPClassSeparationCarrierV2`
  encoded here as Coq Module `PNPClassSeparationCarrierV2`.

  ## Status

  V2 carrier refactor: the V1 Prop-valued decide field is replaced
  with a Bool-valued one, and `M.decides L x` becomes Bool equality
  `M.decide x = L x` (not Iff). This kills the universal-inhabitation
  carrier defect at the Iff-vs-Bool level. The `computability : True`
  placeholder remains — the refactor LOCALIZES the open content to a
  single named field, it does NOT discharge `Literal_P_neq_NP_V2`.

  Mirrored Lean theorems:
    - `class_P_subset_class_NP_V2` -- Cook 1971 P subset NP on V2.
    - `enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2`
      -- the typed equivalence with the literal P neq NP statement.
    - `class_P_typedV2_eq_univ_under_True_placeholder` -- honest
      scope: under the True placeholder, P_typed_V2 = univ.
    - `class_NP_typedV2_eq_univ_under_True_placeholder` -- corollary
      via Cook 1971.
    - `not_Literal_P_neq_NP_V2_under_True_placeholder` -- honest
      scope corollary.
    - `pnp_carrier_V2_honest_scope_capstone` -- bundles all three.

  ## What this file delivers (Coq side)

  1. `Input` placeholder type with a `size : Input -> nat` projection
     (mirrors the V1 Input carrier).
  2. `DecidableProblemV2 := Input -> bool`.
  3. `DeterministicMachineV2`, `NondeterministicMachineV2` Records.
  4. `decidesV2`, polynomial-time bounds.
  5. `class_P_typedV2`, `class_NP_typedV2`, `Literal_P_neq_NP_V2`,
     `EnumToClassSeparationBridgeV2` Props.
  6. Cook 1971 subset theorem + reduction-iff theorem.
  7. Honest-scope theorems (V2 still vacuous under True placeholder).
  8. Capstone Theorem bundling all three.

  ## Honest scope

  Cross-prover STRUCTURAL parity. The refactor REMOVES the
  Iff-vs-Bool carrier defect (carrier-level structural change) but
  does NOT discharge the literal P neq NP statement. The
  `computability : True` placeholder remains the explicit open
  content. NOT a Clay discharge.

  ## Coq libraries used

  - `Stdlib.Init.Datatypes` (bool)
  - `Stdlib.Arith.PeanoNat`, `Lia`
*)

From Coq Require Import PeanoNat Lia.
From Coq Require Import Classical.

(** Mirror Lean namespace `PrincipiaTractalis.PNPClassSeparationCarrierV2`. *)
Module PNPClassSeparationCarrierV2.

(** ## §1 -- The Input carrier

    Mirrors the V1 `Input` type with a `size` projection. We model it
    as an abstract record with a `size : nat` field. *)
Record Input : Type := mkInput {
  size : nat
}.

(** The trivial input (size 0). *)
Definition zeroInput : Input := mkInput 0.

(** ## §2 -- Bool-valued carrier

    Mirrors Lean `DecidableProblemV2 := Input -> Bool`. *)
Definition DecidableProblemV2 : Type := Input -> bool.

(** **V2 deterministic machine.** `decide` is Bool-valued; `runtime`
    is a natural-number cost function; `computability` is a placeholder
    Prop field documenting the future plug-in point for a real machine
    model (Coq's `Computable` or a custom Turing-machine encoding). *)
Record DeterministicMachineV2 : Type := mkDetMachineV2 {
  decideV2  : Input -> bool;
  runtimeV2 : Input -> nat;
  computabilityV2 : True
}.

(** **V2 nondeterministic machine.** `verify` is Bool-valued on
    `(input, certificate)` pairs; `runtime` likewise. *)
Record NondeterministicMachineV2 : Type := mkNondetMachineV2 {
  verifyNDV2  : Input -> Input -> bool;
  runtimeNDV2 : Input -> Input -> nat;
  computabilityNDV2 : True
}.

(** ## §3 -- V2 decides relation (Bool equality, not Iff) *)

(** Mirrors Lean
    `DeterministicMachineV2.decides M L x := M.decide x = L x`. *)
Definition decidesV2 (M : DeterministicMachineV2)
    (L : DecidableProblemV2) (x : Input) : Prop :=
  decideV2 M x = L x.

(** **V2 polynomial-time bound (deterministic).** *)
Definition polyBoundedV2 (M : DeterministicMachineV2) (c : nat) : Prop :=
  forall x : Input, runtimeV2 M x <= c * Nat.pow (size x + 1) c.

(** **V2 polynomial-time bound (nondeterministic verifier).** *)
Definition polyBoundedNDV2 (V : NondeterministicMachineV2) (c : nat) : Prop :=
  forall (x cert : Input),
    size cert <= c * Nat.pow (size x + 1) c ->
    runtimeNDV2 V x cert <= c * Nat.pow (size x + 1) c.

(** ## §4 -- Classes P and NP on V2 carrier *)

(** Mirrors Lean `class_P_typedV2`. *)
Definition class_P_typedV2 (L : DecidableProblemV2) : Prop :=
  exists (M : DeterministicMachineV2) (c : nat),
    polyBoundedV2 M c /\ (forall x : Input, decidesV2 M L x).

(** Mirrors Lean `class_NP_typedV2`. *)
Definition class_NP_typedV2 (L : DecidableProblemV2) : Prop :=
  exists (V : NondeterministicMachineV2) (c : nat),
    polyBoundedNDV2 V c /\
    (forall x : Input,
       L x = true <->
       exists cert : Input,
         size cert <= c * Nat.pow (size x + 1) c /\
         verifyNDV2 V x cert = true).

(** ## §5 -- The literal P neq NP statement (V2)

    Set-equality between classes is mirrored as predicate equality
    via functional extensionality at the Prop level. *)

(** Mirrors Lean `Literal_P_neq_NP_V2 := class_P_typedV2 <> class_NP_typedV2`. *)
Definition Literal_P_neq_NP_V2 : Prop :=
  ~ (forall L : DecidableProblemV2,
       class_P_typedV2 L <-> class_NP_typedV2 L).

(** Mirrors Lean `EnumToClassSeparationBridgeV2`. *)
Definition EnumToClassSeparationBridgeV2 : Prop :=
  exists L : DecidableProblemV2,
    class_NP_typedV2 L /\ ~ class_P_typedV2 L.

(** ## §6 -- Cook 1971 P subset NP on V2 carrier *)

(** Mirrors Lean `class_P_subset_class_NP_V2`. *)
Theorem class_P_subset_class_NP_V2 :
  forall L : DecidableProblemV2,
    class_P_typedV2 L -> class_NP_typedV2 L.
Proof.
  intros L hLP.
  destruct hLP as [M [c [hpoly hdec]]].
  exists (mkNondetMachineV2
            (fun x _ => decideV2 M x)
            (fun x _ => runtimeV2 M x)
            I), c.
  split.
  - (* polyBoundedNDV2: ignore certificate, fall back to det bound. *)
    intros x _cert _hcert. simpl.
    exact (hpoly x).
  - intros x. split.
    + (* L x = true -> exists cert, verifyNDV2 x cert = true. *)
      intros hxL.
      exists zeroInput.
      split.
      * simpl. apply Nat.le_0_l.
      * simpl.
        (* verify x zeroInput = decideV2 M x; hdec x : decideV2 M x = L x. *)
        unfold decidesV2 in hdec.
        rewrite (hdec x). exact hxL.
    + (* exists cert ... -> L x = true. *)
      intros [cert [_hsize hVerify]].
      simpl in hVerify.
      unfold decidesV2 in hdec.
      rewrite <- (hdec x). exact hVerify.
Qed.

(** ## §7 -- EnumToClassSeparationBridgeV2 iff Literal_P_neq_NP_V2 *)

(** Mirrors Lean
    `enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2`. *)
Theorem enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2 :
  EnumToClassSeparationBridgeV2 <-> Literal_P_neq_NP_V2.
Proof.
  unfold EnumToClassSeparationBridgeV2, Literal_P_neq_NP_V2.
  split.
  - (* (->) Given witness L in NP \ P, classes differ pointwise. *)
    intros [L [hNP hP]] heq.
    apply hP.
    apply (heq L). exact hNP.
  - (* (<-) Given classes differ, exhibit a witness. *)
    intros hne.
    (* Classical reasoning via contrapositive: assume no witness,
       derive that the two classes coincide pointwise, contradict hne. *)
    apply NNPP.
    intros h_no_witness.
    apply hne.
    intros L.
    split.
    + (* P -> NP via Cook 1971. *)
      intros hLP. exact (class_P_subset_class_NP_V2 L hLP).
    + (* NP -> P: contradiction from h_no_witness. *)
      intros hLNP.
      apply NNPP. intros hLnotP.
      apply h_no_witness.
      exists L. split; assumption.
Qed.

(** ## §8 -- Honest scope: vacuous under the True placeholder

    The `computability : True` placeholder admits the trivial-machine
    closure `mkDetMachineV2 L (fun _ => 0) I` which decides any L at
    `c = 0`, because `0 * (size x + 1) ^ 0 = 0`. *)

(** Mirrors Lean
    `class_P_typedV2_eq_univ_under_True_placeholder`. *)
Theorem class_P_typedV2_eq_univ_under_True_placeholder :
  forall L : DecidableProblemV2, class_P_typedV2 L.
Proof.
  intros L.
  exists (mkDetMachineV2 L (fun _ => 0) I), 0.
  split.
  - intros x. simpl. apply Nat.le_0_l.
  - intros x. unfold decidesV2. simpl. reflexivity.
Qed.

(** Mirrors Lean
    `class_NP_typedV2_eq_univ_under_True_placeholder`. *)
Theorem class_NP_typedV2_eq_univ_under_True_placeholder :
  forall L : DecidableProblemV2, class_NP_typedV2 L.
Proof.
  intros L.
  apply class_P_subset_class_NP_V2.
  exact (class_P_typedV2_eq_univ_under_True_placeholder L).
Qed.

(** Mirrors Lean
    `not_Literal_P_neq_NP_V2_under_True_placeholder`. *)
Theorem not_Literal_P_neq_NP_V2_under_True_placeholder :
  ~ Literal_P_neq_NP_V2.
Proof.
  unfold Literal_P_neq_NP_V2.
  intros h. apply h.
  intros L. split.
  - intros _. apply class_NP_typedV2_eq_univ_under_True_placeholder.
  - intros _. apply class_P_typedV2_eq_univ_under_True_placeholder.
Qed.

(** ## §9 -- V2 carrier honest-scope capstone

    Mirrors Lean `pnp_carrier_V2_honest_scope_capstone`. *)
Theorem pnp_carrier_V2_honest_scope_capstone :
  (* (1) Cook 1971 P subset NP on V2. *)
  (forall L : DecidableProblemV2,
     class_P_typedV2 L -> class_NP_typedV2 L) /\
  (* (2) Reduction theorem analog. *)
  (EnumToClassSeparationBridgeV2 <-> Literal_P_neq_NP_V2) /\
  (* (3) Honest scope: under True placeholder, Literal_P_neq_NP_V2 is False. *)
  (~ Literal_P_neq_NP_V2).
Proof.
  repeat split.
  - exact class_P_subset_class_NP_V2.
  - apply enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2.
  - apply enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2.
  - exact not_Literal_P_neq_NP_V2_under_True_placeholder.
Qed.

(** ## §10 -- Honest-scope marker *)

Definition honest_scope_coq_parity_only_not_a_discharge : Prop := True.

Theorem honest_scope_marker :
  honest_scope_coq_parity_only_not_a_discharge.
Proof. exact I. Qed.

End PNPClassSeparationCarrierV2.

(*
  ## File-level honest-scope commentary

  1. V2 refactors the V1 carrier from Prop-valued `decide` to
     Bool-valued `decide`. The `M.decides L x` relation becomes Bool
     equality `decideV2 M x = L x`.

  2. Cook 1971 P subset NP holds on V2 by ignoring the certificate.

  3. The reduction-iff theorem (EnumToClassSeparationBridgeV2 iff
     Literal_P_neq_NP_V2) holds via Cook 1971 + classical excluded
     middle (mirroring Lean's `push_neg` / `by_contra` chain).

  4. Honest scope: under the `computability : True` placeholder, the
     trivial machine `mkDetMachineV2 L (fun _ => 0) I` polynomially
     bounds at `c = 0` (since `0 * (size x + 1) ^ 0 = 0`) and decides
     L. Therefore `Literal_P_neq_NP_V2` is provably False on this
     carrier. NOT a refutation: the refactor's contribution is to
     LOCALIZE the open content to a single named field
     (`computabilityV2`) that a future plug-in of a real machine
     model must populate.

  5. NOT a Clay discharge. Cross-prover structural parity only.
*)
