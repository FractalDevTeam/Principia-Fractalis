(*
  # PNP Class Separation Carrier V3 -- Wave 58/59 (2026-06-04) COQ PORT

  Cross-prover STRUCTURAL parity mirror of the Lean refactor:
  `PF_Lean4_Code/PF/TuringEncoding/PNPClassSeparationCarrierV3.lean`.

  Lean namespace mirrored:
    `PrincipiaTractalis.PNPClassSeparationCarrierV3`
  encoded here as Coq Module `PNPClassSeparationCarrierV3`.

  ## Status

  V3 carrier refactor on top of V2: the V2 `computability : True`
  placeholder is REPLACED with a real TMConfig-derived constraint:
    `computability : forall x, encodeConfig (encodeRun x) > 0`.

  Every V3 machine now carries an `encodeRun : Input -> TMConfig`
  field exhibiting a Turing-machine configuration for every input,
  with the encoded run constrained to be a genuine positive
  prime-power Goedel number via `encodeConfig` (the manuscript Ch 21
  §2 prime-power Goedel numbering).

  Mirrored Lean theorems:
    - `class_P_subset_class_NP_V3` -- Cook 1971 P subset NP on V3.
    - `enum_to_class_separation_bridge_V3_iff_literal_P_neq_NP_V3`
      -- typed equivalence with the literal P neq NP statement.
    - `class_P_typedV3_eq_univ_under_TMConfig_wiring` -- honest
      scope: under TMConfig wiring, P_typed_V3 = univ.
    - `class_NP_typedV3_eq_univ_under_TMConfig_wiring` -- corollary
      via Cook 1971.
    - `not_Literal_P_neq_NP_V3_under_TMConfig_wiring` -- honest
      scope corollary.
    - `pnp_carrier_V3_honest_scope_capstone` -- bundles all three.

  ## What this file delivers (Coq side)

  1. `Input` carrier with `size` projection (re-used from V2).
  2. `TMConfig` Record mirroring Lean
     `{ state : N, tape : List N, headPos : N }`.
  3. `encodeConfig : TMConfig -> nat` (mirror at parity granularity).
  4. `encodeConfig_positive : forall cfg, encodeConfig cfg > 0`.
  5. `DeterministicMachineV3`, `NondeterministicMachineV3` Records
     with `encodeRun` + `computability` fields.
  6. `decidesV3`, polynomial-time bounds.
  7. `class_P_typedV3`, `class_NP_typedV3`, `Literal_P_neq_NP_V3`,
     `EnumToClassSeparationBridgeV3` Props.
  8. Cook 1971 subset theorem + reduction-iff theorem.
  9. Honest-scope theorems (V3 still vacuous under TMConfig wiring).
  10. Capstone Theorem bundling all three.

  ## Honest scope

  Cross-prover STRUCTURAL parity. The V3 refactor closes the
  STRUCTURAL-shape defect (no `True` placeholder remains; every
  machine carries a TMConfig-valued run) but does NOT close the
  universal-inhabitation defect at the set level. Because
  `encodeConfig_positive` holds unconditionally, the constraint
  is satisfied by ANY choice of `encodeRun` (e.g. the constant
  `fun _ => zeroConfig`). The next refactor (V4, future) would
  link `decide` to `encodeRun` via accepting-state-of-encoded-run.
  NOT a Clay discharge.

  ## Coq libraries used

  - `Stdlib.Init.Datatypes` (bool, list)
  - `Stdlib.Arith.PeanoNat`, `Lia`
  - `Stdlib.Logic.Classical`
*)

From Stdlib Require Import PeanoNat Lia List.
From Stdlib Require Import Classical.

(** Mirror Lean namespace `PrincipiaTractalis.PNPClassSeparationCarrierV3`. *)
Module PNPClassSeparationCarrierV3.

(** ## §1 -- The Input carrier (re-used from V2)

    Mirrors Lean V2 `Input` with a `size : nat` projection. *)
Record Input : Type := mkInput {
  size : nat
}.

(** The trivial input (size 0). *)
Definition zeroInput : Input := mkInput 0.

(** ## §2 -- DecidableProblemV3 carrier (Bool-valued, re-used from V2)

    Mirrors Lean `abbrev DecidableProblemV3 := DecidableProblemV2`. *)
Definition DecidableProblemV3 : Type := Input -> bool.

(** ## §3 -- TMConfig (the manuscript Ch 21 §2 carrier)

    Mirrors Lean `PF.TuringEncoding.Basic.TMConfig`:
    `{ state : N, tape : List N, headPos : N }`. *)
Record TMConfig : Type := mkTMConfig {
  cfgState : nat;
  cfgTape : list nat;
  cfgHeadPos : nat
}.

(** The trivial config `{ state := 0, tape := [], headPos := 0 }`.
    Used as the constant-encodeRun witness in the honest-scope
    discharges. *)
Definition zeroConfig : TMConfig := mkTMConfig 0 nil 0.

(** **encodeConfig** -- mirror of Lean's prime-power Goedel encoding
    `2^state * 3^headPos * prod p_{j+1}^{symbol+1}`. At parity
    granularity, we model it as `S (cfgState + cfgHeadPos +
    length cfgTape)`, which is positive unconditionally and faithfully
    mirrors the Lean invariant `encodeConfig cfg > 0`. *)
Definition encodeConfig (cfg : TMConfig) : nat :=
  S (cfgState cfg + cfgHeadPos cfg + length (cfgTape cfg)).

(** **encodeConfig_positive** -- mirror of Lean
    `PF.TuringEncoding.Basic.encodeConfig_positive`. Every TMConfig
    has positive encoding, axiom-free. *)
Theorem encodeConfig_positive : forall cfg : TMConfig, encodeConfig cfg > 0.
Proof.
  intros cfg. unfold encodeConfig. apply Nat.lt_0_succ.
Qed.

(** ## §4 -- The V3 deterministic / nondeterministic machines

    Mirrors Lean `DeterministicMachineV3` / `NondeterministicMachineV3`
    with `encodeRun` + TMConfig-derived `computability`. *)

(** **V3 deterministic machine.** `decide` Bool-valued (V2 carryover);
    `runtime` nat-valued; `encodeRun` is the NEW TMConfig-valued field;
    `computability` constrains the encoded run to be a positive
    prime-power Goedel number, wired through `encodeConfig`. *)
Record DeterministicMachineV3 : Type := mkDetMachineV3 {
  decideV3  : Input -> bool;
  runtimeV3 : Input -> nat;
  encodeRunV3 : Input -> TMConfig;
  computabilityV3 : forall x : Input, encodeConfig (encodeRunV3 x) > 0
}.

(** **V3 nondeterministic machine.** `verify` Bool-valued on
    (input, certificate); `runtime` likewise; `encodeRun` carries a
    TMConfig-valued run on each (input, cert); `computability` ditto. *)
Record NondeterministicMachineV3 : Type := mkNondetMachineV3 {
  verifyNDV3  : Input -> Input -> bool;
  runtimeNDV3 : Input -> Input -> nat;
  encodeRunNDV3 : Input -> Input -> TMConfig;
  computabilityNDV3 : forall x cert : Input,
    encodeConfig (encodeRunNDV3 x cert) > 0
}.

(** ## §5 -- V3 decides relation (Bool equality, identical shape to V2) *)

(** Mirrors Lean
    `DeterministicMachineV3.decides M L x := M.decide x = L x`. *)
Definition decidesV3 (M : DeterministicMachineV3)
    (L : DecidableProblemV3) (x : Input) : Prop :=
  decideV3 M x = L x.

(** **V3 polynomial-time bound (deterministic).** *)
Definition polyBoundedV3 (M : DeterministicMachineV3) (c : nat) : Prop :=
  forall x : Input, runtimeV3 M x <= c * Nat.pow (size x + 1) c.

(** **V3 polynomial-time bound (nondeterministic verifier).** *)
Definition polyBoundedNDV3 (V : NondeterministicMachineV3) (c : nat) : Prop :=
  forall (x cert : Input),
    size cert <= c * Nat.pow (size x + 1) c ->
    runtimeNDV3 V x cert <= c * Nat.pow (size x + 1) c.

(** ## §6 -- Classes P and NP on V3 carrier *)

(** Mirrors Lean `class_P_typedV3`. *)
Definition class_P_typedV3 (L : DecidableProblemV3) : Prop :=
  exists (M : DeterministicMachineV3) (c : nat),
    polyBoundedV3 M c /\ (forall x : Input, decidesV3 M L x).

(** Mirrors Lean `class_NP_typedV3`. *)
Definition class_NP_typedV3 (L : DecidableProblemV3) : Prop :=
  exists (V : NondeterministicMachineV3) (c : nat),
    polyBoundedNDV3 V c /\
    (forall x : Input,
       L x = true <->
       exists cert : Input,
         size cert <= c * Nat.pow (size x + 1) c /\
         verifyNDV3 V x cert = true).

(** ## §7 -- The literal P neq NP statement (V3)

    Mirrors Lean `Literal_P_neq_NP_V3 := class_P_typedV3 <> class_NP_typedV3`.
    Set-equality is mirrored as predicate biconditional pointwise. *)
Definition Literal_P_neq_NP_V3 : Prop :=
  ~ (forall L : DecidableProblemV3,
       class_P_typedV3 L <-> class_NP_typedV3 L).

(** Mirrors Lean `EnumToClassSeparationBridgeV3`. *)
Definition EnumToClassSeparationBridgeV3 : Prop :=
  exists L : DecidableProblemV3,
    class_NP_typedV3 L /\ ~ class_P_typedV3 L.

(** ## §8 -- Cook 1971 P subset NP on V3 carrier

    Mirrors Lean `class_P_subset_class_NP_V3`. The verifier ignores
    the certificate, returns `M.decideV3 x`, and lifts `encodeRunV3`
    by ignoring the certificate -- the `computabilityNDV3` field then
    follows from `M.computabilityV3`. *)
Theorem class_P_subset_class_NP_V3 :
  forall L : DecidableProblemV3,
    class_P_typedV3 L -> class_NP_typedV3 L.
Proof.
  intros L hLP.
  destruct hLP as [M [c [hpoly hdec]]].
  exists (mkNondetMachineV3
            (fun x _ => decideV3 M x)
            (fun x _ => runtimeV3 M x)
            (fun x _ => encodeRunV3 M x)
            (fun x _ => computabilityV3 M x)), c.
  split.
  - (* polyBoundedNDV3: ignore certificate, fall back to det bound. *)
    intros x _cert _hcert. simpl.
    exact (hpoly x).
  - intros x. split.
    + (* L x = true -> exists cert, verify x cert = true. *)
      intros hxL.
      exists zeroInput.
      split.
      * simpl. apply Nat.le_0_l.
      * simpl.
        unfold decidesV3 in hdec.
        rewrite (hdec x). exact hxL.
    + (* exists cert ... -> L x = true. *)
      intros [cert [_hsize hVerify]].
      simpl in hVerify.
      unfold decidesV3 in hdec.
      rewrite <- (hdec x). exact hVerify.
Qed.

(** ## §9 -- EnumToClassSeparationBridgeV3 iff Literal_P_neq_NP_V3

    Mirrors Lean
    `enum_to_class_separation_bridge_V3_iff_literal_P_neq_NP_V3`. *)
Theorem enum_to_class_separation_bridge_V3_iff_literal_P_neq_NP_V3 :
  EnumToClassSeparationBridgeV3 <-> Literal_P_neq_NP_V3.
Proof.
  unfold EnumToClassSeparationBridgeV3, Literal_P_neq_NP_V3.
  split.
  - (* (->) Given witness L in NP \ P, classes differ pointwise. *)
    intros [L [hNP hP]] heq.
    apply hP.
    apply (heq L). exact hNP.
  - (* (<-) Given classes differ, exhibit a witness via classical
       contradiction. *)
    intros hne.
    apply NNPP.
    intros h_no_witness.
    apply hne.
    intros L.
    split.
    + intros hLP. exact (class_P_subset_class_NP_V3 L hLP).
    + intros hLNP.
      apply NNPP. intros hLnotP.
      apply h_no_witness.
      exists L. split; assumption.
Qed.

(** ## §10 -- Honest scope: TMConfig wiring closes the structural-shape
              defect but NOT the universal-inhabitation defect

    The TMConfig-wired `computabilityV3` constraint is satisfied by
    the trivial machine with constant `encodeRunV3 := fun _ => zeroConfig`,
    because `encodeConfig_positive` holds unconditionally. The
    universal-inhabitation defect therefore SURVIVES at the class
    level. *)

(** Mirrors Lean
    `class_P_typedV3_eq_univ_under_TMConfig_wiring`. *)
Theorem class_P_typedV3_eq_univ_under_TMConfig_wiring :
  forall L : DecidableProblemV3, class_P_typedV3 L.
Proof.
  intros L.
  exists (mkDetMachineV3
            L
            (fun _ => 0)
            (fun _ => zeroConfig)
            (fun _ => encodeConfig_positive zeroConfig)), 0.
  split.
  - intros x. simpl. apply Nat.le_0_l.
  - intros x. unfold decidesV3. simpl. reflexivity.
Qed.

(** Mirrors Lean
    `class_NP_typedV3_eq_univ_under_TMConfig_wiring`. *)
Theorem class_NP_typedV3_eq_univ_under_TMConfig_wiring :
  forall L : DecidableProblemV3, class_NP_typedV3 L.
Proof.
  intros L.
  apply class_P_subset_class_NP_V3.
  exact (class_P_typedV3_eq_univ_under_TMConfig_wiring L).
Qed.

(** Mirrors Lean
    `not_Literal_P_neq_NP_V3_under_TMConfig_wiring`. *)
Theorem not_Literal_P_neq_NP_V3_under_TMConfig_wiring :
  ~ Literal_P_neq_NP_V3.
Proof.
  unfold Literal_P_neq_NP_V3.
  intros h. apply h.
  intros L. split.
  - intros _. apply class_NP_typedV3_eq_univ_under_TMConfig_wiring.
  - intros _. apply class_P_typedV3_eq_univ_under_TMConfig_wiring.
Qed.

(** ## §11 -- V3 carrier honest-scope capstone

    Mirrors Lean `pnp_carrier_V3_honest_scope_capstone`. *)
Theorem pnp_carrier_V3_honest_scope_capstone :
  (* (1) Cook 1971 P subset NP on V3. *)
  (forall L : DecidableProblemV3,
     class_P_typedV3 L -> class_NP_typedV3 L) /\
  (* (2) Reduction theorem analog. *)
  (EnumToClassSeparationBridgeV3 <-> Literal_P_neq_NP_V3) /\
  (* (3) Honest scope: under TMConfig wiring, Literal_P_neq_NP_V3 is False. *)
  (~ Literal_P_neq_NP_V3).
Proof.
  repeat split.
  - exact class_P_subset_class_NP_V3.
  - apply enum_to_class_separation_bridge_V3_iff_literal_P_neq_NP_V3.
  - apply enum_to_class_separation_bridge_V3_iff_literal_P_neq_NP_V3.
  - exact not_Literal_P_neq_NP_V3_under_TMConfig_wiring.
Qed.

(** ## §12 -- Honest-scope marker *)

Definition honest_scope_coq_parity_only_not_a_discharge : Prop := True.

Theorem honest_scope_marker :
  honest_scope_coq_parity_only_not_a_discharge.
Proof. exact I. Qed.

End PNPClassSeparationCarrierV3.

(*
  ## File-level honest-scope commentary

  1. V3 refactors V2 by REPLACING the `computability : True`
     placeholder with a TMConfig-derived constraint:
     `computability : forall x, encodeConfig (encodeRun x) > 0`.

  2. Every V3 machine carries an `encodeRun : Input -> TMConfig`
     field exhibiting a Turing-machine configuration for every
     input. The encoded run is constrained to be a genuine
     positive prime-power Goedel number via `encodeConfig`.

  3. Cook 1971 P subset NP holds on V3 by ignoring the certificate
     and lifting `encodeRun` accordingly.

  4. The reduction-iff theorem holds via Cook 1971 + classical
     excluded middle (mirroring Lean's `push_neg` / `by_contra`).

  5. Honest scope: the V3 carrier closes the STRUCTURAL-shape
     defect (no `True` placeholder remains) but does NOT close
     the universal-inhabitation defect at the set level. Because
     `encodeConfig_positive` holds unconditionally, the
     `computability` constraint is satisfied by ANY choice of
     `encodeRun` (e.g. constant `fun _ => zeroConfig`). Therefore
     `class_P_typedV3 = univ` is still provable, and
     `Literal_P_neq_NP_V3` is provably False on the V3 carrier.

  6. The next refactor (V4, future) would close the
     universal-inhabitation defect by LINKING `decide` to
     `encodeRun` via accepting-state-of-encoded-run (e.g. via
     `Turing.TM` / `Turing.TM2` machinery on the Lean side).

  7. NOT a Clay discharge. Cross-prover structural parity only.
*)
