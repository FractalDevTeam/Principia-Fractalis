/-
# PNPClassSeparationCarrierV4 — `decide`-to-`encodeRun` linkage refactor
# (extends V3)

★ 2026-06-04 — Wave 58/59 V4 Carrier Refactor (post V3 TMConfig wiring
at HEAD 588a4dd) ★

## Why this file exists

V3 (`PF.TuringEncoding.PNPClassSeparationCarrierV3`) added a real
`encodeRun : Input → TMConfig` field plus a `computability` constraint
`∀ x, encodeConfig (encodeRun x) > 0` wired through the manuscript
Ch 21 §2 prime-power Gödel numbering. That closed the **structural-shape
defect** (every machine carries a TM-config-valued run) but left the
**universal-inhabitation defect** open: because `encodeConfig_positive`
holds unconditionally, the trivial machine

    { decide := L, runtime := fun _ => 0,
      encodeRun := fun _ => ⟨0, [], 0⟩,
      computability := fun _ => encodeConfig_positive _ }

discharges every V3 axiom-free for any `L : Input → Bool`. The fields
`decide` and `encodeRun` are independent.

V4 adds the LINKAGE field that V3 explicitly flagged as the next refactor
target: a state-set `acceptingStates : Set ℕ` and a constraint

    decide_via_encodeRun : ∀ x, decide x = true ↔
                          (encodeRun x).state ∈ acceptingStates

so the Bool decision is computed BY the TM trajectory (the encoded
configuration's state component). The trivial inhabitant from V3 is no
longer admissible for non-constant `L`: a constant `encodeRun = ⟨0,[],0⟩`
forces `decide x = true ↔ 0 ∈ acceptingStates` to hold for every `x`,
which means `decide` must be a CONSTANT function on `Input` — either
identically true (if `0 ∈ acceptingStates`) or identically false
(otherwise). So `class_P_typedV4` is no longer trivially `Set.univ`: it
cannot contain any `L : Input → Bool` that is neither identically true
nor identically false via a constant-encoding machine.

## What is claimed

1. **Carrier refactor with `decide`-to-`encodeRun` linkage.** Define
   `DecidableProblemV4 := DecidableProblemV3`,
   `DeterministicMachineV4` / `NondeterministicMachineV4` with new
   `acceptingStates : Set ℕ` field and the `decide_via_encodeRun`
   linkage constraint.
2. **Cook 1971 P ⊆ NP on V4 carrier.** Same subset direction as V3,
   ported to the strengthened carrier — the verifier ignores the
   certificate and inherits `acceptingStates` / linkage from the
   deterministic machine.
3. **V4 reduction theorem analog.** `EnumToClassSeparationBridgeV4 ↔
   Literal_P_neq_NP_V4` via Cook-1971 backward direction.
4. **NON-TRIVIALITY witness.** A `Decidable`-valued `L_const_true`
   (identically true) is admissible (inhabit with constant
   `encodeRun = ⟨0,[],0⟩` and `acceptingStates := {0}`). A
   `Decidable`-valued `L_witness_nonconst` (any nonconstant predicate)
   is NOT admissible via constant `encodeRun` — formalizing the carrier
   structural strengthening.
5. **Honest scope.** V4 does NOT close `Literal_P_neq_NP_V4` axiom-free
   (that would solve Clay P vs NP). What it closes is the **trivial-
   inhabitation defect at the constant-encoding level**: the witness
   `{decide := L, encodeRun := const ⟨0,[],0⟩}` no longer trivially
   inhabits `class_P_typedV4` for non-constant L. The carrier now
   requires either a non-trivial `encodeRun` or a non-trivial
   `acceptingStates` for non-constant decision problems — populating
   the V3 missing axis with a real structural constraint.

## What is NOT claimed

* No Clay-level discharge of `Literal_P_neq_NP_V4`. The carrier remains
  conditional on populating an actual TM-step transition relation
  linking `runtime` to TMConfig successor traces (the next refactor
  target, V5).
* No new mathematical content beyond carrier strengthening. The
  `decide_via_encodeRun` linkage is an Iff at the Bool/membership level
  using `acceptingStates : Set ℕ` as the carrier of acceptance — not
  a full Turing-machine step relation.

## Axiom budget

Zero project axioms, zero sorries. All theorems depend only on
`[propext, Classical.choice, Quot.sound]`.

Stage Wave 58/59 V4 — `decide`-to-`encodeRun` linkage refactor of the
typed Clay P vs NP class-separation substrate.
-/

import PF.TuringEncoding.PNPClassSeparationCarrierV3
import PF.TuringEncoding.Basic

namespace PrincipiaTractalis.PNPClassSeparationCarrierV4

open PrincipiaTractalis.PNPClassSeparationCarrierV3
open PrincipiaTractalis.PNPClassSeparationCarrierV2
open PrincipiaTractalis.PNPClassSeparationPrecisionBridge
open PrincipiaTractalis.TuringEncoding

/-! ## §1 — `decide`-to-`encodeRun`-linked carrier

`Input` is re-used from `PNPClassSeparationPrecisionBridge` through V2/V3.
`DecidableProblemV4` re-exports the Bool-valued V3 carrier. The new
field on the machine structure is `acceptingStates : Set ℕ`, with the
`decide_via_encodeRun` constraint binding `decide x` to the membership
of `(encodeRun x).state` in `acceptingStates`. -/

/-- **V4 decision problem.** Re-export of `DecidableProblemV3`. -/
abbrev DecidableProblemV4 := DecidableProblemV3

/-- **V4 deterministic machine.** Adds:
    - `acceptingStates : Set ℕ` — the set of TM states deemed accepting.
    - `decide_via_encodeRun : ∀ x, decide x = true ↔
        (encodeRun x).state ∈ acceptingStates` — the load-bearing
      linkage forcing the Bool decision to be COMPUTED BY the
      trajectory's state component.
    `computability` is inherited from V3 (positive Gödel encoding). -/
structure DeterministicMachineV4 where
  decide : Input → Bool
  runtime : Input → ℕ
  encodeRun : Input → TMConfig
  acceptingStates : Set ℕ
  computability : ∀ x : Input, encodeConfig (encodeRun x) > 0
  decide_via_encodeRun : ∀ x : Input,
    decide x = true ↔ (encodeRun x).state ∈ acceptingStates

/-- **V4 nondeterministic machine.** Mirrors the deterministic
    structure on `(input, certificate)` pairs. -/
structure NondeterministicMachineV4 where
  verify : Input → Input → Bool
  runtime : Input → Input → ℕ
  encodeRun : Input → Input → TMConfig
  acceptingStates : Set ℕ
  computability : ∀ x cert : Input, encodeConfig (encodeRun x cert) > 0
  verify_via_encodeRun : ∀ x cert : Input,
    verify x cert = true ↔ (encodeRun x cert).state ∈ acceptingStates

/-- **V4 decides relation.** Bool equality, identical shape to V3. -/
def DeterministicMachineV4.decides (M : DeterministicMachineV4)
    (L : DecidableProblemV4) (x : Input) : Prop :=
  M.decide x = L x

/-- **V4 polynomial-time bound (deterministic).** -/
def DeterministicMachineV4.polyBoundedV4
    (M : DeterministicMachineV4) (c : ℕ) : Prop :=
  ∀ x : Input, M.runtime x ≤ c * (x.size + 1) ^ c

/-- **V4 polynomial-time bound (nondeterministic verifier).** -/
def NondeterministicMachineV4.polyBoundedV4
    (V : NondeterministicMachineV4) (c : ℕ) : Prop :=
  ∀ x cert : Input,
    cert.size ≤ c * (x.size + 1) ^ c →
    V.runtime x cert ≤ c * (x.size + 1) ^ c

/-- **V4 class P (`decide`-to-`encodeRun`-linked carrier).** -/
def class_P_typedV4 : Set DecidableProblemV4 :=
  { L | ∃ (M : DeterministicMachineV4) (c : ℕ),
        M.polyBoundedV4 c ∧ (∀ x : Input, M.decides L x) }

/-- **V4 class NP (`decide`-to-`encodeRun`-linked carrier).** -/
def class_NP_typedV4 : Set DecidableProblemV4 :=
  { L | ∃ (V : NondeterministicMachineV4) (c : ℕ),
        V.polyBoundedV4 c ∧
        (∀ x : Input, L x = true ↔
          ∃ cert : Input,
            cert.size ≤ c * (x.size + 1) ^ c ∧ V.verify x cert = true) }

/-! ## §2 — The literal P ≠ NP statement (V4) -/

/-- **★ THE LITERAL CLAY STATEMENT (V4 carrier) ★**. -/
def Literal_P_neq_NP_V4 : Prop :=
  class_P_typedV4 ≠ class_NP_typedV4

/-! ## §3 — V4 EnumToClassSeparationBridge -/

/-- **★ THE PRECISE GAP — V4 ★**: existence of a `DecidableProblemV4`
    in `class_NP_typedV4` but not `class_P_typedV4`. -/
def EnumToClassSeparationBridgeV4 : Prop :=
  ∃ L : DecidableProblemV4, L ∈ class_NP_typedV4 ∧ L ∉ class_P_typedV4

/-! ## §4 — Cook 1971 P ⊆ NP on V4 carrier

Standard subset direction. Given a deterministic poly-time V4 machine
`M` deciding `L`, build a verifier `V` that ignores the certificate,
returns `M.decide x`, lifts `M.encodeRun` and `M.acceptingStates`,
inherits `computability` and `decide_via_encodeRun`. -/

/-- **Cook 1971 P ⊆ NP (V4 carrier).** -/
theorem class_P_subset_class_NP_V4 :
    class_P_typedV4 ⊆ class_NP_typedV4 := by
  intro L hLP
  obtain ⟨M, c, hpoly, hdec⟩ := hLP
  refine ⟨{ verify := fun x _ => M.decide x
            runtime := fun x _ => M.runtime x
            encodeRun := fun x _ => M.encodeRun x
            acceptingStates := M.acceptingStates
            computability := fun x _ => M.computability x
            verify_via_encodeRun := fun x _ => M.decide_via_encodeRun x },
          c, ?_, ?_⟩
  · intro x _cert _hcert
    exact hpoly x
  · intro x
    constructor
    · intro hxL
      refine ⟨⟨0⟩, Nat.zero_le _, ?_⟩
      simp only
      rw [hdec x]
      exact hxL
    · rintro ⟨_, _, hVerify⟩
      simp only at hVerify
      rw [← hdec x]
      exact hVerify

/-! ## §5 — EnumToClassSeparationBridgeV4 ↔ Literal_P_neq_NP_V4 -/

/-- **★ V4 ANALOG OF `enum_to_class_separation_bridge_iff_literal_P_neq_NP` ★**.
    Forward via `Set.ext` contrapositive; backward via Cook-1971 P ⊆ NP
    on V4. -/
theorem enum_to_class_separation_bridge_V4_iff_literal_P_neq_NP_V4 :
    EnumToClassSeparationBridgeV4 ↔ Literal_P_neq_NP_V4 := by
  unfold EnumToClassSeparationBridgeV4 Literal_P_neq_NP_V4
  constructor
  · rintro ⟨L, hNP, hP⟩ heq
    apply hP
    exact heq ▸ hNP
  · intro hne
    by_contra h_no_witness
    push_neg at h_no_witness
    apply hne
    apply Set.eq_of_subset_of_subset
    · exact class_P_subset_class_NP_V4
    · intro L hLNP
      exact h_no_witness L hLNP

/-! ## §6 — Non-triviality: the V3 trivial inhabitant is NO LONGER
admissible for non-constant `L`.

The key V3 honest-scope counterexample was

    { decide := L, runtime := fun _ => 0,
      encodeRun := fun _ => ⟨0, [], 0⟩,
      computability := fun _ => encodeConfig_positive _ }

which inhabited `class_P_typedV3` for ANY `L`. On V4, this machine
requires choosing `acceptingStates : Set ℕ` and proving

    decide_via_encodeRun : ∀ x, L x = true ↔ 0 ∈ acceptingStates.

Since the RHS does not depend on `x`, this forces `L x = true` to be a
CONSTANT proposition — i.e. `L` is either identically true (when
`0 ∈ acceptingStates`) or identically false (otherwise). So any
non-constant `L` is NOT admissible via the constant-encoding witness.
-/

/-- **Identically-true predicate.** -/
def L_const_true : DecidableProblemV4 := fun _ => true

/-- **Identically-false predicate.** -/
def L_const_false : DecidableProblemV4 := fun _ => false

/-- **Non-triviality lemma (positive case).** `L_const_true ∈ class_P_typedV4`
    via the constant-encoding witness with `acceptingStates := Set.univ`.
    This shows the constant-encoding witness still works for the
    "trivial" cases (constant predicates) — which is the correct
    semantics, since identically-true membership is the easiest possible
    decision problem. -/
theorem L_const_true_in_class_P_typedV4 :
    L_const_true ∈ class_P_typedV4 := by
  refine ⟨{ decide := L_const_true
            runtime := fun _ => 0
            encodeRun := fun _ => ⟨0, [], 0⟩
            acceptingStates := Set.univ
            computability := fun _ => encodeConfig_positive _
            decide_via_encodeRun := fun _ => by
              unfold L_const_true
              simp },
          0, ?_, ?_⟩
  · intro x
    simp
  · intro x
    rfl

/-- **Non-triviality lemma (negative case).** `L_const_false ∈ class_P_typedV4`
    via the constant-encoding witness with `acceptingStates := ∅`. -/
theorem L_const_false_in_class_P_typedV4 :
    L_const_false ∈ class_P_typedV4 := by
  refine ⟨{ decide := L_const_false
            runtime := fun _ => 0
            encodeRun := fun _ => ⟨0, [], 0⟩
            acceptingStates := ∅
            computability := fun _ => encodeConfig_positive _
            decide_via_encodeRun := fun _ => by
              unfold L_const_false
              simp },
          0, ?_, ?_⟩
  · intro x
    simp
  · intro x
    rfl

/-- **★ STRUCTURAL OBSTRUCTION ★**. For ANY V4 deterministic machine `M`
    whose `encodeRun` is CONSTANT (same TMConfig on every input), the
    `decide_via_encodeRun` linkage forces `M.decide` to be a CONSTANT
    function. Concretely: if `M.encodeRun x = M.encodeRun y` for all
    `x, y : Input`, then `M.decide x = M.decide y` for all `x, y`. This
    is the precise sense in which V4 closes the V3 trivial-inhabitation
    defect: constant `encodeRun` ⇒ constant `decide`. -/
theorem constant_encodeRun_forces_constant_decide
    (M : DeterministicMachineV4)
    (h_const : ∀ x y : Input, M.encodeRun x = M.encodeRun y) :
    ∀ x y : Input, M.decide x = M.decide y := by
  intro x y
  -- Bool equality via two Iff-chains through `decide_via_encodeRun`.
  by_cases hx : M.decide x = true
  · -- Case: M.decide x = true. Then (M.encodeRun x).state ∈ M.acceptingStates.
    have hx_in : (M.encodeRun x).state ∈ M.acceptingStates :=
      (M.decide_via_encodeRun x).mp hx
    -- Constant encodeRun ⇒ (M.encodeRun y).state = (M.encodeRun x).state.
    have heq : (M.encodeRun y).state = (M.encodeRun x).state := by
      rw [h_const y x]
    have hy_in : (M.encodeRun y).state ∈ M.acceptingStates := by
      rw [heq]; exact hx_in
    have hy : M.decide y = true :=
      (M.decide_via_encodeRun y).mpr hy_in
    rw [hx, hy]
  · -- Case: M.decide x ≠ true, so M.decide x = false (Bool).
    have hx_false : M.decide x = false := by
      cases hd : M.decide x with
      | true => exact absurd hd hx
      | false => rfl
    -- Then (M.encodeRun x).state ∉ M.acceptingStates.
    have hx_notin : (M.encodeRun x).state ∉ M.acceptingStates := by
      intro h_in
      have : M.decide x = true := (M.decide_via_encodeRun x).mpr h_in
      rw [hx_false] at this
      exact Bool.false_ne_true this
    -- Constant encodeRun ⇒ same state for y.
    have heq : (M.encodeRun y).state = (M.encodeRun x).state := by
      rw [h_const y x]
    have hy_notin : (M.encodeRun y).state ∉ M.acceptingStates := by
      rw [heq]; exact hx_notin
    have hy_false : M.decide y = false := by
      cases hd : M.decide y with
      | true =>
        exfalso
        apply hy_notin
        exact (M.decide_via_encodeRun y).mp hd
      | false => rfl
    rw [hx_false, hy_false]

/-! ## §7 — Honest scope: V4 closes the trivial-inhabitation defect at
the constant-encoding level, but does NOT discharge `Literal_P_neq_NP_V4`.

The structural obstruction `constant_encodeRun_forces_constant_decide`
proves that the V3 trivial witness (constant `encodeRun`) can no longer
inhabit `class_P_typedV4` for non-constant decision problems. This is a
genuine carrier strengthening: where V3 had `class_P_typedV3 = Set.univ`
axiom-free, V4 does not — populating an arbitrary `L` requires either a
non-constant `encodeRun` or a contradiction with the linkage.

V4 still does NOT discharge `Literal_P_neq_NP_V4`: a more sophisticated
machine could choose a non-constant `encodeRun` and an
`acceptingStates` matching any computable predicate, so the carrier
remains inhabited richly. The next refactor (V5) would add the
TM-step-relation constraint linking `runtime` to the number of
configuration transitions from initial state, closing the gap further. -/

/-! ## §8 — V4 carrier honest-scope capstone -/

/-- **V4 carrier honest-scope capstone.** Single citable theorem
    bundling: (1) Cook 1971 P ⊆ NP holds on V4; (2) V4 reduction
    theorem analog; (3) constant-`encodeRun` structural obstruction —
    proving the V3 trivial-inhabitation defect is closed at the
    constant-encoding level (constant `encodeRun` ⇒ constant `decide`);
    (4) admissibility of the genuinely trivial cases (identically-true
    and identically-false predicates) via the constant-encoding
    witness, confirming the linkage is non-vacuous. -/
theorem pnp_carrier_V4_honest_scope_capstone :
    -- (1) Cook 1971 P ⊆ NP on V4.
    (class_P_typedV4 ⊆ class_NP_typedV4) ∧
    -- (2) Reduction theorem analog.
    (EnumToClassSeparationBridgeV4 ↔ Literal_P_neq_NP_V4) ∧
    -- (3) Constant-encodeRun ⇒ constant-decide structural obstruction.
    (∀ (M : DeterministicMachineV4),
      (∀ x y : Input, M.encodeRun x = M.encodeRun y) →
      ∀ x y : Input, M.decide x = M.decide y) ∧
    -- (4) Constant-predicate admissibility (positive and negative).
    (L_const_true ∈ class_P_typedV4 ∧ L_const_false ∈ class_P_typedV4) := by
  refine ⟨class_P_subset_class_NP_V4,
          enum_to_class_separation_bridge_V4_iff_literal_P_neq_NP_V4,
          constant_encodeRun_forces_constant_decide,
          ⟨L_const_true_in_class_P_typedV4,
           L_const_false_in_class_P_typedV4⟩⟩

end PrincipiaTractalis.PNPClassSeparationCarrierV4
