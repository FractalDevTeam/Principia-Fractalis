/-
# PNPClassSeparationCarrierV3 — TMConfig-wired carrier refactor of the
# typed Clay P vs NP class-separation substrate (extends V2)

★ 2026-06-04 — Wave 58/59 V3 Carrier Refactor (post V2 Bool-equality
refactor at HEAD 5a38500) ★

## Why this file exists

The V2 carrier (`PF.TuringEncoding.PNPClassSeparationCarrierV2`) closed
the Iff-vs-Bool defect by retyping `DecidableProblem` to `Input → Bool`
and `M.decides L x` to Bool equality. It left a single named placeholder
field — `computability : True` — documenting the precise plug-in point
for a real machine model.

V3 strengthens the V2 carrier by REPLACING the `True` placeholder with a
real constraint wired through the framework's existing Turing-machine
infrastructure:

* `PF.TuringEncoding.Basic.TMConfig` — the manuscript Ch 21 §2 prime-power
  Gödel numbering carrier `{ state : ℕ, tape : List ℕ, headPos : ℕ }`.
* `PF.TuringEncoding.Basic.encodeConfig : TMConfig → ℕ` — the prime-power
  encoding `2^state · 3^headPos · ∏ p_{j+1}^{symbol+1}`.
* `PF.TuringEncoding.Basic.encodeConfig_positive` — `encodeConfig cfg > 0`
  for every `TMConfig` (axiom-free, via `Nat.pow_pos` on the three
  positive prime-power factors).
* `PF.TuringEncoding.encodeConfig_injective` — prime-factorization
  injectivity (Function.Injective encodeConfig) proven in
  `PF/TuringEncoding.lean` line 1221.

The V3 carrier adds an `encodeRun : Input → TMConfig` field to every
machine and a `computability : ∀ x, encodeConfig (encodeRun x) > 0`
constraint — every machine must exhibit a TMConfig-encoded run on
every input, and the encoding must be a genuine positive prime-power
Gödel number (consistent with the manuscript's discrete-to-continuous
embedding).

## What is claimed

1. **Carrier refactor with TMConfig wiring.** Define
   `DecidableProblemV3 := Input → Bool` (re-used from V2),
   `DeterministicMachineV3` / `NondeterministicMachineV3` with the new
   `encodeRun : Input → TMConfig` field and the TMConfig-derived
   `computability` constraint (no `True` placeholder).
2. **Cook 1971 P ⊆ NP on V3 carrier.** Same subset direction as V2,
   ported to the strengthened carrier — the verifier ignores the
   certificate and returns `M.decide x`, lifting `encodeRun` to ignore
   the certificate likewise.
3. **V3 reduction theorem analog.** `EnumToClassSeparationBridgeV3 ↔
   Literal_P_neq_NP_V3` via the same Cook-1971 backward direction.
4. **Honest scope.** The TMConfig-wired `computability` constraint is
   `∀ x, encodeConfig (encodeRun x) > 0`. Because
   `encodeConfig_positive` is a THEOREM (every TMConfig has positive
   encoding, unconditionally), the constraint is satisfied by ANY choice
   of `encodeRun` — for instance the constant `fun _ => ⟨0, [], 0⟩`.
   Therefore `class_P_typedV3 = Set.univ` is STILL provable: given any
   `L : Input → Bool`, the machine `{ decide := L, runtime := fun _ => 0,
   encodeRun := fun _ => ⟨0, [], 0⟩, computability := fun x =>
   encodeConfig_positive _ }` polyBounds at `c = 0` and decides `L`.
   The TMConfig wiring closes the **structural-shape defect** (every
   machine now carries a TM-config-valued run, not just an opaque
   placeholder) but does NOT yet close the **universal-inhabitation
   defect** at the class level — that requires linking `encodeRun` to
   the `decide` field (e.g. requiring `decide x = true` iff the encoded
   run is an accepting configuration, with a polynomial-step-count
   constraint relating `runtime` to TM-step transitions).

## What is NOT claimed

* No discharge of `Literal_P_neq_NP_V3`. The carrier is structurally
  stronger than V2 (the `computability` field now carries
  TMConfig-derived content rather than `True`), but the universal-
  inhabitation defect at the SET level survives because `encodeRun` and
  `decide` are independent fields and the TMConfig encoding is positive
  unconditionally. The next refactor (V4, future) would tie `decide` to
  the `encodeRun`-produced configuration's accept state via the
  `Turing.TM` / `Turing.TM2` machinery, closing the universal-
  inhabitation defect.
* No new mathematical content beyond carrier strengthening through the
  existing TMConfig infrastructure.

## Axiom budget

Zero project axioms, zero sorries. All theorems depend only on
`[propext, Classical.choice, Quot.sound]`.

Stage Wave 58/59 V3 — TMConfig-wired carrier refactor of the typed Clay
P vs NP class-separation substrate.
-/

import PF.TuringEncoding.PNPClassSeparationCarrierV2
import PF.TuringEncoding.Basic

namespace PrincipiaTractalis.PNPClassSeparationCarrierV3

open PrincipiaTractalis.PNPClassSeparationCarrierV2
open PrincipiaTractalis.PNPClassSeparationPrecisionBridge
open PrincipiaTractalis.TuringEncoding

/-! ## §1 — TMConfig-wired carrier

The `Input` type is re-used from `PNPClassSeparationPrecisionBridge`
through V2. The `DecidableProblemV3` carrier is re-used from V2
(Bool-valued). The load-bearing strengthening is on the machine
structure: every machine carries a `TMConfig`-valued run on every input,
and the `computability` constraint asserts the encoded run is a genuine
positive Gödel number via `encodeConfig`.
-/

/-- **V3 decision problem.** Re-export of `DecidableProblemV2`. -/
abbrev DecidableProblemV3 := DecidableProblemV2

/-- **V3 deterministic machine.** `decide` is `Bool`-valued (carried
    from V2); `runtime` is a natural-number cost function; `encodeRun`
    is the new TMConfig-valued field — every input maps to a Turing-machine
    configuration. `computability` constrains the encoded run to be a
    genuine positive prime-power Gödel number, wired through
    `PF.TuringEncoding.Basic.encodeConfig`. -/
structure DeterministicMachineV3 where
  decide : Input → Bool
  runtime : Input → ℕ
  encodeRun : Input → TMConfig
  computability : ∀ x : Input, encodeConfig (encodeRun x) > 0

/-- **V3 nondeterministic machine.** `verify` is `Bool`-valued on
    `(input, certificate)` pairs; `runtime` likewise; `encodeRun` carries
    a TM-config-valued run on each `(input, certificate)` pair, and the
    encoded run is constrained to be a genuine positive Gödel number. -/
structure NondeterministicMachineV3 where
  verify : Input → Input → Bool
  runtime : Input → Input → ℕ
  encodeRun : Input → Input → TMConfig
  computability : ∀ x cert : Input, encodeConfig (encodeRun x cert) > 0

/-- **V3 decides relation.** Bool equality, identical shape to V2. -/
def DeterministicMachineV3.decides (M : DeterministicMachineV3)
    (L : DecidableProblemV3) (x : Input) : Prop :=
  M.decide x = L x

/-- **V3 polynomial-time bound (deterministic).** -/
def DeterministicMachineV3.polyBoundedV3
    (M : DeterministicMachineV3) (c : ℕ) : Prop :=
  ∀ x : Input, M.runtime x ≤ c * (x.size + 1) ^ c

/-- **V3 polynomial-time bound (nondeterministic verifier).** -/
def NondeterministicMachineV3.polyBoundedV3
    (V : NondeterministicMachineV3) (c : ℕ) : Prop :=
  ∀ x cert : Input,
    cert.size ≤ c * (x.size + 1) ^ c →
    V.runtime x cert ≤ c * (x.size + 1) ^ c

/-- **V3 class P (TMConfig-wired carrier).** -/
def class_P_typedV3 : Set DecidableProblemV3 :=
  { L | ∃ (M : DeterministicMachineV3) (c : ℕ),
        M.polyBoundedV3 c ∧ (∀ x : Input, M.decides L x) }

/-- **V3 class NP (TMConfig-wired carrier).** -/
def class_NP_typedV3 : Set DecidableProblemV3 :=
  { L | ∃ (V : NondeterministicMachineV3) (c : ℕ),
        V.polyBoundedV3 c ∧
        (∀ x : Input, L x = true ↔
          ∃ cert : Input,
            cert.size ≤ c * (x.size + 1) ^ c ∧ V.verify x cert = true) }

/-! ## §2 — The literal P ≠ NP statement (V3) -/

/-- **★ THE LITERAL CLAY STATEMENT (V3 carrier) ★**. -/
def Literal_P_neq_NP_V3 : Prop :=
  class_P_typedV3 ≠ class_NP_typedV3

/-! ## §3 — V3 EnumToClassSeparationBridge -/

/-- **★ THE PRECISE GAP — V3 ★**: existence of a `DecidableProblemV3`
    in `class_NP_typedV3` but not `class_P_typedV3`. -/
def EnumToClassSeparationBridgeV3 : Prop :=
  ∃ L : DecidableProblemV3, L ∈ class_NP_typedV3 ∧ L ∉ class_P_typedV3

/-! ## §4 — Cook 1971 P ⊆ NP on V3 carrier

The standard subset direction `class_P_typedV3 ⊆ class_NP_typedV3` ports
to the strengthened carrier: given a deterministic polynomial-time
machine `M` deciding `L`, build a verifier `V` that ignores the
certificate, returns `M.decide x`, and lifts `M.encodeRun` to ignore the
certificate. The `computability` constraint on `V` follows from `M`'s.
-/

/-- **Cook 1971 P ⊆ NP (V3 carrier).** -/
theorem class_P_subset_class_NP_V3 :
    class_P_typedV3 ⊆ class_NP_typedV3 := by
  intro L hLP
  obtain ⟨M, c, hpoly, hdec⟩ := hLP
  refine ⟨{ verify := fun x _ => M.decide x
            runtime := fun x _ => M.runtime x
            encodeRun := fun x _ => M.encodeRun x
            computability := fun x _ => M.computability x }, c, ?_, ?_⟩
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

/-! ## §5 — EnumToClassSeparationBridgeV3 ↔ Literal_P_neq_NP_V3 -/

/-- **★ V3 ANALOG OF `enum_to_class_separation_bridge_iff_literal_P_neq_NP` ★**.
    The named gap IS the standard "∃ L ∈ NP, L ∉ P" form of P ≠ NP on
    the V3 carrier. Forward via `Set.ext` contrapositive; backward via
    Cook-1971 P ⊆ NP on V3. -/
theorem enum_to_class_separation_bridge_V3_iff_literal_P_neq_NP_V3 :
    EnumToClassSeparationBridgeV3 ↔ Literal_P_neq_NP_V3 := by
  unfold EnumToClassSeparationBridgeV3 Literal_P_neq_NP_V3
  constructor
  · rintro ⟨L, hNP, hP⟩ heq
    apply hP
    exact heq ▸ hNP
  · intro hne
    by_contra h_no_witness
    push_neg at h_no_witness
    apply hne
    apply Set.eq_of_subset_of_subset
    · exact class_P_subset_class_NP_V3
    · intro L hLNP
      exact h_no_witness L hLNP

/-! ## §6 — Honest scope: TMConfig wiring closes the STRUCTURAL-shape
defect but NOT the universal-inhabitation defect.

The V3 `computability : ∀ x, encodeConfig (encodeRun x) > 0` constraint
is structurally stronger than V2's `True`: every V3 machine must exhibit
a `TMConfig`-valued run, and the encoded run is constrained to be a
positive prime-power Gödel number. However, because
`encodeConfig_positive : ∀ cfg, encodeConfig cfg > 0` holds
unconditionally (axiom-free, proved via `Nat.pow_pos`), the constraint
is satisfied by ANY choice of `encodeRun`. The universal-inhabitation
defect therefore SURVIVES at the set level: for any
`L : DecidableProblemV3`, the machine

    { decide := L, runtime := fun _ => 0,
      encodeRun := fun _ => ⟨0, [], 0⟩,
      computability := fun x => encodeConfig_positive _ }

polyBounds at `c = 0` and decides `L`.

The structural gain of V3 over V2: the `computability` field now carries
real TM-config-derived content (rather than a `True` placeholder), and
the machine structure now exhibits the manuscript's discrete-to-continuous
TMConfig encoding for every input. This localizes the surviving carrier
defect to a single named missing axis — the absence of a constraint
LINKING `decide` to `encodeRun` (e.g. `decide x = true` iff the encoded
run from `encodeRun x` reaches an accepting TM state under the framework's
`alpha_at_enum`-modulated phase factor). That linkage is the next
refactoring target (V4).
-/

/-- **Honest scope: `class_P_typedV3 = Set.univ` is still provable under
    the TMConfig-wired `computability` constraint.** Given any
    `L : DecidableProblemV3`, the trivial machine with constant
    `encodeRun := fun _ => ⟨0, [], 0⟩` discharges the TMConfig
    `computability` constraint via `encodeConfig_positive` and decides
    `L` at runtime 0. -/
theorem class_P_typedV3_eq_univ_under_TMConfig_wiring :
    class_P_typedV3 = Set.univ := by
  ext L
  simp only [Set.mem_univ, iff_true]
  refine ⟨{ decide := L
            runtime := fun _ => 0
            encodeRun := fun _ => ⟨0, [], 0⟩
            computability := fun _ => encodeConfig_positive _ },
          0, ?_, ?_⟩
  · intro x
    simp
  · intro x
    rfl

/-- **Honest scope (corollary): `class_NP_typedV3 = Set.univ`.** Via
    Cook 1971 P ⊆ NP on V3. -/
theorem class_NP_typedV3_eq_univ_under_TMConfig_wiring :
    class_NP_typedV3 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro L
  exact class_P_subset_class_NP_V3 <| by
    rw [class_P_typedV3_eq_univ_under_TMConfig_wiring]; trivial

/-- **Honest scope: under the TMConfig-wired `computability` constraint,
    `Literal_P_neq_NP_V3` is provably False.** This is NOT a Clay
    refutation — it is a precise statement that the V3 carrier closes
    the structural-shape defect (no `True` placeholder remains) but the
    universal-inhabitation defect survives because `encodeRun` and
    `decide` are independent fields. The next refactoring target (V4)
    must add a `decide ↔ accepting-state-of-encodeRun` linkage. -/
theorem not_Literal_P_neq_NP_V3_under_TMConfig_wiring :
    ¬ Literal_P_neq_NP_V3 := by
  unfold Literal_P_neq_NP_V3
  rw [class_P_typedV3_eq_univ_under_TMConfig_wiring,
      class_NP_typedV3_eq_univ_under_TMConfig_wiring]
  intro h
  exact h rfl

/-! ## §7 — V3 carrier honest-scope capstone -/

/-- **V3 carrier honest-scope capstone.** Single citable theorem
    bundling: (1) Cook 1971 P ⊆ NP holds on V3; (2) V3 reduction
    theorem analog; (3) honest scope — `Literal_P_neq_NP_V3` is still
    provably False under TMConfig-wired `computability`, exposing the
    precise missing axis (`decide`-to-`encodeRun` linkage) that a V4
    refactor must populate. -/
theorem pnp_carrier_V3_honest_scope_capstone :
    -- (1) Cook 1971 P ⊆ NP on V3.
    (class_P_typedV3 ⊆ class_NP_typedV3) ∧
    -- (2) Reduction theorem analog.
    (EnumToClassSeparationBridgeV3 ↔ Literal_P_neq_NP_V3) ∧
    -- (3) Honest scope: under TMConfig wiring, Literal_P_neq_NP_V3 is False.
    (¬ Literal_P_neq_NP_V3) := by
  refine ⟨class_P_subset_class_NP_V3,
          enum_to_class_separation_bridge_V3_iff_literal_P_neq_NP_V3,
          not_Literal_P_neq_NP_V3_under_TMConfig_wiring⟩

end PrincipiaTractalis.PNPClassSeparationCarrierV3
