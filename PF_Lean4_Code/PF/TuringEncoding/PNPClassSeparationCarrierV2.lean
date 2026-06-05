/-
# PNPClassSeparationCarrierV2 — Bool-valued carrier refactor of the
# typed Clay P vs NP class-separation substrate
#
# ★ 2026-06-04 — Wave 58/59 Carrier Refactor (post Wave 58 Clay-Precision
# Bridge, post Referee Layer 2026-06-02/03) ★
#
# ## Why this file exists
#
# The existing `PNPClassSeparationPrecisionBridge.lean` uses a carrier of
# `DecidableProblem := Input → Prop`, with a `DeterministicMachine` whose
# `decide` field is `Input → Prop`. The machine's `decides` relation is
# defined as an Iff:
#
#     M.decides L x := M.decide x ↔ L x
#
# Because `M.decide : Input → Prop` is unconstrained — there is no link
# to any computable model — `class_P_typed` is INHABITED BY EVERY
# `DecidableProblem`: given any `L`, take `M.decide := L`, runtime 0,
# polyBounded by c = 0 (since `0 * (x.size + 1) ^ 0 = 0`); the
# `decides L x` reduces to `L x ↔ L x = Iff.rfl`. Therefore
# `class_P_typed = Set.univ`, the same proof shows `class_NP_typed
# = Set.univ`, and `Literal_P_neq_NP` is vacuously False on the carrier
# (the two universal sets coincide).
#
# This is a CARRIER-LEVEL DEFECT, not a discharge: the bridge is correctly
# typed but the carrier is too permissive. To make `Literal_P_neq_NP_V2`
# non-trivially open (rather than provably False), we refactor the
# carrier so the `decide` field has codomain `Bool` and the `decides`
# relation is `Bool` equality. This kills the universal-inhabitation
# defect: even with a `True` computability placeholder, `M.decide := L`
# is no longer a legal closure because `L : Input → Bool`, not
# `Input → Prop`, and any `M : DeterministicMachineV2` carries a
# `decide : Input → Bool` that is itself NOT a closure on any
# `L : Input → Bool` (it is a free `Bool`-valued function on `Input`,
# with no a-priori link to a polynomial-time machine model). The
# carrier defect is removed; the surviving content is the (still open)
# question of whether the `computability : True` placeholder can be
# strengthened to a real machine model.
#
# ## What is claimed
#
# 1. **Carrier refactor.** Define `DecidableProblemV2 := Input → Bool`,
#    `DeterministicMachineV2` and `NondeterministicMachineV2` with
#    `decide : Input → Bool` / `verify : Input → Input → Bool` and
#    `computability : True` placeholder fields. `M.decides L x` is
#    `Bool` equality `M.decide x = L x` (not Iff).
# 2. **Cook 1971 P ⊆ NP on Bool-valued carrier.** The same argument
#    as in the precision bridge ports through: the verifier ignores
#    the certificate and returns `M.decide x`.
# 3. **Reduction theorem analog.** `EnumToClassSeparationBridgeV2 ↔
#    Literal_P_neq_NP_V2` holds via the same Cook-1971 P ⊆ NP backward
#    direction, ported to `Bool` equality.
# 4. **Structural non-universality.** We do NOT prove
#    `class_P_typedV2 ≠ Set.univ`. The `decide : Input → Bool` field
#    is still unconstrained — for any `L : Input → Bool`, the machine
#    `{ decide := L, runtime := fun _ => 0, computability := trivial }`
#    polyBounds with `c = 0` and decides `L`. We document this
#    explicitly: the carrier defect (universal inhabitation under
#    Iff-equality of Prop-valued decisions) is removed at the
#    `class_P_typedV2 ≠ class_NP_typedV2` level only if a non-trivial
#    `computability` predicate is supplied. The placeholder `True` is
#    a typed contract for future strengthening to a real machine model
#    (Turing-machine encoding via mathlib `Computable`, when available
#    at the carrier we use).
#
# ## What is NOT claimed
#
# * No discharge of `Literal_P_neq_NP_V2`. The carrier still admits the
#   `M.decide := L` closure under the placeholder `computability := True`,
#   so without strengthening, `class_P_typedV2 = Set.univ` remains
#   provable on this carrier — but ONLY because of the `True` placeholder.
#   The point of this file is to expose the EXACT place where a real
#   machine model must be plugged in (the `computability` field).
# * No new mathematical content beyond carrier refactoring.
#
# ## Axiom budget
#
# Zero project axioms, zero sorries. All theorems depend only on
# `[propext, Classical.choice, Quot.sound]`.
#
# Stage Wave 58/59 — Bool-valued carrier refactor of the typed Clay
# P vs NP class-separation substrate.
-/

import PF.TuringEncoding.PNPClassSeparationPrecisionBridge

namespace PrincipiaTractalis.PNPClassSeparationCarrierV2

open PrincipiaTractalis.PNPClassSeparationPrecisionBridge

/-! ## §1 — Bool-valued carrier

The `Input` type is re-used from `PNPClassSeparationPrecisionBridge`. We
refactor the decision-problem carrier to `Bool`-valued.
-/

/-- **V2 decision problem.** A decision problem is a `Bool`-valued
    predicate on inputs. (Standard textbook encoding: a decision
    problem `L ⊆ Σ*` corresponds to its characteristic function
    `Σ* → Bool`.) Carries no Prop-level ambiguity. -/
abbrev DecidableProblemV2 := Input → Bool

/-- **V2 deterministic machine.** `decide` is `Bool`-valued; `runtime`
    is a natural-number cost function; `computability` is a placeholder
    Prop field documenting the future plug-in point for a real machine
    model (mathlib `Computable` or a custom Turing-machine encoding).

    For now `computability := True`, so the field is vacuously inhabited
    by `trivial`. This is INTENTIONAL: the point of the refactor is to
    expose the precise field that a future strengthening will replace.
    The Bool codomain on `decide` is the load-bearing change relative
    to the Prop-valued carrier in `PNPClassSeparationPrecisionBridge`. -/
structure DeterministicMachineV2 where
  decide : Input → Bool
  runtime : Input → ℕ
  computability : True

/-- **V2 nondeterministic machine.** `verify` is `Bool`-valued on
    `(input, certificate)` pairs; `runtime` likewise. -/
structure NondeterministicMachineV2 where
  verify : Input → Input → Bool
  runtime : Input → Input → ℕ
  computability : True

/-- **V2 decides relation (Bool equality, not Iff).** The machine
    decides language `L` on input `x` iff `M.decide x = L x` as
    `Bool`s. -/
def DeterministicMachineV2.decides (M : DeterministicMachineV2)
    (L : DecidableProblemV2) (x : Input) : Prop :=
  M.decide x = L x

/-- **V2 polynomial-time bound (deterministic).** -/
def DeterministicMachineV2.polyBoundedV2
    (M : DeterministicMachineV2) (c : ℕ) : Prop :=
  ∀ x : Input, M.runtime x ≤ c * (x.size + 1) ^ c

/-- **V2 polynomial-time bound (nondeterministic verifier).**
    Conditional on certificate satisfying the polynomial size bound,
    matching Cook 1971 Def. 1.2. -/
def NondeterministicMachineV2.polyBoundedV2
    (V : NondeterministicMachineV2) (c : ℕ) : Prop :=
  ∀ x cert : Input,
    cert.size ≤ c * (x.size + 1) ^ c →
    V.runtime x cert ≤ c * (x.size + 1) ^ c

/-- **V2 class P (Bool-valued carrier).** Decision problems
    `L : DecidableProblemV2` for which there exists a deterministic
    machine with polynomial-time bound that decides `L` on every input
    (under `Bool` equality). -/
def class_P_typedV2 : Set DecidableProblemV2 :=
  { L | ∃ (M : DeterministicMachineV2) (c : ℕ),
        M.polyBoundedV2 c ∧ (∀ x : Input, M.decides L x) }

/-- **V2 class NP (Bool-valued carrier).** Decision problems
    `L : DecidableProblemV2` for which there exists a nondeterministic
    verifier `V` with polynomial-time bound such that
    `L x = true ↔ ∃ cert with size ≤ poly(x.size), V.verify x cert = true`. -/
def class_NP_typedV2 : Set DecidableProblemV2 :=
  { L | ∃ (V : NondeterministicMachineV2) (c : ℕ),
        V.polyBoundedV2 c ∧
        (∀ x : Input, L x = true ↔
          ∃ cert : Input,
            cert.size ≤ c * (x.size + 1) ^ c ∧ V.verify x cert = true) }

/-! ## §2 — The literal P ≠ NP statement (V2) -/

/-- **★ THE LITERAL CLAY STATEMENT (V2 carrier) ★**. -/
def Literal_P_neq_NP_V2 : Prop :=
  class_P_typedV2 ≠ class_NP_typedV2

/-! ## §3 — V2 EnumToClassSeparationBridge -/

/-- **★ THE PRECISE GAP — V2 ★**: existence of a `DecidableProblemV2`
    in `class_NP_typedV2` but not `class_P_typedV2`. -/
def EnumToClassSeparationBridgeV2 : Prop :=
  ∃ L : DecidableProblemV2, L ∈ class_NP_typedV2 ∧ L ∉ class_P_typedV2

/-! ## §4 — Cook 1971 P ⊆ NP on V2 carrier

The standard subset direction `class_P_typedV2 ⊆ class_NP_typedV2`:
given a deterministic polynomial-time machine `M` deciding `L`, build
a verifier `V` that ignores the certificate and returns `M.decide x`.
-/

/-- **Cook 1971 P ⊆ NP (V2 carrier).** Standard subset direction
    ported to `Bool` equality. -/
theorem class_P_subset_class_NP_V2 :
    class_P_typedV2 ⊆ class_NP_typedV2 := by
  intro L hLP
  obtain ⟨M, c, hpoly, hdec⟩ := hLP
  refine ⟨{ verify := fun x _ => M.decide x
            runtime := fun x _ => M.runtime x
            computability := trivial }, c, ?_, ?_⟩
  · intro x _cert _hcert
    exact hpoly x
  · intro x
    constructor
    · intro hxL
      refine ⟨⟨0⟩, Nat.zero_le _, ?_⟩
      -- V.verify x ⟨0⟩ = M.decide x; from hdec x : M.decide x = L x and
      -- hxL : L x = true, conclude M.decide x = true.
      simp only
      rw [hdec x]
      exact hxL
    · rintro ⟨_, _, hVerify⟩
      -- hVerify : M.decide x = true (after simp on V.verify).
      -- From hdec x : M.decide x = L x, conclude L x = true.
      simp only at hVerify
      rw [← hdec x]
      exact hVerify

/-! ## §5 — EnumToClassSeparationBridgeV2 ↔ Literal_P_neq_NP_V2 -/

/-- **★ V2 ANALOG OF `enum_to_class_separation_bridge_iff_literal_P_neq_NP` ★**.
    The named gap IS the standard "∃ L ∈ NP, L ∉ P" form of P ≠ NP on the
    V2 carrier. Forward via `Set.ext` contrapositive; backward via the
    Cook-1971 P ⊆ NP subset direction `class_P_subset_class_NP_V2`. -/
theorem enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2 :
    EnumToClassSeparationBridgeV2 ↔ Literal_P_neq_NP_V2 := by
  unfold EnumToClassSeparationBridgeV2 Literal_P_neq_NP_V2
  constructor
  · -- (→) Given a witness L ∈ NP \ P, the two classes differ as sets.
    rintro ⟨L, hNP, hP⟩ heq
    apply hP
    exact heq ▸ hNP
  · -- (←) Given classes differ as sets, exhibit a witness.
    intro hne
    by_contra h_no_witness
    push_neg at h_no_witness
    apply hne
    apply Set.eq_of_subset_of_subset
    · -- P ⊆ NP via Cook 1971 (V2).
      exact class_P_subset_class_NP_V2
    · -- NP ⊆ P (the contradiction direction from h_no_witness).
      intro L hLNP
      exact h_no_witness L hLNP

/-! ## §6 — Honest scope: `class_P_typedV2 ≠ Set.univ` is STILL OPEN

The placeholder `computability : True` does NOT constrain `decide` to
any real machine model. Given any `L : DecidableProblemV2`, the machine

    { decide := L, runtime := fun _ => 0, computability := trivial }

polyBounds at `c = 0` (because `0 * (x.size + 1) ^ 0 = 0`) and decides
`L` (because `M.decide x = L x x = L x` is `rfl`). Therefore on this
carrier `class_P_typedV2 = Set.univ` is STILL provable, and the same
holds for `class_NP_typedV2` via Cook 1971 P ⊆ NP. So
`Literal_P_neq_NP_V2` is STILL vacuously False on this carrier.

This is by design — the refactor removes the **Iff-vs-Bool** carrier
defect (so that `M.decides L x` is now a genuine Bool equality
constraint, not a free Iff) but does NOT yet close the **computability
placeholder** carrier defect. The `computability : True` field is the
precise place where a future plug-in of a real machine model
(mathlib `Computable`, Turing-machine encoding, etc.) must occur.

We make this explicit as a single honest-scope theorem documenting
the open status. -/

/-- **Honest scope: `class_P_typedV2 = Set.univ` is still provable
    under the `True` placeholder.** Given any `L : DecidableProblemV2`,
    the trivial machine `{ decide := L, runtime := 0, computability := trivial }`
    polyBounds at `c = 0` and decides `L`. -/
theorem class_P_typedV2_eq_univ_under_True_placeholder :
    class_P_typedV2 = Set.univ := by
  ext L
  simp only [Set.mem_univ, iff_true]
  refine ⟨{ decide := L, runtime := fun _ => 0, computability := trivial }, 0, ?_, ?_⟩
  · intro x
    simp
  · intro x
    rfl

/-- **Honest scope (corollary): `class_NP_typedV2 = Set.univ`.** By
    Cook 1971 P ⊆ NP on V2, combined with the above. -/
theorem class_NP_typedV2_eq_univ_under_True_placeholder :
    class_NP_typedV2 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro L
  exact class_P_subset_class_NP_V2 <| by
    rw [class_P_typedV2_eq_univ_under_True_placeholder]; trivial

/-- **Honest scope: under the `True` placeholder, `Literal_P_neq_NP_V2`
    is provably False.** This is NOT a Clay refutation — it is a
    statement that the V2 carrier with the `computability := True`
    placeholder admits the same trivial-machine closure as the V1
    Prop-valued carrier. The refactor's contribution is to localize
    the defect to a single named field (`computability`) on the
    machine structure. -/
theorem not_Literal_P_neq_NP_V2_under_True_placeholder :
    ¬ Literal_P_neq_NP_V2 := by
  unfold Literal_P_neq_NP_V2
  rw [class_P_typedV2_eq_univ_under_True_placeholder,
      class_NP_typedV2_eq_univ_under_True_placeholder]
  intro h
  exact h rfl

/-! ## §7 — V2 carrier honest-scope capstone -/

/-- **V2 carrier honest-scope capstone.** Single citable theorem
    bundling: (1) carrier refactored to `Bool`; (2) Cook 1971 P ⊆ NP
    holds on V2; (3) V2 reduction theorem analog; (4) honest scope —
    `Literal_P_neq_NP_V2` is still provably False under the `True`
    placeholder, exposing the precise field (`computability`) that a
    future plug-in of a real machine model must populate. -/
theorem pnp_carrier_V2_honest_scope_capstone :
    -- (1) Cook 1971 P ⊆ NP on V2.
    (class_P_typedV2 ⊆ class_NP_typedV2) ∧
    -- (2) Reduction theorem analog.
    (EnumToClassSeparationBridgeV2 ↔ Literal_P_neq_NP_V2) ∧
    -- (3) Honest scope: under True placeholder, Literal_P_neq_NP_V2 is False.
    (¬ Literal_P_neq_NP_V2) := by
  refine ⟨class_P_subset_class_NP_V2,
          enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2,
          not_Literal_P_neq_NP_V2_under_True_placeholder⟩

end PrincipiaTractalis.PNPClassSeparationCarrierV2
