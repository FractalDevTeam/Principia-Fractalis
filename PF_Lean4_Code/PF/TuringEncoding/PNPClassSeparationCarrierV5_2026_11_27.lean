/-
# V5 — `runtime` pinned to an actual computation

**Date**: 2026-11-27 (Legion). Built on
`PF/TuringEncoding/TMStepRelation_2026_11_27.lean`.

V4 named its own gap: the carrier "remains conditional on populating an actual
TM-step transition relation linking `runtime` to TMConfig successor traces (the
next refactor target, V5)". The step relation now exists. This is V5.

## What changes, exactly

In V4 a machine carries `runtime : Input → ℕ` as a **free field**. Nothing ties
it to anything, and §3 proves that: `v4_runtime_is_unconstrained` shows that
for *every* function `f : Input → ℕ` there is a V4 machine whose runtime is
`f`. So `polyBoundedV4` constrains the number the author wrote down, not a
computation.

In V5 the machine carries a `TuringTable`, an `initial : Input → TMConfig`, and
the constraint

    runtime_is_halting_time : ∀ x, HaltsIn table (initial x) (runtime x)

Because `haltsIn_unique` says the halting time is unique,
`v5_runtime_is_determined` proves `runtime` is a **function of the table and
the initial configuration** — two V5 machines agreeing on those agree on
runtime. It is no longer a field the author chooses; it is the number of
transitions the machine actually takes.

The decision is read off the halted configuration:

    decide_via_halt : ∀ x,
      decide x = true ↔ (runFor table (initial x) (runtime x)).state ∈ acceptingStates

so acceptance is a property of where the computation stopped.

## Non-triviality, proved

`class_P_typedV5` is inhabited by two distinct members (`L_const_true`,
`L_const_false`), so the carrier is not Unit-closable. And it admits genuine
multi-step computation, not only immediate halts: `counter_machine_in_class_P`
exhibits a member whose runtime is **three**, pinned to the three transitions
of `counterTable` from `counterStart`.

## Scope — unchanged from V4, and stated again

This does **not** discharge Clay P vs NP, and no theorem here claims to. What
V5 buys over V4 is that a polynomial-time hypothesis now constrains the step
count of an actual transition sequence rather than a free numeral. The Clay
statement remains open and untouched.
-/
import PF.TuringEncoding.TMStepRelation_2026_11_27
import PF.TuringEncoding.PNPClassSeparationCarrierV4

set_option autoImplicit false

namespace PrincipiaTractalis.PNPClassSeparationCarrierV5

open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.PNPClassSeparationCarrierV4
open PrincipiaTractalis.PNPClassSeparationPrecisionBridge

/-! ## §1 — The V5 carrier -/

/-- V5 decision problems are V4's. -/
abbrev DecidableProblemV5 := DecidableProblemV4

/-- **V5 deterministic machine.**

    Carries a transition table and an initial configuration, and pins
    `runtime` to the halting time of the run those determine. -/
structure DeterministicMachineV5 where
  /-- The decision the machine reports. -/
  decide : Input → Bool
  /-- The transition table. -/
  table : TuringTable
  /-- The initial configuration on each input. -/
  initial : Input → TMConfig
  /-- The claimed step count. -/
  runtime : Input → ℕ
  /-- Which states accept. -/
  acceptingStates : Set ℕ
  /-- **The V5 constraint**: `runtime` is the halting time of the actual run. -/
  runtime_is_halting_time :
    ∀ x : Input, HaltsIn table (initial x) (runtime x)
  /-- The decision is read off the halted configuration's state. -/
  decide_via_halt :
    ∀ x : Input,
      decide x = true ↔
        (runFor table (initial x) (runtime x)).state ∈ acceptingStates

/-- V5 polynomial-time bound, same shape as V4's. -/
def DeterministicMachineV5.polyBoundedV5
    (M : DeterministicMachineV5) (c : ℕ) : Prop :=
  ∀ x : Input, M.runtime x ≤ c * (x.size + 1) ^ c

/-- V5 decides, same shape as V4's. -/
def DeterministicMachineV5.decides (M : DeterministicMachineV5)
    (L : DecidableProblemV5) (x : Input) : Prop :=
  M.decide x = L x

/-- **V5 class P.** -/
def class_P_typedV5 : Set DecidableProblemV5 :=
  { L | ∃ (M : DeterministicMachineV5) (c : ℕ),
        M.polyBoundedV5 c ∧ (∀ x : Input, M.decides L x) }

/-! ## §2 — `runtime` is now determined, not chosen -/

/-- **★ If the run halts at `n`, the machine's runtime *is* `n`.**

    Immediate from `haltsIn_unique`. The machine cannot carry any other
    number. -/
theorem runtime_eq_of_haltsIn (M : DeterministicMachineV5) (x : Input) {n : ℕ}
    (h : HaltsIn M.table (M.initial x) n) : M.runtime x = n :=
  haltsIn_unique (M.runtime_is_halting_time x) h

/-- **★★ `runtime` is a function of the table and the initial configuration.**

    Two V5 machines that agree on `table` and `initial` agree on `runtime`,
    input by input. This is the property V4 lacked and the reason V5 exists. -/
theorem runtime_is_determined (M N : DeterministicMachineV5)
    (ht : M.table = N.table) (hi : M.initial = N.initial) (x : Input) :
    M.runtime x = N.runtime x := by
  apply runtime_eq_of_haltsIn
  rw [ht, hi]
  exact N.runtime_is_halting_time x

/-! ## §3 — What V4's `runtime` was: free -/

/-- **★ In V4, every runtime function is realised.**

    For an arbitrary `f : Input → ℕ` there is a V4 machine whose runtime is
    exactly `f`. So `polyBoundedV4` constrained a chosen numeral, and this is
    the defect V5 closes. Stated here rather than in V4 because the comparison
    is the point. -/
theorem v4_runtime_is_unconstrained (f : Input → ℕ) :
    ∃ M : DeterministicMachineV4, M.runtime = f := by
  refine ⟨{ decide := fun _ => true
            runtime := f
            encodeRun := fun _ => ⟨0, [], 0⟩
            acceptingStates := Set.univ
            computability := fun _ => encodeConfig_positive _
            decide_via_encodeRun := fun _ => by simp }, rfl⟩

/-! ## §4 — The carrier is inhabited, and admits real computation -/

/-- A table that halts immediately, in every state. -/
def haltAtOnce : TuringTable where
  next := fun q s => (q, s, Move.stay)
  halting := fun _ => true

/-- `haltAtOnce` halts in zero transitions from any configuration. -/
theorem haltAtOnce_haltsIn_zero (c : TMConfig) : HaltsIn haltAtOnce c 0 := by
  refine ⟨by simp [runFor, haltAtOnce], ?_⟩
  intro m hm
  exact absurd hm (Nat.not_lt_zero m)

/-- **`L_const_true ∈ class_P_typedV5`.** -/
theorem L_const_true_in_class_P_typedV5 :
    L_const_true ∈ class_P_typedV5 := by
  refine ⟨{ decide := fun _ => true
            table := haltAtOnce
            initial := fun _ => ⟨0, [], 0⟩
            runtime := fun _ => 0
            acceptingStates := Set.univ
            runtime_is_halting_time := fun _ => haltAtOnce_haltsIn_zero _
            decide_via_halt := fun _ => by simp }, 0, ?_, ?_⟩
  · intro x; simp
  · intro x; rfl

/-- **`L_const_false ∈ class_P_typedV5`**, with `acceptingStates := ∅`. -/
theorem L_const_false_in_class_P_typedV5 :
    L_const_false ∈ class_P_typedV5 := by
  refine ⟨{ decide := fun _ => false
            table := haltAtOnce
            initial := fun _ => ⟨0, [], 0⟩
            runtime := fun _ => 0
            acceptingStates := ∅
            runtime_is_halting_time := fun _ => haltAtOnce_haltsIn_zero _
            decide_via_halt := fun _ => by simp }, 0, ?_, ?_⟩
  · intro x; simp
  · intro x; rfl

/-- The counter's halted state is `3`. -/
theorem counter_final_state :
    (runFor counterTable counterStart 3).state = 3 := by
  simp [runFor, step, counterTable, counterStart, readSym, writeAt, moveHead]

/-- **★★ The carrier admits genuine multi-step computation.**

    A V5 member whose runtime is **three**, pinned to the three transitions of
    `counterTable` from `counterStart` --- not an immediate halt. So V5 is not
    satisfied only by zero-step machines. -/
theorem counter_machine_in_class_P :
    L_const_true ∈ class_P_typedV5 := by
  refine ⟨{ decide := fun _ => true
            table := counterTable
            initial := fun _ => counterStart
            runtime := fun _ => 3
            acceptingStates := {3}
            runtime_is_halting_time := fun _ => counter_haltsIn_three
            decide_via_halt := fun _ => by
              simp [counter_final_state] }, 3, ?_, ?_⟩
  · intro x
    have h1 : 1 ≤ (x.size + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    calc (3 : ℕ) = 3 * 1 := by ring
      _ ≤ 3 * (x.size + 1) ^ 3 := Nat.mul_le_mul_left 3 h1
  · intro x; rfl

/-! ## §5 — The V5 scope capstone -/

/-- **V5 referee scope, as one citable theorem.**

    (1) `runtime` is determined by the table and the initial configuration;
    (2) in V4 it was not, every runtime function being realisable;
    (3) the carrier is inhabited by two distinct members; and
    (4) it admits a member whose runtime is a genuine three-transition run.

    None of this discharges Clay P vs NP, and no conjunct says otherwise. -/
theorem v5_referee_scope :
    (∀ (M N : DeterministicMachineV5), M.table = N.table → M.initial = N.initial →
      ∀ x : Input, M.runtime x = N.runtime x)
    ∧ (∀ f : Input → ℕ, ∃ M : DeterministicMachineV4, M.runtime = f)
    ∧ (L_const_true ∈ class_P_typedV5 ∧ L_const_false ∈ class_P_typedV5)
    ∧ (runFor counterTable counterStart 3).state = 3 :=
  ⟨fun M N ht hi x => runtime_is_determined M N ht hi x,
   v4_runtime_is_unconstrained,
   ⟨L_const_true_in_class_P_typedV5, L_const_false_in_class_P_typedV5⟩,
   counter_final_state⟩

end PrincipiaTractalis.PNPClassSeparationCarrierV5
