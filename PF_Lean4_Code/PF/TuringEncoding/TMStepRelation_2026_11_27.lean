/-
# A step relation on `TMConfig` — the object V4 asked for

**Date**: 2026-11-27 (Legion).

`PF/TuringEncoding/PNPClassSeparationCarrierV4.lean` closes the V3
constant-encoding defect and then names, precisely, what it cannot do:

> No Clay-level discharge of `Literal_P_neq_NP_V4`. The carrier remains
> conditional on populating an actual TM-step transition relation linking
> `runtime` to TMConfig successor traces (the next refactor target, V5).

and again at its scope capstone:

> The next refactor (V5) would add the TM-step-relation constraint linking
> `runtime` to the number of configuration transitions from initial state.

**That relation did not exist anywhere in the corpus.** `TMConfig` carried a
state, a tape and a head position, and `encodeConfig` gave the prime-power
Gödel number of a configuration, but nothing said how one configuration
becomes the next. So `runtime` was a free field: a machine could carry any
step count at all, and the polynomial bound in `class_P_typedV4` constrained
that chosen number rather than any computation.

This file supplies the relation. It is deliberately small and total:

* `Move` — head displacement, three constructors.
* `TuringTable` — a deterministic transition function
  `next : ℕ → ℕ → ℕ × ℕ × Move` on (state, symbol read), plus a `halting`
  predicate on states.
* `step` — one transition. A halting state is a **fixed point**, so the
  dynamics are total and no partiality or `Option` is needed.
* `runFor` — iterate `step`.
* `HaltsIn δ c n` — halted after exactly `n` steps and at no earlier step.

## What makes it non-vacuous

A step relation is worthless if `step` could be the identity, or if
`HaltsIn` could hold of everything. §3 proves it is not:

* `step_ne_id_witness` exhibits a configuration the step relation genuinely
  moves;
* `counter_haltsIn_three` runs a concrete machine for exactly three
  transitions and halts, with the earlier steps proved *not* halting --- so
  `HaltsIn` pins a specific number, not merely some number;
* `haltsIn_unique` proves the halting time is unique, so
  "`runtime` is the halting time" is a genuine constraint on `runtime` rather
  than a satisfiable-by-choice one.

## Scope — what this does NOT do

It does not solve, or approach, Clay P vs NP, and nothing here should be read
that way. What it buys is narrower and real: a machine's step count can now be
*pinned to the number of transitions of an actual computation*, so a
polynomial-time hypothesis stated against it means polynomial time **of a
computation** rather than a bound on a field the machine author chose. Wiring
a V5 carrier to this relation is the next step and is deliberately not done in
this file.
-/
import PF.TuringEncoding.Basic

set_option autoImplicit false

namespace PrincipiaTractalis.TuringEncoding

/-! ## §1 — The transition data and the dynamics -/

/-- Head displacement for one transition. -/
inductive Move where
  | left : Move
  | stay : Move
  | right : Move
  deriving DecidableEq, Repr

/-- **A deterministic transition table.**

    `next q s` is the triple (new state, symbol written, head move) taken when
    the machine is in state `q` reading symbol `s`. `halting q` marks the
    states at which the machine stops. -/
structure TuringTable where
  /-- The transition function on (state, symbol read). -/
  next : ℕ → ℕ → ℕ × ℕ × Move
  /-- Which states are halting. -/
  halting : ℕ → Bool

/-- The symbol under the head. Cells beyond the written tape read blank, `0`. -/
def readSym (c : TMConfig) : ℕ := c.tape.getD c.headPos 0

/-- Write `s` at position `i`, extending the tape with blanks if the head has
    moved past the end. Total, by construction. -/
def writeAt (t : List ℕ) (i s : ℕ) : List ℕ :=
  if i < t.length then t.set i s
  else t ++ List.replicate (i - t.length) 0 ++ [s]

/-- Head displacement. `left` at position `0` stays at `0` (ℕ truncation), the
    usual one-ended-tape convention. -/
def moveHead : Move → ℕ → ℕ
  | Move.left, i => i - 1
  | Move.stay, i => i
  | Move.right, i => i + 1

/-- **One transition.** A halting state is a fixed point, which keeps `step`
    total and makes `runFor` well behaved past the halt. -/
def step (δ : TuringTable) (c : TMConfig) : TMConfig :=
  if δ.halting c.state then c
  else
    let r := δ.next c.state (readSym c)
    { state := r.1
      tape := writeAt c.tape c.headPos r.2.1
      headPos := moveHead r.2.2 c.headPos }

/-- **Run for `n` transitions.** -/
def runFor (δ : TuringTable) (c : TMConfig) : ℕ → TMConfig
  | 0 => c
  | n + 1 => step δ (runFor δ c n)

/-- **Halts after exactly `n` transitions**: halting at step `n`, and not
    halting at any earlier step. -/
def HaltsIn (δ : TuringTable) (c : TMConfig) (n : ℕ) : Prop :=
  δ.halting (runFor δ c n).state = true ∧
    ∀ m, m < n → δ.halting (runFor δ c m).state = false

/-! ## §2 — Elementary facts -/

/-- A halting configuration is a fixed point of `step`. -/
theorem step_of_halting {δ : TuringTable} {c : TMConfig}
    (h : δ.halting c.state = true) : step δ c = c := by
  unfold step
  simp [h]

/-- Once halted, the configuration never changes again. -/
theorem runFor_of_halting {δ : TuringTable} {c : TMConfig}
    (h : δ.halting c.state = true) (n : ℕ) : runFor δ c n = c := by
  induction n with
  | zero => rfl
  | succ k ih =>
      unfold runFor
      rw [ih]
      exact step_of_halting h

/-- **The halting time is unique.**

    This is what makes "`runtime x` is the halting time" a genuine constraint:
    there is at most one number it can be. -/
theorem haltsIn_unique {δ : TuringTable} {c : TMConfig} {m n : ℕ}
    (hm : HaltsIn δ c m) (hn : HaltsIn δ c n) : m = n := by
  by_contra hne
  rcases Nat.lt_or_ge m n with h | h
  · have := hn.2 m h
    rw [hm.1] at this
    exact absurd this (by simp)
  · have hlt : n < m := lt_of_le_of_ne h (fun e => hne e.symm)
    have := hm.2 n hlt
    rw [hn.1] at this
    exact absurd this (by simp)

/-! ## §3 — The relation has content -/

/-- A two-state table that advances the state and leaves the tape alone. -/
def counterTable : TuringTable where
  next := fun q s => (q + 1, s, Move.stay)
  halting := fun q => q == 3

/-- The starting configuration for the counter: state `0`, one blank cell. -/
def counterStart : TMConfig := { state := 0, tape := [0], headPos := 0 }

/-- **`step` genuinely moves this configuration** --- it is not the identity,
    so the dynamics are not trivial. -/
theorem step_ne_id_witness :
    step counterTable counterStart ≠ counterStart := by
  intro h
  have : (step counterTable counterStart).state = counterStart.state :=
    congrArg TMConfig.state h
  simp [step, counterTable, counterStart, readSym, writeAt, moveHead] at this

/-- **The counter runs for exactly three transitions and halts there.**

    `HaltsIn` therefore pins a specific step count: three, and not zero, one or
    two. Together with `haltsIn_unique` this is what a `runtime` field can be
    held to. -/
theorem counter_haltsIn_three :
    HaltsIn counterTable counterStart 3 := by
  constructor
  · simp [runFor, step, counterTable, counterStart, readSym, writeAt, moveHead]
  · intro m hm
    interval_cases m <;>
      simp [runFor, step, counterTable, counterStart, readSym, writeAt, moveHead]

/-- **The encoded configuration of a run is always positive**, so a step
    relation composes with the existing Gödel encoding without a side
    condition. -/
theorem encodeConfig_runFor_positive (δ : TuringTable) (c : TMConfig) (n : ℕ) :
    encodeConfig (runFor δ c n) > 0 :=
  encodeConfig_positive _

end PrincipiaTractalis.TuringEncoding
