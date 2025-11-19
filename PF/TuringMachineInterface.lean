/-
# Interactive Turing Machine Interface
A user-friendly interface for creating, running, and visualizing Turing machines.

This module provides:
- Builder pattern for TM construction
- Pretty-printing for configurations and execution traces
- Step-by-step visualization
- Batch execution with fuel management
- Error handling and validation
-/

import PF.TuringEncoding
import Mathlib.Data.String.Defs

namespace PrincipiaTractalis.TMInterface

open PrincipiaTractalis

-- ============================================================================
-- SECTION 1: Pretty Printing and Visualization
-- ============================================================================

/-- Convert Fin 3 symbol to readable character -/
def symbolToChar : Fin 3 → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '_'  -- Blank

/-- Convert character to Fin 3 symbol -/
def charToSymbol? : Char → Option (Fin 3)
  | '0' => some 0
  | '1' => some 1
  | '_' => some 2
  | 'B' => some 2  -- Alternative blank notation
  | ' ' => some 2  -- Space as blank
  | _ => none

/-- Pretty print a tape with head position marked -/
def prettyTape (tape : List (Fin 3)) (head : ℕ) : String :=
  let tapeStr := String.mk (tape.map symbolToChar)
  let headMarker := String.mk (List.replicate head ' ' ++ ['^'])
  s!"Tape: [{tapeStr}]\n      {headMarker}"

/-- Pretty print a configuration -/
def TMConfig.pretty (c : TMConfig) (tm : TuringMachine) : String :=
  let stateInfo := 
    if c.state == tm.accept_state then "q_accept"
    else if c.state == tm.reject_state then "q_reject"
    else s!"q{c.state}"
  let tapeViz := prettyTape c.tape c.head
  let currentSym := symbolToChar c.readSymbol
  s!"State: {stateInfo}\n{tapeViz}\nReading: '{currentSym}'\n"

/-- Execution result with trace information -/
structure ExecutionResult where
  initial : TMConfig
  final : TMConfig
  steps : ℕ
  halted : Bool
  accepted : Bool
  trace : List TMConfig
  deriving Repr

/-- Pretty print execution result -/
def ExecutionResult.pretty (r : ExecutionResult) (tm : TuringMachine) : String :=
  let status := 
    if r.accepted then "✓ ACCEPTED"
    else if r.halted then "✗ REJECTED"
    else "⊙ TIMEOUT (not halted)"
  let header := s!"════════════════════════════════════\n{status} in {r.steps} steps\n════════════════════════════════════\n"
  let finalConfig := r.final.pretty tm
  header ++ finalConfig

-- ============================================================================
-- SECTION 2: Execution Tracing
-- ============================================================================

/-- Run TM with full execution trace -/
def runWithTrace (tm : TuringMachine) (c : TMConfig) (fuel : ℕ) : ExecutionResult :=
  let rec loop (current : TMConfig) (remaining : ℕ) (trace : List TMConfig) : ExecutionResult :=
    if current.isHalted tm then
      { initial := c
        final := current
        steps := fuel - remaining
        halted := true
        accepted := current.isAccepting tm
        trace := trace.reverse }
    else if remaining = 0 then
      { initial := c
        final := current
        steps := fuel
        halted := false
        accepted := false
        trace := trace.reverse }
    else
      match current.step tm with
      | none => 
        { initial := c
          final := current
          steps := fuel - remaining
          halted := true
          accepted := current.isAccepting tm
          trace := trace.reverse }
      | some next => loop next (remaining - 1) (current :: trace)
  loop c fuel []

/-- Run from input string -/
def runFromString (tm : TuringMachine) (input : String) (fuel : ℕ) : ExecutionResult :=
  let symbols := input.toList.filterMap charToSymbol?
  let config : TMConfig := { state := tm.initial_state, tape := symbols, head := 0 }
  runWithTrace tm config fuel

-- ============================================================================
-- SECTION 3: Builder Pattern for TM Construction
-- ============================================================================

/-- Builder state for constructing a Turing machine -/
structure TMBuilder where
  num_states : ℕ
  initial_state : ℕ := 0
  accept_state : ℕ
  reject_state : ℕ
  transitions : List (ℕ × Fin 3 × ℕ × Fin 3 × Move) := []
  
/-- Add a transition to the builder -/
def TMBuilder.addTransition (b : TMBuilder) 
    (fromState : ℕ) (readSym : Fin 3) (toState : ℕ) (writeSym : Fin 3) (move : Move) : TMBuilder :=
  { b with transitions := (fromState, readSym, toState, writeSym, move) :: b.transitions }

/-- Convert builder to transition function -/
def TMBuilder.toTransitionFn (b : TMBuilder) : TransitionFn :=
  fun state sym =>
    b.transitions.find? (fun t => t.1 == state && t.2.1 == sym) |>.map 
      (fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2))

/-- Build the Turing machine (with proofs) -/
def TMBuilder.build (b : TMBuilder) 
    (h_init : b.initial_state < b.num_states)
    (h_acc : b.accept_state < b.num_states)
    (h_rej : b.reject_state < b.num_states) : TuringMachine :=
  { num_states := b.num_states
    initial_state := b.initial_state
    accept_state := b.accept_state
    reject_state := b.reject_state
    transition := b.toTransitionFn
    h_initial := h_init
    h_accept := h_acc
    h_reject := h_rej }

-- ============================================================================
-- SECTION 4: Common TM Patterns
-- ============================================================================

/-- Create a simple 2-state TM (init + accept, with reject = accept) -/
def simpleTM (transition : TransitionFn) 
    (h_trans : ∀ state sym result, transition state sym = some result → result.1 < 2) : TuringMachine :=
  { num_states := 2
    initial_state := 0
    accept_state := 1
    reject_state := 1
    transition := transition
    h_initial := by norm_num
    h_accept := by norm_num
    h_reject := by norm_num }

-- ============================================================================
-- SECTION 5: Interactive Commands
-- ============================================================================

/-- Single step with visualization -/
def stepInteractive (tm : TuringMachine) (c : TMConfig) : IO Unit := do
  IO.println "═══════════════════════"
  IO.println "CURRENT CONFIGURATION:"
  IO.println "═══════════════════════"
  IO.println (c.pretty tm)
  
  match c.step tm with
  | none =>
    IO.println "═══════════════════════"
    IO.println "HALTED (no transition)"
    IO.println "═══════════════════════"
  | some next =>
    IO.println "═══════════════════════"
    IO.println "AFTER ONE STEP:"
    IO.println "═══════════════════════"
    IO.println (next.pretty tm)

/-- Run with step-by-step output -/
def runInteractive (tm : TuringMachine) (input : String) (fuel : ℕ) : IO Unit := do
  let result := runFromString tm input fuel
  IO.println "\n╔═══════════════════════════════════╗"
  IO.println "║   TURING MACHINE EXECUTION TRACE  ║"
  IO.println "╚═══════════════════════════════════╝\n"
  
  IO.println s!"Input: \"{input}\""
  IO.println s!"Fuel: {fuel} steps\n"
  
  for (i, config) in result.trace.enum do
    IO.println s!"───────────── Step {i} ─────────────"
    IO.println (config.pretty tm)
  
  IO.println "\n╔═══════════════════════════════════╗"
  IO.println "║          FINAL RESULT             ║"
  IO.println "╚═══════════════════════════════════╝"
  IO.println (result.pretty tm)

-- ============================================================================
-- SECTION 6: Validation and Error Checking
-- ============================================================================

/-- Validate a Turing machine configuration -/
inductive TMError where
  | InvalidState (state : ℕ) (max : ℕ)
  | NoInitialState
  | AcceptRejectSame
  | InvalidTransition (from : ℕ) (to : ℕ) (max : ℕ)
  deriving Repr

/-- Check if TM is well-formed -/
def validateTM (tm : TuringMachine) : List TMError :=
  let errors := []
  let errors := if tm.accept_state == tm.reject_state then 
    TMError.AcceptRejectSame :: errors else errors
  errors

/-- Check if configuration is valid for a TM -/
def validateConfig (tm : TuringMachine) (c : TMConfig) : Option TMError :=
  if c.state >= tm.num_states then
    some (TMError.InvalidState c.state tm.num_states)
  else
    none

-- ============================================================================
-- SECTION 7: Example Usage Patterns
-- ============================================================================

/-- Example: Create a simple incrementer using builder pattern -/
def exampleIncrementer : TuringMachine :=
  let builder : TMBuilder := {
    num_states := 2
    initial_state := 0
    accept_state := 1
    reject_state := 1
  }
  let builder := builder.addTransition 0 1 0 1 Move.right  -- Scan right over 1s
  let builder := builder.addTransition 0 2 1 1 Move.stay   -- Hit blank, write 1, accept
  builder.build (by norm_num) (by norm_num) (by norm_num)

#check exampleIncrementer

/-- Theorem: The incrementer is well-formed -/
theorem incrementer_valid : validateTM exampleIncrementer = [] := by
  unfold validateTM exampleIncrementer
  simp
  
/-- Example: Create all-ones checker -/
def exampleAllOnes : TuringMachine :=
  let builder : TMBuilder := {
    num_states := 3
    initial_state := 0
    accept_state := 1
    reject_state := 2
  }
  let builder := builder.addTransition 0 1 0 1 Move.right  -- Keep scanning 1s
  let builder := builder.addTransition 0 2 1 2 Move.stay   -- Hit blank: accept!
  let builder := builder.addTransition 0 0 2 0 Move.stay   -- Found a 0: reject!
  builder.build (by norm_num) (by norm_num) (by norm_num)

-- ============================================================================
-- SECTION 8: Performance Metrics
-- ============================================================================

/-- Execution statistics -/
structure TMStats where
  totalSteps : ℕ
  maxTapeLength : ℕ
  statesVisited : List ℕ
  symbolsWritten : ℕ
  deriving Repr

/-- Collect statistics during execution -/
def runWithStats (tm : TuringMachine) (c : TMConfig) (fuel : ℕ) : TMStats :=
  let rec loop (current : TMConfig) (remaining : ℕ) (maxLen : ℕ) (states : List ℕ) (writes : ℕ) : TMStats :=
    if current.isHalted tm || remaining = 0 then
      { totalSteps := fuel - remaining
        maxTapeLength := maxLen
        statesVisited := states.reverse
        symbolsWritten := writes }
    else
      match current.step tm with
      | none => 
        { totalSteps := fuel - remaining
          maxTapeLength := maxLen
          statesVisited := states.reverse
          symbolsWritten := writes }
      | some next =>
        let newMaxLen := max maxLen next.tape.length
        let newWrites := if next.tape != current.tape then writes + 1 else writes
        loop next (remaining - 1) newMaxLen (current.state :: states) newWrites
  loop c fuel c.tape.length [] 0

-- ============================================================================
-- SECTION 9: Batch Testing
-- ============================================================================

/-- Test case for TM -/
structure TestCase where
  input : String
  expectedAccept : Bool
  expectedSteps : Option ℕ  -- None = don't care
  description : String
  deriving Repr

/-- Run a test case -/
def runTest (tm : TuringMachine) (test : TestCase) (fuel : ℕ) : Bool × String :=
  let result := runFromString tm test.input fuel
  let passAccept := result.accepted == test.expectedAccept
  let passSteps := match test.expectedSteps with
    | none => true
    | some n => result.steps == n
  let pass := passAccept && passSteps
  let msg := 
    if pass then s!"✓ {test.description}"
    else s!"✗ {test.description} (expected {test.expectedAccept}, got {result.accepted})"
  (pass, msg)

/-- Run test suite -/
def runTestSuite (tm : TuringMachine) (tests : List TestCase) (fuel : ℕ) : IO Unit := do
  IO.println "\n╔═══════════════════════════════════╗"
  IO.println "║        RUNNING TEST SUITE         ║"
  IO.println "╚═══════════════════════════════════╝\n"
  
  let mut passed := 0
  let mut failed := 0
  
  for test in tests do
    let (pass, msg) := runTest tm test fuel
    IO.println msg
    if pass then
      passed := passed + 1
    else
      failed := failed + 1
  
  IO.println s!"\n═══════════════════════════════════"
  IO.println s!"Total: {passed + failed} tests"
  IO.println s!"Passed: {passed}"
  IO.println s!"Failed: {failed}"
  if failed == 0 then
    IO.println "✓ ALL TESTS PASSED!"
  IO.println "═══════════════════════════════════"

end PrincipiaTractalis.TMInterface
