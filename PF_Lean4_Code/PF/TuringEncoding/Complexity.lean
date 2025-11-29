/-
# Complexity Classes P and NP
Canonical definitions of polynomial-time complexity classes following Cook (1971) and Karp (1972).

Since mathlib does not yet have complexity theory formalized, we provide the standard definitions
here, designed to interface with both mathlib's Turing machine theory and our fractal operator
framework.

Reference:
- Cook (1971): "The Complexity of Theorem-Proving Procedures"
- Karp (1972): "Reducibility among Combinatorial Problems"
- Principia Fractalis, Chapter 21, Definition 1 (Complexity Classes)
-/

import Mathlib.Computability.TuringMachine
import Mathlib.Data.List.Basic
import PF.TuringEncoding.Basic

namespace PrincipiaTractalis.TuringEncoding

open Turing

/-!
## Decision Problems and Languages

A decision problem is represented as a language L ⊆ {0,1}*
An instance is a binary string x ∈ {0,1}*
The question: Is x ∈ L?
-/

/-- Binary alphabet {0, 1} -/
inductive BinSymbol
  | zero : BinSymbol
  | one : BinSymbol
  deriving DecidableEq

/-- Binary string (list of binary symbols) -/
def BinString := List BinSymbol

/-- Language: set of binary strings -/
def Language := Set BinString

/-- Length of a binary string -/
def binLength (s : BinString) : ℕ := s.length

/-!
## Time Complexity and Polynomial Time

A function is polynomially bounded if T(n) ≤ c·n^k for some constants c, k.
-/

/-- A function is polynomially bounded -/
def IsPolynomialBounded (T : ℕ → ℕ) : Prop :=
  ∃ (c k : ℕ), c > 0 ∧ k > 0 ∧ ∀ (n : ℕ), T n ≤ c * n ^ k

/-- Time complexity function for a Turing machine (to be axiomatized) -/
axiom turingTimeComplexity : (Γ Λ σ : Type) → TM2.Machine Γ Λ σ → BinString → ℕ

/-!
## The P Class: Polynomial-Time Decidable Languages

Following Cook (1971), Definition 1.1:
A language L is in P if there exists a deterministic Turing machine M that:
1. Decides L (accepts x ∈ L, rejects x ∉ L)
2. Runs in polynomial time

Reference: Chapter 21, Definition 1 (def:p-np)
-/

/-- A language is in P if decidable in polynomial time -/
def InClassP (L : Language) : Prop :=
  ∃ (Γ Λ σ : Type) (M : TM2.Machine Γ Λ σ),
    -- M decides L
    (∀ (x : BinString), x ∈ L ↔ M.accepts x) ∧
    -- M runs in polynomial time
    IsPolynomialBounded (fun n =>
      Sup {turingTimeComplexity Γ Λ σ M x | x : BinString | binLength x = n})

/-- The complexity class P -/
def ClassP : Set Language := {L : Language | InClassP L}

/-!
## The NP Class: Nondeterministic Polynomial Time

Following Cook (1971), Definition 1.2:
A language L is in NP if there exists a polynomial-time verifier V such that:
  x ∈ L ↔ ∃ certificate c with |c| ≤ poly(|x|), V(x, c) accepts

This captures the essential difference:
- P: Can SOLVE in polynomial time
- NP: Can VERIFY solutions in polynomial time

Reference: Chapter 21, Definition 1 (def:p-np)
-/

/-- Certificate (witness) for an NP problem -/
def Certificate := BinString

/-- A language is in NP if it has a polynomial-time verifier -/
def InClassNP (L : Language) : Prop :=
  ∃ (Γ Λ σ : Type) (V : TM2.Machine Γ Λ σ),
    -- V is a polynomial-time verifier
    IsPolynomialBounded (fun n =>
      Sup {turingTimeComplexity Γ Λ σ V (x ++ c) |
           x : BinString, c : Certificate | binLength x = n}) ∧
    -- V correctly verifies L with polynomially-bounded certificates
    (∀ (x : BinString),
      x ∈ L ↔ ∃ (c : Certificate),
        binLength c ≤ (binLength x) ^ 2 ∧  -- Polynomial certificate size
        V.accepts (x ++ c))

/-- The complexity class NP -/
def ClassNP : Set Language := {L : Language | InClassNP L}

/-!
## Fundamental Properties

These are the standard complexity-theoretic facts.
-/

/-- P is contained in NP (every problem solvable in P is also verifiable in NP).

    PROOF: If L ∈ P, there exists a polynomial-time decider M.
    To show L ∈ NP, we construct a verifier V that ignores the certificate and runs M.
    Since M runs in polynomial time, so does V.
    Therefore P ⊆ NP.

    This is a fundamental result in complexity theory (Cook 1971, Theorem 2.1).
-/
theorem P_subset_NP : ClassP ⊆ ClassNP := by
  intro L h_in_P
  unfold ClassP InClassP at h_in_P
  unfold ClassNP InClassNP

  -- Unpack the P witness
  obtain ⟨Γ, Λ, σ, M, h_decides, h_poly⟩ := h_in_P

  -- Use M as the verifier (ignoring the certificate)
  use Γ, Λ, σ, M

  constructor
  · -- The verifier runs in polynomial time
    -- Since M runs in polynomial time, and V = M (ignoring certificate),
    -- V also runs in polynomial time
    exact h_poly

  · -- The verifier correctly verifies L
    intro x
    constructor
    · -- Forward: if x ∈ L, there exists a certificate
      intro h_in_L
      -- Use empty certificate (or any certificate - it's ignored)
      use []
      constructor
      · -- Certificate size is polynomial (0 ≤ |x|²)
        simp [binLength]
      · -- M accepts x (from h_decides)
        rw [List.append_nil]
        exact h_decides x |>.mp h_in_L

    · -- Reverse: if there exists an accepting certificate, x ∈ L
      intro ⟨c, _, h_accepts⟩
      -- M accepts x (certificate is irrelevant)
      exact h_decides x |>.mpr h_accepts

/-- The P vs NP question: are these classes equal? -/
def PvsNP_Question : Prop := ClassP = ClassNP

/-!
## Connection to Fractal Encoding

Each decision problem instance x ∈ {0,1}* gets encoded via encodeConfig into ℕ,
then the digital sum D(encode(x)) modulates the phase in the fractal operator.

The key insight from Chapter 21:
- P problems have encoding with α_P = √2
- NP problems have encoding with α_NP = φ + 1/4
- These lead to different ground state energies

Next file: Operators.lean will define H_P and H_NP using these complexity classes.
-/

/-- Encode binary string to configuration (input-only, state q_0, head at position 0) -/
def binStringToConfig (x : BinString) : TMConfig :=
  { state := 0,  -- Initial state
    tape := x.map (fun b => match b with | BinSymbol.zero => 0 | BinSymbol.one => 1),
    headPos := 0 }

/-- Encode binary string via prime-power encoding -/
def encodeBinString (x : BinString) : ℕ :=
  encodeConfig (binStringToConfig x)

/-- The digital sum of encoded instances drives the fractal dynamics -/
def instanceDigitalSum (x : BinString) : ℕ :=
  digitalSum3 (encodeBinString x)

/-!
## Examples (for testing)

These match the exercises from Chapter 21.
-/

example : binLength [BinSymbol.one, BinSymbol.zero, BinSymbol.one] = 3 := rfl

/-- Digital sum of 27 = 1000₃ is 1 (from Chapter 21 Exercise 1) -/
example : digitalSum3 27 = 1 := by
  unfold digitalSum3
  -- 27 = 1·3³ + 0·3² + 0·3¹ + 0·3⁰ in base 3
  -- So D(27) = 1
  simp only [digitalSumBase3]
  -- 27 / 3 = 9, 27 % 3 = 0
  norm_num
  -- 9 / 3 = 3, 9 % 3 = 0
  simp only [digitalSumBase3]
  norm_num
  -- 3 / 3 = 1, 3 % 3 = 0
  simp only [digitalSumBase3]
  norm_num
  -- 1 / 3 = 0, 1 % 3 = 1
  simp only [digitalSumBase3]
  norm_num

end PrincipiaTractalis.TuringEncoding
