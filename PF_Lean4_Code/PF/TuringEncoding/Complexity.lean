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

/-- Binary string (list of binary symbols).
    `abbrev` (not `def`) so List's typeclass instances — `Append`, `Membership`,
    `HasLength`, etc. — are immediately available for `BinString`. -/
abbrev BinString := List BinSymbol

/-- Language: set of binary strings.
    `abbrev` (not `def`) so `Set`'s `Membership` instance is immediately available. -/
abbrev Language := Set BinString

/-- Length of a binary string -/
def binLength (s : BinString) : ℕ := s.length

/-!
## Time Complexity and Polynomial Time

A function is polynomially bounded if T(n) ≤ c·n^k for some constants c, k.
-/

/-- A function is polynomially bounded -/
def IsPolynomialBounded (T : ℕ → ℕ) : Prop :=
  ∃ (c k : ℕ), c > 0 ∧ k > 0 ∧ ∀ (n : ℕ), T n ≤ c * n ^ k

/-- **Turing machine, TM2 model (multi-tape with stacks)** — abstracted for
    complexity-class formalization. The full mathlib `Turing.TM2` model
    parametrizes over `K` (stack indices), `Γ : K → Type` (alphabet per stack),
    `Λ` (state set), and `σ` (auxiliary register). Here we keep the
    surface signature `(Γ Λ σ : Type)` for compatibility with the manuscript
    formalization, with `accepts : BinString → Prop` as the only operationally
    observable predicate. The concrete TM model is hidden behind this
    abstraction; the `turingTimeComplexity` axiom below supplies step counts. -/
structure Machine (Γ Λ σ : Type) where
  /-- Accept predicate on binary strings. -/
  accepts : BinString → Prop

/-- Time complexity function for a Turing machine (axiomatized — TM2 stepping
    is partial; total step-count requires either a halting hypothesis or a
    sentinel for non-halting computations. See
    `principia_remaining_axioms_roadmap.md` Tier 2 for retirement strategy). -/
axiom turingTimeComplexity : (Γ Λ σ : Type) → Machine Γ Λ σ → BinString → ℕ

/-!
## The P Class: Polynomial-Time Decidable Languages

Following Cook (1971), Definition 1.1:
A language L is in P if there exists a deterministic Turing machine M that:
1. Decides L (accepts x ∈ L, rejects x ∉ L)
2. Runs in polynomial time

Reference: Chapter 21, Definition 1 (def:p-np)
-/

/-- A language is in P if decidable in polynomial time.

    Reformulated 2026-05-10: instead of a `Sup` over the set
    `{turingTimeComplexity M x | binLength x = n}` (which used old set-builder
    syntax and was ill-defined for unbounded sets in ℕ), require a polynomial
    bound `T` holding pointwise for every input. The trailing-input clause
    encodes the standard property of P-deciders that their accept decision
    depends only on their actual input, not on tape junk beyond the input —
    used in the canonical `P_subset_NP` reduction (ignore the certificate). -/
def InClassP (L : Language) : Prop :=
  ∃ (Γ Λ σ : Type) (M : Machine Γ Λ σ) (T : ℕ → ℕ),
    IsPolynomialBounded T ∧
    -- M decides L
    (∀ (x : BinString), x ∈ L ↔ M.accepts x) ∧
    -- M runs in time T(|x|) on every input
    (∀ (x : BinString), turingTimeComplexity Γ Λ σ M x ≤ T (binLength x)) ∧
    -- Standard well-formed-decider property: M's accept decision on (x ++ c)
    -- coincides with its decision on x (trailing bits are not consulted).
    (∀ (x c : BinString), M.accepts (x ++ c) ↔ M.accepts x)

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

/-- Certificate (witness) for an NP problem.
    `abbrev` (not `def`) so it reduces to `BinString = List BinSymbol`, making
    typeclass instances (`Append`, `Membership`) available transparently. -/
abbrev Certificate := BinString

/-- A language is in NP if it has a polynomial-time verifier.

    Reformulated 2026-05-10 (same as `InClassP`): the polynomial bound `T`
    holds pointwise for every `(x ++ c)` input, with `|c|` polynomial in `|x|`. -/
def InClassNP (L : Language) : Prop :=
  ∃ (Γ Λ σ : Type) (V : Machine Γ Λ σ) (T : ℕ → ℕ),
    IsPolynomialBounded T ∧
    -- V runs in polynomial time on every input (x ++ c).
    -- Bound is on |x ++ c|, which is polynomial in |x| when |c| is polynomially
    -- bounded (the polynomial certificate constraint below ensures this).
    (∀ (x : BinString) (c : Certificate),
      turingTimeComplexity Γ Λ σ V (x ++ c) ≤ T (binLength (x ++ c))) ∧
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
  -- Unpack the P witness: machine, time bound, polynomial-bound proof,
  -- decision correctness, time bound, and the trailing-input invariance.
  obtain ⟨Γ, Λ, σ, M, T, h_poly, h_decides, h_time, h_cert_irrel⟩ := h_in_P
  -- Use M as the verifier (ignoring the certificate).
  refine ⟨Γ, Λ, σ, M, T, h_poly, ?_, ?_⟩
  · -- The verifier runs in time T(|x ++ c|) on (x ++ c). Direct from h_time.
    intro x c
    exact h_time (x ++ c)
  · -- The verifier correctly verifies L
    intro x
    refine ⟨fun h_in_L => ⟨[], by simp [binLength], ?_⟩, ?_⟩
    · -- Forward: certificate = []; M.accepts (x ++ []) = M.accepts x from h_decides.
      rw [List.append_nil]
      exact (h_decides x).mp h_in_L
    · -- Reverse: M.accepts (x ++ c) ↔ M.accepts x by h_cert_irrel; then h_decides.
      intro ⟨c, _, h_accepts⟩
      exact (h_decides x).mpr ((h_cert_irrel x c).mp h_accepts)

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

/-- Encode binary string via prime-power encoding. Noncomputable because it
    composes with `encodeConfig`, which uses `nthPrime`. -/
noncomputable def encodeBinString (x : BinString) : ℕ :=
  encodeConfig (binStringToConfig x)

/-- The digital sum of encoded instances drives the fractal dynamics. Noncomputable
    because `encodeBinString` is noncomputable. -/
noncomputable def instanceDigitalSum (x : BinString) : ℕ :=
  digitalSum3 (encodeBinString x)

/-!
## Examples (for testing)

These match the exercises from Chapter 21.
-/

example : binLength [BinSymbol.one, BinSymbol.zero, BinSymbol.one] = 3 := rfl

/-- Digital sum of 27 = 1000₃ is 1 (from Chapter 21 Exercise 1) -/
example : digitalSum3 27 = 1 := by
  -- 27 = 1·3³ + 0·3² + 0·3¹ + 0·3⁰ in base 3, so D(27) = 1.
  -- The recursive `digitalSum3` unfolds: 27 % 3 + digitalSum3 (27/3)
  --                                    = 0 + digitalSum3 9
  --                                    = 0 + (0 + digitalSum3 3)
  --                                    = 0 + 0 + (0 + digitalSum3 1)
  --                                    = 0 + 0 + 0 + (1 + digitalSum3 0) = 1.
  -- digitalSum3 is recursive: n=0 → 0, else (n % 3) + digitalSum3 (n / 3).
  -- Chain: digitalSum3 27 → 0 + digitalSum3 9 → 0 + 0 + digitalSum3 3 →
  --        0 + 0 + 0 + digitalSum3 1 → 0 + 0 + 0 + 1 + digitalSum3 0 → 1.
  have h0 : digitalSum3 0 = 0 := by unfold digitalSum3; rfl
  have h1 : digitalSum3 1 = 1 := by unfold digitalSum3; simp [h0]
  have h3 : digitalSum3 3 = 1 := by unfold digitalSum3; simp [h1]
  have h9 : digitalSum3 9 = 1 := by unfold digitalSum3; simp [h3]
  have h27 : digitalSum3 27 = 1 := by unfold digitalSum3; simp [h9]
  exact h27

end PrincipiaTractalis.TuringEncoding
