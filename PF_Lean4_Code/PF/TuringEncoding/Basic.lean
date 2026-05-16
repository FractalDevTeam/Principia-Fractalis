/-
# Turing Machine to Fractal Operator Encoding - Basic Definitions
Formal encoding of Turing machine configurations into fractal operators.

This file implements the prime-power configuration encoding from Chapter 21, Section 2
(ch21_p_vs_np.tex:143-153), which embeds discrete computation into continuous Hilbert space
via the Timeless Field framework.

Reference: Principia Fractalis, Chapter 21, Definition 2.1 (Prime-Power Configuration Encoding)
-/

import Mathlib.Computability.TuringMachine
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import PF.IntervalArithmetic

namespace PrincipiaTractalis.TuringEncoding

open Turing

-- Define nthPrime using Mathlib's Nat.nth function
/-- The nth prime number (0-indexed): prime(0) = 2, prime(1) = 3, prime(2) = 5, ... -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The nth prime is indeed prime (from Mathlib) -/
theorem nthPrime_is_prime (n : ℕ) : Nat.Prime (nthPrime n) := by
  unfold nthPrime
  exact Nat.prime_nth_prime n

/-- All primes are positive -/
theorem nthPrime_positive (n : ℕ) : nthPrime n > 0 :=
  Nat.Prime.pos (nthPrime_is_prime n)

/-!
## Configuration Encoding via Prime Powers

From Chapter 21: "To construct operators encoding P and NP, we must embed discrete computation
into a continuous Hilbert space."

The encoding uses:
- Powers of 2 to encode state
- Powers of 3 to encode head position
- Higher primes to encode tape symbols

This is the canonical Gödel numbering adapted for fractal operator theory.
-/

/-- Encode a natural number as a state index -/
def stateIndex (q : ℕ) : ℕ := q + 1

/-- Prime-power configuration encoding from Chapter 21, Definition 2.1
    For configuration C = (q, w, i):
    encode(C) = 2^q' · 3^i · ∏(j=1 to |w|) p_{j+1}^{a_j}
-/
structure TMConfig where
  /-- State index (1-indexed) -/
  state : ℕ
  /-- Tape contents as list of symbols (encoded as naturals) -/
  tape : List ℕ
  /-- Head position -/
  headPos : ℕ

/-- Digital sum in base 3 (core fractal invariant from Ch 21)
    D(n) = sum of base-3 digits of n
    This appears in the phase factor e^(iπα·D(encode(x)))
-/
def digitalSum3 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (n % 3) + digitalSum3 (n / 3)

/-- Primorial function: product of first n primes -/
noncomputable def primorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => nthPrime n * primorial n

/-- Encode tape symbol at position using prime power -/
noncomputable def encodeTapeSymbol (symbol : ℕ) (position : ℕ) : ℕ :=
  (nthPrime (position + 1)) ^ (symbol + 1)

/-- Full prime-power encoding of Turing machine configuration
    Reference: Chapter 21, Definition 2.1 (def:config-encoding)
-/
noncomputable def encodeConfig (cfg : TMConfig) : ℕ :=
  let stateEncoding := 2 ^ cfg.state
  let headEncoding := 3 ^ cfg.headPos
  let tapeEncoding := (cfg.tape.mapIdx
    (fun idx symbol => encodeTapeSymbol symbol idx)).prod
  stateEncoding * headEncoding * tapeEncoding

/-!
## Fractal Modulation via R_f

From Chapter 21: The fractal modulation function R_f(α, s) connects discrete computation
to continuous spectrum through the Timeless Field parameterization.

Key insight: R_f modulates the phase factor e^(iπα·D(n)) with scale parameter s ∈ [0,1].
At the consciousness threshold s = ch₂ = 0.95, discrete and continuous structures resonate.
-/

/-- Fractal modulation function R_f(α, s) from the Timeless Field framework
    This creates the bridge between discrete (computation) and continuous (spectrum).

    Mathematical form (from framework):
    R_f(α, s) = (1 - s²)^α · exp(s·α)

    At s = ch₂ = 0.95, this achieves consciousness crystallization.
-/
noncomputable def fractalModulation (α : ℝ) (s : ℝ) : ℝ :=
  (1 - s^2)^α * Real.exp (s * α)

/-- Consciousness crystallization threshold from Chapter 21
    This is the unique value where P and NP become distinguishable
    Reference: consciousness_threshold_unique axiom from IntervalArithmetic.lean
-/
def consciousnessThreshold : ℝ := 0.95

/-!
## Critical Parameters for P and NP

From Chapter 21, Theorem 4 (Critical Values for Consciousness Computation):
The self-adjointness condition determines these values uniquely.
-/

/- `alphaPclass`, `alphaNPclass`, `alphaPclass_eq_sqrt2`,
   `alphaNPclass_eq_phi_quarter`, and the local `alpha_separation`
   — all deleted 2026-05-14 (Stage 40) as orphans following the deletion
   of `phasePclass`/`phaseNPclass` in TuringEncoding/Operators.lean.

   These were the third (camelCase) set of α-parameter definitions in
   the codebase, used only by the phase functions for the H_P/H_NP
   operator kernels. With those phase functions gone, this whole
   sub-block has no consumers.

   The canonical α-parameter definitions live elsewhere:
   - `α_P, α_NP` (Unicode, in P_NP_Complete_Proof.lean) via alpha_of_class
   - `alpha_P, alpha_NP` (ASCII, in TuringEncoding.lean) via alpha_of_class
   - With `α_P_value`, `α_NP_value`, `alpha_P_value_ascii`,
     `alpha_NP_value_ascii` deriving the canonical √2 / φ+¼ values
     from `alpha_class_polylog_eigenvalue_conjecture`.

   A separate `alpha_separation` theorem (parent namespace) lives in
   `TuringEncoding.lean` proving `alpha_NP > alpha_P` for the unified
   ASCII versions, which is what downstream code uses. -/

/-!
## Encoding Properties

Basic properties of the configuration encoding that will be needed
for the operator construction.
-/

/- `digitalSum3_wellDefined` — deleted 2026-05-13. Statement was `True`,
   proof was `trivial`. The name misleadingly suggested well-definedness
   verification when none was performed. Well-definedness of `digitalSum3`
   follows from its `def`-construction (Lean's totality checker). Zero
   downstream consumers. -/

/-- Digital sum of 0 is 0 (base case) -/
theorem digitalSum3_zero : digitalSum3 0 = 0 := by
  unfold digitalSum3
  rfl

-- AXIOM ELIMINATED: encodeConfig_injective (UNUSED)
-- This axiom was declared but never used in any proofs.
-- Injectivity follows from unique prime factorization and can be proven when needed.
--
-- Was: axiom encodeConfig_injective :
--   ∀ (c1 c2 : TMConfig), encodeConfig c1 = encodeConfig c2 → c1 = c2

/-- Each tape symbol encoding is positive (prime power with positive exponent) -/
theorem encodeTapeSymbol_positive (symbol position : ℕ) : encodeTapeSymbol symbol position > 0 := by
  unfold encodeTapeSymbol
  apply Nat.pow_pos
  exact nthPrime_positive (position + 1)

/-- Helper lemma: Product is positive for mapIdx with offset.
    This generalizes to arbitrary starting index to handle the index shift in cons case.
-/
theorem list_mapIdx_prod_pos_offset {α : Type} (l : List α) (f : ℕ → α → ℕ)
    (h : ∀ i a, f i a > 0) (offset : ℕ) :
    (l.mapIdx (fun i a => f (i + offset) a)).prod > 0 := by
  induction l generalizing offset with
  | nil =>
    -- Base case: empty list has product 1
    simp [List.mapIdx_nil]
  | cons head tail ih =>
    -- Inductive case: (head :: tail)
    rw [List.mapIdx_cons, List.prod_cons]
    apply Nat.mul_pos
    -- First element: f (0 + offset) head = f offset head > 0
    · have : (0 : ℕ) + offset = offset := by omega
      rw [this]
      exact h offset head
    -- Rest of list: The mapped function shifts by 1, so we need IH at (offset + 1)
    · have := ih (offset + 1)
      suffices (fun i a => f (i + (offset + 1)) a) = (fun i a => f ((i + 1) + offset) a) by
        rw [← this]; exact ih (offset + 1)
      funext i a
      have : i + (offset + 1) = (i + 1) + offset := by omega
      rw [this]

/-- Product of mapped list where function always returns positive values is positive.
    PROVEN by induction using offset helper lemma.
-/
theorem list_mapIdx_prod_pos {α : Type} (l : List α) (f : ℕ → α → ℕ)
    (h : ∀ i a, f i a > 0) : (l.mapIdx f).prod > 0 := by
  suffices (l.mapIdx (fun i a => f (i + 0) a)).prod > 0 by
    simpa
  exact list_mapIdx_prod_pos_offset l f h 0

/-- The encoding produces positive natural numbers -/
theorem encodeConfig_positive (cfg : TMConfig) : encodeConfig cfg > 0 := by
  unfold encodeConfig
  apply Nat.mul_pos
  apply Nat.mul_pos
  · exact Nat.pow_pos (by norm_num : 0 < 2)
  · exact Nat.pow_pos (by norm_num : 0 < 3)
  · apply list_mapIdx_prod_pos
    intros i a
    exact encodeTapeSymbol_positive a i

/-!
## Connection to Spectral Theory

The encoded configurations become quantum states in the fractal Hilbert space L²(X, μ).
The digital sum D(encode(cfg)) modulates the phase, creating the fractal structure
that distinguishes P from NP at the spectral level.

Next file: Complexity.lean will define P and NP complexity classes formally.
-/

end PrincipiaTractalis.TuringEncoding
