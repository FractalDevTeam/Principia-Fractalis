/-
  PF/CollatzFractal.lean

  Collatz map in the Principia Fractalis framework:
  - Classical Collatz operator T : ℕ → ℕ
  - Binary digit-sum D₂(n)
  - Fractal norm ‖n‖_α = n / α^(D₂(n)), α = φ
  - Collatz Conjecture as a proposition
  - Fractal monotonicity (PF Lyapunov-style) as a proposition
  - Equivalence "Collatz ↔ Fractal monotonicity" as a formal statement (not proved)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.List.Basic

namespace PF
namespace Collatz

open scoped Real

/-- Golden ratio α = φ = (1 + √5) / 2. -/
noncomputable def goldenRatio : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- Classical Collatz operator on ℕ. -/
def collatz (n : ℕ) : ℕ :=
  if h : n % 2 = 0 then
    n / 2
  else
    3 * n + 1

/--
Binary digit-sum D₂(n): sum of base-2 digits of n.

Counts the number of 1-bits in the binary representation.
For example:
- D₂(0) = 0
- D₂(5) = D₂(101₂) = 2
- D₂(7) = D₂(111₂) = 3

Recursive definition: count 1s by repeatedly checking (n % 2) and dividing by 2.
-/
def D2 : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + D2 ((n + 1) / 2)

/--
Fractal-spectral norm on ℕ induced by the PF framework:
‖n‖_α = n / α^(D₂(n)), with α = φ.

We work in ℝ by coercing `n : ℕ` to `(n : ℝ)`.
-/
noncomputable def collatzNorm (n : ℕ) : ℝ :=
  let α := goldenRatio
  (n : ℝ) / α ^ (D2 n)

/-! ## Classical Collatz Conjecture as a `Prop` -/

/--
The usual Collatz Conjecture:
for every n, some iterate hits 1.
-/
def CollatzConjecture : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, (Nat.iterate collatz k n) = 1

/-! ## PF Fractal Monotonicity as a `Prop` -/

/--
Global fractal monotonicity (strong Lyapunov form):

The fractal norm `collatzNorm` strictly decreases along
every Collatz step, for all n ≥ N₀, for some finite threshold N₀.

This encodes the PF idea that there is a global contraction
in the α–weighted digit-sum metric outside a finite set.
-/
def FractalMonotoneAbove (N0 : ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄, n ≥ N0 → collatzNorm (collatz n) < collatzNorm n

/--
Finite verification region for Collatz (classical):

All n < N₀ eventually reach 1.
-/
def CollatzFiniteRegion (N0 : ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄, n < N0 → ∃ k : ℕ, (Nat.iterate collatz k n) = 1

/--
Fractal monotonicity in the PF sense:

There exists a computable threshold N₀ such that
- the fractal norm is strictly decreasing for all n ≥ N₀
- and all n < N₀ are classically verified to reach 1.

This is the PF-level statement that the Collatz dynamics has
a single global depth-1 attractor in the fractal norm.
-/
def FractalMonotonicityPF : Prop :=
  ∃ N0 : ℕ, FractalMonotoneAbove N0 ∧ CollatzFiniteRegion N0

/-! ## Equivalence statement (Collatz ⇔ Fractal monotonicity) -/

/--
PF-level equivalence statement:

The classical Collatz Conjecture holds if and only if
the PF fractal monotonicity condition holds.

This is *not proved here*; it is packaged as a single `Prop`.
You or a future formalization can later attempt to prove:

  theorem collatz_iff_fractalMonotonicity :
    CollatzConjecture ↔ FractalMonotonicityPF := …

For now we just keep the equivalence as a named proposition.
-/
def CollatzEquivalentToFractalMonotone : Prop :=
  CollatzConjecture ↔ FractalMonotonicityPF

/-! ## Optional: even/odd step predicates (for later refinement) -/

/-- Predicate: `n` is an even Collatz step (n % 2 = 0). -/
def EvenStep (n : ℕ) : Prop :=
  n % 2 = 0

/-- Predicate: `n` is an odd Collatz step (n % 2 = 1). -/
def OddStep (n : ℕ) : Prop :=
  n % 2 = 1

/--
PF-style even-step contraction (schematic):

For later work, one can try to prove this from properties of `D2`:

  ∀ n, EvenStep n → collatzNorm (collatz n) < collatzNorm n.

We do *not* assert it as a theorem here; we package it as a `Prop` 
that can be assumed or proved in a separate file.
-/
def EvenStepContractive : Prop :=
  ∀ ⦃n : ℕ⦄, EvenStep n → collatzNorm (collatz n) < collatzNorm n

/--
PF-style odd-step contraction (schematic):

Same idea as `EvenStepContractive`, but restricted to odd inputs.
Again, this is a *statement*, not a proved theorem here.
-/
def OddStepContractive : Prop :=
  ∀ ⦃n : ℕ⦄, OddStep n → collatzNorm (collatz n) < collatzNorm n

/--
Decomposition of full PF fractal monotonicity into
even + odd step contraction, together with a threshold N₀
and a finite verification region.

This lines up with the LaTeX narrative: outside a finite set,
both even and odd steps are contracting in the PF norm.
-/
def FractalMonotonicityDecomposed : Prop :=
  ∃ N0 : ℕ,
    (∀ ⦃n : ℕ⦄, n ≥ N0 ∧ EvenStep n →
      collatzNorm (collatz n) < collatzNorm n) ∧
    (∀ ⦃n : ℕ⦄, n ≥ N0 ∧ OddStep n →
      collatzNorm (collatz n) < collatzNorm n) ∧
    CollatzFiniteRegion N0

end Collatz
end PF
