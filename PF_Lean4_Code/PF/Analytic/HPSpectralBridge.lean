/-
# HP Spectral Bridge: The `λ_0(H_P) = π/(10·α_P) = π/(10·√2)` Existential

## What this file delivers

The "Input #5" target of the Principia Fractalis axiom-retirement programme
is the spectral-bridge existential

```
∃ lambdaHP : ℝ, lambdaHP = π/(10 · alpha_of_class ClassP)
              ∧ lambdaHP = π/(10 · Real.sqrt 2)
```

stating that there is a real number that *simultaneously* (a) equals the
manuscript's eigenvalue formula `π/(10·α_P)` for the H_P ground state and
(b) equals the polylog evaluation `π/(10·√2)` (BookEigenvalueIdentity).

This file proves the existential as a Lean theorem from the existing
derived equality `alpha_at_ClassP_eq_sqrt2 : alpha_of_class ClassP =
Real.sqrt 2`, and then unfolds the dependency structure to isolate the
**minimal** hypothesis that would suffice to derive it without the
`alpha_class_polylog_eigenvalue_conjecture` axiom.

## Why this is the right granularity

The conditional theorem already present in `SpectralParameterBridge.lean`
goes the *other way*: it takes the existential as a hypothesis and uses
it to *derive* the axiom's algebraic content (α² = 2 ∧ 0 < α). That
direction does not retire the axiom because the existential itself
ultimately requires knowing `α_P = √2`.

This file complements `SpectralParameterBridge.lean` by:

1. **Lifting** `alpha_at_ClassP_eq_sqrt2` to the existential statement,
   so the existential is now a named theorem rather than a hypothesis.
2. Proving the **equivalence** between the existential and the bare
   identity `alpha_of_class ClassP = Real.sqrt 2` (under positivity).
3. Connecting the existential to `lambda_0_P` from `SpectralGap.lean`
   (i.e., `lambda_0_P = π/(10·√2)` definitionally).
4. **Sharpening** the operator-theoretic gap: the *only* remaining
   non-trivial obstruction to deriving the spectral bridge axiom-free
   is to derive `alpha_of_class ClassP = √2` from a concrete spectral
   analysis of the integral operator `H_P_at α a` (rather than from
   the manuscript-encoded `alpha_class_polylog_eigenvalue_conjecture`).

## Axiom dependency

The headline `hp_spectral_bridge_existential` theorem depends on the
single project axiom `alpha_class_polylog_eigenvalue_conjecture` (via
`alpha_at_ClassP_eq_sqrt2`). The conditional variants
`hp_spectral_bridge_existential_of_alpha_eq_sqrt2` and
`hp_spectral_bridge_existential_iff_alpha_eq_sqrt2` depend on **zero
project axioms** and isolate the sharp gap.

Stage: Input #5 — HP spectral-bridge existential.
-/

import PF.Analytic.SpectralParameterBridge
import PF.Analytic.SpectralAnalysisFramework
import PF.Analytic.LambdaZeroHPBookBounds
import PF.SpectralGap

namespace PrincipiaTractalis.Analytic

open Real
open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding

/-! ## 1. The headline existential, derived from the manuscript-encoded axiom -/

/-- **Headline theorem**: the spectral-bridge existential is a *theorem*
    (not merely a hypothesis of `SpectralParameterBridge`).

    Witness: `lambdaHP := π / (10 · √2)`.

    Both equalities reduce to `alpha_of_class ClassP = √2`, which is the
    derived theorem `alpha_at_ClassP_eq_sqrt2`. The existential itself
    is therefore as strong as `alpha_class_polylog_eigenvalue_conjecture`
    — no stronger, no weaker. -/
theorem hp_spectral_bridge_existential :
    ∃ lambdaHP : ℝ,
      lambdaHP = Real.pi / (10 * alpha_of_class ClassP) ∧
      lambdaHP = Real.pi / (10 * Real.sqrt 2) := by
  refine ⟨Real.pi / (10 * Real.sqrt 2), ?_, rfl⟩
  rw [alpha_at_ClassP_eq_sqrt2]

/-- **Same headline statement, but with the witness pinned to `lambda_0_P`**
    from `PF/SpectralGap.lean`.

    Recall `lambda_0_P := pi_10 / Real.sqrt 2 = π / (10·√2)`. This phrasing
    makes the bridge to the rest of the codebase explicit: the same
    real number that `SpectralGap.lean` uses as the P-class ground-state
    energy is the witness of the spectral-bridge existential. -/
theorem hp_spectral_bridge_existential_witness_lambda_0_P :
    lambda_0_P = Real.pi / (10 * alpha_of_class ClassP) ∧
    lambda_0_P = Real.pi / (10 * Real.sqrt 2) := by
  refine ⟨?_, ?_⟩
  · rw [alpha_at_ClassP_eq_sqrt2]
    unfold lambda_0_P pi_10
    ring
  · unfold lambda_0_P pi_10
    ring

/-! ## 2. Axiom-free conditional: from `α_P = √2` to the existential -/

/-- **Conditional existential** (axiom-free): given the bare identity
    `α_P = √2`, the spectral-bridge existential holds.

    No reference to `alpha_class_polylog_eigenvalue_conjecture` —
    `α_P = √2` is the only mathematical input. -/
theorem hp_spectral_bridge_existential_of_alpha_eq_sqrt2
    (h : alpha_of_class ClassP = Real.sqrt 2) :
    ∃ lambdaHP : ℝ,
      lambdaHP = Real.pi / (10 * alpha_of_class ClassP) ∧
      lambdaHP = Real.pi / (10 * Real.sqrt 2) := by
  refine ⟨Real.pi / (10 * Real.sqrt 2), ?_, rfl⟩
  rw [h]

/-- **Even weaker conditional**: from any hypothesis that pins
    `π/(10·α_P) = π/(10·√2)`, the existential is immediate by witnessing
    with the shared common value. -/
theorem hp_spectral_bridge_existential_of_eigenvalues_eq
    (h : Real.pi / (10 * alpha_of_class ClassP) =
         Real.pi / (10 * Real.sqrt 2)) :
    ∃ lambdaHP : ℝ,
      lambdaHP = Real.pi / (10 * alpha_of_class ClassP) ∧
      lambdaHP = Real.pi / (10 * Real.sqrt 2) :=
  ⟨Real.pi / (10 * Real.sqrt 2), h.symm, rfl⟩

/-! ## 3. Equivalence: the existential, the eigenvalue equality,
       and the value identity are equivalent (under positivity) -/

/-- **Existential ⇒ `π/(10·α_P) = π/(10·√2)`** (axiom-free).

    Trivial: combine the two conjuncts of the existential witness. -/
theorem eigenvalues_eq_of_hp_spectral_bridge_existential
    (h : ∃ lambdaHP : ℝ,
            lambdaHP = Real.pi / (10 * alpha_of_class ClassP) ∧
            lambdaHP = Real.pi / (10 * Real.sqrt 2)) :
    Real.pi / (10 * alpha_of_class ClassP) =
    Real.pi / (10 * Real.sqrt 2) := by
  obtain ⟨_, h1, h2⟩ := h
  rw [← h1, h2]

/-- **`π/(10·α_P) = π/(10·√2)` ⇒ `α_P = √2`** (axiom-free) under positivity.

    Direct corollary of `alpha_eq_sqrt2_of_eigenvalue_eq` from
    `SpectralParameterBridge.lean`. -/
theorem alpha_P_eq_sqrt2_of_eigenvalues_eq
    (h_pos : 0 < alpha_of_class ClassP)
    (h : Real.pi / (10 * alpha_of_class ClassP) =
         Real.pi / (10 * Real.sqrt 2)) :
    alpha_of_class ClassP = Real.sqrt 2 :=
  alpha_eq_sqrt2_of_eigenvalue_eq h_pos h

/-- **★ Equivalence theorem** (axiom-free, under positivity):

    The spectral-bridge existential is *equivalent* to the bare
    identity `α_P = √2`. This pinpoints the mathematical content
    of the existential: it carries exactly the information
    `alpha_of_class ClassP = Real.sqrt 2`. -/
theorem hp_spectral_bridge_existential_iff_alpha_eq_sqrt2
    (h_pos : 0 < alpha_of_class ClassP) :
    (∃ lambdaHP : ℝ,
        lambdaHP = Real.pi / (10 * alpha_of_class ClassP) ∧
        lambdaHP = Real.pi / (10 * Real.sqrt 2))
    ↔ alpha_of_class ClassP = Real.sqrt 2 := by
  constructor
  · intro h_exist
    have h_eig : Real.pi / (10 * alpha_of_class ClassP) =
                 Real.pi / (10 * Real.sqrt 2) :=
      eigenvalues_eq_of_hp_spectral_bridge_existential h_exist
    exact alpha_P_eq_sqrt2_of_eigenvalues_eq h_pos h_eig
  · exact hp_spectral_bridge_existential_of_alpha_eq_sqrt2

/-! ## 4. Connection to `lambda_zero_HP_book` (polylog target) -/

/-- **Connection to `lambda_zero_HP_book`**: the spectral-bridge
    witness can equivalently be taken as `lambda_zero_HP_book`
    (which is *definitionally* `π / (10 · √2)`).

    This makes the bridge to the polylog-route framework
    (`EigenvalueIdentity.lean`, `BookEigenvalueIdentity`) explicit. -/
theorem hp_spectral_bridge_existential_witness_lambda_zero_HP_book :
    lambda_zero_HP_book = Real.pi / (10 * alpha_of_class ClassP) ∧
    lambda_zero_HP_book = Real.pi / (10 * Real.sqrt 2) := by
  have h_book : lambda_zero_HP_book = Real.pi / (10 * Real.sqrt 2) := rfl
  refine ⟨?_, h_book⟩
  rw [alpha_at_ClassP_eq_sqrt2]
  exact h_book

/-- **Equivalent existential form using `lambda_zero_HP_book`**. -/
theorem hp_spectral_bridge_existential_via_lambda_zero_HP_book :
    ∃ lambdaHP : ℝ,
      lambdaHP = lambda_zero_HP_book ∧
      lambdaHP = Real.pi / (10 * alpha_of_class ClassP) ∧
      lambdaHP = Real.pi / (10 * Real.sqrt 2) := by
  refine ⟨lambda_zero_HP_book, rfl, ?_, ?_⟩
  · exact hp_spectral_bridge_existential_witness_lambda_zero_HP_book.1
  · exact hp_spectral_bridge_existential_witness_lambda_zero_HP_book.2

/-! ## 5. The HPSpectralFormula form of the bridge -/

/-- **HPSpectralFormula witness**: at `α = alpha_of_class ClassP`, the
    real number `π/(10·√2)` satisfies the manuscript's eigenvalue formula
    `HPSpectralFormula α λ ↔ λ = π/(10·α)`.

    Combines `alpha_at_ClassP_eq_sqrt2` with the definition of
    `HPSpectralFormula`. -/
theorem HPSpectralFormula_alpha_P_pi_div_ten_sqrt2 :
    HPSpectralFormula (alpha_of_class ClassP) (Real.pi / (10 * Real.sqrt 2)) := by
  unfold HPSpectralFormula
  rw [alpha_at_ClassP_eq_sqrt2]

/-- **HPSpectralFormula witness as `lambda_zero_HP_book`**: the polylog
    target value satisfies the manuscript's eigenvalue formula at
    `α = alpha_of_class ClassP`. -/
theorem HPSpectralFormula_alpha_P_lambda_zero_HP_book :
    HPSpectralFormula (alpha_of_class ClassP) lambda_zero_HP_book :=
  HPSpectralFormula_alpha_P_pi_div_ten_sqrt2

/-! ## 6. Sharp identification of the remaining operator-theoretic gap

`hp_spectral_bridge_existential_iff_alpha_eq_sqrt2` shows the spectral-
bridge existential is equivalent to `α_P = √2` (under positivity).
Therefore the *exact* operator-theoretic gap is to derive

  `alpha_of_class ClassP = Real.sqrt 2`

from first principles — i.e., from the spectral analysis of an
explicitly-constructed integral operator `H_P_at α a` (see
`HPGeneralOperator.lean`), rather than via the manuscript-encoded
`alpha_class_polylog_eigenvalue_conjecture`.

### Concrete decomposition of the remaining work

The first-principles derivation factors through three sub-deliverables:

1. **Spectral formula** (deepest analytic content):
   `λ_0(H_P_at α a) = π/(10·α)` for the canonical kernel parameters,
   established from the Fourier-cosine decomposition of `fractalKernel`
   on the Cantor IFS substrate (see `PolylogSpectrum.lean`,
   `MatrixSpectrumLevel2.lean`, `KernelSelfSimilarity.lean` for the
   level-truncated approximations that converge to this limit).

2. **Polylog identification** (mostly mechanized):
   `λ_0(H_P_at √2 a) = π/(10·√2)` via `BookEigenvalueIdentity` and
   the IVT framework in `SStarBridge.lean` plus numerical sign-change
   (`LambdaZeroHPBookBounds.lean` provides the 10-digit bracketing).

3. **Identification of `alpha_of_class ClassP` with the spectral
   parameter `α`**: the structural assignment of the Hilbert-space
   resonance parameter to the abstract complexity class. This is the
   piece encoded by `alpha_of_class` opacity and pinned by the axiom.

Combining (1) and (2) gives `π/(10·α) = π/(10·√2)`, hence `α = √2`
(under positivity). Combining with (3) gives
`alpha_of_class ClassP = √2`, which by
`hp_spectral_bridge_existential_iff_alpha_eq_sqrt2` retires the
spectral-bridge existential.

### Mathlib infrastructure that would close the gap

* **Spectral theorem for compact self-adjoint operators** on `Lp ℂ 2 μ`:
  `mathlib4` has this (`Mathlib.Analysis.InnerProductSpace.Spectrum`).
  Applies because `H_P_at α a` is bounded self-adjoint (see
  `HPGeneralOperator.lean::H_P_at_isSelfAdjoint`).
* **Hilbert–Schmidt compactness**: already established at the kernel
  level (`KernelSelfSimilarity.lean::HilbertSchmidt_HP` shows
  `‖H_P‖_HS ≤ a/(a-1)`), the operator-theoretic upgrade is standard.
* **Fourier-cosine eigenmode identification**: the eigenmodes of the
  fractal-kernel operator on the unit interval correspond to cosine
  functions `cos(n π x)` (see `CosineModeInnerProducts.lean`,
  `FourierCosineDecomposition.lean`). The ground-state mode at
  `α = √2, a = 2` has eigenvalue `π/(10√2)` per the manuscript.
* **Min-max characterisation of the ground-state eigenvalue**:
  `mathlib4`'s `IsROrC.lowestEigenvalue` / `Operator.μ_n` machinery.

With these in place, the proof of
`alpha_of_class ClassP = Real.sqrt 2` becomes a multi-page but
*tractable* operator-theory exercise — no further axiomatic input
required.
-/

/-! ## 7. Axiom-print verification helpers -/

/-- Self-check theorem: `hp_spectral_bridge_existential` depends on
    exactly one project axiom, namely `alpha_class_polylog_eigenvalue_conjecture`.
    (Verify via `#print axioms hp_spectral_bridge_existential`.) -/
theorem hp_spectral_bridge_existential_axiom_check :
    (∃ lambdaHP : ℝ,
        lambdaHP = Real.pi / (10 * alpha_of_class ClassP) ∧
        lambdaHP = Real.pi / (10 * Real.sqrt 2)) :=
  hp_spectral_bridge_existential

/-- Self-check theorem: the conditional form
    `hp_spectral_bridge_existential_of_alpha_eq_sqrt2` depends on **zero**
    project axioms. (Verify via `#print axioms`.) -/
theorem hp_spectral_bridge_existential_conditional_axiom_check
    (h : alpha_of_class ClassP = Real.sqrt 2) :
    ∃ lambdaHP : ℝ,
      lambdaHP = Real.pi / (10 * alpha_of_class ClassP) ∧
      lambdaHP = Real.pi / (10 * Real.sqrt 2) :=
  hp_spectral_bridge_existential_of_alpha_eq_sqrt2 h

end PrincipiaTractalis.Analytic
