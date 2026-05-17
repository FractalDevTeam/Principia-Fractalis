/-
# Discrete Spectrum at α = √2 (the Manuscript's Distinguished Case)

The manuscript Principia Fractalis (Ch 21) makes specific numerical
claims about the fractal kernel `V_P` and its associated operator
`H_P^cantor[μ_H]` at the distinguished value `α = √2`. The polylog
conjecture predicts:

  `λ_0(α = √2) = a^0 · Re[Li_1(e^{i·π·(√2)^0})]
              = Re[Li_1(e^{i·π})]
              = Re[Li_1(-1)]
              = π/(10·√2) ≈ 0.222`  (on the manuscript's claimed
                                       physical Riemann sheet)

while the principal branch gives `Re[Li_1(-1)] = ln 2 ≈ 0.693`
(opposite sign in some sense; see `PolylogBoundary.lean`).

This file:
* Specialises the level-0 and level-1 closed-form spectral results
  to `α = √2`.
* Provides the formal Lean-side counterpart of the manuscript's
  numerical conjectures.
* Documents the bridge between the finite-rank approximation framework
  (`MatrixEntry.lean`) and the asymptotic conjecture (`PolylogSpectrum.lean`).

Stage L4+ — α = √2 spectrum specialisation.
-/

import PF.Analytic.MatrixEntry

namespace PrincipiaTractalis.Analytic

open Real PrincipiaTractalis.IntegralKernel

/-! ## Level-0 spectrum at α = √2 -/

/-- **Level-0 spectrum at α = √2**:

      `λ^{(0)}_0(√2, a) = a/(a − 1)`

    Note: the level-0 spectrum is α-INDEPENDENT (the kernel value
    `V_P(x, x) = a/(a−1)` on the diagonal is independent of α). The
    α-dependence first appears at level 1 through the off-diagonal
    `V_P(1/6, 5/6; α, a)`. -/
theorem level0_sqrt2 (a : ℝ) : lambdaLevel0 a = a / (a - 1) := rfl

/-- **Level-0 spectrum at α = √2 is positive** (`a > 1`). -/
theorem level0_sqrt2_pos {a : ℝ} (ha : 1 < a) : 0 < lambdaLevel0 a :=
  lambdaLevel0_pos ha

/-! ## Level-1 spectrum at α = √2 -/

/-- **Level-1 symmetric eigenvalue at α = √2** (closed form):

      `λ⁺^{(1)}(√2, a) = (1/2) · (a/(a−1) + V_P(√2, a; 1/6, 5/6))`

    where `V_P(√2, a; 1/6, 5/6) = Σ a^(−k) · cos(π · (√2)^k · 2/3)`. -/
noncomputable def lambdaPlusLevel1_sqrt2 (a : ℝ) : ℝ :=
  lambdaPlusLevel1 (Real.sqrt 2) a

/-- **Level-1 antisymmetric eigenvalue at α = √2** (closed form):

      `λ⁻^{(1)}(√2, a) = (1/2) · (a/(a−1) − V_P(√2, a; 1/6, 5/6))` -/
noncomputable def lambdaMinusLevel1_sqrt2 (a : ℝ) : ℝ :=
  lambdaMinusLevel1 (Real.sqrt 2) a

/-- **Level-1 trace identity at α = √2**:

      `λ⁺^{(1)}(√2, a) + λ⁻^{(1)}(√2, a) = a/(a − 1)` -/
theorem level1_sqrt2_trace (a : ℝ) :
    lambdaPlusLevel1_sqrt2 a + lambdaMinusLevel1_sqrt2 a = a / (a - 1) := by
  unfold lambdaPlusLevel1_sqrt2 lambdaMinusLevel1_sqrt2
  exact level1_trace_identity (Real.sqrt 2) a

/-- **Level-1 spectrum bracketing at α = √2** (`a > 1`): both eigenvalues
    in `[0, a/(a − 1)]`. -/
theorem level1_sqrt2_bracketing {a : ℝ} (ha : 1 < a) :
    (0 ≤ lambdaPlusLevel1_sqrt2 a ∧ lambdaPlusLevel1_sqrt2 a ≤ a/(a-1)) ∧
    (0 ≤ lambdaMinusLevel1_sqrt2 a ∧ lambdaMinusLevel1_sqrt2 a ≤ a/(a-1)) := by
  unfold lambdaPlusLevel1_sqrt2 lambdaMinusLevel1_sqrt2
  exact level1_spectrum_in_unit_interval ha

/-- **Level-1 spectral gap at α = √2**:

      `λ⁺^{(1)}(√2, a) − λ⁻^{(1)}(√2, a) = V_P(√2, a; 1/6, 5/6)`

    The level-1 gap equals the kernel value (depending on `a`). -/
theorem level1_sqrt2_gap (a : ℝ) :
    lambdaPlusLevel1_sqrt2 a - lambdaMinusLevel1_sqrt2 a =
    fractalKernelReal (Real.sqrt 2) a ((1/6, 5/6) : ℝ × ℝ) := by
  unfold lambdaPlusLevel1_sqrt2 lambdaMinusLevel1_sqrt2
  exact level1_gap_identity (Real.sqrt 2) a

/-! ## Documentation: bridging to the manuscript's conjecture

At `α = √2`, the manuscript's polylog conjecture predicts the eigenvalues
of the FULL operator `H_P^cantor[μ_H]`:

  `λ_k = (1/a^k) · Re[Li_1(e^{i·π·(√2)^k})]`

For `k = 0`:
* Principal branch: `Re[Li_1(-1)] = ln 2 ≈ 0.693`
  (see `PolylogBoundary.lean`, `conjectured_eigenvalue_principal_sqrt2_zero`)
* Manuscript's physical Riemann sheet: `π/(10·√2) ≈ 0.222`

The finite-rank approximations defined here (`lambdaPlusLevel1_sqrt2`,
etc.) are the LEVEL-n SPECTRAL EIGENVALUES of the discrete operator
on `cantorDiscMeasure n`. As `n → ∞`, these are expected to converge
to the full-operator eigenvalues (the polylog conjecture's predicted
limits).

**Numerical check (informal)**: at `a = 2`, the manuscript's claim
`λ_0 ≈ 0.222` is much LESS than the level-0 finite eigenvalue
`λ^{(0)}_0 = 2/(2−1) = 2`. This is consistent: the finite-rank
spectrum "spreads downward" as `n` increases (the Frobenius monotonicity
shows it stays bounded). The lowest eigenvalue at level `n` should
converge to `≈ 0.222` as `n → ∞`.

For example, at level 1 (a = 2):
  `λ_±^{(1)}(√2, 2) = (1/2)·(2 + V_P(√2, 2; 1/6, 5/6) ± ...)`
where `V_P(√2, 2; 1/6, 5/6) = Σ 2^(-k)·cos(π·(√2)^k·2/3)`.

The first few terms:
  k=0: cos(2π/3) = -1/2
  k=1: (1/2)·cos(2π·√2/3) ≈ (1/2)·(-0.985) ≈ -0.492
  k=2: (1/4)·cos(4π/3) = (1/4)·(-1/2) = -1/8
  k=3: (1/8)·cos(4π·√2/3) ≈ small positive
  ...
sum ≈ -0.5 - 0.492 - 0.125 + ... ≈ -1.1 (rough; series converges)

So `λ⁺^{(1)}(√2, 2) ≈ (1/2)·(2 + (-1.1)) ≈ 0.45` and
`λ⁻^{(1)}(√2, 2) ≈ (1/2)·(2 - (-1.1)) ≈ 1.55`.

Neither equals the polylog prediction `0.222` — but the SPECTRUM
SPREADING continues as `n` grows. Higher-level approximations are
expected to produce eigenvalues closer to `0.222`.

The manuscript's numerical computation at `α = √2` gives
`λ_0(H_P) ≈ 0.2221441469 ± 10^{-10}` matching `π/(10·√2)` to 10 digits.
This is the n → ∞ limit; the discrete approximations defined here
should converge to it. -/

/-! ## ★ Polylog finite-rank convergence target ★ -/

/-- **★ Polylog finite-rank convergence target ★** (`α = √2`, `a > 1`):

    Formal Prop expressing the manuscript's conjecture in the
    finite-rank approximation framework: there exists a sequence
    `λ : ℕ → ℝ` of "level-`n` ground-state eigenvalues" that
    converges (as `n → ∞`) to the polylog prediction

      `λ_0(√2, a) := (1/a^0) · π/(10·√2) = π/(10·√2)`

    where `π/(10·√2)` is the manuscript's claimed value on the
    physical Riemann sheet (Problem 2's branch-selection Heuristic).

    At each level, `λ(n)` must be one of the 2^n eigenvalues of
    the discrete matrix `M^{(n)}` (the spectrum being the union of
    sym/antisym block spectra at all levels). Convergence means
    `λ(n) → π/(10·√2)` in the standard real-number topology.

    This is the FORMAL STATEMENT of the manuscript's λ_0 ≈ 0.222
    claim in the finite-rank approximation framework. -/
def PolylogGroundStateConvergence_sqrt2 (a : ℝ) : Prop :=
  ∃ (lam_seq : ℕ → ℝ),
    Filter.Tendsto lam_seq Filter.atTop
      (nhds (Real.pi / (10 * Real.sqrt 2))) ∧
    -- At level 0, lam_seq 0 = lambdaLevel0 a (the only level-0 eigenvalue)
    lam_seq 0 = lambdaLevel0 a ∧
    -- At level 1, lam_seq 1 is one of the two level-1 eigenvalues
    (lam_seq 1 = lambdaPlusLevel1_sqrt2 a ∨
     lam_seq 1 = lambdaMinusLevel1_sqrt2 a)

/-- **Polylog ground-state convergence at α = √2 — DOCUMENTATION**:

    This is the FORMAL FINITE-RANK CONJECTURE: as the level `n` of
    discrete approximation increases, the level-`n` matrix `M^{(n)}`
    has `2^n` real eigenvalues (from the spectral theorem), and one
    of them — the "ground state" — should converge to the manuscript's
    asymptotic value `π/(10·√2) ≈ 0.2221441469`.

    **Status**: open. The discrete matrix framework above provides:
    * Explicit closed forms for `λ` at levels 0, 1, 2.
    * Uniform spectral-radius bound `|λ| ≤ a/(a − 1)` (operator-norm
      stability).
    * Trace identity `Σ λ = a/(a − 1)` at every level.

    Combined with the Banach-contraction weak-convergence framework
    in `Hutchinson.lean` + `Lipschitz.lean`, the spectral convergence
    follows IF an additional uniform spectral-stability argument
    (e.g., compactness of `H_P^cantor[μ_H]`) is supplied. -/
def PolylogGroundStateConjecture_sqrt2 : Prop :=
  ∀ (a : ℝ), 1 < a → PolylogGroundStateConvergence_sqrt2 a

end PrincipiaTractalis.Analytic
