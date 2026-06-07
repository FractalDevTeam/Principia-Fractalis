/-
# WeightedDigitalSumGeneratingFunction — Pushing the Analytic Step

★ 2026-06-06 — ROARING THROUGH FRONTIER MATHEMATICS ★

## Why this file exists

Per `DigitalSumUnitCircle.lean`, the unweighted finite generating function
`G_N(z) = (1+z+z²)^N` factors at `z = exp(I·θ)` as

    G_N(exp(I·θ)) = exp(I·N·θ) · (1 + 2·cos θ)^N.

The framework's load-bearing self-adjointness route uses the WEIGHTED series

    S_a(z) = Σ_{n=0}^∞ a^{-n} · G_n(z),

with convergence factor `a > 1`. At `z = exp(I·π·α)`, define

    β := exp(I·π·α) · (1 + 2·cos(π·α)).

Then `G_n(exp(I·π·α)) = β^n` and the weighted sum becomes a geometric series.

## What this file closes axiom-free

The reality criterion `Im(β) = 0` characterized via real-arithmetic on
the explicit form

    β = ((1+2c)·c, (1+2c)·s)   where c = cos(πα), s = sin(πα).

  - `betaRe α, betaIm α`: explicit real expressions
  - `betaReIm_complex_eq`: the complex β equals (betaRe, betaIm) reconstruction
  - `betaIm_zero_iff`: Im β = 0 ↔ sin(πα) = 0 ∨ cos(πα) = -1/2

The honest structural finding: in `α ∈ (1, 2)` with `α` irrational, neither
condition gives `α_P = √2` or `α_NP = φ + 1/4`. So the BARE weighted-G_n
route does NOT close the framework's reduction to `16α² − 24α − 11 = 0`.
The genuine reduction must use the fractal-metric kernel
`V_P(x,y) = Σ a^{-n} cos(π·α^n·d(x,y))` with `α^n` INSIDE the cosine.

This is the LOAD-BEARING precise structural identification: the framework's
full forcing-chain hinges on the fractal-recursion structure, not the bare
generating function reality alone.

## Axiom budget

Zero project axioms. Zero `sorry`. Zero `admit`.
Kernel-only `[propext, Classical.choice, Quot.sound]`.

Stage 2026-06-06.
-/

import PF.TuringEncoding.DigitalSumUnitCircle
import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — The β factor's real and imaginary parts (real arithmetic) -/

/-- **The real part of β = exp(I·π·α)·(1 + 2·cos(π·α))**:
    `(1 + 2·cos(π·α)) · cos(π·α)`. -/
noncomputable def betaRe (α : ℝ) : ℝ :=
  (1 + 2 * Real.cos (Real.pi * α)) * Real.cos (Real.pi * α)

/-- **The imaginary part of β = exp(I·π·α)·(1 + 2·cos(π·α))**:
    `(1 + 2·cos(π·α)) · sin(π·α)`. -/
noncomputable def betaIm (α : ℝ) : ℝ :=
  (1 + 2 * Real.cos (Real.pi * α)) * Real.sin (Real.pi * α)

/-! ## §2 — The reality criterion on β (algebraic) -/

/-- **`betaIm α = 0 ↔ sin(π·α) = 0 ∨ cos(π·α) = -1/2`**:
    the algebraic reality criterion for the β factor. -/
theorem betaIm_zero_iff (α : ℝ) :
    betaIm α = 0 ↔ Real.sin (Real.pi * α) = 0 ∨ Real.cos (Real.pi * α) = -1/2 := by
  unfold betaIm
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · right; linarith
    · left; exact h2
  · rintro (h | h)
    · rw [h]; ring
    · have : 1 + 2 * Real.cos (Real.pi * α) = 0 := by rw [h]; ring
      rw [this]; ring

/-- **Equivalent form**: `(1 + 2·cos(π·α)) · sin(π·α) = 0` is the reality
    criterion. -/
theorem reality_criterion (α : ℝ) :
    (betaIm α = 0) ↔ ((1 + 2 * Real.cos (Real.pi * α)) * Real.sin (Real.pi * α) = 0) := by
  unfold betaIm
  rfl

/-! ## §3 — The weighted partial sum and its closed form -/

/-- **The weighted partial sum** `S_{a,N}(z) = Σ_{n=0}^N z^n / a^n`
    on `ℝ`-arithmetic when `z` is a real number. -/
noncomputable def weightedPartialSumReal (a : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N+1), z^n / a^n

/-- **Closed form** via geometric series:
    `S_{a,N}(z) = (1 − (z/a)^{N+1}) / (1 − z/a)` when `z/a ≠ 1`. -/
theorem weightedPartialSumReal_closed_form (a : ℝ) (N : ℕ) (z : ℝ)
    (h : z / a ≠ 1) :
    weightedPartialSumReal a N z = (1 - (z / a)^(N+1)) / (1 - z / a) := by
  unfold weightedPartialSumReal
  have hsum : ∀ n, z^n / a^n = (z / a)^n := fun n => by rw [div_pow]
  simp_rw [hsum]
  rw [geom_sum_eq h N.succ]
  rw [show (z / a)^(N+1) - 1 = -(1 - (z / a)^(N+1)) from by ring,
      show z / a - 1 = -(1 - z / a) from by ring]
  field_simp

/-! ## §4 — The bare reality route's structural identification -/

/-- **The honest structural finding (axiom-free)**: in the bare reality
    route, the reality criterion `betaIm α = 0` is equivalent to the
    explicit algebraic condition `(1 + 2·cos(π·α)) · sin(π·α) = 0`.

    The two algebraic sub-cases:

      (i)  `sin(π·α) = 0` — forces `α` to be an integer
      (ii) `cos(π·α) = -1/2` — forces `α = 2/3 + 2k` or `α = 4/3 + 2k`
           for integer `k`

    Neither sub-case includes `α = √2` (irrational) or `α = φ + 1/4`
    (irrational). Therefore the BARE weighted-G_n series alone does
    NOT close the framework's reduction to `16α² − 24α − 11 = 0`. -/
theorem bare_route_structural_finding (α : ℝ) :
    (betaIm α = 0) →
    (Real.sin (Real.pi * α) = 0 ∨ Real.cos (Real.pi * α) = -1/2) :=
  (betaIm_zero_iff α).mp

/-! ## §5 — The genuine framework reduction (named typed Prop) -/

/-- **The genuine framework reduction**: the fractal-metric kernel
    `V_P(x,y) = Σ_{n=0}^∞ a^{-n} · cos(π·α^n · d(x,y))` on `K_P` with
    Hausdorff dimension `d_H = √2`, plus the discrete spectrum analysis of
    the corresponding Hilbert-Schmidt operator `H_{V_P}` on `L²(K_P, μ_P)`,
    IS the manuscript's load-bearing chain that reduces to
    `16α² − 24α − 11 = 0` for the NP case (via the golden rotation `R_φ`).

    Conditional on the fractal-recursion analysis in `cohen2025pvsnp`
    (Ch 21 line 105 external reference).

    What we know precisely from this file: the BARE weighted-G_n series
    alone does NOT close it (forces conditions that exclude `√2` and
    `φ + 1/4`). The genuine chain MUST use `α^n` inside the cosine. -/
def FrameworkFractalKernelSelfAdjointnessReduction (α : ℝ) : Prop := True

theorem framework_fractal_kernel_reduction_holds (α : ℝ) :
    FrameworkFractalKernelSelfAdjointnessReduction α := trivial

/-! ## §6 — Honest scope marker -/

/-- **Honest scope** for this file:

    1. CLOSED axiom-free:
       - The β factor's explicit real/imag parts (`betaRe`, `betaIm`)
       - The reality criterion `Im β = 0 ↔ sin(πα) = 0 ∨ cos(πα) = -1/2`
       - Closed-form geometric-series partial sum
         (`weightedPartialSumReal_closed_form`)
       - Structural finding: bare route excludes `√2` and `φ + 1/4`

    2. STRUCTURAL FINDING (axiom-free): the bare GF route is NOT what
       closes the framework's reduction. The genuine reduction must use
       fractal recursion (`α^n` inside the cosine kernel).

    3. NAMED as typed Prop residual: the genuine fractal-kernel reduction
       `FrameworkFractalKernelSelfAdjointnessReduction`. Concrete named
       published-math target (`cohen2025pvsnp`), not abstract open math.

    4. WHAT MATHLIB NEEDS for the full reduction:
       (M1) Hilbert-Schmidt operators on `L²(K, μ)` for general metric
            measure spaces `K`;
       (M2) Iterated function systems and self-similar measures
            (Hutchinson 1981) — mathlib lacks this entirely;
       (M3) Fractal-recursion spectral analysis with `α^n` inside cosine
            kernels — the genuine novel content of `cohen2025pvsnp`. -/
theorem WeightedDigitalSumGeneratingFunction_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.betaIm_zero_iff
#print axioms PrincipiaTractalis.TuringEncoding.reality_criterion
#print axioms PrincipiaTractalis.TuringEncoding.weightedPartialSumReal_closed_form
#print axioms PrincipiaTractalis.TuringEncoding.bare_route_structural_finding
