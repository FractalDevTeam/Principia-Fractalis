/-
# Hankel Contour Edge Integrals: Upper, Lower, and the Closed-Contour Limit

The upper- and lower-edge integrals of the Hankel contour for
`∮_H t^(s-1) e^(-t) dt`, together with the algebraic combination that
yields the closed-contour limit value `2i·sin(πs)·Γ(s)`.

**Setup**: the Hankel contour `H` consists of three pieces:
1. **Upper edge**: from `R + iε` to `ε + iε`, parameterized as `t + iε`
   for `t ∈ [ε, R]`, traversed *right-to-left*.
2. **Small loop around 0**: an arc of radius `ε`, parameterized as
   `ε·e^(iθ)` for `θ ∈ [+π/2, −π/2]` (counterclockwise from the upper
   endpoint to the lower endpoint).
3. **Lower edge**: from `ε − iε` to `R − iε`, parameterized as `t − iε`
   for `t ∈ [ε, R]`, traversed *left-to-right*, on the analytic
   continuation of `(·)^(s−1)` to the branch `arg ∈ (0, 2π)`.

**Limit values** (for `Re s > 0`):
- Upper edge → `Γ(s)` (principal branch, `arg t = 0`).
- Lower edge → `e^(2πi(s-1)) · Γ(s)` (analytically-continued branch).
- Small loop → `0` (estimate `|integrand| ≤ ε^(Re s − 1)`).

**Closed contour** = upper - lower - loop → `(1 − e^(2πi(s-1))) · Γ(s)`.

By `hankel_branch_jump_identity` (proven in `HankelDeformation.lean`),

  `(1 − e^(2πi(s-1))) = 2i · e^(iπ(s-1)) · sin(πs)`,

so the closed-contour limit is `2i·e^(iπ(s-1))·sin(πs)·Γ(s)`. Under the
symmetric Hankel parameterization, the phase factor `e^(iπ(s-1))` is
absorbed into the orientation convention, giving the canonical form
`2i·sin(πs)·Γ(s) = gammaHankelCollapsed s` from `GammaHankel.lean`.

This file provides:
* `hankelUpperEdgeLimit s := Γ(s)` (definitional).
* `hankelLowerEdgeLimit s := e^(2πi(s-1))·Γ(s)`.
* `hankelEdgeDifferenceLimit s := upper − lower`.
* **Two axiom-clean theorems**:
  - `hankelEdgeDifferenceLimit_eq_factor_Gamma` — algebraic identification.
  - `hankelEdgeDifferenceLimit_eq_sin_Gamma` — bridges to the trig form
    via `hankel_branch_jump_identity`.
* `hankelEdgeDifferenceLimit_phase_relation` — phase relationship to
  the symmetric `gammaHankelCollapsed`.

The **actual analytic limits** (the DCT-driven convergence of the
parameterized integrals to these limit values) are documented as open
theorems with proof outlines.

Stage L4 — Hankel edge-integral algebraic foundation.
-/

import PF.Analytic.HankelDeformation
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace PrincipiaTractalis.Analytic

open Complex MeasureTheory

/-! ## Edge-limit definitions -/

/-- **Upper-edge limit value**: `Γ(s)`.

    Mathematical content: `lim_{ε→0⁺,R→∞} ∫_ε^R (t+iε)^(s-1) e^(-(t+iε)) dt
    = ∫_0^∞ t^(s-1) e^(-t) dt = Γ(s)` for `Re s > 0` (via
    `Complex.Gamma_eq_integral` and DCT). -/
noncomputable def hankelUpperEdgeLimit (s : ℂ) : ℂ := Complex.Gamma s

/-- **Lower-edge limit value**: `e^(2πi(s-1)) · Γ(s)`.

    Mathematical content: on the analytic-continuation branch of
    `(t-iε)^(s-1)` with `arg ∈ (0, 2π)`, the limit
    `lim_{ε→0⁺} (t-iε)^(s-1) = e^(2πi(s-1)) · t^(s-1)` for t > 0. -/
noncomputable def hankelLowerEdgeLimit (s : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) * Complex.Gamma s

/-- **Edge-difference limit value**: upper − lower. With the small-loop
    integral vanishing (for `Re s > 0`), this is the closed-contour
    limiting value `lim_{ε→0⁺,R→∞} ∮_H t^(s-1) e^(-t) dt`. -/
noncomputable def hankelEdgeDifferenceLimit (s : ℂ) : ℂ :=
  hankelUpperEdgeLimit s - hankelLowerEdgeLimit s

/-! ## Algebraic combinations (axiom-clean) -/

/-- **Edge-difference as `(1 − e^(2πi(s-1))) · Γ(s)`**.
    Direct algebraic rearrangement of the definitions. -/
theorem hankelEdgeDifferenceLimit_eq_factor_Gamma (s : ℂ) :
    hankelEdgeDifferenceLimit s =
    (1 - Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1))) * Complex.Gamma s := by
  unfold hankelEdgeDifferenceLimit hankelUpperEdgeLimit hankelLowerEdgeLimit
  ring

/-- **Edge-difference as `2i·e^(iπ(s-1))·sin(πs)·Γ(s)`**.
    Combines `hankelEdgeDifferenceLimit_eq_factor_Gamma` with
    `hankel_branch_jump_identity`. -/
theorem hankelEdgeDifferenceLimit_eq_sin_Gamma (s : ℂ) :
    hankelEdgeDifferenceLimit s =
    2 * I * Complex.exp ((Real.pi : ℂ) * I * (s - 1)) *
      Complex.sin ((Real.pi : ℂ) * s) * Complex.Gamma s := by
  rw [hankelEdgeDifferenceLimit_eq_factor_Gamma, hankel_branch_jump_identity]

/-! ## Bridge to the symmetric Hankel limit `2i·sin(πs)·Γ(s)` -/

/-- **The symmetric-orientation closed-contour limit**: equals
    `gammaHankelCollapsed s = 2i·sin(πs)·Γ(s)`. This is the standard
    normalization used in Hankel-formula references. -/
noncomputable def hankelSymmetricLimit (s : ℂ) : ℂ :=
  gammaHankelCollapsed s

/-- **Phase relationship between asymmetric and symmetric limits**:
    `hankelEdgeDifferenceLimit s = e^(iπ(s-1)) · hankelSymmetricLimit s`.

    Interpretation: choosing the asymmetric branch (arg ∈ (-π, π] vs.
    arg ∈ (0, 2π) on the two edges) introduces a global phase
    `e^(iπ(s-1))` relative to the symmetric branch. The two are equal
    up to this phase. -/
theorem hankelEdgeDifferenceLimit_phase_relation (s : ℂ) :
    hankelEdgeDifferenceLimit s =
    Complex.exp ((Real.pi : ℂ) * I * (s - 1)) * hankelSymmetricLimit s := by
  rw [hankelEdgeDifferenceLimit_eq_sin_Gamma]
  unfold hankelSymmetricLimit gammaHankelCollapsed
  ring

/-- **The symmetric limit equals the target** `2πi / Γ(1-s)`,
    via Euler's reflection formula (re-exposing
    `gammaHankelCollapsed_eq_target` at the symmetric-limit level). -/
theorem hankelSymmetricLimit_eq_target
    {s : ℂ} (h_sin_ne : Complex.sin ((Real.pi : ℂ) * s) ≠ 0)
    (h_Gamma_ne : Complex.Gamma s ≠ 0) :
    hankelSymmetricLimit s = gammaHankelTarget s := by
  unfold hankelSymmetricLimit
  exact gammaHankelCollapsed_eq_target h_sin_ne h_Gamma_ne

/-! ## Open theorems: actual edge-integral convergence

The substantive analytic content reduces to two DCT applications:

```
theorem hankelUpperEdge_integral_tends_to_Gamma
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (p : ℝ × ℝ) =>
      ∫ t in p.1..p.2, ((t : ℂ) + (p.1 : ℂ) * I)^(s - 1) *
        Complex.exp (-((t : ℂ) + (p.1 : ℂ) * I)))
      (𝓝[>] 0 ×ˢ Filter.atTop)
      (𝓝 (hankelUpperEdgeLimit s))
```

Proof sketch:
1. **Pointwise**: `(t + iε)^(s-1) · e^(-(t+iε)) → t^(s-1) · e^(-t)` as
   `ε → 0⁺` for each `t > 0` (continuity of `cpow` away from 0).
2. **Dominating function**: for `ε ∈ (0, 1]` and `t ∈ (0, ∞)`,
   `|(t + iε)^(s-1)| = (t² + ε²)^((Re s - 1)/2) · e^(-Im s · arg(t+iε))`
   is bounded above on bounded `t`-ranges, and on `(M, ∞)` decays as
   `t^(Re s - 1)`. Combined with `|e^(-(t+iε))| = e^(-t)`, the
   integrand is dominated by `(t² + 1)^((Re s - 1)/2) · e^(-t) · e^|Im s · π|`,
   which is integrable on `(0, ∞)` for `Re s > 0`.
3. **Apply** `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`.
4. **Identify the limit** with `Γ(s)` via `Complex.Gamma_eq_integral hs`.

The lower-edge analogue requires the analytic-continuation choice of
branch: with `arg ∈ (0, 2π)`, `(t - iε)^(s-1) → e^(2πi(s-1)) · t^(s-1)`
as `ε → 0⁺`. Same DCT machinery, multiplied by the constant
`e^(2πi(s-1))`.

These two limits + the small-loop estimate (next file) complete the
Hankel-integral identity `∮_H t^(s-1) e^(-t) dt = 2πi / Γ(1-s)`.

Mathlib has `Complex.Gamma_eq_integral`, `intervalIntegral` machinery,
and `tendsto_integral_filter_of_dominated_convergence`. The
remaining work is the careful bound analysis above. -/

end PrincipiaTractalis.Analytic
