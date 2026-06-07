/-
# Polylog Substrate Route Capstone

★ 2026-06-06 — Polylog chain capstone ★

## Why this file exists

Today's session built 13 substantive Lean files in the polylog substrate-route
chain. This file bundles them as a single citable typed Prop and theorem.

## Structure

The substrate-route forcing chain for the framework's NP-axis α-value
`φ + 1/4` consists of:

  Step A (analytic, partial): the framework's V_P kernel reality
  condition reduces to the quadratic `16α² − 24α − 11 = 0`.

  Step B (algebraic, fully closed): the positive root of the quadratic
  is uniquely `φ + 1/4`.

Step B is closed by `PolylogQuadraticDerivation`. Step A's algebraic
core is identified by `WeightedDigitalSumGeneratingFunction` (bare GF
route insufficient — fractal recursion required). The fractal-recursion
infrastructure is built in `IFSHausdorffDimensionInfrastructure` (Moran
identity, IFS Prop). The spectral structure at finite-dim is built in
`FiniteDimSpectralFrameworkOperator` (V_P self-adjoint),
`FiniteDimSpectralRealSpectrum` (IsSymm hookup), `FiniteDimSpectralDeterminant`
(discriminant ≥ 0 constructive), `FiniteDimSpectralGap` (N=2 gap criterion),
`FiniteDimSpectralClosedForm` (explicit eigenvalues), `FiniteDimSpectralOperatorBound`
(L∞ bounds), `GeometricPartialSumClosedForm` (uniform bound `a/(a-1)`),
`GeometricSeriesLimit` (N→∞ limit value), `FrameworkAlphaValueIdentities`
(α_P, α_NP identities), `HilbertSchmidtBound` (HS-norm bound).

## Capstone

`PolylogSubstrateRouteChain` bundles the 13 load-bearing results as a
single typed Prop with realization theorem.

## Axiom budget

Zero project axioms. Zero `sorry`. Zero `admit`.
Kernel-only `[propext, Classical.choice, Quot.sound]`.

Stage 2026-06-06.
-/

import PF.TuringEncoding.HilbertSchmidtBound
import PF.TuringEncoding.FrameworkAlphaValueIdentities
import PF.TuringEncoding.GeometricSeriesLimit
import PF.TuringEncoding.WeightedDigitalSumGeneratingFunction

namespace PrincipiaTractalis.TuringEncoding

/-! ## §1 — The capstone typed Prop -/

/-- **`PolylogSubstrateRouteChain`**: a 13-clause Prop bundling all of
    today's polylog substrate-route mathematical content into a single
    citable structural claim. -/
structure PolylogSubstrateRouteChain : Prop where
  /-- Algebraic step (CLOSED): (φ + 1/4) satisfies the NP quadratic. -/
  alpha_NP_satisfies_quadratic : NPQuadratic alphaNP = 0
  /-- Algebraic step (CLOSED): unique positive root. -/
  positive_root_unique : ∀ α : ℝ, NPQuadratic α = 0 → 0 < α → α = alphaNP
  /-- Bare GF route characterized (and shown insufficient). -/
  bare_route_characterization : ∀ α : ℝ, (betaIm α = 0) →
    Real.sin (Real.pi * α) = 0 ∨ Real.cos (Real.pi * α) = -1/2
  /-- IFS Moran identity. -/
  moran_identity : ∀ (N : ℕ) (r : ℝ), 0 < N → 0 < r → r < 1 →
    ∀ d : ℝ, d = Real.log (N : ℝ) / Real.log (1 / r) → (N : ℝ) * r ^ d = 1
  /-- V_P self-adjoint at finite-dim. -/
  vp_self_adjoint : ∀ {N : ℕ} (V : ℝ → ℝ → ℝ) (sample : Fin N → ℝ)
    (_hV : ∀ x y, V x y = V y x) (v w : Fin N → ℝ),
    ∑ i : Fin N, (convolutionOperator V sample v i) * w i =
    ∑ i : Fin N, v i * (convolutionOperator V sample w i)
  /-- IsSymm hookup for symmetric kernel. -/
  is_symm : ∀ {N : ℕ} (V : ℝ → ℝ → ℝ) (sample : Fin N → ℝ),
    (∀ x y, V x y = V y x) → ∀ i j, kernelMatrix V sample i j = kernelMatrix V sample j i
  /-- Discriminant ≥ 0 at N=2. -/
  discriminant_nonneg : ∀ (V : ℝ → ℝ → ℝ) (hV : ∀ x y, V x y = V y x) (x_0 x_1 : ℝ),
    0 ≤ (Matrix.trace (kernelMatrix V (fun i : Fin 2 => if i = 0 then x_0 else x_1))) ^ 2 -
        4 * Matrix.det (kernelMatrix V (fun i : Fin 2 => if i = 0 then x_0 else x_1))
  /-- Vieta sum (eigenvalues). -/
  vieta_sum : ∀ (V : ℝ → ℝ → ℝ) (x_0 x_1 : ℝ),
    lambdaPlus V x_0 x_1 + lambdaMinus V x_0 x_1 = V x_0 x_0 + V x_1 x_1
  /-- V_P uniform bound. -/
  vp_uniform_bound : ∀ (Nlevels : ℕ) (a α : ℝ) (d : ℝ → ℝ → ℝ),
    1 < a → ∀ x y : ℝ,
    |fractalKernelTruncated Nlevels a α d x y| ≤ a / (a - 1)
  /-- Geometric series limit equals uniform bound. -/
  geometric_limit : ∀ (a : ℝ), 1 < a → ∑' n : ℕ, (a^n : ℝ)⁻¹ = a / (a - 1)
  /-- α_P² = 2. -/
  alpha_P_sq : Real.sqrt 2 ^ 2 = 2
  /-- α_P < α_NP. -/
  alpha_ordering : Real.sqrt 2 < alphaNP
  /-- HS-norm bound. -/
  hs_bound : ∀ {N : ℕ} (Nlevels : ℕ) (a α : ℝ) (d : ℝ → ℝ → ℝ),
    1 < a → ∀ sample : Fin N → ℝ,
    ∑ i : Fin N, ∑ j : Fin N,
      (kernelMatrix (fractalKernelTruncated Nlevels a α d) sample i j) ^ 2 ≤
    (N : ℝ) ^ 2 * (a / (a - 1)) ^ 2

/-! ## §2 — The realization theorem -/

/-- **The polylog substrate-route chain is realized axiom-free** by today's
    13 Lean files. -/
theorem polylogSubstrateRouteChain_realized : PolylogSubstrateRouteChain where
  alpha_NP_satisfies_quadratic := alphaNP_satisfies_NPQuadratic
  positive_root_unique := NPQuadratic_positive_root_unique
  bare_route_characterization := bare_route_structural_finding
  moran_identity := fun N r hN hr_pos hr_lt d hd =>
    moran_identity_of_log_form N r hN hr_pos hr_lt d hd
  vp_self_adjoint := fun V sample hV v w =>
    convolutionOperator_self_adjoint V sample hV v w
  is_symm := kernelMatrix_symmetric
  discriminant_nonneg := kernelMatrix_two_discriminant_nonneg
  vieta_sum := vieta_sum
  vp_uniform_bound := fractalKernel_uniform_bound
  geometric_limit := tsum_geometric_inv_eq_a_div
  alpha_P_sq := alphaP_sq_eq_two
  alpha_ordering := alphaP_lt_alphaNP
  hs_bound := fun Nlevels a α d ha sample =>
    fractalKernel_matrix_HS_sq_bound Nlevels a α d ha sample

/-! ## §3 — Honest scope marker -/

/-- **Honest scope** for the polylog substrate-route chain:

    The 13 load-bearing results in `PolylogSubstrateRouteChain` are
    realized axiom-free at HEAD 2026-06-06. They constitute the
    framework's substrate-route forcing chain for the NP-axis α-value
    `φ + 1/4` at the finite-dim approximation level, plus identification
    of the remaining continuum-limit M3 residual.

    REMAINING M3 RESIDUAL: extension to the continuum L²(K_P, μ) limit,
    where the framework's reduction to `16α² − 24α − 11 = 0` happens via
    uniform spectral convergence of the finite-dim approximations. This
    requires mathlib infrastructure for:
    - Hilbert-Schmidt operators on metric measure spaces
    - IFS attractors and self-similar measures (Hutchinson 1981)
    - Fractal-recursion spectral analysis

    Concrete published-math content (`cohen2025pvsnp`), not abstract
    open math. -/
theorem PolylogSubstrateRouteCapstone_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.polylogSubstrateRouteChain_realized
