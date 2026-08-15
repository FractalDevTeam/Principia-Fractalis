/-
# r271: NAMED PUBLISHED-MATHEMATICS BRIDGE FROM r265 REAL LIMIT TO r269 EXTENSION.

★ 2026-08-15 r271 — the LHS bridge for r266's conditional discharge.
r270 landed the RHS on the nose:
    `dirichletEtaExt (1/2 : ℂ) = (1 - √2) · ζ(1/2)`.
The remaining gap is the LHS:
    `((dirichletEtaHalf : ℝ) : ℂ) = dirichletEtaExt (1/2 : ℂ)`
i.e., the classical identity that the conditionally-convergent
alternating Dirichlet series at `s = 1/2` equals the analytic
continuation of Dirichlet eta at the same point.

This identity — the equality of the alternating-series limit with
the value of the meromorphic extension — is **classical Dirichlet
1858 mathematics**. Full formalization requires:
- The abscissa of *conditional* convergence for η (0 < re s), which
  mathlib currently only exposes via absolute convergence (1 < re s
  in `Mathlib.NumberTheory.LSeries.Basic`).
- Analytic continuation of η to `0 < re s` at the level of
  `Differentiable ℂ` / `AnalyticAt`.
- The identity theorem for holomorphic functions comparing η's
  continuation to `(1 - 2^{1-s}) · ζ(s)`.
- Abel's theorem (present in mathlib as
  `Real.tendsto_tsum_powerSeries_nhdsWithin_lt`) connecting the
  conditionally-convergent series value to the continuation value.

Each of these ingredients is standard mathematics. Their composition
is a substantive infrastructure landing that belongs to a future
mathlib PR, not to this substrate-level Route B brick.

Following the corpus pattern for
`Hardy1914_published_theorem_substrate_citation` and
`Mayer1991_Cohen2025_substrate_HP_program_citation` — well-known
published mathematics named as an explicit `Prop` residual and
carried as an input to the top-level closure — r271 introduces
`Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf` as the named
substrate-level bridge.

## What r271 adds

- `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf : Prop`
  The named published-mathematics Prop asserting
    `((dirichletEtaHalf : ℝ) : ℂ) = dirichletEtaExt (1/2 : ℂ)`.
  Not proved in Lean — carried as a named residual.

- `dirichletEtaHalf_matches_one_minus_sqrt_two_mul_zeta_half`:
  GIVEN the r271 Prop, the r266-required identity
    `((dirichletEtaHalf : ℝ) : ℂ) = (1 - √2) · ζ(1/2 : ℂ)`
  follows by composition with r270's `dirichletEtaExt_half_eq`.

## Route B substrate value

r271 exposes the LAST published-mathematics gap on the Dirichlet-eta
path to closing r266's conditional. r272 next uses this composed
identity to inhabit `zeta_half_re_neg_from_eta_zeta_identity` and,
in composition with a certified positive Xi witness at some `b > 0`,
close Route B fact (a) modulo the two named residuals:
- `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf` (this brick)
- A concrete `Xi b > 0` witness (independent bricks r257-r263)

## Scope

* NOT novel — the identity is Dirichlet 1858 / Hardy 1914 era.
* NOT a Millennium discharge.
* IS the named published-mathematics residual on the Dirichlet-eta
  substrate path, matching the corpus pattern for RH's HP-program
  named residuals.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Kernel-only. r271's named Prop is a genuine mathematical statement
(not `Prop := True`) — its inhabitants are published-mathematics
citations, not internal Lean proofs.
-/

import PF.DirichletEtaExtHalf_r270
import PF.DirichletEtaHalfValue_r265

open scoped Real

namespace PrincipiaTractalis.DirichletEtaHalfBridge

open Complex
open PrincipiaTractalis.DirichletEtaExtension
open PrincipiaTractalis.DirichletEtaExtHalf
open PrincipiaTractalis.DirichletEtaHalfValue

/-! ## §1 The named published-mathematics Prop. -/

/-- **`Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf`** — the
classical identity that the conditionally-convergent alternating
Dirichlet series at `s = 1/2` (r265's `dirichletEtaHalf`) equals the
analytic continuation of Dirichlet eta at the same point (r269's
`dirichletEtaExt (1/2 : ℂ)`).

**Citation:** Classical Dirichlet 1858 mathematics; standard
consequence of Abel's limit theorem applied to the analytic
continuation of η(s) = (1 - 2^{1-s})·ζ(s) into `0 < re s`.
Standard references: Titchmarsh (1951) *The Theory of the Riemann
Zeta-Function* §2.1; Edwards (1974) *Riemann's Zeta Function* Ch.1.

**Status:** Named published-mathematics residual for r272's closure
of r266's conditional. Same corpus pattern as
`Hardy1914_published_theorem_substrate_citation` and
`Mayer1991_Cohen2025_substrate_HP_program_citation` — treated as an
inhabited-in-principle `Prop` awaiting a future mathlib PR that
lands the underlying analytic-continuation infrastructure. -/
def Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf : Prop :=
  ((dirichletEtaHalf : ℝ) : ℂ) = dirichletEtaExt (1/2 : ℂ)

/-! ## §2 Composed identity: r271 Prop + r270 -> r266's RHS on the nose. -/

/-- **`dirichletEtaHalf_matches_one_minus_sqrt_two_mul_zeta_half`** —
under the r271 named Prop, the r266-required identity
    `((dirichletEtaHalf : ℝ) : ℂ) = (1 - √2) · ζ(1/2 : ℂ)`
follows by composition with r270's `dirichletEtaExt_half_eq`. -/
theorem dirichletEtaHalf_matches_one_minus_sqrt_two_mul_zeta_half
    (h : Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf) :
    ((dirichletEtaHalf : ℝ) : ℂ) =
      (1 - ((Real.sqrt 2 : ℝ) : ℂ)) * riemannZeta (1/2 : ℂ) := by
  rw [h, dirichletEtaExt_half_eq]

/-! ## §3 Axiom check. -/

#print axioms
  PrincipiaTractalis.DirichletEtaHalfBridge.dirichletEtaHalf_matches_one_minus_sqrt_two_mul_zeta_half

end PrincipiaTractalis.DirichletEtaHalfBridge
