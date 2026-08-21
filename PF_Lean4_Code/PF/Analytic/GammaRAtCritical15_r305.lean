/-
# r305: Gammaℝ ⟨1/2, 15⟩ DECOMPOSITION — into π-cpow and Γ mathlib primitives
#      (second strictly-necessary infrastructure step toward the Xi_Positive_At_15 discharge)

★ 2026-08-20 r305 — attacks the `Gammaℝ ⟨1/2, 15⟩` factor exposed by
r304's factorization `Xi 15 = (riemannZeta ⟨1/2, 15⟩ * Gammaℝ ⟨1/2, 15⟩).re`.

By mathlib's `Gammaℝ_def : Gammaℝ s = π^(-s/2) * Γ(s/2)`, at
`s = ⟨1/2, 15⟩` we have `-s/2 = ⟨-1/4, -15/2⟩` and `s/2 = ⟨1/4, 15/2⟩`.
This landing computes those divisions in ℂ and exposes
`Gammaℝ ⟨1/2, 15⟩` in terms of a `Complex.cpow` factor and a
`Complex.Gamma` factor — both mathlib-native primitives ready for
further numerical attack.

## What r305 delivers

- `critical_15_half_eq : ((⟨1/2, 15⟩ : ℂ)) / 2 = (⟨1/4, 15/2⟩ : ℂ)` —
  computes the division `s/2` at `s = ⟨1/2, 15⟩`.

- `neg_critical_15_half_eq : (-(⟨1/2, 15⟩ : ℂ)) / 2 = (⟨-1/4, -15/2⟩ : ℂ)` —
  computes `-s/2` at `s = ⟨1/2, 15⟩`.

- `Gammaℝ_at_critical_15_decomposition : Gammaℝ ⟨1/2, 15⟩ =
    ((Real.pi : ℂ)^(⟨-1/4, -15/2⟩ : ℂ)) * Complex.Gamma ⟨1/4, 15/2⟩` —
  decomposition into π-cpow and Γ factors via `Gammaℝ_def`.

## Framework-first scope

Not a discharge. Strictly-necessary infrastructure that exposes
`Gammaℝ ⟨1/2, 15⟩` in mathlib primitives (`Complex.cpow`,
`Complex.Gamma`). Downstream landings will:
- (r306) extract the real-positive magnitude `π^(-1/4)` from the
  cpow factor via `Complex.cpow` of a positive real base, leaving
  a unit-modulus complex phase.
- Later landings attack the `Complex.Gamma ⟨1/4, 15/2⟩` evaluation.

Book anchors: Ch 20 § 20.4 (RH via Fractal Resonance), Ch 34A § 34A.5.
Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6.
-/

import PF.Analytic.XiExplicitFactorization_r304

namespace PrincipiaTractalis.GammaRAtCritical15

open Complex

/-! ## §1 Division computations in ℂ at the discharge target `s = ⟨1/2, 15⟩`. -/

/-- **`critical_15_half_eq`** — `(⟨1/2, 15⟩ : ℂ) / 2 = (⟨1/4, 15/2⟩ : ℂ)`. -/
theorem critical_15_half_eq :
    ((⟨(1 : ℝ)/2, (15 : ℝ)⟩ : ℂ)) / 2 = ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ)) := by
  apply Complex.ext
  · simp; ring
  · simp

/-- **`neg_critical_15_half_eq`** — `-(⟨1/2, 15⟩ : ℂ) / 2 = ⟨-1/4, -15/2⟩`. -/
theorem neg_critical_15_half_eq :
    (-(⟨(1 : ℝ)/2, (15 : ℝ)⟩ : ℂ)) / 2 = ((⟨-(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ)) := by
  apply Complex.ext
  · simp; ring
  · simp; ring

/-! ## §2 Gammaℝ ⟨1/2, 15⟩ decomposition. -/

/-- **`Gammaℝ_at_critical_15_decomposition`** —
`Gammaℝ ⟨1/2, 15⟩ = ((π : ℂ)^⟨-1/4, -15/2⟩) * Complex.Gamma ⟨1/4, 15/2⟩`.

Direct from `Gammaℝ_def : Gammaℝ s = π^(-s/2) * Γ(s/2)` at
`s = ⟨1/2, 15⟩`, using the division computations above. -/
theorem Gammaℝ_at_critical_15_decomposition :
    Gammaℝ ⟨(1 : ℝ)/2, (15 : ℝ)⟩
      = ((Real.pi : ℂ)^((⟨-(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ)))
          * Complex.Gamma ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ)) := by
  rw [Gammaℝ_def, neg_critical_15_half_eq, critical_15_half_eq]

/-! ## §3 Axiom checks. -/

#print axioms
  PrincipiaTractalis.GammaRAtCritical15.critical_15_half_eq
#print axioms
  PrincipiaTractalis.GammaRAtCritical15.neg_critical_15_half_eq
#print axioms
  PrincipiaTractalis.GammaRAtCritical15.Gammaℝ_at_critical_15_decomposition

end PrincipiaTractalis.GammaRAtCritical15
