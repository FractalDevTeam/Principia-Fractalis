/-
# r306: π-cpow POLAR EXTRACTION at ⟨-1/4, -15/2⟩ + downstream Gammaℝ polar form
#      (third strictly-necessary infrastructure step toward Xi_Positive_At_15 discharge)

★ 2026-08-20 r306 — extracts the exact positive magnitude and phase of
the `Complex.cpow` factor `(π : ℂ)^⟨-1/4, -15/2⟩` exposed by r305, and
substitutes into r305's Gammaℝ decomposition to produce the polar
form:

    `Gammaℝ ⟨1/2, 15⟩ = π^(-1/4) · exp(-i · (15/2) · log π) · Γ(1/4 + 15i/2)`

## What r306 delivers

- `pi_cpow_at_neg_15halves_abs :
      Complex.abs ((π : ℂ)^⟨-1/4, -15/2⟩) = Real.pi^(-1/4)` —
  exact positive magnitude via `Complex.abs_cpow_eq_rpow_re_of_pos`.

- `pi_cpow_at_neg_15halves_abs_pos : 0 < Real.pi^(-1/4)` — positivity.

- `pi_cpow_at_neg_15halves_polar :
      (π : ℂ)^⟨-1/4, -15/2⟩
        = ((Real.pi^(-1/4) : ℝ) : ℂ)
            * Complex.exp (((-(15/2) * Real.log Real.pi : ℝ) : ℂ) * Complex.I)` —
  exact polar decomposition.

- `Gammaℝ_at_critical_15_polar_form :
      Gammaℝ ⟨1/2, 15⟩
        = ((Real.pi^(-1/4) : ℝ) : ℂ)
            * Complex.exp (((-(15/2) * Real.log Real.pi : ℝ) : ℂ) * Complex.I)
            * Complex.Gamma ⟨1/4, 15/2⟩` — downstream substitution into
  r305's decomposition.

## Framework-first scope

Not a discharge. Strictly-necessary infrastructure: extracts the
real-positive magnitude of the π-cpow factor, leaving a unit-modulus
complex phase multiplied by the complex Gamma value.

After r306, symbolic factor peeling of Gammaℝ ⟨1/2, 15⟩ is complete.
r307 crosses into certified numerical enclosure of the remaining
`ζ(1/2 + 15i) · phase · Γ(1/4 + 15i/2)` expression, targeting a
kernel-checkable derivation of `0 < Re(product) = Xi 15`.

Book anchors: Ch 20 § 20.4 (RH via Fractal Resonance), Ch 34A § 34A.5.
Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6.
-/

import PF.Analytic.GammaRAtCritical15_r305

namespace PrincipiaTractalis.PiCpowPolarAt15

open Complex
open PrincipiaTractalis.GammaRAtCritical15

/-! ## §1 Magnitude of the π-cpow factor. -/

/-- **`pi_cpow_at_neg_15halves_abs`** — `‖(π : ℂ)^⟨-1/4, -15/2⟩‖ = π^(-1/4)`.

Via `norm_cpow_eq_rpow_re_of_pos` at `x = Real.pi > 0`; the
`.re` of `⟨-1/4, -15/2⟩` is `-1/4`. -/
theorem pi_cpow_at_neg_15halves_abs :
    ‖((Real.pi : ℂ)^((⟨-(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ)))‖
      = Real.pi^(-(1 : ℝ)/4) := by
  rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]

/-- **`pi_cpow_at_neg_15halves_abs_pos`** — `0 < π^(-1/4)`. -/
theorem pi_cpow_at_neg_15halves_abs_pos :
    (0 : ℝ) < Real.pi^(-(1 : ℝ)/4) :=
  Real.rpow_pos_of_pos Real.pi_pos _

/-! ## §2 Polar form of the π-cpow factor. -/

/-- **`pi_cpow_at_neg_15halves_polar`** — exact polar decomposition:

  `(π : ℂ)^⟨-1/4, -15/2⟩
    = ((π^(-1/4) : ℝ) : ℂ) · exp(((-(15/2) · log π : ℝ) : ℂ) · I)`.

Real-positive magnitude `π^(-1/4)` (cast to ℂ) times a unit-modulus
complex phase.

Proof: `Complex.cpow_def_of_ne_zero` → `Complex.ofReal_log` for
positive π → compute `(log π : ℂ) · ⟨-1/4, -15/2⟩` as
`(-log π / 4 : ℝ) + (-(15/2) · log π : ℝ) · I` component-wise → split
via `Complex.exp_add` → convert `exp((-log π/4 : ℝ) : ℂ)` to
`((π^(-1/4) : ℝ) : ℂ)` via `Complex.ofReal_exp` and
`Real.rpow_def_of_pos`. -/
theorem pi_cpow_at_neg_15halves_polar :
    ((Real.pi : ℂ)^((⟨-(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ)))
      = ((Real.pi^(-(1 : ℝ)/4) : ℝ) : ℂ)
          * Complex.exp (((-((15 : ℝ)/2) * Real.log Real.pi : ℝ) : ℂ) * Complex.I) := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi_ne_ℂ : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hpi_pos)
  rw [Complex.cpow_def_of_ne_zero hpi_ne_ℂ, ← Complex.ofReal_log hpi_pos.le]
  have h_prod : (Real.log Real.pi : ℂ) * ((⟨-(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ))
      = ((-Real.log Real.pi / 4 : ℝ) : ℂ)
          + ((-((15 : ℝ)/2) * Real.log Real.pi : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.add_re]
      ring
    · simp [Complex.mul_im, Complex.add_im]
      ring
  rw [h_prod, Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  rw [Real.rpow_def_of_pos hpi_pos]
  ring_nf

/-! ## §3 Downstream: Gammaℝ ⟨1/2, 15⟩ polar form. -/

/-- **★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★ (r306) Gammaℝ ⟨1/2, 15⟩ POLAR FORM ★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★** —
substituting `pi_cpow_at_neg_15halves_polar` into
`Gammaℝ_at_critical_15_decomposition` (r305):

  `Gammaℝ ⟨1/2, 15⟩ = π^(-1/4) · exp(-i · (15/2) · log π) · Γ(1/4 + 15i/2)`

Symbolic factor peeling of `Gammaℝ ⟨1/2, 15⟩` complete. Downstream
Xi(15) work operates on:

  `Xi 15 = π^(-1/4) · Re(ζ(1/2 + 15i) · exp(-i · (15/2) · log π) · Γ(1/4 + 15i/2))`

via r304's `Xi_eq_re_zeta_mul_Gammaℝ` and r305/r306. r307 begins
certified numerical enclosure of the remaining ζ · phase · Γ
expression. -/
theorem Gammaℝ_at_critical_15_polar_form :
    Gammaℝ ⟨(1 : ℝ)/2, (15 : ℝ)⟩
      = ((Real.pi^(-(1 : ℝ)/4) : ℝ) : ℂ)
          * Complex.exp (((-((15 : ℝ)/2) * Real.log Real.pi : ℝ) : ℂ) * Complex.I)
          * Complex.Gamma ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ)) := by
  rw [Gammaℝ_at_critical_15_decomposition, pi_cpow_at_neg_15halves_polar]

/-! ## §4 Axiom checks. -/

#print axioms
  PrincipiaTractalis.PiCpowPolarAt15.pi_cpow_at_neg_15halves_abs
#print axioms
  PrincipiaTractalis.PiCpowPolarAt15.pi_cpow_at_neg_15halves_abs_pos
#print axioms
  PrincipiaTractalis.PiCpowPolarAt15.pi_cpow_at_neg_15halves_polar
#print axioms
  PrincipiaTractalis.PiCpowPolarAt15.Gammaℝ_at_critical_15_polar_form

end PrincipiaTractalis.PiCpowPolarAt15
