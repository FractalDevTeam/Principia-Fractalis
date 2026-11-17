import PF.Consciousness.RfAtAlphaOneIsNegEta
import PF.DirichletEtaExtUniversalIdentity_2026_11_16
import PF.DirichletEtaExtension_r269

/-!
# R_f(α=1) to Riemann zeta via Dirichlet-eta extension (universal-s)

Closes Rio open-item 4 in `PF/DirichletChainStatus_2026_11_16.lean`.

Composition:
- `fractalResonance_alpha_one_eq_neg_dirichletEta` (BRICK F,
  this directory): `R_f(1, s) = -dirichletEta s` termwise.
- `dirichletEtaExt_eq_dirichletEta` (r269): on `1 < re s`,
  `dirichletEtaExt s = dirichletEta s`.
- `dirichletEtaExt_eq_one_sub_two_cpow_mul_riemannZeta_universal`
  (closed at `bb7ceaca`): `dirichletEtaExt s = (1 - 2^(1-s)) · ζ(s)`
  for all `s ≠ 1`.

Compose on `1 < re s` to get `R_f(1, s) = -(1 - 2^(1-s)) · ζ(s)`.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/

namespace PrincipiaTractalis.Consciousness

open Complex
open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt dirichletEtaExt_eq_dirichletEta)
open PrincipiaTractalis.DirichletEtaExtUniversalIdentity
  (dirichletEtaExt_eq_one_sub_two_cpow_mul_riemannZeta_universal)

/-- **R_f(1, s) = -(1 - 2^(1-s)) · riemannZeta s** on `1 < re s`.

    Composition chain:
    - `R_f(1, s) = -dirichletEta s` (termwise, unconditional)
    - `dirichletEta s = dirichletEtaExt s` on `1 < re s` (r269, inverse)
    - `dirichletEtaExt s = (1 - 2^(1-s)) · riemannZeta s` on `s ≠ 1`
      (universal-s identity, `bb7ceaca`).
    - `1 < re s` implies `s ≠ 1`. -/
theorem fractalResonance_alpha_one_eq_neg_one_sub_two_cpow_mul_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    fractalResonance 1 s = -((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
  have hs_ne : s ≠ 1 := by
    intro h; rw [h] at hs; norm_num at hs
  rw [fractalResonance_alpha_one_eq_neg_dirichletEta s,
      ← dirichletEtaExt_eq_dirichletEta hs,
      dirichletEtaExt_eq_one_sub_two_cpow_mul_riemannZeta_universal hs_ne]

/-- **R_f(1, s) = -(1 - 2^(1-s)) · riemannZeta s** on all `s ≠ 1`,
    reading R_f(1, s) through the analytic extension of the
    Dirichlet-eta series.

    For `s` outside `1 < re s`, the tsum defining `fractalResonance 1 s`
    may diverge (returning 0 in mathlib's convention). The content of
    this theorem is that the \emph{extension} `-dirichletEtaExt s`
    equals `-(1 - 2^(1-s)) · riemannZeta s` throughout `ℂ \ {1}`,
    making `-dirichletEtaExt` the natural analytic continuation of
    R_f(1, ·). -/
theorem neg_dirichletEtaExt_eq_neg_one_sub_two_cpow_mul_riemannZeta
    {s : ℂ} (hs : s ≠ 1) :
    -dirichletEtaExt s = -((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
  rw [dirichletEtaExt_eq_one_sub_two_cpow_mul_riemannZeta_universal hs]

/-! ## §Axiom check. -/

#print axioms fractalResonance_alpha_one_eq_neg_one_sub_two_cpow_mul_riemannZeta
#print axioms neg_dirichletEtaExt_eq_neg_one_sub_two_cpow_mul_riemannZeta

end PrincipiaTractalis.Consciousness
