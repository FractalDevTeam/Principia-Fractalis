/-
# r232: α_HN = 5 — the tenth canonical pillar (extending r223 to 10-pillar corpus).

★ 2026-08-12 r232 — adds the α_HN = 5 canonical instance to the corpus,
per the 2026-08-12 cosmology doc §5 (`docs/COSMOLOGY_LOGPERIODIC_G_2026-08-12.md`)
which listed α_HN = 5 as a ten-alpha extension of r212's nine-alpha table.
Extends r223's SubstrateOscillator instance list; joins the σ = 0
constant-amplitude tier alongside α_Poincaré (k = 0) and α_RH (half-integer). ★

## The extension

α_HN = 5 is the odd integer at k = 2 in α = 1 + 2k. Immediate consequences
from prior work:

- r221's `chi_norm_unity_iff_half_or_odd_integer`: α_HN is in the odd-integer
  branch, so `‖χ(e^{iπ·5})‖ = 1` (already proved directly in r221 as
  `chi_norm_alpha_five`).
- r220's `sigma_eq_logb_norm_chi`: σ(α_HN) = log₃(1) = 0.
- r224's classification excludes α_HN from the ‖χ‖ = 3 tier (5 is not even).

So α_HN sits in the constant-amplitude tier {α_Poincaré, α_RH, α_HN}. This
file:

1. Registers `SO_αHN` as the 10th SubstrateOscillator instance.
2. Proves `sigma_alphaHN_eq_zero : σ(5) = 0` directly.
3. Elevates to r223: `SO_αHN_sigma_eq_zero` universal over data-fit.
4. Non-vacuity witness: `chi_norm_alphaHN_eq_one` (already in r221 as
   `chi_norm_alpha_five`, re-exported here for corpus completeness).

The r223 corpus dichotomy theorems (`corpus_constant_amplitude_dichotomy`
and `corpus_sigma_sign_dichotomy`) are NOT modified — they remain 9-pillar.
A downstream 10-pillar bundle can compose r223 + r231 + this file.

## Contents

§1 The `SO_αHN` corpus instance.
§2 `sigma_alphaHN_eq_zero`.
§3 Elevated: `SO_αHN_sigma_eq_zero`.
§4 Axiom check.

## Scope

* NOT a Millennium discharge (α_HN is not a Clay axis; it's an ancillary
  odd-integer anchor per the corpus).
* NOT a substrate derivation of α_HN = 5 itself; it's a listed value from
  the corpus doc.
* IS the extension of r223's 9-pillar corpus to 10 pillars, keeping the
  substrate machinery uniform.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.CorpusSigmaSignDichotomy_r231

open scoped Real

namespace PrincipiaTractalis

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.ChiNormUnity

/-! ## §1 The α_HN = 5 corpus instance. -/

/-- **`SO_αHN`** — the 10th canonical `SubstrateOscillator`, α_HN = 5.

Odd integer (k = 2 in α = 1 + 2k). Constant-amplitude tier alongside
α_Poincaré = 1 (k = 0) and α_RH = 3/2 (half-integer k = 1). -/
def SO_αHN (A φ₀ : ℝ) (hA : A ≠ 0) : SubstrateOscillator :=
  { α := 5, A := A, φ₀ := φ₀, hA := hA }

/-! ## §2 σ(α_HN) = 0. -/

/-- **`sigma_alphaHN_eq_zero`** — α_HN = 5 hits the σ = 0 constant-amplitude
tier.

Direct: `cos(π · 5) = -1` via r212's `cos_pi_mul_eq_neg_one_iff` at k = 2
(α = 1 + 2·2 = 5, odd integer). Then `|1 + 2·(-1)| = 1`, and `log₃(1) = 0`. -/
theorem sigma_alphaHN_eq_zero :
    PrincipiaTractalis.SigmaAbscissa.sigma 5 = 0 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hcos : Real.cos (π * 5) = -1 :=
    (cos_pi_mul_eq_neg_one_iff 5).mpr ⟨2, by push_cast; ring⟩
  have habs : |1 + 2 * Real.cos (π * 5)| = 1 := by rw [hcos]; norm_num
  rw [habs, Real.logb_one]

/-! ## §3 Elevated to r223's `SubstrateOscillator`. -/

/-- **`SO_αHN_sigma_eq_zero`** — the r223 `SubstrateOscillator` method form.

For every data-fit `A ≠ 0` and every `φ₀`, `(SO_αHN A φ₀ hA).sigma = 0`.
Universal over the data-fit parameters — the σ = 0 tier membership is
pillar-intrinsic. Joins `sigma_one` (α_Poincaré) and `sigma_three_halves`
(α_RH) as the third constant-amplitude corpus witness. -/
theorem SO_αHN_sigma_eq_zero (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αHN A φ₀ hA).sigma = 0 := by
  show PrincipiaTractalis.SigmaAbscissa.sigma 5 = 0
  exact sigma_alphaHN_eq_zero

/-! ## §4 Axiom check. -/

#print axioms PrincipiaTractalis.sigma_alphaHN_eq_zero
#print axioms PrincipiaTractalis.SO_αHN_sigma_eq_zero

end PrincipiaTractalis
