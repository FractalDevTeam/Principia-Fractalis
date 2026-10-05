/-
# Ch 27 Quipu Coherence-Length Refutation (2026-10-05)

## Manuscript claim

`Principia_Fractalis_master_folder/chapters/ch27_dark_energy_expansion.tex`,
§"The Quipu Superstructure and Φ-Resonant Cosmogenesis", displays

  `L_coh = (c/H₀) · (π/10) · σ_c`                        (eq:Lcoh_formula)

with `σ_c = 0.95` and `H₀ = 67.36 km s⁻¹ Mpc⁻¹`, attributes the `π/10` factor
to Ch. 9, and states the substitution "gives `L_coh ≈ 1.38 Gly`, consistent
with the observed Quipu extent within uncertainties." The accompanying figure
legend records the observed extent as `≈ 1.4 Gly`.

## The arithmetic

  `c/H₀ = 299792.458 / 67.36 = 4450.60 Mpc = 14.5159 Gly`
  printed formula:  `14.5159 · (π/10) · 0.95 = 4.3323 Gly`
  without the `π` :  `14.5159 · (1/10)  · 0.95 = 1.3790 Gly`

The printed formula yields `4.33 Gly`, not `1.38`. The claimed `1.38` is
exactly what the same expression gives with the `π` deleted, and the ratio
between the two is `4.3323 / 1.38 = 3.139`, i.e. `π` to three figures.

So the defect is a single spurious factor of `π`, and which side it belongs on
is not a matter of rounding.

## The fork this creates, which the chapter cannot straddle

The chapter asserts two things that are now in conflict:

1. the formula carries `π/10`, "the `π/10` factor documented in Ch. 9" — the
   framework's universal factor; and
2. the result is `1.38 Gly`, "consistent with the observed Quipu extent",
   itself given as `≈ 1.4 Gly` in the figure legend.

Both cannot hold. If (1) is right the prediction is `4.33 Gly`, which exceeds
the observed extent by a factor of `3.1` and the agreement claim fails. If (2)
is right the formula is `(c/H₀)(1/10)σ_c`, the agreement stands, and the
attribution of a `π/10` factor to Ch. 9 is wrong at this equation.

**This file does not choose.** Which horn to take is an authorial decision
about what the Φ-coupled coherence scale actually is, and it has consequences
elsewhere: `π/10` is load-bearing across the framework, so deleting it here
and keeping it in Ch. 9 would need a reason. What is proved below is that the
two assertions are incompatible, and by exactly how much.

## What this file proves (axiom-free)

1. `L_coh_printed_eq_pi_mul_piFree` — the printed quantity is **exactly** `π`
   times the `π`-free quantity. This is the whole diagnosis in one identity:
   the discrepancy is one factor of `π`, neither more nor less. Proof: `ring`.

2. `L_coh_piFree_bracket` — the `π`-free quantity lies in `(1.37, 1.39)`, so it
   reproduces the chapter's `1.38` to the precision printed.

3. `L_coh_printed_gt_four` — the printed quantity exceeds `4 Gly`, hence
   exceeds the observed `≈1.4 Gly` by more than a factor of two. Strategy:
   bound `π > 3.14` (`Real.pi_gt_d6`) against the rational factor.

4. `L_coh_printed_ne_claimed` — hence the printed formula does not yield the
   claimed `1.38 Gly`.

## Scope

Arithmetic only. No rigor-ledger label elsewhere moves. The chapter's
qualitative programme — a Φ-coupled coherence scale of order the observed Quipu
extent — is untouched; what fails is one equation's agreement with one number,
and the repair is to decide which of the two the chapter means.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch27Refutation

/-! ## §1 — The chapter's inputs, verbatim -/

/-- Speed of light, km/s. -/
noncomputable def c_km_s : ℝ := 299792458 / 1000

/-- The Hubble constant the chapter substitutes, km/s/Mpc. -/
noncomputable def H0_ch27 : ℝ := 6736 / 100

/-- The universal resonance threshold the chapter substitutes. -/
noncomputable def sigma_c : ℝ := 95 / 100

/-- Megaparsec to gigalight-year, `1 Mpc = 3.26156 × 10⁻³ Gly`. -/
noncomputable def MpcToGly : ℝ := 326156 / 10 ^ 8

/-- The rational core of the coherence length: `(c/H₀) · (1/10) · σ_c`, in Gly.
    This is the printed expression with the `π` removed. -/
noncomputable def L_coh_piFree : ℝ :=
  (c_km_s / H0_ch27) * MpcToGly * (1 / 10) * sigma_c

/-- The coherence length exactly as the chapter's equation prints it:
    `(c/H₀) · (π/10) · σ_c`, in Gly. -/
noncomputable def L_coh_printed : ℝ :=
  (c_km_s / H0_ch27) * MpcToGly * (Real.pi / 10) * sigma_c

/-- The chapter's claimed value, `1.38 Gly`. -/
noncomputable def claimedL_coh : ℝ := 138 / 100

/-! ## §2 — The whole diagnosis in one identity -/

/-- **(1)** The printed quantity is exactly `π` times the `π`-free quantity.

    This is the entire finding: the gap between the chapter's formula and the
    chapter's number is one factor of `π`, neither more nor less. -/
theorem L_coh_printed_eq_pi_mul_piFree :
    L_coh_printed = Real.pi * L_coh_piFree := by
  unfold L_coh_printed L_coh_piFree
  ring

/-! ## §3 — The π-free quantity reproduces the chapter's number -/

/-- **(2)** The `π`-free quantity lies in `(1.37, 1.39)`, so it reproduces the
    printed `1.38 Gly` to the precision given. -/
theorem L_coh_piFree_bracket :
    (137 / 100 : ℝ) < L_coh_piFree ∧ L_coh_piFree < (139 / 100 : ℝ) := by
  unfold L_coh_piFree c_km_s H0_ch27 MpcToGly sigma_c
  constructor <;> norm_num

/-! ## §4 — The printed quantity misses the observed extent -/

/-- **(3)** The printed quantity exceeds `4 Gly`, hence exceeds the observed
    Quipu extent of about `1.4 Gly` by more than a factor of two. -/
theorem L_coh_printed_gt_four : (4 : ℝ) < L_coh_printed := by
  rw [L_coh_printed_eq_pi_mul_piFree]
  have hpi : (3.14 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hlo := L_coh_piFree_bracket.1
  nlinarith [hpi, hlo]

/-- **(4)** Hence the printed formula does not yield the claimed `1.38 Gly`. -/
theorem L_coh_printed_ne_claimed : L_coh_printed ≠ claimedL_coh := by
  intro h
  have h4 := L_coh_printed_gt_four
  rw [h] at h4
  unfold claimedL_coh at h4
  norm_num at h4

/-! ## §5 — Capstone -/

/-- **★ Ch 27 Quipu coherence-length refutation capstone ★**

    The printed quantity is exactly `π` times the `π`-free one; the `π`-free one
    reproduces the chapter's `1.38 Gly`; the printed one exceeds `4 Gly` and so
    misses the observed extent by more than a factor of two; therefore the
    printed formula does not produce the printed number. -/
theorem Ch27QuipuRefutation_capstone :
    L_coh_printed = Real.pi * L_coh_piFree ∧
    ((137 / 100 : ℝ) < L_coh_piFree ∧ L_coh_piFree < (139 / 100 : ℝ)) ∧
    (4 : ℝ) < L_coh_printed ∧
    L_coh_printed ≠ claimedL_coh :=
  ⟨L_coh_printed_eq_pi_mul_piFree,
   L_coh_piFree_bracket,
   L_coh_printed_gt_four,
   L_coh_printed_ne_claimed⟩

/-! ## §6 — Non-vacuity -/

/-- Non-vacuity: both quantities are strictly positive, so the bounds above are
    not bounds on zero. -/
theorem L_coh_pos : 0 < L_coh_piFree ∧ 0 < L_coh_printed := by
  refine ⟨?_, ?_⟩
  · unfold L_coh_piFree c_km_s H0_ch27 MpcToGly sigma_c; norm_num
  · rw [L_coh_printed_eq_pi_mul_piFree]
    have := Real.pi_pos
    have h := L_coh_piFree_bracket.1
    nlinarith [this, h]

end PrincipiaTractalis.Ch27Refutation

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch27Refutation.L_coh_printed_eq_pi_mul_piFree
#print axioms PrincipiaTractalis.Ch27Refutation.L_coh_piFree_bracket
#print axioms PrincipiaTractalis.Ch27Refutation.L_coh_printed_gt_four
#print axioms PrincipiaTractalis.Ch27Refutation.L_coh_printed_ne_claimed
#print axioms PrincipiaTractalis.Ch27Refutation.Ch27QuipuRefutation_capstone
