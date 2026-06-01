/-
# Ch 19 Conj 19.1 Mass-Formula Refutation (Wave 55-Ch19)

## Manuscript claims

`Principia_Fractalis_master_folder_rev2/chapters/ch19_physical_applications.tex`
lines 114-142 contain Conjecture 19.1 ("Masses from Riemann Zeros") with
the boxed closed form

  `m_n² = M_Planck² · exp[ -2π / |ζ'(ρ_n)| ]`

and the explicit numerical "verification" at the first three Riemann zeros:

  ρ_1 ⇒ m_1 ≈ 0.5 MeV  (electron)
  ρ_2 ⇒ m_2 ≈ 105 MeV  (muon)
  ρ_3 ⇒ m_3 ≈ 1.8 GeV  (tau)

The manuscript declares (line 140-142): "remarkably close to the three
charged leptons! This is not a coincidence."

### 80-digit mpmath verification (Wave 55 chapter audit, 2026-05-31)

  |ζ'(ρ_1)|              ≈ 0.79316043
  exp(-2π / 0.79316)     ≈ 3.62 × 10⁻⁴
  M_Planck               ≈ 1.22 × 10¹⁹ GeV
  m_1 = M_Planck·√(...)  ≈ 2.32 × 10¹⁷ GeV
  Manuscript claim       = 0.5 MeV = 5 × 10⁻⁴ GeV
  Ratio predicted/claimed ≈ 4.6 × 10²⁰

So the manuscript verification overshoots the claimed electron mass by
twenty orders of magnitude. The conjecture's literal numerical leg is
arithmetically FALSE.

## What this file proves (axiom-free)

This file follows the *abstract* refutation pattern authorised by the
Wave 55-Ch19 dispatch: rather than formalising `Real.exp`, `Real.log`,
and `ζ'` bounds from scratch — which would require importing significant
analytic-number-theory infrastructure not available in mathlib — we
encode the 80-digit mpmath-verified anchors AS HYPOTHESES to the
refutation theorem. The hypotheses are arithmetic brackets (e.g.
`predicted_m1 > 2 * 10^17`, `claimed_m1 ≤ 10^(-3)`), both verified by
mpmath at 80-digit precision. The pure-Lean content then proves the
ratio `predicted / claimed > 10^19` and derives the contradiction
purely from the brackets.

This keeps the file:

* axiom-free (no `axiom`, no `sorry`),
* numerically faithful to the 80-digit mpmath audit,
* honest about scope (the brackets are HYPOTHESES, conditioned on
  mpmath; the Lean theorem says: GIVEN those brackets, the manuscript
  claim is refuted by twenty orders of magnitude).

Theorems supplied:

1. `ch19_conj_19_1_predicted_m1` — manuscript's symbolic closed form
   for the first-zero mass prediction.
2. `ch19_conj_19_1_claimed_m1_upper` — rational upper bound on
   manuscript's claimed value (0.5 MeV ≤ 10⁻³ GeV).
3. `ch19_conj_19_1_predicted_lower_safe` — rational lower bound on
   predicted m_1 (`2 × 10¹⁷ GeV`), safely below the mpmath value
   `≈ 2.32 × 10¹⁷ GeV`.
4. `ch19_mass_formula_predicted_vs_claimed_off_by_20_orders` — ★ main
   refutation: assuming the mpmath-verified brackets, predicted_m1
   exceeds claimed_m1 by a factor strictly greater than `10¹⁹`.
5. `ch19_mass_formula_predicted_ne_claimed` — direct ≠ corollary.
6. `Ch19MassFormulaRefutation_capstone` — bundles all four.

## Honest scope

This file refutes the SPECIFIC NUMERICAL LEG of Conj 19.1's worked
example (the "remarkably close" claim on lines 140-142 of Ch 19). It
does NOT:

* discharge the Riemann Hypothesis or any Clay problem;
* refute the structural Riemann-zero / fermion-mass correspondence as
  an abstract statement (only the explicit numerical verification);
* refute the conjecture form itself — the manuscript labels it a
  conjecture, so the existential statement "∃ formula matching lepton
  masses" is not touched; only the specific instance with `exp[-2π/
  |ζ'(ρ_n)|]` and the published `0.5 MeV / 105 MeV / 1.8 GeV` outputs.

Recommended action: Ch 19 should add an explicit numerical retraction,
analogous to the v3.3.1 retraction of Conj 19.4 (QCD scale) on lines
374-378.

## Pattern

Identical to Wave 55-Ch11 `Ch11AnomalyCancellationRefutationAttempt.lean`
(commit 8e4a62a): mpmath-verified anchors → axiom-free Lean brackets +
`linarith` / `nlinarith` / `norm_num` strict bracket transitivity.

Stage L7 — Wave 55-Ch19 manuscript refutation.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch19Refutation

/-! ## §1 — Manuscript symbolic closed form for the first-zero mass -/

/-- **Planck mass anchor**, in units of GeV: `M_Planck ≈ 1.22 × 10¹⁹`.

    We use the standard CODATA/PDG value as a rational anchor; the
    exact decimal is `1.220890 × 10¹⁹ GeV`. This is the numerical
    constant the manuscript uses on Ch 19 line 117. -/
noncomputable def M_Planck_GeV : ℝ := 1.22 * 10 ^ (19 : ℕ)

/-- **Manuscript Conjecture 19.1 symbolic closed form** for the
    first-zero mass prediction (Ch 19 line 117, boxed equation):

      `m_1² = M_Planck² · exp[ -2π / |ζ'(ρ_1)| ]`
      `m_1  = M_Planck · √( exp[ -2π / |ζ'(ρ_1)| ] )`

    We parametrise by the abstract scalar `expFactor := exp(-2π/|ζ'(ρ_1)|)`
    rather than reconstructing `Real.exp` / `ζ'` formally. The actual
    mpmath-verified value at 80-digit precision is
    `expFactor ≈ 3.62 × 10⁻⁴`, giving
    `m_1 = M_Planck · √(expFactor) ≈ 1.22e19 · 0.01903 ≈ 2.32 × 10¹⁷ GeV`. -/
noncomputable def ch19_conj_19_1_predicted_m1 (expFactor : ℝ) : ℝ :=
  M_Planck_GeV * Real.sqrt expFactor

/-! ## §2 — Manuscript claimed electron mass as a concrete rational -/

/-- **Manuscript-claimed first-zero mass**, in GeV (Ch 19 line 135):
    `m_1 ≈ 0.5 MeV = 5 × 10⁻⁴ GeV`. We use the safe upper bracket
    `10⁻³ GeV = 0.001 GeV ≥ 0.5 MeV` for the refutation. -/
noncomputable def ch19_conj_19_1_claimed_m1_upper : ℝ := 1 / 1000

/-- The claimed-mass upper bracket is strictly positive. -/
theorem ch19_conj_19_1_claimed_m1_upper_pos :
    0 < ch19_conj_19_1_claimed_m1_upper := by
  unfold ch19_conj_19_1_claimed_m1_upper; norm_num

/-! ## §3 — mpmath-verified safe rational lower bracket on predicted_m1 -/

/-- **Safe rational lower bracket on the predicted first-zero mass**.

    The 80-digit mpmath computation gives
    `predicted_m1 ≈ 2.32 × 10¹⁷ GeV`. We use the conservative bracket
    `predicted_m1 > 2 × 10¹⁷ GeV`, comfortably below 2.32 × 10¹⁷,
    leaving ~16% safety margin against any precision drift. -/
noncomputable def ch19_predicted_m1_safe_lower : ℝ := 2 * 10 ^ (17 : ℕ)

/-- The safe lower bracket is strictly positive. -/
theorem ch19_predicted_m1_safe_lower_pos :
    0 < ch19_predicted_m1_safe_lower := by
  unfold ch19_predicted_m1_safe_lower; positivity

/-! ## §4 — ★ Main refutation: predicted exceeds claimed by > 10¹⁹ -/

/-- **★★ Ch 19 Conjecture 19.1 numerical refutation ★★**.

    The manuscript-claimed verification on lines 134-142
    ("`ρ_1 ⇒ m_1 ≈ 0.5 MeV (electron)`")
    is FALSE by twenty orders of magnitude.

    **Hypotheses** (mpmath-verified at 80-digit precision):

    * `h_pred_lo` : `predicted_m1 > 2 × 10¹⁷ GeV` — the conservative
      lower bracket of the actual mpmath value `≈ 2.32 × 10¹⁷ GeV`,
      computed by the Wave 55 chapter-audit subagent from
      `|ζ'(ρ_1)| ≈ 0.79316043` and `exp(-2π/0.79316) ≈ 3.62 × 10⁻⁴`.

    * `h_claim_hi` : `claimed_m1 ≤ 10⁻³ GeV` — the conservative upper
      bracket of the manuscript-published value `0.5 MeV = 5 × 10⁻⁴
      GeV` from Ch 19 line 135.

    **Conclusion**:
    `predicted_m1 > 10¹⁹ · claimed_m1`. I.e. the manuscript's worked
    example overshoots its own claimed output by more than nineteen
    orders of magnitude (mpmath actual: 20.66 orders). -/
theorem ch19_mass_formula_predicted_vs_claimed_off_by_20_orders
    (predicted_m1 claimed_m1 : ℝ)
    (h_pred_lo  : predicted_m1 > 2 * (10 : ℝ) ^ (17 : ℕ))
    (h_claim_hi : claimed_m1  ≤ 1 / 1000) :
    predicted_m1 > (10 : ℝ) ^ (19 : ℕ) * claimed_m1 := by
  -- Step 1: 10¹⁹ · claimed_m1 ≤ 10¹⁹ · (1/1000) = 10¹⁹ / 1000 = 10¹⁶.
  have h_pow_pos : (0 : ℝ) < (10 : ℝ) ^ (19 : ℕ) := by positivity
  have h_pow_nn  : (0 : ℝ) ≤ (10 : ℝ) ^ (19 : ℕ) := le_of_lt h_pow_pos
  have h_rhs_le :
      (10 : ℝ) ^ (19 : ℕ) * claimed_m1
        ≤ (10 : ℝ) ^ (19 : ℕ) * (1 / 1000) :=
    mul_le_mul_of_nonneg_left h_claim_hi h_pow_nn
  -- Step 2: 10¹⁹ · (1/1000) = 10¹⁶ < 2 · 10¹⁷ (since 2·10¹⁷ = 20·10¹⁶).
  have h_step2 :
      (10 : ℝ) ^ (19 : ℕ) * (1 / 1000)
        < 2 * (10 : ℝ) ^ (17 : ℕ) := by
    norm_num
  -- Step 3: chain via the predicted lower bracket.
  calc (10 : ℝ) ^ (19 : ℕ) * claimed_m1
        ≤ (10 : ℝ) ^ (19 : ℕ) * (1 / 1000) := h_rhs_le
      _ < 2 * (10 : ℝ) ^ (17 : ℕ)          := h_step2
      _ < predicted_m1                     := h_pred_lo

/-- **Direct ≠ corollary**: under the same mpmath-verified hypotheses,
    the predicted and claimed values cannot be equal.

    If they were, the 10¹⁹-multiplier strict inequality from
    `ch19_mass_formula_predicted_vs_claimed_off_by_20_orders` would
    give `predicted > 10¹⁹ · predicted`, contradicting positivity. -/
theorem ch19_mass_formula_predicted_ne_claimed
    (predicted_m1 claimed_m1 : ℝ)
    (h_pred_lo  : predicted_m1 > 2 * (10 : ℝ) ^ (17 : ℕ))
    (h_claim_hi : claimed_m1  ≤ 1 / 1000) :
    predicted_m1 ≠ claimed_m1 := by
  intro h_eq
  have h_off :=
    ch19_mass_formula_predicted_vs_claimed_off_by_20_orders
      predicted_m1 claimed_m1 h_pred_lo h_claim_hi
  -- After substitution: predicted > 10¹⁹ · predicted.
  rw [h_eq] at h_off
  -- h_off : claimed_m1 > 10¹⁹ · claimed_m1.
  -- Combined with claimed_m1 ≤ 1/1000 < 10¹⁷ ≤ 10¹⁹ · claimed_m1 needs
  -- a lower bound on claimed_m1; use the predicted lower bracket
  -- transitively, since h_eq turns h_pred_lo into a strict lower bound
  -- on claimed_m1 itself.
  have h_claim_lo : claimed_m1 > 2 * (10 : ℝ) ^ (17 : ℕ) := by
    rw [h_eq] at h_pred_lo; exact h_pred_lo
  -- But h_claim_hi says claimed_m1 ≤ 1/1000, contradicting
  -- claimed_m1 > 2·10¹⁷.
  have h_lhs_huge : (2 : ℝ) * (10 : ℝ) ^ (17 : ℕ) < claimed_m1 := h_claim_lo
  have h_lhs_huge' : (1 / 1000 : ℝ) < claimed_m1 := by
    have h_bound : (1 / 1000 : ℝ) < 2 * (10 : ℝ) ^ (17 : ℕ) := by norm_num
    linarith
  linarith

/-! ## §5 — Capstone -/

/-- **★ Capstone: Ch 19 Conjecture 19.1 numerical leg REFUTED ★**.

    Conjoins:

    1. `predicted_m1 > 10¹⁹ · claimed_m1` under the mpmath-verified
       brackets `predicted > 2·10¹⁷` and `claimed ≤ 10⁻³`.

    2. `predicted_m1 ≠ claimed_m1` under the same brackets.

    The manuscript's published worked example on Ch 19 lines 134-142
    ("`m_1 ≈ 0.5 MeV (electron)`", "`remarkably close`", "`not a
    coincidence`") fails by twenty orders of magnitude. The structural
    Riemann-zero / fermion-mass conjecture as an abstract STATEMENT
    is not touched by this file; only the explicit numerical
    verification is shown false. -/
theorem Ch19MassFormulaRefutation_capstone
    (predicted_m1 claimed_m1 : ℝ)
    (h_pred_lo  : predicted_m1 > 2 * (10 : ℝ) ^ (17 : ℕ))
    (h_claim_hi : claimed_m1  ≤ 1 / 1000) :
    predicted_m1 > (10 : ℝ) ^ (19 : ℕ) * claimed_m1 ∧
    predicted_m1 ≠ claimed_m1 := by
  refine ⟨?_, ?_⟩
  · exact ch19_mass_formula_predicted_vs_claimed_off_by_20_orders
      predicted_m1 claimed_m1 h_pred_lo h_claim_hi
  · exact ch19_mass_formula_predicted_ne_claimed
      predicted_m1 claimed_m1 h_pred_lo h_claim_hi

end PrincipiaTractalis.Ch19Refutation

/-! ## §6 — Axiom check -/

#print axioms PrincipiaTractalis.Ch19Refutation.Ch19MassFormulaRefutation_capstone
