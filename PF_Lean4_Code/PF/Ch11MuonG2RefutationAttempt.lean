/-
# Ch 11 Muon g-2 Refutation (2026-10-05)

## Manuscript claim

`Principia_Fractalis_master_folder/chapters/ch11_geometric_unity.tex`,
§"Experimental Predictions and Anomaly Resolution", subsection "Muon Magnetic
Moment Anomaly", states the experimental discrepancy

  `a_μ^exp − a_μ^SM = (2.51 ± 0.59) × 10⁻⁹`

and then supplies the framework's prediction as

  `Δa_μ^RQG = (π/10) · (m_μ² / M_GU²) · ch₂ = (2.47 ± 0.12) × 10⁻⁹`

with the inputs given in the very next line: `M_GU ≈ 10¹⁶ GeV` and
`ch₂ = 0.95`. It concludes: "The RQG prediction agrees with experiment within
1σ, resolving the anomaly."

## The arithmetic

With the chapter's own stated inputs and `m_μ = 0.1057 GeV`:

  `(π/10) · (0.1057² / (10¹⁶)²) · 0.95 = 3.3344 × 10⁻³⁵`

not `2.47 × 10⁻⁹`. The claimed value is larger than the formula's output by a
factor of `7.4 × 10²⁵`, and the formula's output falls short of even the 1σ
LOWER edge of the quoted discrepancy (`1.92 × 10⁻⁹`) by a factor of
`5.8 × 10²⁵`.

## Where the number comes from

The formula is not malformed — it is the standard shape of a new-physics
contribution to a magnetic moment, `Δa ∼ (coupling) · (m_μ/M)²`, and it lands
near the quoted discrepancy for a mediator scale of about **1.161 TeV**:

  `(π/10) · (0.1057² / 1161.4²) · 0.95 = 2.470 × 10⁻⁹`

So the defect is a scale substitution, not a wrong formula. The stated
`M_GU ≈ 10¹⁶` GeV is `8.6 × 10¹²` times larger than the scale the claimed
output requires. A grand-unification-scale mediator suppresses the muon moment
far below any foreseeable measurement; only a TeV-scale one could reach the
quoted number, and the chapter does not posit a TeV-scale mediator here.

## What this file proves (axiom-free)

1. `deltaAMuRQG_GUT_upper_bracket` — at the chapter's stated scale the
   prediction is below `10⁻³⁴`.
   Strategy: the expression is `π · K` with `K` an explicit positive rational;
   bound `π < 3.141593` (`Real.pi_lt_d6`) and close the rational inequality.

2. `deltaAMuRQG_GUT_ne_claimed` — it is therefore not `2.47 × 10⁻⁹`.

3. `deltaAMuRQG_GUT_lt_anomaly_lower_edge` — it does not even reach
   `1.92 × 10⁻⁹`, the 1σ lower edge of the chapter's own quoted discrepancy.
   Hence the stated conclusion "agrees with experiment within 1σ" is false at
   the stated inputs.

4. `deltaAMuRQG_strictAnti` — the prediction is strictly decreasing in the
   mediator scale, so no larger scale can help; the GUT-scale value is an upper
   bound for every scale above it.

5. `deltaAMuRQG_claimed_forces_TeV_scale` — a two-sided bracket showing the
   claimed `2.47 × 10⁻⁹` is attained strictly between `M = 1100` GeV and
   `M = 1200` GeV. With (4) this pins the required scale into the TeV range and
   quantifies the substitution error.

## What survives, and what does not

The SHAPE of the prediction survives: `Δa_μ ∝ (m_μ/M)²` with an `O(1)`
coefficient is a legitimate framework output. What does not survive is the
numerical claim and the conclusion drawn from it. At `M_GU = 10¹⁶` GeV the
framework predicts an unobservably small contribution to `a_μ`, and therefore
does not resolve the discrepancy it quotes.

This is a NEGATIVE result about one claimed anomaly resolution. It is not a
statement about the framework's other content, and it changes no rigor-ledger
label elsewhere.

## Open item for the author, NOT settled here

The experimental status of the muon `g−2` discrepancy itself has moved since
the chapter was written: improved lattice determinations of the hadronic
vacuum-polarisation contribution have been reported to bring the Standard
Model prediction substantially closer to the measurement, which would shrink or
remove the `(2.51 ± 0.59) × 10⁻⁹` figure this subsection takes as its target.
That bears on whether there is an anomaly to resolve at all. It is flagged, not
asserted, and requires the author to check the current value against the
literature — nothing in this file depends on it.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch11Refutation

/-! ## §1 — The chapter's inputs, verbatim -/

/-- Muon mass in GeV, at the precision the chapter's arithmetic uses. -/
noncomputable def m_mu_GeV : ℝ := 1057 / 10000

/-- The grand-unification scale in GeV, as the chapter states it. -/
noncomputable def M_GU_GeV : ℝ := 10 ^ 16

/-- The consciousness threshold the chapter substitutes. -/
noncomputable def ch2_threshold : ℝ := 95 / 100

/-- The chapter's claimed value `2.47 × 10⁻⁹`. -/
noncomputable def claimedDeltaAMu : ℝ := 247 / 10 ^ 11

/-- The 1σ lower edge of the chapter's own quoted discrepancy,
    `(2.51 − 0.59) × 10⁻⁹ = 1.92 × 10⁻⁹`. -/
noncomputable def anomalyLowerEdge : ℝ := 192 / 10 ^ 11

/-- **The chapter's formula**, as a function of the mediator scale `M`:
    `Δa_μ^RQG(M) = (π/10) · (m_μ²/M²) · ch₂`. -/
noncomputable def deltaAMuRQG (M : ℝ) : ℝ :=
  (Real.pi / 10) * (m_mu_GeV ^ 2 / M ^ 2) * ch2_threshold

/-! ## §2 — The prediction at the stated GUT scale -/

/-- **(1)** At `M_GU = 10¹⁶` GeV the prediction is below `10⁻³⁴`. -/
theorem deltaAMuRQG_GUT_upper_bracket :
    deltaAMuRQG M_GU_GeV < (1 / 10 ^ 34 : ℝ) := by
  unfold deltaAMuRQG M_GU_GeV m_mu_GeV ch2_threshold
  have hpi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hpos : (0 : ℝ) ≤ (1057 / 10000 : ℝ) ^ 2 / ((10 : ℝ) ^ 16) ^ 2 := by
    positivity
  have step :
      Real.pi / 10 * ((1057 / 10000 : ℝ) ^ 2 / ((10 : ℝ) ^ 16) ^ 2) * (95 / 100)
        ≤ (3.141593 : ℝ) / 10
            * ((1057 / 10000 : ℝ) ^ 2 / ((10 : ℝ) ^ 16) ^ 2) * (95 / 100) := by
    have h10 : Real.pi / 10 ≤ (3.141593 : ℝ) / 10 := by linarith
    have := mul_le_mul_of_nonneg_right h10 hpos
    exact mul_le_mul_of_nonneg_right this (by norm_num)
  refine lt_of_le_of_lt step ?_
  norm_num

/-- **(2)** Hence the prediction is not the claimed `2.47 × 10⁻⁹`. -/
theorem deltaAMuRQG_GUT_ne_claimed :
    deltaAMuRQG M_GU_GeV ≠ claimedDeltaAMu := by
  intro h_eq
  have h := deltaAMuRQG_GUT_upper_bracket
  rw [h_eq] at h
  unfold claimedDeltaAMu at h
  norm_num at h

/-- **(3)** The prediction does not reach even the 1σ LOWER edge of the
    chapter's own quoted discrepancy, so "agrees with experiment within 1σ"
    is false at the stated inputs. -/
theorem deltaAMuRQG_GUT_lt_anomaly_lower_edge :
    deltaAMuRQG M_GU_GeV < anomalyLowerEdge := by
  have h := deltaAMuRQG_GUT_upper_bracket
  unfold anomalyLowerEdge
  refine lt_trans h ?_
  norm_num

/-! ## §3 — No larger scale can help -/

/-- **(4)** The prediction is strictly decreasing in the mediator scale. -/
theorem deltaAMuRQG_strictAnti {M₁ M₂ : ℝ} (h₁ : 0 < M₁) (h : M₁ < M₂) :
    deltaAMuRQG M₂ < deltaAMuRQG M₁ := by
  unfold deltaAMuRQG
  have hC : (0 : ℝ) < Real.pi / 10 * m_mu_GeV ^ 2 * ch2_threshold := by
    unfold m_mu_GeV ch2_threshold
    have := Real.pi_pos
    positivity
  have rw1 : ∀ M : ℝ,
      Real.pi / 10 * (m_mu_GeV ^ 2 / M ^ 2) * ch2_threshold
        = (Real.pi / 10 * m_mu_GeV ^ 2 * ch2_threshold) / M ^ 2 := by
    intro M; ring
  rw [rw1, rw1]
  have h1sq : (0 : ℝ) < M₁ ^ 2 := pow_pos h₁ 2
  have hsq : M₁ ^ 2 < M₂ ^ 2 := by nlinarith
  exact div_lt_div_of_pos_left hC h1sq hsq

/-! ## §4 — The claimed number forces a TeV-scale mediator -/

/-- **(5)** The claimed `2.47 × 10⁻⁹` is attained strictly between
    `M = 1100` GeV and `M = 1200` GeV — i.e. at a TeV-scale mediator, not at
    `10¹⁶` GeV. Together with `deltaAMuRQG_strictAnti` this pins the required
    scale and quantifies the substitution error as roughly `10¹³` in `M`. -/
theorem deltaAMuRQG_claimed_forces_TeV_scale :
    claimedDeltaAMu < deltaAMuRQG 1100 ∧ deltaAMuRQG 1200 < claimedDeltaAMu := by
  constructor
  · unfold deltaAMuRQG claimedDeltaAMu m_mu_GeV ch2_threshold
    have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
    have hpos : (0 : ℝ) ≤ (1057 / 10000 : ℝ) ^ 2 / (1100 : ℝ) ^ 2 := by positivity
    have step :
        (3.141592 : ℝ) / 10 * ((1057 / 10000 : ℝ) ^ 2 / (1100 : ℝ) ^ 2) * (95 / 100)
          ≤ Real.pi / 10 * ((1057 / 10000 : ℝ) ^ 2 / (1100 : ℝ) ^ 2) * (95 / 100) := by
      have h10 : (3.141592 : ℝ) / 10 ≤ Real.pi / 10 := by linarith
      have := mul_le_mul_of_nonneg_right h10 hpos
      exact mul_le_mul_of_nonneg_right this (by norm_num)
    refine lt_of_lt_of_le ?_ step
    norm_num
  · unfold deltaAMuRQG claimedDeltaAMu m_mu_GeV ch2_threshold
    have hpi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
    have hpos : (0 : ℝ) ≤ (1057 / 10000 : ℝ) ^ 2 / (1200 : ℝ) ^ 2 := by positivity
    have step :
        Real.pi / 10 * ((1057 / 10000 : ℝ) ^ 2 / (1200 : ℝ) ^ 2) * (95 / 100)
          ≤ (3.141593 : ℝ) / 10
              * ((1057 / 10000 : ℝ) ^ 2 / (1200 : ℝ) ^ 2) * (95 / 100) := by
      have h10 : Real.pi / 10 ≤ (3.141593 : ℝ) / 10 := by linarith
      have := mul_le_mul_of_nonneg_right h10 hpos
      exact mul_le_mul_of_nonneg_right this (by norm_num)
    refine lt_of_le_of_lt step ?_
    norm_num

/-! ## §5 — Capstone -/

/-- **★ Ch 11 muon `g−2` numerical refutation capstone ★**

    Bundles the four load-bearing facts: at the chapter's stated inputs the
    prediction is below `10⁻³⁴`; it is not the claimed `2.47 × 10⁻⁹`; it does
    not reach the 1σ lower edge of the quoted discrepancy; and the claimed
    value is attained only at a TeV-scale mediator, between `1100` and `1200`
    GeV. -/
theorem Ch11MuonG2Refutation_capstone :
    deltaAMuRQG M_GU_GeV < (1 / 10 ^ 34 : ℝ) ∧
    deltaAMuRQG M_GU_GeV ≠ claimedDeltaAMu ∧
    deltaAMuRQG M_GU_GeV < anomalyLowerEdge ∧
    (claimedDeltaAMu < deltaAMuRQG 1100 ∧ deltaAMuRQG 1200 < claimedDeltaAMu) :=
  ⟨deltaAMuRQG_GUT_upper_bracket,
   deltaAMuRQG_GUT_ne_claimed,
   deltaAMuRQG_GUT_lt_anomaly_lower_edge,
   deltaAMuRQG_claimed_forces_TeV_scale⟩

/-! ## §6 — Non-vacuity witnesses -/

/-- Non-vacuity for `deltaAMuRQG_strictAnti`: its hypotheses are satisfiable,
    witnessed by the very scales the bracket uses. -/
theorem deltaAMuRQG_strictAnti_witness :
    deltaAMuRQG 1200 < deltaAMuRQG 1100 :=
  deltaAMuRQG_strictAnti (by norm_num) (by norm_num)

/-- Non-vacuity: the formula is strictly positive at a physical scale, so the
    bounds above are not bounds on zero. -/
theorem deltaAMuRQG_pos (M : ℝ) (hM : M ≠ 0) : 0 < deltaAMuRQG M := by
  unfold deltaAMuRQG m_mu_GeV ch2_threshold
  have := Real.pi_pos
  have : (0:ℝ) < M ^ 2 := by positivity
  positivity

end PrincipiaTractalis.Ch11Refutation

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch11Refutation.deltaAMuRQG_GUT_upper_bracket
#print axioms PrincipiaTractalis.Ch11Refutation.deltaAMuRQG_GUT_ne_claimed
#print axioms PrincipiaTractalis.Ch11Refutation.deltaAMuRQG_GUT_lt_anomaly_lower_edge
#print axioms PrincipiaTractalis.Ch11Refutation.deltaAMuRQG_strictAnti
#print axioms PrincipiaTractalis.Ch11Refutation.deltaAMuRQG_claimed_forces_TeV_scale
#print axioms PrincipiaTractalis.Ch11Refutation.Ch11MuonG2Refutation_capstone
