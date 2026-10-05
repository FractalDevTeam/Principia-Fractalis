/-
# Ch 07 and Ch 14 Numeric Refutations (2026-10-05)

Two independent arithmetic defects, verified in Python and then proved here.

## Defect A — ch14, the consciousino mass, wrong by eleven orders

`ch14_symmetries_conservation.tex` gives the superpartner mass as

  `m_C̃ ∼ M_SUSY² / M_Planck`

and then states: "For `M_SUSY ∼ 1` TeV, we get `m_C̃ ∼ 10⁻¹⁵` eV — far too light
to have been detected directly."

With the chapter's own inputs and `M_Planck = 1.22 × 10¹⁹` GeV:

  `(10³)² / (1.22 × 10¹⁹) = 8.1967 × 10⁻¹⁴ GeV = 8.1967 × 10⁻⁵ eV`

not `10⁻¹⁵` eV — larger by a factor of `8.20 × 10¹⁰`. The conclusion is robust
to which Planck mass is meant: the reduced value `2.435 × 10¹⁸` GeV gives
`4.11 × 10⁻⁴` eV, off by `4.11 × 10¹¹`. Either way the error is about eleven
orders of magnitude.

**Where `10⁻¹⁵` eV comes from.** The formula returns it at
`M_SUSY ≈ 3.49` MeV, not `1` TeV. Since the mass goes as `M_SUSY²`, a scale
wrong by `2.86 × 10⁵` produces a mass wrong by `8.20 × 10¹⁰` — the two figures
agree exactly, which identifies the defect as a single wrong substituted scale
rather than an error in the see-saw formula.

**What survives, and what weakens.** The formula is the standard
gravity-mediated see-saw shape and is untouched. But the parenthetical
conclusion weakens: at `8 × 10⁻⁵` eV the consciousino is still light, yet it is
eleven orders heavier than claimed and sits in a mass range that laboratory
searches for ultralight bosons do probe. "Far too light to have been detected
directly" is a much weaker statement at `10⁻⁵` eV than at `10⁻¹⁵` eV, and the
dark-matter-candidate remark inherits that.

## Defect B — ch07, an internal inconsistency: 50 % versus 58.5 %

`ch07_constants.tex` states at one site that the qutrit entropy exceeds the
qubit entropy by "**50 %** more entanglement capacity", and fifteen lines later
computes `log 3 / log 2 ≈ 1.585` and calls it a "**58.5 %** increase".

`log 3 / log 2 = 1.584963…`, so the increase is `58.50 %`. The later figure is
right; the earlier one is wrong, and `58.5` is not a defensible rounding of
`50`.

**An integer certificate for the log bound.** No logarithm machinery is needed
to pin the ratio, because

  `2¹⁵⁸ < 3¹⁰⁰ < 2¹⁵⁹`

is a statement about integers, decidable by `norm_num`:

  `2¹⁵⁸ = 365375409332725729550921208179070754913983135744`
  `3¹⁰⁰ = 515377520732011331036461129765621272702107522001`
  `2¹⁵⁹ = 730750818665451459101842416358141509827966271488`

Taking logs and dividing by `100 · log 2 > 0` turns that into
`158/100 < log 3 / log 2 < 159/100`, which is enough to place the increase
strictly between `58 %` and `59 %` — excluding `50 %` and containing the
chapter's own `58.5 %`. (For reference `100 · log₂ 3 = 158.4963`, so the
certificate is comfortable at both ends.)

## Scope

Both defects are arithmetic. No rigor-ledger label elsewhere moves. ch14's
see-saw formula and ch07's radix-economy programme are untouched; what is
corrected is one substituted scale and one inconsistent percentage.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch07Ch14Refutation

/-! ## §1 — ch14: the consciousino mass -/

/-- SUSY-breaking scale the chapter substitutes: `1` TeV, in GeV. -/
noncomputable def M_SUSY_GeV : ℝ := 1000

/-- Planck mass in GeV, `1.22 × 10¹⁹`. -/
noncomputable def M_Planck_GeV : ℝ := 122 / 10 * 10 ^ 18

/-- The chapter's see-saw formula, converted to eV. -/
noncomputable def consciousinoMass_eV : ℝ :=
  M_SUSY_GeV ^ 2 / M_Planck_GeV * 10 ^ 9

/-- The chapter's claimed value, `10⁻¹⁵` eV. -/
noncomputable def claimedMass_eV : ℝ := 1 / 10 ^ 15

/-- **(A1)** The formula's actual output at the chapter's inputs lies strictly
    between `8 × 10⁻⁵` and `9 × 10⁻⁵` eV. -/
theorem consciousinoMass_bracket :
    (8 / 10 ^ 5 : ℝ) < consciousinoMass_eV ∧
    consciousinoMass_eV < (9 / 10 ^ 5 : ℝ) := by
  unfold consciousinoMass_eV M_SUSY_GeV M_Planck_GeV
  constructor <;> norm_num

/-- **(A2)** Hence it is not the claimed `10⁻¹⁵` eV. -/
theorem consciousinoMass_ne_claimed : consciousinoMass_eV ≠ claimedMass_eV := by
  intro h
  have hlo := consciousinoMass_bracket.1
  rw [h] at hlo
  unfold claimedMass_eV at hlo
  norm_num at hlo

/-- **(A3)** The claimed `10⁻¹⁵` eV is attained by the same formula at a
    SUSY-breaking scale strictly between `3` and `4` MeV — not at `1` TeV.

    This identifies the defect as one wrong substituted scale: the see-saw
    formula is fine, the scale put into it is off by five orders of magnitude,
    and squaring that gives the eleven orders in the mass. -/
theorem claimedMass_forces_MeV_scale :
    (3 / 1000 : ℝ) ^ 2 / M_Planck_GeV * 10 ^ 9 < claimedMass_eV ∧
    claimedMass_eV < (4 / 1000 : ℝ) ^ 2 / M_Planck_GeV * 10 ^ 9 := by
  unfold claimedMass_eV M_Planck_GeV
  constructor <;> norm_num

/-! ## §2 — ch07: the qutrit/qubit entropy ratio -/

/-- The ratio the chapter computes: `S₃/S₂ = log 3 / log 2`. -/
noncomputable def qutritQubitRatio : ℝ := Real.log 3 / Real.log 2

/-- **The integer certificate.** `2¹⁵⁸ < 3¹⁰⁰ < 2¹⁵⁹`, decided by `norm_num`
    on exact integer arithmetic. This is what pins the ratio without any
    logarithm estimates. -/
theorem pow_certificate :
    (2 : ℝ) ^ (158 : ℕ) < (3 : ℝ) ^ (100 : ℕ) ∧
    (3 : ℝ) ^ (100 : ℕ) < (2 : ℝ) ^ (159 : ℕ) := by
  constructor <;> norm_num

/-- **(B1)** `1.58 < log 3 / log 2 < 1.59`, obtained from the integer
    certificate by taking logs and dividing by `100 · log 2 > 0`. -/
theorem qutritQubitRatio_bracket :
    (158 / 100 : ℝ) < qutritQubitRatio ∧ qutritQubitRatio < (159 / 100 : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨hc1, hc2⟩ := pow_certificate
  have e2 : Real.log ((2 : ℝ) ^ (158 : ℕ)) = 158 * Real.log 2 := by
    rw [Real.log_pow]; push_cast; ring
  have e3 : Real.log ((3 : ℝ) ^ (100 : ℕ)) = 100 * Real.log 3 := by
    rw [Real.log_pow]; push_cast; ring
  have e4 : Real.log ((2 : ℝ) ^ (159 : ℕ)) = 159 * Real.log 2 := by
    rw [Real.log_pow]; push_cast; ring
  have h1 : 158 * Real.log 2 < 100 * Real.log 3 := by
    rw [← e2, ← e3]; exact Real.log_lt_log (by positivity) hc1
  have h2 : 100 * Real.log 3 < 159 * Real.log 2 := by
    rw [← e3, ← e4]; exact Real.log_lt_log (by positivity) hc2
  unfold qutritQubitRatio
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hl2]; linarith
  · rw [div_lt_iff₀ hl2]; linarith

/-- **(B2)** The entanglement-capacity increase exceeds `50 %` strictly, and
    lies below `59 %`. So the chapter's "50 % more" is wrong and its own later
    figure of `58.5 %` falls inside the certified bracket. -/
theorem increase_exceeds_fifty_percent :
    (1 / 2 : ℝ) < qutritQubitRatio - 1 ∧
    qutritQubitRatio - 1 < (59 / 100 : ℝ) ∧
    (58 / 100 : ℝ) < (585 / 1000 : ℝ) ∧ (585 / 1000 : ℝ) < (59 / 100 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := qutritQubitRatio_bracket
  refine ⟨by linarith, by linarith, by norm_num, by norm_num⟩

/-! ## §3 — Capstone -/

/-- **★ ch07 / ch14 numeric refutation capstone ★**

    ch14: the see-saw formula at the chapter's own inputs gives a mass in
    `(8, 9) × 10⁻⁵` eV, not the claimed `10⁻¹⁵` eV, and the claimed value
    corresponds to a SUSY scale between `3` and `4` MeV rather than `1` TeV.

    ch07: the qutrit/qubit entropy ratio lies in `(1.58, 1.59)`, so the
    capacity increase strictly exceeds `50 %`; the chapter's own `58.5 %` is
    inside the bracket and its "50 % more" is not. -/
theorem Ch07Ch14Refutation_capstone :
    ((8 / 10 ^ 5 : ℝ) < consciousinoMass_eV ∧
      consciousinoMass_eV < (9 / 10 ^ 5 : ℝ)) ∧
    consciousinoMass_eV ≠ claimedMass_eV ∧
    ((158 / 100 : ℝ) < qutritQubitRatio ∧ qutritQubitRatio < (159 / 100 : ℝ)) ∧
    (1 / 2 : ℝ) < qutritQubitRatio - 1 :=
  ⟨consciousinoMass_bracket,
   consciousinoMass_ne_claimed,
   qutritQubitRatio_bracket,
   increase_exceeds_fifty_percent.1⟩

/-! ## §4 — Non-vacuity -/

/-- Non-vacuity: both quantities are strictly positive, so the brackets above
    are not brackets on zero. -/
theorem both_quantities_pos : 0 < consciousinoMass_eV ∧ 0 < qutritQubitRatio := by
  refine ⟨?_, ?_⟩
  · unfold consciousinoMass_eV M_SUSY_GeV M_Planck_GeV; norm_num
  · have := qutritQubitRatio_bracket.1; linarith

end PrincipiaTractalis.Ch07Ch14Refutation

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch07Ch14Refutation.consciousinoMass_bracket
#print axioms PrincipiaTractalis.Ch07Ch14Refutation.consciousinoMass_ne_claimed
#print axioms PrincipiaTractalis.Ch07Ch14Refutation.claimedMass_forces_MeV_scale
#print axioms PrincipiaTractalis.Ch07Ch14Refutation.qutritQubitRatio_bracket
#print axioms PrincipiaTractalis.Ch07Ch14Refutation.increase_exceeds_fifty_percent
#print axioms PrincipiaTractalis.Ch07Ch14Refutation.Ch07Ch14Refutation_capstone
