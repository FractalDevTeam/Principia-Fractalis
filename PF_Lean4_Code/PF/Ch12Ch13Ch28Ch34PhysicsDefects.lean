/-
# Ch 12 / 13 / 28 / 34 — Physics and Infrastructure Defects (2026-10-05)

Six defects. Two of them are the campaign's recurring shape: a correction that
was written correctly and then left contradicted by a sentence a few lines away.

## ch12 — the crystallization energy exceeds its own input mass

`ch12_qft_consciousness.tex:331–337`:

> "For `g_C ∼ 0.1` and `m_C ∼ 10⁻⁵ eV` (neutrino mass scale):
>  `E_crystallization ∼ 1 eV`. This is the energy scale of biochemistry —
>  exactly where life emerges!"

The relation is `E_cryst ∼ m_C · exp(−1/(b₀ g_C²))`, and `:319` establishes
`b₀ = (11N_c − 2N_f)/12π > 0`. Since `exp(−x) < 1` for every `x > 0`
(`exp_neg_lt_one`), the output is **strictly below its own input mass**
(`crystallization_below_input`):

  `E_cryst < m_C = 10⁻⁵ eV`,

for every positive `b₀`, not `∼ 1 eV` — which would be `10⁵` times the input.
Computed across `b₀ ∈ [0.01, 100]` the value never exceeds `3.7 × 10⁻⁶` eV, and
at the chapter's own QCD-like `b₀` of order one it is `10⁻⁴⁹` eV.

This is an **impossible-direction** defect: an exponential suppression factor
cannot amplify. The biochemistry-scale coincidence that the exclamation rests on
is therefore unavailable from this formula at these inputs.

## ch12 — a combinatorial factor that is not what it is said to equal

`:195` asserts `4!/(2!)⁴ = 3`. Literally `24/16 = 3/2`
(`pairing_factor_mismatch`). The value `3` *is* the right count of ways to split
four objects into two unordered pairs; the formula for it is `4!/(2²·2!) = 3`
(`correct_pairing_formula`). Only the displayed denominator is wrong.

## ch12 — two order-of-magnitude predictions

`:432–440`: `σ(e⁺e⁻→Cγ) ∼ g²α/s` at `g ∼ 10⁻⁶` and `√s = 1` TeV gives
`2.84 × 10⁻¹²` pb, not the stated `10⁻¹⁵` pb (`cross_section_bracket`) — about
`3.5` orders high.

`:459–464`: `Δx ∼ πℏ/(m_C c)` at `m_C ∼ 10⁻⁵` eV gives `6.2 × 10⁻²` m, i.e.
`6.2` cm, not the stated `10 μm` (`fringe_spacing_bracket`) — a factor near
`6200`.

## ch13 — a paragraph the chapter has already withdrawn, still standing

`:300–323` is a dated 2026-10-03 remark that proves `w_C ∈ [−1/3, +1/3]`, states
that "increasing `w_C` toward positive values gives `p_C = w_C ρ_C > 0`, i.e.
**positive** pressure, not the negative pressure the interpretation paragraph
asserts", and concludes "what does not survive is its reading as a source of
cosmic acceleration".

**The paragraph it names is still there, unedited, eleven lines below**
(`:325–337`), reading: "The equation of state parameter `w_C` increases toward
positive values, corresponding to *negative pressure* that opposes cosmic
acceleration. This provides a dynamic mechanism for dark energy:
`Λ_eff(t) = Λ₀exp[−∫Γ_C dt']`."

The sign algebra is immediate: `w_C > 0` and `ρ_C > 0` give `p_C > 0`
(`positive_w_gives_positive_pressure`), so "increases toward positive values,
corresponding to negative pressure" is self-contradictory on its own terms.
`PF/EquationOfStateBridge_r219.lean` independently proves that the
`Λ_eff = Λ₀exp(−∫g)` mechanism cannot reach `w < −1` for a non-negative
suppression rate.

So the chapter simultaneously asserts and withdraws the same mechanism. This is
the same failure as `ch29:442` and `ch23`'s UV claim: the defect was diagnosed
correctly and the dependent sentence was left alone.

## ch28 — the inflationary Hubble scale

`:263–271` sets `Λ_eff^inflation = Λ₀ ∼ M_Pl⁴` and then writes
`H_I² = Λ₀/3 ∼ M_Pl⁴/3 ⇒ H_I ∼ 10¹⁴ GeV`.

Two problems. **As typeset it is dimensionally inconsistent**: `H²` has
dimensions of `GeV²` while `Λ₀ ∼ M_Pl⁴` has `GeV⁴`, so the stated equation
cannot hold in the chapter's own units. The standard Friedmann relation in the
reduced-Planck convention the chapter uses elsewhere is `H² = Λ₀/(3M_Pl²)`,
which with `M_Pl = 2.4 × 10¹⁸` GeV gives

  `H_I = M_Pl/√3 = 1.39 × 10¹⁸ GeV`  (`hubble_from_friedmann`),

**4.1 orders above the stated `10¹⁴`**. Conversely the `Λ₀` that would give
`H_I = 10¹⁴` GeV is `1.73 × 10⁶⁵ GeV⁴`, **8.3 orders below `M_Pl⁴`**
(`required_lambda_is_not_planck_scale`). The two printed numbers are the
GUT-inflation scale and the full-Planck scale respectively, and they are not the
same scale.

## ch34 — the chapter that says what is verified was skipped by the pass that corrected its sibling

`ch35`'s own dated 2026-10-03 correction proves the shown discretisation cannot
deliver its claimed resources. `ch34:598` nonetheless still tabulates
"P1: Fractal operators (L16) & **128 GB** & 4 hours & 5 GB", with `:609`
("128 GB ideal") and `:255` ("4 hours (level 16)") restating it.

A dense `float64` operator at level 16 has `N = 3¹⁶ = 43 046 721`, so it needs
`8N² = 14 824 161 510 814 728` bytes — **14.8 PB**, exceeding 128 GB by a factor
above `115 000` (`level16_memory_exceeds_claim`). The largest `N` that fits in
128 GB is `126 491` (`affordable_dimension`), which is level 10, not 16.

A `grep` for `2026-10-03` over `ch34` returns **zero** matches while the same
grep over `ch33` and `ch35` returns several: the correction pass simply did not
reach it. The P-vs-NP gap *conclusion* is unaffected — it is framed as an output
of the corrected code path — but the stated budget for reproducing it is false,
and this is the chapter a referee would follow.

## Scope

Arithmetic, dimensional analysis, and exact integer counting. No claim here
bears on whether a consciousness field exists, on inflation, or on P versus NP.
`b₀ > 0` and the reduced-Planck convention are taken from the chapters' own
text.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics

/-! ## §1 — ch12: the crystallization energy -/

/-- **An exponential suppression factor is strictly below one.** -/
theorem exp_neg_lt_one (x : ℝ) (hx : 0 < x) : Real.exp (-x) < 1 := by
  rw [Real.exp_lt_one_iff]
  linarith

/-- **★ So the crystallization energy is strictly below its own input mass. ★**

    For every positive `b₀` and coupling, `E_cryst = m_C·exp(−1/(b₀g²)) < m_C`.
    The chapter claims `1` eV from `m_C = 10⁻⁵` eV, which is `10⁵` times larger
    — a direction an exponential suppression cannot produce. -/
theorem crystallization_below_input (mC x : ℝ) (hm : 0 < mC) (hx : 0 < x) :
    mC * Real.exp (-x) < mC := by
  have h := exp_neg_lt_one x hx
  nlinarith

/-- Stated against the chapter's own figures: the output cannot reach `1` eV
    from an input of `10⁻⁵` eV, since it cannot even reach the input. -/
theorem claimed_energy_exceeds_input :
    ∀ x : ℝ, 0 < x → (1 / 10 ^ 5 : ℝ) * Real.exp (-x) < 1 / 10 ^ 5 ∧
      (1 / 10 ^ 5 : ℝ) < 1 := by
  intro x hx
  exact ⟨crystallization_below_input _ x (by norm_num) hx, by norm_num⟩

/-! ## §2 — ch12: the combinatorial factor -/

/-- **`4!/(2!)⁴ = 3/2`, not `3`.** -/
theorem pairing_factor_mismatch :
    (24 : ℝ) / 16 = 3 / 2 ∧ (24 : ℝ) / 16 ≠ 3 := by
  refine ⟨by norm_num, by norm_num⟩

/-- The value `3` is correct; the formula for it is `4!/(2²·2!)`. -/
theorem correct_pairing_formula : (24 : ℕ) / (2 ^ 2 * 2) = 3 := by decide

/-! ## §3 — ch12: the two predictions -/

/-- `σ = g²α/s` at `g = 10⁻⁶`, `α = 1/137`, `s = 10⁶ GeV²`, converted to
    picobarns with `1 GeV⁻² = 3.894 × 10⁸` pb.

    Folded to one rational: `g²α/s = 10⁻¹² · (1/137) · 10⁻⁶`, so
    `σ_pb = 3894 · 10⁵ / (137 · 10¹⁸)`. A first draft wrote the conversion as
    `3894/10 · 10⁷ = 3.894 × 10⁹`, a factor of ten too large, and left nested
    divisions that defeated `norm_num`. Both corrected; the folded form is
    checkable by hand. -/
noncomputable def crossSectionPb : ℝ := 3894 * 10 ^ 5 / (137 * 10 ^ 18)

/-- **★ The cross-section is near `2.8 × 10⁻¹²` pb, not `10⁻¹⁵`. ★** -/
theorem cross_section_bracket :
    (28 / 10 ^ 13 : ℝ) < crossSectionPb ∧ crossSectionPb < (29 / 10 ^ 13 : ℝ) := by
  unfold crossSectionPb
  refine ⟨by norm_num, by norm_num⟩

/-- And it exceeds the stated `10⁻¹⁵` pb by more than two thousand. -/
theorem cross_section_exceeds_claim :
    (2000 : ℝ) * (1 / 10 ^ 15) < crossSectionPb := by
  have := cross_section_bracket.1
  nlinarith [this]

/-- `Δx = πℏc/(m_C c²)` in metres — i.e. `πℏc/m_C` with `ℏc` in eV·m — using
    `ℏ = 6.582 × 10⁻¹⁶` eV·s, `c = 2.998 × 10⁸` m/s, `m_C = 10⁻⁵` eV.

    The constants are folded into one rational, `π · 19 732 836 / 10⁹`, because
    `6582 · 2998 = 19 732 836` and the powers of ten collect to `10⁻⁹`. A first
    draft left them as nested divisions, which defeated `nlinarith`, and also
    wrote `c` as `2.998 × 10⁹` — a factor of ten too large. Both are corrected
    here; the folded form is checkable by hand. -/
noncomputable def fringeSpacingM : ℝ :=
  Real.pi * 19732836 / 10 ^ 9

/-- **★ The fringe spacing is about `6.2` cm, not `10 μm`. ★**

    A factor near `6200`. -/
theorem fringe_spacing_bracket :
    (61 / 1000 : ℝ) < fringeSpacingM ∧ fringeSpacingM < (63 / 1000 : ℝ) := by
  have hlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hhi : Real.pi < 3.141593 := Real.pi_lt_d6
  unfold fringeSpacingM
  constructor
  · rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 9)]; nlinarith [hlo]
  · rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 10 ^ 9)]; nlinarith [hhi]

/-- Stated against the claim: `10 μm = 10⁻⁵` m is far below it. -/
theorem fringe_spacing_exceeds_claim :
    (1000 : ℝ) * (1 / 10 ^ 5) < fringeSpacingM := by
  have := fringe_spacing_bracket.1
  nlinarith [this]

/-! ## §4 — ch13: the sign of the pressure -/

/-- **★ Positive `w` with positive density gives POSITIVE pressure. ★**

    `p_C = w_C ρ_C`. So "`w_C` increases toward positive values, corresponding
    to negative pressure" is self-contradictory, exactly as the chapter's own
    2026-10-03 remark states — and the paragraph it withdraws is still in
    place. -/
theorem positive_w_gives_positive_pressure (w rho : ℝ) (hw : 0 < w) (hrho : 0 < rho) :
    0 < w * rho := mul_pos hw hrho

/-- And negative pressure requires negative `w`, which the remark's proved range
    `w_C ∈ [−1/3, 1/3]` permits only on the other side of zero — so the two
    readings cannot be combined. -/
theorem negative_pressure_needs_negative_w (w rho : ℝ) (hrho : 0 < rho)
    (hp : w * rho < 0) : w < 0 := by
  by_contra h
  push_neg at h
  exact absurd hp (not_lt.mpr (mul_nonneg h hrho.le))

/-! ## §5 — ch28: the inflationary Hubble scale -/

/-- Reduced Planck mass in GeV, as `ch28:241` gives it. -/
noncomputable def MPl : ℝ := 24 / 10 * 10 ^ 18

/-- `H_I = M_Pl/√3` from the standard Friedmann relation `H² = Λ/(3M_Pl²)` at
    `Λ = M_Pl⁴`. -/
noncomputable def hubbleInflation : ℝ := MPl / Real.sqrt 3

/-- **★ The Friedmann relation gives `H_I ≈ 1.39 × 10¹⁸` GeV, not `10¹⁴`. ★**

    Four orders above the stated figure. -/
theorem hubble_from_friedmann :
    (138 / 100 * 10 ^ 18 : ℝ) < hubbleInflation ∧
    hubbleInflation < (139 / 100 * 10 ^ 18 : ℝ) := by
  have h3 : Real.sqrt 3 < 1733 / 1000 := by
    have : (1733 / 1000 : ℝ) ^ 2 > 3 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have h3' : (1732 / 1000 : ℝ) < Real.sqrt 3 := by
    have : (1732 / 1000 : ℝ) ^ 2 < 3 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hpos : (0:ℝ) < Real.sqrt 3 := by nlinarith
  unfold hubbleInflation MPl
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith [h3]
  · rw [div_lt_iff₀ hpos]; nlinarith [h3']

/-- **And the `Λ₀` that WOULD give `10¹⁴` GeV is eight orders below `M_Pl⁴`.**

    `Λ₀ = 3·H²·M_Pl² = 1.728 × 10⁶⁵` against `M_Pl⁴ = 3.318 × 10⁷³`. The two
    printed numbers are the GUT-inflation and full-Planck scales, not one
    scale. -/
theorem required_lambda_is_not_planck_scale :
    (3 : ℝ) * (10 ^ 14) ^ 2 * MPl ^ 2 < 10 ^ 66 ∧
    (10 : ℝ) ^ 73 < MPl ^ 4 := by
  unfold MPl
  refine ⟨by norm_num, by norm_num⟩

/-! ## §6 — ch34: the level-16 memory claim -/

/-- Dimension of the level-`k` discretisation, `3^k`. -/
def dim3 (k : ℕ) : ℕ := 3 ^ k

/-- Bytes for a dense `float64` operator of dimension `N`. -/
def denseBytes (N : ℕ) : ℕ := 8 * N * N

/-- **★ Level 16 needs 14.8 PB, exceeding the claimed 128 GB by over 115 000. ★**

    Exact integer arithmetic: `3¹⁶ = 43 046 721` and
    `8·43 046 721² = 14 824 161 510 814 728`. -/
theorem level16_memory_exceeds_claim :
    dim3 16 = 43046721 ∧
    denseBytes (dim3 16) = 14824161510814728 ∧
    115000 * 128000000000 < 14824161510814728 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The largest dimension that fits in 128 GB is `126 491`** — level 10, not
    level 16. -/
theorem affordable_dimension :
    denseBytes 126491 ≤ 128000000000 ∧ 128000000000 < denseBytes 126492 ∧
    dim3 10 = 59049 ∧ dim3 11 = 177147 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Level 12 and 14 for the record: `2.26` TB and `183` TB, both already past
    128 GB, so the claim fails well before level 16. -/
theorem lower_levels_already_exceed :
    128000000000 < denseBytes (dim3 12) ∧
    denseBytes (dim3 12) < denseBytes (dim3 14) := by
  refine ⟨by decide, by decide⟩

/-! ## §7 — Capstone -/

/-- **★ Ch 12 / 13 / 28 / 34 physics-defect capstone ★**

    An exponential suppression cannot exceed its input; `4!/(2!)⁴ ≠ 3`; positive
    `w` gives positive pressure, against a paragraph the chapter has already
    withdrawn; the Friedmann relation puts `H_I` four orders above the printed
    figure; and a dense level-16 operator needs five orders more memory than
    claimed. -/
theorem PhysicsDefects_capstone :
    (∀ mC x : ℝ, 0 < mC → 0 < x → mC * Real.exp (-x) < mC) ∧
    ((24 : ℝ) / 16 ≠ 3) ∧
    (∀ w rho : ℝ, 0 < w → 0 < rho → 0 < w * rho) ∧
    denseBytes (dim3 16) = 14824161510814728 ∧
    115000 * 128000000000 < 14824161510814728 :=
  ⟨crystallization_below_input,
   pairing_factor_mismatch.2,
   positive_w_gives_positive_pressure,
   level16_memory_exceeds_claim.2.1,
   level16_memory_exceeds_claim.2.2⟩

/-! ## §8 — Non-vacuity -/

/-- Non-vacuity: the suppressed energy is positive, so the bound is not a bound
    on zero; and the memory figures are positive counts. -/
theorem quantities_are_positive :
    0 < Real.exp (-(1 : ℝ)) ∧ 0 < denseBytes (dim3 16) ∧ 0 < crossSectionPb := by
  refine ⟨Real.exp_pos _, by decide, ?_⟩
  have := cross_section_bracket.1
  nlinarith [this]

end PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.exp_neg_lt_one
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.crystallization_below_input
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.claimed_energy_exceeds_input
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.pairing_factor_mismatch
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.correct_pairing_formula
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.cross_section_bracket
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.cross_section_exceeds_claim
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.fringe_spacing_bracket
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.fringe_spacing_exceeds_claim
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.positive_w_gives_positive_pressure
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.negative_pressure_needs_negative_w
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.hubble_from_friedmann
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.required_lambda_is_not_planck_scale
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.level16_memory_exceeds_claim
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.affordable_dimension
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.lower_levels_already_exceed
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.PhysicsDefects_capstone
#print axioms PrincipiaTractalis.Ch12Ch13Ch28Ch34Physics.quantities_are_positive
