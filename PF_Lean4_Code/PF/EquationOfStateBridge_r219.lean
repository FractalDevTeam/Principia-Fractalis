/-
# PF.EquationOfStateBridge_r219

★★★ 2026-08-10 — THE Λ-DECAY LAW ACQUIRES AN OBSERVABLE EQUATION OF STATE ★★★

## The bridge, in one line

`PF/ModifiedFriedmann_r187.lean` kernel-checks the framework's Λ-suppression
ODE

  `Λ_eff(t) = Λ₀ · exp(−∫₀ᵗ g)`,   `Λ_eff' = −g · Λ_eff`   (`hasDerivAt_lambdaEff`).

Take the dark-energy density proportional to `Λ_eff`.  The single-component
continuity equation is `ρ' + 3H(1+w)ρ = 0`.  Matching r187's *proved*
derivative against that form pins `w` with no freedom left:

  **w(t) = −1 + g(t) / (3 H(t))**   — exact, no approximation, no limit taken.

This file DERIVES that identity from r187's derivative theorem
(`HasDerivAt.unique` + `lambdaEff_pos` to cancel the nonvanishing factor).
It is not postulated here and it is not re-derived by hand: §2 genuinely
consumes `hasDerivAt_lambdaEff`.

## The physics content: r187's monotone form is NON-PHANTOM

r187's `lambdaEff_antitone` (monotone decay of `Λ_eff`) carries the hypothesis
`hg0 : ∀ s, 0 ≤ g s`.  §3 proves that hypothesis is *exactly equivalent* to
`w ≥ −1`:

  `0 ≤ g t  ⟺  −1 ≤ w(t)`,    `g t = 0  ⟺  w(t) = −1`,
  `g t < 0  ⟺  w(t) < −1`.

So the monotone-decay form of the framework is non-phantom and **cannot cross
`w = −1`**.  Crossing requires `g` to change sign.  r187's ODE *permits* this —
`hasDerivAt_lambdaEff` needs only `Continuous g`, no sign condition — while
r187's monotonicity theorem *forbids* it.  The two theorems are not in
conflict; they describe different regimes of the same postulated law, and the
observable that distinguishes them is `w`.

§4 locates the crossing: with `g` continuous and changing sign, `w` crosses
`−1` exactly at the zeros of `g`, and at least one such zero exists between a
negative and a positive value (intermediate value theorem).

## §5 and the DESI comparison — MEASUREMENT IN PROSE, NOT IN THE KERNEL

§5 contains only arithmetic about the CPL parametrization `w(a) = w₀ + wₐ(1−a)`:
that `w ≥ −1` on all of `a ∈ (0,1]` forces `wₐ ≥ −1 − w₀`, and that the
crossing sits at `a = 1 + (1+w₀)/wₐ`.  No number from any dataset appears in
any theorem statement in this file.

The 2025 DESI DR2 fits, recorded here as prose because they are measurements
and not mathematics:

| dataset                | w₀             | wₐ            | g₀/H₀ | wₐ bound for g≥0 | tension | crossing z |
|------------------------|----------------|---------------|-------|------------------|---------|------------|
| DESI DR2+CMB           | −0.667 ± 0.088 | −1.09 ± 0.29  | 0.999 | ≥ −0.333         | 2.6σ    | 0.440      |
| DESI DR2+CMB+DESY5     | −0.752 ± 0.057 | −0.86 ± 0.22  | 0.744 | ≥ −0.248         | 2.8σ    | 0.405      |
| DESI DR2+CMB+Union3    | −0.65  ± 0.10  | −1.27 ± 0.40  | 1.050 | ≥ −0.350         | 2.3σ    | 0.380      |

How each column is read off the theorems below (arithmetic, done outside the
kernel): `g₀/H₀ = 3(1+w₀)` from §1's `wEff` evaluated today; the `wₐ` bound is
`−1 − w₀` from `cpl_nonphantom_forces_wa_bound`; the tension is
`(wₐ − bound)/σ(wₐ)`; the crossing redshift is `z = 1/a − 1` with
`a = 1 + (1+w₀)/wₐ` from `cpl_crossing`.  Every fit prefers `wₐ` *below* the
non-phantom bound at 2–3σ, i.e. prefers a `g` that goes negative.

## SCOPE — read this before quoting anything above

This is a theorem about **the framework's own postulated Λ-suppression law**.
It asserts nothing about physical spacetime.  Whether `Λ_eff(C)` describes
reality is exactly what the DESI comparison would test, and **that test is not
performed here**: no likelihood, no fit, no data ingestion, no kernel claim
about the universe.  What is established is the conditional — *if* the
framework's Λ-decay law holds with `g ≥ 0`, *then* `w ≥ −1`, and a measured
`w < −1` would falsify that branch.

The book's `Λ_eff/Λ₀ = 10⁻¹²⁰` numerology is untouched, exactly as r187
already says: what is kernel-checked is the differential law, which is the
part that is mathematics.

Cross-reference: `PF/ModifiedFriedmann_r187.lean` (the Λ-decay law), whose
`LambdaEff`, `hasDerivAt_lambdaEff`, `lambdaEff_pos` and `lambdaEff_antitone`
this file imports and uses rather than restates.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-10.
-/
import PF.ModifiedFriedmann_r187
import Mathlib.Topology.Order.IntermediateValue

set_option maxHeartbeats 400000

namespace PrincipiaTractalis.EquationOfStateBridge

open PrincipiaTractalis.ModifiedFriedmann

noncomputable section

/-! ### §0 — pure real arithmetic, factored out over plain variables

These three lemmas are the entire content of the sign analysis in §3, stated
without any cosmology so the inequality manipulation is auditable on its own.
-/

/-- `−1 ≤ −1 + x/c ↔ 0 ≤ x`, for `c > 0`. -/
theorem neg_one_le_neg_one_add_div_iff (x c : ℝ) (hc : 0 < c) :
    -1 ≤ -1 + x / c ↔ 0 ≤ x := by
  have key : 0 ≤ x / c ↔ 0 ≤ x := by rw [le_div_iff₀ hc, zero_mul]
  constructor
  · intro h; exact key.mp (by linarith)
  · intro h; have := key.mpr h; linarith

/-- `−1 + x/c = −1 ↔ x = 0`, for `c ≠ 0`. -/
theorem neg_one_add_div_eq_neg_one_iff (x c : ℝ) (hc : c ≠ 0) :
    -1 + x / c = -1 ↔ x = 0 := by
  constructor
  · intro h
    have hxc : x / c = 0 := by linarith
    exact (div_eq_zero_iff.mp hxc).resolve_right hc
  · intro h; simp [h]

/-- `−1 + x/c < −1 ↔ x < 0`, for `c > 0`. -/
theorem neg_one_add_div_lt_neg_one_iff (x c : ℝ) (hc : 0 < c) :
    -1 + x / c < -1 ↔ x < 0 := by
  have key : x / c < 0 ↔ x < 0 := by rw [div_lt_iff₀ hc, zero_mul]
  constructor
  · intro h; exact key.mp (by linarith)
  · intro h; have := key.mpr h; linarith

/-! ### §1 — definitions

`H` is the Hubble rate, taken as given; positivity is a hypothesis wherever it
is needed rather than being baked into the definition.
-/

/-- The equation-of-state parameter forced on a `Λ_eff`-proportional dark
energy by r187's suppression law: `w = −1 + g/(3H)`.

Sanity: `g ≡ 0` gives `w ≡ −1`, a true cosmological constant.  A positive
suppression rate pushes `w` *up* from `−1` (quintessence side); only a negative
`g` can push it down (phantom side). -/
def wEff (g H : ℝ → ℝ) (t : ℝ) : ℝ := -1 + g t / (3 * H t)

/-- The single-component continuity equation `ρ' = −3H(1+w)ρ`, localized at a
time `t` and phrased as a `HasDerivAt` so it can be matched against r187's
proved derivative.  This is the standard FLRW conservation law for one fluid
with equation of state `w`; it is a hypothesis here, not a claim. -/
def ContinuityEqAt (ρ w H : ℝ → ℝ) (t : ℝ) : Prop :=
  HasDerivAt ρ (-(3 * H t * (1 + w t)) * ρ t) t

/-! ### §2 — THE BRIDGE THEOREM

The derivation is visible in the proof, not asserted in the statement:
`hasDerivAt_lambdaEff` supplies one expression for `Λ_eff'`, the continuity
hypothesis supplies another, `HasDerivAt.unique` identifies them, and
`lambdaEff_pos` cancels the (strictly positive, hence nonzero) common factor.
-/

/-- **The bridge.**  If the dark-energy density *is* r187's `Λ_eff` and it
satisfies the continuity equation with equation of state `w`, then `w` is
forced to be `wEff g H = −1 + g/(3H)`.

Nothing is assumed about `g` beyond continuity — in particular no sign
condition — so this holds on both sides of the phantom divide. -/
theorem wEff_of_continuity (Λ₀ : ℝ) (hΛ : 0 < Λ₀) {g H w : ℝ → ℝ}
    (hg : Continuous g) (hH : ∀ t, 0 < H t) (t : ℝ)
    (hcont : ContinuityEqAt (LambdaEff Λ₀ g) w H t) :
    w t = wEff g H t := by
  -- r187's kernel-checked derivative of the suppression law.
  have hderiv : HasDerivAt (LambdaEff Λ₀ g) (-(g t) * LambdaEff Λ₀ g t) t :=
    hasDerivAt_lambdaEff Λ₀ hg t
  -- r187's positivity: the common factor is nonzero, so it cancels.
  have hL : 0 < LambdaEff Λ₀ g t := lambdaEff_pos hΛ g t
  have huniq : -(g t) * LambdaEff Λ₀ g t
      = -(3 * H t * (1 + w t)) * LambdaEff Λ₀ g t :=
    hderiv.unique hcont
  have hcancel : -(g t) = -(3 * H t * (1 + w t)) :=
    mul_right_cancel₀ (ne_of_gt hL) huniq
  have hg3 : g t = 3 * H t * (1 + w t) := by linarith
  have h3H : (0 : ℝ) < 3 * H t := by have := hH t; linarith
  have hHne : H t ≠ 0 := ne_of_gt (hH t)
  have hne : (3 : ℝ) * H t ≠ 0 := ne_of_gt h3H
  have hkey : g t / (3 * H t) = 1 + w t := by
    field_simp
    linear_combination hg3
  simp only [wEff]
  linarith

/-- The same bridge for a density merely *proportional* to `Λ_eff`,
`ρ = c · Λ_eff` with `c > 0` — which is the physically stated form
`ρ_Λ ∝ Λ_eff`.  The proportionality constant drops out, as it must. -/
theorem wEff_of_continuity_proportional (Λ₀ c : ℝ) (hΛ : 0 < Λ₀) (hc : 0 < c)
    {g H w : ℝ → ℝ} (hg : Continuous g) (hH : ∀ t, 0 < H t) (t : ℝ)
    (hcont : ContinuityEqAt (fun s => c * LambdaEff Λ₀ g s) w H t) :
    w t = wEff g H t := by
  have hderiv : HasDerivAt (fun s => c * LambdaEff Λ₀ g s)
      (c * (-(g t) * LambdaEff Λ₀ g t)) t :=
    (hasDerivAt_lambdaEff Λ₀ hg t).const_mul c
  have hL : 0 < LambdaEff Λ₀ g t := lambdaEff_pos hΛ g t
  have hcL : 0 < c * LambdaEff Λ₀ g t := mul_pos hc hL
  have huniq : c * (-(g t) * LambdaEff Λ₀ g t)
      = -(3 * H t * (1 + w t)) * (c * LambdaEff Λ₀ g t) :=
    hderiv.unique hcont
  have hshape : -(g t) * (c * LambdaEff Λ₀ g t)
      = -(3 * H t * (1 + w t)) * (c * LambdaEff Λ₀ g t) := by
    linear_combination huniq
  have hcancel : -(g t) = -(3 * H t * (1 + w t)) :=
    mul_right_cancel₀ (ne_of_gt hcL) hshape
  have hg3 : g t = 3 * H t * (1 + w t) := by linarith
  have h3H : (0 : ℝ) < 3 * H t := by have := hH t; linarith
  have hHne : H t ≠ 0 := ne_of_gt (hH t)
  have hne : (3 : ℝ) * H t ≠ 0 := ne_of_gt h3H
  have hkey : g t / (3 * H t) = 1 + w t := by
    field_simp
    linear_combination hg3
  simp only [wEff]
  linarith

/-! ### §3 — THE SIGN THEOREM: the physics content

r187's `lambdaEff_antitone` assumes `hg0 : ∀ s, 0 ≤ g s`, and `g ≥ 0` is
**exactly equivalent** to `w ≥ −1`.  So the monotone-decay form of the
framework is NON-PHANTOM and cannot cross `w = −1`.  Crossing requires `g` to
change sign, which r187's ODE permits (`hasDerivAt_lambdaEff` needs only
continuity of `g`) but its monotonicity theorem forbids.
-/

/-- A nonnegative suppression rate — exactly r187's `lambdaEff_antitone`
hypothesis, pointwise — gives a non-phantom equation of state. -/
theorem wEff_ge_neg_one {g H : ℝ → ℝ} {t : ℝ} (hg0 : 0 ≤ g t) (hH : 0 < H t) :
    -1 ≤ wEff g H t := by
  have h3H : (0 : ℝ) < 3 * H t := by linarith
  exact (neg_one_le_neg_one_add_div_iff (g t) (3 * H t) h3H).mpr hg0

/-- The converse too: non-phantom `⟺` nonnegative suppression rate.  This is
the biconditional that makes r187's monotone branch *equivalent* to the
non-phantom branch, not merely contained in it. -/
theorem wEff_ge_neg_one_iff {g H : ℝ → ℝ} {t : ℝ} (hH : 0 < H t) :
    -1 ≤ wEff g H t ↔ 0 ≤ g t := by
  have h3H : (0 : ℝ) < 3 * H t := by linarith
  exact neg_one_le_neg_one_add_div_iff (g t) (3 * H t) h3H

/-- `w = −1` exactly where the suppression rate vanishes: a true cosmological
constant is the `g = 0` locus and nothing else. -/
theorem wEff_eq_neg_one_iff {g H : ℝ → ℝ} {t : ℝ} (hH : 0 < H t) :
    wEff g H t = -1 ↔ g t = 0 := by
  have hne : (3 : ℝ) * H t ≠ 0 := by
    have : (0 : ℝ) < 3 * H t := by linarith
    exact ne_of_gt this
  exact neg_one_add_div_eq_neg_one_iff (g t) (3 * H t) hne

/-- Phantom (`w < −1`) `⟺` the suppression rate is negative, i.e. `Λ_eff` is
locally *growing*.  This is the branch r187's `lambdaEff_antitone` excludes. -/
theorem wEff_lt_neg_one_iff {g H : ℝ → ℝ} {t : ℝ} (hH : 0 < H t) :
    wEff g H t < -1 ↔ g t < 0 := by
  have h3H : (0 : ℝ) < 3 * H t := by linarith
  exact neg_one_add_div_lt_neg_one_iff (g t) (3 * H t) h3H

/-- Restated as the impossibility it is: under r187's monotone-decay
hypothesis the equation of state never enters the phantom regime, at any
time. -/
theorem not_phantom_of_nonneg_rate {g H : ℝ → ℝ} (hg0 : ∀ s, 0 ≤ g s)
    (hH : ∀ t, 0 < H t) (t : ℝ) : ¬ wEff g H t < -1 := by
  intro hlt
  have : g t < 0 := (wEff_lt_neg_one_iff (hH t)).mp hlt
  exact absurd (hg0 t) (not_le.mpr this)

/-! ### §4 — THE CROSSING LOCATION -/

/-- The crossing locus of the phantom divide is precisely the zero set of `g`.
(Same statement as `wEff_eq_neg_one_iff`, named for the role it plays here.) -/
theorem wEff_crossing_iff_g_zero {g H : ℝ → ℝ} {t : ℝ} (hH : 0 < H t) :
    wEff g H t = -1 ↔ g t = 0 :=
  wEff_eq_neg_one_iff hH

/-- A continuous suppression rate that changes sign must vanish somewhere
strictly in between — intermediate value theorem. -/
theorem exists_crossing_of_sign_change {g : ℝ → ℝ} (hg : Continuous g)
    {t₁ t₂ : ℝ} (ht : t₁ < t₂) (h1 : g t₁ < 0) (h2 : 0 < g t₂) :
    ∃ t ∈ Set.Ioo t₁ t₂, g t = 0 := by
  have hsub := intermediate_value_Ioo (le_of_lt ht) hg.continuousOn
  have h0 : (0 : ℝ) ∈ Set.Ioo (g t₁) (g t₂) := ⟨h1, h2⟩
  obtain ⟨x, hx, hgx⟩ := hsub h0
  exact ⟨x, hx, hgx⟩

/-- Consequently the equation of state itself crosses `−1` at some interior
time: a sign change in `g` is a genuine phantom crossing, located. -/
theorem exists_wEff_crossing_of_sign_change {g H : ℝ → ℝ} (hg : Continuous g)
    (hH : ∀ t, 0 < H t) {t₁ t₂ : ℝ} (ht : t₁ < t₂)
    (h1 : g t₁ < 0) (h2 : 0 < g t₂) :
    ∃ t ∈ Set.Ioo t₁ t₂, wEff g H t = -1 := by
  obtain ⟨t, htmem, hgt⟩ := exists_crossing_of_sign_change hg ht h1 h2
  exact ⟨t, htmem, (wEff_eq_neg_one_iff (hH t)).mpr hgt⟩

/-! ### §5 — THE CPL COMPARISON, as pure arithmetic

`w(a) = w₀ + wₐ(1−a)`.  No dataset value occurs in any statement below; see
the header table for the measurements this arithmetic is meant to be compared
against, and the SCOPE paragraph for what that comparison is not.
-/

/-- The CPL parametrization as a function of the scale factor. -/
def wCPL (w₀ wa a : ℝ) : ℝ := w₀ + wa * (1 - a)

/-- **The non-phantom constraint on CPL.**  If `w ≥ −1` holds throughout
`a ∈ (0,1]`, then `wₐ ≥ −1 − w₀`.

Note the hypothesis is only about `a > 0`; the bound is the `a → 0⁺` endpoint,
recovered here without any limit machinery by exhibiting, for any violating
`wₐ`, an explicit admissible `a` at which `w(a) < −1`. -/
theorem cpl_nonphantom_forces_wa_bound {w₀ wa : ℝ}
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 → -1 ≤ w₀ + wa * (1 - a)) :
    -1 - w₀ ≤ wa := by
  by_contra hcon
  push_neg at hcon
  rcases le_or_gt 0 wa with hwa | hwa
  · -- `wₐ ≥ 0`: evaluating at `a = 1` already gives `w₀ ≥ −1`, hence the bound.
    have h1 := h 1 one_pos le_rfl
    have hw0 : (-1 : ℝ) ≤ w₀ := by simpa using h1
    linarith
  · -- `wₐ < 0`: pick an admissible `a` small enough to violate the hypothesis.
    have hwane : wa ≠ 0 := ne_of_lt hwa
    have hnwa : (0 : ℝ) < -wa := by linarith
    have hεpos : (0 : ℝ) < -1 - w₀ - wa := by linarith
    obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ -wa * c < -1 - w₀ - wa := by
      refine ⟨(-1 - w₀ - wa) / (2 * -wa), div_pos hεpos (by linarith), ?_⟩
      have heq : -wa * ((-1 - w₀ - wa) / (2 * -wa)) = (-1 - w₀ - wa) / 2 := by
        field_simp
      rw [heq]
      linarith
    have hapos : 0 < min 1 c := lt_min one_pos hc0
    have hale : min 1 c ≤ 1 := min_le_left _ _
    have hac : min 1 c ≤ c := min_le_right _ _
    have hmul : -wa * min 1 c ≤ -wa * c :=
      mul_le_mul_of_nonneg_left hac hnwa.le
    have hfa := h (min 1 c) hapos hale
    linarith

/-- Same statement in terms of `wCPL`. -/
theorem wCPL_nonphantom_forces_wa_bound {w₀ wa : ℝ}
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 → -1 ≤ wCPL w₀ wa a) : -1 - w₀ ≤ wa :=
  cpl_nonphantom_forces_wa_bound h

/-- **The CPL crossing scale factor.**  For `wₐ ≠ 0` the phantom divide is
crossed at exactly one scale factor, `a = 1 + (1+w₀)/wₐ`. -/
theorem cpl_crossing {w₀ wa a : ℝ} (h : wa ≠ 0) :
    w₀ + wa * (1 - a) = -1 ↔ a = 1 + (1 + w₀) / wa := by
  constructor
  · intro h1
    field_simp
    linear_combination -h1
  · intro h1
    rw [h1]
    field_simp
    ring

/-- Same statement in terms of `wCPL`. -/
theorem wCPL_crossing {w₀ wa a : ℝ} (h : wa ≠ 0) :
    wCPL w₀ wa a = -1 ↔ a = 1 + (1 + w₀) / wa :=
  cpl_crossing h

/-! ### §6 — non-vacuity witnesses

Every theorem above is a conditional.  These `example`s exhibit an actual
inhabitant of each hypothesis set, so none of the sections is vacuously true.
They prove nothing new; they certify that the antecedents are satisfiable.
-/

/-- §2 is non-vacuous: `g ≡ 0`, `H ≡ 1`, `w ≡ −1` really does satisfy
`ContinuityEqAt` for `Λ_eff` — the cosmological-constant limit. -/
example (Λ₀ : ℝ) (t : ℝ) :
    ContinuityEqAt (LambdaEff Λ₀ (fun _ => 0)) (fun _ => (-1 : ℝ))
      (fun _ => (1 : ℝ)) t := by
  have h := hasDerivAt_lambdaEff Λ₀
    (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))) t
  simpa [ContinuityEqAt] using h

/-- and then the bridge returns `w = −1` on that witness, as it must. -/
example (Λ₀ : ℝ) (hΛ : 0 < Λ₀) (t : ℝ) :
    (-1 : ℝ) = wEff (fun _ => 0) (fun _ => 1) t := by
  have hc : ContinuityEqAt (LambdaEff Λ₀ (fun _ => 0)) (fun _ => (-1 : ℝ))
      (fun _ => (1 : ℝ)) t := by
    have h := hasDerivAt_lambdaEff Λ₀
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))) t
    simpa [ContinuityEqAt] using h
  exact wEff_of_continuity Λ₀ hΛ (g := fun _ => 0) (H := fun _ => 1)
    (w := fun _ => -1) continuous_const (fun _ => one_pos) t hc

/-- §4 is non-vacuous: `g = id` changes sign on `(−1, 1)`, so a genuine
crossing time exists there. -/
example : ∃ t ∈ Set.Ioo (-1 : ℝ) 1, (fun s : ℝ => s) t = 0 :=
  exists_crossing_of_sign_change continuous_id (by norm_num) (by norm_num)
    (by norm_num)

/-- §5's hypothesis is satisfiable and its bound is attained: `w₀ = −1`,
`wₐ = 0` sits exactly on `wₐ = −1 − w₀`, so the bound is sharp, not slack. -/
example : ∀ a : ℝ, 0 < a → a ≤ 1 → -1 ≤ (-1 : ℝ) + 0 * (1 - a) := by
  intro a _ _; norm_num

example : (-1 : ℝ) - (-1) ≤ 0 :=
  cpl_nonphantom_forces_wa_bound (by intro a _ _; norm_num)

end

end PrincipiaTractalis.EquationOfStateBridge

/-! ### Axiom audit — every theorem in this file -/

#print axioms PrincipiaTractalis.EquationOfStateBridge.neg_one_le_neg_one_add_div_iff
#print axioms PrincipiaTractalis.EquationOfStateBridge.neg_one_add_div_eq_neg_one_iff
#print axioms PrincipiaTractalis.EquationOfStateBridge.neg_one_add_div_lt_neg_one_iff
#print axioms PrincipiaTractalis.EquationOfStateBridge.wEff_of_continuity
#print axioms PrincipiaTractalis.EquationOfStateBridge.wEff_of_continuity_proportional
#print axioms PrincipiaTractalis.EquationOfStateBridge.wEff_ge_neg_one
#print axioms PrincipiaTractalis.EquationOfStateBridge.wEff_ge_neg_one_iff
#print axioms PrincipiaTractalis.EquationOfStateBridge.wEff_eq_neg_one_iff
#print axioms PrincipiaTractalis.EquationOfStateBridge.wEff_lt_neg_one_iff
#print axioms PrincipiaTractalis.EquationOfStateBridge.not_phantom_of_nonneg_rate
#print axioms PrincipiaTractalis.EquationOfStateBridge.wEff_crossing_iff_g_zero
#print axioms PrincipiaTractalis.EquationOfStateBridge.exists_crossing_of_sign_change
#print axioms PrincipiaTractalis.EquationOfStateBridge.exists_wEff_crossing_of_sign_change
#print axioms PrincipiaTractalis.EquationOfStateBridge.cpl_nonphantom_forces_wa_bound
#print axioms PrincipiaTractalis.EquationOfStateBridge.wCPL_nonphantom_forces_wa_bound
#print axioms PrincipiaTractalis.EquationOfStateBridge.cpl_crossing
#print axioms PrincipiaTractalis.EquationOfStateBridge.wCPL_crossing
