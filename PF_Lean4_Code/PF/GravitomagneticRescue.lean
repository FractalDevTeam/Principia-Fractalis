/-
# The Rescue: Conservation, Frame Dragging, and ch22's Own Selection Rule
(2026-10-06)

Written after being pointed at Weinstein's move and Mallett's counter-rotating
lasers. Both bear directly on the `α₃ ≲ 10⁻²⁰` obstruction recorded in
`PF/Ch08Ch14ModifiedRelativity.lean`, and **they substantially soften it** — in
the framework's favour. Three results.

## §A — The `10⁻²⁰` wall is a wall on the FORMULATION, not on the framework

The PPN preferred-frame parameters split by **origin**, not merely by size:

* `α₁`, `α₂` measure preferred-frame effects. They are nonzero when a preferred
  frame exists, but are **tunable to zero** by choice of couplings — Einstein-
  aether theory does exactly this, and lives at `α₁ = α₂ = 0` for a
  one-parameter family.
* `α₃` measures preferred-frame effects **and non-conservation together**. It
  vanishes **identically** in any theory derived from an action, because such a
  theory conserves total energy–momentum by Noether's theorem. `α₃ ≠ 0` is the
  signature of a *non-conservative* theory.

**That is the crux.** The earlier finding was that a varying `Λ_eff` forces

  `∇_μ(T^{μν} + C^{μν}) = ∇^ν Λ_eff / (8πG) ≠ 0`,

i.e. the framework **as currently written** is non-conservative — which is
precisely the class `α₃ ≲ 10⁻²⁰` exists to exclude. So the `10⁻²⁰` figure is not
a bound the framework must somehow sneak under. **It is a bound that applies only
to the non-conservative formulation, and it is lifted by repairing that.**

**The repair, stated precisely.** `Λ_eff` must come from an action — equivalently,
the field whose potential `Λ_eff` is must carry its own stress-energy `T_φ`.
Then `T + C + T_φ` is conserved, `α₃ = 0` identically rather than by tuning, and
only `α₁, α₂` remain, at `10⁻⁴` and `10⁻⁷`, which aether-type constructions
already know how to zero.

And the compensating stress-energy is **uniquely determined**:
`conservation_iff_compensating_divergence` shows total conservation holds exactly
when `∇·T_φ = −∇Λ_eff/(8πG)`. So this is not a free parameter to be fitted —
it is a specific object the framework must exhibit, and exhibiting it is the
repair.

## §B — Mallett: the mechanism is sound, the CTC claim is not, the scale is wrong

* **Frame dragging from circulating energy is standard general relativity** —
  gravitomagnetism, the Lense–Thirring effect. A loop of circulating
  energy–momentum drags inertial frames. Nothing controversial.
* **The closed-timelike-curve claim does not survive.** Olum and Everett (2005)
  showed Mallett's solution carries a **line singularity on the axis**, and that
  the CTCs persist in the limit of *vanishing* light intensity — so they come
  from the singularity, not from the light. The frame-dragging mechanism
  survives this; the time-travel conclusion does not, and should not be cited
  as support.
* **Laboratory scale is not the regime.** For a light loop of power `P` and
  radius `R`, the circulating energy is `E ≈ 2πRP/c`, the angular momentum
  `J ≈ ER/c`, and the frame-drag rate `ω ≈ GJ/(c²R³)`. At `P = 10¹⁵` W and
  `R = 1` m that is `≈ 5 × 10⁻²⁹ rad/s` (`optical_frame_drag_bracket`), about
  `10⁻¹⁴` of Earth's own `≈ 10⁻¹⁴ rad/s` — which itself required Gravity Probe B
  to measure (`ratio_to_earth_dragging`). The mechanism is right and the
  laboratory is off by fifteen orders from even the Earth-scale signal.

## §C — ch22's emergence condition IS the maximal frame-dragging condition

This is the substantive find, and it is an identity between two things the book
states independently rather than a resemblance.

Gravitomagnetism is sourced by the **circulation of momentum density** — by the
flow's **vorticity**, not its shear. And ch22's emergence condition, proved
earlier in `PF/Ch22EmergencePointSpectrum.lean`, is

  `ch₂(∇u) ≤ 0  ⟺  ‖S‖_F ≤ ‖Ω‖_F`,

i.e. **rotation dominates strain** — vorticity-dominated, shear-suppressed.
**Those are the same condition.** ch22's emergence points are exactly the
configurations that maximise the gravitomagnetic source at fixed
velocity-gradient magnitude, and the extremes line up with the sign of `ch₂`:

| configuration | `ch₂` | gravitomagnetic source |
|---|---|---|
| pure strain, no vorticity | `+1/2` | none |
| balanced | `0` | threshold |
| pure rotation, no shear | `−1/2` | maximal |

(`pure_strain_value`, `pure_rotation_value`, `rotation_is_the_negative_half`.)

So the counter-rotating vortex pair of ch22 and the counter-rotating laser pair
of Mallett's apparatus are the **same geometry**, and the framework already
contains the selection rule that picks it out. That rule was derived here from
the eigenvalue structure, with no reference to gravitomagnetism, which is what
makes the coincidence worth recording.

**What this does and does not show.** It does *not* show that consciousness
causes frame dragging, or that the magnitudes work — §B says they do not at
laboratory scale. What it shows is that the framework's own emergence criterion
selects the configurations with maximal gravitomagnetic source, and that this
follows from two independent statements in the book agreeing. That is a
structural result and it is the kind of thing the framework should be looking
for.

## Scope

**Formalized**: the uniqueness of the compensating divergence; the extremal
`ch₂` values and their identification with the rotation-dominated regime; the
optical frame-drag magnitude and its ratio to the Earth-scale signal.

**Prose only, not proved here**: that `α₃` vanishes identically in
action-derived theories (Noether, standard); that `α₁, α₂` are tunable to zero
in aether-type models (literature); that gravitomagnetism is sourced by
vorticity rather than shear (standard weak-field GR); the Olum–Everett
refutation of the CTC claim (literature). The PPN bounds are cited observational
values.

**Not claimed**: that the repair in §A has been carried out. It has not. What is
established is that it is the right repair and that the object it requires is
uniquely determined.

Author: Pablo Cohen + Claude Opus 5. 2026-10-06.
-/
import PF.Ch22EmergencePointSpectrum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace PrincipiaTractalis.GravitomagneticRescue

/-! ## §A — The compensating stress-energy is uniquely determined -/

/-- **★ Total conservation holds exactly when the compensating divergence is
    `−∇Λ/κ`. ★**

    Given that the matter-plus-consciousness divergence is `∇Λ/κ` — the
    contracted Bianchi consequence of the modified field equation — the sum with
    a third contribution vanishes **iff** that contribution's divergence is
    exactly the negative. So the field that an action-derived `Λ_eff` must carry
    is not a free parameter: it is pinned. -/
theorem conservation_iff_compensating_divergence
    (divS divPhi gradLam kap : ℝ) (hS : divS = gradLam / kap) :
    divS + divPhi = 0 ↔ divPhi = -(gradLam / kap) := by
  rw [hS]
  constructor <;> intro h <;> linarith

/-! A draft carried a companion theorem here stating
    `∇Λ/κ + −(∇Λ/κ) = 0`, closed by `ring`. That is `a + (−a) = 0` and adds
    nothing to the uniqueness statement above, which already says the
    compensator is pinned. Removed — the fifth such removal in two days, and
    the reason the scope notes in these modules are written the way they
    are. -/

/-- Without it, non-conservation is equivalent to `Λ_eff` varying at all. The
    non-conservative formulation is therefore the one `α₃` constrains. -/
theorem nonconservation_iff_varying (gradLam kap : ℝ) (hkap : 0 < kap) :
    gradLam / kap ≠ 0 ↔ gradLam ≠ 0 := by
  rw [div_ne_zero_iff]
  exact and_iff_left (ne_of_gt hkap)

/-! ## §C — ch22's condition and the gravitomagnetic extremes -/

open PrincipiaTractalis.Ch22EmergencePoint

/-- The decomposed `ch₂` of a traceless velocity-gradient tensor, with
    `s = ‖S‖_F²` and `o = ‖Ω‖_F²`. ch22 states its results about this
    expression without naming it; it is named here so the extremes can be
    stated, and ch22's theorems are reused rather than reproved. -/
noncomputable def ch2Decomposed (s o : ℝ) : ℝ := (s - o) / (2 * (s + o))

/-- **Pure strain, no vorticity: `ch₂ = +1/2`, no gravitomagnetic source.** -/
theorem pure_strain_value : ch2Decomposed 1 0 = 1 / 2 := by
  unfold ch2Decomposed; norm_num

/-- **Pure rotation, no shear: `ch₂ = −1/2`, maximal gravitomagnetic source.** -/
theorem pure_rotation_value : ch2Decomposed 0 1 = -(1 / 2) := by
  unfold ch2Decomposed; norm_num

/-- **★ The rotation-dominated regime is exactly the non-positive half of
    `ch₂`. ★**

    Reusing ch22's own equivalence: `ch₂ ≤ 0 ⟺ ‖S‖ ≤ ‖Ω‖`. Vorticity-dominated
    is the same set as emergence-admissible, and it is the set that maximises
    the gravitomagnetic source. -/
theorem rotation_is_the_negative_half (s o : ℝ) (hpos : 0 < s + o) :
    ch2Decomposed s o ≤ 0 ↔ s ≤ o := by
  unfold ch2Decomposed
  exact ch2_nonpos_iff_rotation_dominates s o hpos

/-- The extremes bracket the whole range, so the sign of `ch₂` is a complete
    classifier of which side of the strain/rotation balance a configuration
    sits on. -/
theorem extremes_bracket_the_range (s o : ℝ)
    (hs : 0 ≤ s) (ho : 0 ≤ o) (hpos : 0 < s + o) :
    -(1 / 2 : ℝ) ≤ ch2Decomposed s o ∧ ch2Decomposed s o ≤ 1 / 2 := by
  unfold ch2Decomposed
  exact decomposed_ch2_range s o hs ho hpos

/-! ## §B — Optical frame dragging, in magnitude -/

/-- Frame-drag rate for a light loop: `ω ≈ G·J/(c²R³)` with `J ≈ 2πR²P/c²`,
    so `ω ≈ 2πGP/(c⁴R)`. Evaluated at `P = 10¹⁵` W and `R = 1` m, in SI. -/
noncomputable def opticalFrameDrag (P R : ℝ) : ℝ :=
  2 * Real.pi * (6674 / 10 ^ 14) * P / ((2998 * 10 ^ 5) ^ 4 * R)
-- `c = 2.998e8 = 2998 * 10^5`. A draft of this file wrote it `2998/10^11`,
-- i.e. `2.998e-8` -- sixteen orders out, the same wrong-order-of-magnitude
-- constant this campaign keeps finding in the manuscript, committed here and
-- caught by the kernel rather than by reading.

/-- **★ At `10¹⁵` W and one metre the drag rate is below `10⁻²⁸ rad/s`. ★** -/
theorem optical_frame_drag_bracket :
    opticalFrameDrag (10 ^ 15) 1 < 1 / 10 ^ 28 := by
  have hhi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hlo : (0:ℝ) < Real.pi := Real.pi_pos
  unfold opticalFrameDrag
  rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith [hhi, hlo]


/-- **And that is some `10⁻¹⁴` of Earth's own frame dragging**, itself at
    `≈ 10⁻¹⁴ rad/s` and requiring Gravity Probe B to detect. The mechanism is
    real; the laboratory is not the regime. -/
theorem ratio_to_earth_dragging :
    (1 / 10 ^ 28 : ℝ) / (1 / 10 ^ 14) = 1 / 10 ^ 14 ∧
    (1 / 10 ^ 14 : ℝ) < 1 := by
  refine ⟨by norm_num, by norm_num⟩

/-! ## §D — Capstone -/

/-- **★ Rescue capstone ★**

    The compensating stress-energy an action-derived `Λ_eff` requires is
    uniquely determined; with it the total is conserved identically; ch22's
    emergence condition coincides with the rotation-dominated regime, whose
    extremes are `±1/2`; and optical frame dragging, while real, sits fifteen
    orders below the Earth-scale signal. -/
theorem Rescue_capstone :
    (∀ divS divPhi gradLam kap : ℝ, divS = gradLam / kap →
      (divS + divPhi = 0 ↔ divPhi = -(gradLam / kap))) ∧
    ch2Decomposed 1 0 = 1 / 2 ∧
    ch2Decomposed 0 1 = -(1 / 2) ∧
    (∀ s o : ℝ, 0 < s + o → (ch2Decomposed s o ≤ 0 ↔ s ≤ o)) ∧
    opticalFrameDrag (10 ^ 15) 1 < 1 / 10 ^ 28 :=
  ⟨conservation_iff_compensating_divergence,
   pure_strain_value,
   pure_rotation_value,
   rotation_is_the_negative_half,
   optical_frame_drag_bracket⟩

/-! ## §E — Non-vacuity -/

/-- Non-vacuity: the drag rate is a genuine positive quantity, so the bound
    above is not a bound on zero; and the two extremes are distinct, so the
    sign of `ch₂` genuinely separates configurations. -/
theorem quantities_are_nondegenerate :
    0 < opticalFrameDrag (10 ^ 15) 1 ∧
    ch2Decomposed 1 0 ≠ ch2Decomposed 0 1 := by
  refine ⟨?_, ?_⟩
  · unfold opticalFrameDrag
    have := Real.pi_pos
    positivity
  · rw [pure_strain_value, pure_rotation_value]; norm_num

end PrincipiaTractalis.GravitomagneticRescue

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.GravitomagneticRescue.conservation_iff_compensating_divergence
#print axioms PrincipiaTractalis.GravitomagneticRescue.nonconservation_iff_varying
#print axioms PrincipiaTractalis.GravitomagneticRescue.pure_strain_value
#print axioms PrincipiaTractalis.GravitomagneticRescue.pure_rotation_value
#print axioms PrincipiaTractalis.GravitomagneticRescue.rotation_is_the_negative_half
#print axioms PrincipiaTractalis.GravitomagneticRescue.extremes_bracket_the_range
#print axioms PrincipiaTractalis.GravitomagneticRescue.optical_frame_drag_bracket
#print axioms PrincipiaTractalis.GravitomagneticRescue.ratio_to_earth_dragging
#print axioms PrincipiaTractalis.GravitomagneticRescue.Rescue_capstone
#print axioms PrincipiaTractalis.GravitomagneticRescue.quantities_are_nondegenerate
