/-
# Yang-Mills — SU(2) Haar is bi-invariant and inv-invariant

**Rio's step-0 unblock of the Fubini discharge, 2026-10-20.** Mathlib's
`IsHaarMeasure.isInvInvariant_of_regular` requires `[CommGroup G]`, which
excludes `SU(2)`. For compact groups, inversion-invariance is still
true but needs a separate argument. This file supplies it.

### The compactness route (no continuity needed)

The modular character `Δ : G →* ℝ≥0` satisfies
`map (· * g) μ = Δ(g) • μ`. For a left-Haar **probability** measure `μ`,
applying both sides to `Set.univ`:

* `(map (· * g) μ)(univ) = μ((·*g)⁻¹' univ) = μ(univ) = 1`,
* `(Δ(g) • μ)(univ) = Δ(g) · μ(univ) = Δ(g) · 1 = Δ(g)`.

Hence `Δ(g) = 1` for all `g : SU2`. This bypasses the TODO at
`MeasureTheory/Group/ModularCharacter.lean:21` ("show that the character
is continuous"): compactness + probability normalization are enough.

With `Δ = 1`, right-translation preserves `SU2_haar`
(`IsMulRightInvariant`). Combined with `IsMulLeftInvariant`, `SU2_haar.inv`
is also left-invariant (`inv.instIsMulLeftInvariant`). Uniqueness of
left-Haar measures (both inner-regular on a compact space) + probability
normalization pin `SU2_haar.inv = SU2_haar`, i.e. `IsInvInvariant SU2_haar`.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonSectorMeasureSplit_2026_10_20
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory MeasureTheory.Measure

noncomputable section

/-! ## §1 — `Δ(g) = 1` for every `g : SU2`. -/

/-- **Modular character of SU(2) is trivial.** For any `g : SU2`,
`modularCharacterFun g = 1`. Proof: apply
`map_right_mul_eq_modularCharacterFun_smul` to `Set.univ` and use that
`SU2_haar` is a probability measure. -/
theorem SU2_modularCharacterFun_eq_one (g : SU2) :
    modularCharacterFun g = (1 : NNReal) := by
  have h := map_right_mul_eq_modularCharacterFun_smul SU2_haar g
  -- Apply both measures to `Set.univ`.
  have h_univ : (map (· * g) SU2_haar) Set.univ
                = (modularCharacterFun g • SU2_haar) Set.univ := by rw [h]
  -- LHS = SU2_haar univ = 1 (preimage of univ is univ, SU2_haar is probability).
  have h_measurable : Measurable (fun x : SU2 => x * g) := measurable_mul_const g
  rw [Measure.map_apply h_measurable MeasurableSet.univ, Set.preimage_univ,
      measure_univ] at h_univ
  -- RHS = Δ(g) * 1 = ↑Δ(g).
  rw [Measure.coe_nnreal_smul_apply, measure_univ, mul_one] at h_univ
  -- h_univ : (1 : ℝ≥0∞) = ↑(Δ(g))
  exact_mod_cast h_univ.symm

/-! ## §2 — `SU2_haar` is right-invariant. -/

/-- **`SU2_haar` is right-invariant.** With trivial modular character,
right-translation preserves `SU2_haar`. -/
instance SU2_haar_isMulRightInvariant : IsMulRightInvariant SU2_haar := by
  constructor
  intro g
  have h := map_right_mul_eq_modularCharacterFun_smul SU2_haar g
  rw [SU2_modularCharacterFun_eq_one] at h
  rw [h]
  simp

/-! ## §3 — `SU2_haar.inv` is left-invariant and a Haar probability. -/

/-- `SU2_haar.inv` is left-invariant (via `inv.instIsMulLeftInvariant`
on the right-invariant `SU2_haar`). -/
instance SU2_haar_inv_isMulLeftInvariant : IsMulLeftInvariant SU2_haar.inv :=
  inferInstance

/-- `SU2_haar.inv` is a probability measure. -/
instance SU2_haar_inv_isProbabilityMeasure : IsProbabilityMeasure SU2_haar.inv := by
  constructor
  rw [inv_apply, Set.inv_univ, measure_univ]

/-- `SU2_haar.inv` is a finite measure. -/
instance SU2_haar_inv_isFiniteMeasure : IsFiniteMeasure SU2_haar.inv :=
  inferInstance

/-- `SU2_haar.inv` is finite on compacts (SU2 is compact, so this is
`IsFiniteMeasure`). -/
instance SU2_haar_inv_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts SU2_haar.inv :=
  inferInstance

/-! ## §4 — `IsInvInvariant SU2_haar` by uniqueness. -/

/-- **★ SU(2) HAAR IS INV-INVARIANT ★**

`SU2_haar.inv = SU2_haar`. Both are left-Haar probability measures, inner
regular on the compact space, so they coincide up to a scalar. The scalar
is 1 by probability normalization. -/
instance SU2_haar_isInvInvariant : IsInvInvariant SU2_haar := by
  constructor
  -- Both `SU2_haar.inv` and `SU2_haar` are left-invariant Haar probability
  -- measures on the compact SU2. By uniqueness: `SU2_haar.inv = c • SU2_haar`
  -- for some `c : ℝ≥0`. Applying to `univ` + both being probability measures
  -- pins `c = 1`.
  have h_uniq : SU2_haar.inv = haarScalarFactor SU2_haar.inv SU2_haar • SU2_haar :=
    isMulLeftInvariant_eq_smul_of_innerRegular SU2_haar.inv SU2_haar
  set c := haarScalarFactor SU2_haar.inv SU2_haar with hc_def
  have h_univ : SU2_haar.inv Set.univ = (c • SU2_haar) Set.univ := by rw [h_uniq]
  rw [Measure.coe_nnreal_smul_apply, measure_univ, measure_univ, mul_one]
    at h_univ
  have h_c_eq_one : c = (1 : NNReal) := by
    have : (c : ENNReal) = 1 := h_univ.symm
    exact_mod_cast this
  rw [h_uniq, h_c_eq_one]
  simp

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.SU2_modularCharacterFun_eq_one
#print axioms PF.YangMills.SU2_haar_isMulRightInvariant
#print axioms PF.YangMills.SU2_haar_inv_isMulLeftInvariant
#print axioms PF.YangMills.SU2_haar_inv_isProbabilityMeasure
#print axioms PF.YangMills.SU2_haar_isInvInvariant
