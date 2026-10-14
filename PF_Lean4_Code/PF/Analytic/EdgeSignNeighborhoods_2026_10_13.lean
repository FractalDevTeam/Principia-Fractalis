/-
# EdgeSignNeighborhoods_2026_10_13 — generic sign-preserving neighborhoods on the right edge

Mirrors `R1Neighborhood_2026_10_09` from the single point `t = 0` to generic
infrastructure. Where Legion's file proves a specific `∃δ` for R1 at zero, this
file factors the pattern:

For a continuous `f : ℝ → ℝ`, if `0 < f t₀` (or `f t₀ < 0`), there is a
positive-length closed interval around `t₀` on which the sign persists. Three
variants per sign: closed symmetric `[t₀ - δ, t₀ + δ]`, right-closed `[t₀, t₀ + δ]`,
left-closed `[t₀ - δ, t₀]`. Then specialise to the right-edge imaginary part
`edgeIm t := Im ξ(1+it)`, giving the dual of `R1Neighborhood`'s `continuous_edgeRe`.

### What it unblocks

Any future landing of a point certificate `0 < Im ξ(1 + it₀)` for
`t₀ ∈ {13, 29/2}` immediately yields positive-length coverage of R2 near that
endpoint. Any point certificate `Re ξ(1 + it₀) < 0` for `t₀ ∈ [29/2, 15]` yields R3
left-neighborhood coverage. The infrastructure is additive and does not change
any existing lemma.

### Honesty notes — unchanged discipline

* Generic lemmas are pure real analysis: zero numerical content.
* The specialisation for `edgeIm` adds continuity only; by itself it does NOT
  close R2 anywhere — closing a positive-length segment of R2 still needs an
  interior point certificate `0 < Im ξ(1 + it₀)`, which is numerics.
* `R1_right_neighborhood_of_zero` is logically equivalent to Legion's
  `R1Neighborhood20261009.R1_on_neighborhood`; it is restated here as a one-line
  specialisation of the generic lemma so the three segment endpoints share a
  common proof shape.
* No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. `autoImplicit`
  off. Additive — nothing existing is edited.

### Dependencies (olean verified 2026-10-13)
* `PF/Analytic/R1Neighborhood_2026_10_09.lean` — `edgeRe`, `continuous_edgeRe`,
  `R1_at_zero_local`, `continuous_edgeLine`.
* mathlib — `Metric.isOpen_iff`, `Continuous.isOpen_preimage`, `isOpen_Ioi`,
  `isOpen_Iio`, `Complex.continuous_im`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-13.
-/

import PF.Analytic.R1Neighborhood_2026_10_09

set_option autoImplicit false

namespace PrincipiaTractalis
namespace EdgeSignNeighborhoods20261013

open Complex
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.R1Neighborhood20261009

noncomputable section

/-! ## §0 — Generic sign-preserving neighborhoods for continuous `ℝ → ℝ`

Six lemmas, three per sign. The two one-sided variants reduce to the symmetric
one by sub-interval inclusion; the symmetric one is proved directly from
`Metric.isOpen_iff` on the super-level set. -/

/-- **Positive on a two-sided closed neighborhood.** -/
theorem pos_neighborhood_both {f : ℝ → ℝ} (hf : Continuous f) {t₀ : ℝ}
    (hpos : 0 < f t₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ), 0 < f t := by
  have hUopen : IsOpen (f ⁻¹' Set.Ioi (0 : ℝ)) :=
    hf.isOpen_preimage _ isOpen_Ioi
  have hmem : t₀ ∈ f ⁻¹' Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_preimage, Set.mem_Ioi]; exact hpos
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen t₀ hmem
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t ht
  rw [Set.mem_Icc] at ht
  obtain ⟨htL, htR⟩ := ht
  have htball : t ∈ Metric.ball t₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rcases le_or_gt t t₀ with hle | hgt
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith
    · rw [abs_of_pos (sub_pos.mpr hgt)]
      linarith
  have hpos' := hball htball
  simp only [Set.mem_preimage, Set.mem_Ioi] at hpos'
  exact hpos'

/-- **Positive on a right-closed neighborhood.** `[t₀, t₀ + δ]`. -/
theorem pos_neighborhood_right {f : ℝ → ℝ} (hf : Continuous f) {t₀ : ℝ}
    (hpos : 0 < f t₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc t₀ (t₀ + δ), 0 < f t := by
  obtain ⟨δ, hδ, hcover⟩ := pos_neighborhood_both hf hpos
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  rw [Set.mem_Icc] at ht
  exact hcover t (Set.mem_Icc.mpr ⟨by linarith, ht.2⟩)

/-- **Positive on a left-closed neighborhood.** `[t₀ - δ, t₀]`. -/
theorem pos_neighborhood_left {f : ℝ → ℝ} (hf : Continuous f) {t₀ : ℝ}
    (hpos : 0 < f t₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (t₀ - δ) t₀, 0 < f t := by
  obtain ⟨δ, hδ, hcover⟩ := pos_neighborhood_both hf hpos
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  rw [Set.mem_Icc] at ht
  exact hcover t (Set.mem_Icc.mpr ⟨ht.1, by linarith⟩)

/-- **Negative on a two-sided closed neighborhood.** -/
theorem neg_neighborhood_both {f : ℝ → ℝ} (hf : Continuous f) {t₀ : ℝ}
    (hneg : f t₀ < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ), f t < 0 := by
  have hUopen : IsOpen (f ⁻¹' Set.Iio (0 : ℝ)) :=
    hf.isOpen_preimage _ isOpen_Iio
  have hmem : t₀ ∈ f ⁻¹' Set.Iio (0 : ℝ) := by
    simp only [Set.mem_preimage, Set.mem_Iio]; exact hneg
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen t₀ hmem
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t ht
  rw [Set.mem_Icc] at ht
  obtain ⟨htL, htR⟩ := ht
  have htball : t ∈ Metric.ball t₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rcases le_or_gt t t₀ with hle | hgt
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith
    · rw [abs_of_pos (sub_pos.mpr hgt)]
      linarith
  have hneg' := hball htball
  simp only [Set.mem_preimage, Set.mem_Iio] at hneg'
  exact hneg'

/-- **Negative on a right-closed neighborhood.** `[t₀, t₀ + δ]`. -/
theorem neg_neighborhood_right {f : ℝ → ℝ} (hf : Continuous f) {t₀ : ℝ}
    (hneg : f t₀ < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc t₀ (t₀ + δ), f t < 0 := by
  obtain ⟨δ, hδ, hcover⟩ := neg_neighborhood_both hf hneg
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  rw [Set.mem_Icc] at ht
  exact hcover t (Set.mem_Icc.mpr ⟨by linarith, ht.2⟩)

/-- **Negative on a left-closed neighborhood.** `[t₀ - δ, t₀]`. -/
theorem neg_neighborhood_left {f : ℝ → ℝ} (hf : Continuous f) {t₀ : ℝ}
    (hneg : f t₀ < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (t₀ - δ) t₀, f t < 0 := by
  obtain ⟨δ, hδ, hcover⟩ := neg_neighborhood_both hf hneg
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  rw [Set.mem_Icc] at ht
  exact hcover t (Set.mem_Icc.mpr ⟨ht.1, by linarith⟩)

/-! ## §1 — Specialisation to the imaginary-part right-edge function

Dual of `R1Neighborhood_2026_10_09.continuous_edgeRe`: continuity of
`t ↦ Im ξ(1 + it)`, by the same argument with `Complex.continuous_im`. -/

/-- The imaginary-part right-edge function `t ↦ Im ξ(1 + it)`. -/
def edgeIm (t : ℝ) : ℝ := (riemannXiEntire (⟨1, t⟩ : ℂ)).im

/-- `t ↦ Im ξ(1 + it)` is continuous `ℝ → ℝ`. -/
theorem continuous_edgeIm : Continuous edgeIm := by
  unfold edgeIm
  exact Complex.continuous_im.comp
    (differentiable_riemannXiEntire.continuous.comp continuous_edgeLine)

/-! ## §2 — Convenience specialisations to R1 / R2 / R3

Each specialisation is a one-liner off the generic lemma: it is CONDITIONAL on a
point sign value for `ξ` on the right edge, and concludes positive-length
coverage near that point. R1/R3 fire immediately on the already-proved endpoints
`t = 0` and `t = 15`; R2's two endpoints `t = 13` and `t = 29/2` require numerical
certification that is not yet in-tree. -/

/-- **R1 right-neighborhood** from a point value. `∀ t ∈ [t₀, t₀+δ]`. -/
theorem R1_right_of (t₀ : ℝ) (h : 0 < (riemannXiEntire (⟨1, t₀⟩ : ℂ)).re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc t₀ (t₀ + δ),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re :=
  pos_neighborhood_right continuous_edgeRe h

/-- **R1 symmetric neighborhood** from an interior point value. -/
theorem R1_both_of (t₀ : ℝ) (h : 0 < (riemannXiEntire (⟨1, t₀⟩ : ℂ)).re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re :=
  pos_neighborhood_both continuous_edgeRe h

/-- **R2 symmetric neighborhood** from a point value. -/
theorem R2_both_of (t₀ : ℝ) (h : 0 < (riemannXiEntire (⟨1, t₀⟩ : ℂ)).im) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im :=
  pos_neighborhood_both continuous_edgeIm h

/-- **R2 right-neighborhood** (ready for `t₀ = 13` once point sign lands). -/
theorem R2_right_of (t₀ : ℝ) (h : 0 < (riemannXiEntire (⟨1, t₀⟩ : ℂ)).im) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc t₀ (t₀ + δ),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im :=
  pos_neighborhood_right continuous_edgeIm h

/-- **R2 left-neighborhood** (ready for `t₀ = 29/2` once point sign lands). -/
theorem R2_left_of (t₀ : ℝ) (h : 0 < (riemannXiEntire (⟨1, t₀⟩ : ℂ)).im) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (t₀ - δ) t₀,
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im :=
  pos_neighborhood_left continuous_edgeIm h

/-- **R3 left-neighborhood** (ready for `t₀ = 15` once point sign is wired). -/
theorem R3_left_of (t₀ : ℝ) (h : (riemannXiEntire (⟨1, t₀⟩ : ℂ)).re < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (t₀ - δ) t₀,
      (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0 :=
  neg_neighborhood_left continuous_edgeRe h

/-- **R3 symmetric neighborhood** from an interior point value. -/
theorem R3_both_of (t₀ : ℝ) (h : (riemannXiEntire (⟨1, t₀⟩ : ℂ)).re < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0 :=
  neg_neighborhood_both continuous_edgeRe h

/-! ## §3 — The one point sign already in this file's dependency closure

`R1_at_zero_local` gives `0 < Re ξ(1 + 0i)` (because `ξ(1) = 1/2`), transitively
from the r325 definition. Instantiating the R1 right-neighborhood specialisation
at that point gives a one-line restatement of Legion's
`R1Neighborhood20261009.R1_on_neighborhood`, confirming the infrastructure
reproduces the existing endpoint coverage.

The analogue for R3 (`t₀ = 15`) depends on `top15_re_lt_neg_1e4`
(`PF/Analytic/RiemannXiTopUnion.lean`), which is deliberately NOT imported here
to keep the file's build closure small (TopUnion's olean is currently stale at
HEAD). The `R3_left_of` lemma is ready to fire the moment any file that imports
TopUnion plus this one specialises it at `t₀ = 15`. -/

/-- **R1 right-neighborhood of `t = 0`** — the already-proved endpoint, restated
as a specialisation of the generic lemma. Logically equivalent to Legion's
`R1Neighborhood20261009.R1_on_neighborhood`; delivered here so the three segment
endpoints share a common proof shape. -/
theorem R1_right_neighborhood_of_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc (0 : ℝ) δ,
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  obtain ⟨δ, hδ, hcover⟩ := R1_right_of 0 R1_at_zero_local
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  simp only [zero_add] at hcover
  exact hcover t ht

end

/-! ## §Axiom check -/

#print axioms pos_neighborhood_both
#print axioms pos_neighborhood_right
#print axioms pos_neighborhood_left
#print axioms neg_neighborhood_both
#print axioms neg_neighborhood_right
#print axioms neg_neighborhood_left
#print axioms edgeIm
#print axioms continuous_edgeIm
#print axioms R1_right_of
#print axioms R1_both_of
#print axioms R2_both_of
#print axioms R2_right_of
#print axioms R2_left_of
#print axioms R3_left_of
#print axioms R3_both_of
#print axioms R1_right_neighborhood_of_zero

end EdgeSignNeighborhoods20261013
end PrincipiaTractalis
