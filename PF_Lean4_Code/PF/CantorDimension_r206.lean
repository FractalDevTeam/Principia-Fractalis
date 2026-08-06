/-
# PF.CantorDimension_r206 — the ternary Cantor set: dimension UPPER bound,
# plus the mass distribution principle in usable (constant-carrying) form

Consumes the Moran/Falconer engine of `PF.HausdorffIFS_r205` and applies it to
mathlib's `cantorSet`.

## What this file proves

* `dimH_cantorSet_le : dimH cantorSet ≤ ENNReal.ofReal (Real.logb 3 2)` — the
  covering (UPPER) bound, via the two globally-`(1/3)`-Lipschitz maps
  `x ↦ x/3`, `x ↦ (2+x)/3` and mathlib's `cantorSet_eq_union_halves`.

* `le_dimH_of_massDistribution` — the mass distribution principle (Frostman's
  lemma, easy direction) WITH a multiplicative constant.  mathlib's
  `MeasureTheory.Measure.le_hausdorffMeasure` has no constant, which makes it
  unusable in practice; this version absorbs the constant into a scaled measure.

* `le_dimH_of_holder_surj` — the abstract Hölder transfer lemma
  `r * dimH F ≤ dimH E` when `F ⊆ f '' E` and `f` is `r`-Hölder on `E`.

## HONESTY STATEMENT — read this before quoting anything from this file

1. **UPPER BOUND ONLY.**  This file proves `dimH cantorSet ≤ logb 3 2`.  It does
   **NOT** prove the matching lower bound.  Therefore the exact value
   `dimH cantorSet = logb 3 2` is **NOT** established here, and nothing below
   may be quoted as computing the dimension of the Cantor set.

2. **THE TWO CANDIDATE ROUTES FOR THE LOWER BOUND, NEITHER CARRIED OUT.**

   (a) *Self-similar (Cantor–Lebesgue) measure.*  Build the `Bernoulli(1/2)`
       product measure on `{0,1}^ℕ`, push it forward to `cantorSet` along the
       base-3 digit map, verify the Frostman estimate
       `μ(B(x,ρ)) ≤ C · ρ^(logb 3 2)`, and feed it to
       `le_dimH_of_massDistribution` below.  mathlib has the product-measure
       machinery (`Mathlib/Probability/ProductMeasure.lean`) but the pushforward,
       the digit map, and the Frostman estimate are all missing.  NOT done here.

   (b) *Cantor function + Hölder transfer.*  The Cantor staircase
       `c : cantorSet → [0,1]` is surjective and Hölder with exponent
       `logb 3 2`; combined with `dimH (Icc 0 1) = 1` and
       `le_dimH_of_holder_surj` below this gives the lower bound.  The Cantor
       function is **not in mathlib** and constructing it is a stone of its own.
       NOT done here.  Only the *abstract* transfer lemma is supplied.

3. `le_dimH_of_massDistribution` is a general bridge: it is stated for an
   arbitrary Borel EMetric space and makes no reference to the Cantor set.  It
   is the intended entry point for all future Hausdorff-dimension LOWER bounds
   in this project.

4. No `sorry`, no `native_decide`, no project axioms.  All results reduce to
   `[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic
import PF.HausdorffIFS_r205

open scoped NNReal ENNReal Topology
open Set MeasureTheory

namespace PrincipiaTractalis.CantorDimension

/-! ## §1 — the two Cantor branches as a global IFS on `ℝ` -/

/-- The ternary Cantor IFS `φ 0 x = x / 3`, `φ 1 x = (2 + x) / 3`, packaged as a
single formula `φ j x = (2 * j + x) / 3` indexed by `j : Fin 2`. -/
noncomputable def cantorIFS (j : Fin 2) : ℝ → ℝ := fun x => (2 * ((j : ℕ) : ℝ) + x) / 3

@[simp] theorem cantorIFS_zero (x : ℝ) : cantorIFS 0 x = x / 3 := by
  simp [cantorIFS]

@[simp] theorem cantorIFS_one (x : ℝ) : cantorIFS 1 x = (2 + x) / 3 := by
  simp [cantorIFS]

/-- Both branches are GLOBALLY `1/3`-Lipschitz on `ℝ` (they are affine). -/
theorem cantorIFS_lipschitz (j : Fin 2) : LipschitzWith (1 / 3 : ℝ≥0) (cantorIFS j) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hcoe : ((1 / 3 : ℝ≥0) : ℝ) = 1 / 3 := by
    push_cast
    norm_num
  have hxy : cantorIFS j x - cantorIFS j y = (x - y) / 3 := by
    simp only [cantorIFS]
    ring
  rw [Real.dist_eq, Real.dist_eq, hxy, hcoe, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  exact le_of_eq (by ring)

/-- mathlib's `cantorSet_eq_union_halves`, repackaged as the r205 self-covering
hypothesis `E ⊆ ⋃ j, φ j '' E`. -/
theorem cantorSet_selfCover : cantorSet ⊆ ⋃ j : Fin 2, cantorIFS j '' cantorSet := by
  intro x hx
  rw [cantorSet_eq_union_halves] at hx
  rcases hx with h | h
  · obtain ⟨y, hy, rfl⟩ := h
    exact Set.mem_iUnion.2 ⟨0, ⟨y, hy, by simp⟩⟩
  · obtain ⟨y, hy, rfl⟩ := h
    exact Set.mem_iUnion.2 ⟨1, ⟨y, hy, by simp⟩⟩

/-- The Cantor set is bounded, so its extended diameter is finite. -/
theorem cantorSet_ediam_ne_top : EMetric.diam cantorSet ≠ ⊤ := by
  have h : EMetric.diam cantorSet ≤ EMetric.diam (Set.Icc (0 : ℝ) 1) :=
    EMetric.diam_mono cantorSet_subset_unitInterval
  rw [Real.ediam_Icc] at h
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-! ## §2 — the Moran exponent `log 2 / log 3` -/

theorem logb_three_two_nonneg : (0 : ℝ) ≤ Real.logb 3 2 :=
  Real.logb_nonneg (by norm_num) (by norm_num)

/-- The Moran exponent `d = logb 3 2`, as an `ℝ≥0`. -/
noncomputable def cantorDim : ℝ≥0 := (Real.logb 3 2).toNNReal

@[simp] theorem cantorDim_coe : ((cantorDim : ℝ≥0) : ℝ) = Real.logb 3 2 :=
  Real.coe_toNNReal _ logb_three_two_nonneg

theorem cantorDim_coe_ennreal : (cantorDim : ℝ≥0∞) = ENNReal.ofReal (Real.logb 3 2) := rfl

/-- **The key arithmetic.**  `(1/3)^(logb 3 2) = 1/2`, because `3^(logb 3 2) = 2`. -/
theorem rpow_one_third_logb : ((1 : ℝ) / 3) ^ (Real.logb 3 2) = 1 / 2 := by
  rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem nnrpow_one_third_logb :
    (((1 / 3 : ℝ≥0)) ^ (Real.logb 3 2) : ℝ≥0) = (1 / 2 : ℝ≥0) := by
  have h : ((((1 / 3 : ℝ≥0)) ^ (Real.logb 3 2) : ℝ≥0) : ℝ) = ((1 / 2 : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_rpow]
    push_cast
    exact rpow_one_third_logb
  exact_mod_cast h

/-- The Moran sum condition for the Cantor IFS: `2 · (1/3)^d = 1` at `d = logb 3 2`. -/
theorem sum_cantor_rpow_le_one :
    (∑ _j : Fin 2, ((1 / 3 : ℝ≥0) : ℝ≥0∞) ^ ((cantorDim : ℝ≥0) : ℝ)) ≤ 1 := by
  have key : ((1 / 3 : ℝ≥0) : ℝ≥0∞) ^ ((cantorDim : ℝ≥0) : ℝ)
      = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [cantorDim_coe, ← ENNReal.coe_rpow_of_nonneg _ logb_three_two_nonneg,
      nnrpow_one_third_logb]
  rw [Fin.sum_univ_two, key, ← ENNReal.coe_add]
  norm_num

/-! ## §3 — DELIVERABLE A: the upper bound -/

/-- **Upper bound for the Hausdorff dimension of mathlib's ternary Cantor set.**

`dimH cantorSet ≤ logb 3 2`.

This is a COVERING bound only.  The matching lower bound is NOT proved in this
file, so this does not establish `dimH cantorSet = logb 3 2`.  See the honesty
statement at the top of the file. -/
theorem dimH_cantorSet_le : dimH cantorSet ≤ ENNReal.ofReal (Real.logb 3 2) := by
  have h := PrincipiaTractalis.HausdorffIFS.dimH_le_of_selfCover_global
      (φ := cantorIFS) (E := cantorSet) (L := fun _ : Fin 2 => (1 / 3 : ℝ≥0))
      (d := cantorDim)
      cantorSet_ediam_ne_top cantorSet_selfCover cantorIFS_lipschitz
      (fun _ => by norm_num) sum_cantor_rpow_le_one
  rwa [cantorDim_coe_ennreal] at h

/-- Same statement with the exponent as an `ℝ≥0`. -/
theorem dimH_cantorSet_le' : dimH cantorSet ≤ (cantorDim : ℝ≥0∞) :=
  dimH_cantorSet_le

/-! ## §4 — DELIVERABLE B: the mass distribution principle, with a constant -/

/-- **Mass distribution principle (Frostman, easy direction), usable form.**

If a measure `μ` gives `E` positive mass and satisfies the Frostman-type
estimate `μ s ≤ C · diam(s)^d` for all `s` of diameter at most `ε`, then
`d ≤ dimH E`.

mathlib's `MeasureTheory.Measure.le_hausdorffMeasure` is the `C = 1` case; that
form is essentially never applicable.  Here the constant is absorbed by applying
mathlib's version to the scaled measure `C⁻¹ • μ`.

Note the hypothesis `hmass` is required for ALL sets `s` of small diameter, not
just balls; this is the form that comes out of a covering argument, and it is
what mathlib's `le_hausdorffMeasure` consumes. -/
theorem le_dimH_of_massDistribution {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {E : Set X} {d : ℝ≥0} (μ : Measure X) (hpos : μ E ≠ 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hmass : ∀ s : Set X, EMetric.diam s ≤ ε → μ s ≤ C * EMetric.diam s ^ (d : ℝ)) :
    (d : ℝ≥0∞) ≤ dimH E := by
  -- the rescaled measure `C⁻¹ • μ` satisfies the constant-free hypothesis
  have hle : (C⁻¹ • μ) ≤ μH[(d : ℝ)] := by
    refine MeasureTheory.Measure.le_hausdorffMeasure (d : ℝ) (C⁻¹ • μ) ε hε ?_
    intro s hs
    rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
    calc C⁻¹ * μ s ≤ C⁻¹ * (C * EMetric.diam s ^ (d : ℝ)) := by
          exact mul_le_mul_left' (hmass s hs) _
      _ = EMetric.diam s ^ (d : ℝ) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCtop, one_mul]
  -- evaluate at `E`
  have hEval : C⁻¹ * μ E ≤ μH[(d : ℝ)] E := by
    have h := (MeasureTheory.Measure.le_iff'.1 hle) E
    rwa [MeasureTheory.Measure.smul_apply, smul_eq_mul] at h
  have hne : C⁻¹ * μ E ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.2 hCtop) hpos
  exact le_dimH_of_hausdorffMeasure_ne_zero (fun h => hne (le_antisymm (h ▸ hEval) (zero_le _)))

/-! ## §5 — DELIVERABLE C: the abstract Hölder transfer lemma

This is *scaffolding* for a future lower-bound stone.  The Cantor function is
NOT constructed here (it is not in mathlib), so this lemma is not applied to the
Cantor set anywhere in this file. -/

/-- **Hölder transfer for dimension lower bounds.**

If `f` is `r`-Hölder on `E` and `F` is covered by `f '' E`, then
`r · dimH F ≤ dimH E`.

Intended use: with `F = Icc 0 1` (so `dimH F = 1`), `E = cantorSet`, `f` the
Cantor staircase and `r = logb 3 2`, this would give the missing lower bound
`logb 3 2 ≤ dimH cantorSet`.  The Cantor staircase is not available, so that
application is NOT made here. -/
theorem le_dimH_of_holder_surj {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    {E : Set X} {F : Set Y} {f : X → Y} {C r : ℝ≥0} (hr : 0 < r)
    (hf : HolderOnWith C r f E) (hsurj : F ⊆ f '' E) :
    (r : ℝ≥0∞) * dimH F ≤ dimH E := by
  have hr0 : ((r : ℝ≥0∞)) ≠ 0 := by
    simpa using hr.ne'
  have hchain : dimH F ≤ dimH E / (r : ℝ≥0∞) :=
    (dimH_mono hsurj).trans (hf.dimH_image_le hr)
  calc (r : ℝ≥0∞) * dimH F ≤ (r : ℝ≥0∞) * (dimH E / (r : ℝ≥0∞)) :=
        mul_le_mul_left' hchain _
    _ = dimH E := by
        rw [div_eq_mul_inv, mul_comm (dimH E) ((r : ℝ≥0∞))⁻¹, ← mul_assoc,
          ENNReal.mul_inv_cancel hr0 ENNReal.coe_ne_top, one_mul]

/-! ## Axiom audit -/

#print axioms cantorIFS_lipschitz
#print axioms cantorSet_selfCover
#print axioms cantorSet_ediam_ne_top
#print axioms rpow_one_third_logb
#print axioms sum_cantor_rpow_le_one
#print axioms dimH_cantorSet_le
#print axioms le_dimH_of_massDistribution
#print axioms le_dimH_of_holder_surj

end PrincipiaTractalis.CantorDimension
