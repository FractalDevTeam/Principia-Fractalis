/-
# Hutchinson Measure — Construction Framework

The Hutchinson invariant measure `μ_H` on `cantorSet` is the unique
Borel probability measure satisfying the IFS-invariance equation:

  `μ_H = (1/2)·(f_1)_* μ_H + (1/2)·(f_2)_* μ_H`

(where `f_1, f_2` are the two Cantor contractions).

Its existence and uniqueness follow from the Banach fixed-point
theorem applied to the **Hutchinson operator** `T : μ ↦ (1/2)·f_1_*μ +
(1/2)·f_2_*μ` on the space of Borel probability measures, with the
Wasserstein-1 / Prokhorov metric (Hutchinson 1981; Falconer 2003).

## What this file delivers

* **`hutchinsonOp`** — the Hutchinson operator on Borel measures.
* **Measurability + continuity** of the two contractions
  (`cantorContraction1`, `cantorContraction2`).
* **Equivalence with the fixed-point characterisation**:
  `IsHutchinsonInvariant μ ↔ μ = hutchinsonOp μ`.
* **Mass preservation**: the Hutchinson operator preserves total
  mass on any measure. In particular, it maps probability measures
  to probability measures.

## What this file does NOT deliver (yet)

* The full Banach fixed-point construction in
  `ProbabilityMeasure ℝ` (would require Prokhorov metric machinery
  not yet directly in mathlib).
* Concrete construction of `μ_H` via Bernoulli measures on
  `{0, 1}^ℕ` (requires the `cantorSet ↔ {0,1}^ℕ` homeomorphism).
* Hausdorff-measure construction at dimension `log 2 / log 3`.

Each is a separate substantial deliverable. The framework here gives
the operator and its basic preservation properties; the existence
proof is the next layer.

Stage L4+ — Hutchinson operator + fixed-point framework.
-/

import PF.Analytic.FractalDomain

namespace PrincipiaTractalis.Analytic

open Set MeasureTheory ENNReal

/-! ## Measurability of the Cantor contractions -/

/-- **`cantorContraction1` is Borel-measurable**. -/
theorem cantorContraction1_measurable : Measurable cantorContraction1 := by
  unfold cantorContraction1
  exact measurable_id.div_const 3

/-- **`cantorContraction2` is Borel-measurable**. -/
theorem cantorContraction2_measurable : Measurable cantorContraction2 := by
  unfold cantorContraction2
  exact (measurable_id.add_const 2).div_const 3

/-- **`cantorContraction1` is continuous** (hence Borel-measurable). -/
theorem cantorContraction1_continuous : Continuous cantorContraction1 := by
  unfold cantorContraction1
  exact continuous_id.div_const 3

/-- **`cantorContraction2` is continuous**. -/
theorem cantorContraction2_continuous : Continuous cantorContraction2 := by
  unfold cantorContraction2
  exact (continuous_id.add continuous_const).div_const 3

/-! ## The Hutchinson operator -/

/-- **The Hutchinson operator** on Borel measures of `ℝ`:

      `T(μ) := (1/2)·(f_1)_* μ + (1/2)·(f_2)_* μ`

    The IFS-induced contraction whose unique fixed point on the
    space of Borel probability measures is the Hutchinson invariant
    measure `μ_H` (Hutchinson 1981). The weights `(1/2, 1/2)` are
    uniform — the canonical choice corresponding to the
    self-similarity of `cantorSet` at the Hausdorff dimension
    `log 2 / log 3`. -/
noncomputable def hutchinsonOp (μ : MeasureTheory.Measure ℝ) :
    MeasureTheory.Measure ℝ :=
  (1/2 : ENNReal) • (MeasureTheory.Measure.map cantorContraction1 μ) +
  (1/2 : ENNReal) • (MeasureTheory.Measure.map cantorContraction2 μ)

/-! ## Fixed-point characterisation -/

/-- **`IsHutchinsonInvariant μ` is exactly being a fixed point of
    `hutchinsonOp`**. Definitional. -/
theorem IsHutchinsonInvariant_iff_fixed_point (μ : MeasureTheory.Measure ℝ) :
    IsHutchinsonInvariant μ ↔ μ = hutchinsonOp μ := by
  rfl

/-! ## Mass preservation -/

/-- **★ The Hutchinson operator preserves total mass ★**:

      `(T μ)(univ) = μ(univ)`

    Direct computation: each pushforward `(f_i)_* μ` has total mass
    `μ(univ)` (since `(f_i)_* μ (univ) = μ(f_i⁻¹(univ)) = μ(univ)`),
    and the weighted sum `(1/2 + 1/2) · μ(univ) = μ(univ)`.

    **Consequence**: `hutchinsonOp` maps probability measures
    (those with `μ(univ) = 1`) to probability measures. Combined
    with the (currently-not-formalised) Banach fixed-point theorem
    in the Prokhorov topology, this guarantees the existence of a
    unique fixed point on `ProbabilityMeasure ℝ` — the Hutchinson
    measure `μ_H`. -/
theorem hutchinsonOp_total (μ : MeasureTheory.Measure ℝ) :
    (hutchinsonOp μ) Set.univ = μ Set.univ := by
  unfold hutchinsonOp
  rw [Measure.add_apply]
  rw [Measure.smul_apply, Measure.smul_apply]
  rw [Measure.map_apply cantorContraction1_measurable MeasurableSet.univ]
  rw [Measure.map_apply cantorContraction2_measurable MeasurableSet.univ]
  simp
  rw [show (2 : ENNReal)⁻¹ * μ univ + 2⁻¹ * μ univ
        = (2⁻¹ + 2⁻¹) * μ univ from by ring]
  rw [show (2 : ENNReal)⁻¹ + 2⁻¹ = 1 from by
    rw [show (2 : ENNReal)⁻¹ + 2⁻¹ = 2 * 2⁻¹ from by ring]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  rw [one_mul]

/-- **Hutchinson operator preserves the probability-measure property**:
    if `μ(univ) = 1`, then `(T μ)(univ) = 1`. -/
theorem hutchinsonOp_probability (μ : MeasureTheory.Measure ℝ)
    (hμ : μ Set.univ = 1) :
    (hutchinsonOp μ) Set.univ = 1 := by
  rw [hutchinsonOp_total μ, hμ]

/-! ## Linearity in μ -/

/-- **Additivity**: `T(μ₁ + μ₂) = T μ₁ + T μ₂`.

    The Hutchinson operator distributes over measure addition. Direct
    consequence of `Measure.map_add` for each contraction + the
    additive structure of the smul-weighted sum. -/
theorem hutchinsonOp_add (μ₁ μ₂ : MeasureTheory.Measure ℝ) :
    hutchinsonOp (μ₁ + μ₂) = hutchinsonOp μ₁ + hutchinsonOp μ₂ := by
  unfold hutchinsonOp
  rw [Measure.map_add _ _ cantorContraction1_measurable]
  rw [Measure.map_add _ _ cantorContraction2_measurable]
  rw [smul_add, smul_add]
  ext s _
  simp [Measure.add_apply, Measure.smul_apply]
  ring

/-- **Scalar homogeneity**: `T(c · μ) = c · T μ` for any `c : ℝ≥0∞`.

    Consequence of `Measure.map_smul` applied to each contraction. -/
theorem hutchinsonOp_smul (c : ENNReal) (μ : MeasureTheory.Measure ℝ) :
    hutchinsonOp (c • μ) = c • hutchinsonOp μ := by
  unfold hutchinsonOp
  rw [Measure.map_smul]
  rw [Measure.map_smul]
  ext s _
  simp [Measure.add_apply, Measure.smul_apply]
  ring

/-! ## Documentation: existence and uniqueness of μ_H

The existence and uniqueness of the Hutchinson measure `μ_H` follow
from the Banach fixed-point theorem applied to `hutchinsonOp` on
the space `ProbabilityMeasure ℝ` (or more precisely, its restriction
to measures supported in `[0, 1]`).

**Hutchinson 1981 theorem**: Let `(f_1, ..., f_n)` be an IFS of
contractions on a complete metric space with contraction factors
`(r_1, ..., r_n)` and weights `(p_1, ..., p_n)` summing to 1. The
Hutchinson operator
  `T(μ) := Σ_i p_i · (f_i)_* μ`
is a contraction on the space of Borel probability measures with
the Wasserstein-1 metric, with contraction factor `max r_i`. Hence
`T` has a unique fixed point `μ_H` (the Hutchinson invariant
measure).

For our Cantor case:
* `f_1(x) = x/3`, `f_2(x) = (x+2)/3` — both with contraction factor 1/3.
* Weights `p_1 = p_2 = 1/2`.
* Max contraction factor 1/3 < 1, so `T` is a 1/3-contraction in
  Wasserstein-1.
* Unique fixed point `μ_H` exists on `ProbabilityMeasure [0, 1]`.

The fixed point is supported on `cantorSet` (the unique closed set
satisfying `cantorSet = f_1(cantorSet) ∪ f_2(cantorSet)`).

**Equivalent constructions** of `μ_H`:
1. Hausdorff measure at dimension `log 2 / log 3`, normalised to
   `cantorSet` with mass 1.
2. Bernoulli(1/2) measure on `{0, 1}^ℕ`, pushed through the standard
   `{0, 1}^ℕ ≃ cantorSet` homeomorphism.
3. Limit of `T^n(λ|_{[0,1]})` (n-th iterate of `T` on uniform
   Lebesgue on `[0,1]`) in the Prokhorov topology.

Each is a separate substantial formalisation. The current framework
provides the operator and its preservation properties; the existence
proof is the next layer of Route A. -/

end PrincipiaTractalis.Analytic
