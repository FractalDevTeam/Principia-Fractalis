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
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Dirac

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

/-! ## Iteration -/

/-- **The n-th iterate of T preserves total mass**: `(T^n μ)(univ) = μ(univ)`.

    By induction: each step preserves mass via `hutchinsonOp_total`. -/
theorem hutchinsonOp_iter_total (μ : MeasureTheory.Measure ℝ) (n : ℕ) :
    (hutchinsonOp^[n] μ) Set.univ = μ Set.univ := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [hutchinsonOp_total]
    exact ih

/-- **Iteration preserves probability measures**: if `μ(univ) = 1`,
    then `(T^n μ)(univ) = 1` for all `n`. -/
theorem hutchinsonOp_iter_probability (μ : MeasureTheory.Measure ℝ) (n : ℕ)
    (hμ : μ Set.univ = 1) :
    (hutchinsonOp^[n] μ) Set.univ = 1 := by
  rw [hutchinsonOp_iter_total, hμ]

/-- **Iteration additivity**: `T^(n+m) = T^n ∘ T^m`. -/
theorem hutchinsonOp_iter_add (μ : MeasureTheory.Measure ℝ) (n m : ℕ) :
    hutchinsonOp^[n + m] μ = hutchinsonOp^[n] (hutchinsonOp^[m] μ) := by
  rw [Function.iterate_add_apply]

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

/-! ## Seed measure for Hutchinson iteration -/

/-- **Seed measure for the Hutchinson iteration**: Lebesgue restricted
    to `[0, 1]`.

      `cantorSeed := volume.restrict ([0, 1])`

    The canonical initial probability measure for the iteration
    `μ_n := T^n cantorSeed`. As `n → ∞`, the sequence concentrates
    on `cantorSet` and converges (in Wasserstein-1) to the Hutchinson
    invariant measure `μ_H`. -/
noncomputable def cantorSeed : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

/-- **`cantorSeed` is a probability measure**: total mass 1. -/
theorem cantorSeed_total : cantorSeed Set.univ = 1 := by
  unfold cantorSeed
  rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
  simp

/-- **Hutchinson iteration starting from `cantorSeed` stays on
    probability measures**:

      `(T^n cantorSeed)(univ) = 1`  for all `n`. -/
theorem hutchinsonOp_iter_cantorSeed_total (n : ℕ) :
    (hutchinsonOp^[n] cantorSeed) Set.univ = 1 := by
  rw [hutchinsonOp_iter_total, cantorSeed_total]

/-! ## Pre-Cantor-set recursion (using framework contraction names) -/

/-- **Pre-Cantor-set IFS recursion** using framework's
    `cantorContraction1, 2` names:

      `preCantorSet (n+1) = f₁(preCantorSet n) ∪ f₂(preCantorSet n)`

    Equivalent to mathlib's `preCantorSet_succ` but in framework
    naming. This is the level-by-level construction of `cantorSet`
    from `[0,1]`: each level applies both IFS contractions to the
    previous level. -/
theorem preCantorSet_succ_frameworkContractions (n : ℕ) :
    preCantorSet (n + 1) =
    (cantorContraction1 '' preCantorSet n) ∪
    (cantorContraction2 '' preCantorSet n) := by
  rw [preCantorSet_succ]
  rw [cantorContraction1_eq, cantorContraction2_eq]

/-! ## ★ Discrete n-cell approximations ★ -/

/-- **Discrete n-cell Hutchinson approximation**:

      `cantorDiscMeasure n := T^n (δ_{1/2})`

    The `n`-fold iterate of the Hutchinson operator applied to a
    single Dirac measure at the center of `[0, 1]`. After `n` steps,
    the support is a set of `2^n` points, each carrying mass `1/2^n`
    — exactly the cell midpoints of `preCantorSet n` (when iterated
    from `[0,1]`'s midpoint).

    This is the **finite-rank, computable approximation** to the
    Hutchinson measure `μ_H`. Each level adds detail (more cells,
    smaller Dirac masses), and the sequence converges weakly to `μ_H`
    as `n → ∞`. -/
noncomputable def cantorDiscMeasure (n : ℕ) : MeasureTheory.Measure ℝ :=
  hutchinsonOp^[n] (MeasureTheory.Measure.dirac (1/2 : ℝ))

/-- **Base case**: at level 0, the measure is a single Dirac at the
    center of `[0, 1]`. -/
theorem cantorDiscMeasure_zero :
    cantorDiscMeasure 0 = MeasureTheory.Measure.dirac (1/2 : ℝ) := by
  unfold cantorDiscMeasure
  simp

/-- **Recursive step**:

      `cantorDiscMeasure (n+1) = T (cantorDiscMeasure n)`

    Each level applies one more Hutchinson step, doubling the cell
    count and halving the per-cell mass. -/
theorem cantorDiscMeasure_succ (n : ℕ) :
    cantorDiscMeasure (n + 1) = hutchinsonOp (cantorDiscMeasure n) := by
  unfold cantorDiscMeasure
  rw [Function.iterate_succ_apply']

/-- **Probability measure**: at every level, `cantorDiscMeasure n`
    is a probability measure (total mass 1). -/
theorem cantorDiscMeasure_total (n : ℕ) :
    cantorDiscMeasure n Set.univ = 1 := by
  unfold cantorDiscMeasure
  rw [hutchinsonOp_iter_total]
  rw [MeasureTheory.Measure.dirac_apply']
  · simp
  · exact MeasurableSet.univ

/-- **Level 1 explicit form**:

      `cantorDiscMeasure 1 = (1/2)·δ_{1/6} + (1/2)·δ_{5/6}`

    The two Dirac points `1/6, 5/6` are exactly the midpoints of the
    level-1 cells `[0, 1/3]` and `[2/3, 1]`. -/
theorem cantorDiscMeasure_one :
    cantorDiscMeasure 1 =
    (1/2 : ENNReal) • MeasureTheory.Measure.dirac (1/6 : ℝ) +
    (1/2 : ENNReal) • MeasureTheory.Measure.dirac (5/6 : ℝ) := by
  rw [cantorDiscMeasure_succ, cantorDiscMeasure_zero]
  unfold hutchinsonOp
  rw [MeasureTheory.Measure.map_dirac cantorContraction1_measurable]
  rw [MeasureTheory.Measure.map_dirac cantorContraction2_measurable]
  unfold cantorContraction1 cantorContraction2
  norm_num

/-! ## Discrete operator action -/

/-- **Discrete operator action**:

      `(H_P^disc[μ] f)(x) := ∫ y, V_P(x, y) · f(y) dμ(y)`

    The operator action against a measure `μ` without restricting to
    `cantorSet`. For `μ = cantorDiscMeasure n`, this is a FINITE SUM
    over the level-n cell midpoints.

    Distinct from `H_P_at_cantor` (which restricts to `cantorSet`).
    `H_P_at_disc` is the natural operator-action for discrete
    approximations, where the support of `μ` is a finite point set
    (Dirac comb). -/
noncomputable def H_P_at_disc (α a : ℝ) (μ : MeasureTheory.Measure ℝ)
    (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, cantorKernel α a x y * f y ∂μ

/-- **Dirac action**: for `μ = δ_z`,

      `(H_P^disc[δ_z] f)(x) = V_P(x, z) · f(z)`.

    Direct consequence of `MeasureTheory.integral_dirac`. -/
theorem H_P_at_disc_dirac (α a : ℝ) (z : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    H_P_at_disc α a (MeasureTheory.Measure.dirac z) f x =
    cantorKernel α a x z * f z := by
  unfold H_P_at_disc
  exact MeasureTheory.integral_dirac _ z

/-- **Level-0 explicit action**:

      `(H_P^disc[cantorDiscMeasure 0] f)(x) = V_P(x, 1/2) · f(1/2)`. -/
theorem H_P_at_disc_cantorDiscMeasure_zero (α a : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    H_P_at_disc α a (cantorDiscMeasure 0) f x =
    cantorKernel α a x (1/2) * f (1/2) := by
  rw [cantorDiscMeasure_zero]
  exact H_P_at_disc_dirac α a (1/2) f x

/-! ## H_P^disc additivity in μ -/

/-- **`H_P^disc` is additive in μ** (with integrability hypotheses):

      `H_P^disc[μ₁ + μ₂] f x = H_P^disc[μ₁] f x + H_P^disc[μ₂] f x`

    Required for unfolding `cantorDiscMeasure` iterates into explicit
    sums of Dirac contributions. -/
theorem H_P_at_disc_add (α a : ℝ) (μ₁ μ₂ : MeasureTheory.Measure ℝ)
    (f : ℝ → ℝ) (x : ℝ)
    (h₁ : MeasureTheory.Integrable (fun y => cantorKernel α a x y * f y) μ₁)
    (h₂ : MeasureTheory.Integrable (fun y => cantorKernel α a x y * f y) μ₂) :
    H_P_at_disc α a (μ₁ + μ₂) f x =
    H_P_at_disc α a μ₁ f x + H_P_at_disc α a μ₂ f x := by
  unfold H_P_at_disc
  exact MeasureTheory.integral_add_measure h₁ h₂

/-- **`H_P^disc` scalar in μ**: `H_P^disc[c • μ] f x = c · H_P^disc[μ] f x`. -/
theorem H_P_at_disc_smul_measure (α a : ℝ) (c : ENNReal)
    (μ : MeasureTheory.Measure ℝ) (f : ℝ → ℝ) (x : ℝ) :
    H_P_at_disc α a (c • μ) f x = c.toReal • H_P_at_disc α a μ f x := by
  unfold H_P_at_disc
  rw [MeasureTheory.integral_smul_measure]

/-- **Scaled Dirac evaluation**:

      `H_P^disc[c • δ_z] f x = c.toReal · V_P(x, z) · f(z)`

    The atomic building block for any finite Dirac-sum measure.
    Combining with `H_P_at_disc_add` gives the explicit form for
    `H_P^disc` against any discrete probability measure
    `Σ p_i · δ_{z_i}`. -/
theorem H_P_at_disc_smul_dirac (α a : ℝ) (c : ENNReal) (z : ℝ)
    (f : ℝ → ℝ) (x : ℝ) :
    H_P_at_disc α a (c • MeasureTheory.Measure.dirac z) f x =
    c.toReal * (cantorKernel α a x z * f z) := by
  rw [H_P_at_disc_smul_measure, H_P_at_disc_dirac, smul_eq_mul]

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
