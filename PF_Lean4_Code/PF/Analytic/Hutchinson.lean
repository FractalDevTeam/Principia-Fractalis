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

/-- **Level 2 explicit form**:

      `cantorDiscMeasure 2 = (1/4)·δ_{1/18} + (1/4)·δ_{5/18}
                            + (1/4)·δ_{13/18} + (1/4)·δ_{17/18}`

    The four Dirac points are exactly the midpoints of the four
    level-2 Cantor cells (`[0, 1/9]`, `[2/9, 1/3]`, `[2/3, 7/9]`,
    `[8/9, 1]`). Derived via one application of `hutchinsonOp_dirac`
    to each of the two level-1 Diracs. -/
theorem cantorDiscMeasure_two :
    cantorDiscMeasure 2 =
    (1/4 : ENNReal) • MeasureTheory.Measure.dirac (1/18 : ℝ) +
    (1/4 : ENNReal) • MeasureTheory.Measure.dirac (13/18 : ℝ) +
    ((1/4 : ENNReal) • MeasureTheory.Measure.dirac (5/18 : ℝ) +
     (1/4 : ENNReal) • MeasureTheory.Measure.dirac (17/18 : ℝ)) := by
  have : cantorDiscMeasure 2 = hutchinsonOp (cantorDiscMeasure 1) :=
    cantorDiscMeasure_succ 1
  rw [this, cantorDiscMeasure_one]
  -- T((1/2)·δ_{1/6} + (1/2)·δ_{5/6}) splits into 4 pieces
  unfold hutchinsonOp
  rw [MeasureTheory.Measure.map_add _ _ cantorContraction1_measurable,
      MeasureTheory.Measure.map_add _ _ cantorContraction2_measurable]
  rw [MeasureTheory.Measure.map_smul,
      MeasureTheory.Measure.map_smul,
      MeasureTheory.Measure.map_smul,
      MeasureTheory.Measure.map_smul]
  rw [MeasureTheory.Measure.map_dirac cantorContraction1_measurable,
      MeasureTheory.Measure.map_dirac cantorContraction1_measurable,
      MeasureTheory.Measure.map_dirac cantorContraction2_measurable,
      MeasureTheory.Measure.map_dirac cantorContraction2_measurable]
  -- f₁(1/6) = 1/18, f₁(5/6) = 5/18, f₂(1/6) = 13/18, f₂(5/6) = 17/18
  have h1 : cantorContraction1 (1/6 : ℝ) = 1/18 := by
    unfold cantorContraction1; norm_num
  have h2 : cantorContraction1 (5/6 : ℝ) = 5/18 := by
    unfold cantorContraction1; norm_num
  have h3 : cantorContraction2 (1/6 : ℝ) = 13/18 := by
    unfold cantorContraction2; norm_num
  have h4 : cantorContraction2 (5/6 : ℝ) = 17/18 := by
    unfold cantorContraction2; norm_num
  rw [h1, h2, h3, h4]
  -- Now distribute the outer (1/2) and combine smuls into (1/4)
  rw [smul_add, smul_add]
  rw [smul_smul, smul_smul, smul_smul, smul_smul]
  have hq : (1/2 : ENNReal) * (1/2 : ENNReal) = 1/4 := by
    rw [show (1/2 : ENNReal) = 2⁻¹ from one_div 2,
        show (1/4 : ENNReal) = 4⁻¹ from one_div 4]
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  rw [hq]
  abel

/-! ## ★ Integral against cantorDiscMeasure at low levels ★ -/

/-- **Level-0 integral**: `∫ f d(cantorDiscMeasure 0) = f(1/2)`. -/
theorem integral_cantorDiscMeasure_zero (f : ℝ → ℝ) :
    ∫ x, f x ∂(cantorDiscMeasure 0) = f (1/2) := by
  rw [cantorDiscMeasure_zero]
  exact MeasureTheory.integral_dirac _ _

/-- **Level-1 integral**: `∫ f d(cantorDiscMeasure 1) = (1/2)·(f(1/6) + f(5/6))`.

    Direct from the explicit level-1 form
    `cantorDiscMeasure 1 = (1/2)·(δ_{1/6} + δ_{5/6})`. -/
theorem integral_cantorDiscMeasure_one (f : ℝ → ℝ) :
    ∫ x, f x ∂(cantorDiscMeasure 1) = (1/2) * (f (1/6) + f (5/6)) := by
  rw [cantorDiscMeasure_one]
  rw [MeasureTheory.integral_add_measure]
  · rw [MeasureTheory.integral_smul_measure,
        MeasureTheory.integral_smul_measure,
        MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
    simp [ENNReal.toReal_ofNat]
    ring
  · refine MeasureTheory.Integrable.smul_measure ?_ (by simp)
    exact MeasureTheory.integrable_dirac (by simp [enorm_eq_nnnorm])
  · refine MeasureTheory.Integrable.smul_measure ?_ (by simp)
    exact MeasureTheory.integrable_dirac (by simp [enorm_eq_nnnorm])

/-- **Level-2 integral**:

      `∫ f d(cantorDiscMeasure 2) = (1/4)·(f(1/18) + f(5/18) + f(13/18) + f(17/18))`

    Direct from the explicit level-2 form
    `cantorDiscMeasure 2 = (1/4)·(δ_{1/18} + δ_{13/18} + δ_{5/18} + δ_{17/18})`. -/
theorem integral_cantorDiscMeasure_two (f : ℝ → ℝ) :
    ∫ x, f x ∂(cantorDiscMeasure 2) =
    (1/4) * (f (1/18) + f (13/18) + f (5/18) + f (17/18)) := by
  rw [cantorDiscMeasure_two]
  -- Reuse the integrability helper used in MatrixEntry.lean
  have hint : ∀ z : ℝ, MeasureTheory.Integrable (f : ℝ → ℝ)
      ((1/4 : ENNReal) • MeasureTheory.Measure.dirac z) := by
    intro z
    refine MeasureTheory.Integrable.smul_measure ?_ (by simp)
    exact MeasureTheory.integrable_dirac (by simp [enorm_eq_nnnorm])
  rw [MeasureTheory.integral_add_measure
        (MeasureTheory.Integrable.add_measure (hint _) (hint _))
        (MeasureTheory.Integrable.add_measure (hint _) (hint _))]
  rw [MeasureTheory.integral_add_measure (hint _) (hint _),
      MeasureTheory.integral_add_measure (hint _) (hint _)]
  rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure,
      MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_dirac, MeasureTheory.integral_dirac,
      MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
  simp [ENNReal.toReal_ofNat]
  ring

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

/-- **★ H_P^disc is self-adjoint ★** (Lebesgue integration form):

      `∫ (H_P^disc[μ] f)(x) · g(x) dμ(x) = ∫ f(x) · (H_P^disc[μ] g)(x) dμ(x)`

    The bilinear form `(f, g) ↦ ∫ (H_P^disc f) · g dμ` is **symmetric**
    in `f` and `g`. This is the operator-theoretic statement of
    self-adjointness for the kernel operator H_P^disc.

    Proof: pull `g(x)` into the inner integral (linearity), swap
    integration order via Fubini (`integral_integral_swap`), use kernel
    symmetry `V_P(x, y) = V_P(y, x)` (`cantorKernel_symm`), pull
    `f(y)` out, and recognise the inner integral as `H_P^disc g`.

    **Hypothesis**: the bilinear integrand `V_P(x, y) · f(y) · g(x)` is
    integrable on the product measure `μ × μ`. For DISCRETE measures
    (finite sums of Diracs, including `cantorDiscMeasure n`), this is
    automatic via the bounded kernel and finite support. -/
theorem H_P_at_disc_self_adjoint (α a : ℝ) (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.SFinite μ]
    (f g : ℝ → ℝ)
    (h_int : MeasureTheory.Integrable
      (Function.uncurry (fun x y => cantorKernel α a x y * f y * g x))
      (μ.prod μ)) :
    ∫ x, H_P_at_disc α a μ f x * g x ∂μ =
    ∫ x, f x * H_P_at_disc α a μ g x ∂μ := by
  unfold H_P_at_disc
  -- Pull g(x) into the inner integral
  have hL : ∀ x, (∫ y, cantorKernel α a x y * f y ∂μ) * g x =
                  ∫ y, cantorKernel α a x y * f y * g x ∂μ := by
    intro x
    rw [← MeasureTheory.integral_mul_const]
  simp_rw [hL]
  -- Fubini: swap integration order
  rw [MeasureTheory.integral_integral_swap h_int]
  -- Pull f(y) out + apply kernel symmetry, both inner integrands
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only
  -- Goal: ∫ x, V_P(x, y) · f(y) · g(x) dμ
  --     = f(y) · ∫ y', V_P(y, y') · g(y') dμ
  rw [show (fun x => cantorKernel α a x y * f y * g x) =
          (fun x => f y * (cantorKernel α a x y * g x)) from by
        funext x; ring]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only
  rw [cantorKernel_symm]

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

/-- **★ Sup-norm bound at level 0 ★** (`a > 1`):

    For any test function `f` with `|f(1/2)| ≤ M`,

      `|H_P^disc[cantorDiscMeasure 0] f (x)| ≤ M · a/(a − 1)`

    Direct from the level-0 explicit action
    `(H_P^disc f)(x) = V_P(x, 1/2) · f(1/2)` and the uniform kernel
    bound `|V_P| ≤ a/(a − 1)`. -/
theorem abs_H_P_at_disc_level0_le {α a : ℝ} (ha : 1 < a)
    (M : ℝ) (f : ℝ → ℝ) (hf : |f (1/2)| ≤ M) (x : ℝ) :
    |H_P_at_disc α a (cantorDiscMeasure 0) f x| ≤ M * (a / (a - 1)) := by
  rw [H_P_at_disc_cantorDiscMeasure_zero]
  rw [abs_mul]
  have h1 : |cantorKernel α a x (1/2)| ≤ a/(a-1) := by
    unfold cantorKernel
    exact PrincipiaTractalis.IntegralKernel.abs_fractalKernelReal_le α ha _
  calc |cantorKernel α a x (1/2)| * |f (1/2)|
      ≤ (a/(a-1)) * M :=
        mul_le_mul h1 hf (abs_nonneg _)
          (div_nonneg (by linarith) (by linarith))
    _ = M * (a/(a-1)) := by ring

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

/-- **`T` applied to a Dirac**:

      `T(δ_z) = (1/2)·δ_{f₁(z)} + (1/2)·δ_{f₂(z)}`

    Each Dirac splits into two children Diracs under one application
    of the Hutchinson operator, with equal weights `1/2`. This is the
    recursive step generating the level-by-level structure of
    `cantorDiscMeasure n`. -/
theorem hutchinsonOp_dirac (z : ℝ) :
    hutchinsonOp (MeasureTheory.Measure.dirac z) =
    (1/2 : ENNReal) • MeasureTheory.Measure.dirac (cantorContraction1 z) +
    (1/2 : ENNReal) • MeasureTheory.Measure.dirac (cantorContraction2 z) := by
  unfold hutchinsonOp
  rw [MeasureTheory.Measure.map_dirac cantorContraction1_measurable]
  rw [MeasureTheory.Measure.map_dirac cantorContraction2_measurable]

/-! ## ★ Integral recursion under Hutchinson iteration ★ -/

/-- **★ Integral recursion ★**:

      `∫ f d(T μ) = (1/2) ∫ f ∘ f₁ dμ + (1/2) ∫ f ∘ f₂ dμ`

    The fundamental recursion for integrals against the Hutchinson
    iterate. Each step distributes via the pushforward formula
    `∫ f d(map g μ) = ∫ f∘g dμ` (mathlib `integral_map`) and the
    measure-additivity of integrals.

    **Consequence**: applied iteratively, `∫ f d(T^n μ)` decomposes
    into a sum of `2^n` integrals against `μ`, each of `f` composed
    with a length-`n` IFS-word. For `μ = δ_{1/2}`, each integral is
    a single point evaluation `f(IFS-word(1/2))`, giving the explicit
    `2^n`-term finite sum. -/
theorem integral_hutchinsonOp_apply (μ : MeasureTheory.Measure ℝ) (f : ℝ → ℝ)
    (h1 : MeasureTheory.Integrable f
            (MeasureTheory.Measure.map cantorContraction1 μ))
    (h2 : MeasureTheory.Integrable f
            (MeasureTheory.Measure.map cantorContraction2 μ)) :
    ∫ x, f x ∂(hutchinsonOp μ) =
    (1/2) * ∫ y, f (cantorContraction1 y) ∂μ +
    (1/2) * ∫ y, f (cantorContraction2 y) ∂μ := by
  unfold hutchinsonOp
  rw [MeasureTheory.integral_add_measure
        ((MeasureTheory.integrable_smul_measure
          (by norm_num : (1/2 : ENNReal) ≠ 0)
          (by norm_num : (1/2 : ENNReal) ≠ ⊤)).mpr h1)
        ((MeasureTheory.integrable_smul_measure
          (by norm_num : (1/2 : ENNReal) ≠ 0)
          (by norm_num : (1/2 : ENNReal) ≠ ⊤)).mpr h2)]
  rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_map cantorContraction1_measurable.aemeasurable
        h1.aestronglyMeasurable]
  rw [MeasureTheory.integral_map cantorContraction2_measurable.aemeasurable
        h2.aestronglyMeasurable]
  rw [show (1/2 : ENNReal).toReal = (1/2 : ℝ) from by simp]
  simp only [smul_eq_mul]

/-! ## Weak-* convergence predicate -/

/-- **Weak-* limit predicate** for the Hutchinson iterates:

      `IsWeakLimitOfHutchinsonIterates μ :=
        ∀ bounded continuous f, ∫ f d(cantorDiscMeasure n) → ∫ f dμ`

    `μ` is a weak-* limit of the iterates `cantorDiscMeasure n` if
    integrals against bounded continuous test functions converge to
    integrals against `μ`. This is the standard "weak convergence
    of measures" notion (Portmanteau theorem characterisation).

    **Conjecture** (provable from Banach contraction in Wasserstein-1):

      `IsWeakLimitOfHutchinsonIterates μ_H`

    i.e., the Hutchinson invariant measure `μ_H` is the (unique)
    weak-* limit of the iterates from `δ_{1/2}`. The proof uses the
    integral recursion (`integral_hutchinsonOp_apply`) iteratively
    + the Cauchy property in Wasserstein-1 (factor 1/3 per
    iteration step). -/
def IsWeakLimitOfHutchinsonIterates (μ : MeasureTheory.Measure ℝ) : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f → (∃ M, ∀ x, |f x| ≤ M) →
    Filter.Tendsto (fun n => ∫ x, f x ∂(cantorDiscMeasure n))
            Filter.atTop (nhds (∫ x, f x ∂μ))

/-- **Integral recursion for `cantorDiscMeasure` iterates**:

      `∫ f d(cantorDiscMeasure (n+1)) =
        (1/2) ∫ f∘f₁ d(cantorDiscMeasure n) +
        (1/2) ∫ f∘f₂ d(cantorDiscMeasure n)`

    Specialisation of `integral_hutchinsonOp_apply` to the iterate
    `cantorDiscMeasure n`. The recursion shows how integral
    evaluations at level `n+1` reduce to integral evaluations at
    level `n`, with the IFS-word composition `f∘f_i` on the
    integrand. -/
theorem integral_cantorDiscMeasure_succ (n : ℕ) (f : ℝ → ℝ)
    (h1 : MeasureTheory.Integrable f
            (MeasureTheory.Measure.map cantorContraction1 (cantorDiscMeasure n)))
    (h2 : MeasureTheory.Integrable f
            (MeasureTheory.Measure.map cantorContraction2 (cantorDiscMeasure n))) :
    ∫ x, f x ∂(cantorDiscMeasure (n + 1)) =
    (1/2) * ∫ y, f (cantorContraction1 y) ∂(cantorDiscMeasure n) +
    (1/2) * ∫ y, f (cantorContraction2 y) ∂(cantorDiscMeasure n) := by
  rw [cantorDiscMeasure_succ]
  exact integral_hutchinsonOp_apply (cantorDiscMeasure n) f h1 h2

/-! ## Hutchinson-invariant ⟹ integral fixed-point identity -/

/-- **★ Integral fixed-point identity for Hutchinson-invariant measures ★**:

    If `μ` is Hutchinson-invariant, then for every (suitably-integrable)
    function `f`:

      `∫ f dμ = (1/2) ∫ f∘f₁ dμ + (1/2) ∫ f∘f₂ dμ`

    Direct from `μ = T μ` (Hutchinson invariance) + the integral
    recursion `integral_hutchinsonOp_apply`.

    **Significance**: this is the integral-level expression of the
    measure-level invariance. It says that integration against `μ_H`
    is BALANCED across the two IFS cells. Specialized to indicator
    functions of cells gives `μ_H(cell) = 1/2 · μ_H(parent)`, the
    canonical cell-mass identity. -/
theorem integral_of_isHutchinsonInvariant (μ : MeasureTheory.Measure ℝ)
    (hμ : IsHutchinsonInvariant μ) (f : ℝ → ℝ)
    (h1 : MeasureTheory.Integrable f
            (MeasureTheory.Measure.map cantorContraction1 μ))
    (h2 : MeasureTheory.Integrable f
            (MeasureTheory.Measure.map cantorContraction2 μ)) :
    ∫ x, f x ∂μ =
    (1/2) * ∫ y, f (cantorContraction1 y) ∂μ +
    (1/2) * ∫ y, f (cantorContraction2 y) ∂μ := by
  conv_lhs => rw [hμ]
  exact integral_hutchinsonOp_apply μ f h1 h2

/-! ## ★ Difference recursion (the weak-convergence contraction structure) ★ -/

/-- **★ Difference recursion ★** — for any Hutchinson-invariant `μ`,
    the difference between `cantorDiscMeasure` integrals and the
    `μ`-integral satisfies the same recursion as the iterate integral:

      `(∫ f d(cantorDiscMeasure (n+1))) − (∫ f dμ)
        = (1/2) · [(∫ f∘f₁ d(cantorDiscMeasure n)) − (∫ f∘f₁ dμ)]
        + (1/2) · [(∫ f∘f₂ d(cantorDiscMeasure n)) − (∫ f∘f₂ dμ)]`

    **This is the structural CONTRACTION at the integral level**.
    For Lipschitz `f` with constant `L`, `f∘f_i` has Lipschitz
    constant `L/3` (since each `f_i` is a `1/3`-contraction). So:

      `|Δ_{n+1}(f)| ≤ (L/3) · sup{|Δ_n(g)| : g Lipschitz constant L/3}`

    Iterating gives `|Δ_n(f)| ≤ L · (1/3)^n · |Δ_0|`, the geometric
    rate of weak-* convergence.

    The full convergence proof requires Lipschitz/Wasserstein
    machinery; this commit establishes the STRUCTURAL DIFFERENCE
    RECURSION that any such proof reduces to. -/
theorem integral_difference_recursion (μ : MeasureTheory.Measure ℝ)
    (hμ : IsHutchinsonInvariant μ) (n : ℕ) (f : ℝ → ℝ)
    (h1n : MeasureTheory.Integrable f
            (MeasureTheory.Measure.map cantorContraction1 (cantorDiscMeasure n)))
    (h2n : MeasureTheory.Integrable f
            (MeasureTheory.Measure.map cantorContraction2 (cantorDiscMeasure n)))
    (h1μ : MeasureTheory.Integrable f
            (MeasureTheory.Measure.map cantorContraction1 μ))
    (h2μ : MeasureTheory.Integrable f
            (MeasureTheory.Measure.map cantorContraction2 μ)) :
    (∫ x, f x ∂(cantorDiscMeasure (n + 1))) - ∫ x, f x ∂μ =
    (1/2) * ((∫ y, f (cantorContraction1 y) ∂(cantorDiscMeasure n)) -
             ∫ y, f (cantorContraction1 y) ∂μ) +
    (1/2) * ((∫ y, f (cantorContraction2 y) ∂(cantorDiscMeasure n)) -
             ∫ y, f (cantorContraction2 y) ∂μ) := by
  rw [integral_cantorDiscMeasure_succ n f h1n h2n]
  rw [integral_of_isHutchinsonInvariant μ hμ f h1μ h2μ]
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
