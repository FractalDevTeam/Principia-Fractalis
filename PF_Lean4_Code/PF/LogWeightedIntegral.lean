/-
# Log-weighted Lebesgue Integral Infrastructure

Parallel infrastructure for the log-weighted inner product
  ⟨f, g⟩ = ∫₀¹ conj(f(x)) · g(x) · dx/x
that the transfer operator T₃ uses for self-adjointness.

This file defines the measure `logWeightedMeasure := (1/x) · volume on ℝ`
via `MeasureTheory.Measure.withDensity`. A future refactor should replace
the structure-based `LogWeightedL2` in `PF/TransferOperator.lean` with
`MeasureTheory.Lp ℂ 2 logWeightedMeasure`, which automatically provides
the inner product; once that lands, `LogWeightedL2.inner` and
`T3_self_adjoint_conj` become theorems (by the change-of-variables
proof in Chapter 20).

Started 2026-04-24 as action item #1 of RESEARCH_ROADMAP.md.

Reference: Principia Fractalis, Chapter 20
-/

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.ENNReal.Basic
import PF.TransferOperator

namespace PrincipiaTractalis

open MeasureTheory
open scoped Function  -- for the `on` notation in `Pairwise (Disjoint on _)`

/-- The log-weighted measure on the real line: dμ = (1/x) · dx, with
    dμ({x ≤ 0}) = 0 by the piecewise definition (the physical domain
    is (0, 1], but we extend by 0 on the complement for convenience).

    On (0, 1], this is a sigma-finite but infinite measure:
      ∫_{(0,1]} dx/x = ∞ (logarithmic divergence at 0).
    Yet L² with respect to it is well-defined. -/
noncomputable def logWeightedMeasure : Measure ℝ :=
  volume.withDensity (fun x => if x ≤ 0 then 0 else (ENNReal.ofReal (1 / x)))

/-- The density function used in the measure definition, isolated for
    reuse in proofs. -/
noncomputable def logWeightDensity (x : ℝ) : ENNReal :=
  if x ≤ 0 then 0 else ENNReal.ofReal (1 / x)

lemma logWeightedMeasure_def :
    logWeightedMeasure = volume.withDensity logWeightDensity := by
  rfl

/-- The log-weighted density is everywhere finite (ne top). -/
lemma logWeightDensity_ne_top (x : ℝ) : logWeightDensity x ≠ ⊤ := by
  unfold logWeightDensity
  split_ifs
  · exact ENNReal.zero_ne_top
  · exact ENNReal.ofReal_ne_top

/-- `logWeightedMeasure` is sigma-finite. -/
instance : SigmaFinite logWeightedMeasure := by
  unfold logWeightedMeasure
  exact MeasureTheory.SigmaFinite.withDensity_of_ne_top' (fun x => logWeightDensity_ne_top x)

/-- The concrete L²(logWeightedMeasure) Hilbert space. This is the type that
    should replace the current structure-based `LogWeightedL2` in
    `PF/TransferOperator.lean`. It automatically inherits an
    `InnerProductSpace ℂ` instance from mathlib's `MeasureTheory.L2` theory
    — when the refactor is complete, `LogWeightedL2.inner` and
    `T3_self_adjoint_conj` become provable theorems, not axioms.

    The `SigmaFinite` instance above is required for this type to
    satisfy the `NormedAddCommGroup` / `InnerProductSpace` instances
    consistently. -/
noncomputable abbrev LogWeightedL2_concrete : Type :=
  MeasureTheory.Lp ℂ 2 logWeightedMeasure

/-! ### Phase A milestone: `LogWeightedL2_concrete` is an `InnerProductSpace ℂ`

The strongest Lean-side evidence that the Phase A elimination of
`LogWeightedL2.inner` is structurally viable: mathlib's
`InnerProductSpace ℂ (Lp ℂ 2 μ)` instance applies directly, with no
extra hypotheses (the `SigmaFinite logWeightedMeasure` instance proven
above provides any measure-theoretic side condition that mathlib needs).

After the eventual structural swap (`LogWeightedL2 :=
LogWeightedL2_concrete`), the inner product `⟪·, ·⟫` becomes the mathlib
`@inner ℂ _ _` (with `inner f g = ∫ conj(f) * g ∂logWeightedMeasure`),
the axiom `LogWeightedL2.inner` is replaceable by the mathlib instance,
and sesquilinearity + conjugate symmetry + positive-definiteness
(currently taken as hypotheses in `self_adjoint_real_eigenvalues`)
become free instance fields.
-/

/-- `LogWeightedL2_concrete` carries mathlib's `InnerProductSpace ℂ`
    instance. -/
noncomputable example : InnerProductSpace ℂ LogWeightedL2_concrete := inferInstance

/-- `LogWeightedL2_concrete` carries mathlib's `NormedAddCommGroup`
    instance (the additive structure with the L² norm). -/
noncomputable example : NormedAddCommGroup LogWeightedL2_concrete := inferInstance

/-- `LogWeightedL2_concrete` is complete: it is a Hilbert space, so the
    spectral theorem applies (mathlib's `IsCompactOperator` API depends
    on this). -/
noncomputable example : CompleteSpace LogWeightedL2_concrete := inferInstance

/-- `LogWeightedL2_concrete` is a `ℂ`-normed space. -/
noncomputable example : NormedSpace ℂ LogWeightedL2_concrete := inferInstance

/-! ## Phase A Foundations: Measurability of Transfer-Operator Constituents

Measurability lemmas for the maps that compose `transferOperatorAction`
(in `PF/TransferOperator.lean`). These are prerequisites for the
eventual Phase A elimination of `LogWeightedL2.inner` — the load-bearing
`MemLp` proof for the rewritten `transferOperatorAction` output requires
that each constituent map (inverse branches, weight functions, expanding
maps) is Borel measurable so the integral against `logWeightedMeasure`
is well-defined.

Added 2026-04-29 as durable infrastructure ahead of the structural
abbrev swap (`LogWeightedL2 := LogWeightedL2_concrete`).
RESEARCH_ROADMAP.md §2.1.
-/

/-- The inverse branch $y_k(x) = (x + k)/b$ is continuous on $\mathbb{R}$
    when $b \ne 0$. -/
theorem inverseBranch_continuous (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0) :
    Continuous (fun x : ℝ => inverseBranch b k x) := by
  unfold inverseBranch
  exact (continuous_id.add continuous_const).div_const _

/-- The inverse branch $y_k(x) = (x + k)/b$ is Borel measurable on
    $\mathbb{R}$ when $b \ge 1$ (which is the only regime the transfer
    operator framework uses; in particular $b = 3$). -/
theorem inverseBranch_measurable (b : ℕ) (k : Fin b) (hb : b ≥ 1) :
    Measurable (fun x : ℝ => inverseBranch b k x) := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)
  exact (inverseBranch_continuous b k (ne_of_gt hb_pos)).measurable

/-- The expanding base-$b$ map $\tau_b(x) = bx \bmod 1 = bx - \lfloor bx \rfloor$
    is Borel measurable on $\mathbb{R}$.

    Recognises $\tau_b(x) = \mathrm{Int.fract}(bx)$ and discharges
    via `Measurable.fract` (`Mathlib.MeasureTheory.Function.Floor`). -/
theorem expandingMap_measurable (b : ℕ) :
    Measurable (fun x : ℝ => expandingMap b x) := by
  -- `expandingMap b x = b*x - ⌊b*x⌋ = Int.fract (b*x)` definitionally
  -- (mathlib's `Int.fract` reduces to that form).
  show Measurable (fun x : ℝ => (b : ℝ) * x - ⌊(b : ℝ) * x⌋)
  have heq : (fun x : ℝ => (b : ℝ) * x - ⌊(b : ℝ) * x⌋)
      = fun x => Int.fract ((b : ℝ) * x) := by
    ext x; rfl
  rw [heq]
  exact (measurable_const.mul measurable_id).fract

/-- The weight function $w_k(x) = \sqrt{bx/(x+k)}$ is uniformly bounded
    by $\sqrt{b}$ on all of $\mathbb{R}$.

    Proof: when the if-branch fires (so $x > 0$ and $x + k > 0$), we have
    $bx/(x+k) \le b$ because $b \cdot x \le b \cdot (x + k)$ holds whenever
    $b \ge 0$ and $k \ge 0$ (both hold since $b, k$ come from $\mathbb{N}$).
    When the if-branch is false the weight is $0 \le \sqrt{b}$.

    The bound is uniform in $x$ — no domain restriction needed (an earlier
    weaker form required $x \in [0, 1]$, but the proof only needs the
    nonnegativity of $b$ and $k$).

    Load-bearing for the future Phase A `MemLp` proof: the $L^2$ norm
    of `transferOperatorAction f` decomposes as a sum over branches, each
    bounded by $\sqrt{b}$ times the $L^2$ norm of $f$ on the branch image. -/
theorem weightFunction_bounded (b : ℕ) (k : Fin b) (x : ℝ) :
    weightFunction b k x ≤ Real.sqrt (b : ℝ) := by
  unfold weightFunction
  split_ifs with h
  · -- Active branch: weight = √(b·x/(x+k))
    obtain ⟨_, hxk_pos⟩ := h
    apply Real.sqrt_le_sqrt
    -- Goal: b·x/(x+k) ≤ b
    rw [div_le_iff₀ hxk_pos]
    -- Goal: b·x ≤ b·(x+k)
    have hk_nonneg : (0:ℝ) ≤ k.val := Nat.cast_nonneg _
    have hb_nonneg : (0:ℝ) ≤ b := Nat.cast_nonneg _
    nlinarith
  · -- Inactive branch: weight = 0 ≤ √b
    exact Real.sqrt_nonneg _

/-- Composition of a measurable function with the inverse branch is
    measurable. Direct consequence of `inverseBranch_measurable`. -/
theorem Measurable.comp_inverseBranch {α : Type*} [MeasurableSpace α]
    {f : ℝ → α} (hf : Measurable f) (b : ℕ) (k : Fin b) (hb : b ≥ 1) :
    Measurable (fun x : ℝ => f (inverseBranch b k x)) :=
  hf.comp (inverseBranch_measurable b k hb)

/-- The inverse branch is injective on $\mathbb{R}$ (when $b \ne 0$).

    $y_k(x) = (x + k)/b$ is an affine map with nonzero slope $1/b$,
    hence injective. Required by mathlib's change-of-variables formula
    `MeasurePreserving.lintegral_comp`, which expects the substitution
    map to be a `MeasurableEmbedding` (injective + measurable). -/
theorem inverseBranch_injective (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0) :
    Function.Injective (fun x : ℝ => inverseBranch b k x) := by
  intros x y hxy
  unfold inverseBranch at hxy
  -- hxy : (x + ↑k) / ↑b = (y + ↑k) / ↑b
  -- Multiply both sides by b (nonzero) and cancel.
  have h_eq : x + (k.val : ℝ) = y + (k.val : ℝ) := by
    have := congr_arg (fun r => r * (b : ℝ)) hxy
    simp only at this
    rwa [div_mul_cancel₀ _ hb, div_mul_cancel₀ _ hb] at this
  linarith

/-- The (left) inverse of `inverseBranch b k`: `g(u) = b · u - k`.

    Globally on $\mathbb{R}$ this is a continuous affine map
    (slope $b$). Restricted to the image $[k/b, (k+1)/b]$ of
    `inverseBranch b k` on $[0, 1]$, this is the genuine inverse. -/
noncomputable def inverseBranchInverse (b : ℕ) (k : Fin b) (u : ℝ) : ℝ :=
  (b : ℝ) * u - (k.val : ℝ)

/-- `inverseBranchInverse` is continuous: an affine map. -/
theorem inverseBranchInverse_continuous (b : ℕ) (k : Fin b) :
    Continuous (fun u : ℝ => inverseBranchInverse b k u) := by
  unfold inverseBranchInverse
  exact (continuous_const.mul continuous_id).sub continuous_const

/-- `inverseBranchInverse` is Borel measurable. -/
theorem inverseBranchInverse_measurable (b : ℕ) (k : Fin b) :
    Measurable (fun u : ℝ => inverseBranchInverse b k u) :=
  (inverseBranchInverse_continuous b k).measurable

/-- `inverseBranchInverse b k` is a left inverse of `inverseBranch b k`.

    Computation: `g(y_k(x)) = b · ((x + k)/b) - k = x + k - k = x`. -/
theorem inverseBranchInverse_leftInverse (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0) :
    Function.LeftInverse (fun u => inverseBranchInverse b k u)
                          (fun x => inverseBranch b k x) := by
  intro x
  unfold inverseBranchInverse inverseBranch
  -- Goal: b * ((x + k) / b) - k = x
  field_simp
  ring

/-- The range of `inverseBranch b k : ℝ → ℝ` is all of $\mathbb{R}$.

    The affine map $y_k(x) = (x + k)/b$ is surjective $\mathbb{R} \to \mathbb{R}$:
    for any $y$, pick $x = b \cdot y - k$, then $y_k(x) = y$. -/
theorem inverseBranch_range_eq_univ (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0) :
    Set.range (fun x : ℝ => inverseBranch b k x) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  refine ⟨(b : ℝ) * y - (k.val : ℝ), ?_⟩
  unfold inverseBranch
  field_simp
  ring

/-- The range of `inverseBranch b k : ℝ → ℝ` is Borel measurable
    (trivially, since it equals $\mathbb{R}$). -/
theorem inverseBranch_range_measurable (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0) :
    MeasurableSet (Set.range (fun x : ℝ => inverseBranch b k x)) := by
  rw [inverseBranch_range_eq_univ b k hb]
  exact MeasurableSet.univ

/-- The inverse branch is a `MeasurableEmbedding` — the four-piece
    composition: injective + measurable + measurable inverse with
    LeftInverse + measurable range.

    Required by mathlib's `MeasurePreserving.lintegral_comp` and
    `MeasurableEmbedding.lintegral_map` for the per-branch change-of-
    variables in the Mayer 1991 operator-norm bound. -/
theorem inverseBranch_measurableEmbedding (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0)
    (hb_ge : b ≥ 1) :
    MeasurableEmbedding (fun x : ℝ => inverseBranch b k x) :=
  MeasurableEmbedding.of_measurable_inverse
    (inverseBranch_measurable b k hb_ge)
    (inverseBranch_range_measurable b k hb)
    (inverseBranchInverse_measurable b k)
    (inverseBranchInverse_leftInverse b k hb)

/-- `inverseBranchInverse b k` is also a right inverse of `inverseBranch b k`:
    `inverseBranch (inverseBranchInverse u) = u`.

    Computation: $y_k(b u - k) = ((bu - k) + k)/b = bu/b = u$.
    Together with `inverseBranchInverse_leftInverse`, this gives
    a full bijection (Equiv) between $\mathbb{R}$ and itself,
    making `inverseBranch` a `MeasurableEquiv`. -/
theorem inverseBranchInverse_rightInverse (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0) :
    Function.RightInverse (fun u => inverseBranchInverse b k u)
                           (fun x => inverseBranch b k x) := by
  intro u
  unfold inverseBranchInverse inverseBranch
  -- Goal: ((b * u - k) + k) / b = u
  field_simp
  ring

/-- The `MeasurableEmbedding` instance for `inverseBranchInverse b k`
    (the inverse direction).

    Symmetric construction to `inverseBranch_measurableEmbedding`:
    `inverseBranchInverse u = b · u - k` is also affine with nonzero
    slope $b$, hence injective; its inverse is `inverseBranch`, which
    is measurable; and its range is all of $\mathbb{R}$. -/
theorem inverseBranchInverse_measurableEmbedding (b : ℕ) (k : Fin b)
    (hb : (b : ℝ) ≠ 0) (hb_ge : b ≥ 1) :
    MeasurableEmbedding (fun u : ℝ => inverseBranchInverse b k u) :=
  MeasurableEmbedding.of_measurable_inverse
    (inverseBranchInverse_measurable b k)
    (by
      -- Range of inverseBranchInverse is all of ℝ (it's surjective:
      -- u = (x+k)/b is hit by x = inverseBranch b k u given b ≠ 0).
      have : Set.range (fun u : ℝ => inverseBranchInverse b k u) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        refine ⟨(x + (k.val : ℝ)) / (b : ℝ), ?_⟩
        unfold inverseBranchInverse
        field_simp
        ring
      rw [this]; exact MeasurableSet.univ)
    (inverseBranch_measurable b k hb_ge)
    (inverseBranchInverse_rightInverse b k hb)

/-- The `Equiv` (bijection) between $\mathbb{R}$ and itself given by
    `inverseBranch b k` and its inverse `inverseBranchInverse b k`. -/
noncomputable def inverseBranch_equiv (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0) :
    ℝ ≃ ℝ where
  toFun := fun x => inverseBranch b k x
  invFun := fun u => inverseBranchInverse b k u
  left_inv := inverseBranchInverse_leftInverse b k hb
  right_inv := inverseBranchInverse_rightInverse b k hb

/-- The `MeasurableEquiv` between $\mathbb{R}$ and itself given by
    `inverseBranch b k`.

    Strongest measure-theoretic structure: combined with the affine
    pushforward identity `volume.map inverseBranch = ENNReal.ofReal b
    • volume` below, it unlocks the per-branch change-of-variables in
    its full mathlib form. -/
noncomputable def inverseBranch_measurableEquiv (b : ℕ) (k : Fin b)
    (hb : (b : ℝ) ≠ 0) (hb_ge : b ≥ 1) : ℝ ≃ᵐ ℝ where
  toEquiv := inverseBranch_equiv b k hb
  measurable_toFun := inverseBranch_measurable b k hb_ge
  measurable_invFun := inverseBranchInverse_measurable b k

/-- The volume pushforward identity for the inverse branch:
    $\mathrm{volume.map}\, y_k = \mathrm{ENNReal.ofReal}\, b \cdot \mathrm{volume}$.

    Decomposes $y_k(x) = (x + k)/b$ as the composition of translation
    `(· + k)` (which preserves volume on $\mathbb{R}$ by Haar measure
    translation invariance) and scaling `(· / b) = (· * (1/b))`
    (which scales volume by `|1/b|⁻¹ = b` via `Real.map_volume_mul_right`).

    This is the **affine Jacobian** of the change-of-variables,
    machine-checked from mathlib's pre-existing affine-pushforward
    infrastructure. -/
theorem inverseBranch_volume_map (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0) :
    Measure.map (fun x : ℝ => inverseBranch b k x) volume =
      ENNReal.ofReal (b : ℝ) • volume := by
  -- Decompose: y_k = (· / b) ∘ (· + k.val)
  have h_decomp : (fun x : ℝ => inverseBranch b k x)
                = (fun y : ℝ => y / (b : ℝ)) ∘ (fun x : ℝ => x + (k.val : ℝ)) := by
    funext x; unfold inverseBranch; rfl
  rw [h_decomp]
  rw [← Measure.map_map (f := fun x : ℝ => x + (k.val : ℝ))
                        (g := fun y : ℝ => y / (b : ℝ))
                        (measurable_id.div_const _) (measurable_id.add_const _)]
  -- (volume.map (· + k.val)).map (· / b) = ENNReal.ofReal b • volume
  -- Translation invariance: volume.map (· + k.val) = volume
  rw [show Measure.map (fun x : ℝ => x + (k.val : ℝ)) volume = volume from
      map_add_right_eq_self volume (k.val : ℝ)]
  -- Now: volume.map (· / b) = ENNReal.ofReal b • volume
  -- (· / b) = (· * (1/b))
  have h_div : (fun y : ℝ => y / (b : ℝ)) = (fun y => y * (1 / (b : ℝ))) := by
    funext y; rw [div_eq_mul_inv, one_div]
  rw [h_div, Real.map_volume_mul_right (one_div_ne_zero hb)]
  -- Goal: ENNReal.ofReal |(1/b)⁻¹| • volume = ENNReal.ofReal b • volume
  congr 1
  rw [one_div, inv_inv, abs_of_nonneg (Nat.cast_nonneg b)]

/-- The full lintegral change-of-variables identity for the inverse
    branch:

      $\int_x g(y_k(x))\, \mathrm{dvolume}(x) = b \cdot \int_y g(y)\, \mathrm{dvolume}(y)$

    Composes:
      1. `MeasurableEmbedding.lintegral_map` (commit c54bf82) gives
         $\int_x g(y_k(x)) = \int_y g(y) \, \mathrm{d}(volume.map\, y_k)$.
      2. `inverseBranch_volume_map` (commit 91d3254) substitutes
         $\mathrm{volume.map}\, y_k = \mathrm{ENNReal.ofReal}\, b \cdot \mathrm{volume}$.
      3. `lintegral_smul_measure` pulls out the constant factor $b$.

    This is the **per-branch change-of-variables formula** in its
    full mathlib form. Combined with the Radon-Nikodym identity
    `weight_squared_eq_jacobian` (commit 257726c) and the linearity
    of integration over the b-branch sum, it gives the integration
    of the pointwise bound that closes the Mayer 1991 chain. -/
theorem inverseBranch_lintegral_change_of_variables (b : ℕ) (k : Fin b)
    (hb : (b : ℝ) ≠ 0) (hb_ge : b ≥ 1) (g : ℝ → ENNReal) :
    ∫⁻ x, g (inverseBranch b k x) ∂volume
      = ENNReal.ofReal (b : ℝ) * ∫⁻ y, g y ∂volume := by
  -- Step 1: Apply MeasurableEmbedding.lintegral_map (right-to-left).
  rw [← (inverseBranch_measurableEmbedding b k hb hb_ge).lintegral_map g]
  -- Goal: ∫⁻ y, g y ∂(volume.map inverseBranch) = b * ∫⁻ y, g y ∂volume
  -- Step 2: Substitute the volume pushforward identity.
  rw [inverseBranch_volume_map b k hb]
  -- Goal: ∫⁻ y, g y ∂(ENNReal.ofReal b • volume) = ENNReal.ofReal b * ∫⁻ y, g y ∂volume
  -- Step 3: Pull out the scalar factor via lintegral_smul_measure.
  rw [lintegral_smul_measure]
  -- Goal: ENNReal.ofReal b • ∫⁻ y, g y ∂volume = ENNReal.ofReal b * ∫⁻ y, g y ∂volume
  rfl

/-- `inverseBranch b k` is a `MeasurePreserving` map from volume to
    the scaled measure `ENNReal.ofReal b • volume`.

    Packages `inverseBranch_measurable` (commit ab98579) and
    `inverseBranch_volume_map` (commit 91d3254) into mathlib's
    `MeasurePreserving` structure. Useful for downstream API that
    expects this packaged form (e.g., for `MeasurePreserving.lintegral_comp`
    in restricted-measure variants). -/
theorem inverseBranch_measurePreserving (b : ℕ) (k : Fin b)
    (hb : (b : ℝ) ≠ 0) (hb_ge : b ≥ 1) :
    MeasureTheory.MeasurePreserving (fun x : ℝ => inverseBranch b k x)
                                    volume
                                    (ENNReal.ofReal (b : ℝ) • volume) where
  measurable := inverseBranch_measurable b k hb_ge
  map_eq := inverseBranch_volume_map b k hb

/-- The set-restricted change-of-variables identity for the inverse branch:

      $\int_{x \in y_k^{-1}(s)} h(y_k(x))\, \mathrm{dvolume}(x)
        = b \cdot \int_{y \in s} h(y)\, \mathrm{dvolume}(y)$

    for any set $s \subseteq \mathbb{R}$ and any (possibly non-measurable)
    integrand $h : \mathbb{R} \to \mathbb{R}_{\ge 0}^\infty$.

    Composes:
      1. `MeasurePreserving.setLIntegral_comp_preimage_emb` (mathlib) on the
         packaged `inverseBranch_measurePreserving` (this commit) and
         `inverseBranch_measurableEmbedding` (commit c54bf82) gives
         $\int_{y_k^{-1} s} h(y_k(x))\, \mathrm{dvolume}
            = \int_s h(y)\, \mathrm{d}(\mathrm{ENNReal.ofReal}\, b \cdot \mathrm{volume})$.
      2. `setLIntegral_smul_measure` (mathlib) pulls out the constant factor $b$.

    This is the **set-restricted per-branch CoV** — the form the operator-norm
    bound consumes when integrating the pointwise estimate over $[0,1]$ and
    partitioning into the per-branch images $[k/b, (k+1)/b]$. -/
theorem inverseBranch_set_lintegral_change_of_variables (b : ℕ) (k : Fin b)
    (hb : (b : ℝ) ≠ 0) (hb_ge : b ≥ 1) (s : Set ℝ) (h : ℝ → ENNReal) :
    ∫⁻ x in (inverseBranch b k) ⁻¹' s, h (inverseBranch b k x) ∂volume
      = ENNReal.ofReal (b : ℝ) * ∫⁻ y in s, h y ∂volume := by
  -- Step 1: Push the integral through the change-of-variables. Result is
  --   a setLIntegral of `h` over `s` against the pushforward measure
  --   `ENNReal.ofReal b • volume`.
  rw [(inverseBranch_measurePreserving b k hb hb_ge).setLIntegral_comp_preimage_emb
        (inverseBranch_measurableEmbedding b k hb hb_ge) h s]
  -- Step 2: Pull out the scalar factor via setLIntegral_smul_measure.
  rw [setLIntegral_smul_measure]
  rfl

/-- The inverse branch maps the unit interval into itself:
    $y_k(x) = (x + k)/b \in [0, 1]$ for $x \in [0, 1]$ and $k \in \mathrm{Fin}\, b$.

    Lower bound: $(x + k)/b \ge 0/b = 0$ since $x, k \ge 0$.
    Upper bound: $(x + k)/b \le (1 + (b-1))/b = 1$ since $x \le 1$ and
    $k \le b - 1$. -/
theorem inverseBranch_image_in_unit_interval (b : ℕ) (k : Fin b) (x : ℝ)
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    inverseBranch b k x ∈ Set.Icc (0:ℝ) 1 := by
  unfold inverseBranch
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    have hb_nat : 0 < b := Fin.pos k
    exact_mod_cast hb_nat
  refine ⟨?_, ?_⟩
  · -- Lower bound: (x + k) / b ≥ 0
    apply div_nonneg
    · exact add_nonneg hx.1 (Nat.cast_nonneg k.val)
    · exact le_of_lt hb_pos
  · -- Upper bound: (x + k) / b ≤ 1
    rw [div_le_one hb_pos]
    have hk_lt : k.val + 1 ≤ b := k.isLt
    have hk_cast : (k.val : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hk_lt
    linarith [hx.2]

/-- The expanding map maps the unit interval into itself:
    $\tau_b(x) = bx \bmod 1 \in [0, 1)$ for $x \in [0, 1]$ and $b \ge 1$.
    (At $x = 1$ exactly, $\tau_b(1) = b - \lfloor b \rfloor = 0$.)

    Uses the Mathlib `Int.fract` characterisation: $\mathrm{Int.fract}(y)
    \in [0, 1)$ for any $y \in \mathbb{R}$. -/
theorem expandingMap_image_in_unit_interval (b : ℕ) (x : ℝ) :
    expandingMap b x ∈ Set.Ico (0:ℝ) 1 := by
  show (b : ℝ) * x - ⌊(b : ℝ) * x⌋ ∈ Set.Ico (0:ℝ) 1
  have h_eq : (b : ℝ) * x - ⌊(b : ℝ) * x⌋ = Int.fract ((b : ℝ) * x) := rfl
  rw [h_eq]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

-- Note: `logWeightedMeasure_Iic_zero` (the lemma that the log-weighted
-- measure assigns 0 to the non-positive half-line) is left for a
-- follow-on commit; the `setLIntegral_congr_fun` discharge ran into
-- elaboration friction (measure inference on the right-hand-side
-- `lintegral_zero`). The mathematical content is true by definition
-- (density is 0 on `Iic 0`); deferring lets us focus on bounds lemmas
-- that are immediately load-bearing for Phase A.

/-- The weight function $w_k(x) = \sqrt{bx/(x+k)}$ (or 0 outside its
    domain) is Borel measurable on $\mathbb{R}$.

    The `dite` over the propositional condition reduces to an `ite`
    (the body $\sqrt{bx/(x+k)}$ does not use the proof of the
    condition), which is then handled by `Measurable.ite` over the
    measurable predicate $\{x > 0\} \cap \{x + k > 0\}$ with both
    branches measurable. -/
theorem weightFunction_measurable (b : ℕ) (k : Fin b) :
    Measurable (fun x : ℝ => weightFunction b k x) := by
  -- Convert dite to ite: the body doesn't use the bound proof.
  have heq : (fun x : ℝ => weightFunction b k x)
      = fun x => if x > 0 ∧ x + (k.val : ℝ) > 0
                  then Real.sqrt ((b : ℝ) * x / (x + (k.val : ℝ)))
                  else 0 := by
    ext x
    unfold weightFunction
    split_ifs <;> rfl
  rw [heq]
  refine Measurable.ite ?_ ?_ measurable_const
  · -- {x | x > 0 ∧ x + k > 0} is measurable
    refine MeasurableSet.inter measurableSet_Ioi ?_
    -- {x | x + k > 0} = preimage of Ioi 0 under (· + k)
    exact (measurable_id.add measurable_const) measurableSet_Ioi
  · -- √(bx/(x+k)) is measurable via Real.sqrt (continuous) ∘ measurable
    refine Continuous.measurable Real.continuous_sqrt |>.comp ?_
    exact (measurable_const.mul measurable_id).div
      (measurable_id.add measurable_const)

/-! ## The Radon-Nikodym Identity (Phase A change-of-variables key)

The weight function $w_k(x) = \sqrt{bx/(x+k)}$ is designed so that
$|w_k(x)|^2 \cdot d\mu_{\log}(x)$ is the pull-back of $d\mu_{\log}(y)$
under $y = y_k(x) = (x+k)/b$:

  $|w_k(x)|^2 \cdot \frac{dx}{x} = \frac{bx}{x+k} \cdot \frac{dx}{x}
   = \frac{b\, dx}{x+k} = \frac{b\, dx}{b\, y_k(x)} = \frac{dx}{y_k(x)}.$

Then under $u = y_k(x)$ (with $x = bu - k$, $dx = b\, du$):

  $\frac{dx}{y_k(x)} = \frac{b\, du}{u} = b \cdot \frac{du}{u}.$

So $\int_0^1 |w_k(x)|^2 \cdot g(y_k(x)) \cdot d\mu_{\log}(x)
   = b \int_{k/b}^{(k+1)/b} g(u) \cdot d\mu_{\log}(u)$.

This is the change-of-variables identity that drives the $b$-branch
Mayer-1991 estimate $\|T_b f\|_{L^2(d\mu_{\log})} \le \|f\|_{L^2(d\mu_{\log})}$
via Cauchy-Schwarz. The algebraic identity below is the Lean version
of the cancellation $|w_k|^2 / x = b / (x+k)$ that makes the calculation
go through. -/

/-- The Radon-Nikodym identity: $w_k(x)^2 / x = b / (x + k)$ on the
    active domain $\{x > 0\} \cap \{x + k > 0\}$.

    This is the algebraic core of the change-of-variables computation
    that proves $\|T_b\| \le 1$ on $L^2(d\mu_{\log})$. -/
theorem weight_squared_eq_jacobian (b : ℕ) (k : Fin b) (x : ℝ)
    (hx : x > 0) (hxk : x + (k.val : ℝ) > 0) :
    (weightFunction b k x)^2 / x = (b : ℝ) / (x + (k.val : ℝ)) := by
  unfold weightFunction
  -- Active branch fires by hypotheses
  rw [dif_pos ⟨hx, hxk⟩]
  -- Goal: (√(b·x/(x+k)))² / x = b / (x + k)
  rw [Real.sq_sqrt]
  · -- Goal: (b·x/(x+k)) / x = b / (x + k)
    field_simp
  · -- b·x/(x+k) ≥ 0
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt hx)
    · exact le_of_lt hxk

/-- The crisp one-line form of the Radon-Nikodym identity:
    $w_k(x)^2 \cdot y_k(x) = x$.

    Multiplying both sides of `weight_squared_eq_jacobian` by $x \cdot y_k(x)
    = x \cdot (x + k)/b$ yields this form. Says that the weight squared
    is exactly the Jacobian of the inverse branch in the multiplicative
    sense: $|w_k|^2 = x / y_k(x)$. -/
theorem weight_squared_times_inverseBranch (b : ℕ) (k : Fin b) (x : ℝ)
    (hb : b ≥ 1) (hx : x > 0) (hxk : x + (k.val : ℝ) > 0) :
    (weightFunction b k x)^2 * inverseBranch b k x = x := by
  unfold weightFunction inverseBranch
  rw [dif_pos ⟨hx, hxk⟩]
  -- Goal: (√(b·x/(x+k)))² · ((x+k)/b) = x
  rw [Real.sq_sqrt]
  · -- Goal: (b·x/(x+k)) · ((x+k)/b) = x
    have hb_pos : (0 : ℝ) < (b : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)
    have hxk_ne : (x + (k.val : ℝ)) ≠ 0 := ne_of_gt hxk
    have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
    field_simp
  · -- b·x/(x+k) ≥ 0
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt hx)
    · exact le_of_lt hxk

/-! ## Cauchy-Schwarz on the b-branch finite sum -/

/-- The b-branch Cauchy-Schwarz bound: $\|\sum_{k=0}^{b-1} a_k\|^2
    \le b \cdot \sum_{k=0}^{b-1} \|a_k\|^2$ for any
    $a : \mathrm{Fin}\, b \to \mathbb{C}$.

    Proof: triangle inequality $\|\sum a_k\| \le \sum \|a_k\|$, then
    `sq_sum_le_card_mul_sum_sq` (Chebyshev / AM-QM) on the
    nonnegative sequence $\|a_k\|$.

    This is the pointwise bound that drives the Mayer 1991
    operator-norm estimate for transfer operators: combined with
    the Radon-Nikodym identity (`weight_squared_eq_jacobian`,
    `weight_squared_times_inverseBranch`) and the change-of-
    variables formula, it gives $\|T_b f\|_{L^2(d\mu_{\log})} \le
    \|f\|_{L^2(d\mu_{\log})}$. -/
theorem branch_sum_sq_bound {b : ℕ} (a : Fin b → ℂ) :
    ‖∑ k, a k‖^2 ≤ (b : ℝ) * ∑ k, ‖a k‖^2 := by
  -- Step 1: triangle inequality ‖Σ a_k‖ ≤ Σ ‖a_k‖
  have h_tri : ‖∑ k, a k‖ ≤ ∑ k, ‖a k‖ := norm_sum_le _ _
  -- Step 2: square both sides (both nonneg)
  have h_sq : ‖∑ k, a k‖^2 ≤ (∑ k, ‖a k‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) h_tri 2
  -- Step 3: AM-QM (sq_sum_le_card_mul_sum_sq) on nonneg ‖a_k‖
  have h_amqm : (∑ k, ‖a k‖)^2 ≤
      (Finset.univ : Finset (Fin b)).card * ∑ k, ‖a k‖^2 :=
    sq_sum_le_card_mul_sum_sq
  -- Step 4: Finset.univ.card = b
  have h_card : ((Finset.univ : Finset (Fin b)).card : ℝ) = (b : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  -- Combine
  calc ‖∑ k, a k‖^2
      ≤ (∑ k, ‖a k‖)^2 := h_sq
    _ ≤ (Finset.univ : Finset (Fin b)).card * ∑ k, ‖a k‖^2 := h_amqm
    _ = (b : ℝ) * ∑ k, ‖a k‖^2 := by rw [h_card]

/-- The b-branch Cauchy-Schwarz bound applied to phase-multiplied values:
    when each phase $\omega_k$ has unit modulus, the phase modulus drops
    out of the bound.

    $\|\sum_k \omega_k \cdot v_k\|^2 \le b \cdot \sum_k \|v_k\|^2$
      whenever $\|\omega_k\| = 1$ for all $k$.

    Discharge: apply `branch_sum_sq_bound` to `fun k => phases k * vals k`,
    then simplify $\|\omega_k \cdot v_k\| = \|\omega_k\| \cdot \|v_k\| = \|v_k\|$
    via the unit-modulus hypothesis. -/
theorem branch_pointwise_bound_with_unit_phases {b : ℕ}
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (vals : Fin b → ℂ) :
    ‖∑ k, phases k * vals k‖^2 ≤ (b : ℝ) * ∑ k, ‖vals k‖^2 := by
  have h_pre : ‖∑ k, phases k * vals k‖^2 ≤
      (b : ℝ) * ∑ k, ‖phases k * vals k‖^2 :=
    branch_sum_sq_bound _
  have h_phase_drop : ∀ k, ‖phases k * vals k‖^2 = ‖vals k‖^2 := by
    intro k
    rw [norm_mul, hphases k, one_mul]
  -- Replace ‖ω_k · v_k‖² with ‖v_k‖² in the sum
  rw [show (∑ k, ‖phases k * vals k‖^2) = ∑ k, ‖vals k‖^2 from
        Finset.sum_congr rfl (fun k _ => h_phase_drop k)] at h_pre
  exact h_pre

/-- The full pointwise pre-integral bound for the transfer operator:

    $\left\|\frac{1}{b}\sum_k \omega_k \cdot w_k(x) \cdot v_k\right\|^2
     \le \frac{1}{b} \cdot \sum_k w_k(x)^2 \cdot \|v_k\|^2$

    given unit-modulus phases $\|\omega_k\| = 1$ and $b \ge 1$.

    This is the final pointwise estimate before integration. Composes
    `branch_pointwise_bound_with_unit_phases` (Cauchy-Schwarz with unit
    phases) with the prefactor $1/b$ and the real-to-complex coercion
    of the (nonnegative) weight function. The remaining work for the
    Mayer 1991 operator-norm bound $\|T_b f\|_{L^2} \le \|f\|_{L^2}$
    is integrating both sides against $d\mu_{\log}$ and applying the
    change-of-variables formula per branch. -/
theorem transferOperator_pointwise_norm_sq_bound (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (x : ℝ) (vals : Fin b → ℂ) :
    ‖(1 / (b : ℂ)) * ∑ k, phases k * ((weightFunction b k x : ℂ) * vals k)‖^2
      ≤ (1 / (b : ℝ)) * ∑ k, (weightFunction b k x)^2 * ‖vals k‖^2 := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)
  -- Step 1: Apply branch_pointwise_bound_with_unit_phases to the values
  -- (w_k(x) : ℂ) * vals k, getting ‖Σ ω_k (w_k v_k)‖² ≤ b · Σ ‖w_k v_k‖²
  have h_sum_bound :
      ‖∑ k, phases k * ((weightFunction b k x : ℂ) * vals k)‖^2
        ≤ (b : ℝ) * ∑ k, ‖(weightFunction b k x : ℂ) * vals k‖^2 :=
    branch_pointwise_bound_with_unit_phases phases hphases _
  -- Step 2: simplify ‖(w : ℂ) · v‖² = w² · ‖v‖² (since w ≥ 0)
  have h_weight_sq : ∀ k,
      ‖(weightFunction b k x : ℂ) * vals k‖^2 = (weightFunction b k x)^2 * ‖vals k‖^2 := by
    intro k
    rw [norm_mul, mul_pow]
    congr 1
    -- ‖(w : ℂ)‖² = w² since w ≥ 0; chain via Complex.norm_real → ℝ-norm → |w| → w
    have hw_nonneg : 0 ≤ weightFunction b k x := by
      unfold weightFunction
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact le_refl 0
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
  -- Step 3: rewrite the right-hand side of h_sum_bound
  rw [show (∑ k, ‖(weightFunction b k x : ℂ) * vals k‖^2) = ∑ k, (weightFunction b k x)^2 * ‖vals k‖^2 from
        Finset.sum_congr rfl (fun k _ => h_weight_sq k)] at h_sum_bound
  -- Step 4: apply ‖(1/b) · S‖² = (1/b)² · ‖S‖² = (1/b²) · ‖S‖²
  rw [norm_mul, mul_pow, norm_div, norm_one]
  rw [Complex.norm_natCast]
  -- Goal: (1/b)² · ‖S‖² ≤ (1/b) · Σ w_k² ‖v_k‖²
  have h_b_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have h_one_div_b_pos : (0 : ℝ) < 1 / (b : ℝ) := by positivity
  -- Multiply h_sum_bound by (1/b²) ≥ 0 on both sides:
  --   (1/b²) · ‖S‖² ≤ (1/b²) · b · Σ w_k² ‖v_k‖² = (1/b) · Σ w_k² ‖v_k‖²
  have h_scaled : ((1 / (b : ℝ))^2) * ‖∑ k, phases k * ((weightFunction b k x : ℂ) * vals k)‖^2
      ≤ ((1 / (b : ℝ))^2) * ((b : ℝ) * ∑ k, (weightFunction b k x)^2 * ‖vals k‖^2) :=
    mul_le_mul_of_nonneg_left h_sum_bound (by positivity)
  calc (1 / (b : ℝ))^2 * ‖∑ k, phases k * ((weightFunction b k x : ℂ) * vals k)‖^2
      ≤ (1 / (b : ℝ))^2 * ((b : ℝ) * ∑ k, (weightFunction b k x)^2 * ‖vals k‖^2) := h_scaled
    _ = (1 / (b : ℝ)) * ∑ k, (weightFunction b k x)^2 * ‖vals k‖^2 := by
        field_simp

/-- Pointwise norm-squared bound on `transferOperatorAction`'s output,
    for any unit-modulus phase family.

    Plumbs `transferOperator_pointwise_norm_sq_bound` (the abstract
    pointwise estimate) onto the concrete structural `toFun` field
    of `transferOperatorAction` from `PF/TransferOperator.lean`.

    The structural definition unfolds to exactly the abstract pattern
    $\frac{1}{b}\sum_k \omega_k \cdot w_k(x) \cdot f(y_k(x))$, with the
    inverse-branch bounds proof inline; here we extract the abstract
    pointwise bound at each $x \in [0, 1]$.

    Combined with the Radon-Nikodym identity
    `weight_squared_times_inverseBranch` (which gives
    $w_k(x)^2 = x / y_k(x)$ on the active domain), and integration
    against $d\mu_{\log}(x) = dx/x$ plus the change-of-variables
    formula per branch, this yields the Mayer 1991 bound
    $\|T_b f\|_{L^2(d\mu_{\log})} \le \|f\|_{L^2(d\mu_{\log})}$. -/
theorem transferOperatorAction_norm_sq_bound (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : LogWeightedL2) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ‖(transferOperatorAction b phases f).toFun ⟨x, hx⟩‖^2
      ≤ (1 / (b : ℝ)) * ∑ k, (weightFunction b k x)^2 *
          ‖f.toFun ⟨inverseBranch b k x,
              inverseBranch_image_in_unit_interval b k x hx⟩‖^2 := by
  -- Unfold transferOperatorAction's toFun: it's the pattern
  -- (1/b) · Σ ω_k · w_k(x) · f(y_k(x)) that our abstract bound applies to.
  -- Need to massage left-assoc multiplication to match the abstract bound's
  -- right-assoc parenthesisation `phases k * (weightFunction k x · vals k)`.
  unfold transferOperatorAction
  simp only
  -- Rewrite the LHS sum to match the abstract bound's parenthesisation
  -- (phases k * w * f → phases k * (w * f) via mul_assoc inside Σ)
  have heq : (1 / (b : ℂ)) * ∑ k, phases k * (weightFunction b k x : ℂ) *
                  f.toFun ⟨inverseBranch b k x,
                    inverseBranch_image_in_unit_interval b k x hx⟩
           = (1 / (b : ℂ)) * ∑ k, phases k * ((weightFunction b k x : ℂ) *
                  f.toFun ⟨inverseBranch b k x,
                    inverseBranch_image_in_unit_interval b k x hx⟩) := by
    congr 1
    apply Finset.sum_congr rfl
    intros k _; ring
  rw [heq]
  exact transferOperator_pointwise_norm_sq_bound b hb phases hphases x
    (fun k => f.toFun ⟨inverseBranch b k x,
      inverseBranch_image_in_unit_interval b k x hx⟩)

/-! ## Conditional Mayer 1991 Bound (Phase A integration arithmetic)

The arithmetic skeleton of the Mayer 1991 operator-norm estimate. The
real-number inequality below is what the integration step reduces to
once mathlib's change-of-variables formula is applied per branch.

Concretely, the integration step shows:

  $\|T_b f\|^2_{L^2(d\mu_{\log})} \le (1/b) \sum_k \int_0^1 w_k(x)^2 \cdot \|f(y_k(x))\|^2 \, d\mu_{\log}(x)$

(via `lintegral_mono` applied to the pointwise bound), and the per-branch
change-of-variables shows:

  $\int_0^1 w_k(x)^2 \cdot \|f(y_k(x))\|^2 \, d\mu_{\log}(x) = b \cdot \int_{k/b}^{(k+1)/b} \|f(u)\|^2 \, d\mu_{\log}(u)$

(via `MeasurePreserving.lintegral_comp` with the affine map $y_k$).
Summing over $k$ and using the partition $[0, 1] = \cup_k [k/b, (k+1)/b]$
gives $\sum_k = b \cdot \|f\|^2_{L^2(d\mu_{\log})}$. The arithmetic
combination $(1/b) \cdot b = 1$ then yields $\|T_b f\|^2 \le \|f\|^2$.

The lemma below captures this arithmetic combination as a real-number
identity, abstracting away from the integration. -/

/-- Arithmetic skeleton of the Mayer 1991 bound: given a per-branch
    decomposition `lhs ≤ (1/b) Σ_k branch_k` and a partition
    `Σ_k branch_k = b · target`, conclude `lhs ≤ target`.

    Discharge: substitute `Σ_k branch_k` by `b · target` in the
    pointwise bound, then simplify $(1/b) \cdot b \cdot t = t$
    via `field_simp`. -/
theorem mayer_bound_arithmetic
    {b : ℕ} (hb : b ≥ 1)
    {lhs : ℝ} {branch : Fin b → ℝ} {target : ℝ}
    (h_pointwise_integrated : lhs ≤ (1 / (b : ℝ)) * ∑ k, branch k)
    (h_partition_with_CoV : ∑ k, branch k = (b : ℝ) * target) :
    lhs ≤ target := by
  rw [h_partition_with_CoV] at h_pointwise_integrated
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)
  have h_simp : (1 / (b : ℝ)) * ((b : ℝ) * target) = target := by
    field_simp
  linarith

/-- The inverse branch is `AEStronglyMeasurable` with respect to
    `logWeightedMeasure`. This is the form mathlib's `MemLp` predicate
    consumes; the future Phase A `MemLp` proof of
    `transferOperatorAction`'s output requires the constituent maps in
    this form. -/
theorem inverseBranch_aestronglyMeasurable (b : ℕ) (k : Fin b)
    (hb : (b : ℝ) ≠ 0) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : ℝ => inverseBranch b k x) logWeightedMeasure :=
  (inverseBranch_continuous b k hb).aestronglyMeasurable

/-- The expanding map is `AEStronglyMeasurable` with respect to
    `logWeightedMeasure`. -/
theorem expandingMap_aestronglyMeasurable (b : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : ℝ => expandingMap b x) logWeightedMeasure :=
  (expandingMap_measurable b).aestronglyMeasurable

/-- The weight function is `AEStronglyMeasurable` with respect to
    `logWeightedMeasure`. -/
theorem weightFunction_aestronglyMeasurable (b : ℕ) (k : Fin b) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : ℝ => weightFunction b k x) logWeightedMeasure :=
  (weightFunction_measurable b k).aestronglyMeasurable

/-- The unit half-open interval $[0, 1)$ decomposes as the union of the
    per-branch image intervals $[k/b, (k+1)/b)$ for $k \in \mathrm{Fin}\, b$.

    Geometric partition fact, prerequisite for the integration partition.
    The `Ico` formulation is genuinely disjoint (no boundary overlap)
    making it the natural input to `lintegral_iUnion`.

    Forward (`x ∈ [0, 1) → ∃ k, x ∈ [k/b, (k+1)/b)`): set
    $k := \lfloor b \cdot x \rfloor$. Then $0 \le k < b$ since $0 \le bx < b$,
    and $k \le bx < k+1$ implies $k/b \le x < (k+1)/b$.

    Reverse: from $k/b \le x$ with $k \ge 0$ get $x \ge 0$;
    from $x < (k+1)/b$ with $k+1 \le b$ get $x < 1$. -/
theorem unitInterval_eq_iUnion_Ico_partition (b : ℕ) (hb : b ≥ 1) :
    Set.Ico (0:ℝ) 1
      = ⋃ k : Fin b, Set.Ico ((k : ℝ) / (b : ℝ)) (((k : ℝ) + 1) / (b : ℝ)) := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := Nat.lt_of_lt_of_le Nat.zero_lt_one hb
    exact_mod_cast this
  ext x
  simp only [Set.mem_Ico, Set.mem_iUnion]
  constructor
  · rintro ⟨hx0, hx1⟩
    have hbx_nonneg : (0 : ℝ) ≤ (b : ℝ) * x := mul_nonneg hb_pos.le hx0
    have hbx_lt : (b : ℝ) * x < (b : ℝ) := by
      calc (b : ℝ) * x
          < (b : ℝ) * 1 := mul_lt_mul_of_pos_left hx1 hb_pos
        _ = (b : ℝ) := mul_one _
    set k : ℕ := ⌊((b : ℝ) * x)⌋₊ with hk_def
    have hk_lt_b : k < b := by
      rw [hk_def, Nat.floor_lt hbx_nonneg]
      exact_mod_cast hbx_lt
    have hk_le : (k : ℝ) ≤ (b : ℝ) * x := by
      rw [hk_def]; exact Nat.floor_le hbx_nonneg
    have hk_succ_gt : (b : ℝ) * x < (k : ℝ) + 1 := by
      rw [hk_def]; exact Nat.lt_floor_add_one _
    refine ⟨⟨k, hk_lt_b⟩, ?_, ?_⟩
    · rw [div_le_iff₀ hb_pos]; linarith
    · rw [lt_div_iff₀ hb_pos]; linarith
  · rintro ⟨k, hk0, hk1⟩
    have hk_div_nonneg : (0 : ℝ) ≤ (k.val : ℝ) / (b : ℝ) :=
      div_nonneg (by exact_mod_cast Nat.zero_le _) hb_pos.le
    have hk_succ_le_one : ((k.val : ℝ) + 1) / (b : ℝ) ≤ 1 := by
      rw [div_le_one hb_pos]
      have : k.val + 1 ≤ b := k.isLt
      exact_mod_cast this
    exact ⟨by linarith, by linarith⟩

/-- The per-branch image intervals $[k/b, (k+1)/b)$ are pairwise disjoint
    over $k \in \mathrm{Fin}\, b$.

    For distinct $k, k' \in \mathrm{Fin}\, b$, WLOG $k < k'$ as naturals,
    so $k + 1 \le k'$, hence $(k+1)/b \le k'/b$ (with $b > 0$). The two
    intervals $[k/b, (k+1)/b)$ and $[k'/b, (k'+1)/b)$ are then disjoint
    via mathlib's `Set.Ico_disjoint_Ico` criterion
    `min a₂ b₂ ≤ max a₁ b₁`.

    Combined with `unitInterval_eq_iUnion_Ico_partition` (this commit
    chain), this is the data `lintegral_iUnion` consumes to give the
    integration partition $\int_{[0,1)} = \sum_k \int_{[k/b, (k+1)/b)}$. -/
theorem pairwiseDisjoint_Ico_partition (b : ℕ) (hb : (0 : ℝ) < (b : ℝ)) :
    Pairwise (Disjoint on (fun k : Fin b =>
        Set.Ico ((k : ℝ) / (b : ℝ)) (((k : ℝ) + 1) / (b : ℝ)))) := by
  intro k k' hkk'
  simp only [Function.onFun]
  rw [Set.Ico_disjoint_Ico]
  have hval_ne : k.val ≠ k'.val := fun h => hkk' (Fin.ext h)
  rcases lt_or_gt_of_ne hval_ne with h | h
  · -- k.val < k'.val
    have h1 : ((k.val : ℝ) + 1) ≤ (k'.val : ℝ) := by exact_mod_cast h
    have hk_succ_le : ((k.val : ℝ) + 1) / (b : ℝ) ≤ ((k'.val : ℝ) + 1) / (b : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hb.le
    have hk_le : ((k.val : ℝ)) / (b : ℝ) ≤ ((k'.val : ℝ)) / (b : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_of_lt h) hb.le
    rw [min_eq_left hk_succ_le, max_eq_right hk_le]
    exact div_le_div_of_nonneg_right h1 hb.le
  · -- k.val > k'.val: symmetric
    have h1 : ((k'.val : ℝ) + 1) ≤ (k.val : ℝ) := by exact_mod_cast h
    have hk_succ_le : ((k'.val : ℝ) + 1) / (b : ℝ) ≤ ((k.val : ℝ) + 1) / (b : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hb.le
    have hk_le : ((k'.val : ℝ)) / (b : ℝ) ≤ ((k.val : ℝ)) / (b : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_of_lt h) hb.le
    rw [min_eq_right hk_succ_le, max_eq_left hk_le]
    exact div_le_div_of_nonneg_right h1 hb.le

/-- The lintegral partition identity for the unit interval:

      $\int_{[0, 1)} g(y)\, \mathrm{dvolume}
        = \sum_{k=0}^{b-1} \int_{[k/b,\, (k+1)/b)} g(y)\, \mathrm{dvolume}$

    for any (possibly non-measurable) integrand $g : \mathbb{R} \to \mathbb{R}_{\ge 0}^\infty$
    and any $b \ge 1$.

    Composes:
      1. `unitInterval_eq_iUnion_Ico_partition` (commit 76f8246) — the
         set equality $[0, 1) = \bigcup_k [k/b, (k+1)/b)$.
      2. `pairwiseDisjoint_Ico_partition` (commit d2b04ae) — the
         pairwise disjointness of the family.
      3. `lintegral_iUnion` (mathlib) — converts the integral over the
         union to a tsum of integrals over the parts.
      4. `tsum_fintype` (mathlib) — converts the tsum over the
         finite type `Fin b` to a `Finset.sum`.

    This is the **partition identity** at the integration level. Combined
    with `inverseBranch_set_lintegral_change_of_variables` (commit
    28a669a) and the Radon-Nikodym identity `weight_squared_eq_jacobian`
    (commit 257726c), this completes the analytic ingredients to
    integrate the pointwise transfer-operator bound and obtain
    $\|T_b f\|_2 \le \|f\|_2$. -/
theorem lintegral_unitInterval_eq_sum_Ico_partition
    (b : ℕ) (hb : b ≥ 1) (g : ℝ → ENNReal) :
    ∫⁻ y in Set.Ico (0:ℝ) 1, g y ∂volume
      = ∑ k : Fin b, ∫⁻ y in Set.Ico ((k : ℝ) / (b : ℝ)) (((k : ℝ) + 1) / (b : ℝ)),
                       g y ∂volume := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := Nat.lt_of_lt_of_le Nat.zero_lt_one hb
    exact_mod_cast this
  -- Step 1: Rewrite [0,1) as the iUnion of per-branch images.
  rw [unitInterval_eq_iUnion_Ico_partition b hb]
  -- Step 2: Apply lintegral_iUnion (measurable + pairwise disjoint).
  rw [lintegral_iUnion (fun _ => measurableSet_Ico)
        (pairwiseDisjoint_Ico_partition b hb_pos) g]
  -- Step 3: tsum on Fin b (a Fintype) collapses to a Finset.sum.
  exact tsum_fintype _

/-- The preimage of the per-branch image $[k/b, (k+1)/b)$ under
    $y_k(x) = (x+k)/b$ is exactly the unit half-open interval $[0, 1)$.

    $(x+k)/b \in [k/b, (k+1)/b) \iff k \le x+k < k+1 \iff 0 \le x < 1$
    (for $b > 0$, dividing/multiplying by $b$ preserves order).

    This is the geometric link between the per-branch CoV (which restricts
    on the source side via a preimage) and the unit-interval target form
    needed by the operator-norm bound. -/
theorem inverseBranch_preimage_Ico_image (b : ℕ) (k : Fin b)
    (hb : (0 : ℝ) < (b : ℝ)) :
    inverseBranch b k ⁻¹' Set.Ico ((k : ℝ) / (b : ℝ)) (((k : ℝ) + 1) / (b : ℝ))
      = Set.Ico (0:ℝ) 1 := by
  unfold inverseBranch
  ext x
  simp only [Set.mem_preimage, Set.mem_Ico,
             div_le_div_iff_of_pos_right hb, div_lt_div_iff_of_pos_right hb]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The per-branch CoV specialized to the unit interval source:

      $\int_{[0, 1)} h(y_k(y))\, \mathrm{dvolume}(y)
        = b \cdot \int_{[k/b, (k+1)/b)} h(u)\, \mathrm{dvolume}(u)$

    Composes `inverseBranch_set_lintegral_change_of_variables`
    (commit 28a669a) with the preimage identity
    `inverseBranch_preimage_Ico_image` (this commit). The unit-interval
    source [0, 1) on the LHS lines up with the operator-norm integration
    domain; the per-branch image [k/b, (k+1)/b) on the RHS lines up with
    the partition pieces from `lintegral_unitInterval_eq_sum_Ico_partition`
    (commit bf8c69f). Together: the per-branch piece of the operator-norm
    bound, ready for the partition reassembly. -/
theorem branch_lintegral_unitInterval_to_Ico
    (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0) (hb_ge : b ≥ 1) (h : ℝ → ENNReal) :
    ∫⁻ y in Set.Ico (0:ℝ) 1, h (inverseBranch b k y) ∂volume
      = ENNReal.ofReal (b : ℝ)
          * ∫⁻ u in Set.Ico ((k : ℝ) / (b : ℝ)) (((k : ℝ) + 1) / (b : ℝ)),
              h u ∂volume := by
  have hb_pos : (0 : ℝ) < (b : ℝ) :=
    lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hb)
  rw [← inverseBranch_preimage_Ico_image b k hb_pos]
  exact inverseBranch_set_lintegral_change_of_variables b k hb hb_ge _ h

/-- The combined per-branch sum identity over the unit interval:

      $\sum_{k=0}^{b-1} \int_{[0, 1)} h(y_k(y))\, \mathrm{dvolume}(y)
        = b \cdot \int_{[0, 1)} h(y)\, \mathrm{dvolume}(y)$.

    Composes:
      1. `branch_lintegral_unitInterval_to_Ico` (commit e4cc6b9), applied
         under the sum, replaces each summand by
         `b * ∫⁻ in [k/b, (k+1)/b), h`.
      2. `Finset.mul_sum` extracts the constant factor `b`.
      3. `lintegral_unitInterval_eq_sum_Ico_partition` (commit bf8c69f),
         used in reverse, collapses the per-branch sum into a single
         integral over [0, 1).

    This is the **summed per-branch identity** in the operator-norm chain.
    For the transfer operator $T_b f(y) = (1/b) \sum_k \omega_k\, w_k(y)\, f(y_k(y))$,
    the integral $\int_{[0,1)} \|T_b f\|^2 (1/y)\, dy$ — after the
    pointwise Cauchy-Schwarz bound and the Radon-Nikodym substitution —
    reduces to $\sum_k \int_{[0,1)} (1/(y+k)) |f(y_k(y))|^2\, dy$, and a
    suitable rewrite of $1/(y+k) = w_k(y)^2/y$ followed by this lemma
    closes the bound to $\|f\|^2$. -/
theorem sum_branch_lintegral_unitInterval_eq_b_lintegral
    (b : ℕ) (hb : b ≥ 1) (h : ℝ → ENNReal) :
    ∑ k : Fin b, ∫⁻ y in Set.Ico (0:ℝ) 1, h (inverseBranch b k y) ∂volume
      = ENNReal.ofReal (b : ℝ)
          * ∫⁻ y in Set.Ico (0:ℝ) 1, h y ∂volume := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := Nat.lt_of_lt_of_le Nat.zero_lt_one hb
    exact_mod_cast this
  have hb_ne : (b : ℝ) ≠ 0 := hb_pos.ne'
  -- Step 1: Replace each summand using branch_lintegral_unitInterval_to_Ico.
  rw [Finset.sum_congr rfl
        (fun k _ => branch_lintegral_unitInterval_to_Ico b k hb_ne hb h)]
  -- Goal: ∑ k, b * ∫⁻ in [k/b, (k+1)/b) = b * ∫⁻ in [0, 1)
  -- Step 2: Pull out the constant `b` via Finset.mul_sum.
  rw [← Finset.mul_sum]
  -- Step 3: Collapse the sum via the partition identity (in reverse).
  rw [← lintegral_unitInterval_eq_sum_Ico_partition b hb h]

/-- The integrated form of the summed per-branch identity:

      $\int_{[0, 1)} \Bigl(\sum_{k=0}^{b-1} h(y_k(y))\Bigr)\, \mathrm{dvolume}(y)
        = b \cdot \int_{[0, 1)} h(y)\, \mathrm{dvolume}(y)$

    Same content as `sum_branch_lintegral_unitInterval_eq_b_lintegral`
    (commit d2c6487), but with the per-branch sum **inside** the integral.
    This is the form the operator-norm chain consumes after distributing
    the Radon-Nikodym factor $w_k(y)^2/y = b/(y+k)$ across the branches.

    Composes:
      1. `lintegral_finset_sum` (mathlib) — commutes Finset.sum with
         lintegral, given measurability of each summand
         `h ∘ inverseBranch b k` (via `Measurable.comp` on
         `inverseBranch_measurable`, commit ab98579).
      2. `sum_branch_lintegral_unitInterval_eq_b_lintegral` (commit d2c6487)
         — the summed identity in its sum-outside form.

    The `Measurable h` hypothesis will dissolve in the eventual
    operator-norm proof, where `h` is `‖f‖²` for `f` in the L² space
    (automatically AE-strongly-measurable). -/
theorem lintegral_sum_branch_compose_unitInterval_eq_b_lintegral
    (b : ℕ) (hb : b ≥ 1) (h : ℝ → ENNReal) (hh : Measurable h) :
    ∫⁻ y in Set.Ico (0:ℝ) 1, (∑ k : Fin b, h (inverseBranch b k y)) ∂volume
      = ENNReal.ofReal (b : ℝ) * ∫⁻ y in Set.Ico (0:ℝ) 1, h y ∂volume := by
  -- Step 1: Commute Finset.sum with lintegral via linearity.
  --   The cast through `Eq.trans` (rather than `rw`) avoids an eta-expansion
  --   mismatch on the implicit `f` argument of `lintegral_finset_sum`.
  have step1 : ∫⁻ y in Set.Ico (0:ℝ) 1,
                  (∑ k : Fin b, h (inverseBranch b k y)) ∂volume
             = ∑ k : Fin b,
                  ∫⁻ y in Set.Ico (0:ℝ) 1, h (inverseBranch b k y) ∂volume :=
    lintegral_finset_sum Finset.univ
      (fun k _ => hh.comp (inverseBranch_measurable b k hb))
  -- Step 2: Apply the summed identity (sum-outside form).
  rw [step1, sum_branch_lintegral_unitInterval_eq_b_lintegral b hb h]

/-- The Radon-Nikodym integrand identity at the lintegral level: on the
    open unit interval (0, 1), the weight-squared-over-$y$ integrand
    against $h \circ y_k$ equals the simpler $1/y_k(y)$ integrand
    against $h \circ y_k$.

      $\int_{(0, 1)} \frac{w_k(y)^2}{y}\, h(y_k(y))\, \mathrm{dvolume}(y)
        = \int_{(0, 1)} \frac{1}{y_k(y)}\, h(y_k(y))\, \mathrm{dvolume}(y)$.

    Proof composes two pointwise facts on $(0, 1)$:
      1. `weight_squared_eq_jacobian` (commit 257726c) — the
         Radon-Nikodym identity $w_k(y)^2/y = b/(y + k)$ on
         $\{y > 0\} \cap \{y + k > 0\}$ (both hold for $y \in (0, 1)$,
         $k \in \mathrm{Fin}\, b$, since $k \ge 0$).
      2. The algebraic identity $b/(y + k) = 1/y_k(y)$ since
         $y_k(y) = (y + k)/b$, via `one_div_div` (mathlib).

    Lift to `ENNReal` via `setLIntegral_congr_fun` on `measurableSet_Ioo`.

    This is the **integrand-level Radon-Nikodym substitution** in the
    operator-norm chain: it lets the per-branch contribution of
    `‖T_b f‖²` against `dμ_log = (1/y) dy` be rewritten in the form
    `(1/y_k(y)) · h(y_k(y))`, ready for the summed per-branch identity
    (commit 88d7baf) once we recognize the integrand as `g(y_k(y))`
    with `g(u) = (1/u) · h(u)`. -/
theorem lintegral_weight_squared_branch_eq_jacobian_subst
    (b : ℕ) (k : Fin b) (h : ℝ → ENNReal) :
    ∫⁻ y in Set.Ioo (0:ℝ) 1,
        ENNReal.ofReal ((weightFunction b k y)^2 / y) *
          h (inverseBranch b k y) ∂volume
      = ∫⁻ y in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal (1 / inverseBranch b k y) *
            h (inverseBranch b k y) ∂volume := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro y hy
  have hy_pos : y > 0 := hy.1
  have hyk_pos : y + (k.val : ℝ) > 0 := by
    have : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
    linarith
  have key : (weightFunction b k y)^2 / y = 1 / inverseBranch b k y := by
    rw [weight_squared_eq_jacobian b k y hy_pos hyk_pos]
    unfold inverseBranch
    rw [one_div_div]
  show ENNReal.ofReal ((weightFunction b k y)^2 / y) * h (inverseBranch b k y)
     = ENNReal.ofReal (1 / inverseBranch b k y) * h (inverseBranch b k y)
  rw [key]

/-- The combined Mayer-1991 chain identity: the weighted per-branch sum
    of integrals reduces to `b` times the log-weighted integral of `h`.

      $\sum_{k=0}^{b-1} \int_{(0, 1)} \frac{w_k(y)^2}{y}\, h(y_k(y))\, \mathrm{dvolume}(y)
        = b \cdot \int_{(0, 1)} \frac{1}{u}\, h(u)\, \mathrm{dvolume}(u)$

    Composes four facts:
      1. `lintegral_weight_squared_branch_eq_jacobian_subst` (commit 0befd95)
         — applied per-summand under `Finset.sum_congr` to substitute
         `(w_k y)²/y · h(y_k y) → (1/y_k y) · h(y_k y)`.
      2. `setLIntegral_congr` with `Ioo_ae_eq_Ico` (mathlib) — bridges
         each summand from $(0, 1)$ to $[0, 1)$ (the partition's domain).
      3. `sum_branch_lintegral_unitInterval_eq_b_lintegral` (commit d2c6487)
         — the summed per-branch identity on $[0, 1)$, applied with
         `g(u) := \mathrm{ofReal}(1/u) \cdot h(u)`. Collapses the sum
         to $b \cdot \int_{[0,1)} g$.
      4. `setLIntegral_congr` with `Ioo_ae_eq_Ico.symm` — bridges the
         RHS back from $[0, 1)$ to $(0, 1)$ to match the goal statement.

    With $h = |f|^2$, the RHS is $b \cdot \|f\|^2_{L^2(d\mu_{\log})}$
    (modulo the $1/b$ in $T_b$'s prefactor). This is the **last
    analytic identity** in the operator-norm chain — combined with the
    pointwise bound `transferOperator_pointwise_norm_sq_bound`
    (commit 6c4ea9c), the Mayer-1991 estimate
    $\|T_b f\|_2 \le \|f\|_2$ now reduces to algebraic plumbing
    around the $(1/b)$ prefactor and lifting the real pointwise
    inequality to ENNReal. -/
theorem lintegral_sum_weight_squared_branch_eq_b_lintegral_inv
    (b : ℕ) (hb : b ≥ 1) (h : ℝ → ENNReal) :
    ∑ k : Fin b, ∫⁻ y in Set.Ioo (0:ℝ) 1,
        ENNReal.ofReal ((weightFunction b k y)^2 / y) *
          h (inverseBranch b k y) ∂volume
      = ENNReal.ofReal (b : ℝ)
          * ∫⁻ u in Set.Ioo (0:ℝ) 1,
              ENNReal.ofReal (1 / u) * h u ∂volume := by
  calc ∑ k : Fin b, ∫⁻ y in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal ((weightFunction b k y)^2 / y) *
            h (inverseBranch b k y) ∂volume
      = ∑ k : Fin b, ∫⁻ y in Set.Ioo (0:ℝ) 1,
            ENNReal.ofReal (1 / inverseBranch b k y) *
              h (inverseBranch b k y) ∂volume :=
        Finset.sum_congr rfl
          (fun k _ => lintegral_weight_squared_branch_eq_jacobian_subst b k h)
    _ = ∑ k : Fin b, ∫⁻ y in Set.Ico (0:ℝ) 1,
            ENNReal.ofReal (1 / inverseBranch b k y) *
              h (inverseBranch b k y) ∂volume :=
        Finset.sum_congr rfl (fun k _ => setLIntegral_congr Ioo_ae_eq_Ico)
    _ = ENNReal.ofReal (b : ℝ) *
            ∫⁻ y in Set.Ico (0:ℝ) 1, ENNReal.ofReal (1 / y) * h y ∂volume :=
        sum_branch_lintegral_unitInterval_eq_b_lintegral b hb
          (fun u => ENNReal.ofReal (1 / u) * h u)
    _ = ENNReal.ofReal (b : ℝ) *
            ∫⁻ u in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (1 / u) * h u ∂volume := by
          congr 1
          exact setLIntegral_congr (Filter.EventuallyEq.symm Ioo_ae_eq_Ico)

/-- The $(1/b)$-normalized combined Mayer-1991 identity:

      $\frac{1}{b} \cdot \sum_{k=0}^{b-1} \int_{(0, 1)} \frac{w_k(y)^2}{y}\,
            h(y_k(y))\, \mathrm{dvolume}(y)
        = \int_{(0, 1)} \frac{1}{u}\, h(u)\, \mathrm{dvolume}(u)$

    The form that directly matches the $(1/b)$ prefactor in the
    pointwise bound `transferOperator_pointwise_norm_sq_bound`
    (commit 6c4ea9c). Multiplies both sides of
    `lintegral_sum_weight_squared_branch_eq_b_lintegral_inv`
    (commit ab41c4e) by $(\mathrm{ofReal}\, b)^{-1}$ and uses
    `ENNReal.inv_mul_cancel` ($b > 0$, $b < \infty$) to cancel.

    With $h := |f|^2$, the LHS is exactly the integrated form of the
    pointwise bound's right-hand side against $d\mu_{\log} = (1/y)\,dy$,
    and the RHS is $\|f\|^2$ in the log-weighted norm. The remaining
    work for $\|T_b f\|_2 \le \|f\|_2$ is just lifting the real
    pointwise inequality to ENNReal and integrating. -/
theorem lintegral_one_div_b_sum_weight_squared_branch_eq_lintegral_inv
    (b : ℕ) (hb : b ≥ 1) (h : ℝ → ENNReal) :
    (ENNReal.ofReal (b : ℝ))⁻¹ *
        (∑ k : Fin b, ∫⁻ y in Set.Ioo (0:ℝ) 1,
            ENNReal.ofReal ((weightFunction b k y)^2 / y) *
              h (inverseBranch b k y) ∂volume)
      = ∫⁻ u in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal (1 / u) * h u ∂volume := by
  have hb_real_pos : (0:ℝ) < (b:ℝ) := by
    have : 0 < b := Nat.lt_of_lt_of_le Nat.zero_lt_one hb
    exact_mod_cast this
  have hne_zero : ENNReal.ofReal (b : ℝ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hb_real_pos).ne'
  have hne_top : ENNReal.ofReal (b : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [lintegral_sum_weight_squared_branch_eq_b_lintegral_inv b hb h,
      ← mul_assoc, ENNReal.inv_mul_cancel hne_zero hne_top, one_mul]

/-- The integrated form of the pointwise transfer-operator bound,
    against the log-weighted density `1/x` over $(0, 1)$:

      $\int_{(0, 1)} \bigl\|\tfrac{1}{b} \sum_k \omega_k\, w_k(x)\, f(y_k(x))\bigr\|^2 \cdot \frac{1}{x}\, \mathrm{dvolume}(x)
        \le \int_{(0, 1)} \tfrac{1}{b} \sum_k w_k(x)^2 \cdot |f(y_k(x))|^2 \cdot \frac{1}{x}\, \mathrm{dvolume}(x)$.

    This is the **integrated form** of the Cauchy-Schwarz pointwise
    bound on the transfer operator action. Lifts
    `transferOperator_pointwise_norm_sq_bound` (commit 6c4ea9c) from
    real to `ENNReal` via `ENNReal.ofReal_le_ofReal`, then applies
    monotonicity of multiplication by `ofReal (1/x)` followed by
    `lintegral_mono`.

    Combined with
    `lintegral_one_div_b_sum_weight_squared_branch_eq_lintegral_inv`
    (commit a3960ce), the RHS becomes (after distributing `(1/x)`
    inside the sum and recognizing the `(w_k x)²/x` factor)
    exactly $\int_{(0,1)} \frac{1}{u}\, |f(u)|^2\, \mathrm{dvolume}(u) = \|f\|^2$
    in the log-weighted norm. The remaining work is the algebraic
    distribution of the `(1/x)` factor inside the sum on the RHS. -/
theorem lintegral_transferOp_pointwise_bound_log_weighted
    (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : ℝ → ℂ) :
    ∫⁻ x in Set.Ioo (0:ℝ) 1,
        ENNReal.ofReal (‖(1 / (b : ℂ)) *
            ∑ k, phases k *
              ((weightFunction b k x : ℂ) * f (inverseBranch b k x))‖^2) *
          ENNReal.ofReal (1 / x) ∂volume
      ≤ ∫⁻ x in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal ((1 / (b : ℝ)) *
              ∑ k, (weightFunction b k x)^2 * ‖f (inverseBranch b k x)‖^2) *
            ENNReal.ofReal (1 / x) ∂volume := by
  apply lintegral_mono
  intro x
  apply mul_le_mul_right'
  exact ENNReal.ofReal_le_ofReal
    (transferOperator_pointwise_norm_sq_bound b hb phases hphases x
      (fun k => f (inverseBranch b k x)))

/-- Integrand identity bridging the pointwise bound's RHS to the form
    consumed by the (1/b)-normalized Mayer identity. For $x > 0$:

      $\mathrm{ofReal}\bigl(\tfrac{1}{b} \sum_k w_k(x)^2 \|v_k\|^2\bigr) \cdot \mathrm{ofReal}(1/x)
        = (\mathrm{ofReal}\, b)^{-1} \cdot \sum_k \mathrm{ofReal}(w_k(x)^2/x) \cdot \mathrm{ofReal}(\|v_k\|^2)$.

    Pure ENNReal arithmetic on top of mathlib lifts:
      * `ENNReal.ofReal_mul` (and reverse) for distributing/combining
        `ofReal` over real products of nonneg factors.
      * `ENNReal.ofReal_sum_of_nonneg` for distributing `ofReal` over
        a real Finset.sum of nonneg terms.
      * `ENNReal.ofReal_inv_of_pos` for `ofReal (1/b) = (ofReal b)⁻¹`
        when $b > 0$.
      * `Finset.sum_mul` for distributing the trailing `ofReal(1/x)`
        factor inside the sum.

    With $\|v_k\|^2 := \|f(y_k(x))\|^2$, the RHS is exactly the
    integrand of the LHS of `lintegral_one_div_b_sum_weight_squared_branch_eq_lintegral_inv`
    (commit a3960ce) — modulo the still-pending pulling-out of the
    constant $(\mathrm{ofReal}\, b)^{-1}$ and commuting Σ with ∫⁻. -/
theorem ofReal_one_div_b_sum_mul_ofReal_one_div_eq
    (b : ℕ) (hb : b ≥ 1) (x : ℝ) (hx_pos : x > 0)
    (vals : Fin b → ℂ) :
    ENNReal.ofReal ((1 / (b : ℝ)) *
        ∑ k, (weightFunction b k x)^2 * ‖vals k‖^2) *
      ENNReal.ofReal (1 / x)
      = (ENNReal.ofReal (b : ℝ))⁻¹ *
          ∑ k, ENNReal.ofReal ((weightFunction b k x)^2 / x) *
            ENNReal.ofReal (‖vals k‖^2) := by
  have hb_real_pos : (0:ℝ) < (b:ℝ) := by
    have : 0 < b := Nat.lt_of_lt_of_le Nat.zero_lt_one hb
    exact_mod_cast this
  have hone_div_b_nonneg : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  have hweight_sq_vals_sq_nonneg : ∀ k : Fin b,
      (0 : ℝ) ≤ (weightFunction b k x)^2 * ‖vals k‖^2 :=
    fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hweight_sq_div_x_nonneg : ∀ k : Fin b,
      (0 : ℝ) ≤ (weightFunction b k x)^2 / x :=
    fun k => div_nonneg (sq_nonneg _) hx_pos.le
  -- ofReal((1/b) · Σ a_k) → ofReal(1/b) · ofReal(Σ a_k)
  rw [ENNReal.ofReal_mul hone_div_b_nonneg]
  -- ofReal(Σ a_k) → Σ ofReal(a_k)
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hweight_sq_vals_sq_nonneg k)]
  -- ofReal(1/b) → (ofReal b)⁻¹
  rw [show ENNReal.ofReal (1 / (b : ℝ)) = (ENNReal.ofReal (b : ℝ))⁻¹ by
    rw [one_div, ENNReal.ofReal_inv_of_pos hb_real_pos]]
  -- (ofReal b)⁻¹ · (Σ ofReal a_k) · ofReal(1/x) → (ofReal b)⁻¹ · ((Σ ofReal a_k) · ofReal(1/x))
  rw [mul_assoc]
  -- (Σ ofReal a_k) · ofReal(1/x) → Σ (ofReal a_k · ofReal(1/x))
  rw [Finset.sum_mul]
  -- Per-summand cleanup
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  -- LHS summand:  ofReal((w_k x)² * ‖v_k‖²) * ofReal(1/x)
  -- RHS summand:  ofReal((w_k x)²/x) * ofReal(‖v_k‖²)
  rw [← ENNReal.ofReal_mul (hweight_sq_vals_sq_nonneg k),
      ← ENNReal.ofReal_mul (hweight_sq_div_x_nonneg k)]
  congr 1
  ring

/-- The integrated form of `ofReal_one_div_b_sum_mul_ofReal_one_div_eq`
    (commit 84ad7ac): integrating the pointwise identity over $(0, 1)$,
    pulling out the constant $(\mathrm{ofReal}\, b)^{-1}$, and commuting
    Σ with ∫⁻.

      $\int_{(0, 1)} \mathrm{ofReal}\bigl(\tfrac{1}{b}\sum_k w_k(x)^2 \|f(y_k x)\|^2\bigr) \cdot \mathrm{ofReal}(1/x)\, \mathrm{dvolume}
        = (\mathrm{ofReal}\, b)^{-1} \cdot
            \sum_k \int_{(0, 1)} \mathrm{ofReal}(w_k(x)^2/x) \cdot \mathrm{ofReal}(\|f(y_k x)\|^2)\, \mathrm{dvolume}$.

    Three-step chain:
      1. `setLIntegral_congr_fun` on `measurableSet_Ioo` substitutes the
         integrand using the pointwise identity (commit 84ad7ac).
      2. `lintegral_const_mul'` pulls $(\mathrm{ofReal}\, b)^{-1}$ outside
         the integral (needs $(\mathrm{ofReal}\, b)^{-1} \ne \infty$,
         from $b > 0$ via `ENNReal.inv_ne_top`).
      3. `lintegral_finset_sum` commutes Σ with ∫⁻ (needs measurability
         of each summand, established via composition of
         `weightFunction_measurable`, `ENNReal.continuous_ofReal.measurable`,
         `Measurable.norm`, `Measurable.pow_const`, `Measurable.div`,
         and `inverseBranch_measurable`).

    The RHS is exactly the LHS of
    `lintegral_one_div_b_sum_weight_squared_branch_eq_lintegral_inv`
    (commit a3960ce) instantiated with $h(u) := \mathrm{ofReal}(\|f(u)\|^2)$.
    Composing with a3960ce closes the operator-norm chain. -/
theorem lintegral_one_div_b_sum_weight_squared_vals_sq_eq_inv_mul_sum_lintegral
    (b : ℕ) (hb : b ≥ 1) (f : ℝ → ℂ) (hf : Measurable f) :
    ∫⁻ x in Set.Ioo (0:ℝ) 1,
        ENNReal.ofReal ((1 / (b : ℝ)) *
            ∑ k, (weightFunction b k x)^2 * ‖f (inverseBranch b k x)‖^2) *
          ENNReal.ofReal (1 / x) ∂volume
      = (ENNReal.ofReal (b : ℝ))⁻¹ *
          ∑ k : Fin b, ∫⁻ x in Set.Ioo (0:ℝ) 1,
              ENNReal.ofReal ((weightFunction b k x)^2 / x) *
                ENNReal.ofReal (‖f (inverseBranch b k x)‖^2) ∂volume := by
  have hb_real_pos : (0:ℝ) < (b:ℝ) := by
    have : 0 < b := Nat.lt_of_lt_of_le Nat.zero_lt_one hb
    exact_mod_cast this
  have h_inv_ne_top : (ENNReal.ofReal (b : ℝ))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hb_real_pos).ne'
  -- Step 1: substitute integrand via pointwise identity (commit 84ad7ac)
  rw [setLIntegral_congr_fun measurableSet_Ioo
        (fun x hx => ofReal_one_div_b_sum_mul_ofReal_one_div_eq b hb x hx.1
          (fun k => f (inverseBranch b k x)))]
  -- Step 2: pull constant `(ofReal b)⁻¹` out of integral
  rw [lintegral_const_mul' _ _ h_inv_ne_top]
  -- Step 3: commute Σ and ∫⁻
  congr 1
  rw [lintegral_finset_sum]
  intro k _
  refine Measurable.mul ?_ ?_
  · exact ENNReal.continuous_ofReal.measurable.comp
      (((weightFunction_measurable b k).pow_const 2).div measurable_id)
  · exact ENNReal.continuous_ofReal.measurable.comp
      ((hf.comp (inverseBranch_measurable b k hb)).norm.pow_const 2)

/-- **Mayer 1991 operator-norm bound** in lintegral form, against the
    log-weighted measure $d\mu_{\log} = (1/x)\, dx$ on $(0, 1)$:

      $\int_{(0, 1)} \bigl\|\tfrac{1}{b} \sum_k \omega_k\, w_k(x)\, f(y_k(x))\bigr\|^2 \cdot \frac{1}{x}\, \mathrm{dvolume}(x)
        \le \int_{(0, 1)} \|f(u)\|^2 \cdot \frac{1}{u}\, \mathrm{dvolume}(u)$.

    This is the integrated form of $\|T_b f\|_2^2 \le \|f\|_2^2$ for
    the transfer operator
    $T_b f(x) := \tfrac{1}{b} \sum_k \omega_k \cdot w_k(x) \cdot f(y_k(x))$
    with unit-modulus phases $\|\omega_k\| = 1$.

    **Capstone of the Phase A analytic chain**, composing four steps:
      1. `lintegral_transferOp_pointwise_bound_log_weighted` (commit dc8cb14)
         — the integrated pointwise Cauchy-Schwarz bound:
         $\int_{(0,1)} \|T_b f\|^2 \cdot (1/x) \le \int_{(0,1)} \tfrac{1}{b} \sum_k w_k^2 \|f \circ y_k\|^2 \cdot (1/x)$.
      2. `lintegral_one_div_b_sum_weight_squared_vals_sq_eq_inv_mul_sum_lintegral`
         (commit 8038a01) — rewrites the RHS as
         $(\mathrm{ofReal}\, b)^{-1} \cdot \sum_k \int_{(0,1)} \mathrm{ofReal}(w_k^2/x) \cdot \mathrm{ofReal}(\|f \circ y_k\|^2)$.
      3. `lintegral_one_div_b_sum_weight_squared_branch_eq_lintegral_inv`
         (commit a3960ce) instantiated with $h(u) := \mathrm{ofReal}(\|f(u)\|^2)$
         — collapses to $\int_{(0,1)} \mathrm{ofReal}(1/u) \cdot \mathrm{ofReal}(\|f(u)\|^2)$.
      4. `setLIntegral_congr_fun` with `mul_comm` reorders the integrand
         to match the standard log-weighted-norm form.

    With the structural `transferOperatorAction` (commit ed0efbd) and
    once Phase A swaps `LogWeightedL2` for `MeasureTheory.Lp ℂ 2 logWeightedMeasure`,
    this lintegral form lifts directly to the operator-norm statement
    `‖T_b‖ ≤ 1`, retiring the `T3_self_adjoint_conj` axiom and closing
    the spectral framework's analytic foundation. -/
theorem mayer_1991_lintegral_norm_sq_bound_log_weighted
    (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : ℝ → ℂ) (hf : Measurable f) :
    ∫⁻ x in Set.Ioo (0:ℝ) 1,
        ENNReal.ofReal (‖(1 / (b : ℂ)) *
            ∑ k, phases k *
              ((weightFunction b k x : ℂ) * f (inverseBranch b k x))‖^2) *
          ENNReal.ofReal (1 / x) ∂volume
      ≤ ∫⁻ u in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal (‖f u‖^2) * ENNReal.ofReal (1 / u) ∂volume := by
  calc ∫⁻ x in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal (‖(1 / (b : ℂ)) *
              ∑ k, phases k *
                ((weightFunction b k x : ℂ) * f (inverseBranch b k x))‖^2) *
            ENNReal.ofReal (1 / x) ∂volume
      ≤ ∫⁻ x in Set.Ioo (0:ℝ) 1,
            ENNReal.ofReal ((1 / (b : ℝ)) *
                ∑ k, (weightFunction b k x)^2 * ‖f (inverseBranch b k x)‖^2) *
              ENNReal.ofReal (1 / x) ∂volume :=
        lintegral_transferOp_pointwise_bound_log_weighted b hb phases hphases f
    _ = (ENNReal.ofReal (b : ℝ))⁻¹ *
          ∑ k : Fin b, ∫⁻ x in Set.Ioo (0:ℝ) 1,
              ENNReal.ofReal ((weightFunction b k x)^2 / x) *
                ENNReal.ofReal (‖f (inverseBranch b k x)‖^2) ∂volume :=
        lintegral_one_div_b_sum_weight_squared_vals_sq_eq_inv_mul_sum_lintegral b hb f hf
    _ = ∫⁻ u in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal (1 / u) * ENNReal.ofReal (‖f u‖^2) ∂volume :=
        lintegral_one_div_b_sum_weight_squared_branch_eq_lintegral_inv b hb
          (fun u => ENNReal.ofReal (‖f u‖^2))
    _ = ∫⁻ u in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal (‖f u‖^2) * ENNReal.ofReal (1 / u) ∂volume := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro u _
        exact mul_comm _ _

/-- The log-weighted density `logWeightDensity` is Borel measurable.

    Mathematically: $\mathrm{logWeightDensity}(x) = \mathbf{1}_{x > 0} \cdot \mathrm{ofReal}(1/x)$,
    a measurable function on $\mathbb{R}$ via `Measurable.ite` over the
    measurable set $\{x \le 0\}$, with branches `measurable_const` and
    `ENNReal.continuous_ofReal.measurable.comp (measurable_const.div measurable_id)`. -/
theorem logWeightDensity_measurable : Measurable logWeightDensity := by
  unfold logWeightDensity
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  exact ENNReal.continuous_ofReal.measurable.comp
    (measurable_const.div measurable_id)

/-- **Bridge lemma**: integrating an `ENNReal`-valued integrand against
    `logWeightedMeasure` on $(0, 1)$ equals integrating it against
    `volume` with an explicit $\mathrm{ofReal}(1/x)$ factor:

      $\int_{(0, 1)} g(x)\, \mathrm{d}\mu_{\log}(x)
        = \int_{(0, 1)} g(x) \cdot \mathrm{ofReal}(1/x)\, \mathrm{dvolume}(x)$.

    Composes:
      1. `setLIntegral_withDensity_eq_setLIntegral_mul` (mathlib) on the
         density `logWeightDensity` (whose measurability is established
         in `logWeightDensity_measurable`) and the user's integrand `g`
         (`Measurable g` is a hypothesis).
      2. `setLIntegral_congr_fun` on `measurableSet_Ioo` rewrites the
         resulting `logWeightDensity x * g x` integrand to
         `g x * ofReal(1/x)` using $x > 0$ from $x \in (0, 1)$ to fire
         the else-branch of the if-then-else and `mul_comm` to swap factors.

    With this bridge, the Mayer 1991 lintegral bound (commit b8ee9a9)
    can be restated as $\int_{(0,1)} \|T_b f\|^2\, \mathrm{d}\mu_{\log}
    \le \int_{(0,1)} \|f\|^2\, \mathrm{d}\mu_{\log}$ — the form mathlib's
    `eLpNorm` consumes for the operator-norm statement once the L²
    structural swap lands. -/
theorem setLIntegral_Ioo_logWeightedMeasure_eq_setLIntegral_volume_mul_inv
    (g : ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ x in Set.Ioo (0:ℝ) 1, g x ∂logWeightedMeasure
      = ∫⁻ x in Set.Ioo (0:ℝ) 1, g x * ENNReal.ofReal (1 / x) ∂volume := by
  rw [logWeightedMeasure_def]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul _
        logWeightDensity_measurable hg measurableSet_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro x hx
  show logWeightDensity x * g x = g x * ENNReal.ofReal (1 / x)
  unfold logWeightDensity
  rw [if_neg (not_le.mpr hx.1), mul_comm]

/-- The **Mayer 1991 operator-norm bound** restated against the
    `logWeightedMeasure` directly:

      $\int_{(0, 1)} \|T_b f(x)\|^2\, \mathrm{d}\mu_{\log}(x)
        \le \int_{(0, 1)} \|f(u)\|^2\, \mathrm{d}\mu_{\log}(u)$.

    Composes:
      1. The volume-form Mayer bound `mayer_1991_lintegral_norm_sq_bound_log_weighted`
         (commit b8ee9a9).
      2. The `logWeightedMeasure ↔ volume · (1/x)` bridge
         `setLIntegral_Ioo_logWeightedMeasure_eq_setLIntegral_volume_mul_inv`
         (commit 69b7054), applied to both sides.

    Measurability of the LHS integrand
    `fun x => ofReal(‖(1/b) Σ_k ω_k · w_k(x) · f(y_k(x))‖²)`
    is established by chaining `weightFunction_measurable`,
    `inverseBranch_measurable`, `Complex.continuous_ofReal.measurable`,
    `Measurable.mul` / `Measurable.const_mul`, `Finset.measurable_sum`,
    `Measurable.norm`, `Measurable.pow_const`, and
    `ENNReal.continuous_ofReal.measurable`.

    This is the form mathlib's `eLpNorm` consumes: once the L²
    structural swap lands, this restated bound is one
    `eLpNorm_eq_lintegral_rpow_enorm` away from `‖T_b f‖_{L²(μ_log)}^2
    ≤ ‖f‖_{L²(μ_log)}^2`, which by `Real.sqrt`-monotonicity gives
    `‖T_b‖ ≤ 1` — the Mayer 1991 contractivity. -/
theorem mayer_1991_lintegral_norm_sq_bound_against_logWeightedMeasure
    (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : ℝ → ℂ) (hf : Measurable f) :
    ∫⁻ x in Set.Ioo (0:ℝ) 1,
        ENNReal.ofReal (‖(1 / (b : ℂ)) *
            ∑ k, phases k *
              ((weightFunction b k x : ℂ) * f (inverseBranch b k x))‖^2)
          ∂logWeightedMeasure
      ≤ ∫⁻ u in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal (‖f u‖^2) ∂logWeightedMeasure := by
  -- LHS integrand measurability (long chain)
  have h_lhs_meas : Measurable (fun x : ℝ => ENNReal.ofReal
      (‖(1 / (b : ℂ)) *
          ∑ k, phases k *
            ((weightFunction b k x : ℂ) * f (inverseBranch b k x))‖^2)) := by
    refine ENNReal.continuous_ofReal.measurable.comp ?_
    refine Measurable.pow_const ?_ 2
    refine Measurable.norm ?_
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ ?_
    intro k _
    refine Measurable.const_mul ?_ _
    refine Measurable.mul ?_ ?_
    · exact Complex.continuous_ofReal.measurable.comp (weightFunction_measurable b k)
    · exact hf.comp (inverseBranch_measurable b k hb)
  -- RHS integrand measurability
  have h_rhs_meas : Measurable (fun u : ℝ => ENNReal.ofReal (‖f u‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp (hf.norm.pow_const 2)
  -- Apply bridges to convert both sides to volume · (1/x) form
  rw [setLIntegral_Ioo_logWeightedMeasure_eq_setLIntegral_volume_mul_inv _ h_lhs_meas,
      setLIntegral_Ioo_logWeightedMeasure_eq_setLIntegral_volume_mul_inv _ h_rhs_meas]
  -- Goal is now exactly the volume-form Mayer bound (commit b8ee9a9)
  exact mayer_1991_lintegral_norm_sq_bound_log_weighted b hb phases hphases f hf

/-! ## Function-level transfer operator (bridge to mathlib's `Lp`)

The structure-based `transferOperatorAction` in `PF/TransferOperator.lean`
acts on the placeholder `LogWeightedL2` structure (whose `toFun` is
restricted to `Set.Icc 0 1 → ℂ`). For the L² structural swap to
`MeasureTheory.Lp ℂ 2 logWeightedMeasure`, we need a parallel
**function-level** action on `ℝ → ℂ`, whose `MemLp` membership is
controlled by the Mayer 1991 lintegral bound. The definitions and
lemmas below establish that bridge. -/

/-- Function-level transfer operator action: directly on `ℝ → ℂ` rather
    than the structure-based `LogWeightedL2`. The formula matches
    `transferOperatorAction` (in `PF/TransferOperator.lean`) but operates
    on plain functions — the form mathlib's `MemLp` predicate consumes.

    For `f : ℝ → ℂ`:
    $$T_b^{fn}\, f(x) := \frac{1}{b}\sum_k \omega_k \cdot w_k(x) \cdot f(y_k(x)).$$

    This is the bridge between the structural `transferOperatorAction`
    (which acts on `LogWeightedL2`) and mathlib's `Lp ℂ 2 μ_log` function
    space. The Mayer 1991 lintegral bound
    (`mayer_1991_lintegral_norm_sq_bound_log_weighted`, commit b8ee9a9)
    controls `transferOperatorAction_fn`'s `MemLp` membership; combined
    with `Measurable f`, this lifts to a well-defined map `Lp ℂ 2 μ_log
    → Lp ℂ 2 μ_log` once the structural swap lands. -/
noncomputable def transferOperatorAction_fn (b : ℕ) (phases : Fin b → ℂ)
    (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1 / (b : ℂ)) * ∑ k, phases k *
    ((weightFunction b k x : ℂ) * f (inverseBranch b k x))

/-- The function-level transfer operator action preserves measurability:
    when `f` is Borel measurable, so is `T_b^{fn} f`.

    Proof composes:
      * `weightFunction_measurable` (for each branch's weight),
      * `Complex.continuous_ofReal.measurable` (the ℝ → ℂ coercion),
      * `inverseBranch_measurable` + `hf` (for `f ∘ y_k`),
      * `Measurable.mul`, `Measurable.const_mul` (phase and 1/b factors),
      * `Finset.measurable_sum` (the b-branch sum).

    This is the measurability ingredient required to lift the action
    onto `MeasureTheory.Lp` (which insists on the underlying function
    being AE-strongly-measurable). -/
theorem transferOperatorAction_fn_measurable (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (transferOperatorAction_fn b phases f) := by
  unfold transferOperatorAction_fn
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ ?_
  intro k _
  refine Measurable.const_mul ?_ _
  refine Measurable.mul ?_ ?_
  · exact Complex.continuous_ofReal.measurable.comp (weightFunction_measurable b k)
  · exact hf.comp (inverseBranch_measurable b k hb)

/-- The Mayer 1991 bound restated in terms of the named function-level
    operator `transferOperatorAction_fn`:

      $\int_{(0, 1)} \|T_b^{fn} f(x)\|^2\, \mathrm{d}\mu_{\log}(x)
        \le \int_{(0, 1)} \|f(u)\|^2\, \mathrm{d}\mu_{\log}(u)$.

    Pure restatement of `mayer_1991_lintegral_norm_sq_bound_against_logWeightedMeasure`
    (commit f13126b) under the name `transferOperatorAction_fn`. The
    `unfold` reduces to the spelled-out formula matching the Mayer
    bound's LHS. -/
theorem transferOperatorAction_fn_lintegral_norm_sq_bound_logWeightedMeasure
    (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : ℝ → ℂ) (hf : Measurable f) :
    ∫⁻ x in Set.Ioo (0:ℝ) 1,
        ENNReal.ofReal (‖transferOperatorAction_fn b phases f x‖^2)
          ∂logWeightedMeasure
      ≤ ∫⁻ u in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal (‖f u‖^2) ∂logWeightedMeasure := by
  unfold transferOperatorAction_fn
  exact mayer_1991_lintegral_norm_sq_bound_against_logWeightedMeasure
    b hb phases hphases f hf

/-- Pointwise bridge: `‖x‖ₑ^(2:ℝ)` (enorm raised to the real exponent
    2, in `ℝ≥0∞`) equals `ENNReal.ofReal(‖x‖^2)` for any element of a
    normed group.

    Standard mathlib chain: `ENNReal.rpow_two` reduces `x^(2:ℝ)` to
    `x * x`; `ofReal_norm_eq_enorm` lifts the norm to ofReal-form;
    `ENNReal.ofReal_mul` combines the two factors. This bridge is
    the missing link between the volume-form Mayer bound (which is
    stated in `ENNReal.ofReal(‖·‖²)` form) and mathlib's `eLpNorm`
    (which uses `‖·‖ₑ^(p.toReal)` form). -/
theorem enorm_rpow_two_eq_ofReal_norm_sq (x : ℂ) :
    ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [ENNReal.rpow_two, sq, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _), ← sq]

/-- The transfer operator is a contraction on $L^2(d\mu_{\log})$ over
    $(0, 1)$ — the **operator-norm bound** $\|T_b\| \le 1$ in `eLpNorm`
    form, restricted to the unit interval:

      $\|T_b^{fn}\, f\|_{L^2(\mu_{\log}\!\restriction(0,1))}
        \le \|f\|_{L^2(\mu_{\log}\!\restriction(0,1))}$.

    This is **Mayer 1991 contractivity** in the form mathlib's
    `MemLp` / `Lp` space-API consume. Once the L² structural swap
    `LogWeightedL2 := MeasureTheory.Lp ℂ 2 logWeightedMeasure` lands,
    this lifts directly to a `ContinuousLinearMap` instance with
    operator norm $\le 1$, retiring the `T3_self_adjoint_conj` axiom
    for the canonical 8-axiom referee surface (8 → 7).

    Proof — four-step:
      1. `eLpNorm_eq_lintegral_rpow_enorm` (mathlib) reduces both
         eLpNorms to lintegral form `(∫⁻ ‖·‖ₑ^(2.toReal) ∂μ)^(1/2.toReal)`.
      2. `ENNReal.rpow_le_rpow` (with $0 \le 1/2$) reduces the
         outer rpow to a lintegral inequality.
      3. The pointwise bridge `enorm_rpow_two_eq_ofReal_norm_sq` lifted
         under `lintegral_congr` rewrites both integrands `‖·‖ₑ^(2:ℝ)`
         to `ENNReal.ofReal(‖·‖²)`.
      4. The named-operator Mayer bound
         `transferOperatorAction_fn_lintegral_norm_sq_bound_logWeightedMeasure`
         (commit e259e42) closes the chain. -/
theorem transferOperatorAction_fn_eLpNorm_le_logWeightedMeasure
    (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : ℝ → ℂ) (hf : Measurable f) :
    eLpNorm (transferOperatorAction_fn b phases f) 2
        (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))
      ≤ eLpNorm f 2
          (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have h_toReal : (2 : ENNReal).toReal = 2 := by norm_num
  simp only [h_toReal]
  rw [lintegral_congr
        (fun x => enorm_rpow_two_eq_ofReal_norm_sq
          (transferOperatorAction_fn b phases f x))]
  rw [lintegral_congr (fun x => enorm_rpow_two_eq_ofReal_norm_sq (f x))]
  exact transferOperatorAction_fn_lintegral_norm_sq_bound_logWeightedMeasure
    b hb phases hphases f hf

/-- The transfer operator preserves $L^2$ membership against
    `logWeightedMeasure` over $(0, 1)$:

      $f \in L^2(\mu_{\log}\!\restriction(0,1))
        \Rightarrow T_b^{fn}\, f \in L^2(\mu_{\log}\!\restriction(0,1))$.

    Direct corollary of the eLpNorm contractivity bound (commit
    de54564) via `MemLp = AEStronglyMeasurable + eLpNorm_lt_top`:
      * AEStronglyMeasurable: from `Measurable T_b^{fn} f` (commit
        9429dd6) via `Measurable.aestronglyMeasurable`.
      * eLpNorm < ⊤: `eLpNorm (T_b^{fn} f) 2 μ ≤ eLpNorm f 2 μ < ⊤`
        via `lt_of_le_of_lt` on de54564 + `hfMemLp.eLpNorm_lt_top`.

    This is the **MemLp corollary** of Mayer 1991 contractivity. With
    this, `T_b^{fn}` lifts to a well-defined map
    `Lp ℂ 2 (μ_log.restrict (0,1)) → Lp ℂ 2 (μ_log.restrict (0,1))`
    via mathlib's `MemLp.toLp` once the structural swap lands. -/
theorem transferOperatorAction_fn_memLp
    (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfMemLp : MemLp f 2 (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))) :
    MemLp (transferOperatorAction_fn b phases f) 2
        (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)) :=
  ⟨(transferOperatorAction_fn_measurable b hb phases f hf).aestronglyMeasurable,
   lt_of_le_of_lt
     (transferOperatorAction_fn_eLpNorm_le_logWeightedMeasure
       b hb phases hphases f hf)
     hfMemLp.eLpNorm_lt_top⟩

/-! ## L² structural-swap scaffolding (begin cascade)

The pieces below establish the parallel `Lp`-typed scaffolding alongside
the existing structural `LogWeightedL2`. They do NOT touch the existing
structure; the eventual rename cascade through `PF/TransferOperator.lean`
will use these pieces as drop-in replacements once the cascade lands. -/

/-- The `L²` Hilbert space against the log-weighted measure restricted
    to the unit interval $(0, 1)$ — the **target type** for the L²
    structural swap. Inherits `InnerProductSpace ℂ`,
    `NormedAddCommGroup`, `CompleteSpace`, and `NormedSpace ℂ` from
    mathlib's `MeasureTheory.Lp` family via `inferInstance`. -/
noncomputable abbrev LogWeightedL2_Ioo : Type :=
  MeasureTheory.Lp ℂ 2 (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))

/-- `LogWeightedL2_Ioo` carries mathlib's `InnerProductSpace ℂ`. -/
noncomputable example : InnerProductSpace ℂ LogWeightedL2_Ioo := inferInstance

/-- `LogWeightedL2_Ioo` is a complete normed space (Hilbert space). -/
noncomputable example : CompleteSpace LogWeightedL2_Ioo := inferInstance

/-- The transfer operator action lifted to an `Lp` element via
    `MemLp.toLp`. Given measurable `f : ℝ → ℂ` with `MemLp f 2`,
    produces an `LogWeightedL2_Ioo` element representing $T_b^{fn}\, f$.

    This is the lift through the `Lp = MemLp / AE-equiv` quotient at
    a single representative. A future step will establish AE-compatibility
    of `transferOperatorAction_fn` and lift to a `Lp → Lp` quotient map.
    For now, this is the operator-norm-bounded $L^2$-target form of the
    Mayer 1991 contractivity result. -/
noncomputable def transferOperatorAction_fn_toLp
    (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfMemLp : MemLp f 2 (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))) :
    LogWeightedL2_Ioo :=
  MemLp.toLp (transferOperatorAction_fn b phases f)
    (transferOperatorAction_fn_memLp b hb phases hphases f hf hfMemLp)

/-- The Lp-lifted transfer operator action is contractive: its eLpNorm
    is bounded by the input's eLpNorm. Direct corollary of
    `transferOperatorAction_fn_eLpNorm_le_logWeightedMeasure`
    (commit de54564) via `MemLp.coeFn_toLp` (which establishes
    `(h.toLp f) =ᵐ[μ] f`, allowing `eLpNorm_congr_ae` to swap the
    Lp-element's eLpNorm with the underlying function's eLpNorm). -/
theorem transferOperatorAction_fn_toLp_eLpNorm_le
    (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfMemLp : MemLp f 2 (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))) :
    eLpNorm (transferOperatorAction_fn_toLp b hb phases hphases f hf hfMemLp) 2
        (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))
      ≤ eLpNorm f 2
          (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)) := by
  unfold transferOperatorAction_fn_toLp
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  exact transferOperatorAction_fn_eLpNorm_le_logWeightedMeasure
    b hb phases hphases f hf

/-- The Lp-lifted transfer operator action is contractive in the natural
    Banach-space norm on `LogWeightedL2_Ioo`:
      `‖T_b^{fn,Lp} f‖ ≤ (eLpNorm f 2 μ_log).toReal`.

    This is the real-norm form of `‖T_b‖ ≤ 1` consumed by the operator-norm
    interpretation. Direct corollary of `transferOperatorAction_fn_toLp_eLpNorm_le`
    via `Lp.norm_def` (Lp norm = toReal of eLpNorm) and `ENNReal.toReal_mono`
    with the side condition `eLpNorm f 2 μ ≠ ⊤` from `hfMemLp.eLpNorm_lt_top`. -/
theorem transferOperatorAction_fn_toLp_norm_le
    (b : ℕ) (hb : b ≥ 1)
    (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfMemLp : MemLp f 2 (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))) :
    ‖transferOperatorAction_fn_toLp b hb phases hphases f hf hfMemLp‖
      ≤ (eLpNorm f 2
          (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))).toReal := by
  rw [Lp.norm_def]
  exact ENNReal.toReal_mono hfMemLp.eLpNorm_lt_top.ne
    (transferOperatorAction_fn_toLp_eLpNorm_le
      b hb phases hphases f hf hfMemLp)

/-! ### Linearity of the function-level transfer operator

The pointwise additivity and homogeneity identities for
`transferOperatorAction_fn`. These are the linearity ingredients consumed
by `LinearMap.mkContinuous`, which builds a `ContinuousLinearMap` out of
a linear map plus an operator-norm bound. Combined with
`transferOperatorAction_fn_toLp_norm_le`, this is all the analytic
content needed to package `T_b^{fn,Lp}` as a CLM
`LogWeightedL2_Ioo →L[ℂ] LogWeightedL2_Ioo` with operator norm ≤ 1. -/

/-- Additivity: `T_b^{fn} (f + g) = T_b^{fn} f + T_b^{fn} g` pointwise. -/
theorem transferOperatorAction_fn_add (b : ℕ) (phases : Fin b → ℂ)
    (f g : ℝ → ℂ) (x : ℝ) :
    transferOperatorAction_fn b phases (f + g) x
      = transferOperatorAction_fn b phases f x
        + transferOperatorAction_fn b phases g x := by
  unfold transferOperatorAction_fn
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Homogeneity: `T_b^{fn} (c • f) = c • T_b^{fn} f` pointwise. -/
theorem transferOperatorAction_fn_smul (b : ℕ) (phases : Fin b → ℂ) (c : ℂ)
    (f : ℝ → ℂ) (x : ℝ) :
    transferOperatorAction_fn b phases (c • f) x
      = c • transferOperatorAction_fn b phases f x := by
  unfold transferOperatorAction_fn
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show ∑ k, phases k * ((weightFunction b k x : ℂ) * (c * f (inverseBranch b k x)))
        = c * ∑ k, phases k * ((weightFunction b k x : ℂ) * f (inverseBranch b k x)) from ?_]
  · ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring

/-! ### Lp-lifted linearity

Lifting the pointwise linearity of `T_b^{fn}` through `MemLp.toLp`:
the Lp elements built from `T_b^{fn} (f+g)` and `T_b^{fn} (c•f)` are
literally the sum / scalar of the Lp elements built from `T_b^{fn} f`
and `T_b^{fn} g`.

Both proofs are an `Eq.trans` chain:
  1. `MemLp.toLp_congr` (mathlib `LpSpace/Basic.lean:109`) bridges
     `MemLp.toLp (T_b (f+g)) hWit_lhs` to `MemLp.toLp (T_b f + T_b g)
     (hWit_f.add hWit_g)` using ae-equality from pointwise equality.
  2. `MemLp.toLp_add` / `MemLp.toLp_const_smul` (each `rfl`, mathlib
     `LpSpace/Basic.lean:120, 456`) splits the canonical-form Lp element
     into the sum / scalar.

A direct `rw [funext ...]` approach hits "motive is not type correct"
because the MemLp witness's type depends on the function being rewritten;
the `MemLp.toLp_congr` route bypasses this by accepting two distinct
witnesses for ae-equal functions. -/

/-- Lp-lifted additivity: `T_b^{fn,Lp} (f+g) = T_b^{fn,Lp} f + T_b^{fn,Lp} g`. -/
theorem transferOperatorAction_fn_toLp_add
    (b : ℕ) (hb : b ≥ 1) (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfMemLp : MemLp f 2 (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)))
    (hgMemLp : MemLp g 2 (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))) :
    transferOperatorAction_fn_toLp b hb phases hphases (f + g) (hf.add hg)
        (hfMemLp.add hgMemLp)
      = transferOperatorAction_fn_toLp b hb phases hphases f hf hfMemLp
        + transferOperatorAction_fn_toLp b hb phases hphases g hg hgMemLp := by
  unfold transferOperatorAction_fn_toLp
  have h_ae : transferOperatorAction_fn b phases (f + g)
            =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
              transferOperatorAction_fn b phases f
                + transferOperatorAction_fn b phases g :=
    Filter.Eventually.of_forall
      fun x => transferOperatorAction_fn_add b phases f g x
  exact (MemLp.toLp_congr
    (transferOperatorAction_fn_memLp b hb phases hphases (f + g)
      (hf.add hg) (hfMemLp.add hgMemLp))
    ((transferOperatorAction_fn_memLp b hb phases hphases f hf hfMemLp).add
      (transferOperatorAction_fn_memLp b hb phases hphases g hg hgMemLp))
    h_ae).trans (MemLp.toLp_add _ _)

/-- Contractivity stated entirely in Lp.norm: input is the Lp element built
    from `f`, and the bound `‖T_b^{fn,Lp} f‖ ≤ ‖f-toLp‖` is exactly
    the form `LinearMap.mkContinuous` consumes as the operator-norm bound
    (with `M = 1`). Direct corollary of
    `transferOperatorAction_fn_toLp_norm_le` (commit 0e87907) plus the
    identity `‖MemLp.toLp f hfMemLp‖ = (eLpNorm f 2 μ).toReal` from
    `Lp.norm_def` + `MemLp.coeFn_toLp`. -/
theorem transferOperatorAction_fn_toLp_norm_le_input_toLp
    (b : ℕ) (hb : b ≥ 1) (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfMemLp : MemLp f 2 (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))) :
    ‖transferOperatorAction_fn_toLp b hb phases hphases f hf hfMemLp‖
      ≤ ‖(MemLp.toLp f hfMemLp : LogWeightedL2_Ioo)‖ := by
  have h_eq : ‖(MemLp.toLp f hfMemLp : LogWeightedL2_Ioo)‖
            = (eLpNorm f 2
                (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))).toReal := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae (MemLp.coeFn_toLp _))
  rw [h_eq]
  exact transferOperatorAction_fn_toLp_norm_le b hb phases hphases f hf hfMemLp

/-! ### Direct `Lp → Lp` form of the transfer operator

`transferOperatorAction_fn_toLp` takes (function, Measurable, MemLp) as
input. To package T_b as a `ContinuousLinearMap`, we need a function
`Lp → Lp` directly. This is achieved by extracting the canonical
strongly-measurable representative from any Lp element via
`AEStronglyMeasurable.mk`. -/

/-- The Lp-element-level transfer operator action. Takes
    `g : LogWeightedL2_Ioo` directly (not function + Measurable + MemLp)
    by extracting the canonical strongly-measurable representative
    `(Lp.aestronglyMeasurable g).mk g`, then applying
    `transferOperatorAction_fn_toLp`. -/
noncomputable def transferOperator_lp
    (b : ℕ) (hb : b ≥ 1) (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (g : LogWeightedL2_Ioo) : LogWeightedL2_Ioo :=
  transferOperatorAction_fn_toLp b hb phases hphases
    ((Lp.aestronglyMeasurable g).mk (g : ℝ → ℂ))
    (Lp.aestronglyMeasurable g).measurable_mk
    ((Lp.memLp g).ae_eq (Lp.aestronglyMeasurable g).ae_eq_mk)

/-- Contractivity for the direct `Lp → Lp` form: `‖T_b^{Lp} g‖ ≤ ‖g‖`.
    The operator-norm bound on `transferOperator_lp` — the form
    `LinearMap.mkContinuous` consumes (with `M = 1`).

    Proof: chain `transferOperatorAction_fn_toLp_norm_le_input_toLp`
    (commit 712ee4e) with the identity `MemLp.toLp ((aesm g).mk g) ... = g`
    in `Lp`, which holds because `↑↑(MemLp.toLp ...) =ᵐ (aesm g).mk g =ᵐ ↑↑g`
    via `MemLp.coeFn_toLp` and `AEStronglyMeasurable.ae_eq_mk`. -/
theorem transferOperator_lp_norm_le
    (b : ℕ) (hb : b ≥ 1) (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (g : LogWeightedL2_Ioo) :
    ‖transferOperator_lp b hb phases hphases g‖ ≤ ‖g‖ := by
  have h_eq : (MemLp.toLp ((Lp.aestronglyMeasurable g).mk (g : ℝ → ℂ))
                ((Lp.memLp g).ae_eq (Lp.aestronglyMeasurable g).ae_eq_mk)
              : LogWeightedL2_Ioo) = g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
                      ((Lp.memLp g).ae_eq (Lp.aestronglyMeasurable g).ae_eq_mk),
                    (Lp.aestronglyMeasurable g).ae_eq_mk]
      with x h1 h2
    rw [h1, ← h2]
  unfold transferOperator_lp
  conv_rhs => rw [← h_eq]
  exact transferOperatorAction_fn_toLp_norm_le_input_toLp b hb phases hphases
    ((Lp.aestronglyMeasurable g).mk (g : ℝ → ℂ))
    (Lp.aestronglyMeasurable g).measurable_mk
    ((Lp.memLp g).ae_eq (Lp.aestronglyMeasurable g).ae_eq_mk)

/-! ### AE-equality propagation infrastructure (toward CLM linearity)

To package `transferOperator_lp` as a `ContinuousLinearMap`, we need to
show `T_b` respects ae-equality of input under `μ_log↾(0,1)`. The route
goes through two absolute-continuity facts:
  (a) `μ_log↾(0,1) ≪ volume`            — the log-weighted measure is
                                            absolutely continuous wrt
                                            Lebesgue (via `withDensity`),
                                            so this lifts naturally
                                            to the restriction.
  (b) `(μ_log↾(0,1)).map y_k ≪ μ_log↾(0,1)` — the pushforward under
                                            `inverseBranch` preserves
                                            null sets.

The combination plus `ae_map_iff` propagates `f₁ =ᵐ f₂` through
`f ↦ f ∘ y_k`. Applied per branch and summed, this gives
`T_b f₁ =ᵐ T_b f₂`. -/

/-- `μ_log↾(0,1) ≪ volume`: the log-weighted measure restricted to
    the unit interval is absolutely continuous wrt Lebesgue measure
    on ℝ. Direct chain: `restrict_le_self` (giving `μ_log↾(0,1) ≪ μ_log`)
    then `withDensity_absolutelyContinuous` (giving `μ_log ≪ volume`),
    composed via `Measure.AbsolutelyContinuous.trans`. -/
theorem logWeightedMeasure_restrict_Ioo_absolutelyContinuous_volume :
    logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1) ≪ (volume : Measure ℝ) :=
  Measure.absolutelyContinuous_of_le Measure.restrict_le_self
    |>.trans (withDensity_absolutelyContinuous _ _)

/-- `volume↾(0,1) ≪ μ_log↾(0,1)`: the converse absolute continuity.
    The log-weight density `(1/x)` is strictly positive on `(0,1)`, so
    `μ_log` and `volume` share null sets there.

    Proof via `withDensity_apply_eq_zero` (mathlib `WithDensity.lean:279`):
      `μ_log s = 0 ↔ volume({x | logWeightDensity x ≠ 0} ∩ s) = 0`
    Since `logWeightDensity x ≠ 0` for all `x > 0` (and `(0,1) ⊂ (0,∞)`),
    the intersection with `s ∩ (0,1)` equals `s ∩ (0,1)` itself, giving
    `volume(s ∩ (0,1)) = 0`. -/
theorem volume_restrict_Ioo_absolutelyContinuous_logWeightedMeasure :
    (volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) 1)
      ≪ logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1) := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  rw [Measure.restrict_apply hs] at hs_zero
  rw [Measure.restrict_apply hs]
  rw [logWeightedMeasure_def] at hs_zero
  rw [withDensity_apply_eq_zero logWeightDensity_measurable] at hs_zero
  have h_sub : (s ∩ Set.Ioo (0:ℝ) 1) ⊆ {x | logWeightDensity x ≠ 0} := by
    intro x hx
    have hx_pos : (0:ℝ) < x := hx.2.1
    simp only [Set.mem_setOf_eq, logWeightDensity]
    rw [if_neg (not_le.mpr hx_pos)]
    exact (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hx_pos)).ne'
  rw [Set.inter_eq_right.mpr h_sub] at hs_zero
  exact hs_zero

/-- `(μ_log↾(0,1)).map y_k ≪ μ_log↾(0,1)`: the pushforward absolute
    continuity — the substantive lemma needed for ae-equality propagation
    through the transfer operator T_b.

    Proof chain (combining the previous two abs-continuity directions
    with `inverseBranch_volume_map`):

      μ_log↾(0,1)(E) = 0
        ⟹ volume(E ∩ (0,1)) = 0           [volume↾(0,1) ≪ μ_log↾(0,1)]
        ⟹ volume(y_k⁻¹(E ∩ (0,1))) = 0    [inverseBranch_volume_map: vol.map y_k = b·vol]
        ⟹ volume(y_k⁻¹(E) ∩ (0,1)) = 0    [y_k⁻¹(E) ∩ (0,1) ⊆ y_k⁻¹(E ∩ (0,1)),
                                            since y_k((0,1)) ⊆ (0,1)]
        ⟹ μ_log(y_k⁻¹(E) ∩ (0,1)) = 0     [μ_log↾(0,1) ≪ volume]
        ⟹ ((μ_log↾(0,1)).map y_k) E = 0    [unfold pushforward + restrict] -/
theorem logWeightedMeasure_restrict_Ioo_map_inverseBranch_absolutelyContinuous
    (b : ℕ) (hb : b ≥ 1) (k : Fin b) :
    (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)).map (inverseBranch b k)
      ≪ logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1) := by
  have hb_real : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hb
  have hb_pos : (0 : ℝ) < b := by exact_mod_cast hb
  refine Measure.AbsolutelyContinuous.mk fun E hE hE_zero => ?_
  -- Step A: volume(E ∩ Ioo) = 0 via volume↾(0,1) ≪ μ_log↾(0,1) (commit 869b6f7)
  have hE_volume : volume (E ∩ Set.Ioo (0:ℝ) 1) = 0 := by
    have key := volume_restrict_Ioo_absolutelyContinuous_logWeightedMeasure hE_zero
    rwa [Measure.restrict_apply hE] at key
  -- Step B: volume(y_k⁻¹(E ∩ Ioo)) = 0 via inverseBranch_volume_map
  have hY_preimage : volume (inverseBranch b k ⁻¹' (E ∩ Set.Ioo (0:ℝ) 1)) = 0 := by
    rw [← Measure.map_apply (inverseBranch_measurable b k hb)
          (hE.inter measurableSet_Ioo)]
    rw [inverseBranch_volume_map b k hb_real]
    rw [Measure.smul_apply, hE_volume, smul_zero]
  -- Step C: y_k⁻¹(E) ∩ Ioo ⊆ y_k⁻¹(E ∩ Ioo), hence its volume is 0
  have hY_inter : volume (inverseBranch b k ⁻¹' E ∩ Set.Ioo (0:ℝ) 1) = 0 := by
    apply measure_mono_null _ hY_preimage
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hx_pos : 0 < x := hx.2.1
    have hx_lt : x < 1 := hx.2.2
    have hk_succ_le_b_nat : k.val + 1 ≤ b := k.isLt
    have hk_succ_le_b : (k.val : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hk_succ_le_b_nat
    have hk_nonneg : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    refine ⟨?_, ?_⟩
    · simp only [inverseBranch]
      apply div_pos (by linarith) hb_pos
    · simp only [inverseBranch]
      rw [div_lt_one hb_pos]
      linarith
  -- Step D: μ_log↾(0,1)(y_k⁻¹(E)) = 0 via μ_log↾(0,1) ≪ volume (commit 98b1f7e)
  rw [Measure.map_apply (inverseBranch_measurable b k hb) hE]
  have h_target : (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))
                  (inverseBranch b k ⁻¹' E ∩ Set.Ioo (0:ℝ) 1) = 0 :=
    logWeightedMeasure_restrict_Ioo_absolutelyContinuous_volume hY_inter
  rw [Measure.restrict_apply (inverseBranch_measurable b k hb hE)]
  rwa [Measure.restrict_apply
        ((inverseBranch_measurable b k hb hE).inter measurableSet_Ioo),
       Set.inter_assoc, Set.inter_self] at h_target

/-- Per-branch ae-propagation: `f₁ =ᵐ f₂ ⟹ f₁ ∘ y_k =ᵐ f₂ ∘ y_k`
    (under `μ_log↾(0,1)`).

    Two-step proof using the pushforward absolute continuity:
      1. `EventuallyEq.filter_mono` lifts the hypothesis at `μ_log↾(0,1).ae`
         to `(μ_log↾(0,1).map y_k).ae` via the filter inequality from
         `25e00eb.ae_le : (μ.map y_k).ae ≤ μ.ae`.
      2. `EventuallyEq.comp_tendsto` composes with
         `Measure.tendsto_ae_map (inverseBranch_measurable b k hb).aemeasurable`
         (giving `Tendsto y_k μ.ae (μ.map y_k).ae`) to pull back to the
         source filter, yielding `f₁ ∘ y_k =ᵐ[μ.ae] f₂ ∘ y_k`. -/
theorem inverseBranch_ae_eq_propagation
    (b : ℕ) (hb : b ≥ 1) (k : Fin b)
    {f₁ f₂ : ℝ → ℂ}
    (h : f₁ =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)] f₂) :
    (fun x => f₁ (inverseBranch b k x))
      =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (fun x => f₂ (inverseBranch b k x)) := by
  have h_le := (logWeightedMeasure_restrict_Ioo_map_inverseBranch_absolutelyContinuous b hb k).ae_le
  have h_map : f₁ =ᵐ[(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)).map
                      (inverseBranch b k)] f₂ :=
    h.filter_mono h_le
  exact h_map.comp_tendsto
    (Measure.tendsto_ae_map (inverseBranch_measurable b k hb).aemeasurable)

/-- Full T_b ae-respect: `f₁ =ᵐ f₂ ⟹ T_b f₁ =ᵐ T_b f₂` (under `μ_log↾(0,1)`).

    Combines `inverseBranch_ae_eq_propagation` per branch via
    `Filter.eventually_all` (for the finite indexing `Fin b`):
    suffices to show, simultaneously for all branches at almost every x,
    that `f₁ (y_k x) = f₂ (y_k x)`, and then `Finset.sum_congr` composes
    pointwise inside the b-summed pointwise definition of T_b.

    With this lemma, `transferOperator_lp` becomes well-defined as a
    `Lp → Lp` map modulo ae-equivalence — the well-definedness step that
    `LinearMap.mkContinuous` packaging consumes. -/
theorem transferOperatorAction_fn_ae_eq_of_ae_eq
    (b : ℕ) (hb : b ≥ 1) (phases : Fin b → ℂ)
    {f₁ f₂ : ℝ → ℂ}
    (h : f₁ =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)] f₂) :
    transferOperatorAction_fn b phases f₁
      =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        transferOperatorAction_fn b phases f₂ := by
  have h_all : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      ∀ k : Fin b, f₁ (inverseBranch b k x) = f₂ (inverseBranch b k x) :=
    Filter.eventually_all.mpr fun k => inverseBranch_ae_eq_propagation b hb k h
  filter_upwards [h_all] with x hx_all
  unfold transferOperatorAction_fn
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hx_all k]

/-- Lp-level additivity: `transferOperator_lp (g + h) = transferOperator_lp g + transferOperator_lp h`.

    Composes today's chain:
      Lp.coeFn_add + AEStronglyMeasurable.ae_eq_mk →
        `(aesm (g+h)).mk ⇑(g+h) =ᵐ (aesm g).mk ⇑g + (aesm h).mk ⇑h`
      transferOperatorAction_fn_ae_eq_of_ae_eq (commit e989098) →
        `T_b f_gh =ᵐ T_b (f_g + f_h)`
      transferOperatorAction_fn_add (commit 49ff3ba, pointwise) →
        `T_b (f_g + f_h) = T_b f_g + T_b f_h`
      MemLp.toLp_congr + MemLp.toLp_add → final Lp equality.

    With this lemma, `transferOperator_lp` is formally additive at the
    Lp level — half of the linearity needed for `LinearMap.mkContinuous`
    packaging. -/
theorem transferOperator_lp_add
    (b : ℕ) (hb : b ≥ 1) (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (g h : LogWeightedL2_Ioo) :
    transferOperator_lp b hb phases hphases (g + h)
      = transferOperator_lp b hb phases hphases g
        + transferOperator_lp b hb phases hphases h := by
  -- Names for representatives
  set f_gh := (Lp.aestronglyMeasurable (g + h)).mk ((g + h : LogWeightedL2_Ioo) : ℝ → ℂ)
  set f_g := (Lp.aestronglyMeasurable g).mk ((g : LogWeightedL2_Ioo) : ℝ → ℂ)
  set f_h := (Lp.aestronglyMeasurable h).mk ((h : LogWeightedL2_Ioo) : ℝ → ℂ)
  -- Step 1: representatives' ae-equality
  have h_input : f_gh =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)] f_g + f_h :=
    ((Lp.aestronglyMeasurable (g + h)).ae_eq_mk.symm.trans (Lp.coeFn_add g h)).trans
      ((Lp.aestronglyMeasurable g).ae_eq_mk.add (Lp.aestronglyMeasurable h).ae_eq_mk)
  -- Step 2: T_b respects ae (e989098), then split via pointwise add (49ff3ba)
  have h_T : transferOperatorAction_fn b phases f_gh
            =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
              transferOperatorAction_fn b phases f_g
                + transferOperatorAction_fn b phases f_h := by
    have h_T_pre := transferOperatorAction_fn_ae_eq_of_ae_eq b hb phases h_input
    rw [show transferOperatorAction_fn b phases (f_g + f_h)
          = transferOperatorAction_fn b phases f_g
            + transferOperatorAction_fn b phases f_h
        from funext fun x => transferOperatorAction_fn_add b phases f_g f_h x] at h_T_pre
    exact h_T_pre
  -- Step 3: bridge to Lp via toLp_congr + toLp_add
  unfold transferOperator_lp transferOperatorAction_fn_toLp
  exact (MemLp.toLp_congr _
    ((transferOperatorAction_fn_memLp b hb phases hphases f_g
        (Lp.aestronglyMeasurable g).measurable_mk
        ((Lp.memLp g).ae_eq (Lp.aestronglyMeasurable g).ae_eq_mk)).add
      (transferOperatorAction_fn_memLp b hb phases hphases f_h
        (Lp.aestronglyMeasurable h).measurable_mk
        ((Lp.memLp h).ae_eq (Lp.aestronglyMeasurable h).ae_eq_mk)))
    h_T).trans (MemLp.toLp_add _ _)

/-- Lp-level homogeneity: `transferOperator_lp (c • g) = c • transferOperator_lp g`.

    Analogous to `transferOperator_lp_add` (commit 483b388):
      Lp.coeFn_smul + AEStronglyMeasurable.ae_eq_mk →
        `(aesm (c•g)).mk ⇑(c•g) =ᵐ c • (aesm g).mk ⇑g`
        (via `EventuallyEq.const_smul`)
      transferOperatorAction_fn_ae_eq_of_ae_eq (commit e989098) →
        `T_b f_cg =ᵐ T_b (c • f_g)`
      transferOperatorAction_fn_smul (commit 49ff3ba, pointwise) →
        `T_b (c • f_g) = c • T_b f_g`
      MemLp.toLp_congr + MemLp.toLp_const_smul → final Lp equality.

    Together with `transferOperator_lp_add`, this completes the linearity
    of `transferOperator_lp` — both ingredients `LinearMap.mkContinuous`
    consumes are now in source. -/
theorem transferOperator_lp_smul
    (b : ℕ) (hb : b ≥ 1) (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (c : ℂ) (g : LogWeightedL2_Ioo) :
    transferOperator_lp b hb phases hphases (c • g)
      = c • transferOperator_lp b hb phases hphases g := by
  set f_cg := (Lp.aestronglyMeasurable (c • g)).mk ((c • g : LogWeightedL2_Ioo) : ℝ → ℂ)
  set f_g := (Lp.aestronglyMeasurable g).mk ((g : LogWeightedL2_Ioo) : ℝ → ℂ)
  -- Step 1: f_cg =ᵐ c • f_g
  have h_input : f_cg =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)] c • f_g :=
    ((Lp.aestronglyMeasurable (c • g)).ae_eq_mk.symm.trans (Lp.coeFn_smul c g)).trans
      ((Lp.aestronglyMeasurable g).ae_eq_mk.const_smul c)
  -- Step 2: T_b respects ae (e989098), then split via pointwise smul (49ff3ba)
  have h_T : transferOperatorAction_fn b phases f_cg
            =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
              c • transferOperatorAction_fn b phases f_g := by
    have h_T_pre := transferOperatorAction_fn_ae_eq_of_ae_eq b hb phases h_input
    rw [show transferOperatorAction_fn b phases (c • f_g)
          = c • transferOperatorAction_fn b phases f_g
        from funext fun x => transferOperatorAction_fn_smul b phases c f_g x] at h_T_pre
    exact h_T_pre
  -- Step 3: bridge to Lp via toLp_congr + toLp_const_smul
  unfold transferOperator_lp transferOperatorAction_fn_toLp
  exact (MemLp.toLp_congr _
    ((transferOperatorAction_fn_memLp b hb phases hphases f_g
        (Lp.aestronglyMeasurable g).measurable_mk
        ((Lp.memLp g).ae_eq (Lp.aestronglyMeasurable g).ae_eq_mk)).const_smul c)
    h_T).trans (MemLp.toLp_const_smul c _)

/-! ### Continuous linear map packaging

Assembles `transferOperator_lp` (commit `0e5e4b9`), its linearity
(commits `483b388` for `_add`, `d448a7e` for `_smul`), and its
operator-norm bound (`transferOperator_lp_norm_le`, commit `0e5e4b9`)
into a `ContinuousLinearMap` `LogWeightedL2_Ioo →L[ℂ] LogWeightedL2_Ioo`
with operator norm `≤ 1` via `LinearMap.mkContinuous`. -/

/-- The transfer operator T_b as a `ContinuousLinearMap`
    `LogWeightedL2_Ioo →L[ℂ] LogWeightedL2_Ioo` with operator norm `≤ 1`.

    Construction:
      LinearMap.mkContinuous L 1 (op-norm bound)
    where `L` packages `transferOperator_lp` with its additivity (`483b388`)
    and homogeneity (`d448a7e`) into a `LinearMap`, and the op-norm bound
    is `transferOperator_lp_norm_le` (`0e5e4b9`) lifted from `‖·‖ ≤ ‖·‖`
    to `‖·‖ ≤ 1 * ‖·‖` via `one_mul`. -/
noncomputable def transferOperator_clm
    (b : ℕ) (hb : b ≥ 1) (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1) :
    LogWeightedL2_Ioo →L[ℂ] LogWeightedL2_Ioo :=
  LinearMap.mkContinuous
    { toFun := transferOperator_lp b hb phases hphases
      map_add' := transferOperator_lp_add b hb phases hphases
      map_smul' := transferOperator_lp_smul b hb phases hphases }
    1
    (fun g => by
      rw [one_mul]
      exact transferOperator_lp_norm_le b hb phases hphases g)

/-- Operator-norm bound for the continuous linear map form:
    `‖transferOperator_clm‖ ≤ 1`. Direct from `LinearMap.mkContinuous_norm_le`
    (mathlib) given the bound passed to `mkContinuous`. -/
theorem transferOperator_clm_norm_le
    (b : ℕ) (hb : b ≥ 1) (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1) :
    ‖transferOperator_clm b hb phases hphases‖ ≤ 1 := by
  unfold transferOperator_clm
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Lp-lifted homogeneity: `T_b^{fn,Lp} (c•f) = c • T_b^{fn,Lp} f`. -/
theorem transferOperatorAction_fn_toLp_smul
    (b : ℕ) (hb : b ≥ 1) (phases : Fin b → ℂ) (hphases : ∀ k, ‖phases k‖ = 1)
    (c : ℂ) (f : ℝ → ℂ) (hf : Measurable f)
    (hfMemLp : MemLp f 2 (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))) :
    transferOperatorAction_fn_toLp b hb phases hphases (c • f) (hf.const_smul c)
        (hfMemLp.const_smul c)
      = c • transferOperatorAction_fn_toLp b hb phases hphases f hf hfMemLp := by
  unfold transferOperatorAction_fn_toLp
  have h_ae : transferOperatorAction_fn b phases (c • f)
            =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
              c • transferOperatorAction_fn b phases f :=
    Filter.Eventually.of_forall
      fun x => transferOperatorAction_fn_smul b phases c f x
  exact (MemLp.toLp_congr
    (transferOperatorAction_fn_memLp b hb phases hphases (c • f)
      (hf.const_smul c) (hfMemLp.const_smul c))
    ((transferOperatorAction_fn_memLp b hb phases hphases f hf hfMemLp).const_smul c)
    h_ae).trans (MemLp.toLp_const_smul c _)

end PrincipiaTractalis
