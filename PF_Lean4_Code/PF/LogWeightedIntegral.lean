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

end PrincipiaTractalis
