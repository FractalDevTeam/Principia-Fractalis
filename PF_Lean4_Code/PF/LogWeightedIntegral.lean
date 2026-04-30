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

end PrincipiaTractalis
