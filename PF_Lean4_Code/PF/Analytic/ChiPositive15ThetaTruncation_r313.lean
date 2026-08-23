/-
# r313: Theta series identity for `evenKernel 0 y − 1`
#      via `hasSum_nat_cosKernel₀ 0` + peel-off + tail positivity
#      + definitions `I_15`, `J_1`, `R_{≥2}` + forward chain-closer bridge

★ 2026-08-22 r313 — exact theta truncation landing. Establishes the pointwise
series identity for the theta kernel factor of the r312 folded-cosine integrand,
defines the split `I_15 = J_1 + R_{≥2}` at the definitional level (with
`R_{≥2} := I_15 − J_1`), and provides the forward chain-closer bridge that
r314 (bound on `|R_{≥2}|`) and r315 (bound on `J_1`) will feed into.

## Route

- Use `HurwitzZeta.hasSum_nat_cosKernel₀ 0` (nat-indexed positive-index expansion)
  combined with `evenKernel_eq_cosKernel_of_zero`. At `a = 0`, the cosine factor
  `Real.cos (2π · 0 · (n+1)) = cos 0 = 1` disappears, yielding

    `HasSum (fun n : ℕ => 2 · exp(−π · (n+1)² · y)) (evenKernel 0 y − 1)`.

- Peel off the `n = 0` term (giving `2·exp(−π·y)`, the `k = 1` term of the theta
  series) via `Summable.tsum_eq_zero_add` applied to the summable function
  `n ↦ 2 · exp(−π · (n+1)² · y)`, yielding

    `evenKernel 0 y − 1 = 2·exp(−π·y) + ∑' n, 2·exp(−π · (n+2)² · y)`.

- The tail `∑' n, 2·exp(−π · (n+2)² · y)` is nonnegative (each summand is
  manifestly nonneg), giving `∀ y > 0, 0 ≤ evenKernel 0 y − 1 − 2·exp(−π·y)`.

- Definitions:
  - `I_15 := ∫ y in Ioi 1, (evenKernel 0 y − 1) · y^(−3/4) · cos((15/2) log y)`.
  - `J_1 := 2 · ∫ y in Ioi 1, exp(−π·y) · y^(−3/4) · cos((15/2) log y)`.
  - `R_geq_2 := I_15 − J_1`.

  The identity `I_15 = J_1 + R_geq_2` is definitional. r314 will prove
  `R_geq_2 = ∫ y in Ioi 1, (evenKernel 0 y − 1 − 2·exp(−π·y)) · y^(−3/4) · cos((15/2) log y)`
  via integrability + linearity, then bound `|R_geq_2|`.

- Forward chain-closer bridge `Xi_Positive_At_15_from_J_1_and_R_geq_2_bounds`:
  taking `L ≤ J_1`, `|R_geq_2| ≤ E`, and `4/901 < L − E`, we conclude
  `Xi_Positive_At_15` via r312's `Xi_Positive_At_15_from_folded_cosine_integral_lower_bound`
  applied at `L − E`.

## Framework-first status

NOT a numerical discharge. Exact theta identity + definitional split + bridge,
ready for the certified numerical enclosure in r314 (`|R_geq_2|` bound) and
r315 (`J_1` lower bound). Standing rules absolute: no numerical approximation
in this landing, no `sorry`, no `native_decide`, no floating-point-as-proof,
no hidden oracle, no assumed transcendental enclosure.

The theta identity is established rigorously via mathlib's `HasSum` machinery;
tail positivity from the manifestly-nonneg summand.

## r314+ direction

- **r314**: prove `R_geq_2 = ∫ y in Ioi 1, (evenKernel 0 y − 1 − 2·exp(−π·y)) · y^(−3/4) · cos((15/2) log y)`
  (via integrability of piece_1 = `2·exp(−π·y) · y^(−3/4) · cos(·)` on `Ioi 1`
  from `integrable_of_isBigO_exp_neg`, integrability of `I_15` integrand from
  r312's `MellinConvergent`-based chain, `integral_add`/`integral_sub`).
  Then bound `∀ y ≥ 1, 0 ≤ evenKernel 0 y − 1 − 2·exp(−π·y) ≤ (2·exp(−4π·y)) · C`
  for certified `C = 1/(1 − exp(−4π)) ≤ 2` (via geometric bound on
  `∑_{k≥2} exp(−π(k² − 4))`). Then `|R_geq_2| ≤ 2C · exp(−4π)/(4π)`; rationalize
  via `exp(−4π) < 1/256` from mathlib exp-bound machinery.

- **r315**: certified `J_1 > L` via `t = log y` substitution transforming to
  `2·∫_0^∞ exp(−π·e^t) · e^(t/4) · cos((15/2) t) dt`; explicit truncation `T`,
  rigorous exp/cos Taylor bounds on `[0, T]`, tail bound on `[T, ∞)`, sum to
  rational `L > 4/901 + E`.

- **r316**: apply `Xi_Positive_At_15_from_J_1_and_R_geq_2_bounds` with r314's `E`
  and r315's `L` to discharge `Xi_Positive_At_15`.

Book anchors: Ch 20 § 20.4 (RH via Fractal Resonance), Ch 34A § 34A.5.
Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6.
-/

import PF.Analytic.CompletedZeta0MellinFoldedCosineIntegralExplicit_r312
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.MellinTransform
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace PrincipiaTractalis.ChiPositive15ThetaTruncation

open Complex MeasureTheory Set Real
open HurwitzZeta
open PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit

/-! ## §1 The pointwise theta series identity for `evenKernel 0 y − 1`. -/

/-- **`hasSum_evenKernel_zero_sub_one`** — for `y > 0`,

  `HasSum (fun n : ℕ => 2 · rexp (−π · (n + 1)² · y)) (evenKernel 0 y − 1)`.

Via `HurwitzZeta.hasSum_nat_cosKernel₀ 0` (which gives the sum with
`Real.cos (2π · 0 · (n+1)) = cos 0 = 1` factor) + `evenKernel_eq_cosKernel_of_zero`. -/
theorem hasSum_evenKernel_zero_sub_one {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y))
           (evenKernel 0 y - 1) := by
  have h := hasSum_nat_cosKernel₀ (0 : ℝ) hy
  -- h : HasSum (fun n => 2 * Real.cos (2*π*0*(n+1)) * rexp (-π*(n+1)²*y)) (cosKernel (↑0 : UnitAddCircle) y - 1)
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one] at h
  -- After simp: h : HasSum (fun n => 2 * rexp (-π * (↑n + 1)² * y)) (cosKernel (↑0 : UnitAddCircle) y - 1)
  -- (↑0 : ℝ → UnitAddCircle) = (0 : UnitAddCircle) via QuotientAddGroup.mk_zero.
  have h_zero : ((0 : ℝ) : UnitAddCircle) = 0 := by
    change ((QuotientAddGroup.mk (0 : ℝ)) : UnitAddCircle) = 0
    exact QuotientAddGroup.mk_zero _
  rw [h_zero] at h
  rw [← evenKernel_eq_cosKernel_of_zero] at h
  exact h

/-- **`evenKernel_zero_sub_one_split_at_one`** — the pointwise split at the `n = 0`
term (which is `2·exp(−π·y)`, the `k = 1` term of the theta series):

  `∀ y > 0, evenKernel 0 y − 1 = 2·exp(−π·y) + ∑' n : ℕ, 2·exp(−π·(n+2)²·y)`.

Via `Summable.tsum_eq_zero_add` on the `n = 0` peel-off of the series
`n ↦ 2·exp(−π·(n+1)²·y)`. At `n = 0`: value is `2·exp(−π·y)`. At `n ↦ n + 1`:
value is `2·exp(−π·(n+2)²·y)`. -/
theorem evenKernel_zero_sub_one_split_at_one {y : ℝ} (hy : 0 < y) :
    evenKernel 0 y - 1
      = 2 * Real.exp (-Real.pi * y)
          + ∑' n : ℕ, 2 * Real.exp (-Real.pi * ((n : ℝ) + 2)^2 * y) := by
  have h_sum := (hasSum_evenKernel_zero_sub_one hy).tsum_eq
  have h_summable : Summable (fun n : ℕ => 2 * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y)) :=
    (hasSum_evenKernel_zero_sub_one hy).summable
  have h_peel := h_summable.tsum_eq_zero_add
  rw [← h_sum, h_peel]
  congr 1
  · push_cast; ring_nf
  · congr 1
    funext b
    push_cast
    ring_nf

/-- **`tail_nonneg_of_pos`** — the "tail" part `evenKernel 0 y − 1 − 2·exp(−π·y)`
is nonnegative for `y > 0`, because it equals a `tsum` of manifestly nonneg terms
`2·exp(−π·(n+2)²·y) ≥ 0`. -/
theorem tail_nonneg_of_pos {y : ℝ} (hy : 0 < y) :
    0 ≤ evenKernel 0 y - 1 - 2 * Real.exp (-Real.pi * y) := by
  have h := evenKernel_zero_sub_one_split_at_one hy
  linarith [tsum_nonneg
    (fun n : ℕ => (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-Real.pi * ((n : ℝ) + 2)^2 * y)))]

/-! ## §2 Definitions: `I_15`, `J_1`, `R_geq_2`. -/

/-- **`I_15`** — the r312 folded cosine integral target:

  `I_15 := ∫ y in Ioi 1, (evenKernel 0 y − 1) · y^(−3/4) · cos((15/2) log y)`. -/
noncomputable def I_15 : ℝ :=
  ∫ y in Ioi (1 : ℝ),
    (evenKernel 0 y - 1) * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y)

/-- **`J_1`** — the `n = 1` (`k = 1` in the theta series) cosine integral:

  `J_1 := 2 · ∫ y in Ioi 1, exp(−π·y) · y^(−3/4) · cos((15/2) log y)`. -/
noncomputable def J_1 : ℝ :=
  2 * ∫ y in Ioi (1 : ℝ),
    Real.exp (-Real.pi * y) * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y)

/-- **`R_geq_2`** — the tail (indices `k ≥ 2` in the theta series) contribution,
DEFINED as the residual `I_15 − J_1`:

  `R_geq_2 := I_15 − J_1`.

r314 will prove the equivalent integral form
`R_geq_2 = ∫ y in Ioi 1, (evenKernel 0 y − 1 − 2·exp(−π·y)) · y^(−3/4) · cos((15/2) log y)`
and bound `|R_geq_2|` via the tail estimate. -/
noncomputable def R_geq_2 : ℝ := I_15 - J_1

/-! ## §3 The definitional split identity `I_15 = J_1 + R_geq_2`. -/

/-- **`I_15_split`** — the split identity, definitional in this formulation:

  `I_15 = J_1 + R_geq_2`.

Since `R_geq_2 := I_15 − J_1`, this is immediate via `sub_add_cancel`. -/
theorem I_15_split : I_15 = J_1 + R_geq_2 := by
  unfold R_geq_2
  ring

/-- **`i_15_eq_folded_cosine_integral`** — connection to r312's folded cosine
integral: `I_15` (as defined here) equals the integral appearing in r312's
`re_mellin_F_at_q_eq_two_folded_cosine_integral` and
`Xi_Positive_At_15_from_folded_cosine_integral_lower_bound`. Definitional. -/
theorem i_15_eq_folded_cosine_integral :
    I_15 = ∫ y in Ioi (1 : ℝ),
      (evenKernel 0 y - 1) * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y) := rfl

/-! ## §4 Forward chain-closer bridge. -/

/-- **`Xi_Positive_At_15_from_J_1_and_R_geq_2_bounds`** — forward chain-closer:
given rational-level lower bound `L` on `J_1`, rational-level upper bound `E`
on `|R_geq_2|`, with `4/901 < L − E`, we discharge `Xi_Positive_At_15`.

Since `R_geq_2 = I_15 − J_1`, we have `J_1 + R_geq_2 = I_15`. From `|R_geq_2| ≤ E`
we get `R_geq_2 ≥ −E`, hence `I_15 = J_1 + R_geq_2 ≥ L − E`. Combining with
`4/901 < L − E` and r312's chain-closer discharges `Xi_Positive_At_15`.

r314 will supply `E`, r315 will supply `L`, this bridge closes to
`Xi_Positive_At_15`. -/
theorem Xi_Positive_At_15_from_J_1_and_R_geq_2_bounds
    {L E : ℝ} (hL : L ≤ J_1) (hE : |R_geq_2| ≤ E) (h_gap : (4 : ℝ)/901 < L - E) :
    PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning.Xi_Positive_At_15 := by
  refine Xi_Positive_At_15_from_folded_cosine_integral_lower_bound (a := L - E) h_gap ?_
  -- Need: L - E ≤ ∫ y in Ioi 1, (evenKernel 0 y - 1) · y^(-3/4) · cos((15/2) log y) = I_15
  rw [← i_15_eq_folded_cosine_integral, I_15_split]
  -- Goal: L - E ≤ J_1 + R_geq_2
  have h_R_lower : -E ≤ R_geq_2 := neg_le_of_abs_le hE
  linarith

/-! ## §5 Axiom checks. -/

#print axioms
  PrincipiaTractalis.ChiPositive15ThetaTruncation.hasSum_evenKernel_zero_sub_one
#print axioms
  PrincipiaTractalis.ChiPositive15ThetaTruncation.evenKernel_zero_sub_one_split_at_one
#print axioms
  PrincipiaTractalis.ChiPositive15ThetaTruncation.tail_nonneg_of_pos
#print axioms
  PrincipiaTractalis.ChiPositive15ThetaTruncation.I_15_split
#print axioms
  PrincipiaTractalis.ChiPositive15ThetaTruncation.i_15_eq_folded_cosine_integral
#print axioms
  PrincipiaTractalis.ChiPositive15ThetaTruncation.Xi_Positive_At_15_from_J_1_and_R_geq_2_bounds

end PrincipiaTractalis.ChiPositive15ThetaTruncation
