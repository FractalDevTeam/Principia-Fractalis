/-
# polyLog Analyticity on the FULL Open Unit Ball for Negative Integer s
# (s ∈ {-1, -2, -3, -4}) and Full Disc-Agreement Capstones

This file LIFTS the pointwise analyticity established in
`PolyLogAnalyticAtHalfNegInt.lean` (which only gives analyticity at
`z = 1/2`) to **on-disc** analyticity

```
AnalyticOnNhd ℂ (polyLog (-N)) (Metric.ball 0 1)
```

for `N ∈ {1, 2, 3, 4}`, by leveraging the unconditional rational
closed forms

```
polyLog (-1) z = z / (1 - z)^2                       (NegOneDischarge)
polyLog (-2) z = z (1 + z) / (1 - z)^3               (NegTwoDischarge)
polyLog (-3) z = z (1 + 4z + z^2) / (1 - z)^4        (NegThreeDischarge)
polyLog (-4) z = z (1 + 11z + 11z^2 + z^3) / (1-z)^5 (NegFourDischarge)
```

on the open unit disc `‖z‖ < 1`.

This is the disc-analytic upgrade that
`PolyLogAnalyticAtHalfNegInt.lean` explicitly flagged as the residual
needed to extend `discAgreementReduced_of_germAtHalf` (and ancestors)
to the negative-integer values. Once we have on-disc analyticity, we
construct a sibling of `polyLog_eq_jonquieresExpansion_on_preconnected`
that takes the polylog analyticity as a hypothesis directly (instead
of deriving it from `0 ≤ Re s` via `polyLog_analyticOnNhd_ball`), and
the entire chain extends cleanly.

## Strategy per negative integer

Each `polyLog (-N) z` agrees with a rational function `R_N(z)` on the
OPEN UNIT BALL `Metric.ball 0 1`. The rational function `R_N` has
denominator `(1 - z)^(N+1)`, which is non-zero on the ball (the only
zero of `1 - z` is at `z = 1`, NOT in the ball). Hence `R_N` is
analytic on the ball via standard mathlib `AnalyticOnNhd.div` /
`.pow` / `.mul` machinery. Then `AnalyticOnNhd.congr` transfers this
analyticity to `polyLog (-N)` using the pointwise equality on the
ball as an EqOn (then upgraded to EventuallyEq locally).

## What this file delivers (axiom-free, no `sorry`)

1. Four `rational_neg_N_analyticOnNhd_ball` lemmas — the rational
   closed forms `R_N` are analytic on `Metric.ball 0 1`.

2. Four `polyLog_analyticOnNhd_ball_neg_N` lemmas — **MAIN**:
   `polyLog (-N)` is analytic on `Metric.ball 0 1` for `N ∈ {1,2,3,4}`.

3. A sibling propagation theorem
   `polyLog_eq_jonquieresExpansion_on_preconnected_of_analytic` —
   identical to `polyLog_eq_jonquieresExpansion_on_preconnected`
   but accepts `AnalyticOnNhd ℂ (polyLog s) (Metric.ball 0 1)` as a
   hypothesis instead of `0 ≤ s.re`.

4. Sibling capstones
   `discAgreementReduced_of_sharper_and_reachability_of_analytic`,
   `discAgreementReduced_of_germAtHalf_of_analytic`,
   `discAgreementReduced_of_frequentAgreement_of_analytic`.

5. Final capstones
   `discAgreementReduced_at_neg_one_of_germ`,
   `discAgreementReduced_at_neg_two_of_germ`,
   `discAgreementReduced_at_neg_three_of_germ`,
   `discAgreementReduced_at_neg_four_of_germ` — disc-wide identity
   at each `s ∈ {-1, -2, -3, -4}` from analyticity-of-the-expansion
   + germ at 1/2 + slit-disc reachability.

Stage L22 — On-ball analyticity of polyLog at negative integers + full
disc-agreement capstones at s ∈ {-1,-2,-3,-4}.
-/

import PF.Analytic.PolyLogAnalyticAtHalfNegInt
import PF.Analytic.JonquieresAtNegThreeDischarge
import PF.Analytic.JonquieresAtNegFourDischarge
import PF.Analytic.GermAtHalfDischarge

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Analyticity of the rational closed forms on the open unit ball

The denominator `(1 - z)^(N+1)` vanishes only at `z = 1`, which is
NOT in `Metric.ball 0 1`. So `R_N` is analytic on the ball. -/

/-- For `z ∈ Metric.ball 0 1`, we have `1 - z ≠ 0`. -/
private theorem one_sub_ne_zero_of_mem_ball
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : (1 : ℂ) - z ≠ 0 := by
  intro h
  have h_eq : z = 1 := by linear_combination -h
  have h_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  rw [h_eq] at h_norm
  simp at h_norm

/-- `fun z => z / (1 - z)^2` is analytic on the open unit ball. -/
theorem rational_neg_one_analyticOnNhd_ball :
    AnalyticOnNhd ℂ (fun z : ℂ => z / (1 - z)^2) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have h_num : AnalyticAt ℂ (fun z : ℂ => z) z := analyticAt_id
  have h_one_sub : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) z :=
    analyticAt_const.sub analyticAt_id
  have h_den : AnalyticAt ℂ (fun z : ℂ => (1 - z)^2) z := h_one_sub.pow 2
  have h_den_ne : (fun z : ℂ => (1 - z)^2) z ≠ 0 := by
    simp only
    exact pow_ne_zero _ (one_sub_ne_zero_of_mem_ball hz)
  exact h_num.fun_div h_den h_den_ne

/-- `fun z => z * (1 + z) / (1 - z)^3` is analytic on the open unit ball. -/
theorem rational_neg_two_analyticOnNhd_ball :
    AnalyticOnNhd ℂ (fun z : ℂ => z * (1 + z) / (1 - z)^3)
      (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have h_z : AnalyticAt ℂ (fun z : ℂ => z) z := analyticAt_id
  have h_one_add : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) + z) z :=
    analyticAt_const.add analyticAt_id
  have h_num : AnalyticAt ℂ (fun z : ℂ => z * (1 + z)) z :=
    h_z.mul h_one_add
  have h_one_sub : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) z :=
    analyticAt_const.sub analyticAt_id
  have h_den : AnalyticAt ℂ (fun z : ℂ => (1 - z)^3) z := h_one_sub.pow 3
  have h_den_ne : (fun z : ℂ => (1 - z)^3) z ≠ 0 := by
    simp only
    exact pow_ne_zero _ (one_sub_ne_zero_of_mem_ball hz)
  exact h_num.fun_div h_den h_den_ne

/-- `fun z => z * (1 + 4z + z^2) / (1 - z)^4` is analytic on the open unit ball. -/
theorem rational_neg_three_analyticOnNhd_ball :
    AnalyticOnNhd ℂ (fun z : ℂ => z * (1 + 4*z + z^2) / (1 - z)^4)
      (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have h_z : AnalyticAt ℂ (fun z : ℂ => z) z := analyticAt_id
  -- 1 + 4z + z^2
  have h_4z : AnalyticAt ℂ (fun z : ℂ => 4 * z) z :=
    analyticAt_const.mul analyticAt_id
  have h_z2 : AnalyticAt ℂ (fun z : ℂ => z^2) z := analyticAt_id.pow 2
  have h_1plus4z : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) + 4 * z) z :=
    analyticAt_const.add h_4z
  have h_poly : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) + 4*z + z^2) z :=
    h_1plus4z.add h_z2
  have h_num : AnalyticAt ℂ (fun z : ℂ => z * (1 + 4*z + z^2)) z :=
    h_z.mul h_poly
  have h_one_sub : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) z :=
    analyticAt_const.sub analyticAt_id
  have h_den : AnalyticAt ℂ (fun z : ℂ => (1 - z)^4) z := h_one_sub.pow 4
  have h_den_ne : (fun z : ℂ => (1 - z)^4) z ≠ 0 := by
    simp only
    exact pow_ne_zero _ (one_sub_ne_zero_of_mem_ball hz)
  exact h_num.fun_div h_den h_den_ne

/-- `fun z => z * (1 + 11z + 11z^2 + z^3) / (1 - z)^5` is analytic on the
    open unit ball. -/
theorem rational_neg_four_analyticOnNhd_ball :
    AnalyticOnNhd ℂ
      (fun z : ℂ => z * (1 + 11*z + 11*z^2 + z^3) / (1 - z)^5)
      (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have h_z : AnalyticAt ℂ (fun z : ℂ => z) z := analyticAt_id
  have h_11z : AnalyticAt ℂ (fun z : ℂ => 11 * z) z :=
    analyticAt_const.mul analyticAt_id
  have h_z2 : AnalyticAt ℂ (fun z : ℂ => z^2) z := analyticAt_id.pow 2
  have h_z3 : AnalyticAt ℂ (fun z : ℂ => z^3) z := analyticAt_id.pow 3
  have h_11z2 : AnalyticAt ℂ (fun z : ℂ => 11 * z^2) z :=
    analyticAt_const.mul h_z2
  have h_1plus11z : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) + 11 * z) z :=
    analyticAt_const.add h_11z
  have h_1plus11z_plus11z2 :
      AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) + 11 * z + 11 * z^2) z :=
    h_1plus11z.add h_11z2
  have h_poly :
      AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) + 11*z + 11*z^2 + z^3) z :=
    h_1plus11z_plus11z2.add h_z3
  have h_num : AnalyticAt ℂ (fun z : ℂ => z * (1 + 11*z + 11*z^2 + z^3)) z :=
    h_z.mul h_poly
  have h_one_sub : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) z :=
    analyticAt_const.sub analyticAt_id
  have h_den : AnalyticAt ℂ (fun z : ℂ => (1 - z)^5) z := h_one_sub.pow 5
  have h_den_ne : (fun z : ℂ => (1 - z)^5) z ≠ 0 := by
    simp only
    exact pow_ne_zero _ (one_sub_ne_zero_of_mem_ball hz)
  exact h_num.fun_div h_den h_den_ne

/-! ## Polylog at negative integers is analytic on the OPEN UNIT BALL

For each `N ∈ {1, 2, 3, 4}`, the polylog `polyLog (-N)` is analytic
on the full open unit ball. The proof transfers analyticity from the
rational closed form via `AnalyticAt.congr`, applied pointwise on
the ball; the open ball is a neighborhood of each of its points. -/

/-- **`polyLog (-1)` is analytic on `Metric.ball 0 1`** (the full open
    unit disc).

    Proof: at each `z₀ ∈ ball 0 1`, the open ball is a nhd of `z₀`,
    so the pointwise identity `polyLog (-1) z = z/(1-z)^2` (on the
    ball) is an `EventuallyEq` at `z₀`. The rational function is
    analytic at `z₀` (by `rational_neg_one_analyticOnNhd_ball`).
    Transfer via `AnalyticAt.congr`. -/
theorem polyLog_analyticOnNhd_ball_neg_one :
    AnalyticOnNhd ℂ (polyLog (-1)) (Metric.ball (0 : ℂ) 1) := by
  intro z₀ hz₀
  have h_rat : AnalyticAt ℂ (fun z : ℂ => z / (1 - z)^2) z₀ :=
    rational_neg_one_analyticOnNhd_ball z₀ hz₀
  have h_ball_nhd : Metric.ball (0 : ℂ) 1 ∈ nhds z₀ :=
    Metric.isOpen_ball.mem_nhds hz₀
  have h_eventually :
      (fun z : ℂ => z / (1 - z)^2) =ᶠ[nhds z₀] polyLog (-1) := by
    filter_upwards [h_ball_nhd] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact (polyLog_neg_one_eq_geom_sq z h_norm).symm
  exact h_rat.congr h_eventually

/-- **`polyLog (-2)` is analytic on `Metric.ball 0 1`**. -/
theorem polyLog_analyticOnNhd_ball_neg_two :
    AnalyticOnNhd ℂ (polyLog (-2)) (Metric.ball (0 : ℂ) 1) := by
  intro z₀ hz₀
  have h_rat : AnalyticAt ℂ (fun z : ℂ => z * (1 + z) / (1 - z)^3) z₀ :=
    rational_neg_two_analyticOnNhd_ball z₀ hz₀
  have h_ball_nhd : Metric.ball (0 : ℂ) 1 ∈ nhds z₀ :=
    Metric.isOpen_ball.mem_nhds hz₀
  have h_eventually :
      (fun z : ℂ => z * (1 + z) / (1 - z)^3) =ᶠ[nhds z₀] polyLog (-2) := by
    filter_upwards [h_ball_nhd] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact (polyLog_neg_two_eq_rational z h_norm).symm
  exact h_rat.congr h_eventually

/-- **`polyLog (-3)` is analytic on `Metric.ball 0 1`**. -/
theorem polyLog_analyticOnNhd_ball_neg_three :
    AnalyticOnNhd ℂ (polyLog (-3)) (Metric.ball (0 : ℂ) 1) := by
  intro z₀ hz₀
  have h_rat :
      AnalyticAt ℂ (fun z : ℂ => z * (1 + 4*z + z^2) / (1 - z)^4) z₀ :=
    rational_neg_three_analyticOnNhd_ball z₀ hz₀
  have h_ball_nhd : Metric.ball (0 : ℂ) 1 ∈ nhds z₀ :=
    Metric.isOpen_ball.mem_nhds hz₀
  have h_eventually :
      (fun z : ℂ => z * (1 + 4*z + z^2) / (1 - z)^4)
        =ᶠ[nhds z₀] polyLog (-3) := by
    filter_upwards [h_ball_nhd] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact (polyLog_neg_three_eq_rational z h_norm).symm
  exact h_rat.congr h_eventually

/-- **`polyLog (-4)` is analytic on `Metric.ball 0 1`**. -/
theorem polyLog_analyticOnNhd_ball_neg_four :
    AnalyticOnNhd ℂ (polyLog (-4)) (Metric.ball (0 : ℂ) 1) := by
  intro z₀ hz₀
  have h_rat :
      AnalyticAt ℂ (fun z : ℂ => z * (1 + 11*z + 11*z^2 + z^3) / (1 - z)^5) z₀ :=
    rational_neg_four_analyticOnNhd_ball z₀ hz₀
  have h_ball_nhd : Metric.ball (0 : ℂ) 1 ∈ nhds z₀ :=
    Metric.isOpen_ball.mem_nhds hz₀
  have h_eventually :
      (fun z : ℂ => z * (1 + 11*z + 11*z^2 + z^3) / (1 - z)^5)
        =ᶠ[nhds z₀] polyLog (-4) := by
    filter_upwards [h_ball_nhd] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact (polyLog_neg_four_eq_rational z h_norm).symm
  exact h_rat.congr h_eventually

/-! ## Generic propagation theorem (polylog-analyticity hypothesis variant)

This is a sibling of `polyLog_eq_jonquieresExpansion_on_preconnected`
that takes `AnalyticOnNhd ℂ (polyLog s) (Metric.ball 0 1)` as a
hypothesis instead of `0 ≤ s.re`. The proof is otherwise identical:
the only place `hs` is used in the original is to call
`polyLog_analyticOnNhd_ball hs`, which we now supply directly. -/

/-- **Sibling propagation lemma** (polylog-analyticity hypothesis):
    given a polylog-analyticity hypothesis on the open unit ball
    (replacing `0 ≤ s.re`), the sharper hypothesis, AND a
    preconnected open set `S` containing the witness ball and
    contained in `JonquieresAnalyticDomain ∩ ball 0 1`, the identity
    `polyLog s z = jonquieresExpansion s z` holds for every `z ∈ S`. -/
theorem polyLog_eq_jonquieresExpansion_on_preconnected_of_analytic
    {s : ℂ}
    (h_polyLog_an : AnalyticOnNhd ℂ (polyLog s) (Metric.ball (0 : ℂ) 1))
    (h_sharper : JonquieresIdentitySharperHypothesis s)
    {S : Set ℂ}
    (_hS_open : IsOpen S)
    (hS_pre : IsPreconnected S)
    (hS_sub_dom : S ⊆ JonquieresAnalyticDomain)
    (hS_sub_ball : S ⊆ Metric.ball (0 : ℂ) 1)
    (hS_contains_witness : ∃ z₀ ∈ S, ∃ ρ > 0,
      Metric.ball z₀ ρ ⊆ S ∧
      (∀ z ∈ Metric.ball z₀ ρ, polyLog s z = jonquieresExpansion s z)) :
    ∀ z ∈ S, polyLog s z = jonquieresExpansion s z := by
  obtain ⟨h_an_j, _h_witness⟩ := h_sharper
  obtain ⟨z₀, hz₀_in_S, ρ, hρ_pos, _h_ball_sub_S, h_local_eq⟩ :=
    hS_contains_witness
  -- polyLog analytic on S via the hypothesis (instead of via `hs`).
  have h_an_p : AnalyticOnNhd ℂ (polyLog s) S := by
    intro z hz
    exact h_polyLog_an z (hS_sub_ball hz)
  -- jonquieresExpansion analytic on S (subset of slit disc).
  have h_an_j_on_S : AnalyticOnNhd ℂ (jonquieresExpansion s) S := by
    intro z hz
    refine h_an_j z ?_
    exact ⟨hS_sub_ball hz, hS_sub_dom hz⟩
  -- EventuallyEq at z₀.
  have h_evEq : polyLog s =ᶠ[nhds z₀] jonquieresExpansion s := by
    have h_ball_open : IsOpen (Metric.ball z₀ ρ) := Metric.isOpen_ball
    have h_z₀_mem : z₀ ∈ Metric.ball z₀ ρ := Metric.mem_ball_self hρ_pos
    have h_nhd : Metric.ball z₀ ρ ∈ nhds z₀ := h_ball_open.mem_nhds h_z₀_mem
    filter_upwards [h_nhd] with z hz using h_local_eq z hz
  exact fun z hz =>
    h_an_p.eqOn_of_preconnected_of_eventuallyEq h_an_j_on_S
      hS_pre hz₀_in_S h_evEq hz

/-- **Sibling sharper-and-reachability capstone** (polylog-analyticity
    hypothesis variant). Identical to
    `discAgreementReduced_of_sharper_and_reachability` but takes
    polylog analyticity as a hypothesis. -/
theorem discAgreementReduced_of_sharper_and_reachability_of_analytic
    {s : ℂ}
    (h_polyLog_an : AnalyticOnNhd ℂ (polyLog s) (Metric.ball (0 : ℂ) 1))
    (h_sharper : JonquieresIdentitySharperHypothesis s)
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion s z = polyLog s z := by
  set S : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain with hS_def
  have hS_open : IsOpen S :=
    Metric.isOpen_ball.inter JonquieresAnalyticDomain_isOpen
  have hS_pre : IsPreconnected S := h_reach
  have hS_sub_dom : S ⊆ JonquieresAnalyticDomain := Set.inter_subset_right
  have hS_sub_ball : S ⊆ Metric.ball (0 : ℂ) 1 := Set.inter_subset_left
  obtain ⟨z₀, ρ, hρ_pos, h_sub_ball, h_sub_dom, h_eq⟩ := h_sharper.2
  have h_witness_sub_S : Metric.ball z₀ ρ ⊆ S := by
    intro z hz
    exact ⟨h_sub_ball hz, h_sub_dom hz⟩
  have h_z₀_in_S : z₀ ∈ S :=
    h_witness_sub_S (Metric.mem_ball_self hρ_pos)
  have h_contains : ∃ w₀ ∈ S, ∃ ρ' > 0,
      Metric.ball w₀ ρ' ⊆ S ∧
      (∀ z ∈ Metric.ball w₀ ρ', polyLog s z = jonquieresExpansion s z) := by
    refine ⟨z₀, h_z₀_in_S, ρ, hρ_pos, h_witness_sub_S, h_eq⟩
  have h_id_on_S : ∀ z ∈ S, polyLog s z = jonquieresExpansion s z :=
    polyLog_eq_jonquieresExpansion_on_preconnected_of_analytic
      h_polyLog_an h_sharper hS_open hS_pre hS_sub_dom hS_sub_ball h_contains
  intro z hz
  have hz_in_S : z ∈ S := ⟨hz.2, hz.1⟩
  exact (h_id_on_S z hz_in_S).symm

/-- **Sibling germ-at-half capstone** (polylog-analyticity hypothesis
    variant). Identical to `discAgreementReduced_of_germAtHalf` but
    takes polylog analyticity as a hypothesis. -/
theorem discAgreementReduced_of_germAtHalf_of_analytic
    {s : ℂ}
    (h_polyLog_an : AnalyticOnNhd ℂ (polyLog s) (Metric.ball (0 : ℂ) 1))
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall s)
    (h_germ : JonquieresIdentityPointGermAtHalf s)
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion s z = polyLog s z :=
  discAgreementReduced_of_sharper_and_reachability_of_analytic
    h_polyLog_an
    (jonquieresIdentitySharperHypothesis_of_germAtHalf h_an h_germ)
    h_reach

/-- **Sibling frequent-agreement capstone** (polylog-analyticity
    hypothesis variant). The frequent-agreement reduction to germ
    equality uses analyticity of `polyLog s` AT THE POINT `1/2`,
    obtained by restricting the on-ball analyticity. -/
theorem discAgreementReduced_of_frequentAgreement_of_analytic
    {s : ℂ}
    (h_polyLog_an : AnalyticOnNhd ℂ (polyLog s) (Metric.ball (0 : ℂ) 1))
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall s)
    (h_freq : JonquieresFrequentAgreementAtHalf s)
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion s z = polyLog s z := by
  -- Build the germ equality from frequent agreement using on-ball
  -- analyticity restricted to z = 1/2.
  have h_polyLog_at_half : AnalyticAt ℂ (polyLog s) (1/2 : ℂ) :=
    h_polyLog_an (1/2 : ℂ) half_mem_ball_one
  have h_germ : JonquieresIdentityPointGermAtHalf s := by
    unfold JonquieresIdentityPointGermAtHalf JonquieresIdentityPointGerm
    exact (AnalyticAt.frequently_eq_iff_eventually_eq
      h_polyLog_at_half
      (jonquieresExpansion_analyticAt_half h_an)).mp h_freq
  exact discAgreementReduced_of_germAtHalf_of_analytic
    h_polyLog_an h_an h_germ h_reach

/-! ## Final capstones: full disc-agreement at each s ∈ {-1, -2, -3, -4}

Combine the on-ball analyticity (this file) + the sibling
germ-at-half capstone + the slit-disc reachability theorem. The only
remaining open content per `s` is:

* `JonquieresExpansionAnalyticOnPuncturedBall s` (named hypothesis), AND
* `JonquieresIdentityPointGermAtHalf s` (named hypothesis).

These mirror the s = 0 capstone in `JonquieresAtZeroFinalDischarge.lean`. -/

/-- **CAPSTONE at `s = -1`**: full disc-wide identity from analyticity
    of the Jonquières expansion on the slit disc + the germ at `1/2`
    + slit-disc reachability. The polylog on-ball analyticity is
    supplied by `polyLog_analyticOnNhd_ball_neg_one`. -/
theorem discAgreementReduced_at_neg_one_of_germ
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall (-1))
    (h_germ : JonquieresIdentityPointGermAtHalf (-1))
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion (-1) z = polyLog (-1) z :=
  discAgreementReduced_of_germAtHalf_of_analytic
    polyLog_analyticOnNhd_ball_neg_one h_an h_germ h_reach

/-- **CAPSTONE at `s = -2`**. -/
theorem discAgreementReduced_at_neg_two_of_germ
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall (-2))
    (h_germ : JonquieresIdentityPointGermAtHalf (-2))
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion (-2) z = polyLog (-2) z :=
  discAgreementReduced_of_germAtHalf_of_analytic
    polyLog_analyticOnNhd_ball_neg_two h_an h_germ h_reach

/-- **CAPSTONE at `s = -3`**. -/
theorem discAgreementReduced_at_neg_three_of_germ
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall (-3))
    (h_germ : JonquieresIdentityPointGermAtHalf (-3))
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion (-3) z = polyLog (-3) z :=
  discAgreementReduced_of_germAtHalf_of_analytic
    polyLog_analyticOnNhd_ball_neg_three h_an h_germ h_reach

/-- **CAPSTONE at `s = -4`**. -/
theorem discAgreementReduced_at_neg_four_of_germ
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall (-4))
    (h_germ : JonquieresIdentityPointGermAtHalf (-4))
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion (-4) z = polyLog (-4) z :=
  discAgreementReduced_of_germAtHalf_of_analytic
    polyLog_analyticOnNhd_ball_neg_four h_an h_germ h_reach

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `one_sub_ne_zero_of_mem_ball` — `1 - z ≠ 0` for `z ∈ ball 0 1`.
* `rational_neg_one_analyticOnNhd_ball` — `z/(1-z)^2` analytic on the ball.
* `rational_neg_two_analyticOnNhd_ball` — `z(1+z)/(1-z)^3` analytic on the ball.
* `rational_neg_three_analyticOnNhd_ball` — `z(1+4z+z²)/(1-z)^4` analytic on the ball.
* `rational_neg_four_analyticOnNhd_ball` — `z(1+11z+11z²+z³)/(1-z)^5` analytic on the ball.
* `polyLog_analyticOnNhd_ball_neg_one` — **MAIN**: `polyLog (-1)` analytic
  on `Metric.ball 0 1`.
* `polyLog_analyticOnNhd_ball_neg_two` — **MAIN**: `polyLog (-2)` analytic
  on `Metric.ball 0 1`.
* `polyLog_analyticOnNhd_ball_neg_three` — **MAIN**: `polyLog (-3)` analytic
  on `Metric.ball 0 1`.
* `polyLog_analyticOnNhd_ball_neg_four` — **MAIN**: `polyLog (-4)` analytic
  on `Metric.ball 0 1`.
* `polyLog_eq_jonquieresExpansion_on_preconnected_of_analytic` — sibling
  propagation lemma (polylog-analyticity hypothesis variant).
* `discAgreementReduced_of_sharper_and_reachability_of_analytic` — sibling
  sharper-and-reachability capstone.
* `discAgreementReduced_of_germAtHalf_of_analytic` — sibling germ-at-half
  capstone.
* `discAgreementReduced_of_frequentAgreement_of_analytic` — sibling
  frequent-agreement capstone.
* `discAgreementReduced_at_neg_one_of_germ` — full disc-agreement at `s = -1`.
* `discAgreementReduced_at_neg_two_of_germ` — full disc-agreement at `s = -2`.
* `discAgreementReduced_at_neg_three_of_germ` — full disc-agreement at `s = -3`.
* `discAgreementReduced_at_neg_four_of_germ` — full disc-agreement at `s = -4`.

**Open content at each `s ∈ {-1, -2, -3, -4}` (after this file)**:

Per s, exactly TWO named hypotheses:
* `JonquieresExpansionAnalyticOnPuncturedBall s` (analyticity of the
  expansion on the slit disc).
* `JonquieresIdentityPointGermAtHalf s` (germ equality at `1/2`).

This brings the negative-integer chain into the same shape as the
s = 0 chain capstone `discAgreementReduced_at_zero_of_germ`.

Stage L22 — On-ball analyticity of polyLog at negative integers + full
disc-agreement capstones at s ∈ {-1,-2,-3,-4}.
-/

end PrincipiaTractalis.Analytic.Sheaf
