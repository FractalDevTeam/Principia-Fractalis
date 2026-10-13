/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import PF.Analytic.RiemannXiZeroCountLowerBound_r331f
import Mathlib.Analysis.Analytic.Order

/-!
# RH below height 15 — the zero-count exhaustion step (the non-numerical "Gap B")

`codex/RH_BELOW_15_ROUTE_2026-10-01.md` splits `riemannHypothesis_below_15` into
two independent pieces once the contour value is `2`:

* **numerical** — the three right-edge sign facts R1/R2/R3 (open; the t-boxed
  interval campaign), which give `RectangleIntegral' (logDeriv ξ) zF wF = 2`;
* **non-numerical** — turning that contour value into off-line exclusion.

`r331e`'s `xi_full_rectangle_zero_count_identity` evaluates the contour as
`∑_{ρ ∈ Z} (analyticOrderNatAt ξ ρ : ℂ)` over the finite zero set `Z` in the
rectangle. This file supplies the non-numerical bridge: **if that multiplicity
sum is `2`, then every zero in the rectangle is one of the two reflection
partners already known unconditionally** (`two_distinct_critical_zeros_exists`),
i.e. `XiRectangleCountAtMostTwo`, whence `rh_below_15_of_count_le_two` gives RH on
the rectangle.

The two inputs that `r331e` + the contour reduction supply are taken here as
explicit hypotheses `hmem` (the zero-set membership characterisation, exactly
`Set.Finite.mem_toFinset` of `finite_zeros_rectangle`) and `hsum` (the sum = 2).
Both are already proven in the corpus; discharging them is mechanical wiring,
deferred only because `r331e`/`RightEdgeSigns` oleans are not built at this pin
(r331e still imports the autoImplicit-broken r331c).

**Scope.** `riemannHypothesis_below_15` is RH on one finite rectangle, classically
known since Riemann and Gram. Nothing here bears on the open problem. The new
content is the exhaustion argument; everything else is standard mathlib.
-/

set_option autoImplicit false

namespace PrincipiaTractalis
namespace RHBelow15CountExhaustion

open Complex Finset Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.XiZeroCountLowerBound

/-- A genuine zero of `ξ` has order `≥ 1`: `ξ` is entire, so `AnalyticAt`, and it
is not eventually zero (`ξ 1 = 1/2 ≠ 0` on the connected plane), so
`analyticOrderAt ξ z` is neither `0` nor `⊤`, hence its `ℕ`-projection is `≥ 1`. -/
lemma one_le_order_of_zero {z : ℂ} (hz : riemannXiEntire z = 0) :
    1 ≤ analyticOrderNatAt riemannXiEntire z := by
  have hAna : ∀ w : ℂ, AnalyticAt ℂ riemannXiEntire w :=
    fun w => differentiable_riemannXiEntire.analyticAt w
  have hξ1 : riemannXiEntire 1 = 1 / 2 := by
    simp only [riemannXiEntire]; ring
  have hξ1ne : riemannXiEntire 1 ≠ 0 := by rw [hξ1]; norm_num
  have hne0 : analyticOrderAt riemannXiEntire z ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hAna z, hz⟩
  have hAnaUniv : AnalyticOnNhd ℂ riemannXiEntire Set.univ := fun w _ => hAna w
  have hne_top : analyticOrderAt riemannXiEntire z ≠ ⊤ := by
    have hiff := hAnaUniv.exists_analyticOrderAt_ne_top_iff_forall isConnected_univ
    have h1 : analyticOrderAt riemannXiEntire 1 ≠ ⊤ := by
      simp only [ne_eq, analyticOrderAt_eq_top]
      intro hcon
      exact hξ1ne hcon.self_of_nhds
    exact hiff.mp ⟨⟨1, Set.mem_univ 1⟩, h1⟩ ⟨z, Set.mem_univ z⟩
  have hnat : analyticOrderNatAt riemannXiEntire z = (analyticOrderAt riemannXiEntire z).toNat := rfl
  rw [Nat.one_le_iff_ne_zero, hnat, ne_eq, ENat.toNat_eq_zero, not_or]
  exact ⟨hne0, hne_top⟩

/-- **Exhaustion.** If the rectangle's zero multiplicities sum to `2` and two
distinct zeros are already known on the critical line, then every zero in the
rectangle is one of those two — i.e. `XiRectangleCountAtMostTwo`. -/
theorem xiRectangleCountAtMostTwo_of_zeroSum
    (S : Finset ℂ)
    (hmem : ∀ ρ : ℂ, ρ ∈ S ↔
      (0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ -15 ≤ ρ.im ∧ ρ.im ≤ 15 ∧ riemannXiEntire ρ = 0))
    (hsum : ∑ ρ ∈ S, (analyticOrderNatAt riemannXiEntire ρ : ℂ) = 2) :
    XiRectangleCountAtMostTwo := by
  intro σ t h0 h1 hm hM hz
  obtain ⟨t₀, ht1, ht15, hza, hzb, hab⟩ := two_distinct_critical_zeros_exists
  have ha : (⟨1 / 2, t₀⟩ : ℂ) ∈ S := by
    rw [hmem]
    refine ⟨?_, ?_, ?_, ?_, hza⟩
    · show (0 : ℝ) ≤ 1 / 2; norm_num
    · show (1 : ℝ) / 2 ≤ 1; norm_num
    · show (-15 : ℝ) ≤ t₀; linarith
    · show t₀ ≤ (15 : ℝ); linarith
  have hb : (⟨1 / 2, -t₀⟩ : ℂ) ∈ S := by
    rw [hmem]
    refine ⟨?_, ?_, ?_, ?_, hzb⟩
    · show (0 : ℝ) ≤ 1 / 2; norm_num
    · show (1 : ℝ) / 2 ≤ 1; norm_num
    · show (-15 : ℝ) ≤ -t₀; linarith
    · show -t₀ ≤ (15 : ℝ); linarith
  have hρ : (⟨σ, t⟩ : ℂ) ∈ S := by
    rw [hmem]; exact ⟨h0, h1, hm, hM, hz⟩
  have hpos : ∀ x ∈ S, 1 ≤ analyticOrderNatAt riemannXiEntire x :=
    fun x hx => one_le_order_of_zero ((hmem x).mp hx).2.2.2.2
  have hsumN : ∑ x ∈ S, analyticOrderNatAt riemannXiEntire x = 2 := by
    have hc : ((∑ x ∈ S, analyticOrderNatAt riemannXiEntire x : ℕ) : ℂ) = 2 := by
      rw [Nat.cast_sum]; exact hsum
    exact_mod_cast hc
  have hcard : S.card ≤ 2 := by
    have hone : S.card = ∑ _x ∈ S, 1 := by rw [Finset.card_eq_sum_ones]
    rw [hone]
    calc ∑ _x ∈ S, 1 ≤ ∑ x ∈ S, analyticOrderNatAt riemannXiEntire x :=
          Finset.sum_le_sum hpos
      _ = 2 := hsumN
  have hsub : ({(⟨1 / 2, t₀⟩ : ℂ), (⟨1 / 2, -t₀⟩ : ℂ)} : Finset ℂ) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact ha
    · rw [Finset.mem_singleton.mp h]; exact hb
  have hcard2 : ({(⟨1 / 2, t₀⟩ : ℂ), (⟨1 / 2, -t₀⟩ : ℂ)} : Finset ℂ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hab),
      Finset.card_singleton]
  have hSeq : S = ({(⟨1 / 2, t₀⟩ : ℂ), (⟨1 / 2, -t₀⟩ : ℂ)} : Finset ℂ) :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2]; exact hcard)).symm
  rw [hSeq] at hρ
  rcases Finset.mem_insert.mp hρ with h | h
  · have he := Complex.ext_iff.mp h
    exact ⟨t₀, ht1, ht15, Or.inl he.2, he.1⟩
  · rw [Finset.mem_singleton] at h
    have he := Complex.ext_iff.mp h
    exact ⟨t₀, ht1, ht15, Or.inr he.2, he.1⟩

/-- **RH below height 15 from the zero-count sum.** Composes the exhaustion with
`r331f`'s `rh_below_15_of_count_le_two`. Conditional only on the multiplicity sum
being `2` — exactly what `r331e`'s count identity plus the contour value `2`
(RightEdgeSigns, from R1 ∧ R2 ∧ R3) deliver. -/
theorem rh_below_15_of_zeroSum
    (S : Finset ℂ)
    (hmem : ∀ ρ : ℂ, ρ ∈ S ↔
      (0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ -15 ≤ ρ.im ∧ ρ.im ≤ 15 ∧ riemannXiEntire ρ = 0))
    (hsum : ∑ ρ ∈ S, (analyticOrderNatAt riemannXiEntire ρ : ℂ) = 2) :
    ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → -15 ≤ t → t ≤ 15 →
      riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1 / 2 :=
  rh_below_15_of_count_le_two (xiRectangleCountAtMostTwo_of_zeroSum S hmem hsum)

end RHBelow15CountExhaustion
end PrincipiaTractalis

#print axioms PrincipiaTractalis.RHBelow15CountExhaustion.one_le_order_of_zero
#print axioms PrincipiaTractalis.RHBelow15CountExhaustion.xiRectangleCountAtMostTwo_of_zeroSum
#print axioms PrincipiaTractalis.RHBelow15CountExhaustion.rh_below_15_of_zeroSum
