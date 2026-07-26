/-
# PF.Analytic.XiOnLineZero   (r120)

MILESTONE B5 -- the RH on-line-zero atom
`PositiveOnLineZetaZeroOrdinatesNonempty` is DISCHARGED.

Route B assembly (HARDY_SCOPING_2026-07-24 §3 row B5):

* `Xi 1 < 0` -- free: at `T = 1` the finite part of the theta-integral
  representation is empty, so the whole integral is controlled by the
  B4a tail brick `Xi_tail_bound`: `Xi 1 ≤ -0.8 + 0.03 < 0`.

* `0 < Xi (77/5)` -- the certified-quadrature certificate at
  `t = 15.4`, where `Xi` attains its maximum `≈ 6.6826e-6` between the
  first two critical-line zeros `t ≈ 14.1347` and `t ≈ 21.022`:

    `Xi t = -1/(1/4+t²) + ∫_1^5 FT + ∫_1^5 (g - FT) + ∫_(Ioi 5) g`

  with `FT` the `N = 3` truncated integrand, evaluated by a
  14-segment GRADED composite midpoint rule (474 panels) whose node
  sums are enclosed by the vendored kernel-verified interval engine
  (165 `decide +kernel` panels), and whose panel-local `C²` bound is
  `abs_thetaTermD2_sum_le_at`.

* IVT (`xi_sign_change_implies_on_line_zero`) then produces the zero.

Certified error budget vs `Xi(15.4) = 6.6826e-6`:
  quadrature   `Σ mb_j (d-c)³/(24 n_j²)`  ≈ 3.6e-6
  tail `T = 5`                            ≤ 1.1e-7
  `ω`-truncation `N = 3`                  ≤ 1e-12
  ⇒ certified `Xi(15.4) ≥ 2.9e-6 > 0`.

NO `native_decide`; zero project axioms; zero sorries.
-/

import PF.Analytic.XiOnLineZeroConstants
import PF.Analytic.XiPanels.Seg01
import PF.Analytic.XiPanels.Seg02
import PF.Analytic.XiPanels.Seg03
import PF.Analytic.XiPanels.Seg04
import PF.Analytic.XiPanels.Seg05
import PF.Analytic.XiPanels.Seg06
import PF.Analytic.XiPanels.Seg07
import PF.Analytic.XiPanels.Seg08
import PF.Analytic.XiPanels.Seg09
import PF.Analytic.XiPanels.Seg10
import PF.Analytic.XiPanels.Seg11
import PF.Analytic.XiPanels.Seg12
import PF.Analytic.XiPanels.Seg13
import PF.Analytic.XiPanels.Seg14

namespace PrincipiaTractalis.XiOnLineZero

open Set MeasureTheory Filter
open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open PrincipiaTractalis.XiOnLineZeroCore
open PrincipiaTractalis.XiOnLineZeroConstants
open PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability
open scoped Real Topology

/-! ## §1 -- the truncated integrand at `t = 77/5` -/

/-- The `N = 3` truncated critical-line integrand at `t = 15.4`. -/
noncomputable def FT (y : ℝ) : ℝ := ∑ k ∈ Finset.range 3, thetaTerm (77 / 5 : ℝ) k y

theorem FT_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt FT (∑ k ∈ Finset.range 3, thetaTermD1 (77 / 5 : ℝ) k x) x :=
  hasDerivAt_thetaTerm_sum (77 / 5 : ℝ) 3 hx

theorem FT_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable FT volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro x hx
  have hx0 : 0 < x := by
    rcases le_total a b with h | h
    · rw [Set.uIcc_of_le h] at hx; exact lt_of_lt_of_le ha hx.1
    · rw [Set.uIcc_of_ge h] at hx; exact lt_of_lt_of_le hb hx.1
  exact (FT_hasDerivAt hx0).continuousAt.continuousWithinAt

/-- `FT` IS the `omegaPartial`-truncated theta integrand. -/
theorem trunc_eq_FT :
    (fun u : ℝ ↦ 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((77 / 5 : ℝ) / 2 * Real.log u)
        * omegaPartial 3 u) = FT :=
  truncated_integrand_eq (77 / 5 : ℝ) 3

/-! ## §2 -- the `C²` constants at `t = 77/5` -/

private theorem habs : |(77 : ℝ) / 5| = 77 / 5 := abs_of_pos (by norm_num)

theorem K0_le : thetaTermK (77 / 5 : ℝ) 0 ≤ 285.7 := by
  have hpi : π < 3.141593 := Real.pi_lt_d6
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  unfold thetaTermK
  rw [habs]
  push_cast
  nlinarith [hpi, hpi0]

theorem K1_le : thetaTermK (77 / 5 : ℝ) 1 ≤ 900.4 := by
  have hpi : π < 3.141593 := Real.pi_lt_d6
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  unfold thetaTermK
  rw [habs]
  push_cast
  nlinarith [hpi, hpi0]

theorem K2_le : thetaTermK (77 / 5 : ℝ) 2 ≤ 2714.4 := by
  have hpi : π < 3.141593 := Real.pi_lt_d6
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  unfold thetaTermK
  rw [habs]
  push_cast
  nlinarith [hpi, hpi0]

theorem K_nonneg (n : ℕ) : 0 ≤ thetaTermK (77 / 5 : ℝ) n := by
  unfold thetaTermK
  have h1 : (0 : ℝ) ≤ |(77 : ℝ) / 5| := abs_nonneg _
  positivity

/-- The panel-local `C²` bound in the rational shape the segments use. -/
theorem sumK_le {c : ℝ} (hc : 1 ≤ c) {e0 : ℝ} (he0 : Real.exp (-(π * c)) ≤ e0) :
    (∑ k ∈ Finset.range 3, Real.exp (-π * ((k : ℝ) + 1) ^ 2 * c) * thetaTermK (77 / 5 : ℝ) k)
      ≤ 285.7 * e0 + 0.00315 := by
  have hE := exp_neg_pi_le
  have hEpos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  have h0 : Real.exp (-π * ((0 : ℝ) + 1) ^ 2 * c) = Real.exp (-(π * c)) := by
    congr 1; ring
  have h1 : Real.exp (-π * ((1 : ℝ) + 1) ^ 2 * c) ≤ 0.0000034875 := by
    have hle : -π * ((1 : ℝ) + 1) ^ 2 * c ≤ ((4 : ℕ) : ℝ) * (-π) := by
      push_cast; nlinarith
    refine le_trans (Real.exp_le_exp.mpr hle) ?_
    rw [Real.exp_nat_mul]
    calc Real.exp (-π) ^ (4 : ℕ) ≤ (0.04321392 : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ hEpos.le hE 4
      _ ≤ 0.0000034875 := by norm_num
  have h2 : Real.exp (-π * ((2 : ℝ) + 1) ^ 2 * c) ≤ 0.00000000000053 := by
    have hle : -π * ((2 : ℝ) + 1) ^ 2 * c ≤ ((9 : ℕ) : ℝ) * (-π) := by
      push_cast; nlinarith
    refine le_trans (Real.exp_le_exp.mpr hle) ?_
    rw [Real.exp_nat_mul]
    calc Real.exp (-π) ^ (9 : ℕ) ≤ (0.04321392 : ℝ) ^ (9 : ℕ) :=
          pow_le_pow_left₀ hEpos.le hE 9
      _ ≤ 0.00000000000053 := by norm_num
  have he0n : (0 : ℝ) ≤ e0 := le_trans (Real.exp_pos _).le he0
  have hK0 := K0_le
  have hK1 := K1_le
  have hK2 := K2_le
  have hk0 := K_nonneg 0
  have hk1 := K_nonneg 1
  have hk2 := K_nonneg 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  push_cast
  rw [h0]
  nlinarith [mul_le_mul he0 hK0 hk0 he0n,
    mul_le_mul h1 hK1 hk1 (by norm_num : (0:ℝ) ≤ 0.0000034875),
    mul_le_mul h2 hK2 hk2 (by norm_num : (0:ℝ) ≤ 0.00000000000053)]

/-! ## §3 -- the per-segment lower bound -/

theorem seg_lower (c d u0 h : ℝ) (n : ℕ) (e0 lo mb bnd : ℝ)
    (hn : 0 < n) (hc : 1 ≤ c) (hcd : c ≤ d)
    (hh : h = (d - c) / (n : ℕ)) (hu0 : u0 = c + h / 2)
    (he0 : Real.exp (-(π * c)) ≤ e0) (hmb : 285.7 * e0 + 0.00315 ≤ mb)
    (hlo : lo ≤ ∑ i ∈ Finset.range n, nodeR (u0 + h * (i : ℕ)))
    (hbnd : bnd ≤ h * lo - mb * (d - c) ^ 3 / (24 * (n : ℕ) ^ 2)) :
    bnd ≤ ∫ x in c..d, FT x := by
  have hnR : (0 : ℝ) < (n : ℕ) := by exact_mod_cast hn
  have hhpos : 0 ≤ h := by rw [hh]; exact div_nonneg (by linarith) hnR.le
  have hmem : ∀ x ∈ Set.uIcc c d, 1 ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hcd] at hx
    exact le_trans hc hx.1
  have hM : ∀ x ∈ Set.uIcc c d,
      |∑ k ∈ Finset.range 3, thetaTermD2 (77 / 5 : ℝ) k x| ≤ mb := by
    intro x hx
    refine le_trans (abs_thetaTermD2_sum_le_at (77 / 5 : ℝ) 3 hc ?_) ?_
    · rw [Set.uIcc_of_le hcd] at hx; exact hx.1
    · exact le_trans (sumK_le hc he0) hmb
  have hf : ∀ x ∈ Set.uIcc c d,
      HasDerivAt FT (∑ k ∈ Finset.range 3, thetaTermD1 (77 / 5 : ℝ) k x) x :=
    fun x hx ↦ FT_hasDerivAt (lt_of_lt_of_le one_pos (hmem x hx))
  have hf' : ∀ x ∈ Set.uIcc c d,
      HasDerivAt (fun y ↦ ∑ k ∈ Finset.range 3, thetaTermD1 (77 / 5 : ℝ) k y)
        (∑ k ∈ Finset.range 3, thetaTermD2 (77 / 5 : ℝ) k x) x :=
    fun x hx ↦ hasDerivAt_thetaTermD1_sum (77 / 5 : ℝ) 3
      (lt_of_lt_of_le one_pos (hmem x hx))
  have key := composite_midpoint_error hn hcd hf hf' hM
  have hnodes : (∑ i ∈ Finset.range n, FT (c + (d - c) / (n : ℕ) * ((i : ℕ) + 1 / 2)))
      = ∑ i ∈ Finset.range n, nodeR (u0 + h * (i : ℕ)) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have harg : c + (d - c) / (n : ℕ) * ((i : ℕ) + 1 / 2) = u0 + h * (i : ℕ) := by
      rw [hu0, hh]; ring
    have hpos : (0 : ℝ) < u0 + h * (i : ℕ) := by
      have hi : (0 : ℝ) ≤ h * (i : ℕ) := mul_nonneg hhpos (Nat.cast_nonneg i)
      have h2 : (1 : ℝ) ≤ u0 := by rw [hu0]; linarith
      linarith
    rw [harg]
    exact (nodeR_eq hpos).symm
  rw [hnodes, ← hh] at key
  have hS := abs_le.mp key
  have hmul : h * lo ≤ h * (∑ i ∈ Finset.range n, nodeR (u0 + h * (i : ℕ))) :=
    mul_le_mul_of_nonneg_left hlo hhpos
  linarith [hS.1, hS.2]

/-! ## §4 -- the assembled lower bound for `∫_1^5 FT` -/

theorem int_lower : (0.004215162 : ℝ) ≤ ∫ x in (1 : ℝ)..5, FT x := by
  have i01 := seg_lower 1 1.0625 1.00125 0.0025 25 0.04321392 (1.8531401634) 12.349367 (0.00463264939)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_01 (by norm_num) XiPanels.seg01 (by push_cast; norm_num)
  have i02 := seg_lower 1.0625 1.125 1.06375 0.0025 25 0.03550996 (1.1634895136) 10.148346 (0.00290855859)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_02 (by norm_num) XiPanels.seg02 (by push_cast; norm_num)
  have i03 := seg_lower 1.125 1.1875 1.12625 0.0025 25 0.02917942 (0.5262304967) 8.339711 (0.00131544049)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_03 (by norm_num) XiPanels.seg03 (by push_cast; norm_num)
  have i04 := seg_lower 1.1875 1.25 1.1890625 0.003125 20 0.02397746 (0.0418538013) 6.853511 (0.00013061882)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_04 (by norm_num) XiPanels.seg04 (by push_cast; norm_num)
  have i05 := seg_lower 1.25 1.375 1.2515625 0.003125 40 0.01970288 (-0.4921928491) 5.632263 (-0.00153838914)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_05 (by norm_num) XiPanels.seg05 (by push_cast; norm_num)
  have i06 := seg_lower 1.375 1.5 1.3765625 0.003125 40 0.01330401 (-0.6138658963) 3.804106 (-0.00191852443)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_06 (by norm_num) XiPanels.seg06 (by push_cast; norm_num)
  have i07 := seg_lower 1.5 1.625 1.501953125 0.00390625 32 0.0089833 (-0.3235692421) 2.569679 (-0.00126414659)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_07 (by norm_num) XiPanels.seg07 (by push_cast; norm_num)
  have i08 := seg_lower 1.625 1.75 1.6275 0.005 25 0.00606581 (-0.1087282646) 1.736152 (-0.0005438674)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_08 (by norm_num) XiPanels.seg08 (by push_cast; norm_num)
  have i09 := seg_lower 1.75 2 1.7525 0.005 50 0.00409583 (0.0078703585) 1.173329 (0.00003904622)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_09 (by norm_num) XiPanels.seg09 (by push_cast; norm_num)
  have i10 := seg_lower 2 2.25 2.003125 0.00625 40 0.00186745 (0.048806056) 0.536681 (0.00030481946)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_10 (by norm_num) XiPanels.seg10 (by push_cast; norm_num)
  have i11 := seg_lower 2.25 2.5 2.25390625 0.0078125 32 0.00085144 (0.0183664357) 0.246407 (0.0001433311)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_11 (by norm_num) XiPanels.seg11 (by push_cast; norm_num)
  have i12 := seg_lower 2.5 3 2.505 0.01 50 0.00038821 (0.002328187) 0.114062 (0.00002304423)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_12 (by norm_num) XiPanels.seg12 (by push_cast; norm_num)
  have i13 := seg_lower 3 4 3.01 0.02 50 0.0000807 (-0.0008306806) 0.026206 (-0.00001705039)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_13 (by norm_num) XiPanels.seg13 (by push_cast; norm_num)
  have i14 := seg_lower 4 5 4.025 0.05 20 0.00000349 (0.0000012855) 0.004148 (-3.6782E-7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_14 (by norm_num) XiPanels.seg14 (by push_cast; norm_num)
  have a01 : (∫ x in (1 : ℝ)..(1.0625 : ℝ), FT x) + (∫ x in (1.0625 : ℝ)..(1.125 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(1.125 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a02 : (∫ x in (1 : ℝ)..(1.125 : ℝ), FT x) + (∫ x in (1.125 : ℝ)..(1.1875 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(1.1875 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a03 : (∫ x in (1 : ℝ)..(1.1875 : ℝ), FT x) + (∫ x in (1.1875 : ℝ)..(1.25 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(1.25 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a04 : (∫ x in (1 : ℝ)..(1.25 : ℝ), FT x) + (∫ x in (1.25 : ℝ)..(1.375 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(1.375 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a05 : (∫ x in (1 : ℝ)..(1.375 : ℝ), FT x) + (∫ x in (1.375 : ℝ)..(1.5 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(1.5 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a06 : (∫ x in (1 : ℝ)..(1.5 : ℝ), FT x) + (∫ x in (1.5 : ℝ)..(1.625 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(1.625 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a07 : (∫ x in (1 : ℝ)..(1.625 : ℝ), FT x) + (∫ x in (1.625 : ℝ)..(1.75 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(1.75 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a08 : (∫ x in (1 : ℝ)..(1.75 : ℝ), FT x) + (∫ x in (1.75 : ℝ)..(2 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(2 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a09 : (∫ x in (1 : ℝ)..(2 : ℝ), FT x) + (∫ x in (2 : ℝ)..(2.25 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(2.25 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a10 : (∫ x in (1 : ℝ)..(2.25 : ℝ), FT x) + (∫ x in (2.25 : ℝ)..(2.5 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(2.5 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a11 : (∫ x in (1 : ℝ)..(2.5 : ℝ), FT x) + (∫ x in (2.5 : ℝ)..(3 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(3 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a12 : (∫ x in (1 : ℝ)..(3 : ℝ), FT x) + (∫ x in (3 : ℝ)..(4 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(4 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  have a13 : (∫ x in (1 : ℝ)..(4 : ℝ), FT x) + (∫ x in (4 : ℝ)..(5 : ℝ), FT x)
      = ∫ x in (1 : ℝ)..(5 : ℝ), FT x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_integrable (by norm_num) (by norm_num)) (FT_integrable (by norm_num) (by norm_num))
  linarith [i01, i02, i03, i04, i05, i06, i07, i08, i09, i10, i11, i12, i13, i14, a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13]

/-! ## §5 -- `0 < Xi (15.4)` -/

theorem Xi_154_pos : 0 < Xi (77 / 5 : ℝ) := by
  have hsplit := Xi_split_intervalIntegral (77 / 5 : ℝ) 5 (by norm_num)
  have htail := Xi_tail_bound (77 / 5 : ℝ) 5 (by norm_num)
  have htn := tail_le
  have hgint : IntervalIntegrable
      (fun u : ℝ ↦ 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((77 / 5 : ℝ) / 2 * Real.log u) * omega u)
      volume 1 5 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((integrableOn_Xi_theta_integrand (77 / 5 : ℝ)).mono_set Set.Ioc_subset_Ioi_self)
  have hFTint : IntervalIntegrable FT volume 1 5 := FT_integrable (by norm_num) (by norm_num)
  have hsub : (∫ u in (1 : ℝ)..5,
        2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((77 / 5 : ℝ) / 2 * Real.log u) * omega u)
      - (∫ x in (1 : ℝ)..5, FT x)
      = ∫ u in (1 : ℝ)..5,
        (2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((77 / 5 : ℝ) / 2 * Real.log u) * omega u - FT u) :=
    (intervalIntegral.integral_sub hgint hFTint).symm
  have hbd : ∀ u ∈ Set.uIoc (1 : ℝ) 5,
      ‖2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((77 / 5 : ℝ) / 2 * Real.log u) * omega u - FT u‖
        ≤ 0.00000000000000000001 := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 5)] at hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu.1
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
    have hFTu : FT u
        = 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((77 / 5 : ℝ) / 2 * Real.log u) * omegaPartial 3 u := by
      rw [← trunc_eq_FT]
    have hfac : 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((77 / 5 : ℝ) / 2 * Real.log u) * omega u - FT u
        = (2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((77 / 5 : ℝ) / 2 * Real.log u))
          * (omega u - omegaPartial 3 u) := by
      rw [hFTu]; ring
    have hrp : u ^ (-(3 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
    have hrp0 : (0 : ℝ) < u ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hu0 _
    have hA : |2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((77 / 5 : ℝ) / 2 * Real.log u)| ≤ 2 := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * u ^ (-(3 / 4) : ℝ))]
      nlinarith [Real.abs_cos_le_one ((77 / 5 : ℝ) / 2 * Real.log u),
        abs_nonneg (Real.cos ((77 / 5 : ℝ) / 2 * Real.log u))]
    have hom := omega_partial_error hu1 3
    have hE := exp_neg_pi_le
    have hEpos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
    have hpi0 : (0 : ℝ) < π := Real.pi_pos
    have he16 : Real.exp (-π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u) ≤ 0.000000000000000000001 := by
      have hle : -π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u ≤ ((16 : ℕ) : ℝ) * (-π) := by
        push_cast; nlinarith
      refine le_trans (Real.exp_le_exp.mpr hle) ?_
      rw [Real.exp_nat_mul]
      calc Real.exp (-π) ^ (16 : ℕ) ≤ (0.04321392 : ℝ) ^ (16 : ℕ) :=
            pow_le_pow_left₀ hEpos.le hE 16
        _ ≤ 0.000000000000000000001 := by norm_num
    have hden : (0.95 : ℝ) ≤ 1 - Real.exp (-π) := by linarith
    have hnum : (0 : ℝ) ≤ Real.exp (-π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u) := (Real.exp_pos _).le
    have hq : Real.exp (-π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u) / (1 - Real.exp (-π))
        ≤ 0.0000000000000000000011 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hd2 : |omega u - omegaPartial 3 u| ≤ 0.0000000000000000000011 := le_trans hom hq
    rw [Real.norm_eq_abs, hfac, abs_mul]
    nlinarith [abs_nonneg (omega u - omegaPartial 3 u),
      abs_nonneg (2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((77 / 5 : ℝ) / 2 * Real.log u))]
  have hnb := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [← hsub, Real.norm_eq_abs] at hnb
  have hnb2 := abs_le.mp hnb
  have hta := abs_le.mp htail
  have hil := int_lower
  have hcon : -(1 / (1 / 4 + ((77 : ℝ) / 5) ^ 2)) = -(100 / 23741) := by norm_num
  rw [hcon] at hsplit
  norm_num at hnb2 hsplit
  linarith [hnb2.1, hnb2.2, hta.1, hta.2, hil, htn]

/-! ## §6 -- `Xi 1 < 0` -/

theorem Xi_one_neg : Xi 1 < 0 := by
  have hsplit := Xi_split_intervalIntegral (1 : ℝ) 1 le_rfl
  have htail := Xi_tail_bound (1 : ℝ) 1 le_rfl
  have htn := tail1_le
  rw [intervalIntegral.integral_same, zero_add,
    show -(1 / (1 / 4 + (1 : ℝ) ^ 2)) = -(4 / 5) from by norm_num] at hsplit
  have hta := abs_le.mp htail
  linarith [hta.1, hta.2]

/-! ## §7 -- the atom -/

/-- **★★★★★ THE RH ON-LINE-ZERO ATOM ★★★★★** -/
theorem positiveOnLineZetaZeroOrdinatesNonempty :
    PositiveOnLineZetaZeroOrdinatesNonempty :=
  xi_sign_change_implies_on_line_zero
    ⟨1, 77 / 5, one_pos, by norm_num,
      mul_neg_of_neg_of_pos Xi_one_neg Xi_154_pos⟩

end PrincipiaTractalis.XiOnLineZero

-- Axiom check. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.XiOnLineZero.int_lower
#print axioms PrincipiaTractalis.XiOnLineZero.Xi_154_pos
#print axioms PrincipiaTractalis.XiOnLineZero.Xi_one_neg
#print axioms PrincipiaTractalis.XiOnLineZero.positiveOnLineZetaZeroOrdinatesNonempty
