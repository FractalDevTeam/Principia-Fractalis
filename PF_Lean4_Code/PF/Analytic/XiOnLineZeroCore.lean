/-
# PF.Analytic.XiOnLineZeroCore

Core layer for milestone B5 (r120): analytic glue between the B4
quadrature bricks (`PF.Analytic.XiQuadrature`) and the vendored
kernel-verified interval engine.  Zero project axioms, zero sorries,
no `native_decide`.
-/

import PF.Analytic.XiQuadrature
import Interval.Interval.Conversion
import Interval.Interval.Exp
import Interval.Interval.Log
import Interval.Interval.Sincos
import Interval.Interval.Pi
import Interval.Interval.Order
import Interval.Tactic.Approx

namespace PrincipiaTractalis.XiOnLineZeroCore

open Set MeasureTheory Filter
open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open scoped Real Topology

/-! ## §1 -- the `u`-dependent `C²` bound -/

/-- The `u`-independent part of the `thetaTerm` second-derivative bound. -/
noncomputable def thetaTermK (t : ℝ) (n : ℕ) : ℝ :=
  21 / 8 + 5 / 2 * |t| + |t| ^ 2 / 2 + 3 * (π * ((n : ℝ) + 1) ^ 2)
    + 2 * |t| * (π * ((n : ℝ) + 1) ^ 2) + 2 * (π * ((n : ℝ) + 1) ^ 2) ^ 2

private theorem abs_triple_le {x y z bx by' bz : ℝ}
    (hx : |x| ≤ bx) (hy : |y| ≤ by') (hz : |z| ≤ bz) :
    |x * y * z| ≤ bx * by' * bz := by
  have hbx : 0 ≤ bx := (abs_nonneg x).trans hx
  have hby : 0 ≤ by' := (abs_nonneg y).trans hy
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg y) hbx) hz (abs_nonneg z)
    (mul_nonneg hbx hby)

private theorem abs_sum6_le {x₁ x₂ x₃ x₄ x₅ x₆ b₁ b₂ b₃ b₄ b₅ b₆ : ℝ}
    (h₁ : |x₁| ≤ b₁) (h₂ : |x₂| ≤ b₂) (h₃ : |x₃| ≤ b₃)
    (h₄ : |x₄| ≤ b₄) (h₅ : |x₅| ≤ b₅) (h₆ : |x₆| ≤ b₆) :
    |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅ + 2 * x₆|
      ≤ b₁ + b₂ + b₃ + 2 * b₄ + 2 * b₅ + 2 * b₆ := by
  have k₄ : |2 * x₄| ≤ 2 * b₄ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₄]
  have k₅ : |2 * x₅| ≤ 2 * b₅ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₅]
  have k₆ : |2 * x₆| ≤ 2 * b₆ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₆]
  calc |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅ + 2 * x₆|
      ≤ |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅| + |2 * x₆| := abs_add _ _
    _ ≤ |x₁ + x₂ + x₃ + 2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂ + x₃ + 2 * x₄) (2 * x₅)]
    _ ≤ |x₁ + x₂ + x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂ + x₃) (2 * x₄)]
    _ ≤ |x₁ + x₂| + |x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂) x₃]
    _ ≤ |x₁| + |x₂| + |x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add x₁ x₂]
    _ ≤ b₁ + b₂ + b₃ + 2 * b₄ + 2 * b₅ + 2 * b₆ := by linarith

/-- SHARPENED B4d `C²` BOUND -- the exponential factor is kept. -/
theorem abs_thetaTermD2_le_exp (t : ℝ) (n : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |thetaTermD2 t n u| ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u) * thetaTermK t n := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hA : (0 : ℝ) < π * ((n : ℝ) + 1) ^ 2 := by positivity
  have hE : (0 : ℝ) < Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u) := Real.exp_pos _
  have hrpow_le_one : ∀ e : ℝ, e ≤ 0 → u ^ e ≤ 1 :=
    fun e he ↦ Real.rpow_le_one_of_one_le_of_nonpos hu he
  have hrpow_pos : ∀ e : ℝ, (0 : ℝ) < u ^ e := fun e ↦ Real.rpow_pos_of_pos hu0 e
  have hP0 : |2 * u ^ (-(3 / 4) : ℝ)| ≤ 2 := by
    rw [abs_of_pos (by positivity)]
    nlinarith [hrpow_le_one (-(3 / 4) : ℝ) (by norm_num)]
  have hP1 : |-3 / 2 * u ^ (-(7 / 4) : ℝ)| ≤ 3 / 2 := by
    rw [abs_mul, show |(-3 / 2 : ℝ)| = 3 / 2 from by norm_num, abs_of_pos (hrpow_pos _)]
    nlinarith [hrpow_le_one (-(7 / 4) : ℝ) (by norm_num), hrpow_pos (-(7 / 4) : ℝ)]
  have hP2 : |21 / 8 * u ^ (-(11 / 4) : ℝ)| ≤ 21 / 8 := by
    rw [abs_of_pos (by positivity)]
    nlinarith [hrpow_le_one (-(11 / 4) : ℝ) (by norm_num)]
  have hQ0 : |Real.cos (t / 2 * Real.log u)| ≤ 1 := Real.abs_cos_le_one _
  have hsin := Real.abs_sin_le_one (t / 2 * Real.log u)
  have hcos := Real.abs_cos_le_one (t / 2 * Real.log u)
  have habs_half : |t / 2| = |t| / 2 := by rw [abs_div, abs_two]
  have hQ1 : |-(t / 2) * Real.sin (t / 2 * Real.log u) / u| ≤ |t| / 2 := by
    rw [abs_div, abs_of_pos hu0]
    refine le_trans (div_le_self (abs_nonneg _) hu) ?_
    rw [abs_mul, abs_neg, habs_half]
    nlinarith [mul_nonneg (div_nonneg (abs_nonneg t) (by norm_num : (0:ℝ) ≤ 2))
      (sub_nonneg.mpr hsin)]
  have hQ2 : |(t / 2 * Real.sin (t / 2 * Real.log u)
      - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)) / u ^ 2|
      ≤ |t| / 2 + (|t| / 2) ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < u ^ 2)]
    have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith
    refine le_trans (div_le_self (abs_nonneg _) hu2) ?_
    rw [sub_eq_add_neg]
    refine le_trans (abs_add _ _) ?_
    rw [abs_neg, abs_mul, abs_mul, habs_half,
      show |(t / 2) ^ 2| = (|t| / 2) ^ 2 from by rw [abs_pow, habs_half]]
    nlinarith [mul_nonneg (div_nonneg (abs_nonneg t) (by norm_num : (0:ℝ) ≤ 2))
      (sub_nonneg.mpr hsin), mul_nonneg (sq_nonneg (|t| / 2)) (sub_nonneg.mpr hcos)]
  have hR0 : |Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
      ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u) := le_of_eq (abs_of_pos hE)
  have hR1 : |-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
      ≤ π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u) := by
    rw [abs_mul, show |-π * ((n : ℝ) + 1) ^ 2| = π * ((n : ℝ) + 1) ^ 2 from by
        rw [abs_of_neg (by nlinarith : -π * ((n : ℝ) + 1) ^ 2 < 0)]; ring,
      abs_of_pos hE]
  have hR2 : |(π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
      ≤ (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (π * ((n : ℝ) + 1) ^ 2) ^ 2),
      abs_of_pos hE]
  have hT1 := abs_triple_le hP2 hQ0 hR0
  have hT2 := abs_triple_le hP0 hQ2 hR0
  have hT3 := abs_triple_le hP0 hQ0 hR2
  have hT4 := abs_triple_le hP1 hQ1 hR0
  have hT5 := abs_triple_le hP1 hQ0 hR1
  have hT6 := abs_triple_le hP0 hQ1 hR1
  unfold thetaTermD2 thetaTermK
  refine le_trans (abs_sum6_le hT1 hT2 hT3 hT4 hT5 hT6) (le_of_eq ?_)
  ring

/-- Panel-local `C²` bound for the truncated integrand on `[c, ∞)`, `c ≥ 1`. -/
theorem abs_thetaTermD2_sum_le_at (t : ℝ) (N : ℕ) {c u : ℝ} (hc : 1 ≤ c) (hu : c ≤ u) :
    |∑ n ∈ Finset.range N, thetaTermD2 t n u|
      ≤ ∑ n ∈ Finset.range N, Real.exp (-π * ((n : ℝ) + 1) ^ 2 * c) * thetaTermK t n := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
  refine (abs_thetaTermD2_le_exp t n (hc.trans hu)).trans ?_
  have hA : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
  have hK : (0 : ℝ) ≤ thetaTermK t n := by
    unfold thetaTermK
    have h1 : (0:ℝ) ≤ |t| := abs_nonneg t
    positivity
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hK
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) hA]

/-! ## §2 -- the critical-line node function at `t = 77/5 = 15.4` -/

/-- The truncated critical-line integrand at `t = 15.4`, in pure
    `exp`/`log`/`cos` form so the interval engine can mirror it. -/
noncomputable def nodeR (u : ℝ) : ℝ :=
  2 * Real.exp (Real.log u * (-0.75)) * Real.cos (7.7 * Real.log u)
    * (Real.exp (-(π * u)) + Real.exp (-(π * u)) ^ 4 + Real.exp (-(π * u)) ^ 9)

/-- Each `thetaTerm` at `t = 77/5` in `exp`/`log`/`cos` form. -/
theorem thetaTerm_eq_exp (k : ℕ) {u : ℝ} (hu : 0 < u) :
    thetaTerm (77 / 5 : ℝ) k u
      = 2 * Real.exp (Real.log u * (-0.75)) * Real.cos (7.7 * Real.log u)
        * Real.exp (-(π * u)) ^ ((k + 1) ^ 2) := by
  have h1 : u ^ (-(3 / 4) : ℝ) = Real.exp (Real.log u * (-0.75)) := by
    rw [Real.rpow_def_of_pos hu]
    norm_num
  have h2 : ((77 : ℝ) / 5) / 2 = 7.7 := by norm_num
  have h3 : Real.exp (-(π * u)) ^ ((k + 1) ^ 2)
      = Real.exp (-π * ((k : ℝ) + 1) ^ 2 * u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [thetaTerm]
  rw [h1, h2, h3]

/-- `nodeR` IS the `N = 3` truncated integrand `∑_{n<3} thetaTerm (77/5) n u`. -/
theorem nodeR_eq {u : ℝ} (hu : 0 < u) :
    nodeR u = ∑ n ∈ Finset.range 3, thetaTerm (77 / 5 : ℝ) n u := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, thetaTerm_eq_exp 0 hu, thetaTerm_eq_exp 1 hu,
    thetaTerm_eq_exp 2 hu]
  norm_num [nodeR]
  ring

/-! ## §3 -- the interval mirror and the panel-sum fold -/

/-- Interval mirror of `nodeR`.  The `let`-bindings are LOAD-BEARING:
    the kernel's `whnf` cache is pointer-keyed, so structurally
    duplicated `exp` subterms would be recomputed (12 transcendental
    evaluations per node instead of 4). -/
def nodeI (u : _root_.Interval) : _root_.Interval :=
  let L := _root_.Interval.log u
  let E := _root_.Interval.exp (-(_root_.Interval.pi * u))
  let E2 := E * E
  let E4 := E2 * E2
  2 * _root_.Interval.exp (L * (-0.75 : _root_.Interval))
    * _root_.Interval.cos ((7.7 : _root_.Interval) * L)
    * (E + E4 + E4 * E4 * E)

/-- Conservativity of the interval node. -/
theorem nodeR_mem_approx {u : ℝ} {U : _root_.Interval} (hu : u ∈ approx U) :
    nodeR u ∈ approx (nodeI U) := by
  have h4 : Real.exp (-(π * u)) ^ 4
      = Real.exp (-(π * u)) * Real.exp (-(π * u))
        * (Real.exp (-(π * u)) * Real.exp (-(π * u))) := by ring
  have h9 : Real.exp (-(π * u)) ^ 9
      = Real.exp (-(π * u)) * Real.exp (-(π * u))
          * (Real.exp (-(π * u)) * Real.exp (-(π * u)))
          * (Real.exp (-(π * u)) * Real.exp (-(π * u))
            * (Real.exp (-(π * u)) * Real.exp (-(π * u))))
          * Real.exp (-(π * u)) := by ring
  show nodeR u ∈ approx
    (2 * _root_.Interval.exp (_root_.Interval.log U * (-0.75 : _root_.Interval))
      * _root_.Interval.cos ((7.7 : _root_.Interval) * _root_.Interval.log U)
      * (_root_.Interval.exp (-(_root_.Interval.pi * U))
          + _root_.Interval.exp (-(_root_.Interval.pi * U))
              * _root_.Interval.exp (-(_root_.Interval.pi * U))
              * (_root_.Interval.exp (-(_root_.Interval.pi * U))
                * _root_.Interval.exp (-(_root_.Interval.pi * U)))
          + _root_.Interval.exp (-(_root_.Interval.pi * U))
              * _root_.Interval.exp (-(_root_.Interval.pi * U))
              * (_root_.Interval.exp (-(_root_.Interval.pi * U))
                * _root_.Interval.exp (-(_root_.Interval.pi * U)))
              * (_root_.Interval.exp (-(_root_.Interval.pi * U))
                * _root_.Interval.exp (-(_root_.Interval.pi * U))
                * (_root_.Interval.exp (-(_root_.Interval.pi * U))
                  * _root_.Interval.exp (-(_root_.Interval.pi * U))))
              * _root_.Interval.exp (-(_root_.Interval.pi * U))))
  unfold nodeR
  rw [h4, h9]
  approx

/-- Interval fold computing an enclosure of `∑_{i<n} nodeR (u + h·i)`. -/
def nodeFold : ℕ → _root_.Interval → _root_.Interval → _root_.Interval
  | 0,       _, _ => 0
  | (n + 1), U, H => nodeI U + nodeFold n (U + H) H

/-- The fold is conservative. -/
theorem nodeFold_mem : ∀ (n : ℕ) (u h : ℝ) (U H : _root_.Interval),
    u ∈ approx U → h ∈ approx H →
    (∑ i ∈ Finset.range n, nodeR (u + h * (i : ℕ))) ∈ approx (nodeFold n U H) := by
  intro n
  induction n with
  | zero =>
      intro u h U H _ _
      simp only [Finset.sum_range_zero, nodeFold]
      exact _root_.Interval.mem_approx_zero
  | succ m ih =>
      intro u h U H hU hH
      have hstep : (∑ i ∈ Finset.range (m + 1), nodeR (u + h * (i : ℕ)))
          = nodeR u + (∑ i ∈ Finset.range m, nodeR ((u + h) + h * (i : ℕ))) := by
        rw [Finset.sum_range_succ', add_comm]
        congr 1
        · norm_num
        · exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring_nf
      rw [hstep]
      have hUH : u + h ∈ approx (U + H) :=
        approx_add U H (Set.add_mem_add hU hH)
      show nodeR u + _ ∈ approx (nodeI U + nodeFold m (U + H) H)
      exact approx_add _ _ (Set.add_mem_add (nodeR_mem_approx hU)
        (ih (u + h) h (U + H) H hUH hH))

/-- Splitting a node sum into two consecutive chunks (for parallel /
    memory-bounded kernel evaluation). -/
theorem nodeSum_split (n1 n2 m : ℕ) (u h v : ℝ) (hm : m = n1 + n2)
    (hv : v = u + h * (n1 : ℕ)) :
    (∑ i ∈ Finset.range m, nodeR (u + h * (i : ℕ)))
      = (∑ i ∈ Finset.range n1, nodeR (u + h * (i : ℕ)))
        + ∑ i ∈ Finset.range n2, nodeR (v + h * (i : ℕ)) := by
  subst hm; subst hv
  rw [Finset.sum_range_add]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring_nf

end PrincipiaTractalis.XiOnLineZeroCore
