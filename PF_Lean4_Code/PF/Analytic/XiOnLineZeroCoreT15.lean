/-
# PF.Analytic.XiOnLineZeroCoreT15

t = 15 mirror of `XiOnLineZeroCore.lean`.  Same construction, but the
truncated critical-line integrand is evaluated at `t = 15` (integer)
instead of `t = 77/5`, so `cos((t/2)·log u)` becomes `cos(7.5·log u)`.

Reused verbatim from the r120 stack (via the base `XiOnLineZeroCore`):
- `thetaTermK`, `abs_thetaTermD2_le_exp`, `abs_thetaTermD2_sum_le_at`.
  These are parametric in `t`, so no duplication is needed.

Duplicated with t = 15 substitution (kept isolated to keep the tested
r120 machinery untouched):
- `nodeR15`   — real node function (7.5·log u instead of 7.7·log u).
- `nodeI15`   — interval mirror.
- `nodeR15_mem_approx` — conservativity of the interval mirror.
- `thetaTerm_eq_exp_15` — `thetaTerm 15 k` in `exp`/`log`/`cos` form.
- `nodeR15_eq` — `nodeR15` IS the N = 3 truncated integrand at t = 15.
- `nodeFold15`, `nodeFold15_mem`, `nodeSum15_split` — panel-sum plumbing.

Zero project axioms, no `sorry`, no `native_decide`.
-/
import PF.Analytic.XiOnLineZeroCore

namespace PrincipiaTractalis.XiOnLineZeroCoreT15

open Set MeasureTheory Filter
open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real Topology

/-! ## §1 -- the critical-line node function at `t = 15` -/

/-- The truncated critical-line integrand at `t = 15`, in pure
    `exp`/`log`/`cos` form so the interval engine can mirror it. -/
noncomputable def nodeR15 (u : ℝ) : ℝ :=
  2 * Real.exp (Real.log u * (-0.75)) * Real.cos (7.5 * Real.log u)
    * (Real.exp (-(π * u)) + Real.exp (-(π * u)) ^ 4 + Real.exp (-(π * u)) ^ 9)

/-- Each `thetaTerm` at `t = 15` in `exp`/`log`/`cos` form. -/
theorem thetaTerm_eq_exp_15 (k : ℕ) {u : ℝ} (hu : 0 < u) :
    thetaTerm (15 : ℝ) k u
      = 2 * Real.exp (Real.log u * (-0.75)) * Real.cos (7.5 * Real.log u)
        * Real.exp (-(π * u)) ^ ((k + 1) ^ 2) := by
  have h1 : u ^ (-(3 / 4) : ℝ) = Real.exp (Real.log u * (-0.75)) := by
    rw [Real.rpow_def_of_pos hu]
    norm_num
  have h2 : (15 : ℝ) / 2 = 7.5 := by norm_num
  have h3 : Real.exp (-(π * u)) ^ ((k + 1) ^ 2)
      = Real.exp (-π * ((k : ℝ) + 1) ^ 2 * u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [thetaTerm]
  rw [h1, h2, h3]

/-- `nodeR15` IS the `N = 3` truncated integrand `∑_{n<3} thetaTerm 15 n u`. -/
theorem nodeR15_eq {u : ℝ} (hu : 0 < u) :
    nodeR15 u = ∑ n ∈ Finset.range 3, thetaTerm (15 : ℝ) n u := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, thetaTerm_eq_exp_15 0 hu, thetaTerm_eq_exp_15 1 hu,
    thetaTerm_eq_exp_15 2 hu]
  norm_num [nodeR15]
  ring

/-! ## §2 -- the interval mirror and the panel-sum fold -/

/-- Interval mirror of `nodeR15`.  The `let`-bindings are load-bearing
    (see the r120 core note): the kernel's `whnf` cache is pointer-keyed. -/
def nodeI15 (u : _root_.Interval) : _root_.Interval :=
  let L := _root_.Interval.log u
  let E := _root_.Interval.exp (-(_root_.Interval.pi * u))
  let E2 := E * E
  let E4 := E2 * E2
  2 * _root_.Interval.exp (L * (-0.75 : _root_.Interval))
    * _root_.Interval.cos ((7.5 : _root_.Interval) * L)
    * (E + E4 + E4 * E4 * E)

/-- Conservativity of the interval node. -/
theorem nodeR15_mem_approx {u : ℝ} {U : _root_.Interval} (hu : u ∈ approx U) :
    nodeR15 u ∈ approx (nodeI15 U) := by
  have h4 : Real.exp (-(π * u)) ^ 4
      = Real.exp (-(π * u)) * Real.exp (-(π * u))
        * (Real.exp (-(π * u)) * Real.exp (-(π * u))) := by ring
  have h9 : Real.exp (-(π * u)) ^ 9
      = Real.exp (-(π * u)) * Real.exp (-(π * u))
          * (Real.exp (-(π * u)) * Real.exp (-(π * u)))
          * (Real.exp (-(π * u)) * Real.exp (-(π * u))
            * (Real.exp (-(π * u)) * Real.exp (-(π * u))))
          * Real.exp (-(π * u)) := by ring
  show nodeR15 u ∈ approx
    (2 * _root_.Interval.exp (_root_.Interval.log U * (-0.75 : _root_.Interval))
      * _root_.Interval.cos ((7.5 : _root_.Interval) * _root_.Interval.log U)
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
  unfold nodeR15
  rw [h4, h9]
  approx

/-- Interval fold computing an enclosure of `∑_{i<n} nodeR15 (u + h·i)`. -/
def nodeFold15 : ℕ → _root_.Interval → _root_.Interval → _root_.Interval
  | 0,       _, _ => 0
  | (n + 1), U, H => nodeI15 U + nodeFold15 n (U + H) H

/-- The fold is conservative. -/
theorem nodeFold15_mem : ∀ (n : ℕ) (u h : ℝ) (U H : _root_.Interval),
    u ∈ approx U → h ∈ approx H →
    (∑ i ∈ Finset.range n, nodeR15 (u + h * (i : ℕ))) ∈ approx (nodeFold15 n U H) := by
  intro n
  induction n with
  | zero =>
      intro u h U H _ _
      simp only [Finset.sum_range_zero, nodeFold15]
      exact _root_.Interval.mem_approx_zero
  | succ m ih =>
      intro u h U H hU hH
      have hstep : (∑ i ∈ Finset.range (m + 1), nodeR15 (u + h * (i : ℕ)))
          = nodeR15 u + (∑ i ∈ Finset.range m, nodeR15 ((u + h) + h * (i : ℕ))) := by
        rw [Finset.sum_range_succ', add_comm]
        congr 1
        · norm_num
        · exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring_nf
      rw [hstep]
      have hUH : u + h ∈ approx (U + H) :=
        approx_add U H (Set.add_mem_add hU hH)
      show nodeR15 u + _ ∈ approx (nodeI15 U + nodeFold15 m (U + H) H)
      exact approx_add _ _ (Set.add_mem_add (nodeR15_mem_approx hU)
        (ih (u + h) h (U + H) H hUH hH))

/-- Splitting a `nodeR15` sum into two consecutive chunks (for
    parallel / memory-bounded kernel evaluation). -/
theorem nodeSum15_split (n1 n2 m : ℕ) (u h v : ℝ) (hm : m = n1 + n2)
    (hv : v = u + h * (n1 : ℕ)) :
    (∑ i ∈ Finset.range m, nodeR15 (u + h * (i : ℕ)))
      = (∑ i ∈ Finset.range n1, nodeR15 (u + h * (i : ℕ)))
        + ∑ i ∈ Finset.range n2, nodeR15 (v + h * (i : ℕ)) := by
  subst hm; subst hv
  rw [Finset.sum_range_add]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring_nf

end PrincipiaTractalis.XiOnLineZeroCoreT15
