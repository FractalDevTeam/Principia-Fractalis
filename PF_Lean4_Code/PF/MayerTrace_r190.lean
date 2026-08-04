/-
# PF.MayerTrace_r190

★★★ 2026-08-04 — COMPLEX-s WEIGHTS: THE FULL MAYER TRACE AS A KERNEL LIMIT ★★★

r189 proved the Gauss-system trace at s = 1 (rational weights).  This stone
lifts the weights to the **actual Mayer weights at arbitrary complex s**,

  w_j(z) = (z + j)^(−2s)   (principal branch),

and closes two statements:

1. **`mayer_trace`** — for every s : ℂ and every depth K, the trace of the
   truncated Mayer transfer matrix is

     Σ'_m A[m,m](s)  =  Σ_{j=1}^{K}  x_j^{2s} / (1 + x_j²),

   x_j = (√(j²+4) − j)/2 = [0; j,j,j,…].  The branch point of the principal
   power never matters: on the disc |z−1| ≤ 3/2 every z+j has Re ≥ 1/2, so
   the weight is holomorphic there (slit-plane condition, kernel-checked).
   The uniform weight bound W is produced by compactness of the circle —
   no cpow norm estimates enter the main theorem.

2. **`tendsto_mayer_trace`** — for Re s > 1/2 (Mayer's classical
   convergence threshold, *derived here*, not assumed folklore: the bound is
   ‖x_j^{2s}/(1+x_j²)‖ ≤ x_j^{2·Re s} ≤ (j+1)^{−2·Re s}, a p-series), the
   truncated traces converge as K → ∞, and

     `mayerTrace s := Σ'_j x_{j+1}^{2s}/(1 + x_{j+1}²)`

   is their limit.  This is the **full Mayer trace** — the trace of Mayer's
   operator L_s in the classical theory (Mayer 1991, Thm 7.17-type residue
   sums) — realized in the kernel as the limit of finitely-many-branch
   traces, each of which is itself a kernel theorem.

Sanity anchor (`mayer_trace_one_golden`): at s = 1, K = 1 the formula
reproduces r189's golden value (5 − √5)/10 through the cpow bridge.

Scope — what is NOT claimed: the infinite-branch OPERATOR (Mayer's L_s on
H²(D)) is not constructed; `mayerTrace` is defined as the limit of the
truncated traces, which is what the classical trace formula evaluates it to.
Nuclearity/Lidskii for the infinite system remains open (r188 record).
Selberg/RH connections: none claimed.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-04.
-/
import PF.GaussTrace_r189
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.PSeries

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.HilbertSchmidtL2

open Complex Metric Real Filter
open scoped Real Topology NNReal

noncomputable section

/-! ### The complex-s Mayer weight -/

/-- The Mayer weight at complex parameter `s`: `z ↦ (z + a)^(−2s)`,
principal branch. -/
def mayerWeight (s : ℂ) (a : ℝ) : ℂ → ℂ := fun z => (z + (a : ℂ)) ^ (-(2 * s))

/-- On the disc the denominator stays in the slit plane (`Re ≥ 1/2 > 0`),
so the principal power is holomorphic. -/
theorem differentiableAt_mayerWeight (s : ℂ) {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) (3 / 2)) :
    DifferentiableAt ℂ (mayerWeight s a) z := by
  apply DifferentiableAt.cpow_const (differentiableAt_id.add_const _)
  exact Or.inl (lt_of_lt_of_le (by norm_num) (denom_re ha hz))

/-! ### Fixed-point identities (extracted from the r189 inline proofs) -/

/-- The noble reciprocity: `x + a = 1/x` for the fixed point. -/
theorem gaussFix_add_eq_inv {a : ℝ} (ha : 1 ≤ a) :
    ((gaussFix a : ℝ) : ℂ) + (a : ℂ) = ((gaussFix a : ℝ) : ℂ)⁻¹ := by
  have hx0 : 0 < gaussFix a := gaussFix_pos (by linarith)
  have hxC : ((gaussFix a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx0
  have hid := gaussFix_identityC a
  field_simp
  linear_combination hid

/-- The branch derivative at the fixed point is `−x²`. -/
theorem deriv_gaussBranch_fix {a : ℝ} (ha : 1 ≤ a) :
    deriv (gaussBranch a) ((gaussFix a : ℝ) : ℂ)
      = -((gaussFix a : ℝ) : ℂ) ^ 2 := by
  have hx0 : 0 < gaussFix a := gaussFix_pos (by linarith)
  have hxC : ((gaussFix a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx0
  have hsum := gaussFix_add_eq_inv ha
  have hne : ((gaussFix a : ℝ) : ℂ) + (a : ℂ) ≠ 0 := by
    rw [hsum]
    exact inv_ne_zero hxC
  have h1 : HasDerivAt (fun z : ℂ => z + (a : ℂ)) 1 ((gaussFix a : ℝ) : ℂ) :=
    (hasDerivAt_id _).add_const _
  have hd : HasDerivAt (fun z : ℂ => (z + (a : ℂ))⁻¹)
      (-1 / (((gaussFix a : ℝ) : ℂ) + (a : ℂ)) ^ 2) ((gaussFix a : ℝ) : ℂ) :=
    h1.inv hne
  unfold gaussBranch
  rw [hd.deriv, hsum, inv_pow, div_inv_eq_mul, neg_one_mul]

/-- The Mayer weight at the fixed point: `w(x) = x^{2s}`
(via `x + a = 1/x` and the principal-branch inverse power on `(0,∞)`). -/
theorem mayerWeight_fix (s : ℂ) {a : ℝ} (ha : 1 ≤ a) :
    mayerWeight s a ((gaussFix a : ℝ) : ℂ)
      = ((gaussFix a : ℝ) : ℂ) ^ (2 * s) := by
  have hx0 : 0 < gaussFix a := gaussFix_pos (by linarith)
  have harg : Complex.arg ((gaussFix a : ℝ) : ℂ) ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hx0.le]
    exact Ne.symm Real.pi_ne_zero
  show (((gaussFix a : ℝ) : ℂ) + (a : ℂ)) ^ (-(2 * s)) = _
  rw [gaussFix_add_eq_inv ha, Complex.inv_cpow _ _ harg,
    Complex.cpow_neg, inv_inv]

/-! ### The uniform weight bound, by compactness -/

/-- Any family of functions continuous on the circle admits one uniform
bound — the interface `trace_eq_residues` needs, with no explicit
cpow estimates. -/
theorem exists_uniform_bound (K : ℕ) (w : Fin K → ℂ → ℂ)
    (hwc : ∀ k, ContinuousOn (w k) (Metric.sphere (1 : ℂ) (3 / 2))) :
    ∃ W : ℝ, 0 ≤ W ∧
      ∀ k, ∀ z ∈ Metric.sphere (1 : ℂ) (3 / 2), ‖w k z‖ ≤ W := by
  have h : ∀ k : Fin K, ∃ C : ℝ,
      ∀ z ∈ Metric.sphere (1 : ℂ) (3 / 2), ‖w k z‖ ≤ C := fun k =>
    (isCompact_sphere (1 : ℂ) (3 / 2)).exists_bound_of_continuousOn (hwc k)
  choose C hC using h
  refine ⟨(Finset.univ.sup fun k => (C k).toNNReal : ℝ≥0),
    NNReal.coe_nonneg _, fun k z hz => ?_⟩
  calc ‖w k z‖ ≤ C k := hC k z hz
    _ ≤ ((C k).toNNReal : ℝ) := Real.le_coe_toNNReal _
    _ ≤ _ := by
        exact_mod_cast NNReal.coe_le_coe.mpr
          (Finset.le_sup (f := fun j => (C j).toNNReal) (Finset.mem_univ k))

/-! ### THE MAYER TRACE AT COMPLEX s -/

/-- **The truncated Mayer trace at arbitrary complex `s`**:

`Σ'_m A[m,m](s) = Σ_{j=1}^{K} x_j^{2s} / (1 + x_j²)`. -/
theorem mayer_trace (s : ℂ) (K : ℕ) :
    (∑' m : ℕ, transferMatrix 1 (5 / 4) (3 / 2) K
        (fun k : Fin K => mayerWeight s (((k : ℕ) : ℝ) + 1))
        (fun k : Fin K => gaussBranch (((k : ℕ) : ℝ) + 1)) m m)
      = ∑ k : Fin K, ((gaussFix (((k : ℕ) : ℝ) + 1) : ℝ) : ℂ) ^ (2 * s)
          / (1 + ((gaussFix (((k : ℕ) : ℝ) + 1) : ℝ) : ℂ) ^ 2) := by
  have hak : ∀ k : Fin K, (1 : ℝ) ≤ ((k : ℕ) : ℝ) + 1 :=
    fun k => le_add_of_nonneg_left (by positivity)
  -- the weight family is continuous on the circle, hence uniformly bounded
  have hwc : ∀ k : Fin K, ContinuousOn (mayerWeight s (((k : ℕ) : ℝ) + 1))
      (Metric.sphere (1 : ℂ) (3 / 2)) := fun k z hz =>
    (differentiableAt_mayerWeight s (hak k)
      (Metric.sphere_subset_closedBall hz)).continuousAt.continuousWithinAt
  obtain ⟨W, hW0, hWb⟩ := exists_uniform_bound K _ hwc
  have main := trace_eq_residues (c := 1) (R := 5 / 4) (R₁ := 3 / 2)
    (τ := 1) (W := W) (K := K)
    (w := fun k : Fin K => mayerWeight s (((k : ℕ) : ℝ) + 1))
    (φ := fun k : Fin K => gaussBranch (((k : ℕ) : ℝ) + 1))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hW0
    (fun k z hz => hWb k z hz)
    (fun k z hz => gaussBranch_mem (hak k) hz)
    (x := fun k => (gaussFix (((k : ℕ) : ℝ) + 1) : ℂ))
    (fun k => gaussFix_mem_ball (hak k))
    (g := fun k => gaussCofactor (((k : ℕ) : ℝ) + 1))
    (fun k z hz => gauss_factor (hak k) hz)
    (fun k => diffContOnCl_of_closedBall fun z hz =>
      differentiableAt_mayerWeight s (hak k) hz)
    (fun k => diffContOnCl_of_closedBall fun z hz =>
      differentiableAt_denom_inv (hak k) hz)
    (fun k => diffContOnCl_of_closedBall fun z hz =>
      ((differentiableAt_id.add_const _).add_const _).mul
        (differentiableAt_denom_inv (hak k) hz))
    (fun k z hz => gaussCofactor_ne_zero (hak k) hz)
  rw [main]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  rw [mayerWeight_fix s (hak k), deriv_gaussBranch_fix (hak k),
    sub_neg_eq_add]

/-! ### Convergence: the full Mayer trace, Re s > 1/2 -/

/-- The `j`-th residue term of the full Mayer trace. -/
def mayerTerm (s : ℂ) (j : ℕ) : ℂ :=
  ((gaussFix ((j : ℝ) + 1) : ℝ) : ℂ) ^ (2 * s)
    / (1 + ((gaussFix ((j : ℝ) + 1) : ℝ) : ℂ) ^ 2)

/-- The fixed points decay like `1/a`: `x_a ≤ 1/a`. -/
theorem gaussFix_le_inv {a : ℝ} (ha : 1 ≤ a) : gaussFix a ≤ 1 / a := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hkey : a * (2 / a) = 2 := by field_simp
  have h1 : a ^ 2 + 4 ≤ (a + 2 / a) ^ 2 := by nlinarith [sq_nonneg (2 / a)]
  have h2 : Real.sqrt (a ^ 2 + 4) ≤ a + 2 / a := by
    calc Real.sqrt (a ^ 2 + 4) ≤ Real.sqrt ((a + 2 / a) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = a + 2 / a := Real.sqrt_sq (by positivity)
  have h4 : Real.sqrt (a ^ 2 + 4) - a ≤ 2 / a := by
    rw [le_div_iff₀ ha0]
    nlinarith [h2, hkey, ha0]
  have h5 : (2 : ℝ) / a = 2 * (1 / a) := by ring
  unfold gaussFix
  linarith

/-- The residue terms are dominated by the p-series `(j+1)^{−2·Re s}`. -/
theorem norm_mayerTerm_le {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) :
    ‖mayerTerm s j‖ ≤ ((((j : ℝ) + 1) ^ (2 * s.re))⁻¹ : ℝ) := by
  set a : ℝ := (j : ℝ) + 1 with hadef
  have ha : (1 : ℝ) ≤ a := le_add_of_nonneg_left (by positivity)
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hx0 : 0 < gaussFix a := gaussFix_pos (by linarith)
  have hre : (2 * s).re = 2 * s.re := by
    simp [Complex.mul_re]
  -- numerator norm: x^(2·Re s), an rpow of a positive real
  have hnum : ‖((gaussFix a : ℝ) : ℂ) ^ (2 * s)‖
      = gaussFix a ^ (2 * s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
  -- denominator norm: 1 + x² ≥ 1
  have hden_cast : (1 : ℂ) + ((gaussFix a : ℝ) : ℂ) ^ 2
      = (((1 + gaussFix a ^ 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  have hden : ‖(1 : ℂ) + ((gaussFix a : ℝ) : ℂ) ^ 2‖ = 1 + gaussFix a ^ 2 := by
    rw [hden_cast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  rw [mayerTerm, norm_div, hnum, hden]
  have hstep1 : gaussFix a ^ (2 * s.re) / (1 + gaussFix a ^ 2)
      ≤ gaussFix a ^ (2 * s.re) :=
    div_le_self (Real.rpow_nonneg hx0.le _) (by nlinarith [sq_nonneg (gaussFix a)])
  have hstep2 : gaussFix a ^ (2 * s.re) ≤ (1 / a) ^ (2 * s.re) :=
    Real.rpow_le_rpow hx0.le (gaussFix_le_inv ha) (by positivity)
  have hstep3 : (1 / a : ℝ) ^ (2 * s.re) = (a ^ (2 * s.re))⁻¹ := by
    rw [one_div, Real.inv_rpow ha0.le]
  calc gaussFix a ^ (2 * s.re) / (1 + gaussFix a ^ 2)
      ≤ gaussFix a ^ (2 * s.re) := hstep1
    _ ≤ (1 / a) ^ (2 * s.re) := hstep2
    _ = (a ^ (2 * s.re))⁻¹ := hstep3

/-- **Mayer's convergence threshold, derived**: the residue series converges
for `Re s > 1/2`. -/
theorem summable_mayerTerm {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (mayerTerm s) := by
  have hs0 : 0 ≤ s.re := by linarith
  apply Summable.of_norm_bounded ?_ (fun j => norm_mayerTerm_le hs0 j)
  have hbase : Summable (fun n : ℕ => (((n : ℝ)) ^ (2 * s.re))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  exact hshift.congr fun n => by push_cast; rfl

/-- **The full Mayer trace**: the sum over ALL branches of the fixed-point
residues, `Σ'_j x_{j+1}^{2s}/(1 + x_{j+1}²)`. -/
def mayerTrace (s : ℂ) : ℂ := ∑' j : ℕ, mayerTerm s j

/-- **The truncated kernel traces converge to the full Mayer trace** for
`Re s > 1/2`: the classical Mayer trace is the limit of kernel-checked
finite-branch traces. -/
theorem tendsto_mayer_trace {s : ℂ} (hs : 1 / 2 < s.re) :
    Filter.Tendsto (fun K : ℕ => ∑' m : ℕ, transferMatrix 1 (5 / 4) (3 / 2) K
        (fun k : Fin K => mayerWeight s (((k : ℕ) : ℝ) + 1))
        (fun k : Fin K => gaussBranch (((k : ℕ) : ℝ) + 1)) m m)
      Filter.atTop (𝓝 (mayerTrace s)) := by
  have h := (summable_mayerTerm hs).hasSum.tendsto_sum_nat
  refine h.congr fun K => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun i => mayerTerm s i) K, mayer_trace s K]
  exact Finset.sum_congr rfl fun i _ => rfl

/-! ### Sanity anchor: s = 1 reproduces the golden trace -/

/-- At `s = 1, K = 1` the complex-power formula reproduces r189's golden
value `(5 − √5)/10` — the cpow bridge is consistent with the rational case. -/
theorem mayer_trace_one_golden :
    (∑' m : ℕ, transferMatrix 1 (5 / 4) (3 / 2) 1
        (fun k : Fin 1 => mayerWeight 1 (((k : ℕ) : ℝ) + 1))
        (fun k : Fin 1 => gaussBranch (((k : ℕ) : ℝ) + 1)) m m)
      = (((5 - Real.sqrt 5) / 10 : ℝ) : ℂ) := by
  rw [mayer_trace 1 1, Fin.sum_univ_one]
  have hcast : (((0 : Fin 1) : ℕ) : ℝ) + 1 = 1 := by norm_num
  rw [hcast]
  have hfix : gaussFix 1 = (Real.sqrt 5 - 1) / 2 := by
    unfold gaussFix
    norm_num
  rw [hfix]
  -- bridge the cpow to the natural square
  have hbridge : (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ) ^ ((2 : ℂ) * 1)
      = (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ) ^ (2 : ℕ) := by
    rw [mul_one, show ((2 : ℂ)) = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
  rw [hbridge]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hreal : ((Real.sqrt 5 - 1) / 2) ^ 2 / (1 + ((Real.sqrt 5 - 1) / 2) ^ 2)
      = (5 - Real.sqrt 5) / 10 := by
    have hden : (0 : ℝ) < 1 + ((Real.sqrt 5 - 1) / 2) ^ 2 := by positivity
    rw [div_eq_div_iff hden.ne' (by norm_num : (10 : ℝ) ≠ 0)]
    linear_combination ((Real.sqrt 5 + 3) / 4) * h5
  exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hreal

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.mayer_trace
#print axioms PrincipiaTractalis.HilbertSchmidtL2.summable_mayerTerm
#print axioms PrincipiaTractalis.HilbertSchmidtL2.tendsto_mayer_trace
#print axioms PrincipiaTractalis.HilbertSchmidtL2.mayer_trace_one_golden
