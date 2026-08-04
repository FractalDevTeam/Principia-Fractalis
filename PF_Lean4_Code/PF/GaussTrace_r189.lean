/-
# PF.GaussTrace_r189

★★★ 2026-08-03 — THE TRACE FORMULA MEETS THE GAUSS MAP ★★★

r188 proved the holomorphic Lefschetz trace formula for abstract contracting
systems.  This stone instantiates it on the **actual Mayer branch data**: the
inverse branches of the Gauss continued-fraction map,

  φ_j(z) = 1/(z + j),   j = 1, …, K,

with the s = 1 Mayer weights w_j(z) = 1/(z+j)² — the Gauss–Kuzmin–Wirsing
operator, the object of RH_M1/RH_MOBIUS3 — on Mayer's disc |z − 1| ≤ 3/2.

**The geometry, verified in the kernel:** every branch maps the circle
|z−1| = 3/2 into the closed ball |w−1| ≤ 1 (the inversion estimate
‖z+j−1‖ ≤ ‖z+j‖ from Re z ≥ −1/2), so the r186/r188 hypotheses hold with
τ = 1 < R = 5/4 < R₁ = 3/2, W = 4.

**The fixed points are the noble continued fractions:**
x_j = [0; j, j, j, …] = (√(j²+4) − j)/2, the positive root of x² + jx = 1.
The simple-zero factorization is exact rational algebra:
z − 1/(z+j) = (z − x_j)·(z + j + x_j)/(z + j).

**The result** (`gauss_trace`): for every truncation depth K,

  Σ'_m A[m,m]  =  Σ_{j=1}^{K}  x_j² / (1 + x_j²) ,

since w_j(x_j) = x_j² and φ_j'(x_j) = −x_j² (because x_j + j = 1/x_j).

**The golden special case** (`gauss_trace_one`): K = 1 gives x₁ = 1/φ
(the golden ratio conjugate) and

  trace  =  (5 − √5)/10 .

Scope: this is the trace of the K-branch TRUNCATED Gauss system — the finite
Möbius systems of RH_MOBIUS3_2026-08-02.md, at s = 1 where the weights are
rational (no complex powers, no branch cuts).  The full Mayer operator has
infinitely many branches and complex weight exponent 2s; neither
infinite-branch traces nor complex powers are formalized here.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-03.
-/
import PF.TransferResidue_r188c

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.HilbertSchmidtL2

open Complex Metric Real
open scoped Real

noncomputable section

/-! ### The Gauss system -/

/-- The `a`-th inverse branch of the Gauss map: `z ↦ 1/(z + a)`. -/
def gaussBranch (a : ℝ) : ℂ → ℂ := fun z => (z + (a : ℂ))⁻¹

/-- The Mayer weight at `s = 1` (Gauss–Kuzmin–Wirsing): `z ↦ 1/(z + a)²`. -/
def gaussWeight (a : ℝ) : ℂ → ℂ := fun z => ((z + (a : ℂ))⁻¹) ^ 2

/-- The fixed point of `gaussBranch a`: the positive root of `x² + a·x = 1`,
i.e. the continued fraction `[0; a, a, a, …]`. -/
def gaussFix (a : ℝ) : ℝ := (Real.sqrt (a ^ 2 + 4) - a) / 2

/-- The holomorphic cofactor of the simple zero of `z − 1/(z+a)` at the
fixed point: `(z + a + x)/(z + a)`. -/
def gaussCofactor (a : ℝ) : ℂ → ℂ :=
  fun z => (z + (a : ℂ) + (gaussFix a : ℂ)) * (z + (a : ℂ))⁻¹

/-! ### The fixed point -/

theorem gaussFix_pos {a : ℝ} (ha : 0 ≤ a) : 0 < gaussFix a := by
  have h : a < Real.sqrt (a ^ 2 + 4) := by
    rw [Real.lt_sqrt ha]
    linarith
  unfold gaussFix
  linarith

theorem gaussFix_lt_one {a : ℝ} (ha : 1 ≤ a) : gaussFix a < 1 := by
  have h : Real.sqrt (a ^ 2 + 4) < a + 2 := by
    rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < a + 2)]
    nlinarith
  unfold gaussFix
  linarith

/-- The defining identity: `x² + a·x = 1`. -/
theorem gaussFix_identity (a : ℝ) : gaussFix a ^ 2 + a * gaussFix a = 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 + 4 by positivity)
  unfold gaussFix
  linear_combination (1 / 4 : ℝ) * h

theorem gaussFix_identityC (a : ℝ) :
    (gaussFix a : ℂ) ^ 2 + (a : ℂ) * (gaussFix a : ℂ) = 1 := by
  exact_mod_cast gaussFix_identity a

theorem gaussFix_mem_ball {a : ℝ} (ha : 1 ≤ a) :
    ((gaussFix a : ℝ) : ℂ) ∈ Metric.ball (1 : ℂ) (3 / 2) := by
  rw [Metric.mem_ball, dist_eq_norm]
  have h0 := gaussFix_pos (show (0 : ℝ) ≤ a by linarith)
  have h1 := gaussFix_lt_one ha
  have hcast : ((gaussFix a : ℝ) : ℂ) - 1 = ((gaussFix a - 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  linarith

/-! ### The disc geometry -/

theorem re_ge_of_mem {z : ℂ} (hz : z ∈ Metric.closedBall (1 : ℂ) (3 / 2)) :
    -(1 / 2 : ℝ) ≤ z.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 : |(z - 1).re| ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
  have h2 : (z - 1).re = z.re - 1 := by simp
  rw [h2] at h1
  have h3 := abs_le.mp (h1.trans hz)
  linarith [h3.1]

theorem denom_re {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) (3 / 2)) :
    (1 / 2 : ℝ) ≤ (z + (a : ℂ)).re := by
  have := re_ge_of_mem hz
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

theorem denom_ne_zero {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) (3 / 2)) :
    z + (a : ℂ) ≠ 0 := by
  have h2 := denom_re ha hz
  intro h0
  rw [h0, Complex.zero_re] at h2
  linarith

theorem denom_norm_ge {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) (3 / 2)) :
    (1 / 2 : ℝ) ≤ ‖z + (a : ℂ)‖ :=
  (denom_re ha hz).trans (Complex.re_le_norm _)

/-- **The inversion contraction**: every branch maps the circle
`|z−1| = 3/2` into the closed ball `|w−1| ≤ 1`. -/
theorem gaussBranch_mem {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.sphere (1 : ℂ) (3 / 2)) :
    gaussBranch a z ∈ Metric.closedBall (1 : ℂ) 1 := by
  have hz' : z ∈ Metric.closedBall (1 : ℂ) (3 / 2) :=
    Metric.sphere_subset_closedBall hz
  have hne := denom_ne_zero ha hz'
  have hre := re_ge_of_mem hz'
  -- the key estimate: ‖z + a − 1‖ ≤ ‖z + a‖ since Re(z) ≥ −1/2, a ≥ 1
  have hkey : ‖z + (a : ℂ) - 1‖ ≤ ‖z + (a : ℂ)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    rw [Complex.normSq_apply, Complex.normSq_apply]
    have h1 : (z + (a : ℂ) - 1).re = z.re + a - 1 := by simp
    have h2 : (z + (a : ℂ) - 1).im = z.im := by simp
    have h3 : (z + (a : ℂ)).re = z.re + a := by simp
    have h4 : (z + (a : ℂ)).im = z.im := by simp
    rw [h1, h2, h3, h4]
    nlinarith [hre, ha]
  rw [Metric.mem_closedBall, dist_eq_norm, gaussBranch]
  have hrw : (z + (a : ℂ))⁻¹ - 1 = -((z + (a : ℂ) - 1) * (z + (a : ℂ))⁻¹) := by
    have h : (z + (a : ℂ) - 1) * (z + (a : ℂ))⁻¹ = 1 - (z + (a : ℂ))⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hne, one_mul]
    rw [h]
    ring
  rw [hrw, norm_neg, norm_mul, norm_inv]
  have hden : (0 : ℝ) < ‖z + (a : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num) (denom_norm_ge ha hz')
  calc ‖z + (a : ℂ) - 1‖ * ‖z + (a : ℂ)‖⁻¹
      ≤ ‖z + (a : ℂ)‖ * ‖z + (a : ℂ)‖⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hden)

theorem gaussWeight_norm_le {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.sphere (1 : ℂ) (3 / 2)) :
    ‖gaussWeight a z‖ ≤ 4 := by
  have hz' := Metric.sphere_subset_closedBall hz
  have hd := denom_norm_ge ha hz'
  rw [gaussWeight, norm_pow, norm_inv]
  have h2 : ‖z + (a : ℂ)‖⁻¹ ≤ 2 := by
    rw [← one_div]
    calc 1 / ‖z + (a : ℂ)‖ ≤ 1 / (1 / 2 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num) hd
      _ = 2 := by norm_num
  calc ‖z + (a : ℂ)‖⁻¹ ^ 2 ≤ 2 ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
    _ = 4 := by norm_num

/-! ### The factorization -/

/-- The simple-zero factorization, exact rational algebra:
`z − 1/(z+a) = (z − x)·(z + a + x)/(z + a)`. -/
theorem gauss_factor {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) (3 / 2)) :
    z - gaussBranch a z = (z - (gaussFix a : ℂ)) * gaussCofactor a z := by
  have hne := denom_ne_zero ha hz
  have hid := gaussFix_identityC a
  rw [gaussBranch, gaussCofactor]
  field_simp
  linear_combination hid

theorem gaussCofactor_ne_zero {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) (3 / 2)) :
    gaussCofactor a z ≠ 0 := by
  have hne := denom_ne_zero ha hz
  apply mul_ne_zero _ (inv_ne_zero hne)
  intro h0
  have hre := denom_re ha hz
  have hx := gaussFix_pos (show (0 : ℝ) ≤ a by linarith)
  have hsum : (z + (a : ℂ) + (gaussFix a : ℂ)).re
      = (z + (a : ℂ)).re + gaussFix a := by simp
  rw [h0, Complex.zero_re] at hsum
  linarith [hsum.symm.le]

/-! ### Holomorphy -/

theorem differentiableAt_denom_inv {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) (3 / 2)) :
    DifferentiableAt ℂ (fun z : ℂ => (z + (a : ℂ))⁻¹) z :=
  (differentiableAt_id.add_const _).inv (denom_ne_zero ha hz)

theorem diffContOnCl_of_closedBall {f : ℂ → ℂ}
    (h : ∀ z ∈ Metric.closedBall (1 : ℂ) (3 / 2), DifferentiableAt ℂ f z) :
    DiffContOnCl ℂ f (Metric.ball (1 : ℂ) (3 / 2)) := by
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball (1 : ℂ) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  exact fun z hz => (h z hz).differentiableWithinAt

/-! ### THE GAUSS TRACE -/

/-- **The trace of the depth-`K` Gauss/GKW transfer matrix**:

`Σ'_m A[m,m] = Σ_{j=1}^{K} x_j²/(1 + x_j²)`,

`x_j = (√(j²+4) − j)/2 = [0; j, j, j, …]` the noble fixed points. -/
theorem gauss_trace (K : ℕ) :
    (∑' m : ℕ, transferMatrix 1 (5 / 4) (3 / 2) K
        (fun k : Fin K => gaussWeight (((k : ℕ) : ℝ) + 1))
        (fun k : Fin K => gaussBranch (((k : ℕ) : ℝ) + 1)) m m)
      = ∑ k : Fin K, (gaussFix (((k : ℕ) : ℝ) + 1) : ℂ) ^ 2
          / (1 + (gaussFix (((k : ℕ) : ℝ) + 1) : ℂ) ^ 2) := by
  have hak : ∀ k : Fin K, (1 : ℝ) ≤ ((k : ℕ) : ℝ) + 1 :=
    fun k => le_add_of_nonneg_left (by positivity)
  have main := trace_eq_residues (c := 1) (R := 5 / 4) (R₁ := 3 / 2)
    (τ := 1) (W := 4) (K := K)
    (w := fun k : Fin K => gaussWeight (((k : ℕ) : ℝ) + 1))
    (φ := fun k : Fin K => gaussBranch (((k : ℕ) : ℝ) + 1))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun k z hz => gaussWeight_norm_le (hak k) hz)
    (fun k z hz => gaussBranch_mem (hak k) hz)
    (x := fun k => (gaussFix (((k : ℕ) : ℝ) + 1) : ℂ))
    (fun k => gaussFix_mem_ball (hak k))
    (g := fun k => gaussCofactor (((k : ℕ) : ℝ) + 1))
    (fun k z hz => gauss_factor (hak k) hz)
    (fun k => diffContOnCl_of_closedBall fun z hz =>
      (differentiableAt_denom_inv (hak k) hz).pow 2)
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
  set a : ℝ := ((k : ℕ) : ℝ) + 1 with hadef
  have ha : (1 : ℝ) ≤ a := hak k
  have hx0 : 0 < gaussFix a := gaussFix_pos (by linarith)
  have hxC : ((gaussFix a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hx0
  have hid := gaussFix_identityC a
  -- x + a = 1/x, the defining reciprocity of the noble numbers
  have hsum : ((gaussFix a : ℝ) : ℂ) + (a : ℂ) = ((gaussFix a : ℝ) : ℂ)⁻¹ := by
    field_simp
    linear_combination hid
  have hderiv : deriv (gaussBranch a) ((gaussFix a : ℝ) : ℂ)
      = -((gaussFix a : ℝ) : ℂ) ^ 2 := by
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
  have hweight : gaussWeight a ((gaussFix a : ℝ) : ℂ)
      = ((gaussFix a : ℝ) : ℂ) ^ 2 := by
    rw [gaussWeight, hsum, inv_inv]
  rw [hweight, hderiv, sub_neg_eq_add]

/-- **The golden trace**: at depth `K = 1` the only fixed point is
`1/φ = (√5−1)/2`, and the trace of the Gauss–Kuzmin–Wirsing matrix is

`(5 − √5)/10 = 0.27639320225…` -/
theorem gauss_trace_one :
    (∑' m : ℕ, transferMatrix 1 (5 / 4) (3 / 2) 1
        (fun k : Fin 1 => gaussWeight (((k : ℕ) : ℝ) + 1))
        (fun k : Fin 1 => gaussBranch (((k : ℕ) : ℝ) + 1)) m m)
      = (((5 - Real.sqrt 5) / 10 : ℝ) : ℂ) := by
  rw [gauss_trace 1, Fin.sum_univ_one]
  have hcast : (((0 : Fin 1) : ℕ) : ℝ) + 1 = 1 := by norm_num
  rw [hcast]
  have hfix : gaussFix 1 = (Real.sqrt 5 - 1) / 2 := by
    unfold gaussFix
    norm_num
  rw [hfix]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hreal : ((Real.sqrt 5 - 1) / 2) ^ 2 / (1 + ((Real.sqrt 5 - 1) / 2) ^ 2)
      = (5 - Real.sqrt 5) / 10 := by
    have hden : (0 : ℝ) < 1 + ((Real.sqrt 5 - 1) / 2) ^ 2 := by positivity
    rw [div_eq_div_iff hden.ne' (by norm_num : (10 : ℝ) ≠ 0)]
    linear_combination ((Real.sqrt 5 + 3) / 4) * h5
  exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hreal

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.gaussBranch_mem
#print axioms PrincipiaTractalis.HilbertSchmidtL2.gauss_factor
#print axioms PrincipiaTractalis.HilbertSchmidtL2.gauss_trace
#print axioms PrincipiaTractalis.HilbertSchmidtL2.gauss_trace_one
