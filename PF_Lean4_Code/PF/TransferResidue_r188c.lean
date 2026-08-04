/-
# PF.TransferResidue_r188c

★★★ 2026-08-03 — THE LEFSCHETZ TRACE FORMULA, CLOSED ★★★

r188/r188b proved, from contraction geometry alone,

  Σ'_m A[m,m]  =  (2πi)⁻¹ ∮_{|z−c|=R₁}  Σ_k w_k(z)/(z − φ_k(z)) dz.

This stone evaluates the contour.  Under holomorphy inside the disc and the
standard simple-zero factorization `z − φ_k(z) = (z − x_k)·g_k(z)` with `g_k`
holomorphic and nonvanishing (the analytic statement that `x_k` is the unique
fixed point of the strictly contracting branch `φ_k`, and that it is simple),
the Cauchy integral formula gives the **holomorphic Lefschetz fixed-point
formula** for the transfer operator:

  trace(𝓛)  =  Σ_k  w_k(x_k) / (1 − φ_k'(x_k)).

This is the identity that ch24's trace–rank mechanism and the Mayer/Ruelle
program both live on: the trace of a weighted composition (transfer) operator
is a finite sum of fixed-point residues.  The factorization hypothesis is the
honest interface: it is exactly what "x_k is a simple zero of z − φ_k(z)" means,
and for the PF branches (Gauss-map inverse branches, elliptic-curve dynamical
weights) it is checkable by explicit division of holomorphic functions.

Contents:
* `fixedPoint_of_factor`   — the factorization forces `φ x = x`;
* `contour_eq_residue_single` — one branch: `(2πi)⁻¹ ∮ w/(z−φ) = w(x)/g(x)`
  (Cauchy formula applied to `w·g⁻¹`);
* `cofactor_eq_one_sub_deriv` — `g(x) = 1 − φ'(x)` (differentiate the
  factorization at the fixed point);
* `trace_eq_residues` — **the trace formula**: chained with r188b,
  `Σ'_m A[m,m] = Σ_k w_k(x_k)/(1 − φ_k'(x_k))`.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-03.
-/
import PF.TransferTrace_r188
import Mathlib.Analysis.Complex.CauchyIntegral

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.HilbertSchmidtL2

open Complex Metric Real
open scoped Real

noncomputable section

variable {c : ℂ} {R R₁ τ W : ℝ} {K : ℕ}

/-! ### The factorization interface -/

/-- The factorization `z − φ z = (z − x)·g z` forces `x` to be a fixed point
of `φ`. -/
theorem fixedPoint_of_factor {x : ℂ} {φ g : ℂ → ℂ}
    (hx : x ∈ Metric.ball c R₁)
    (hfactor : ∀ z ∈ Metric.closedBall c R₁, z - φ z = (z - x) * g z) :
    φ x = x := by
  have h := hfactor x (Metric.ball_subset_closedBall hx)
  rw [sub_self, zero_mul, sub_eq_zero] at h
  exact h.symm

/-! ### One branch: the residue at the fixed point -/

/-- **Single-branch residue evaluation**: if `w` and the cofactor `g` are
holomorphic on the disc and continuous up to the boundary, `g` nonvanishing,
then the contour of `w/(z−φ)` picks up exactly the residue `w(x)/g(x)` at the
(unique, simple) zero `x` of `z − φ z`. -/
theorem contour_eq_residue_single (hR₁ : 0 < R₁) {x : ℂ}
    (hx : x ∈ Metric.ball c R₁) {w φ g : ℂ → ℂ}
    (hfactor : ∀ z ∈ Metric.closedBall c R₁, z - φ z = (z - x) * g z)
    (hwd : DiffContOnCl ℂ w (Metric.ball c R₁))
    (hgd : DiffContOnCl ℂ g (Metric.ball c R₁))
    (hg0 : ∀ z ∈ Metric.closedBall c R₁, g z ≠ 0) :
    (2 * ↑π * Complex.I)⁻¹ • (∮ z in C(c, R₁), w z / (z - φ z))
      = w x / g x := by
  -- the Cauchy-formula integrand
  have hcont : ContinuousOn (fun z => w z * (g z)⁻¹) (Metric.closedBall c R₁) :=
    hwd.continuousOn_ball.mul (hgd.continuousOn_ball.inv₀ hg0)
  have hdiff : ∀ z ∈ Metric.ball c R₁ \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun z => w z * (g z)⁻¹) z := by
    intro z hz
    have hz' : z ∈ Metric.ball c R₁ := hz.1
    have hd : DifferentiableOn ℂ (fun z => w z * (g z)⁻¹) (Metric.ball c R₁) :=
      hwd.differentiableOn.mul (hgd.differentiableOn.inv
        fun y hy => hg0 y (Metric.ball_subset_closedBall hy))
    exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz')
  -- rewrite the integrand via the factorization
  have hcong : (∮ z in C(c, R₁), w z / (z - φ z))
      = ∮ z in C(c, R₁), (z - x)⁻¹ • (w z * (g z)⁻¹) := by
    apply circleIntegral.integral_congr hR₁.le
    intro z hz
    have hz' : z ∈ Metric.sphere c R₁ := by
      simpa [abs_of_pos hR₁] using hz
    dsimp only
    rw [hfactor z (Metric.sphere_subset_closedBall hz'), smul_eq_mul,
      div_eq_mul_inv, mul_inv]
    ring
  rw [hcong,
    Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hx hcont hdiff, div_eq_mul_inv]

/-- **The cofactor at the fixed point is `1 − φ'(x)`**: differentiate the
factorization at `x`. -/
theorem cofactor_eq_one_sub_deriv {x : ℂ} (hx : x ∈ Metric.ball c R₁)
    {φ g : ℂ → ℂ}
    (hfactor : ∀ z ∈ Metric.closedBall c R₁, z - φ z = (z - x) * g z)
    (hφd : DifferentiableAt ℂ φ x)
    (hgd : DiffContOnCl ℂ g (Metric.ball c R₁)) :
    g x = 1 - deriv φ x := by
  have hgx : DifferentiableAt ℂ g x :=
    hgd.differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds hx)
  -- left side: d/dz (z − φ z) at x
  have hL : HasDerivAt (fun z => z - φ z) (1 - deriv φ x) x :=
    (hasDerivAt_id x).sub hφd.hasDerivAt
  -- right side: d/dz ((z − x)·g z) at x is g x
  have hRt : HasDerivAt (fun z => (z - x) * g z) (g x) x := by
    have h1 : HasDerivAt (fun z => z - x) 1 x := (hasDerivAt_id x).sub_const x
    simpa using h1.mul hgx.hasDerivAt
  -- the two functions agree near x, so the derivatives agree
  have heq : (fun z => (z - x) * g z) =ᶠ[nhds x] fun z => z - φ z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact (hfactor z (Metric.ball_subset_closedBall hz)).symm
  have hL' : HasDerivAt (fun z => (z - x) * g z) (1 - deriv φ x) x :=
    hL.congr_of_eventuallyEq heq
  exact hRt.unique hL'

/-! ### The trace formula -/

/-- **THE HOLOMORPHIC LEFSCHETZ TRACE FORMULA** for the transfer matrix:
under the r186 contraction geometry plus holomorphy of the weights and
branches inside the disc, with each branch's simple-zero factorization,

`Σ'_m A[m,m] = Σ_k w_k(x_k) / (1 − φ_k'(x_k))`.

The trace of the transfer operator is the sum of fixed-point residues. -/
theorem trace_eq_residues (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W) {w φ : Fin K → ℂ → ℂ}
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ)
    {x : Fin K → ℂ} (hx : ∀ k, x k ∈ Metric.ball c R₁)
    {g : Fin K → ℂ → ℂ}
    (hfactor : ∀ k, ∀ z ∈ Metric.closedBall c R₁,
      z - φ k z = (z - x k) * g k z)
    (hwd : ∀ k, DiffContOnCl ℂ (w k) (Metric.ball c R₁))
    (hφd : ∀ k, DiffContOnCl ℂ (φ k) (Metric.ball c R₁))
    (hgd : ∀ k, DiffContOnCl ℂ (g k) (Metric.ball c R₁))
    (hg0 : ∀ k, ∀ z ∈ Metric.closedBall c R₁, g k z ≠ 0) :
    (∑' m : ℕ, transferMatrix c R R₁ K w φ m m)
      = ∑ k : Fin K, w k (x k) / (1 - deriv (φ k) (x k)) := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hτR₁ : τ < R₁ := hτR.trans hRR
  have hmem : ∀ θ : ℝ, circleMap c R₁ θ ∈ Metric.sphere c R₁ :=
    fun θ => circleMap_mem_sphere c hR₁.le θ
  have hwc : ∀ k, ContinuousOn (w k) (Metric.sphere c R₁) :=
    fun k => (hwd k).continuousOn_ball.mono Metric.sphere_subset_closedBall
  have hφc : ∀ k, ContinuousOn (φ k) (Metric.sphere c R₁) :=
    fun k => (hφd k).continuousOn_ball.mono Metric.sphere_subset_closedBall
  rw [trace_eq_contour hR hRR hτ0 hτR hW hwc hφc hw hφ]
  -- split the contour over the finite branch sum
  have hsplit : (∮ z in C(c, R₁), ∑ k : Fin K, w k z / (z - φ k z))
      = ∑ k : Fin K, ∮ z in C(c, R₁), w k z / (z - φ k z) := by
    simp only [circleIntegral]
    rw [← intervalIntegral.integral_finset_sum]
    · apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [Finset.smul_sum]
    · intro k _
      apply Continuous.intervalIntegrable
      apply Continuous.smul
      · exact ((continuous_circleMap 0 R₁).mul continuous_const).congr
          fun θ => (deriv_circleMap c R₁ θ).symm
      · apply Continuous.div
        · exact (hwc k).comp_continuous (continuous_circleMap c R₁) hmem
        · exact (continuous_circleMap c R₁).sub
            ((hφc k).comp_continuous (continuous_circleMap c R₁) hmem)
        · intro θ
          exact sub_apply_ne_zero hτR₁ hφ k (hmem θ)
  rw [hsplit, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hφdAt : DifferentiableAt ℂ (φ k) (x k) :=
    (hφd k).differentiableOn.differentiableAt
      (Metric.isOpen_ball.mem_nhds (hx k))
  rw [contour_eq_residue_single hR₁ (hx k) (hfactor k) (hwd k) (hgd k) (hg0 k),
    cofactor_eq_one_sub_deriv (hx k) (hfactor k) hφdAt (hgd k)]

/-- **Non-vacuity witness** (audit rule 2026-08-01): every hypothesis of
`trace_eq_residues` is satisfiable and the formula computes.  One constant
branch `φ = 0` at center `0`, weight `w = 1`, cofactor `g = 1`, fixed point
`x = 0`: the trace of the resulting rank-one averaging operator is
`1/(1 − 0) = 1`. -/
example : (∑' m : ℕ, transferMatrix (0 : ℂ) (1/2) 1 1
    (fun _ _ => 1) (fun _ _ => (0 : ℂ)) m m) = 1 := by
  have h := trace_eq_residues (c := 0) (R := 1/2) (R₁ := 1) (τ := 0) (W := 1)
    (w := fun _ _ => 1) (φ := fun _ _ => (0 : ℂ)) (K := 1)
    (by norm_num) (by norm_num) le_rfl (by norm_num) zero_le_one
    (fun k z _ => by simp)
    (fun k z _ => by simp)
    (x := fun _ => 0) (fun k => by simp)
    (g := fun _ _ => 1) (fun k z _ => by ring)
    (fun k => diffContOnCl_const)
    (fun k => diffContOnCl_const)
    (fun k => diffContOnCl_const)
    (fun k z _ => one_ne_zero)
  rw [h]
  simp

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.fixedPoint_of_factor
#print axioms PrincipiaTractalis.HilbertSchmidtL2.contour_eq_residue_single
#print axioms PrincipiaTractalis.HilbertSchmidtL2.cofactor_eq_one_sub_deriv
#print axioms PrincipiaTractalis.HilbertSchmidtL2.trace_eq_residues
