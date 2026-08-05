/-
# PF.DynamicalDeterminant_r204

★★★ 2026-08-05 — TRACE BOUNDS AND THE DYNAMICAL DETERMINANT ★★★

r192 proved `A⁽ⁿ⁾ = Aⁿ` and r191 identified each trace with a periodic-orbit
sum.  This stone supplies what turns those traces into an analytic object:
**a uniform geometric bound on `Tr(Aⁿ)`**, and with it the convergence of the
trace series that *defines* the dynamical determinant,

  `det(1 − tA) := exp(−Σ_{n≥1} tⁿ·Tr(Aⁿ)/n)`.

Contents:

* `norm_tsum_diag_le` — for any matrix with double-geometric decay
  `‖A m n‖ ≤ C·r^m·ρ^n` and `rρ < 1`, the diagonal trace obeys
  `‖Σ'_m A[m,m]‖ ≤ C/(1 − rρ)`.  General, reusable, no dynamics.
* `geomBound_power` — the `(n+1)`-word system inherits the r186 bound with
  constant `Kⁿ⁺¹Wⁿ⁺¹`: contraction and weight bounds compose (r191).
* `norm_trace_matPow_le` — hence, through `transferMatrix_pow` (r192),
  `‖Tr(Aⁿ⁺¹)‖ ≤ Kⁿ⁺¹Wⁿ⁺¹/(1 − τ/R₁)` — the traces grow at most
  geometrically, at rate `KW`.
* `summable_traceSeries` — so `Σ_n tⁿ⁺¹·Tr(Aⁿ⁺¹)/(n+1)` converges absolutely
  whenever `|t|·K·W < 1`.
* `dynDet` — the dynamical determinant on that disc, and `dynDet_ne_zero`.

**Scope — read this before quoting anything.**  `dynDet` is *defined* by the
exponential-trace series; that is the standard definition of the dynamical
(Ruelle) determinant, and it is what the periodic-orbit data computes.  It is
NOT here proved equal to a Fredholm determinant of an operator, because no
determinant of an infinite matrix is available at this pin — that
identification (and with it any statement that its zeros are reciprocal
eigenvalues) is exactly the missing analytic content, and is not claimed.
`dynDet_ne_zero` says the determinant does not vanish *on the disc of
convergence*; the interesting zeros live outside it, in a continuation that
is not constructed here.  Nothing in this file concerns Selberg zeta
functions, the Riemann zeta function, or the Riemann hypothesis.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-05.
-/
import PF.TransferCompose_r192

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.HilbertSchmidtL2

open Complex Metric Real
open scoped Real NNReal

noncomputable section

variable {c : ℂ} {R R₁ τ W : ℝ} {K : ℕ} {w φ : Fin K → ℂ → ℂ}

/-! ### §1 — the diagonal trace of a geometrically decaying matrix -/

/-- **The trace bound.**  Double-geometric decay with `rρ < 1` bounds the
diagonal sum by `C/(1 − rρ)`.  No dynamics, no analyticity. -/
theorem norm_tsum_diag_le {A : ℕ → ℕ → ℂ} {C r ρ : ℝ}
    (h : GeomBound A C r ρ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hρ0 : 0 ≤ ρ)
    (hrρ : r * ρ < 1) :
    ‖∑' m : ℕ, A m m‖ ≤ C / (1 - r * ρ) := by
  have hrρ0 : (0 : ℝ) ≤ r * ρ := mul_nonneg hr0 hρ0
  have hdiag : ∀ m, ‖A m m‖ ≤ C * (r * ρ) ^ m := by
    intro m
    calc ‖A m m‖ ≤ C * r ^ m * ρ ^ m := h m m
      _ = C * (r * ρ) ^ m := by rw [mul_assoc, ← mul_pow]
  have hgeo : Summable fun m : ℕ => C * (r * ρ) ^ m :=
    (summable_geometric_of_lt_one hrρ0 hrρ).mul_left C
  have hnorm : Summable fun m : ℕ => ‖A m m‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hdiag hgeo
  calc ‖∑' m : ℕ, A m m‖ ≤ ∑' m : ℕ, ‖A m m‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, C * (r * ρ) ^ m := hnorm.tsum_le_tsum hdiag hgeo
    _ = C / (1 - r * ρ) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hrρ0 hrρ, div_eq_mul_inv]

/-! ### §2 — the word systems inherit the geometric bound -/

/-- The `(n+1)`-word system satisfies the r186 bound with constant
`Kⁿ⁺¹·Wⁿ⁺¹`. -/
theorem geomBound_power (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hw : ∀ k, ∀ z ∈ Metric.closedBall c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (hwd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (w k) z)
    (hφd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (φ k) z)
    (n : ℕ) :
    GeomBound (transferMatrix c R R₁ (K ^ (n + 1))
        (powerWeight w φ (n + 1)) (powerBranch φ (n + 1)))
      (((K ^ (n + 1) : ℕ) : ℝ) * W ^ (n + 1)) (R / R₁) (τ / R) := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hτR₁ : τ ≤ R₁ := le_of_lt (hτR.trans hRR)
  have hword_ne : ∀ i : Fin (K ^ (n + 1)),
      (List.ofFn (finFunctionFinEquiv.symm i) : List (Fin K)) ≠ [] :=
    fun i => List.ne_nil_of_length_pos
      (by rw [List.length_ofFn]; exact Nat.succ_pos n)
  have hwn : ∀ j, ∀ z ∈ Metric.sphere c R₁,
      ‖powerWeight w φ (n + 1) j z‖ ≤ W ^ (n + 1) := by
    intro j z hz
    have h := norm_listWeight_le hτR₁ hW hw hφ
      (List.ofFn (finFunctionFinEquiv.symm j)) z
      (Metric.sphere_subset_closedBall hz)
    rwa [List.length_ofFn] at h
  have hφn : ∀ j, ∀ z ∈ Metric.sphere c R₁,
      powerBranch φ (n + 1) j z ∈ Metric.closedBall c τ :=
    fun j z hz => listBranch_mem_tau_of_ne_nil hτR₁ hφ (hword_ne j) z
      (Metric.sphere_subset_closedBall hz)
  have hwdn : ∀ j, ∀ z ∈ Metric.closedBall c R₁,
      DifferentiableAt ℂ (powerWeight w φ (n + 1) j) z :=
    fun j z hz => differentiableAt_listWeight hτR₁ hφ hwd hφd _ z hz
  have hφdn : ∀ j, ∀ z ∈ Metric.closedBall c R₁,
      DifferentiableAt ℂ (powerBranch φ (n + 1) j) z :=
    fun j z hz => differentiableAt_listBranch hτR₁ hφ hφd _ z hz
  have hwcn : ∀ j, ContinuousOn (powerWeight w φ (n + 1) j)
      (Metric.sphere c R₁) :=
    fun j z hz => ((hwdn j z
      (Metric.sphere_subset_closedBall hz)).continuousAt).continuousWithinAt
  have hφcn : ∀ j, ContinuousOn (powerBranch φ (n + 1) j)
      (Metric.sphere c R₁) :=
    fun j z hz => ((hφdn j z
      (Metric.sphere_subset_closedBall hz)).continuousAt).continuousWithinAt
  exact geomBound_transferMatrix hR hRR hτ0 hτR (pow_nonneg hW (n + 1))
    hwcn hφcn hwn hφn

/-! ### §3 — the traces of the powers grow at most geometrically -/

/-- **The key estimate**: `‖Tr(Aⁿ⁺¹)‖ ≤ Kⁿ⁺¹Wⁿ⁺¹/(1 − τ/R₁)`.  The traces of
all matrix powers are controlled at the single geometric rate `KW`. -/
theorem norm_trace_matPow_le (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hw : ∀ k, ∀ z ∈ Metric.closedBall c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (hwd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (w k) z)
    (hφd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (φ k) z)
    (n : ℕ) :
    ‖∑' m : ℕ, matPowPos (transferMatrix c R R₁ K w φ) n m m‖
      ≤ ((K : ℝ) * W) ^ (n + 1) / (1 - τ / R₁) := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hτR₁ : τ < R₁ := hτR.trans hRR
  have hratio : τ / R₁ < 1 := by rw [div_lt_one hR₁]; linarith
  have hprod : (R / R₁) * (τ / R) = τ / R₁ := by
    field_simp
  have hgb := geomBound_power hR hRR hτ0 hτR hW hw hφ hwd hφd n
  rw [← transferMatrix_pow hR hRR hτ0 hτR hW hw hφ hwd hφd n]
  have hbound := norm_tsum_diag_le hgb
    (by positivity) (by positivity) (by positivity)
    (by rw [hprod]; exact hratio)
  rw [hprod] at hbound
  have hCeq : ((K ^ (n + 1) : ℕ) : ℝ) * W ^ (n + 1) = ((K : ℝ) * W) ^ (n + 1) := by
    push_cast
    ring
  rwa [hCeq] at hbound

/-! ### §4 — the trace series converges -/

/-- The `n`-th coefficient of the log-determinant series. -/
def traceTerm (A : ℕ → ℕ → ℂ) (t : ℂ) (n : ℕ) : ℂ :=
  t ^ (n + 1) * (∑' m : ℕ, matPowPos A n m m) / ((n : ℂ) + 1)

/-- **Convergence.**  On the disc `|t|·K·W < 1` the trace series converges
absolutely. -/
theorem summable_traceSeries (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hw : ∀ k, ∀ z ∈ Metric.closedBall c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (hwd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (w k) z)
    (hφd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (φ k) z)
    {t : ℂ} (ht : ‖t‖ * ((K : ℝ) * W) < 1) :
    Summable (traceTerm (transferMatrix c R R₁ K w φ) t) := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hτR₁ : τ < R₁ := hτR.trans hRR
  have hratio : τ / R₁ < 1 := by rw [div_lt_one hR₁]; linarith
  have hden : (0 : ℝ) < 1 - τ / R₁ := by linarith
  have hKW0 : (0 : ℝ) ≤ (K : ℝ) * W := by positivity
  have hq0 : (0 : ℝ) ≤ ‖t‖ * ((K : ℝ) * W) := by positivity
  -- the dominating geometric series
  have hgeo : Summable fun n : ℕ =>
      (‖t‖ * ((K : ℝ) * W)) ^ (n + 1) / (1 - τ / R₁) := by
    apply Summable.div_const
    have h := (summable_geometric_of_lt_one hq0 ht).mul_left
      (‖t‖ * ((K : ℝ) * W))
    exact h.congr fun n => by ring
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hgeo
  intro n
  have htr := norm_trace_matPow_le hR hRR hτ0 hτR hW hw hφ hwd hφd n
  have hn1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    push_cast; ring
  rw [traceTerm, norm_div, norm_mul, norm_pow, hn1]
  have hX0 : (0 : ℝ) ≤ ‖t‖ ^ (n + 1) * ‖∑' m : ℕ,
      matPowPos (transferMatrix c R R₁ K w φ) n m m‖ := by positivity
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  calc ‖t‖ ^ (n + 1) * ‖∑' m : ℕ,
        matPowPos (transferMatrix c R R₁ K w φ) n m m‖ / ((n : ℝ) + 1)
      ≤ ‖t‖ ^ (n + 1) * ‖∑' m : ℕ,
        matPowPos (transferMatrix c R R₁ K w φ) n m m‖ := div_le_self hX0 h1
    _ ≤ ‖t‖ ^ (n + 1) * (((K : ℝ) * W) ^ (n + 1) / (1 - τ / R₁)) :=
        mul_le_mul_of_nonneg_left htr (by positivity)
    _ = (‖t‖ * ((K : ℝ) * W)) ^ (n + 1) / (1 - τ / R₁) := by
        rw [mul_pow]
        ring

/-! ### §5 — the dynamical determinant -/

/-- The dynamical (Ruelle) determinant, defined by the exponential-trace
series.  See the scope note in the file header: this is a definition, not an
identification with a Fredholm determinant. -/
def dynDet (A : ℕ → ℕ → ℂ) (t : ℂ) : ℂ :=
  Complex.exp (-∑' n : ℕ, traceTerm A t n)

/-- The dynamical determinant never vanishes on its disc of convergence —
the spectral information lives in the continuation, which is not constructed
here. -/
theorem dynDet_ne_zero (A : ℕ → ℕ → ℂ) (t : ℂ) : dynDet A t ≠ 0 :=
  Complex.exp_ne_zero _

/-- At `t = 0` the determinant is `1`. -/
theorem dynDet_zero (A : ℕ → ℕ → ℂ) : dynDet A 0 = 1 := by
  rw [dynDet]
  have h : ∀ n : ℕ, traceTerm A 0 n = 0 := by
    intro n
    rw [traceTerm, zero_pow (Nat.succ_ne_zero n), zero_mul, zero_div]
  rw [tsum_congr h, tsum_zero, neg_zero, Complex.exp_zero]

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.norm_tsum_diag_le
#print axioms PrincipiaTractalis.HilbertSchmidtL2.geomBound_power
#print axioms PrincipiaTractalis.HilbertSchmidtL2.norm_trace_matPow_le
#print axioms PrincipiaTractalis.HilbertSchmidtL2.summable_traceSeries
#print axioms PrincipiaTractalis.HilbertSchmidtL2.dynDet_zero
