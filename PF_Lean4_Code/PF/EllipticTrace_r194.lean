/-
# PF.EllipticTrace_r194

★★★ 2026-08-04 — THE TRACE FORMULA ON THE BSD FACE ★★★

r189 instantiated the Lefschetz trace formula (r188c) on the Gauss branches —
the RH face.  This stone instantiates it on the **ch24 elliptic operator** —
the BSD face: the contracting system

  φ_p(z) = z/p,     weights  a_p · p^(−s)

whose fixed-point trace is the regularized Mestre–Nagao sum

  trace  =  Σ_p  a_p p^(−s) / (1 − 1/p).

This is the operator whose trace slopes were MEASURED on kernel-verified
ranks (codex/BSD_TRACE_RANK_2026-08-03.md: slopes +0.780/+1.473/+2.168 for
ranks 1/2/3 of 37a1/389a1/5077a1, P = 5·10⁴).  With this stone the measured
quantity is a kernel-checked identity: the trace of the truncated transfer
matrix EQUALS the Mestre–Nagao sum, exactly — one machinery, two Millennium
faces, which is the framework's one-object principle in verified form.

All branches fix the origin; the geometry is the simplest possible:
c = 0, R₁ = 1, τ = 1/2 (since p ≥ 2), R = 3/4; the factorization is
`z − z/p = (z − 0)·(1 − 1/p)` with CONSTANT cofactor.

Scope — what this does and does not say: the trace identity is exact and
kernel-checked for every finite truncation, for ARBITRARY constant weights
(`elliptic_trace`) and in particular for the Mestre–Nagao weights
(`mestre_nagao_trace`).  Nothing about L-functions, analytic continuation,
ranks, or BSD is claimed: the connection trace ~ r·log(s−1) is the classical
Mestre–Nagao heuristic, measured (not proven) in the codex record.  The
branch integers are only assumed ≥ 2 — primality plays no role in the trace
formula itself.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-04.
-/
import PF.TransferCompose_r192

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.HilbertSchmidtL2

open Complex Metric Real
open scoped Real NNReal

noncomputable section

/-! ### The elliptic system: geometry -/

variable {K : ℕ} {P : Fin K → ℕ}

theorem ellipticDenom_ne_zero (hP : ∀ k, 2 ≤ P k) (k : Fin K) :
    ((P k : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by have := hP k; omega)

/-- The branches contract the unit circle into the ball of radius 1/2. -/
theorem ellipticBranch_mem (hP : ∀ k, 2 ≤ P k) (k : Fin K) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    z / ((P k : ℕ) : ℂ) ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
  rw [Metric.mem_sphere, dist_zero_right] at hz
  rw [Metric.mem_closedBall, dist_zero_right, norm_div, hz,
    Complex.norm_natCast]
  have h2 : (2 : ℝ) ≤ (P k : ℝ) := by exact_mod_cast hP k
  exact one_div_le_one_div_of_le (by norm_num) h2

/-- The constant cofactor never vanishes. -/
theorem ellipticCofactor_ne_zero (hP : ∀ k, 2 ≤ P k) (k : Fin K) :
    (1 : ℂ) - ((P k : ℕ) : ℂ)⁻¹ ≠ 0 := by
  have hp2 : (2 : ℝ) ≤ (P k : ℝ) := by exact_mod_cast hP k
  intro h0
  have h1 : ((P k : ℕ) : ℂ)⁻¹ = 1 := by linear_combination -h0
  have h2 : ((P k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (by have := hP k; omega)
  have h3 : ((P k : ℕ) : ℂ) = 1 := by
    field_simp at h1
    linear_combination -h1
  have h4 : (P k : ℝ) = 1 := by exact_mod_cast h3
  linarith

/-! ### THE ELLIPTIC TRACE -/

/-- **The trace of the elliptic system**, arbitrary constant weights: for
branches `z ↦ z/p_k` (`p_k ≥ 2`) with constant weights `A_k`,

`Σ'_m A[m,m] = Σ_k A_k / (1 − 1/p_k)`. -/
theorem elliptic_trace (K : ℕ) (P : Fin K → ℕ) (hP : ∀ k, 2 ≤ P k)
    (A : Fin K → ℂ) :
    (∑' m : ℕ, transferMatrix 0 (3 / 4) 1 K
        (fun k _ => A k) (fun k z => z / ((P k : ℕ) : ℂ)) m m)
      = ∑ k : Fin K, A k / (1 - ((P k : ℕ) : ℂ)⁻¹) := by
  -- uniform bound on the constant weights
  set W : ℝ := ((Finset.univ.sup fun k => ‖A k‖₊ : ℝ≥0) : ℝ) with hWdef
  have hW0 : 0 ≤ W := NNReal.coe_nonneg _
  have hWb : ∀ k : Fin K, ‖A k‖ ≤ W := by
    intro k
    rw [hWdef, ← coe_nnnorm]
    exact_mod_cast Finset.le_sup (f := fun k => ‖A k‖₊) (Finset.mem_univ k)
  have hPne : ∀ k : Fin K, ((P k : ℕ) : ℂ) ≠ 0 := by
    intro k
    exact_mod_cast Nat.cast_ne_zero.mpr (by have := hP k; omega)
  have main := trace_eq_residues (c := 0) (R := 3 / 4) (R₁ := 1)
    (τ := 1 / 2) (W := W) (K := K)
    (w := fun k _ => A k) (φ := fun k z => z / ((P k : ℕ) : ℂ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hW0
    (fun k z _ => hWb k)
    (fun k z hz => ellipticBranch_mem hP k hz)
    (x := fun _ => 0) (fun k => by simp)
    (g := fun k _ => 1 - ((P k : ℕ) : ℂ)⁻¹)
    (fun k z hz => by
      rw [sub_zero]
      field_simp)
    (fun k => diffContOnCl_const)
    (fun k => diffContOnCl_of_differentiableAt (by norm_num) fun z hz =>
      differentiableAt_id.div_const _)
    (fun k => diffContOnCl_const)
    (fun k z hz => ellipticCofactor_ne_zero hP k)
  rw [main]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  have hd : deriv (fun z : ℂ => z / ((P k : ℕ) : ℂ)) 0
      = ((P k : ℕ) : ℂ)⁻¹ := by
    have h : HasDerivAt (fun z : ℂ => z / ((P k : ℕ) : ℂ))
        (1 / ((P k : ℕ) : ℂ)) 0 :=
      (hasDerivAt_id (0 : ℂ)).div_const _
    rw [h.deriv, one_div]
  rw [hd]

/-- **The Mestre–Nagao trace, kernel-checked**: with the ch24 weights
`a_k · p_k^(−s)`,

`Σ'_m A[m,m](s) = Σ_k a_k p_k^(−s) / (1 − 1/p_k)`

— exactly the regularized sum whose slope in `s` was measured on
kernel-verified ranks (codex/BSD_TRACE_RANK_2026-08-03.md). -/
theorem mestre_nagao_trace (K : ℕ) (P : Fin K → ℕ) (hP : ∀ k, 2 ≤ P k)
    (a : Fin K → ℤ) (s : ℂ) :
    (∑' m : ℕ, transferMatrix 0 (3 / 4) 1 K
        (fun k _ => (a k : ℂ) * ((P k : ℕ) : ℂ) ^ (-s))
        (fun k z => z / ((P k : ℕ) : ℂ)) m m)
      = ∑ k : Fin K, (a k : ℂ) * ((P k : ℕ) : ℂ) ^ (-s)
          / (1 - ((P k : ℕ) : ℂ)⁻¹) :=
  elliptic_trace K P hP (fun k => (a k : ℂ) * ((P k : ℕ) : ℂ) ^ (-s))

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.elliptic_trace
#print axioms PrincipiaTractalis.HilbertSchmidtL2.mestre_nagao_trace
