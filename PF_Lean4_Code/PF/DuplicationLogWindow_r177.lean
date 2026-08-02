/-
# PF.DuplicationLogWindow_r177

★★★ 2026-08-01 — `HeightWindow` FROM CURVE COEFFICIENTS ALONE ★★★

r176 closed the multiplicative window `H(x)⁴ ≤ CL·H(2x)`, `H(2x) ≤ CU·H(x)⁴`
for every rational Weierstrass curve.  This stone takes logarithms and hands the
result to r171's `HeightWindow`, which r173 proved is the *only* input the
canonical height ever needed.

## The chain, now complete

  r174  content   `gcd(Φ,Ψ) ∣ Δ²`              universal
  r175  size      `Δ²M⁴ ≤ CL·max|Φ||Ψ| ≤ …`    universal
  r176  heights   `H(x)⁴ ≤ CL·H(2x) ≤ …`       universal
  r177  logs      `HeightWindow … κ`, κ = max CU CL
  r171  ⟹ the canonical height exists, with all its laws
  r173  ⟹ and it is unique

## ⚠ CORRECTED BY r179 — READ BEFORE USING `heightWindow_of_xdbl`

`heightWindow_of_xdbl` below quantifies `hx` over **all** `R`, including the
point at infinity.  With the standard convention `x(O) = 0` that demands
`0 = dblQ 0 = −b₈/b₆`, which is false (389a1: 3; 5077a1: 49/25).  The theorem is
true but its hypothesis cannot be discharged for a real point group.

`PF.DuplicationLogWindowFixed_r179.heightWindow_of_xdbl_ne_zero` is the usable
form: it quantifies away from `0` and handles `O` by `lognh 0 = 0`.  Everything
else in this file — in particular `abs_lognh_dblQ_sub_le`, which is the actual
analytic content — is unaffected and is what r179 calls.

## The one remaining per-curve obligation

`heightWindow_of_xdbl` takes a group `G`, an `x`-coordinate map `xco : G → ℚ`,
and **one** hypothesis: that `xco` intertwines doubling with `dblQ`, i.e.
`xco (R + R) = dblQ b₂ b₄ b₆ b₈ (xco R)`.  That is precisely the statement that
`Φ/Ψ` computes the group law on `x`-coordinates, verified numerically against
eight on-curve points in r176 and supplied per curve by mathlib's `Point.add`.

Everything else — the constants, the Cauchy construction, the doubling law, the
window, uniqueness — is now curve-independent.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-01.
-/
import PF.DuplicationHeightUniversal_r176
import PF.CanonicalHeightGeneric_r171

set_option maxHeartbeats 1000000

namespace PrincipiaTractalis.DuplicationLogWindow

open PrincipiaTractalis.DuplicationBezout PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.CanonicalHeightGeneric

variable {b₂ b₄ b₆ b₈ : ℤ}

/-- The universal window constant. -/
def kappa (b₂ b₄ b₆ b₈ : ℤ) : ℤ := max (CU b₂ b₄ b₆ b₈) (CL b₂ b₄ b₆ b₈)

/-- The logarithmic naive height of a rational. -/
noncomputable def lognh (x : ℚ) : ℝ := Real.log (nh x)

theorem one_le_nh (x : ℚ) : (1 : ℤ) ≤ nh x := nh_pos x

theorem lognh_nonneg (x : ℚ) : 0 ≤ lognh x :=
  Real.log_nonneg (by exact_mod_cast one_le_nh x)

theorem one_le_CU (b₂ b₄ b₆ b₈ : ℤ) : (1 : ℤ) ≤ CU b₂ b₄ b₆ b₈ := by
  simp only [CU]
  refine le_trans ?_ (le_max_left _ _)
  linarith [abs_nonneg b₄, abs_nonneg b₆, abs_nonneg b₈]

/-- **The logarithmic window**, for every curve, from the coefficients alone. -/
theorem abs_lognh_dblQ_sub_le (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2)
    (hΔ : Disc b₂ b₄ b₆ b₈ ≠ 0) (x : ℚ)
    (hΨ : Psi b₂ b₄ b₆ x.num (x.den : ℤ) ≠ 0) :
    |lognh (dblQ b₂ b₄ b₆ b₈ x) - 4 * lognh x| ≤ Real.log (kappa b₂ b₄ b₆ b₈) := by
  have hup : nh (dblQ b₂ b₄ b₆ b₈ x) ≤ CU b₂ b₄ b₆ b₈ * nh x ^ 4 := nh_dblQ_le x hΨ
  have hlo : nh x ^ 4 ≤ CL b₂ b₄ b₆ b₈ * nh (dblQ b₂ b₄ b₆ b₈ x) :=
    nh_pow_le_of_disc_ne_zero hrel x hΨ hΔ
  -- Positivity, in ℝ.
  have hAz : (1 : ℤ) ≤ nh x := one_le_nh x
  have hBz : (1 : ℤ) ≤ nh (dblQ b₂ b₄ b₆ b₈ x) := one_le_nh _
  have hA : (1 : ℝ) ≤ (nh x : ℝ) := by exact_mod_cast hAz
  have hB : (1 : ℝ) ≤ ((nh (dblQ b₂ b₄ b₆ b₈ x) : ℤ) : ℝ) := by exact_mod_cast hBz
  have hA0 : (0 : ℝ) < (nh x : ℝ) := lt_of_lt_of_le one_pos hA
  have hB0 : (0 : ℝ) < ((nh (dblQ b₂ b₄ b₆ b₈ x) : ℤ) : ℝ) := lt_of_lt_of_le one_pos hB
  -- CL > 0, forced by the lower bound itself (1 ≤ nh x ^ 4 ≤ CL * nh (2x)).
  have hCLz : (0 : ℤ) < CL b₂ b₄ b₆ b₈ := by
    by_contra hc
    push_neg at hc
    have h1 : (1 : ℤ) ≤ nh x ^ 4 := one_le_pow₀ hAz
    have h2 : CL b₂ b₄ b₆ b₈ * nh (dblQ b₂ b₄ b₆ b₈ x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (le_of_lt (nh_pos _))
    omega
  have hCUz : (0 : ℤ) < CU b₂ b₄ b₆ b₈ := lt_of_lt_of_le one_pos (one_le_CU _ _ _ _)
  have hCU : (0 : ℝ) < (CU b₂ b₄ b₆ b₈ : ℝ) := by exact_mod_cast hCUz
  have hCL : (0 : ℝ) < (CL b₂ b₄ b₆ b₈ : ℝ) := by exact_mod_cast hCLz
  -- Cast the two integer bounds to ℝ.
  have hupR : ((nh (dblQ b₂ b₄ b₆ b₈ x) : ℤ) : ℝ)
      ≤ (CU b₂ b₄ b₆ b₈ : ℝ) * (nh x : ℝ) ^ 4 := by exact_mod_cast hup
  have hloR : ((nh x : ℤ) : ℝ) ^ 4
      ≤ (CL b₂ b₄ b₆ b₈ : ℝ) * ((nh (dblQ b₂ b₄ b₆ b₈ x) : ℤ) : ℝ) := by
    exact_mod_cast hlo
  -- Both constants are ≤ κ.
  have hkU : CU b₂ b₄ b₆ b₈ ≤ kappa b₂ b₄ b₆ b₈ := le_max_left _ _
  have hkL : CL b₂ b₄ b₆ b₈ ≤ kappa b₂ b₄ b₆ b₈ := le_max_right _ _
  have hCUk : Real.log (CU b₂ b₄ b₆ b₈) ≤ Real.log (kappa b₂ b₄ b₆ b₈) :=
    Real.log_le_log hCU (by exact_mod_cast hkU)
  have hCLk : Real.log (CL b₂ b₄ b₆ b₈) ≤ Real.log (kappa b₂ b₄ b₆ b₈) :=
    Real.log_le_log hCL (by exact_mod_cast hkL)
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- lower side: 4·log H(x) − log H(2x) ≤ log CL ≤ log κ
    have h := Real.log_le_log (by positivity) hloR
    rw [Real.log_pow, Real.log_mul (ne_of_gt hCL) (ne_of_gt hB0)] at h
    simp only [lognh]
    push_cast at h ⊢
    linarith
  · -- upper side: log H(2x) − 4·log H(x) ≤ log CU ≤ log κ
    have h := Real.log_le_log hB0 hupR
    rw [Real.log_mul (ne_of_gt hCU) (by positivity), Real.log_pow] at h
    simp only [lognh]
    push_cast at h ⊢
    linarith

/-- **`HeightWindow` for any group carrying a compatible `x`-coordinate.**

The single per-curve obligation is `hx`: that `Φ/Ψ` computes doubling on
`x`-coordinates. -/
theorem heightWindow_of_xdbl {G : Type} [AddCommGroup G]
    (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) (hΔ : Disc b₂ b₄ b₆ b₈ ≠ 0)
    (xco : G → ℚ)
    (hΨ : ∀ R : G, Psi b₂ b₄ b₆ (xco R).num ((xco R).den : ℤ) ≠ 0)
    (hx : ∀ R : G, xco (R + R) = dblQ b₂ b₄ b₆ b₈ (xco R)) :
    HeightWindow (fun R : G => lognh (xco R)) (kappa b₂ b₄ b₆ b₈ : ℝ) where
  nonneg R := lognh_nonneg _
  one_le := by
    have : (1 : ℤ) ≤ kappa b₂ b₄ b₆ b₈ :=
      le_trans (one_le_CU b₂ b₄ b₆ b₈) (le_max_left _ _)
    exact_mod_cast this
  window R := by
    rw [hx R]
    exact abs_lognh_dblQ_sub_le hrel hΔ (xco R) (hΨ R)

/-! ### The payoff, stated plainly.

Given a curve and a compatible `x`-coordinate, r171 now yields the canonical
height and every one of its laws, and r173 yields uniqueness — with no
curve-specific work beyond `hx`. -/

theorem canonical_height_exists {G : Type} [AddCommGroup G]
    (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) (hΔ : Disc b₂ b₄ b₆ b₈ ≠ 0)
    (xco : G → ℚ)
    (hΨ : ∀ R : G, Psi b₂ b₄ b₆ (xco R).num ((xco R).den : ℤ) ≠ 0)
    (hx : ∀ R : G, xco (R + R) = dblQ b₂ b₄ b₆ b₈ (xco R)) :
    ∀ R : G,
      canheight (fun S : G => lognh (xco S)) (R + R)
        = 4 * canheight (fun S : G => lognh (xco S)) R :=
  fun R => canheight_dbl (heightWindow_of_xdbl hrel hΔ xco hΨ hx) R

end PrincipiaTractalis.DuplicationLogWindow

#print axioms PrincipiaTractalis.DuplicationLogWindow.abs_lognh_dblQ_sub_le
#print axioms PrincipiaTractalis.DuplicationLogWindow.heightWindow_of_xdbl
#print axioms PrincipiaTractalis.DuplicationLogWindow.canonical_height_exists
