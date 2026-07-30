/-
# PF.QuasiParallelogramSize5077a1_r159

★★★ 2026-07-30 — r159: SIZE UPPER BOUNDS FOR THE 5077a1 ADDITION FORMS ★★★

The triangle-inequality half of W2's size control for the rank-3 curve: each
bihomogeneous addition form is bounded by its coefficient sum times `H₁²·H₂²`,
where `Hᵢ = max |aᵢ| |bᵢ|`:

  `|DD| ≤ 4·H₁²H₂²`,   `|Sf| ≤ 57·H₁²H₂²`,   `|Pf| ≤ 114·H₁²H₂²`.

(389a1 for comparison: `4`, `17`, `10`.)

The `114` is not a coincidence and serves as a cross-check on the whole W2
derivation: `p(t,t) = f(t)` (r157's `Pf_diagonal`), and `f`'s coefficient sum
is `1 + 14 + 50 + 49 = 114`, which is exactly the upper duplication
coefficient r146 proved independently.

With r158's content bound these give the upper half of
`naiveHeight(x₃)·naiveHeight(x₄) ≍ H₁²H₂²`.

## Note on the proof

r148c wrote out the iterated `Int.natAbs_add_le` / `natAbs_sub_le` chain
inline for each form. Here it is factored into `natAbs_add5_le`, since all
three 5077a1 forms have exactly five monomials; that keeps each bound to a
`ring`-normalised triangle step plus five `pair_bound` applications.

HONEST SCOPE. Upper bounds only. NO lower bound, NO height inequality, NO
secant bridge, NO parallelogram law, NO rank-3 statement.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-30.
-/
import PF.QuasiParallelogramCerts5077a1_r157
import Mathlib.Tactic.Linarith

namespace PrincipiaTractalis.QuasiParallelogramSize5077a1

open PrincipiaTractalis.QuasiParallelogramCerts5077a1

/-! ## §1 — reusable triangle and monomial lemmas -/

/-- Triangle inequality for a five-term integer sum, in `natAbs`. -/
private theorem natAbs_add5_le (x y z w v : ℤ) :
    (x + y + z + w + v).natAbs
      ≤ x.natAbs + y.natAbs + z.natAbs + w.natAbs + v.natAbs := by
  calc (x + y + z + w + v).natAbs
      ≤ (x + y + z + w).natAbs + v.natAbs := Int.natAbs_add_le _ _
    _ ≤ ((x + y + z).natAbs + w.natAbs) + v.natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ (((x + y).natAbs + z.natAbs) + w.natAbs) + v.natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ ≤ ((((x.natAbs + y.natAbs) + z.natAbs) + w.natAbs) + v.natAbs) :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _) _

/-- Any bidegree-(2,2) monomial is at most `H₁²·H₂²`. -/
private theorem pair_bound (a₁ b₁ a₂ b₂ : ℤ) (i₁ j₁ i₂ j₂ : ℕ)
    (h₁ : i₁ + j₁ = 2) (h₂ : i₂ + j₂ = 2) :
    a₁.natAbs ^ i₁ * b₁.natAbs ^ j₁ * (a₂.natAbs ^ i₂ * b₂.natAbs ^ j₂)
      ≤ (max a₁.natAbs b₁.natAbs) ^ 2 * (max a₂.natAbs b₂.natAbs) ^ 2 := by
  have g₁ : a₁.natAbs ^ i₁ * b₁.natAbs ^ j₁ ≤ (max a₁.natAbs b₁.natAbs) ^ 2 := by
    calc a₁.natAbs ^ i₁ * b₁.natAbs ^ j₁
        ≤ (max a₁.natAbs b₁.natAbs) ^ i₁ * (max a₁.natAbs b₁.natAbs) ^ j₁ :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) _)
            (Nat.pow_le_pow_left (le_max_right _ _) _)
      _ = (max a₁.natAbs b₁.natAbs) ^ 2 := by rw [← pow_add, h₁]
  have g₂ : a₂.natAbs ^ i₂ * b₂.natAbs ^ j₂ ≤ (max a₂.natAbs b₂.natAbs) ^ 2 := by
    calc a₂.natAbs ^ i₂ * b₂.natAbs ^ j₂
        ≤ (max a₂.natAbs b₂.natAbs) ^ i₂ * (max a₂.natAbs b₂.natAbs) ^ j₂ :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) _)
            (Nat.pow_le_pow_left (le_max_right _ _) _)
      _ = (max a₂.natAbs b₂.natAbs) ^ 2 := by rw [← pow_add, h₂]
  exact Nat.mul_le_mul g₁ g₂

/-! ## §2 — the three form bounds -/

/-- `|DD| ≤ 4·H₁²·H₂²`.  (Same form as 389a1; same bound.) -/
theorem DD_upper (a₁ b₁ a₂ b₂ : ℤ) :
    (DD a₁ b₁ a₂ b₂).natAbs
      ≤ 4 * (max a₁.natAbs b₁.natAbs) ^ 2 * (max a₂.natAbs b₂.natAbs) ^ 2 := by
  have h1 : (a₁ * b₂ - a₂ * b₁).natAbs
      ≤ a₁.natAbs * b₂.natAbs + a₂.natAbs * b₁.natAbs := by
    calc (a₁ * b₂ - a₂ * b₁).natAbs
        ≤ (a₁ * b₂).natAbs + (a₂ * b₁).natAbs := Int.natAbs_sub_le _ _
      _ = a₁.natAbs * b₂.natAbs + a₂.natAbs * b₁.natAbs := by
          rw [Int.natAbs_mul, Int.natAbs_mul]
  have hterm1 : a₁.natAbs * b₂.natAbs
      ≤ max a₁.natAbs b₁.natAbs * max a₂.natAbs b₂.natAbs :=
    Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
  have hterm2 : a₂.natAbs * b₁.natAbs
      ≤ max a₁.natAbs b₁.natAbs * max a₂.natAbs b₂.natAbs := by
    calc a₂.natAbs * b₁.natAbs
        ≤ max a₂.natAbs b₂.natAbs * max a₁.natAbs b₁.natAbs :=
          Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
      _ = max a₁.natAbs b₁.natAbs * max a₂.natAbs b₂.natAbs := Nat.mul_comm _ _
  have h2 : (a₁ * b₂ - a₂ * b₁).natAbs
      ≤ 2 * (max a₁.natAbs b₁.natAbs * max a₂.natAbs b₂.natAbs) := by
    calc (a₁ * b₂ - a₂ * b₁).natAbs
        ≤ a₁.natAbs * b₂.natAbs + a₂.natAbs * b₁.natAbs := h1
      _ ≤ max a₁.natAbs b₁.natAbs * max a₂.natAbs b₂.natAbs
            + max a₁.natAbs b₁.natAbs * max a₂.natAbs b₂.natAbs :=
          Nat.add_le_add hterm1 hterm2
      _ = 2 * (max a₁.natAbs b₁.natAbs * max a₂.natAbs b₂.natAbs) := by ring
  calc (DD a₁ b₁ a₂ b₂).natAbs
      = (a₁ * b₂ - a₂ * b₁).natAbs ^ 2 := by
        simp only [DD]; rw [← Int.natAbs_pow]
    _ ≤ (2 * (max a₁.natAbs b₁.natAbs * max a₂.natAbs b₂.natAbs)) ^ 2 :=
        Nat.pow_le_pow_left h2 2
    _ = 4 * (max a₁.natAbs b₁.natAbs) ^ 2 * (max a₂.natAbs b₂.natAbs) ^ 2 := by
        ring

/-- `|Sf| ≤ 57·H₁²·H₂²` (coefficient sum `2+2+14+14+25 = 57`). -/
theorem Sf_upper (a₁ b₁ a₂ b₂ : ℤ) :
    (Sf a₁ b₁ a₂ b₂).natAbs
      ≤ 57 * (max a₁.natAbs b₁.natAbs) ^ 2 * (max a₂.natAbs b₂.natAbs) ^ 2 := by
  have hs : Sf a₁ b₁ a₂ b₂
      = 2 * a₁ ^ 2 * a₂ * b₂ + 2 * a₁ * a₂ ^ 2 * b₁ + (-14) * a₁ * b₁ * b₂ ^ 2
        + (-14) * a₂ * b₁ ^ 2 * b₂ + 25 * b₁ ^ 2 * b₂ ^ 2 := by
    simp only [Sf]; ring
  have tri : (Sf a₁ b₁ a₂ b₂).natAbs
      ≤ 2 * (a₁.natAbs ^ 2 * (a₂.natAbs ^ 1 * b₂.natAbs ^ 1))
        + 2 * (a₁.natAbs ^ 1 * b₁.natAbs ^ 1 * a₂.natAbs ^ 2)
        + 14 * (a₁.natAbs ^ 1 * b₁.natAbs ^ 1 * b₂.natAbs ^ 2)
        + 14 * (b₁.natAbs ^ 2 * (a₂.natAbs ^ 1 * b₂.natAbs ^ 1))
        + 25 * (b₁.natAbs ^ 2 * b₂.natAbs ^ 2) := by
    rw [hs]
    refine le_trans (natAbs_add5_le _ _ _ _ _) ?_
    simp only [Int.natAbs_mul, Int.natAbs_pow]
    norm_num
    ring_nf
    exact le_refl _
  have m1 := pair_bound a₁ b₁ a₂ b₂ 2 0 1 1 rfl rfl
  have m2 := pair_bound a₁ b₁ a₂ b₂ 1 1 2 0 rfl rfl
  have m3 := pair_bound a₁ b₁ a₂ b₂ 1 1 0 2 rfl rfl
  have m4 := pair_bound a₁ b₁ a₂ b₂ 0 2 1 1 rfl rfl
  have m5 := pair_bound a₁ b₁ a₂ b₂ 0 2 0 2 rfl rfl
  simp only [pow_zero, Nat.mul_one, Nat.one_mul] at m1 m2 m3 m4 m5
  linarith

/-- `|Pf| ≤ 114·H₁²·H₂²` (coefficient sum `1+14+25+25+49 = 114`). -/
theorem Pf_upper (a₁ b₁ a₂ b₂ : ℤ) :
    (Pf a₁ b₁ a₂ b₂).natAbs
      ≤ 114 * (max a₁.natAbs b₁.natAbs) ^ 2 * (max a₂.natAbs b₂.natAbs) ^ 2 := by
  have hs : Pf a₁ b₁ a₂ b₂
      = 1 * a₁ ^ 2 * a₂ ^ 2 + 14 * a₁ * a₂ * b₁ * b₂ + (-25) * a₁ * b₁ * b₂ ^ 2
        + (-25) * a₂ * b₁ ^ 2 * b₂ + 49 * b₁ ^ 2 * b₂ ^ 2 := by
    simp only [Pf]; ring
  have tri : (Pf a₁ b₁ a₂ b₂).natAbs
      ≤ 1 * (a₁.natAbs ^ 2 * a₂.natAbs ^ 2)
        + 14 * (a₁.natAbs ^ 1 * b₁.natAbs ^ 1 * (a₂.natAbs ^ 1 * b₂.natAbs ^ 1))
        + 25 * (a₁.natAbs ^ 1 * b₁.natAbs ^ 1 * b₂.natAbs ^ 2)
        + 25 * (b₁.natAbs ^ 2 * (a₂.natAbs ^ 1 * b₂.natAbs ^ 1))
        + 49 * (b₁.natAbs ^ 2 * b₂.natAbs ^ 2) := by
    rw [hs]
    refine le_trans (natAbs_add5_le _ _ _ _ _) ?_
    simp only [Int.natAbs_mul, Int.natAbs_pow]
    norm_num
    ring_nf
    exact le_refl _
  have m1 := pair_bound a₁ b₁ a₂ b₂ 2 0 2 0 rfl rfl
  have m2 := pair_bound a₁ b₁ a₂ b₂ 1 1 1 1 rfl rfl
  have m3 := pair_bound a₁ b₁ a₂ b₂ 1 1 0 2 rfl rfl
  have m4 := pair_bound a₁ b₁ a₂ b₂ 0 2 1 1 rfl rfl
  have m5 := pair_bound a₁ b₁ a₂ b₂ 0 2 0 2 rfl rfl
  simp only [pow_zero, Nat.mul_one, Nat.one_mul] at m1 m2 m3 m4 m5
  linarith

/-! ## §3 — the joint bound -/

/-- All three forms are bounded by `114·H₁²·H₂²`. -/
theorem forms_upper (a₁ b₁ a₂ b₂ : ℤ) :
    (DD a₁ b₁ a₂ b₂).natAbs
        ≤ 114 * (max a₁.natAbs b₁.natAbs) ^ 2 * (max a₂.natAbs b₂.natAbs) ^ 2 ∧
      (Sf a₁ b₁ a₂ b₂).natAbs
        ≤ 114 * (max a₁.natAbs b₁.natAbs) ^ 2 * (max a₂.natAbs b₂.natAbs) ^ 2 ∧
      (Pf a₁ b₁ a₂ b₂).natAbs
        ≤ 114 * (max a₁.natAbs b₁.natAbs) ^ 2 * (max a₂.natAbs b₂.natAbs) ^ 2 := by
  refine ⟨le_trans (DD_upper a₁ b₁ a₂ b₂) ?_,
          le_trans (Sf_upper a₁ b₁ a₂ b₂) ?_, Pf_upper a₁ b₁ a₂ b₂⟩
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))

end PrincipiaTractalis.QuasiParallelogramSize5077a1

#print axioms PrincipiaTractalis.QuasiParallelogramSize5077a1.DD_upper
#print axioms PrincipiaTractalis.QuasiParallelogramSize5077a1.Sf_upper
#print axioms PrincipiaTractalis.QuasiParallelogramSize5077a1.Pf_upper
#print axioms PrincipiaTractalis.QuasiParallelogramSize5077a1.forms_upper
