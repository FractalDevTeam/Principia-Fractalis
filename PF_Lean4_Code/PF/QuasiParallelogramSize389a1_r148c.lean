/-
# PF.QuasiParallelogramSize389a1_r148c

★★★ 2026-07-28 — r148c: SIZE UPPER BOUNDS FOR THE ADDITION FORMS ★★★

The triangle-inequality half of W2's size control: each bihomogeneous
addition form is bounded by its coefficient sum times `H₁²·H₂²`
(`Hᵢ = max |aᵢ| |bᵢ|`):

  `|DD| ≤ 4·H₁²H₂²`,  `|Sf| ≤ 17·H₁²H₂²`,  `|Pf| ≤ 10·H₁²H₂²`.

With r148b's content bound these give the upper half of
`naiveHeight(x₃)·naiveHeight(x₄) ≍ H₁²H₂²`; the lower half (via the
certificates) and the root bookkeeping complete r148.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.QuasiParallelogramCerts389a1_r148a
import Mathlib.Tactic.Linarith

namespace PrincipiaTractalis.QuasiParallelogramSize389a1

open PrincipiaTractalis.QuasiParallelogramCerts389a1

/-! ## §1 — bidegree-(2,·) monomial bounds -/

private theorem mono_sq (x y : ℤ) : x.natAbs ^ 2 ≤ (max x.natAbs y.natAbs) ^ 2 :=
  Nat.pow_le_pow_left (le_max_left _ _) 2

private theorem mono_sq' (x y : ℤ) : y.natAbs ^ 2 ≤ (max x.natAbs y.natAbs) ^ 2 :=
  Nat.pow_le_pow_left (le_max_right _ _) 2

private theorem mono_mix (x y : ℤ) :
    x.natAbs * y.natAbs ≤ (max x.natAbs y.natAbs) ^ 2 := by
  calc x.natAbs * y.natAbs
      ≤ max x.natAbs y.natAbs * max x.natAbs y.natAbs :=
        Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
    _ = (max x.natAbs y.natAbs) ^ 2 := by ring

/-! ## §2 — the form bounds -/

/-- `|DD(a₁,b₁,a₂,b₂)| ≤ 4·H₁²·H₂²`. -/
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

section FormBounds

variable (a₁ b₁ a₂ b₂ : ℤ)

private theorem pair_bound (i₁ j₁ i₂ j₂ : ℕ) (h₁ : i₁ + j₁ = 2) (h₂ : i₂ + j₂ = 2) :
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

end FormBounds

/-- `|Sf| ≤ 17·H₁²·H₂²` (coefficient sum `2+2+4+4+4+1 = 17`). -/
theorem Sf_upper (a₁ b₁ a₂ b₂ : ℤ) :
    (Sf a₁ b₁ a₂ b₂).natAbs
      ≤ 17 * (max a₁.natAbs b₁.natAbs) ^ 2 * (max a₂.natAbs b₂.natAbs) ^ 2 := by
  set H₁ := max a₁.natAbs b₁.natAbs
  set H₂ := max a₂.natAbs b₂.natAbs
  have m1 := pair_bound a₁ b₁ a₂ b₂ 2 0 1 1 rfl rfl
  have m2 := pair_bound a₁ b₁ a₂ b₂ 1 1 2 0 rfl rfl
  have m3 := pair_bound a₁ b₁ a₂ b₂ 1 1 1 1 rfl rfl
  have m4 := pair_bound a₁ b₁ a₂ b₂ 1 1 0 2 rfl rfl
  have m5 := pair_bound a₁ b₁ a₂ b₂ 0 2 1 1 rfl rfl
  have m6 := pair_bound a₁ b₁ a₂ b₂ 0 2 0 2 rfl rfl
  simp only [pow_zero, pow_one, Nat.mul_one, Nat.one_mul] at m1 m2 m3 m4 m5 m6
  have tri : (Sf a₁ b₁ a₂ b₂).natAbs
      ≤ 2 * (a₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs))
        + 2 * (a₁.natAbs * b₁.natAbs * a₂.natAbs ^ 2)
        + 4 * (a₁.natAbs * b₁.natAbs * (a₂.natAbs * b₂.natAbs))
        + 4 * (a₁.natAbs * b₁.natAbs * b₂.natAbs ^ 2)
        + 4 * (b₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs))
        + b₁.natAbs ^ 2 * b₂.natAbs ^ 2 := by
    simp only [Sf]
    calc (2 * a₁ ^ 2 * a₂ * b₂ + 2 * a₁ * a₂ ^ 2 * b₁ + 4 * a₁ * a₂ * b₁ * b₂
          - 4 * a₁ * b₁ * b₂ ^ 2 - 4 * a₂ * b₁ ^ 2 * b₂
          + b₁ ^ 2 * b₂ ^ 2).natAbs
        ≤ (2 * a₁ ^ 2 * a₂ * b₂ + 2 * a₁ * a₂ ^ 2 * b₁ + 4 * a₁ * a₂ * b₁ * b₂
            - 4 * a₁ * b₁ * b₂ ^ 2 - 4 * a₂ * b₁ ^ 2 * b₂).natAbs
          + (b₁ ^ 2 * b₂ ^ 2).natAbs := Int.natAbs_add_le _ _
      _ ≤ ((2 * a₁ ^ 2 * a₂ * b₂ + 2 * a₁ * a₂ ^ 2 * b₁
              + 4 * a₁ * a₂ * b₁ * b₂ - 4 * a₁ * b₁ * b₂ ^ 2).natAbs
            + ((4 : ℤ) * a₂ * b₁ ^ 2 * b₂).natAbs)
          + (b₁ ^ 2 * b₂ ^ 2).natAbs :=
          Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
      _ ≤ (((2 * a₁ ^ 2 * a₂ * b₂ + 2 * a₁ * a₂ ^ 2 * b₁
                + 4 * a₁ * a₂ * b₁ * b₂).natAbs
              + ((4 : ℤ) * a₁ * b₁ * b₂ ^ 2).natAbs)
            + ((4 : ℤ) * a₂ * b₁ ^ 2 * b₂).natAbs)
          + (b₁ ^ 2 * b₂ ^ 2).natAbs :=
          Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
      _ ≤ ((((2 * a₁ ^ 2 * a₂ * b₂ + 2 * a₁ * a₂ ^ 2 * b₁).natAbs
                + ((4 : ℤ) * a₁ * a₂ * b₁ * b₂).natAbs)
              + ((4 : ℤ) * a₁ * b₁ * b₂ ^ 2).natAbs)
            + ((4 : ℤ) * a₂ * b₁ ^ 2 * b₂).natAbs)
          + (b₁ ^ 2 * b₂ ^ 2).natAbs := by
          exact Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _) _
      _ ≤ (((((2 : ℤ) * a₁ ^ 2 * a₂ * b₂).natAbs
                  + ((2 : ℤ) * a₁ * a₂ ^ 2 * b₁).natAbs)
                + ((4 : ℤ) * a₁ * a₂ * b₁ * b₂).natAbs)
              + ((4 : ℤ) * a₁ * b₁ * b₂ ^ 2).natAbs)
            + ((4 : ℤ) * a₂ * b₁ ^ 2 * b₂).natAbs
          + (b₁ ^ 2 * b₂ ^ 2).natAbs := by
          exact Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.add_le_add_right (Nat.add_le_add_right
              (Int.natAbs_add_le _ _) _) _) _) _
      _ = 2 * (a₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs))
            + 2 * (a₁.natAbs * b₁.natAbs * a₂.natAbs ^ 2)
            + 4 * (a₁.natAbs * b₁.natAbs * (a₂.natAbs * b₂.natAbs))
            + 4 * (a₁.natAbs * b₁.natAbs * b₂.natAbs ^ 2)
            + 4 * (b₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs))
            + b₁.natAbs ^ 2 * b₂.natAbs ^ 2 := by
          simp only [Int.natAbs_mul, Int.natAbs_pow]
          ring
  calc (Sf a₁ b₁ a₂ b₂).natAbs
      ≤ 2 * (a₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs))
        + 2 * (a₁.natAbs * b₁.natAbs * a₂.natAbs ^ 2)
        + 4 * (a₁.natAbs * b₁.natAbs * (a₂.natAbs * b₂.natAbs))
        + 4 * (a₁.natAbs * b₁.natAbs * b₂.natAbs ^ 2)
        + 4 * (b₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs))
        + b₁.natAbs ^ 2 * b₂.natAbs ^ 2 := tri
    _ ≤ 2 * (H₁ ^ 2 * H₂ ^ 2) + 2 * (H₁ ^ 2 * H₂ ^ 2) + 4 * (H₁ ^ 2 * H₂ ^ 2)
        + 4 * (H₁ ^ 2 * H₂ ^ 2) + 4 * (H₁ ^ 2 * H₂ ^ 2) + H₁ ^ 2 * H₂ ^ 2 := by
        have e1 : a₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs) ≤ H₁ ^ 2 * H₂ ^ 2 := m1
        have e2 : a₁.natAbs * b₁.natAbs * a₂.natAbs ^ 2 ≤ H₁ ^ 2 * H₂ ^ 2 := m2
        have e3 : a₁.natAbs * b₁.natAbs * (a₂.natAbs * b₂.natAbs)
            ≤ H₁ ^ 2 * H₂ ^ 2 := m3
        have e4 : a₁.natAbs * b₁.natAbs * b₂.natAbs ^ 2 ≤ H₁ ^ 2 * H₂ ^ 2 := m4
        have e5 : b₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs) ≤ H₁ ^ 2 * H₂ ^ 2 := m5
        have e6 : b₁.natAbs ^ 2 * b₂.natAbs ^ 2 ≤ H₁ ^ 2 * H₂ ^ 2 := m6
        linarith
    _ = 17 * H₁ ^ 2 * H₂ ^ 2 := by ring

/-- `|Pf| ≤ 10·H₁²·H₂²` (coefficient sum `1+4+1+1+3 = 10`). -/
theorem Pf_upper (a₁ b₁ a₂ b₂ : ℤ) :
    (Pf a₁ b₁ a₂ b₂).natAbs
      ≤ 10 * (max a₁.natAbs b₁.natAbs) ^ 2 * (max a₂.natAbs b₂.natAbs) ^ 2 := by
  set H₁ := max a₁.natAbs b₁.natAbs
  set H₂ := max a₂.natAbs b₂.natAbs
  have m1 := pair_bound a₁ b₁ a₂ b₂ 2 0 2 0 rfl rfl
  have m2 := pair_bound a₁ b₁ a₂ b₂ 1 1 1 1 rfl rfl
  have m3 := pair_bound a₁ b₁ a₂ b₂ 1 1 0 2 rfl rfl
  have m4 := pair_bound a₁ b₁ a₂ b₂ 0 2 1 1 rfl rfl
  have m5 := pair_bound a₁ b₁ a₂ b₂ 0 2 0 2 rfl rfl
  simp only [pow_zero, pow_one, Nat.mul_one, Nat.one_mul] at m1 m2 m3 m4 m5
  have tri : (Pf a₁ b₁ a₂ b₂).natAbs
      ≤ a₁.natAbs ^ 2 * a₂.natAbs ^ 2
        + 4 * (a₁.natAbs * b₁.natAbs * (a₂.natAbs * b₂.natAbs))
        + a₁.natAbs * b₁.natAbs * b₂.natAbs ^ 2
        + b₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs)
        + 3 * (b₁.natAbs ^ 2 * b₂.natAbs ^ 2) := by
    simp only [Pf]
    calc (a₁ ^ 2 * a₂ ^ 2 + 4 * a₁ * a₂ * b₁ * b₂ - a₁ * b₁ * b₂ ^ 2
          - a₂ * b₁ ^ 2 * b₂ + 3 * b₁ ^ 2 * b₂ ^ 2).natAbs
        ≤ (a₁ ^ 2 * a₂ ^ 2 + 4 * a₁ * a₂ * b₁ * b₂ - a₁ * b₁ * b₂ ^ 2
            - a₂ * b₁ ^ 2 * b₂).natAbs + ((3 : ℤ) * b₁ ^ 2 * b₂ ^ 2).natAbs :=
          Int.natAbs_add_le _ _
      _ ≤ ((a₁ ^ 2 * a₂ ^ 2 + 4 * a₁ * a₂ * b₁ * b₂
              - a₁ * b₁ * b₂ ^ 2).natAbs + (a₂ * b₁ ^ 2 * b₂).natAbs)
          + ((3 : ℤ) * b₁ ^ 2 * b₂ ^ 2).natAbs :=
          Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
      _ ≤ (((a₁ ^ 2 * a₂ ^ 2 + 4 * a₁ * a₂ * b₁ * b₂).natAbs
                + (a₁ * b₁ * b₂ ^ 2).natAbs)
              + (a₂ * b₁ ^ 2 * b₂).natAbs)
          + ((3 : ℤ) * b₁ ^ 2 * b₂ ^ 2).natAbs :=
          Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
      _ ≤ ((((a₁ ^ 2 * a₂ ^ 2).natAbs + ((4 : ℤ) * a₁ * a₂ * b₁ * b₂).natAbs)
                + (a₁ * b₁ * b₂ ^ 2).natAbs)
              + (a₂ * b₁ ^ 2 * b₂).natAbs)
          + ((3 : ℤ) * b₁ ^ 2 * b₂ ^ 2).natAbs :=
          Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _) _
      _ = a₁.natAbs ^ 2 * a₂.natAbs ^ 2
            + 4 * (a₁.natAbs * b₁.natAbs * (a₂.natAbs * b₂.natAbs))
            + a₁.natAbs * b₁.natAbs * b₂.natAbs ^ 2
            + b₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs)
            + 3 * (b₁.natAbs ^ 2 * b₂.natAbs ^ 2) := by
          simp only [Int.natAbs_mul, Int.natAbs_pow]
          ring
  calc (Pf a₁ b₁ a₂ b₂).natAbs
      ≤ a₁.natAbs ^ 2 * a₂.natAbs ^ 2
        + 4 * (a₁.natAbs * b₁.natAbs * (a₂.natAbs * b₂.natAbs))
        + a₁.natAbs * b₁.natAbs * b₂.natAbs ^ 2
        + b₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs)
        + 3 * (b₁.natAbs ^ 2 * b₂.natAbs ^ 2) := tri
    _ ≤ H₁ ^ 2 * H₂ ^ 2 + 4 * (H₁ ^ 2 * H₂ ^ 2) + H₁ ^ 2 * H₂ ^ 2
        + H₁ ^ 2 * H₂ ^ 2 + 3 * (H₁ ^ 2 * H₂ ^ 2) := by
        have e1 : a₁.natAbs ^ 2 * a₂.natAbs ^ 2 ≤ H₁ ^ 2 * H₂ ^ 2 := m1
        have e2 : a₁.natAbs * b₁.natAbs * (a₂.natAbs * b₂.natAbs)
            ≤ H₁ ^ 2 * H₂ ^ 2 := m2
        have e3 : a₁.natAbs * b₁.natAbs * b₂.natAbs ^ 2 ≤ H₁ ^ 2 * H₂ ^ 2 := m3
        have e4 : b₁.natAbs ^ 2 * (a₂.natAbs * b₂.natAbs) ≤ H₁ ^ 2 * H₂ ^ 2 := m4
        have e5 : b₁.natAbs ^ 2 * b₂.natAbs ^ 2 ≤ H₁ ^ 2 * H₂ ^ 2 := m5
        linarith
    _ = 10 * H₁ ^ 2 * H₂ ^ 2 := by ring

end PrincipiaTractalis.QuasiParallelogramSize389a1

#print axioms PrincipiaTractalis.QuasiParallelogramSize389a1.DD_upper
#print axioms PrincipiaTractalis.QuasiParallelogramSize389a1.Sf_upper
#print axioms PrincipiaTractalis.QuasiParallelogramSize389a1.Pf_upper
