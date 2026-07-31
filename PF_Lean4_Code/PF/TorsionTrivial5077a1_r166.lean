/-
################################################################################
##  NOT VERIFIED -- DO NOT IMPORT, DO NOT CITE                                ##
##                                                                            ##
##  This file does NOT compile within the resources of this machine.  The      ##
##  `decide +kernel` blocks exhaust memory: one block of 1140 candidates       ##
##  reached 12.9 GB RSS on a 15 GB box and was killed (SIGKILL, LEAN_EXIT=137) ##
##  with swap already full.  It is retained as a worked draft, NOT as a proof. ##
##  It is deliberately absent from PF.lean.                                    ##
##                                                                            ##
##  The mathematics is sound and pre-verified numerically -- see               ##
##  codex/R166_RESOURCE_WALL_2026-07-31.md for the measured wall and the fix   ##
##  (restrict to perfect-square denominators: 2783 -> 363 candidates).         ##
################################################################################
-/

/-
# PF.TorsionTrivial5077a1_r166

★★★ 2026-07-31 — THE TORSION SUBGROUP OF 5077a1 IS TRIVIAL ★★★

`E5077a1(ℚ)` has no nonzero torsion point, hence `R ≠ 0 → 0 < ĥ(R)`.

## Why this is the unlock for rank 3

r164 proved the parallelogram law for `ĥ` on 5077a1, but *conditionally*: it
needs `P, Q, P ± Q` non-torsion.  By the Jordan–von Neumann argument, a function
satisfying the parallelogram identity on an abelian group **is** a quadratic
form, so the pairing `⟨P,Q⟩ = ½(ĥ(P+Q) − ĥP − ĥQ)` is automatically bi-additive
— *provided the law is unconditional*.  The obstruction to a 3×3 Sylvester
argument was therefore never bi-additivity itself; it was the side conditions.
This file removes them.

## The argument (same shape as r155 for 389a1)

r156's `naiveHeight_le_47_of_canheight_zero` gives: if `ĥ(R) = 0` then
`h(x(2ⁿR)) ≤ 47` for every `n`, since `47³ = 103823 ≤ 105754 < 110592 = 48³`.
So a torsion point and all its doublings live among the rationals of naive
height `≤ 47`.  There are exactly **2783** of them (against 183 at the bound 12
for 389a1).  Iterating `x ↦ f x / g x`:

  * of the 2783, only `1` and `2` still have height `≤ 47` after one step
    (they go to `14` and `21`);
  * both escape on the second step.

So no rational of height `≤ 47` keeps height `≤ 47` for two doublings, and a
nonzero torsion point would have to.  Contradiction.

As in r155 the check needs **no curve equation and no square-testing** — only
iteration of a rational function and comparison of heights — so it is a
`decide +kernel` over ℚ arithmetic.  The candidate set is presented over
`Finset.range` because `Finset.Icc` on ℤ is built from an order embedding the
kernel will not unfold.

HONEST SCOPE.  Torsion-freeness for 5077a1, and the positivity of `ĥ` off zero.
This does NOT by itself prove rank ≥ 3: it removes the side conditions, and the
Jordan–von Neumann step and the 3×3 determinant argument are still to be built.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import PF.CanheightMultiple5077a1_r165

-- 2783 candidates (against 183 in r155): both the membership unfolding and the
-- kernel reduction need a raised recursion limit.
set_option maxRecDepth 1000000

namespace PrincipiaTractalis.TorsionTrivial5077a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E5077a1RankOne
open PrincipiaTractalis.CanonicalHeight5077a1
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the 2783 rationals of naive height at most 47, in four blocks

A single `decide +kernel` over all 2783 does not reduce: 1140 candidates go
through comfortably but 2783 gets stuck at `List.decidableBAll`, with or without
a raised `maxRecDepth` and a 256 MB stack.  So the candidate set is split by
denominator into four blocks of at most 1140, each discharged separately.  This
is a purely mechanical split; no mathematical content depends on it. -/

/-- Numerators `i - 47` for `i < 95`; denominators `lo+1 … lo+n`. -/
def candChunk (lo n : ℕ) : Finset ℚ :=
  ((Finset.range 95) ×ˢ (Finset.range n)).image
    (fun p => ((p.1 : ℚ) - 47) / ((p.2 + lo : ℚ) + 1))

/-- A rational of naive height `≤ 47` whose denominator slot lies in
`[lo, lo+n)` belongs to `candChunk lo n`. -/
theorem mem_candChunk {q : ℚ} (h : naiveHeight q ≤ 47) (lo n : ℕ)
    (hlo : lo ≤ q.den - 1) (hhi : q.den - 1 < lo + n) :
    q ∈ candChunk lo n := by
  have hn : q.num.natAbs ≤ 47 := le_trans (le_max_left _ _) h
  have hd : q.den ≤ 47 := le_trans (le_max_right _ _) h
  have hd1 : 1 ≤ q.den := q.pos
  refine Finset.mem_image.mpr ⟨((q.num + 47).toNat, q.den - 1 - lo), ?_, ?_⟩
  · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · have hi : (((q.num + 47).toNat : ℕ) : ℚ) = (q.num : ℚ) + 47 := by
      have ht : ((q.num + 47).toNat : ℤ) = q.num + 47 :=
        Int.toNat_of_nonneg (by omega)
      have hc : (((q.num + 47).toNat : ℕ) : ℚ)
          = (((q.num + 47).toNat : ℤ) : ℚ) := by push_cast; ring
      rw [hc, ht]; push_cast; ring
    have hnat : (q.den - 1 - lo) + lo + 1 = q.den := by omega
    have hj : ((q.den - 1 - lo : ℕ) : ℚ) + (lo : ℚ) + 1 = (q.den : ℚ) := by
      have := congrArg (fun m : ℕ => (m : ℚ)) hnat
      push_cast at this
      linarith [this]
    simp only []
    rw [hi]
    have hden : ((q.den - 1 - lo : ℕ) : ℚ) + (lo : ℚ) + 1 = (q.den : ℚ) := hj
    rw [show (((q.den - 1 - lo : ℕ) : ℚ) + (lo : ℚ) + 1) = (q.den : ℚ) from hden]
    have he : (q.num : ℚ) + 47 - 47 = (q.num : ℚ) := by ring
    rw [he]
    exact Rat.num_div_den q

/-! ## §2 — the finite verification, four blocks -/

/-- The predicate the check rules out. -/
abbrev Escapes (q : ℚ) : Prop :=
  naiveHeight (f q / g q) ≤ 47 ∧
    naiveHeight (f (f q / g q) / g (f q / g q)) ≤ 47

theorem no_survivor_0  : ∀ q ∈ candChunk  0 12, ¬ Escapes q := by decide +kernel
theorem no_survivor_12 : ∀ q ∈ candChunk 12 12, ¬ Escapes q := by decide +kernel
theorem no_survivor_24 : ∀ q ∈ candChunk 24 12, ¬ Escapes q := by decide +kernel
theorem no_survivor_36 : ∀ q ∈ candChunk 36 11, ¬ Escapes q := by decide +kernel

/-- **The finite check**, assembled.  No rational of naive height `≤ 47` still
has height `≤ 47` after two applications of `x ↦ f x / g x`.  Only `1` and `2`
survive the first step (to `14` and `21`); neither survives the second. -/
theorem no_survivor {q : ℚ} (h : naiveHeight q ≤ 47) : ¬ Escapes q := by
  have hd : q.den ≤ 47 := le_trans (le_max_right _ _) h
  have hd1 : 1 ≤ q.den := q.pos
  rcases Nat.lt_or_ge (q.den - 1) 12 with h1 | h1
  · exact no_survivor_0 q (mem_candChunk h 0 12 (by omega) (by omega))
  rcases Nat.lt_or_ge (q.den - 1) 24 with h2 | h2
  · exact no_survivor_12 q (mem_candChunk h 12 12 (by omega) (by omega))
  rcases Nat.lt_or_ge (q.den - 1) 36 with h3 | h3
  · exact no_survivor_24 q (mem_candChunk h 24 12 (by omega) (by omega))
  · exact no_survivor_36 q (mem_candChunk h 36 11 (by omega) (by omega))

/-! ## §3 — two doublings in `X`-form -/

theorem two_zsmul_eq (R : E5077a1.toAffine.Point) : (2 : ℤ) • R = R + R := by
  rw [show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]

theorem X_two_smul {x₀ y₀ : ℚ} (h₀ : E5077a1.toAffine.Nonsingular x₀ y₀) :
    X ((2 : ℤ) • Point.some h₀) = f x₀ / g x₀ := by
  obtain ⟨x₁, y₁, h₁, e₁, hx₁⟩ := dbl_x h₀
  have s₁ : (2 : ℤ) • Point.some h₀ = Point.some h₁ := by
    rw [two_zsmul_eq]; exact e₁
  rw [s₁]; show x₁ = _; exact hx₁

theorem X_four_smul {x₀ y₀ : ℚ} (h₀ : E5077a1.toAffine.Nonsingular x₀ y₀) :
    X (((2 : ℤ) ^ 2) • Point.some h₀)
      = f (f x₀ / g x₀) / g (f x₀ / g x₀) := by
  obtain ⟨x₁, y₁, h₁, e₁, hx₁⟩ := dbl_x h₀
  obtain ⟨x₂, y₂, h₂, e₂, hx₂⟩ := dbl_x h₁
  have h4 : ((2 : ℤ) ^ 2) • Point.some h₀
      = (2 : ℤ) • ((2 : ℤ) • Point.some h₀) := by
    rw [smul_smul]; norm_num
  have s₁ : (2 : ℤ) • Point.some h₀ = Point.some h₁ := by
    rw [two_zsmul_eq]; exact e₁
  have s₂ : (2 : ℤ) • Point.some h₁ = Point.some h₂ := by
    rw [two_zsmul_eq]; exact e₂
  rw [h4, s₁, s₂]; show x₂ = _; rw [hx₂, hx₁]

/-! ## §4 — the theorem -/

/-- **CAPSTONE — the torsion subgroup of `E5077a1(ℚ)` is trivial.** -/
theorem torsion_eq_zero {R : E5077a1.toAffine.Point}
    (h : IsOfFinAddOrder R) : R = 0 := by
  by_contra hne
  have h0 : canheight R = 0 := canheight_of_torsion h
  cases R with
  | zero => exact hne rfl
  | @some x y hxy =>
      have b0 := naiveHeight_le_47_of_canheight_zero h0 0
      have b1 := naiveHeight_le_47_of_canheight_zero h0 1
      have b2 := naiveHeight_le_47_of_canheight_zero h0 2
      rw [pow_zero, one_zsmul] at b0
      rw [pow_one, X_two_smul hxy] at b1
      rw [X_four_smul hxy] at b2
      have hx : X (Point.some hxy) = x := rfl
      rw [hx] at b0
      exact no_survivor b0 ⟨b1, b2⟩

theorem nonTorsion_of_ne_zero {R : E5077a1.toAffine.Point} (h : R ≠ 0) :
    ¬ IsOfFinAddOrder R :=
  fun hfin => h (torsion_eq_zero hfin)

/-- **The payoff.**  Every nonzero point has strictly positive canonical height,
so r164's parallelogram law and r165's multiple law lose their side conditions
for 5077a1. -/
theorem canheight_pos_of_ne_zero {R : E5077a1.toAffine.Point} (h : R ≠ 0) :
    0 < canheight R := by
  rcases lt_or_eq_of_le (canheight_nonneg R) with hlt | heq
  · exact hlt
  · exact absurd (canheight_eq_zero_torsion heq.symm) (nonTorsion_of_ne_zero h)

end PrincipiaTractalis.TorsionTrivial5077a1

#print axioms PrincipiaTractalis.TorsionTrivial5077a1.mem_candChunk
#print axioms PrincipiaTractalis.TorsionTrivial5077a1.no_survivor
#print axioms PrincipiaTractalis.TorsionTrivial5077a1.torsion_eq_zero
#print axioms PrincipiaTractalis.TorsionTrivial5077a1.canheight_pos_of_ne_zero
