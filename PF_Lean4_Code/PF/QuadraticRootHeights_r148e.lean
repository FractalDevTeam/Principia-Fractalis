/-
# PF.QuadraticRootHeights_r148e

★★★ 2026-07-28 — r148e: HEIGHTS OF THE ROOTS OF AN INTEGER QUADRATIC ★★★

A general, curve-independent height lemma — the last piece of genuinely new
mathematics in the independence arc:

  if `x₃, x₄ : ℚ` satisfy `A(x₃+x₄) = B` and `A·x₃x₄ = C` for integers
  `A ≠ 0, B, C`, then

      `naiveHeight x₃ · naiveHeight x₄ ≤ 2 · max(|A|, |B|, |C|)`.

Two ingredients, both elementary and both proved here from scratch:

* **`den_mul_den_dvd`** — the denominators multiply into `A`:
  `x₃.den · x₄.den ∣ A`.  Proof avoids all prime/gcd reasoning: the
  rational-root theorem gives `v₃ ∣ A`; writing `A = v₃·m`, the sum and
  product relations give `v₄ ∣ m·u₃` and `v₄ ∣ m·v₃`, and a Bézout
  combination for `IsCoprime u₃ v₃` yields `v₄ ∣ m`.
* **`four_term_bound`** — `max(|u₃|,v₃)·max(|u₄|,v₄) ≤ 2·max(v₃v₄, |B'|, |u₃u₄|)`
  where `B' = u₃v₄ + u₄v₃`.  The two diagonal products are outright ≤ max;
  for the cross terms `s = |u₃|v₄`, `t = v₃|u₄|`: `s·t ≤ M²` forces
  `min(s,t) ≤ M`, while `|s − t| ≤ |B'| ≤ M`, so `max(s,t) ≤ 2M`.

Applied to `(A,B,C) = (DD, Sf, Pf)` from r148d this gives the upper half of
the quasi-parallelogram inequality; the lower half then follows *for free*
from the duplication bound applied to the pair `(P+Q, P−Q)` (whose sum and
difference are `2P` and `2Q`) — no further certificates needed.

HONEST SCOPE.  A statement about rational numbers and integers only.  No
elliptic curve appears; no height inequality on a curve is claimed here.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.NaiveHeightQ_r130
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

namespace PrincipiaTractalis.QuadraticRootHeights

open PrincipiaTractalis.NaiveHeightQ

/-! ## §1 — coprimality of a rational's numerator and denominator -/

theorem isCoprime_num_den (q : ℚ) : IsCoprime q.num ((q.den : ℤ)) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  simpa [Int.gcd, Int.natAbs_natCast] using q.reduced

theorem den_pos_int (q : ℚ) : (0 : ℤ) < (q.den : ℤ) := by
  exact_mod_cast q.pos

theorem den_ne_zero_int (q : ℚ) : ((q.den : ℤ)) ≠ 0 :=
  ne_of_gt (den_pos_int q)

/-! ## §2 — the three integer relations -/

section Relations

variable {x₃ x₄ : ℚ} {A B C : ℤ}

/-- Sum relation, cleared: `A(u₃v₄ + u₄v₃) = B·v₃v₄`. -/
theorem sum_rel (hs : (A : ℚ) * (x₃ + x₄) = (B : ℚ)) :
    A * (x₃.num * (x₄.den : ℤ) + x₄.num * (x₃.den : ℤ))
      = B * ((x₃.den : ℤ) * (x₄.den : ℤ)) := by
  have hd₃ : ((x₃.den : ℚ)) ≠ 0 := by
    exact_mod_cast x₃.den_ne_zero
  have hn₃ : (x₃.num : ℚ) = x₃ * (x₃.den : ℚ) :=
    (div_eq_iff hd₃).mp (Rat.num_div_den x₃)
  have hd₄ : ((x₄.den : ℚ)) ≠ 0 := by
    exact_mod_cast x₄.den_ne_zero
  have hn₄ : (x₄.num : ℚ) = x₄ * (x₄.den : ℚ) :=
    (div_eq_iff hd₄).mp (Rat.num_div_den x₄)
  have : (A : ℚ) * ((x₃.num : ℚ) * (x₄.den : ℚ) + (x₄.num : ℚ) * (x₃.den : ℚ))
      = (B : ℚ) * ((x₃.den : ℚ) * (x₄.den : ℚ)) := by
    rw [hn₃, hn₄]
    linear_combination ((x₃.den : ℚ) * (x₄.den : ℚ)) * hs
  exact_mod_cast this

/-- Product relation, cleared: `A·u₃u₄ = C·v₃v₄`. -/
theorem prod_rel (hp : (A : ℚ) * (x₃ * x₄) = (C : ℚ)) :
    A * (x₃.num * x₄.num) = C * ((x₃.den : ℤ) * (x₄.den : ℤ)) := by
  have hd₃ : ((x₃.den : ℚ)) ≠ 0 := by
    exact_mod_cast x₃.den_ne_zero
  have hn₃ : (x₃.num : ℚ) = x₃ * (x₃.den : ℚ) :=
    (div_eq_iff hd₃).mp (Rat.num_div_den x₃)
  have hd₄ : ((x₄.den : ℚ)) ≠ 0 := by
    exact_mod_cast x₄.den_ne_zero
  have hn₄ : (x₄.num : ℚ) = x₄ * (x₄.den : ℚ) :=
    (div_eq_iff hd₄).mp (Rat.num_div_den x₄)
  have : (A : ℚ) * ((x₃.num : ℚ) * (x₄.num : ℚ))
      = (C : ℚ) * ((x₃.den : ℚ) * (x₄.den : ℚ)) := by
    rw [hn₃, hn₄]
    linear_combination ((x₃.den : ℚ) * (x₄.den : ℚ)) * hp
  exact_mod_cast this

/-- Each root satisfies the integer quadratic: `A·u² − B·u·v + C·v² = 0`. -/
theorem quadratic_rel (hs : (A : ℚ) * (x₃ + x₄) = (B : ℚ))
    (hp : (A : ℚ) * (x₃ * x₄) = (C : ℚ)) :
    A * x₃.num ^ 2 - B * (x₃.num * (x₃.den : ℤ)) + C * (x₃.den : ℤ) ^ 2 = 0 := by
  have hd₃ : ((x₃.den : ℚ)) ≠ 0 := by
    exact_mod_cast x₃.den_ne_zero
  have hn₃ : (x₃.num : ℚ) = x₃ * (x₃.den : ℚ) :=
    (div_eq_iff hd₃).mp (Rat.num_div_den x₃)
  -- A x₃² − B x₃ + C = A(x₃ − x₃)(x₃ − x₄) = 0
  have hq : (A : ℚ) * x₃ ^ 2 - (B : ℚ) * x₃ + (C : ℚ) = 0 := by
    have h : (A : ℚ) * x₃ ^ 2 - (B : ℚ) * x₃ + (C : ℚ)
        = (A : ℚ) * x₃ ^ 2 - ((A : ℚ) * (x₃ + x₄)) * x₃
          + (A : ℚ) * (x₃ * x₄) := by rw [hs, hp]
    rw [h]; ring
  have : (A : ℚ) * (x₃.num : ℚ) ^ 2 - (B : ℚ) * ((x₃.num : ℚ) * (x₃.den : ℚ))
      + (C : ℚ) * (x₃.den : ℚ) ^ 2 = 0 := by
    rw [hn₃]
    linear_combination ((x₃.den : ℚ) ^ 2) * hq
  exact_mod_cast this

end Relations

/-! ## §3 — the denominators multiply into `A` -/

/-- **Rational-root step.**  `x₃.den ∣ A`. -/
theorem den_dvd {x₃ x₄ : ℚ} {A B C : ℤ}
    (hs : (A : ℚ) * (x₃ + x₄) = (B : ℚ))
    (hp : (A : ℚ) * (x₃ * x₄) = (C : ℚ)) :
    ((x₃.den : ℤ)) ∣ A := by
  have hq := quadratic_rel hs hp
  have hdvd : ((x₃.den : ℤ)) ∣ A * x₃.num ^ 2 := by
    refine ⟨B * x₃.num - C * (x₃.den : ℤ), ?_⟩
    linear_combination hq
  have hcop : IsCoprime ((x₃.den : ℤ)) (x₃.num ^ 2) :=
    ((isCoprime_num_den x₃).symm).pow_right
  exact hcop.dvd_of_dvd_mul_right hdvd

/-- **★ The denominator product divides `A`.**  `x₃.den · x₄.den ∣ A`.
No prime or gcd reasoning: only the rational-root step, cancellation, and a
Bézout combination for `IsCoprime x₃.num x₃.den`.
(`_hA` is carried for interface symmetry; the proof does not need it.) -/
theorem den_mul_den_dvd {x₃ x₄ : ℚ} {A B C : ℤ} (_hA : A ≠ 0)
    (hs : (A : ℚ) * (x₃ + x₄) = (B : ℚ))
    (hp : (A : ℚ) * (x₃ * x₄) = (C : ℚ)) :
    ((x₃.den : ℤ)) * ((x₄.den : ℤ)) ∣ A := by
  set u₃ := x₃.num with hu₃
  set v₃ := ((x₃.den : ℤ)) with hv₃
  set u₄ := x₄.num with hu₄
  set v₄ := ((x₄.den : ℤ)) with hv₄
  have hv₃0 : v₃ ≠ 0 := den_ne_zero_int x₃
  obtain ⟨m, hm⟩ := den_dvd hs hp        -- A = v₃ * m
  -- product relation, with A = v₃ m and v₃ cancelled: m·u₃u₄ = C·v₄
  have hP := prod_rel hp                  -- A(u₃u₄) = C(v₃v₄)
  have hPm : m * (u₃ * u₄) = C * v₄ := by
    have h : v₃ * (m * (u₃ * u₄)) = v₃ * (C * v₄) := by
      rw [hm] at hP; linear_combination hP
    exact mul_left_cancel₀ hv₃0 h
  -- sum relation, same cancellation: m(u₃v₄ + u₄v₃) = B·v₄
  have hS := sum_rel hs                   -- A(u₃v₄+u₄v₃) = B(v₃v₄)
  have hSm : m * (u₃ * v₄ + u₄ * v₃) = B * v₄ := by
    have h : v₃ * (m * (u₃ * v₄ + u₄ * v₃)) = v₃ * (B * v₄) := by
      rw [hm] at hS; linear_combination hS
    exact mul_left_cancel₀ hv₃0 h
  -- v₄ ∣ m·u₃ : from hPm, v₄ ∣ m u₃ u₄, and IsCoprime v₄ u₄
  have hcop₄ : IsCoprime v₄ u₄ := (isCoprime_num_den x₄).symm
  have hmu₃ : v₄ ∣ m * u₃ := by
    have h1 : v₄ ∣ (m * u₃) * u₄ := ⟨C, by linear_combination hPm⟩
    exact hcop₄.dvd_of_dvd_mul_right h1
  -- v₄ ∣ m·v₃ : from hSm minus the v₄-divisible part, then IsCoprime v₄ u₄
  have hmv₃ : v₄ ∣ m * v₃ := by
    have h1 : v₄ ∣ (m * v₃) * u₄ := ⟨B - m * u₃, by linear_combination hSm⟩
    exact hcop₄.dvd_of_dvd_mul_right h1
  -- Bézout on IsCoprime u₃ v₃ : m = s(m u₃) + t(m v₃)
  obtain ⟨s, t, hst⟩ := isCoprime_num_den x₃
  have hvm : v₄ ∣ m := by
    have key : m = s * (m * u₃) + t * (m * v₃) := by
      linear_combination (-m : ℤ) * hst
    rw [key]
    exact dvd_add (hmu₃.mul_left s) (hmv₃.mul_left t)
  obtain ⟨n, hn⟩ := hvm
  exact ⟨n, by rw [hm, hn]; ring⟩

/-! ## §4 — the four-term max inequality -/

section FourTerm

/-- If `s·t ≤ M²` in `ℕ` then `min s t ≤ M`. -/
private theorem min_le_of_mul_le_sq {s t M : ℕ} (h : s * t ≤ M * M) :
    min s t ≤ M := by
  by_contra hc
  push_neg at hc
  have hs : M < s := lt_of_lt_of_le hc (min_le_left _ _)
  have ht : M < t := lt_of_lt_of_le hc (min_le_right _ _)
  have : M * M < s * t := Nat.mul_lt_mul_of_lt_of_le hs (le_of_lt ht) (by omega)
  omega

/-- **The four-term bound.**  With `s = p₃q₄`, `t = q₃p₄` and
`M = max(q₃q₄, b, p₃p₄)` where `b ≥ |s − t|`:
`max p₃ q₃ · max p₄ q₄ ≤ 2M`. -/
theorem four_term_bound {p₃ q₃ p₄ q₄ b : ℕ}
    (hb : max (p₃ * q₄) (q₃ * p₄) - min (p₃ * q₄) (q₃ * p₄) ≤ b) :
    max p₃ q₃ * max p₄ q₄
      ≤ 2 * max (max (q₃ * q₄) b) (p₃ * p₄) := by
  set M := max (max (q₃ * q₄) b) (p₃ * p₄) with hM
  have hqq : q₃ * q₄ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hbM : b ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hpp : p₃ * p₄ ≤ M := le_max_right _ _
  -- the two cross terms
  have hcross : max (p₃ * q₄) (q₃ * p₄) ≤ 2 * M := by
    have hst : (p₃ * q₄) * (q₃ * p₄) ≤ M * M := by
      calc (p₃ * q₄) * (q₃ * p₄) = (p₃ * p₄) * (q₃ * q₄) := by ring
        _ ≤ M * M := Nat.mul_le_mul hpp hqq
    have hmin : min (p₃ * q₄) (q₃ * p₄) ≤ M := min_le_of_mul_le_sq hst
    have hdiff : max (p₃ * q₄) (q₃ * p₄) - min (p₃ * q₄) (q₃ * p₄) ≤ M :=
      le_trans hb hbM
    have hmm : min (p₃ * q₄) (q₃ * p₄) ≤ max (p₃ * q₄) (q₃ * p₄) :=
      min_le_max
    omega
  rcases le_total p₃ q₃ with h₃ | h₃ <;> rcases le_total p₄ q₄ with h₄ | h₄
  · rw [max_eq_right h₃, max_eq_right h₄]; omega
  · rw [max_eq_right h₃, max_eq_left h₄]
    exact le_trans (le_max_right _ _) hcross
  · rw [max_eq_left h₃, max_eq_right h₄]
    exact le_trans (le_max_left _ _) hcross
  · rw [max_eq_left h₃, max_eq_left h₄]; omega

end FourTerm

/-! ## §5 — the capstone -/

/-- **★★★ r148e — HEIGHTS OF THE ROOTS OF AN INTEGER QUADRATIC ★★★**

If `x₃, x₄ : ℚ` are the two roots of `A·T² − B·T + C` (`A ≠ 0`, integer
coefficients), then

  `naiveHeight x₃ · naiveHeight x₄ ≤ 2 · max(|A|, |B|, |C|)`.

Curve-independent.  Applied to r148d's addition quadratic
`(A,B,C) = (DD, Sf, Pf)` with r148c's size bounds, this is the upper half
of the quasi-parallelogram inequality. -/
theorem naiveHeight_mul_le_of_quadratic {x₃ x₄ : ℚ} {A B C : ℤ} (hA : A ≠ 0)
    (hs : (A : ℚ) * (x₃ + x₄) = (B : ℚ))
    (hp : (A : ℚ) * (x₃ * x₄) = (C : ℚ)) :
    naiveHeight x₃ * naiveHeight x₄
      ≤ 2 * max (max A.natAbs B.natAbs) C.natAbs := by
  set u₃ := x₃.num
  set v₃ := ((x₃.den : ℤ))
  set u₄ := x₄.num
  set v₄ := ((x₄.den : ℤ))
  -- the primitive coefficients
  set A' := v₃ * v₄ with hA'
  set B' := u₃ * v₄ + u₄ * v₃ with hB'
  set C' := u₃ * u₄ with hC'
  have hv₃0 : v₃ ≠ 0 := den_ne_zero_int x₃
  have hv₄0 : v₄ ≠ 0 := den_ne_zero_int x₄
  have hA'0 : A' ≠ 0 := mul_ne_zero hv₃0 hv₄0
  -- A = k·A', and then B = k·B', C = k·C'
  obtain ⟨k, hk⟩ := den_mul_den_dvd hA hs hp
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hk; exact hA hk
  have hBk : B = k * B' := by
    have hS := sum_rel hs
    have h : A' * (k * B') = A' * B := by rw [hk] at hS; linear_combination hS
    exact (mul_left_cancel₀ hA'0 h).symm
  have hCk : C = k * C' := by
    have hP := prod_rel hp
    have h : A' * (k * C') = A' * C := by rw [hk] at hP; linear_combination hP
    exact (mul_left_cancel₀ hA'0 h).symm
  -- so the primitive coefficients are dominated
  have h1k : 1 ≤ k.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hk0)
  have hAle : A'.natAbs ≤ A.natAbs := by
    have e : A.natAbs = A'.natAbs * k.natAbs := by
      rw [hA', hk, Int.natAbs_mul]
    rw [e]
    exact Nat.le_mul_of_pos_right _ h1k
  have hBle : B'.natAbs ≤ B.natAbs := by
    have e : B.natAbs = k.natAbs * B'.natAbs := by
      rw [hBk, Int.natAbs_mul]
    rw [e]
    exact Nat.le_mul_of_pos_left _ h1k
  have hCle : C'.natAbs ≤ C.natAbs := by
    have e : C.natAbs = k.natAbs * C'.natAbs := by
      rw [hCk, Int.natAbs_mul]
    rw [e]
    exact Nat.le_mul_of_pos_left _ h1k
  -- the four-term bound at the primitive level
  set p₃ := u₃.natAbs
  set q₃ := x₃.den
  set p₄ := u₄.natAbs
  set q₄ := x₄.den
  have hq₃ : v₃.natAbs = q₃ := Int.natAbs_natCast _
  have hq₄ : v₄.natAbs = q₄ := Int.natAbs_natCast _
  have hAn : A'.natAbs = q₃ * q₄ := by
    rw [hA', Int.natAbs_mul, hq₃, hq₄]
  have hCn : C'.natAbs = p₃ * p₄ := by rw [hC', Int.natAbs_mul]
  -- |B'| dominates the difference of the cross terms
  have hdiff : max (p₃ * q₄) (q₃ * p₄) - min (p₃ * q₄) (q₃ * p₄) ≤ B'.natAbs := by
    have e1 : (u₃ * v₄).natAbs = p₃ * q₄ := by rw [Int.natAbs_mul, hq₄]
    have e2 : (u₄ * v₃).natAbs = p₄ * q₃ := by rw [Int.natAbs_mul, hq₃]
    have habs : max (u₃ * v₄).natAbs (u₄ * v₃).natAbs
        - min (u₃ * v₄).natAbs (u₄ * v₃).natAbs ≤ (u₃ * v₄ + u₄ * v₃).natAbs := by
      rcases le_total (u₃ * v₄).natAbs (u₄ * v₃).natAbs with h | h
      · rw [max_eq_right h, min_eq_left h]
        have : (u₄ * v₃).natAbs ≤ (u₃ * v₄ + u₄ * v₃).natAbs + (u₃ * v₄).natAbs := by
          have := Int.natAbs_sub_le (u₃ * v₄ + u₄ * v₃) (u₃ * v₄)
          simpa using this
        omega
      · rw [max_eq_left h, min_eq_right h]
        have : (u₃ * v₄).natAbs ≤ (u₃ * v₄ + u₄ * v₃).natAbs + (u₄ * v₃).natAbs := by
          have := Int.natAbs_sub_le (u₃ * v₄ + u₄ * v₃) (u₄ * v₃)
          simpa using this
        omega
    rw [e1, e2] at habs
    have hc : p₄ * q₃ = q₃ * p₄ := Nat.mul_comm _ _
    rw [hc] at habs
    exact habs
  have hfour := four_term_bound (p₃ := p₃) (q₃ := q₃) (p₄ := p₄) (q₄ := q₄)
    (b := B'.natAbs) hdiff
  -- assemble
  have hheight : naiveHeight x₃ * naiveHeight x₄ = max p₃ q₃ * max p₄ q₄ := rfl
  rw [hheight]
  calc max p₃ q₃ * max p₄ q₄
      ≤ 2 * max (max (q₃ * q₄) B'.natAbs) (p₃ * p₄) := hfour
    _ = 2 * max (max A'.natAbs B'.natAbs) C'.natAbs := by rw [hAn, hCn]
    _ ≤ 2 * max (max A.natAbs B.natAbs) C.natAbs := by
        exact Nat.mul_le_mul_left 2 (max_le_max (max_le_max hAle hBle) hCle)

end PrincipiaTractalis.QuadraticRootHeights

#print axioms PrincipiaTractalis.QuadraticRootHeights.den_dvd
#print axioms PrincipiaTractalis.QuadraticRootHeights.den_mul_den_dvd
#print axioms PrincipiaTractalis.QuadraticRootHeights.four_term_bound
#print axioms PrincipiaTractalis.QuadraticRootHeights.naiveHeight_mul_le_of_quadratic
