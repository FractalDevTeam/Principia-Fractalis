/-
# PF.TorsionCheck5077a1_r166a

★★★ 2026-07-31 — THE FINITE TORSION CHECK FOR 5077a1, DONE IN ℤ ★★★

The computational core of "5077a1 has trivial torsion", as a single
kernel-verified theorem: **no coprime pair `(a,b)` with `|a| ≤ 47`,
`1 ≤ b ≤ 47` keeps height `≤ 47` through two steps of the duplication map.**

## Why this file exists separately

r156 gives: if `ĥ(R) = 0` then `h(x(2ⁿR)) ≤ 47` for all `n`, since
`47³ = 103823 ≤ 105754 < 110592 = 48³`.  So torsion-freeness reduces to a check
over the 2783 rationals of naïve height `≤ 47` — the same argument r155 used at
the bound 12 for 389a1, where there were only 183.

Phrased over `ℚ` that check **does not fit on this machine**.  Measured:
`decide +kernel` on all 2783 gets stuck at `List.decidableBAll`; split into four
blocks of ≤1140, the first block reached **12.9 GB RSS** on a 15 GB box with
swap exhausted and had to be killed.  The cost is `Rat`: normalization gcds on
22-digit numerators, with the whole `Finset ℚ` and every intermediate
materialized.

Phrased over `ℤ` the identical mathematical content costs
**6.2 s and 2.5 GB, all 2783 in one shot** — a >5× memory reduction and no
chunking.  The reason is that `ℤ`/`ℕ` arithmetic and `Int.gcd` are
GMP-accelerated in the kernel, while `Rat` carries a structure plus an
invariant.  **This is the transferable lesson: put finite kernel checks in `ℤ`,
never in `ℚ`.**

## What is proved here, exactly

`all_escape` is a statement about integers only.  With
`F, G3, D` the r144 duplication forms and `hgt p q` the height of the reduced
form of `p/q` (the right-hand side of r133's `naiveHeight_div_int`), it says: for
every `i < 95`, `j < 47`, writing `a = i - 47`, `b = j + 1`, one of the two
heights exceeds 47.  The two survivors of the first step are `a/b = 1` and `2`
(mapping to `14` and `21`); neither survives the second.

Note `F` and `D` are invariant under `(a,b) ↦ (−a,−b)` (`F` has even degree, and
`D = b·G3` with `G3` odd), so the sign of the reduced denominator is irrelevant
— which is what lets the second step be taken on `(F/g, D/g)` without
normalising the sign.

HONEST SCOPE.  This is the finite check, nothing more.  It is **not** yet
`torsion_eq_zero` for 5077a1: that needs the bridge
`naiveHeight (f x / g x) = hgt (F x.num x.den) (D x.num x.den)` — available from
r144's `F_cast`/`D_cast` plus r133's `naiveHeight_div_int` — together with a
`num`/`den` lemma for `(p : ℚ)/(q : ℚ)` in reduced form, which r133 proves
internally but does not export.  See `codex/R166_RESOURCE_WALL_2026-07-31.md`.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import PF.NaiveHeightQ_r130
import Mathlib.Tactic.Ring

namespace PrincipiaTractalis.TorsionCheck5077a1

/-- Height of the reduced form of `p/q`, in ℤ.  This is exactly the right-hand
side of r133's `naiveHeight_div_int`. -/
def hgt (p q : ℤ) : ℕ :=
  max ((p / (Int.gcd p q : ℤ)).natAbs) ((q / (Int.gcd p q : ℤ)).natAbs)

/-- r144's duplication numerator form. -/
def Fp  (a b : ℤ) : ℤ := a ^ 4 + 14 * a ^ 2 * b ^ 2 - 50 * a * b ^ 3 + 49 * b ^ 4
/-- r144's `G3`. -/
def G3p (a b : ℤ) : ℤ := 4 * a ^ 3 - 28 * a * b ^ 2 + 25 * b ^ 3
/-- r144's duplication denominator form `D = b·G3`. -/
def Dp  (a b : ℤ) : ℤ := b * G3p a b

/-- Numerator of the reduced form of the first duplication step. -/
def sN (a b : ℤ) : ℤ := Fp a b / (Int.gcd (Fp a b) (Dp a b) : ℤ)
/-- Denominator of the reduced form of the first duplication step. -/
def sD (a b : ℤ) : ℤ := Dp a b / (Int.gcd (Fp a b) (Dp a b) : ℤ)

/-- `Fp` and `Dp` are invariant under negating both arguments, so the sign of a
reduced denominator never matters below. -/
theorem Fp_neg (a b : ℤ) : Fp (-a) (-b) = Fp a b := by simp only [Fp]; ring

theorem Dp_neg (a b : ℤ) : Dp (-a) (-b) = Dp a b := by
  simp only [Dp, G3p]; ring

set_option maxRecDepth 1000000 in
/-- **★ THE FINITE CHECK ★**  All 2783 candidates, in one kernel reduction:
no rational of naïve height `≤ 47` keeps height `≤ 47` through two duplication
steps.  6.2 s, 2.5 GB. -/
theorem all_escape :
    ∀ i ∈ Finset.range 95, ∀ j ∈ Finset.range 47,
      ¬ (hgt (Fp ((i : ℤ) - 47) ((j : ℤ) + 1)) (Dp ((i : ℤ) - 47) ((j : ℤ) + 1)) ≤ 47 ∧
         hgt (Fp (sN ((i : ℤ) - 47) ((j : ℤ) + 1)) (sD ((i : ℤ) - 47) ((j : ℤ) + 1)))
             (Dp (sN ((i : ℤ) - 47) ((j : ℤ) + 1)) (sD ((i : ℤ) - 47) ((j : ℤ) + 1))) ≤ 47) := by
  decide +kernel

end PrincipiaTractalis.TorsionCheck5077a1

#print axioms PrincipiaTractalis.TorsionCheck5077a1.Fp_neg
#print axioms PrincipiaTractalis.TorsionCheck5077a1.Dp_neg
#print axioms PrincipiaTractalis.TorsionCheck5077a1.all_escape
