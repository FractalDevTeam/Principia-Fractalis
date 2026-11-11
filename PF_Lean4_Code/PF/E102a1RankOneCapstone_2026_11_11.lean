/-
# PF.E102a1RankOneCapstone_2026_11_11 — the rank bound for 102a1

The tail of `PF/E102a1RankOne_2026_11_10.lean`: from the per-curve facts
proved there (b-invariants, `Ψ`-factorisation, `Ψ ≠ 0` at every rational
`x ≠ 0`, discriminant) to

  `1 ≤ Module.rank ℤ E_102a1(ℚ)`.

**Delta from the 91a1 capstone.**  E_91a1 has no rational 2-torsion, so
`CanheightParallelogramUniversal_r200`'s wrapper `X_dbl_of_ne_zero`
applies with a single curve-wide `h2tor`.  E_102a1 has rational 2-torsion
at `(0, 0)` (LMFDB torsion `ℤ/6ℤ`), so the curve-wide hypothesis fails
and the route is per-point: at every orbit level we transfer
`2 • (2^n • P102) ≠ 0` through the orbit via a curve-specific lemma —
`two_smul_ne_zero_of_x_ne_zero` — which specialises the universal
2-torsion analysis to E_102a1's unique rational 2-torsion `(0, 0)`.  The
scaffold's `Psi_ne_zero_at_nonzero` discharges `Ψ ≠ 0` per level without
any curve-wide input.

**The base point.** `P102 = (2, 2)`, LMFDB's rank-1 generator of
E_102a1(ℚ) modulo the ℤ/2 torsion subgroup `{O, (0, 0)}`.

**The orbit.**
`x(2^n P102) : 2 → 1 → 9 → 6889/3249 → 4701889196324329/4863621711188241`,
heights `2, 1, 9, 6889, 4863621711188241`.  The universal curve constant
`CL 5 (-4) 0 (-4) = 1 569 168`; the threshold bites at `n = 4`, so the
chain from `16 P102` on is infinite.

**κ is never transcribed.** `kap` is defined as `(CL 5 (-4) 0 (-4)).toNat`
and `norm_num` computes it; a wrong hand-copied value cannot sit here
undetected.

HONEST SCOPE.  A LOWER bound on the rank of one curve.  It does not
compute the exact rank, says nothing about `L(E, s)`, and proves no part
of BSD.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.E102a1RankOne_2026_11_10
import PF.DuplicationFormula_r178
import PF.DuplicationHeightBound37a1_r133
import PF.NonTorsionFromOrbit_2026_10_21
import PF.PointParallelogramUniversal_r199
import PF.CanheightParallelogramUniversal_r200
import PF.CanonicalHeightGeneric_r171
import Mathlib.Tactic.NormNum.GCD

namespace PrincipiaTractalis
namespace E102a1RankOneCapstone20261111

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.BSD_HeegnerRank1ProofE102a1
open PrincipiaTractalis.E102a1RankOne20261110
open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationFormula
open PrincipiaTractalis.PointParallelogramUniversal
open PrincipiaTractalis.CanheightParallelogramUniversal
open PrincipiaTractalis.CanonicalHeightGeneric

/-! ## §1 — the base point `P102 = (2, 2)` -/

/-- `(2, 2)` is a nonsingular rational point of 102a1.  Since the
discriminant is nonzero, `Equation ↔ Nonsingular`, and the equation at
`(2, 2)` is a direct norm_num check. -/
theorem P102_nonsingular : E_102a1.toAffine.Nonsingular 2 2 := by
  have hΔ : E_102a1.toAffine.Δ ≠ 0 := E_102a1_Δ_ne_zero
  have hEq : E_102a1.toAffine.Equation 2 2 := by
    rw [WeierstrassCurve.Affine.equation_iff]
    unfold E_102a1
    norm_num
  exact (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hEq

/-- **The base point** `P102 = (2, 2) ∈ E_102a1(ℚ)`. -/
noncomputable def P102 : E_102a1.toAffine.Point := Point.some P102_nonsingular

theorem P102_ne_zero : P102 ≠ 0 := some_ne_zero _

theorem X_P102 : X P102 = 2 := rfl

/-! ## §2 — `dblQ` on 102a1, dehomogenised

Instantiating the b-invariants `(5, -4, 0, -4)` into r178's `phiX`/`psiX`
produces two concrete rational polynomials that make the orbit
`norm_num`-computable. -/

/-- Duplication numerator on 102a1: `x⁴ + 4x² + 4 = (x² + 2)²`. -/
def f102 (x : ℚ) : ℚ := x ^ 4 + 4 * x ^ 2 + 4

/-- Duplication denominator on 102a1: `4x³ + 5x² − 8x = x·(4x² + 5x − 8)`. -/
def g102 (x : ℚ) : ℚ := 4 * x ^ 3 + 5 * x ^ 2 - 8 * x

theorem phiX_eq_f102 (x : ℚ) : phiX (E_102a1.toAffine) x = f102 x := by
  simp only [phiX, f102, b₄_eq, b₆_eq, b₈_eq]
  push_cast
  ring

theorem psiX_eq_g102 (x : ℚ) : psiX (E_102a1.toAffine) x = g102 x := by
  simp only [psiX, g102, b₂_eq, b₄_eq, b₆_eq]
  push_cast
  ring

/-- **The duplication map on 102a1, as a rational function.** -/
theorem dblQ_eq_fg102 (x : ℚ) :
    dblQ 5 (-4) 0 (-4) x = f102 x / g102 x := by
  rw [dblQ_eq_phiX_div_psiX b₂_eq.symm b₄_eq.symm b₆_eq.symm b₈_eq.symm x,
      phiX_eq_f102, psiX_eq_g102]

/-- `f102` is always strictly positive: `f102 x = (x² + 2)² ≥ 4 > 0`. -/
theorem f102_pos (x : ℚ) : 0 < f102 x := by
  have h : f102 x = (x ^ 2 + 2) ^ 2 := by unfold f102; ring
  rw [h]
  have hpos : 0 < x ^ 2 + 2 := by positivity
  positivity

theorem f102_ne_zero (x : ℚ) : f102 x ≠ 0 := (f102_pos x).ne'

/-- `g102(x) ≠ 0` whenever `x ≠ 0`.  Proof: `g102 = x·(4x² + 5x − 8)`;
`x ≠ 0` and the scaffold's `quadratic_factor_coprime_no_solution`
(mod-5 argument) together force both factors nonzero. -/
theorem g102_ne_zero_of_ne_zero (x : ℚ) (hx : x ≠ 0) : g102 x ≠ 0 := by
  intro h
  -- Factor: g102 x = x · Q(x) where Q(x) = 4x² + 5x - 8.
  have hfactor : x * (4 * x ^ 2 + 5 * x - 8) = 0 := by
    have : g102 x = x * (4 * x ^ 2 + 5 * x - 8) := by unfold g102; ring
    linarith [this, h]
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact hx h1
  -- Q(x) = 0 at a rational x: translate to (x.num, x.den) and kill via scaffold.
  apply quadratic_factor_coprime_no_solution x.num (x.den : ℤ)
    (by exact_mod_cast x.den_nz) (isCoprime_num_den x)
  -- Multiply Q(x) = 0 by den², get the integer identity.
  have hden_ne : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hx_num : (x.num : ℚ) = x * (x.den : ℚ) := by
    have := Rat.num_div_den x
    field_simp at this
    linarith
  have hQ : (4 * (x.num : ℚ) ^ 2 + 5 * (x.num : ℚ) * (x.den : ℚ)
             - 8 * (x.den : ℚ) ^ 2) = 0 := by
    rw [hx_num]
    have : (x.den : ℚ) ^ 2 * (4 * x ^ 2 + 5 * x - 8) = 0 := by
      rw [h2]; ring
    linear_combination this
  have hQ_int : (((4 * x.num ^ 2 + 5 * x.num * (x.den : ℤ)
                  - 8 * (x.den : ℤ) ^ 2 : ℤ) : ℚ) = 0) := by
    push_cast
    linear_combination hQ
  exact_mod_cast hQ_int

/-- The ratio `dblQ x = f102 x / g102 x ≠ 0` at every rational `x ≠ 0`,
because `f102 ≠ 0` always and `g102 ≠ 0` when `x ≠ 0`. -/
theorem dblQ_ne_zero_of_ne_zero (x : ℚ) (hx : x ≠ 0) :
    dblQ 5 (-4) 0 (-4) x ≠ 0 := by
  rw [dblQ_eq_fg102]
  exact div_ne_zero (f102_ne_zero x) (g102_ne_zero_of_ne_zero x hx)

/-! ## §3 — the arithmetic chain and its first five values -/

/-- The x-coordinates of the doubling orbit of `P102`, as pure arithmetic. -/
def xs : ℕ → ℚ
  | 0 => 2
  | n + 1 => dblQ 5 (-4) 0 (-4) (xs n)

theorem xs_zero : xs 0 = 2 := rfl

theorem xs_succ (n : ℕ) : xs (n + 1) = dblQ 5 (-4) 0 (-4) (xs n) := rfl

theorem xs_one : xs 1 = 1 := by
  show xs (0 + 1) = 1
  rw [xs_succ, xs_zero, dblQ_eq_fg102]
  norm_num [f102, g102]

theorem xs_two : xs 2 = 9 := by
  show xs (1 + 1) = 9
  rw [xs_succ, xs_one, dblQ_eq_fg102]
  norm_num [f102, g102]

theorem xs_three : xs 3 = 6889 / 3249 := by
  show xs (2 + 1) = 6889 / 3249
  rw [xs_succ, xs_two, dblQ_eq_fg102]
  norm_num [f102, g102]

/-- `x(16 P102) = 4701889196324329 / 4863621711188241`. -/
theorem xs_four :
    xs 4 = 4701889196324329 / 4863621711188241 := by
  show xs (3 + 1) = 4701889196324329 / 4863621711188241
  rw [xs_succ, xs_three, dblQ_eq_fg102]
  norm_num [f102, g102]

/-- Every element of the orbit is nonzero.  By induction: `xs 0 = 2 ≠ 0`,
and `xs (n+1) = dblQ(xs n) ≠ 0` whenever `xs n ≠ 0` by
`dblQ_ne_zero_of_ne_zero`. -/
theorem xs_ne_zero (n : ℕ) : xs n ≠ 0 := by
  induction n with
  | zero => show (2 : ℚ) ≠ 0; norm_num
  | succ k ih =>
      rw [xs_succ]
      exact dblQ_ne_zero_of_ne_zero (xs k) ih

/-! ## §4 — the height step, straight from the universal layer -/

/-- The curve constant, **computed** rather than copied: r175's `CL` at
102a1's b-invariants.  Nothing downstream depends on its decimal value. -/
def kap : ℕ := (CL 5 (-4) 0 (-4)).toNat

theorem kap_cast : ((kap : ℤ)) = CL 5 (-4) 0 (-4) :=
  Int.toNat_of_nonneg (CL_nonneg 5 (-4) 0 (-4))

/-- **The quartic duplication step, for every element of the chain.**
r176 proves this for every rational on every curve with nonzero
discriminant; the only 102a1 input is that `Ψ` never vanishes on the
orbit, which holds because `xs n ≠ 0` and the scaffold's
`Psi_ne_zero_at_nonzero` handles the rest. -/
theorem height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ kap * naiveHeight (xs (n + 1)) := by
  have h := nh_pow_le_of_disc_ne_zero (hrel := hrel102) (x := xs n)
    (hΨ := Psi_ne_zero_at_nonzero (xs n) (xs_ne_zero n)) hΔ102
  rw [← xs_succ n] at h
  have hgoal : ((naiveHeight (xs n) : ℤ)) ^ 4
      ≤ (kap : ℤ) * ((naiveHeight (xs (n + 1)) : ℤ)) := by
    rw [naiveHeight_eq_nh, naiveHeight_eq_nh, kap_cast]
    exact h
  exact_mod_cast hgoal

/-! ## §5 — the threshold -/

/-- `naiveHeight (x(16 P102)) = 4 863 621 711 188 241`; the fraction is
already reduced, certified by `norm_num`'s gcd extension. -/
theorem naiveHeight_xs_four :
    naiveHeight (xs 4) = 4863621711188241 := by
  have h4 : xs 4 =
      ((4701889196324329 : ℤ) : ℚ) / ((4863621711188241 : ℤ) : ℚ) := by
    rw [xs_four]; norm_num
  have hg : Int.gcd 4701889196324329 4863621711188241 = 1 := by norm_num
  rw [h4, DuplicationHeightBound37a1.naiveHeight_div_int
    4701889196324329 4863621711188241 (by norm_num), hg]
  norm_num

theorem kap_pos : 0 < kap := by
  show 0 < (CL 5 (-4) 0 (-4)).toNat
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11,
    cG12, cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-- **The threshold check**: the orbit clears the curve constant at `n = 4`. -/
theorem threshold : kap < naiveHeight (xs 4) := by
  rw [naiveHeight_xs_four]
  show (CL 5 (-4) 0 (-4)).toNat < 4863621711188241
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11,
    cG12, cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-! ## §6 — firing r130's driver -/

/-- **The chain from `16 P102` on takes infinitely many values.** -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 4)).Infinite :=
  infinite_of_duplication_step (κ := kap) (fun n => xs (n + 4)) kap_pos
    (fun n => height_step (n + 4)) threshold

/-! ## §7 — the curve-specific 2-torsion lemma

On E_102a1, the only rational 2-torsion is `(0, 0)` (the other roots of
the 2-torsion polynomial `4x² + 5x − 8` are irrational by the scaffold's
mod-5 argument).  Hence: for any nonsingular affine `(x, y)` on 102a1
with `x ≠ 0`, we have `2 • Point.some h ≠ 0`.

This is the single per-point substitute for the curve-wide
`h2tor : ∀ R ≠ 0, 2 • R ≠ 0` used by the 91a1 capstone. -/

/-- `negY` on 102a1 at `(x, y)` is `-y - x` (because `a₁ = 1, a₃ = 0`). -/
theorem negY_E102a1 (x y : ℚ) : E_102a1.toAffine.negY x y = -y - x := by
  simp [Affine.negY, E_102a1]

/-- **Curve-specific 2-torsion lemma.**  If `(x, y)` is a nonsingular
rational point of E_102a1 with `x ≠ 0`, then `2 • Point.some h ≠ 0`.

Proof: `2 • Point.some h = 0 ⟺ y = negY x y = -y - x`, i.e. `2y + x = 0`,
i.e. `y = -x/2`.  Substituting into the Weierstrass equation
`y² + xy = x³ + x² − 2x` and multiplying by 4 gives `4x³ + 5x² − 8x = 0`,
i.e. `x · (4x² + 5x − 8) = 0`.  With `x ≠ 0`, the quadratic factor
vanishes at a rational — but the scaffold's
`quadratic_factor_coprime_no_solution` rules that out. -/
theorem two_smul_ne_zero_of_x_ne_zero {x y : ℚ}
    (h : E_102a1.toAffine.Nonsingular x y) (hx : x ≠ 0) :
    (2 : ℕ) • Point.some h ≠ 0 := by
  intro h2
  -- From `2 • Point.some h = 0` derive `y = negY x y`.
  rw [two_nsmul] at h2
  by_cases hy : y = E_102a1.toAffine.negY x y
  · -- The main case: `y = -y - x`, hence `y = -x/2`.
    rw [negY_E102a1] at hy
    have h2y : 2 * y + x = 0 := by linarith
    -- Substitute into the equation `y² + xy = x³ + x² − 2x` (from `h.left`).
    have hEq : E_102a1.toAffine.Equation x y := h.left
    rw [WeierstrassCurve.Affine.equation_iff] at hEq
    -- E_102a1 coefficients unfold: `y² + 1·x·y + 0·y − x³ − 1·x² − (-2)·x − 0 = 0`.
    have hUnfold : y ^ 2 + x * y - x ^ 3 - x ^ 2 + 2 * x = 0 := by
      have := hEq
      simp [E_102a1] at this
      linarith
    -- From `2y + x = 0` we get `y = -x/2`; substitute into `hUnfold`.
    have hcubic : 4 * x ^ 3 + 5 * x ^ 2 - 8 * x = 0 := by
      have hy_eq : y = -x / 2 := by linarith
      have : y ^ 2 = x ^ 2 / 4 := by rw [hy_eq]; ring
      have hxy : x * y = -x ^ 2 / 2 := by rw [hy_eq]; ring
      -- y² + xy = x²/4 - x²/2 = -x²/4
      have hlhs : y ^ 2 + x * y = -x ^ 2 / 4 := by rw [this, hxy]; ring
      -- Rewriting hUnfold with hlhs:
      have : -x ^ 2 / 4 - x ^ 3 - x ^ 2 + 2 * x = 0 := by linarith [hUnfold]
      linarith
    -- Factor: `x · (4x² + 5x − 8) = 0`; with `x ≠ 0`, the quadratic factor is 0.
    have hfactor : x * (4 * x ^ 2 + 5 * x - 8) = 0 := by linarith
    have hquad : 4 * x ^ 2 + 5 * x - 8 = 0 := by
      rcases mul_eq_zero.mp hfactor with h1 | h2
      · exact absurd h1 hx
      · exact h2
    -- Translate to integer form via x.num, x.den and kill via scaffold.
    apply quadratic_factor_coprime_no_solution x.num (x.den : ℤ)
      (by exact_mod_cast x.den_nz) (isCoprime_num_den x)
    have hden_ne : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
    have hx_num : (x.num : ℚ) = x * (x.den : ℚ) := by
      have := Rat.num_div_den x
      field_simp at this
      linarith
    have hQ : (4 * (x.num : ℚ) ^ 2 + 5 * (x.num : ℚ) * (x.den : ℚ)
               - 8 * (x.den : ℚ) ^ 2) = 0 := by
      rw [hx_num]
      have : (x.den : ℚ) ^ 2 * (4 * x ^ 2 + 5 * x - 8) = 0 := by
        rw [hquad]; ring
      linear_combination this
    have hQ_int : (((4 * x.num ^ 2 + 5 * x.num * (x.den : ℤ)
                    - 8 * (x.den : ℤ) ^ 2 : ℤ) : ℚ) = 0) := by
      push_cast
      linear_combination hQ
    exact_mod_cast hQ_int
  · -- If `y ≠ negY`, then `Point.add_self_of_Y_ne` gives a nonzero sum,
    -- contradicting `h2 : Point.some h + Point.some h = 0`.
    rw [Point.add_self_of_Y_ne hy] at h2
    exact some_ne_zero _ h2

/-! ## §8 — transporting the chain onto the point group

The orbit of `P102` under doubling, as points, has x-coordinates `xs n`.
Because 102a1 has rational 2-torsion we can't borrow a curve-wide
`h2tor` from r200; instead, a single bundled induction carries both
invariants —

  * `((2 : ℤ) ^ n) • P102 ≠ 0`
  * `X (((2 : ℤ) ^ n) • P102) = xs n`

— using `two_smul_ne_zero_of_x_ne_zero` as the bridge between them at
every successor step. -/

/-- **The orbit, bundled.**  At every level `n`, `2^n • P102` is an
affine point whose x-coordinate is `xs n`. -/
theorem smul_P102_affine_xs (n : ℕ) :
    ∃ (xn yn : ℚ) (h : E_102a1.toAffine.Nonsingular xn yn),
      ((2 : ℤ) ^ n) • P102 = Point.some h ∧ xn = xs n := by
  induction n with
  | zero =>
      refine ⟨2, 2, P102_nonsingular, ?_, xs_zero.symm⟩
      show (1 : ℤ) • P102 = Point.some P102_nonsingular
      simp [P102]
  | succ k ih =>
      obtain ⟨xk, yk, hk, hpk_eq, hxk_eq⟩ := ih
      have hxk_ne : xk ≠ 0 := by rw [hxk_eq]; exact xs_ne_zero k
      have h2k : (2 : ℕ) • Point.some hk ≠ 0 :=
        two_smul_ne_zero_of_x_ne_zero hk hxk_ne
      have hy : yk ≠ E_102a1.toAffine.negY xk yk :=
        y_ne_negY_of_two_smul_ne_zero hk h2k
      -- `(2 : ℤ) ^ (k+1) • P102 = (2^k • P) + (2^k • P) = Point.some hk + Point.some hk`.
      have hkp1_rw : ((2 : ℤ) ^ (k + 1)) • P102
          = Point.some hk + Point.some hk := by
        rw [two_pow_succ_zsmul, hpk_eq]
      -- The x-coordinate of the next point is `dblQ 5 (-4) 0 (-4) xk = xs (k+1)`.
      have hXkp1 : X (((2 : ℤ) ^ (k + 1)) • P102) = xs (k + 1) := by
        rw [hkp1_rw, X_dbl b₂_eq b₄_eq b₆_eq b₈_eq hk hy, hxk_eq, xs_succ]
      -- `(2 : ℤ) ^ (k+1) • P102` is affine (nonzero), extract its data.
      rcases hcase : ((2 : ℤ) ^ (k + 1)) • P102 with _ | @⟨xkp1, ykp1, hkp1⟩
      · -- Impossible: would contradict h2k.
        exfalso
        apply h2k
        rw [two_nsmul, ← hpk_eq, ← two_pow_succ_zsmul]
        exact hcase
      · refine ⟨xkp1, ykp1, hkp1, rfl, ?_⟩
        rw [hcase] at hXkp1
        simpa [X_some] using hXkp1

/-- The key invariant: `2^n • P102` is nonzero at every level. -/
theorem smul_P102_ne_zero (n : ℕ) : ((2 : ℤ) ^ n) • P102 ≠ 0 := by
  obtain ⟨xn, yn, hn, heq, _⟩ := smul_P102_affine_xs n
  rw [heq]
  exact some_ne_zero _

/-- The r199 `X` on `2^n • P102` equals `xs n`, unconditionally. -/
theorem X_two_pow_smul (n : ℕ) :
    X (((2 : ℤ) ^ n) • P102) = xs n := by
  obtain ⟨xn, yn, hn, heq, hxn⟩ := smul_P102_affine_xs n
  rw [heq, X_some]
  exact hxn

/-- Bridge between r199's generic `X` and `NonTorsionFromOrbit`'s local
`X`.  Both are the same `match`, so they agree by `rfl` pointwise. -/
theorem X_bridge (R : E_102a1.toAffine.Point) :
    NonTorsionFromOrbit20261021.X R = X R := by
  cases R <;> rfl

/-- The non-torsion driver's x-orbit, in terms of the arithmetic chain. -/
theorem orbit_infinite :
    (Set.range fun n =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 4)) • P102)).Infinite := by
  have hfun : (fun n : ℕ =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 4)) • P102))
      = fun n : ℕ => xs (n + 4) := by
    funext n
    rw [X_bridge, X_two_pow_smul]
  rw [hfun]
  exact xs_shifted_infinite

/-! ## §9 — the capstones -/

/-- **`P102 = (2, 2)` has infinite order in `E_102a1(ℚ)`.** -/
theorem P102_nonTorsion : ¬ IsOfFinAddOrder P102 :=
  NonTorsionFromOrbit20261021.nonTorsion_of_doubling_orbit_infinite P102 4
    orbit_infinite

/-- **THE FLAG — `rank E_102a1(ℚ) ≥ 1`.** A lower bound, nothing more. -/
theorem E102a1_rank_ge_one : 1 ≤ Module.rank ℤ E_102a1.toAffine.Point :=
  NonTorsionFromOrbit20261021.rank_ge_one_of_doubling_orbit_infinite P102 4
    orbit_infinite

end E102a1RankOneCapstone20261111
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.P102_nonsingular
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.dblQ_eq_fg102
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.xs_four
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.xs_ne_zero
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.height_step
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.naiveHeight_xs_four
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.threshold
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.xs_shifted_infinite
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.two_smul_ne_zero_of_x_ne_zero
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.smul_P102_ne_zero
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.X_two_pow_smul
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.X_bridge
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.P102_nonTorsion
#print axioms PrincipiaTractalis.E102a1RankOneCapstone20261111.E102a1_rank_ge_one

-- The computed curve constant, for the record: kap = 1569168.
#eval PrincipiaTractalis.E102a1RankOneCapstone20261111.kap
