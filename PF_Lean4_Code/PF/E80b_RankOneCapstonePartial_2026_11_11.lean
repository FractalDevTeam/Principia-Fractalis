/-
# PF.E80b_RankOneCapstonePartial_2026_11_11 — partial capstone for E_80b

Partial continuation of `E80b_RankOne_2026_11_11.lean`.  This file
delivers the pieces that are feasible under a bounded session budget:

  * `P_80b : E_80b.toAffine.Point` — the classical congruent-number
    witness `(-4, 6)`, nonsingular on E_80b.
  * `f80b`, `g80b` — the dehomogenised duplication numerator and
    denominator on E_80b, concretised at the b-invariants.
  * `dblQ_eq_fg80b` — the rational-function form.
  * `xs` — the arithmetic orbit of x-coordinates under duplication.
  * `xs_zero`, `xs_one`, `xs_two` — the first three orbit values via
    `norm_num` (verified: `−4 → 1681/144 → 11183412793921/2234116132416`).
  * `kap`, `kap_cast`, `kap_pos` — the universal curve constant
    `CL(0, -50, 0, -625) = 144,750,000,000,000`, computed by `norm_num`.

**NOT yet delivered (future sessions):**

  * `xs_three` and `naiveHeight_xs_three` — these involve the 53-digit
    `xs 3 ≈ 6.24 × 10⁵²`, which is a `norm_num` stress test that may
    or may not fit a single Lean invocation.
  * The `xs_not_torsion` propagation invariant (`xs n ∉ {0, 5, -5}`
    for all `n`), which requires a height-growth induction past the
    shift level — algebraically different from the `xs_ne_zero` of
    E_102a1 and requires a `h > κ ⟹ h' > κ` nat-arithmetic step.
  * The bundled induction, X_two_pow_smul, orbit_infinite, and the
    final `E_80b_rank_ge_one` theorem.

Scope: this file is a landing pad. See `codex/BSD_NEXT_STEPS_2026-11-11.md`
item B.rank≥1 for the full plan.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.E80b_RankOne_2026_11_11
import PF.DuplicationFormula_r178
import PF.DuplicationHeightBound37a1_r133
import PF.NonTorsionFromOrbit_2026_10_21
import PF.CanonicalHeightGeneric_r171
import Mathlib.Tactic.NormNum.GCD

namespace PrincipiaTractalis
namespace E80b_RankOneCapstonePartial20261111

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.E80b_RankOne20261111
open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.CanonicalHeightGeneric
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationFormula
open PrincipiaTractalis.PointParallelogramUniversal
open PrincipiaTractalis.CanheightParallelogramUniversal

/-! ## §1 — the base point `P_80b = (-4, 6)` -/

/-- `(-4, 6)` is a nonsingular rational point of E_80b.  The equation
`y² = x³ − 25x` at `(-4, 6)` reads `36 = -64 + 100 = 36`. ✓ -/
theorem P_80b_nonsingular : E_80b.toAffine.Nonsingular (-4) 6 := by
  have hΔ : E_80b.toAffine.Δ ≠ 0 := by
    show E_80b.Δ ≠ 0
    -- E_80b.Δ = -16·(4·a4³ + 27·a6²) = -16·(4·(-25)³) = 16·62500 = 10^6
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈, E_80b]
  have hEq : E_80b.toAffine.Equation (-4) 6 := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [E_80b]
    norm_num
  exact (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hEq

/-- **The base point** `P_80b = (-4, 6) ∈ E_80b(ℚ)`. -/
noncomputable def P_80b : E_80b.toAffine.Point := Point.some P_80b_nonsingular

theorem P_80b_ne_zero : P_80b ≠ 0 := some_ne_zero _

theorem X_P_80b : X P_80b = -4 := rfl

/-! ## §2 — `dblQ` on E_80b, dehomogenised -/

/-- Duplication numerator on E_80b: `x⁴ + 50x² + 625 = (x² + 25)²`. -/
def f80b (x : ℚ) : ℚ := x ^ 4 + 50 * x ^ 2 + 625

/-- Duplication denominator on E_80b: `4x³ − 100x = 4·x·(x − 5)·(x + 5)`. -/
def g80b (x : ℚ) : ℚ := 4 * x ^ 3 - 100 * x

theorem phiX_eq_f80b (x : ℚ) : phiX (E_80b.toAffine) x = f80b x := by
  simp only [phiX, f80b, b₄_eq, b₆_eq, b₈_eq]
  push_cast
  ring

theorem psiX_eq_g80b (x : ℚ) : psiX (E_80b.toAffine) x = g80b x := by
  simp only [psiX, g80b, b₂_eq, b₄_eq, b₆_eq]
  push_cast
  ring

/-- **The duplication map on E_80b, as a rational function.** -/
theorem dblQ_eq_fg80b (x : ℚ) :
    dblQ 0 (-50) 0 (-625) x = f80b x / g80b x := by
  rw [dblQ_eq_phiX_div_psiX b₂_eq.symm b₄_eq.symm b₆_eq.symm b₈_eq.symm x,
      phiX_eq_f80b, psiX_eq_g80b]

/-! ## §3 — the arithmetic chain and its first three values -/

/-- The x-coordinates of the doubling orbit of `P_80b`. -/
def xs : ℕ → ℚ
  | 0 => -4
  | n + 1 => dblQ 0 (-50) 0 (-625) (xs n)

theorem xs_zero : xs 0 = -4 := rfl

theorem xs_succ (n : ℕ) : xs (n + 1) = dblQ 0 (-50) 0 (-625) (xs n) := rfl

/-- `x(2 P_80b) = 1681/144`, where `1681 = 41²` and `144 = 12²`. -/
theorem xs_one : xs 1 = 1681 / 144 := by
  show xs (0 + 1) = 1681 / 144
  rw [xs_succ, xs_zero, dblQ_eq_fg80b]
  norm_num [f80b, g80b]

/-- `x(4 P_80b) = 11183412793921 / 2234116132416`. -/
theorem xs_two : xs 2 = 11183412793921 / 2234116132416 := by
  show xs (1 + 1) = 11183412793921 / 2234116132416
  rw [xs_succ, xs_one, dblQ_eq_fg80b]
  norm_num [f80b, g80b]

/-! ## §4 — the universal curve constant -/

/-- The curve constant, **computed** rather than copied: r175's `CL`
at E_80b's b-invariants.  `#eval kap = 144750000000000`. -/
def kap : ℕ := (CL 0 (-50) 0 (-625)).toNat

theorem kap_cast : ((kap : ℤ)) = CL 0 (-50) 0 (-625) :=
  Int.toNat_of_nonneg (CL_nonneg 0 (-50) 0 (-625))

theorem kap_pos : 0 < kap := by
  show 0 < (CL 0 (-50) 0 (-625)).toNat
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11,
    cG12, cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-- `kap ≥ 6` on E_80b.  Needed so that `h > kap` implies `h > 5` and
hence `xs ∉ {0, 5, -5}` on the orbit. (Actually `kap = 144 750 000 000 000`.) -/
theorem kap_ge_six : 6 ≤ kap := by
  show 6 ≤ (CL 0 (-50) 0 (-625)).toNat
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11,
    cG12, cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-! ## §5 — `xs 3` and the threshold -/

/-- `x(8 P_80b) = 62425319345774489875576913540908007654663493663770881
                / 28667777423930631959129990083752908396266457397504`.
Both numerator and denominator are 53/50-digit integers; `norm_num`
dispatches the identity in ~1.5 seconds. -/
theorem xs_three :
    xs 3 = 62425319345774489875576913540908007654663493663770881
         / 28667777423930631959129990083752908396266457397504 := by
  show xs (2 + 1) = _
  rw [xs_succ, xs_two, dblQ_eq_fg80b]
  norm_num [f80b, g80b]

/-- `naiveHeight (x(8 P_80b)) = 62 425 319 345 774 489 875 576 913
540 908 007 654 663 493 663 770 881` (53 digits).  The fraction is
reduced, certified by `norm_num`'s gcd extension. -/
theorem naiveHeight_xs_three :
    naiveHeight (xs 3) = 62425319345774489875576913540908007654663493663770881 := by
  have h3 : xs 3 =
      ((62425319345774489875576913540908007654663493663770881 : ℤ) : ℚ)
      / ((28667777423930631959129990083752908396266457397504 : ℤ) : ℚ) := by
    rw [xs_three]; norm_num
  have hg : Int.gcd 62425319345774489875576913540908007654663493663770881
                    28667777423930631959129990083752908396266457397504 = 1 := by
    norm_num
  rw [h3, DuplicationHeightBound37a1.naiveHeight_div_int
    62425319345774489875576913540908007654663493663770881
    28667777423930631959129990083752908396266457397504 (by norm_num), hg]
  norm_num

/-- **The threshold check**: the orbit clears the curve constant at `n = 3`.
`κ = 1.45 × 10¹⁴ < 6.24 × 10⁵² = h(xs 3)`. -/
theorem threshold : kap < naiveHeight (xs 3) := by
  rw [naiveHeight_xs_three]
  show (CL 0 (-50) 0 (-625)).toNat < 62425319345774489875576913540908007654663493663770881
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11,
    cG12, cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-! ## §6 — orbit values are not 2-torsion -/

/-- `h(x) > 5` forces `x ∉ {0, 5, -5}`.  Because `naiveHeight 0 = 1`,
`naiveHeight 5 = 5`, `naiveHeight (-5) = 5`. -/
theorem not_torsion_of_height_gt_five {x : ℚ} (hh : 5 < naiveHeight x) :
    x ≠ 0 ∧ x ≠ 5 ∧ x ≠ -5 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> rw [heq] at hh <;>
    simp [naiveHeight] at hh

/-- Explicit non-torsion at the first three orbit values. -/
theorem xs_zero_not_torsion : xs 0 ≠ 0 ∧ xs 0 ≠ 5 ∧ xs 0 ≠ -5 := by
  rw [xs_zero]; refine ⟨?_, ?_, ?_⟩ <;> norm_num

theorem xs_one_not_torsion : xs 1 ≠ 0 ∧ xs 1 ≠ 5 ∧ xs 1 ≠ -5 := by
  rw [xs_one]; refine ⟨?_, ?_, ?_⟩ <;> norm_num

theorem xs_two_not_torsion : xs 2 ≠ 0 ∧ xs 2 ≠ 5 ∧ xs 2 ≠ -5 := by
  rw [xs_two]; refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-! ## §7 — the height step at any level where `xs n` is not 2-torsion -/

/-- Conditional height step: at every `n` where `xs n ∉ {0, 5, -5}`,
`h(xs n)^4 ≤ κ · h(xs (n+1))`. Uses the scaffold's
`Psi_ne_zero_at_not_torsion` and r176's `nh_pow_le_of_disc_ne_zero`. -/
theorem height_step_at (n : ℕ)
    (hnt : xs n ≠ 0 ∧ xs n ≠ 5 ∧ xs n ≠ -5) :
    naiveHeight (xs n) ^ 4 ≤ kap * naiveHeight (xs (n + 1)) := by
  have hΨ := Psi_ne_zero_at_not_torsion (xs n) hnt.1 hnt.2.1 hnt.2.2
  have h := nh_pow_le_of_disc_ne_zero (hrel := hrel80b) (x := xs n)
    (hΨ := hΨ) hΔ80b
  rw [← xs_succ n] at h
  have hgoal : ((naiveHeight (xs n) : ℤ)) ^ 4
      ≤ (kap : ℤ) * ((naiveHeight (xs (n + 1)) : ℤ)) := by
    rw [naiveHeight_eq_nh, naiveHeight_eq_nh, kap_cast]
    exact h
  exact_mod_cast hgoal

/-! ## §8 — propagation: `kap < h(xs (n+3))` for all `n`

Height-growth induction: given `kap < h(xs k)` and `xs k ∉ {0, 5, -5}`,
the height step gives `kap * h(xs (k+1)) ≥ h(xs k)^4`. Since
`h(xs k) ≥ kap + 1` (nat inequality, kap pos), `h(xs k)^4 ≥ (kap+1)^4`.
Expanding, `(kap+1)^4 = kap^4 + 4kap^3 + 6kap^2 + 4kap + 1 > kap^2 + kap`
when `kap ≥ 1`. So `kap * h(xs (k+1)) > kap^2 + kap = kap (kap + 1)`,
giving `h(xs (k+1)) > kap + 1 > kap`. -/

theorem xs_shifted_above_kap : ∀ n, kap < naiveHeight (xs (n + 3)) := by
  intro n
  induction n with
  | zero =>
      show kap < naiveHeight (xs 3)
      exact threshold
  | succ k ih =>
      -- ih : kap < h(xs (k + 3))
      -- Derive xs (k+3) ∉ {0, 5, -5} from h > kap ≥ 6 > 5.
      have hh_gt_five : 5 < naiveHeight (xs (k + 3)) := by
        have h1 : 6 ≤ kap := kap_ge_six
        omega
      have hnt := not_torsion_of_height_gt_five hh_gt_five
      -- Height step applies at xs (k + 3).
      have hstep := height_step_at (k + 3) hnt
      -- Now argue kap < h(xs (k + 4)).
      -- From ih: h(xs (k+3)) ≥ kap + 1.
      -- h(xs (k+3))^4 ≥ (kap + 1)^4 ≥ (kap + 1)^2 = kap^2 + 2kap + 1 > kap(kap+1).
      -- hstep: kap * h(xs (k+4)) ≥ h(xs (k+3))^4 > kap(kap+1).
      -- So h(xs (k+4)) > kap + 1 > kap. ✓
      have hkap_pos : 0 < kap := kap_pos
      have h1 : kap + 1 ≤ naiveHeight (xs (k + 3)) := ih
      -- (kap+1)^4 ≥ (kap+1)^2 via (kap+1) ≥ 1
      have hsq : (kap + 1) ^ 2 ≤ naiveHeight (xs (k + 3)) ^ 2 :=
        Nat.pow_le_pow_left h1 2
      have hquad : naiveHeight (xs (k + 3)) ^ 2
          ≤ naiveHeight (xs (k + 3)) ^ 4 :=
        Nat.pow_le_pow_right (one_le_naiveHeight _) (by decide)
      -- so (kap+1)^2 ≤ h^4 ≤ kap * h(next)
      have hbound : (kap + 1) ^ 2 ≤ kap * naiveHeight (xs (k + 3 + 1)) :=
        hsq.trans (hquad.trans hstep)
      -- (kap+1)^2 = kap^2 + 2kap + 1 = kap * (kap + 2) + 1 > kap * (kap + 1)
      have hexpand : kap * (kap + 1) < (kap + 1) ^ 2 := by
        have : (kap + 1) ^ 2 = kap * (kap + 1) + (kap + 1) := by ring
        omega
      have hmul : kap * (kap + 1) < kap * naiveHeight (xs (k + 3 + 1)) :=
        lt_of_lt_of_le hexpand hbound
      have hnew : kap + 1 < naiveHeight (xs (k + 3 + 1)) :=
        (Nat.mul_lt_mul_left hkap_pos).mp hmul
      show kap < naiveHeight (xs (k + 1 + 3))
      have heq : k + 3 + 1 = k + 1 + 3 := by omega
      rw [← heq]
      omega

/-- The non-torsion invariant for the shifted orbit. -/
theorem xs_shifted_not_torsion (n : ℕ) :
    xs (n + 3) ≠ 0 ∧ xs (n + 3) ≠ 5 ∧ xs (n + 3) ≠ -5 := by
  have h1 : kap < naiveHeight (xs (n + 3)) := xs_shifted_above_kap n
  have h2 : 5 < naiveHeight (xs (n + 3)) := by
    have h3 : 6 ≤ kap := kap_ge_six
    omega
  exact not_torsion_of_height_gt_five h2

/-! ## §9 — the shifted height step and r130's driver -/

/-- Height step along the shifted chain. -/
theorem height_step_shifted (n : ℕ) :
    naiveHeight (xs (n + 3)) ^ 4 ≤ kap * naiveHeight (xs (n + 3 + 1)) :=
  height_step_at (n + 3) (xs_shifted_not_torsion n)

/-- **The chain from `8 P_80b` on takes infinitely many values.** -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 3)).Infinite := by
  refine infinite_of_duplication_step (κ := kap) (fun n => xs (n + 3)) kap_pos
    (fun n => ?_) threshold
  show naiveHeight (xs (n + 3)) ^ 4 ≤ kap * naiveHeight (xs (n + 3 + 1))
  exact height_step_shifted n

/-! ## §10 — bundled induction on the point-group orbit

Because E_80b has full rational 2-torsion, r200's `X_dbl_of_ne_zero`
with its curve-wide `h2tor` does not apply.  We take the E_102a1-style
per-point route and carry both invariants in one existential:

  `2^n • P_80b ≠ 0`  and  `X(2^n • P_80b) = xs n`,

using `two_smul_ne_zero_of_x_not_torsion` at each step. The crucial
non-torsion invariant `xs n ∉ {0, 5, -5}` splits:

  * n = 0, 1, 2 — by explicit norm_num (xs_zero/one/two_not_torsion).
  * n ≥ 3     — by the height-growth propagation. -/

/-- Curve-specific non-torsion invariant at every orbit level. -/
theorem xs_not_torsion (n : ℕ) :
    xs n ≠ 0 ∧ xs n ≠ 5 ∧ xs n ≠ -5 := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · -- Case n < 3: explicit check
    interval_cases n
    · exact xs_zero_not_torsion
    · exact xs_one_not_torsion
    · exact xs_two_not_torsion
  · -- Case n ≥ 3: use shifted propagation
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
    rw [Nat.add_comm]
    exact xs_shifted_not_torsion k

/-- **The orbit, bundled.** -/
theorem smul_P_80b_affine_xs (n : ℕ) :
    ∃ (xn yn : ℚ) (h : E_80b.toAffine.Nonsingular xn yn),
      ((2 : ℤ) ^ n) • P_80b = Point.some h ∧ xn = xs n := by
  induction n with
  | zero =>
      refine ⟨-4, 6, P_80b_nonsingular, ?_, xs_zero.symm⟩
      show ((2 : ℤ) ^ 0) • P_80b = Point.some P_80b_nonsingular
      simp [P_80b]
  | succ k ih =>
      obtain ⟨xk, yk, hk, hpk_eq, hxk_eq⟩ := ih
      -- xk = xs k ∉ {0, 5, -5}
      have hnt := xs_not_torsion k
      have hxk_nt : xk ≠ 0 ∧ xk ≠ 5 ∧ xk ≠ -5 := by
        rw [hxk_eq]; exact hnt
      have h2k : (2 : ℕ) • Point.some hk ≠ 0 :=
        two_smul_ne_zero_of_x_not_torsion hk hxk_nt.1 hxk_nt.2.1 hxk_nt.2.2
      have hy : yk ≠ E_80b.toAffine.negY xk yk :=
        y_ne_negY_of_two_smul_ne_zero hk h2k
      have hkp1_rw : ((2 : ℤ) ^ (k + 1)) • P_80b
          = Point.some hk + Point.some hk := by
        rw [two_pow_succ_zsmul, hpk_eq]
      have hXkp1 : X (((2 : ℤ) ^ (k + 1)) • P_80b) = xs (k + 1) := by
        rw [hkp1_rw, X_dbl b₂_eq b₄_eq b₆_eq b₈_eq hk hy, hxk_eq, xs_succ]
      rcases hcase : ((2 : ℤ) ^ (k + 1)) • P_80b with _ | @⟨xkp1, ykp1, hkp1⟩
      · exfalso
        apply h2k
        rw [two_nsmul, ← hpk_eq, ← two_pow_succ_zsmul]
        exact hcase
      · refine ⟨xkp1, ykp1, hkp1, rfl, ?_⟩
        rw [hcase] at hXkp1
        simpa [X_some] using hXkp1

/-- r199 `X` on `2^n • P_80b` equals `xs n`, unconditionally. -/
theorem X_two_pow_smul (n : ℕ) :
    X (((2 : ℤ) ^ n) • P_80b) = xs n := by
  obtain ⟨xn, yn, hn, heq, hxn⟩ := smul_P_80b_affine_xs n
  rw [heq, X_some]
  exact hxn

/-- Bridge between r199's generic `X` and `NonTorsionFromOrbit`'s local `X`. -/
theorem X_bridge (R : E_80b.toAffine.Point) :
    NonTorsionFromOrbit20261021.X R = X R := by
  cases R <;> rfl

theorem orbit_infinite :
    (Set.range fun n =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 3)) • P_80b)).Infinite := by
  have hfun : (fun n : ℕ =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 3)) • P_80b))
      = fun n : ℕ => xs (n + 3) := by
    funext n
    rw [X_bridge, X_two_pow_smul]
  rw [hfun]
  exact xs_shifted_infinite

/-! ## §11 — the capstones -/

/-- **`P_80b = (-4, 6)` has infinite order in `E_80b(ℚ)`.** -/
theorem P_80b_nonTorsion : ¬ IsOfFinAddOrder P_80b :=
  NonTorsionFromOrbit20261021.nonTorsion_of_doubling_orbit_infinite P_80b 3
    orbit_infinite

/-- **THE FLAG — `rank E_80b(ℚ) ≥ 1`.**  A lower bound, nothing more. -/
theorem E_80b_rank_ge_one : 1 ≤ Module.rank ℤ E_80b.toAffine.Point :=
  NonTorsionFromOrbit20261021.rank_ge_one_of_doubling_orbit_infinite P_80b 3
    orbit_infinite

end E80b_RankOneCapstonePartial20261111
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.P_80b_nonsingular
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.dblQ_eq_fg80b
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.xs_one
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.xs_two
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.kap_pos
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.kap_ge_six
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.xs_three
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.naiveHeight_xs_three
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.threshold
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.not_torsion_of_height_gt_five
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.xs_shifted_above_kap
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.xs_shifted_not_torsion
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.xs_shifted_infinite
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.xs_not_torsion
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.X_two_pow_smul
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.X_bridge
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.P_80b_nonTorsion
#print axioms PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.E_80b_rank_ge_one

-- Computed curve constant for the record: kap = 144750000000000.
#eval PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.kap
