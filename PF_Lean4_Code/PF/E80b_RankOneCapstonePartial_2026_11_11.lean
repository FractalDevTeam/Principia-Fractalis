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

namespace PrincipiaTractalis
namespace E80b_RankOneCapstonePartial20261111

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.E80b_RankOne20261111
open PrincipiaTractalis.NaiveHeightQ
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

-- Computed curve constant for the record: kap = 144750000000000.
#eval PrincipiaTractalis.E80b_RankOneCapstonePartial20261111.kap
