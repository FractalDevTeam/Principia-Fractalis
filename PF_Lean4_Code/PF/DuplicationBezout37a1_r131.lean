/-
# PF.DuplicationBezout37a1_r131

★★★ 2026-07-27 — B3 OF THE NON-TORSION ARC ★★★

The resultant/gcd stone for the duplication height inequality on the curve
37a1 (`y² + y = x³ − x`). Stone B3 of the arc mapped in
`codex/BSD_NONTORSION_ARC_PLAN_2026-07-27.md`; it feeds
`infinite_of_duplication_step` (r130, `PF/NaiveHeightQ_r130.lean`) through B4.

For the homogenized duplication numerator `F(a,b) = a⁴ + 2a²b² − 2ab³ + b⁴`
and denominator `D(a,b) = b·(4a³ − 4ab² + b³)` (so that `x(2P) = F/D` for
`x = a/b`), this file proves — in PURE INTEGER ARITHMETIC:

* `bezout_b` / `bezout_a`: explicit Bézout identities certifying
  `Res(f, g) = 37²` at the cofactor level (`ring`-checked);
* `gcd_dvd_37`: for coprime `a b`, `gcd (F a b) (D a b) ∣ 37`;
* `size_bound`: `37·H⁷ ≤ 171·H³·max |F| |D|` where `H = max |a| |b|`
  (constants: `|P₁·b| ≤ 112H³`, `|Q₁| ≤ 59H³`, `112 + 59 = 171`;
  the `a`-branch needs only `73 + 33 = 106 ≤ 171`);
* `reduced_height_bound`: after dividing out `gcd(F, D)` (which divides 37),
  `37·H⁴ ≤ 171·37·max |F/gcd| |D/gcd|` — the exact shape B4 needs to
  convert into `naiveHeight (x 2P) · κ ≥ naiveHeight (x P)⁴` with
  `κ = 171·37 = 6327`.

HONEST SCOPE. Integer polynomial identities and elementary absolute-value
bookkeeping only. No elliptic curves appear; nothing here mentions points,
heights on curves, or torsion. The connection of `F/D` to the actual
duplication map on 37a1 is stone B2/B4, not this file.

Kernel axioms `[propext, Classical.choice, Quot.sound]` (the `ring`
identities are axiom-light); no `sorry`, no project axioms, no
`native_decide`.

Author: Pablo Cohen + Claude. 2026-07-27.
-/
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace PrincipiaTractalis.DuplicationBezout37a1

/-! ## §1 — the duplication numerator and denominator, homogenized

For 37a1 (`y² + y = x³ − x`): `x(2P) = f(x)/g(x)` with
`f(x) = x⁴ + 2x² − 2x + 1`, `g(x) = 4x³ − 4x + 1`. Substituting `x = a/b`
and clearing denominators (`f` by `b⁴`, `g` by `b³`, then one more `b` to
make the degrees match) gives the pair below. -/

/-- Homogenized duplication numerator for 37a1: `b⁴·f(a/b)`. -/
def F (a b : ℤ) : ℤ := a ^ 4 + 2 * a ^ 2 * b ^ 2 - 2 * a * b ^ 3 + b ^ 4

/-- Homogenized `g` before the extra factor of `b`: `b³·g(a/b)`. -/
def G3 (a b : ℤ) : ℤ := 4 * a ^ 3 - 4 * a * b ^ 2 + b ^ 3

/-- The duplication denominator form: `x(2P) = F a b / D a b` for `x = a/b`. -/
def D (a b : ℤ) : ℤ := b * G3 a b

/-! ## §2 — the two Bézout identities (resultant 37² at cofactor level) -/

/-- **Bézout identity, `b`-side**: eliminates `a` down to `37·b⁶`. -/
theorem bezout_b (a b : ℤ) :
    (-48 * a ^ 2 + 64 * b ^ 2) * F a b
      + (12 * a ^ 3 + 20 * a * b ^ 2 - 27 * b ^ 3) * G3 a b = 37 * b ^ 6 := by
  simp only [F, G3]; ring

/-- **Bézout identity, `a`-side**: eliminates `b` down to `37·a⁷`, already in
the `D = b·G3` denominator form. -/
theorem bezout_a (a b : ℤ) :
    (37 * a ^ 3 + 4 * a ^ 2 * b - 26 * a * b ^ 2 + 6 * b ^ 3) * F a b
      + (-a ^ 3 - 12 * a ^ 2 * b + 14 * a * b ^ 2 - 6 * b ^ 3) * D a b
      = 37 * a ^ 7 := by
  simp only [F, D, G3]; ring

/-- `bezout_b` multiplied through by `b`: the `b`-side identity in the
`D`-form that the gcd and size arguments consume. -/
theorem bezout_b_D (a b : ℤ) :
    ((-48 * a ^ 2 + 64 * b ^ 2) * b) * F a b
      + (12 * a ^ 3 + 20 * a * b ^ 2 - 27 * b ^ 3) * D a b = 37 * b ^ 7 := by
  simp only [F, D, G3]; ring

/-! ## §3 — the gcd bound: for coprime `(a, b)`, `gcd (F, D) ∣ 37` -/

/-- **The gcd bound.** For coprime `a b : ℤ`, the gcd of the duplication
numerator and denominator divides `37`. This is the whole point of the
Bézout identities: the gcd divides `37·a⁷` and `37·b⁷`, and coprimality of
`a⁷, b⁷` squeezes it into `37`. -/
theorem gcd_dvd_37 {a b : ℤ} (h : IsCoprime a b) :
    (Int.gcd (F a b) (D a b) : ℤ) ∣ 37 := by
  have hdF : (Int.gcd (F a b) (D a b) : ℤ) ∣ F a b := Int.gcd_dvd_left _ _
  have hdD : (Int.gcd (F a b) (D a b) : ℤ) ∣ D a b := Int.gcd_dvd_right _ _
  have hb7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 37 * b ^ 7 := by
    rw [← bezout_b_D a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have ha7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 37 * a ^ 7 := by
    rw [← bezout_a a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have h7 : IsCoprime (a ^ 7) (b ^ 7) := h.pow
  obtain ⟨u, v, huv⟩ := h7
  have key : (37 : ℤ) = u * (37 * a ^ 7) + v * (37 * b ^ 7) := by
    linear_combination (-37 : ℤ) * huv
  rw [key]
  exact dvd_add (ha7.mul_left u) (hb7.mul_left v)

/-- `gcd_dvd_37` in `ℕ`-form. -/
theorem gcd_dvd_37_nat {a b : ℤ} (h : IsCoprime a b) :
    Int.gcd (F a b) (D a b) ∣ 37 := by
  exact_mod_cast gcd_dvd_37 h

/-! ## §4 — the size lower bound

`37·H⁷ ≤ 171·H³·max |F| |D|` with `H = max |a| |b|`. Everything happens
in `ℕ` via `Int.natAbs`; the cofactor coefficient sums are
`b`-side: `112 + 59 = 171`, `a`-side: `73 + 33 = 106 ≤ 171`. -/

section SizeBound

/-- `|a|³ ≤ H³`. -/
private theorem mono30 (a b : ℤ) :
    a.natAbs ^ 3 ≤ (max a.natAbs b.natAbs) ^ 3 :=
  Nat.pow_le_pow_left (le_max_left _ _) 3

/-- `|b|³ ≤ H³`. -/
private theorem mono03 (a b : ℤ) :
    b.natAbs ^ 3 ≤ (max a.natAbs b.natAbs) ^ 3 :=
  Nat.pow_le_pow_left (le_max_right _ _) 3

/-- `|a|²·|b| ≤ H³`. -/
private theorem mono21 (a b : ℤ) :
    a.natAbs ^ 2 * b.natAbs ≤ (max a.natAbs b.natAbs) ^ 3 := by
  calc a.natAbs ^ 2 * b.natAbs
      ≤ (max a.natAbs b.natAbs) ^ 2 * max a.natAbs b.natAbs :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) 2) (le_max_right _ _)
    _ = (max a.natAbs b.natAbs) ^ 3 := by ring

/-- `|a|·|b|² ≤ H³`. -/
private theorem mono12 (a b : ℤ) :
    a.natAbs * b.natAbs ^ 2 ≤ (max a.natAbs b.natAbs) ^ 3 := by
  calc a.natAbs * b.natAbs ^ 2
      ≤ max a.natAbs b.natAbs * (max a.natAbs b.natAbs) ^ 2 :=
        Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_left (le_max_right _ _) 2)
    _ = (max a.natAbs b.natAbs) ^ 3 := by ring

/-- Cofactor bound, `b`-side, first cofactor: `|(−48a² + 64b²)·b| ≤ 112·H³`. -/
private theorem c1_bound (a b : ℤ) :
    ((-48 * a ^ 2 + 64 * b ^ 2) * b).natAbs
      ≤ 112 * (max a.natAbs b.natAbs) ^ 3 := by
  have h48 : ((-48 : ℤ)).natAbs = 48 := rfl
  have h64 : ((64 : ℤ)).natAbs = 64 := rfl
  have e1 : ((-48 : ℤ) * a ^ 2).natAbs = 48 * a.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h48]
  have e2 : ((64 : ℤ) * b ^ 2).natAbs = 64 * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h64]
  calc ((-48 * a ^ 2 + 64 * b ^ 2) * b).natAbs
      = (-48 * a ^ 2 + 64 * b ^ 2).natAbs * b.natAbs := Int.natAbs_mul _ _
    _ ≤ ((-48 * a ^ 2).natAbs + (64 * b ^ 2).natAbs) * b.natAbs :=
        Nat.mul_le_mul (Int.natAbs_add_le _ _) le_rfl
    _ = (48 * a.natAbs ^ 2 + 64 * b.natAbs ^ 2) * b.natAbs := by rw [e1, e2]
    _ = 48 * (a.natAbs ^ 2 * b.natAbs) + 64 * b.natAbs ^ 3 := by ring
    _ ≤ 48 * (max a.natAbs b.natAbs) ^ 3 + 64 * (max a.natAbs b.natAbs) ^ 3 :=
        Nat.add_le_add (Nat.mul_le_mul le_rfl (mono21 a b))
          (Nat.mul_le_mul le_rfl (mono03 a b))
    _ = 112 * (max a.natAbs b.natAbs) ^ 3 := by ring

/-- Cofactor bound, `b`-side, second cofactor:
`|12a³ + 20ab² − 27b³| ≤ 59·H³`. -/
private theorem c2_bound (a b : ℤ) :
    (12 * a ^ 3 + 20 * a * b ^ 2 - 27 * b ^ 3).natAbs
      ≤ 59 * (max a.natAbs b.natAbs) ^ 3 := by
  have h12 : ((12 : ℤ)).natAbs = 12 := rfl
  have h20 : ((20 : ℤ)).natAbs = 20 := rfl
  have h27 : ((27 : ℤ)).natAbs = 27 := rfl
  have e1 : ((12 : ℤ) * a ^ 3).natAbs = 12 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h12]
  have e2 : ((20 : ℤ) * a * b ^ 2).natAbs = 20 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h20]
  have e3 : ((27 : ℤ) * b ^ 3).natAbs = 27 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h27]
  calc (12 * a ^ 3 + 20 * a * b ^ 2 - 27 * b ^ 3).natAbs
      ≤ (12 * a ^ 3 + 20 * a * b ^ 2).natAbs + (27 * b ^ 3).natAbs :=
        Int.natAbs_sub_le _ _
    _ ≤ (((12 : ℤ) * a ^ 3).natAbs + ((20 : ℤ) * a * b ^ 2).natAbs)
          + ((27 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ = 12 * a.natAbs ^ 3 + 20 * a.natAbs * b.natAbs ^ 2 + 27 * b.natAbs ^ 3 := by
        rw [e1, e2, e3]
    _ ≤ 59 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono12 a b
        have m3 := mono03 a b
        linarith

/-- Cofactor bound, `a`-side, first cofactor:
`|37a³ + 4a²b − 26ab² + 6b³| ≤ 73·H³`. -/
private theorem c3_bound (a b : ℤ) :
    (37 * a ^ 3 + 4 * a ^ 2 * b - 26 * a * b ^ 2 + 6 * b ^ 3).natAbs
      ≤ 73 * (max a.natAbs b.natAbs) ^ 3 := by
  have h37 : ((37 : ℤ)).natAbs = 37 := rfl
  have h4 : ((4 : ℤ)).natAbs = 4 := rfl
  have h26 : ((26 : ℤ)).natAbs = 26 := rfl
  have h6 : ((6 : ℤ)).natAbs = 6 := rfl
  have e1 : ((37 : ℤ) * a ^ 3).natAbs = 37 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h37]
  have e2 : ((4 : ℤ) * a ^ 2 * b).natAbs = 4 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h4]
  have e3 : ((26 : ℤ) * a * b ^ 2).natAbs = 26 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h26]
  have e4 : ((6 : ℤ) * b ^ 3).natAbs = 6 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h6]
  calc (37 * a ^ 3 + 4 * a ^ 2 * b - 26 * a * b ^ 2 + 6 * b ^ 3).natAbs
      ≤ (37 * a ^ 3 + 4 * a ^ 2 * b - 26 * a * b ^ 2).natAbs + (6 * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ ((37 * a ^ 3 + 4 * a ^ 2 * b).natAbs + ((26 : ℤ) * a * b ^ 2).natAbs)
          + ((6 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
    _ ≤ ((((37 : ℤ) * a ^ 3).natAbs + ((4 : ℤ) * a ^ 2 * b).natAbs)
            + ((26 : ℤ) * a * b ^ 2).natAbs)
          + ((6 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ = 37 * a.natAbs ^ 3 + 4 * a.natAbs ^ 2 * b.natAbs
          + 26 * a.natAbs * b.natAbs ^ 2 + 6 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 73 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- Cofactor bound, `a`-side, second cofactor:
`|−a³ − 12a²b + 14ab² − 6b³| ≤ 33·H³`. -/
private theorem c4_bound (a b : ℤ) :
    (-a ^ 3 - 12 * a ^ 2 * b + 14 * a * b ^ 2 - 6 * b ^ 3).natAbs
      ≤ 33 * (max a.natAbs b.natAbs) ^ 3 := by
  have h12 : ((12 : ℤ)).natAbs = 12 := rfl
  have h14 : ((14 : ℤ)).natAbs = 14 := rfl
  have h6 : ((6 : ℤ)).natAbs = 6 := rfl
  have e0 : ((-a ^ 3 : ℤ)).natAbs = a.natAbs ^ 3 := by
    rw [Int.natAbs_neg, Int.natAbs_pow]
  have e1 : ((12 : ℤ) * a ^ 2 * b).natAbs = 12 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h12]
  have e2 : ((14 : ℤ) * a * b ^ 2).natAbs = 14 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h14]
  have e3 : ((6 : ℤ) * b ^ 3).natAbs = 6 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h6]
  calc (-a ^ 3 - 12 * a ^ 2 * b + 14 * a * b ^ 2 - 6 * b ^ 3).natAbs
      ≤ (-a ^ 3 - 12 * a ^ 2 * b + 14 * a * b ^ 2).natAbs + (6 * b ^ 3).natAbs :=
        Int.natAbs_sub_le _ _
    _ ≤ ((-a ^ 3 - 12 * a ^ 2 * b).natAbs + ((14 : ℤ) * a * b ^ 2).natAbs)
          + ((6 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ (((-a ^ 3).natAbs + ((12 : ℤ) * a ^ 2 * b).natAbs)
            + ((14 : ℤ) * a * b ^ 2).natAbs)
          + ((6 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
    _ = a.natAbs ^ 3 + 12 * a.natAbs ^ 2 * b.natAbs
          + 14 * a.natAbs * b.natAbs ^ 2 + 6 * b.natAbs ^ 3 := by
        rw [e0, e1, e2, e3]
    _ ≤ 33 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- The `b`-branch of the size bound: `37·|b|⁷ ≤ 171·H³·max |F| |D|`. -/
theorem size_bound_b (a b : ℤ) :
    37 * b.natAbs ^ 7
      ≤ 171 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h37 : ((37 : ℤ)).natAbs = 37 := rfl
  have h0 : ((37 : ℤ) * b ^ 7).natAbs = 37 * b.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h37]
  have hterm1 : (((-48 * a ^ 2 + 64 * b ^ 2) * b) * F a b).natAbs
      ≤ 112 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c1_bound a b) (le_max_left _ _)
  have hterm2 : ((12 * a ^ 3 + 20 * a * b ^ 2 - 27 * b ^ 3) * D a b).natAbs
      ≤ 59 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c2_bound a b) (le_max_right _ _)
  calc 37 * b.natAbs ^ 7 = ((37 : ℤ) * b ^ 7).natAbs := h0.symm
    _ = (((-48 * a ^ 2 + 64 * b ^ 2) * b) * F a b
          + (12 * a ^ 3 + 20 * a * b ^ 2 - 27 * b ^ 3) * D a b).natAbs := by
        rw [bezout_b_D a b]
    _ ≤ (((-48 * a ^ 2 + 64 * b ^ 2) * b) * F a b).natAbs
          + ((12 * a ^ 3 + 20 * a * b ^ 2 - 27 * b ^ 3) * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 112 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 59 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 171 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring

/-- The `a`-branch of the size bound: `37·|a|⁷ ≤ 171·H³·max |F| |D|`
(the natural constant is `106`; we relax to `171` to share one constant). -/
theorem size_bound_a (a b : ℤ) :
    37 * a.natAbs ^ 7
      ≤ 171 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h37 : ((37 : ℤ)).natAbs = 37 := rfl
  have h0 : ((37 : ℤ) * a ^ 7).natAbs = 37 * a.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h37]
  have hterm1 : ((37 * a ^ 3 + 4 * a ^ 2 * b - 26 * a * b ^ 2 + 6 * b ^ 3) * F a b).natAbs
      ≤ 73 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c3_bound a b) (le_max_left _ _)
  have hterm2 : ((-a ^ 3 - 12 * a ^ 2 * b + 14 * a * b ^ 2 - 6 * b ^ 3) * D a b).natAbs
      ≤ 33 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c4_bound a b) (le_max_right _ _)
  calc 37 * a.natAbs ^ 7 = ((37 : ℤ) * a ^ 7).natAbs := h0.symm
    _ = ((37 * a ^ 3 + 4 * a ^ 2 * b - 26 * a * b ^ 2 + 6 * b ^ 3) * F a b
          + (-a ^ 3 - 12 * a ^ 2 * b + 14 * a * b ^ 2 - 6 * b ^ 3) * D a b).natAbs := by
        rw [bezout_a a b]
    _ ≤ ((37 * a ^ 3 + 4 * a ^ 2 * b - 26 * a * b ^ 2 + 6 * b ^ 3) * F a b).natAbs
          + ((-a ^ 3 - 12 * a ^ 2 * b + 14 * a * b ^ 2 - 6 * b ^ 3) * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 73 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 33 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 106 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring
    _ ≤ 171 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) le_rfl

/-- **The size lower bound.** For all `a b : ℤ`, with `H = max |a| |b|`:
`37·H⁷ ≤ 171·H³·max |F(a,b)| |D(a,b)|`. This is the quantitative heart of
the duplication height inequality: the duplication fraction cannot collapse
below `H⁴/171` before gcd cancellation. -/
theorem size_bound (a b : ℤ) :
    37 * (max a.natAbs b.natAbs) ^ 7
      ≤ 171 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  rcases le_total a.natAbs b.natAbs with hab | hab
  · have h := size_bound_b a b
    rw [max_eq_right hab] at h ⊢
    exact h
  · have h := size_bound_a a b
    rw [max_eq_left hab] at h ⊢
    exact h

end SizeBound

/-! ## §5 — the division consequence: height survives gcd cancellation -/

section Reduced

/-- `max` distributes over a common right factor in `ℕ`. -/
private theorem max_mul_nat (x y d : ℕ) : max (x * d) (y * d) = max x y * d := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (Nat.mul_le_mul hxy le_rfl)]
  · rw [max_eq_left hxy, max_eq_left (Nat.mul_le_mul hxy le_rfl)]

/-- Splitting `max |x| |y|` along a common divisor `n`:
`max |x| |y| = max |x/n| |y/n| · n`. -/
private theorem max_natAbs_split {x y : ℤ} {n : ℕ}
    (hx : (n : ℤ) ∣ x) (hy : (n : ℤ) ∣ y) :
    max x.natAbs y.natAbs
      = max ((x / (n : ℤ)).natAbs) ((y / (n : ℤ)).natAbs) * n := by
  have ex : (x / (n : ℤ)).natAbs * n = x.natAbs := by
    calc (x / (n : ℤ)).natAbs * n
        = (x / (n : ℤ)).natAbs * ((n : ℤ)).natAbs := by rw [Int.natAbs_natCast]
      _ = ((x / (n : ℤ)) * (n : ℤ)).natAbs := (Int.natAbs_mul _ _).symm
      _ = x.natAbs := by rw [Int.ediv_mul_cancel hx]
  have ey : (y / (n : ℤ)).natAbs * n = y.natAbs := by
    calc (y / (n : ℤ)).natAbs * n
        = (y / (n : ℤ)).natAbs * ((n : ℤ)).natAbs := by rw [Int.natAbs_natCast]
      _ = ((y / (n : ℤ)) * (n : ℤ)).natAbs := (Int.natAbs_mul _ _).symm
      _ = y.natAbs := by rw [Int.ediv_mul_cancel hy]
  rw [← ex, ← ey, max_mul_nat]

/-- Pure-`ℕ` descent arithmetic: from `37·H⁷ ≤ 171·H³·(M·d)` with `d ≤ 37`
and `1 ≤ H`, cancel `H³` to get `37·H⁴ ≤ 171·37·M`. -/
private theorem descend {H M d : ℕ} (hd : d ≤ 37) (hH : 1 ≤ H)
    (hkey : 37 * H ^ 7 ≤ 171 * H ^ 3 * (M * d)) : 37 * H ^ 4 ≤ 171 * 37 * M := by
  have hH0 : 0 < H := hH
  have h2 : (37 * H ^ 4) * H ^ 3 ≤ (171 * 37 * M) * H ^ 3 := by
    calc (37 * H ^ 4) * H ^ 3 = 37 * H ^ 7 := by ring
      _ ≤ 171 * H ^ 3 * (M * d) := hkey
      _ ≤ 171 * H ^ 3 * (M * 37) := Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hd)
      _ = (171 * 37 * M) * H ^ 3 := by ring
  exact Nat.le_of_mul_le_mul_right h2 (pow_pos hH0 3)

/-- **The reduced height bound.** For coprime `a b` with `b ≠ 0`, after
dividing the duplication pair `(F, D)` by `gcd(F, D)` (which divides `37` by
`gcd_dvd_37`), the reduced max still dominates the fourth power of the input
height: `37·H⁴ ≤ 171·37·max |F/g| |D/g|`, i.e. the reduced max is
`≥ H⁴/171` (κ = 171·37 = 6327 in the κ·M-form).

The hypothesis `_hD : D a b ≠ 0` is not needed by this proof (the bound is
vacuously safe when `D = 0` forces `F = 0`, which `size_bound` rules out for
`H ≥ 1`), but is kept in the signature because B4 discharges it anyway
(2-torsion-freeness of 37a1 over ℚ) and downstream applies positionally. -/
theorem reduced_height_bound {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (_hD : D a b ≠ 0) :
    37 * (max a.natAbs b.natAbs) ^ 4
      ≤ 171 * 37 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have hd37 : Int.gcd (F a b) (D a b) ≤ 37 :=
    Nat.le_of_dvd (by norm_num) (gcd_dvd_37_nat h)
  have hH1 : 1 ≤ max a.natAbs b.natAbs :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb))
      (le_max_right _ _)
  have hsplit :=
    max_natAbs_split (n := Int.gcd (F a b) (D a b))
      (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  have key := size_bound a b
  rw [hsplit] at key
  exact descend hd37 hH1 key

/-- `reduced_height_bound` with the common factor `37` cancelled:
`H⁴ ≤ 171·max |F/g| |D/g|`. Cleanest form for B4. -/
theorem reduced_height_bound' {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 171 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have key := reduced_height_bound h hb hD
  have key2 : 37 * (max a.natAbs b.natAbs) ^ 4
      ≤ 37 * (171 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by
    calc 37 * (max a.natAbs b.natAbs) ^ 4
        ≤ 171 * 37 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := key
      _ = 37 * (171 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by ring
  exact Nat.le_of_mul_le_mul_left key2 (by norm_num)

end Reduced

end PrincipiaTractalis.DuplicationBezout37a1

#print axioms PrincipiaTractalis.DuplicationBezout37a1.bezout_b
#print axioms PrincipiaTractalis.DuplicationBezout37a1.bezout_a
#print axioms PrincipiaTractalis.DuplicationBezout37a1.bezout_b_D
#print axioms PrincipiaTractalis.DuplicationBezout37a1.gcd_dvd_37
#print axioms PrincipiaTractalis.DuplicationBezout37a1.size_bound
#print axioms PrincipiaTractalis.DuplicationBezout37a1.reduced_height_bound
#print axioms PrincipiaTractalis.DuplicationBezout37a1.reduced_height_bound'
