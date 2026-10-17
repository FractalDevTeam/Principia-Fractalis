/-
# PF.Ch24Descent2TorsionBookkeeping_2026_10_17

**The two bookkeeping layers on top of `descent_core` (5ea7e0e9).**

`descent_core` proved the arithmetic heart: for `e ≠ 0` and `m` coprime to `e`,
`n² = m(m² + e⁴)` forces `m = 0`. This file supplies the two layers that turn
that into a rank statement.

## Layer 1 — lowest-terms form (§2)

`descent_lowest_terms` : for integers `a, b, Y` with `b > 0`, `a` coprime to `b`,

    `Y² = a·b·(a² + b²)  →  a = 0`.

This is the shape a rational point takes after clearing denominators: writing
`x = a/b` in lowest terms and multiplying `y² = x³ + x` through by `b⁴` gives
exactly `(b²y)² = ab(a² + b²)`.

**Why this shape rather than the textbook one.** The usual presentation writes
`x = m/e²` and needs "`b³` a square ⟹ `b` a square", i.e. a coprime-exponent
argument. Multiplying by `b⁴` instead keeps everything inside the
coprime-factors-with-square-product lemma already used by `descent_core`:
`ab` and `a²+b²` are coprime, so each is a square; then `a` and `b` are coprime
with square product, so **each of them** is a square — which *is* the
denominator-is-a-square fact, obtained for free. The proof then closes by
feeding `m = a`, `e = v` (where `b = v²`) to `descent_core`.

## Layer 2 — rank zero from 2-torsion (§3)

`rank_eq_zero_of_two_torsion` : for any `ℤ`-module all of whose elements are
killed by `2`, `Module.rank ℤ M = 0`. Stated generically; it is the step from
"every point is 2-torsion" to the rank statement, via mathlib's
`rank_eq_zero_iff`.

**Implementation note.** The hypothesis is written `P + P = 0` rather than
`(2 : ℤ) • P = 0` deliberately. An `AddCommGroup M` with `[Module ℤ M]` carries
*two* ℤ-scalar actions — `SubNegMonoid.toZSMul` and the `Module` one — which are
definitionally equal but not syntactically, and the elaborator picks the
former in a hypothesis while the goal wants the latter. The additive form is
instance-free and sidesteps the mismatch; `two_smul` bridges it inside the
proof.

## The one remaining interface, stated precisely rather than implied

Connecting §2 to `E(ℚ)` for `E : y² = x³ + x` still needs the `Rat`-level step:
that a rational point gives `a = x.num`, `b = x.den`, `Y = b²y` with `Y` an
**integer** (its square is an integer, and `ℤ` is integrally closed in `ℚ`).
That is `Rat.num`/`Rat.den` bookkeeping, not arithmetic, and it is **not done
here** — so this file does *not* yet yield `Module.rank ℤ E(ℚ) = 0`. What it
yields is both halves with a named gap between them.

Three-axiom bar: `[propext, Classical.choice, Quot.sound]`. No `sorry`,
no `axiom`, no `native_decide`.

Author: Pablo Cohen + Claude Opus 5. 2026-10-17.
-/
import PF.Ch24Descent2TorsionCore_2026_10_17
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.RingTheory.Int.Basic

namespace PrincipiaTractalis.Ch24DescentBookkeeping20261017

open PrincipiaTractalis.Ch24Descent20261017

/-! ## §1 — coprimality bookkeeping -/

/-- From `IsCoprime a b` and `b > 0`, the two descent factors `a*b` and
`a² + b²` are coprime. -/
theorem isCoprime_prod_sumSq {a b : ℤ} (hco : IsCoprime a b) :
    IsCoprime (a * b) (a ^ 2 + b ^ 2) := by
  have ha : IsCoprime a (a ^ 2 + b ^ 2) := by
    have h2 : IsCoprime a (b ^ 2) := hco.pow_right
    have := h2.add_mul_left_right a
    have hEq : b ^ 2 + a * a = a ^ 2 + b ^ 2 := by ring
    rwa [hEq] at this
  have hb : IsCoprime b (a ^ 2 + b ^ 2) := by
    have h2 : IsCoprime b (a ^ 2) := (hco.symm).pow_right
    have := h2.add_mul_left_right b
    have hEq : a ^ 2 + b * b = a ^ 2 + b ^ 2 := by ring
    rwa [hEq] at this
  exact ha.mul_left hb

/-- If `IsCoprime x (y ^ n)` with `n ≠ 0` then `IsCoprime x y`
(Bézout, directly). -/
theorem isCoprime_of_isCoprime_pow_right {x y : ℤ} (h : IsCoprime x (y ^ 2)) :
    IsCoprime x y := by
  obtain ⟨p, q, hpq⟩ := h
  exact ⟨p, q * y, by linear_combination hpq⟩

/-! ## §2 — Layer 1: the lowest-terms form -/

/-- **Layer 1.** The lowest-terms shape of a rational point on `y² = x³ + x`:
with `x = a/b` reduced and `Y = b²y`, the curve equation becomes
`Y² = ab(a² + b²)`, and that forces `a = 0`.

Closes by reducing to `descent_core`. -/
theorem descent_lowest_terms {a b Y : ℤ} (hb : 0 < b) (hco : IsCoprime a b)
    (h : Y ^ 2 = a * b * (a ^ 2 + b ^ 2)) : a = 0 := by
  by_contra ha
  -- the sum of squares is positive
  have hsum : 0 < a ^ 2 + b ^ 2 := by positivity
  -- `a * b ≥ 0`, because `Y² ≥ 0` and the other factor is positive
  have hab_nonneg : 0 ≤ a * b := by
    rcases le_or_gt 0 (a * b) with hle | hlt
    · exact hle
    · exfalso
      have : a * b * (a ^ 2 + b ^ 2) < 0 := mul_neg_of_neg_of_pos hlt hsum
      have h0 : (0 : ℤ) ≤ Y ^ 2 := sq_nonneg Y
      linarith [h ▸ h0]
  -- `a ≠ 0` and `b > 0` give `a * b ≠ 0`, hence `a * b > 0`, hence `a > 0`
  have hab_pos : 0 < a * b := by
    rcases hab_nonneg.lt_or_eq with hpos | heq
    · exact hpos
    · exact absurd (by
        rcases mul_eq_zero.mp heq.symm with h1 | h2
        · exact h1
        · exact absurd h2 hb.ne') ha
  have hapos : 0 < a := by
    by_contra hle
    push_neg at hle
    nlinarith [hab_pos, hb]
  -- split `a * b * (a² + b²) = Y²` into two squares
  have hcf : IsCoprime (a * b) (a ^ 2 + b ^ 2) := isCoprime_prod_sumSq hco
  have hmul : a * b * (a ^ 2 + b ^ 2) = Y ^ 2 := h.symm
  obtain ⟨t, ht⟩ := exists_associated_pow_of_mul_eq_pow' hcf.symm
    (by linarith [hmul] : (a ^ 2 + b ^ 2) * (a * b) = Y ^ 2)
  have htsq : a ^ 2 + b ^ 2 = t ^ 2 := by
    rcases Int.associated_iff.mp ht with hc | hc
    · exact hc.symm
    · exfalso; have := sq_nonneg t; omega
  -- `a` and `b` are coprime with square product, so each is a square
  obtain ⟨s, hs⟩ := exists_associated_pow_of_mul_eq_pow' hcf hmul
  have hssq : a * b = s ^ 2 := by
    rcases Int.associated_iff.mp hs with hc | hc
    · exact hc.symm
    · exfalso; have := sq_nonneg s; omega
  obtain ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hco hssq
  obtain ⟨v, hv⟩ := exists_associated_pow_of_mul_eq_pow' hco.symm
    (by linarith [hssq] : b * a = s ^ 2)
  have hasq : a = u ^ 2 := by
    rcases Int.associated_iff.mp hu with hc | hc
    · exact hc.symm
    · exfalso; have := sq_nonneg u; omega
  have hbsq : b = v ^ 2 := by
    rcases Int.associated_iff.mp hv with hc | hc
    · exact hc.symm
    · exfalso; have := sq_nonneg v; omega
  -- now feed `descent_core` with `m = a`, `e = v`, `n = u * t`
  have hv0 : v ≠ 0 := by
    intro hvz; rw [hvz] at hbsq; simp at hbsq; omega
  have hcoae : IsCoprime a v := by
    refine isCoprime_of_isCoprime_pow_right ?_
    rw [← hbsq]; exact hco
  have hkey : (u * t) ^ 2 = a * (a ^ 2 + v ^ 4) := by
    have hb4 : v ^ 4 = b ^ 2 := by rw [hbsq]; ring
    rw [hb4, htsq, hasq]
    ring
  exact ha (descent_core hv0 hcoae hkey)

/-! ## §3 — Layer 2: rank zero from 2-torsion -/

/-- **Layer 2.** A `ℤ`-module in which every element is killed by `2` has
rank `0`. This is the step from "every point is 2-torsion" to the rank
statement. -/
theorem rank_eq_zero_of_two_torsion {M : Type*} [AddCommGroup M] [Module ℤ M]
    (h : ∀ P : M, P + P = 0) : Module.rank ℤ M = 0 := by
  rw [rank_eq_zero_iff]
  intro P
  refine ⟨2, by norm_num, ?_⟩
  rw [two_smul]
  exact h P

end PrincipiaTractalis.Ch24DescentBookkeeping20261017
