/-
# PF.QuasiParallelogramCerts389a1_r148a

★★★ 2026-07-28 — r148a: THE CERTIFICATE LAYER OF THE QUASI-PARALLELOGRAM ★★★

The `ring`-certified algebraic core of stone W2 (see
`codex/W2_CERTIFICATES_389a1.md`, all sympy-verified with 42 PASS
assertions).  The bihomogeneous addition forms for 389a1 and the level-1
Cramer certificates: at coprime coordinate pairs, the gcd of the three
forms divides `R6(a₂,b₂)` — the first half of the content control
`gcd(DD,S,P) ∣ 389³` that the quasi-parallelogram inequality (r148, to
come) consumes.

HONEST SCOPE.  Polynomial identities and their immediate gcd consequence
only.  No height inequality, no parallelogram law, no rank statement.

Kernel axioms `[propext, Classical.choice, Quot.sound]` (identities are
axiom-lighter); no `sorry`, no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace PrincipiaTractalis.QuasiParallelogramCerts389a1

/-! ## §1 — the bihomogeneous addition forms (bidegree (2,2)) -/

/-- `DD = (a₁b₂ − a₂b₁)²` — the denominator form of the addition quadratic. -/
def DD (a₁ b₁ a₂ b₂ : ℤ) : ℤ := (a₁ * b₂ - a₂ * b₁) ^ 2

/-- `Sf` — homogenization of `x₃ + x₄` numerator (the sum form). -/
def Sf (a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  2 * a₁ ^ 2 * a₂ * b₂ + 2 * a₁ * a₂ ^ 2 * b₁ + 4 * a₁ * a₂ * b₁ * b₂
    - 4 * a₁ * b₁ * b₂ ^ 2 - 4 * a₂ * b₁ ^ 2 * b₂ + b₁ ^ 2 * b₂ ^ 2

/-- `Pf` — homogenization of `x₃ · x₄` numerator (the product form). -/
def Pf (a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  a₁ ^ 2 * a₂ ^ 2 + 4 * a₁ * a₂ * b₁ * b₂ - a₁ * b₁ * b₂ ^ 2
    - a₂ * b₁ ^ 2 * b₂ + 3 * b₁ ^ 2 * b₂ ^ 2

/-- The control sextic `R6` (irreducible over ℚ): the determinant of the
`(a₁,b₁)`-coefficient matrix of `(DD, Sf, Pf)`. -/
def R6 (a b : ℤ) : ℤ :=
  2 * a ^ 6 + 4 * a ^ 5 * b - 20 * a ^ 4 * b ^ 2 + 10 * a ^ 3 * b ^ 3
    - 30 * a ^ 2 * b ^ 4 - 8 * a * b ^ 5 + 11 * b ^ 6

/-! ## §2 — sanity: the diagonal degenerates to the duplication data

`Sf(a,b,a,b) = b·G3(a,b)` and `Pf(a,b,a,b) = F(a,b)` with r143's forms —
the structural check tying addition to duplication. -/

theorem Sf_diagonal (a b : ℤ) :
    Sf a b a b = b * (4 * a ^ 3 + 4 * a ^ 2 * b - 8 * a * b ^ 2 + b ^ 3) := by
  simp only [Sf]; ring

theorem Pf_diagonal (a b : ℤ) :
    Pf a b a b = a ^ 4 + 4 * a ^ 2 * b ^ 2 - 2 * a * b ^ 3 + 3 * b ^ 4 := by
  simp only [Pf]; ring

/-! ## §3 — the level-1 Cramer certificates (sympy-verified, `ring`-certified) -/

/-- **cert1**: eliminates `(a₁, b₁)` down to `R6(a₂,b₂)·b₁²`. -/
theorem cert_b1 (a₁ b₁ a₂ b₂ : ℤ) :
    (2 * a₂ ^ 4 + 4 * a₂ ^ 3 * b₂ - 12 * a₂ ^ 2 * b₂ ^ 2 + 2 * a₂ * b₂ ^ 3)
        * DD a₁ b₁ a₂ b₂
      + (2 * a₂ ^ 3 * b₂ + 4 * a₂ * b₂ ^ 3 - b₂ ^ 4) * Sf a₁ b₁ a₂ b₂
      + (-6 * a₂ ^ 2 * b₂ ^ 2 - 4 * a₂ * b₂ ^ 3 + 4 * b₂ ^ 4) * Pf a₁ b₁ a₂ b₂
      = R6 a₂ b₂ * b₁ ^ 2 := by
  simp only [DD, Sf, Pf, R6]; ring

/-- **cert2**: eliminates `(a₁, b₁)` down to `R6(a₂,b₂)·a₁²`. -/
theorem cert_a1 (a₁ b₁ a₂ b₂ : ℤ) :
    (2 * a₂ ^ 3 * b₂ - 18 * a₂ ^ 2 * b₂ ^ 2 - 8 * a₂ * b₂ ^ 3 + 11 * b₂ ^ 4)
        * DD a₁ b₁ a₂ b₂
      + (-4 * a₂ ^ 3 * b₂ + 3 * a₂ ^ 2 * b₂ ^ 2 - 6 * a₂ * b₂ ^ 3) * Sf a₁ b₁ a₂ b₂
      + (2 * a₂ ^ 4 + 4 * a₂ ^ 3 * b₂ - 12 * a₂ ^ 2 * b₂ ^ 2 + 2 * a₂ * b₂ ^ 3)
          * Pf a₁ b₁ a₂ b₂
      = R6 a₂ b₂ * a₁ ^ 2 := by
  simp only [DD, Sf, Pf, R6]; ring

/-! ## §4 — the gcd consequence: content divides `R6(a₂,b₂)` -/

/-- **The level-1 content bound.** For `(a₁, b₁)` coprime, any common
divisor of the three addition forms divides `R6(a₂, b₂)` — in particular
the gcd does.  (Level 2 — `R6`'s own control by `389³` via the F/G3
certificates — composes with r143's layer in the full r148.) -/
theorem dvd_R6_of_dvd_forms {a₁ b₁ a₂ b₂ d : ℤ} (h : IsCoprime a₁ b₁)
    (hDD : d ∣ DD a₁ b₁ a₂ b₂) (hS : d ∣ Sf a₁ b₁ a₂ b₂)
    (hP : d ∣ Pf a₁ b₁ a₂ b₂) : d ∣ R6 a₂ b₂ := by
  have hb : d ∣ R6 a₂ b₂ * b₁ ^ 2 := by
    rw [← cert_b1 a₁ b₁ a₂ b₂]
    exact dvd_add (dvd_add (hDD.mul_left _) (hS.mul_left _)) (hP.mul_left _)
  have ha : d ∣ R6 a₂ b₂ * a₁ ^ 2 := by
    rw [← cert_a1 a₁ b₁ a₂ b₂]
    exact dvd_add (dvd_add (hDD.mul_left _) (hS.mul_left _)) (hP.mul_left _)
  have h22 : IsCoprime (a₁ ^ 2) (b₁ ^ 2) := h.pow
  obtain ⟨u, v, huv⟩ := h22
  have key : R6 a₂ b₂ = u * (R6 a₂ b₂ * a₁ ^ 2) + v * (R6 a₂ b₂ * b₁ ^ 2) := by
    linear_combination (-(R6 a₂ b₂) : ℤ) * huv
  rw [key]
  exact dvd_add (ha.mul_left u) (hb.mul_left v)

end PrincipiaTractalis.QuasiParallelogramCerts389a1

#print axioms PrincipiaTractalis.QuasiParallelogramCerts389a1.cert_b1
#print axioms PrincipiaTractalis.QuasiParallelogramCerts389a1.cert_a1
#print axioms PrincipiaTractalis.QuasiParallelogramCerts389a1.dvd_R6_of_dvd_forms
