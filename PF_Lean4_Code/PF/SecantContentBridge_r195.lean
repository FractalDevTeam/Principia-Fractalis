/-
# PF.SecantContentBridge_r195

★★★ 2026-08-04 — THE SECANT CONTENT PROBLEM REDUCES TO THE r174 KEYSTONE ★★★

The missing half of the universal secant chain (after r193's size bounds) is
the content bound: a universal divisor bound for `gcd(DDz, Sfz, Prz)`.  This
stone proves the structural reduction that makes it possible — in TWO moves:

**1. Diagonal degeneration.**  On the diagonal `(a₂,b₂) = (a₁,b₁)` the secant
forms ARE the duplication forms of r174:

  `Sfz(a,b,a,b) = Psi(a,b)`,    `Prz(a,b,a,b) = Phi(a,b)`.

The secant chain literally lands on the objects whose resultant keystone
`Res(Φ,Ψ) = Δ²` closed the duplication content problem.

**2. Elimination certificates.**  Eliminating the second point against the
denominator form `DDz = (a₁b₂ − a₂b₁)²` produces exactly the SQUARES of the
duplication pair at the first point, with small integer Bézout cofactors
(sympy-derived from the x₂-resultants `Res(DD,Sf) = ψ(x₁)²`,
`Res(DD,Pr) = φ(x₁)²`, then bihomogenized and re-verified):

  `sfCert₁·DDz + sfCert₂·Sfz = b₂³·Psi(a₁,b₁)²`
  `prCert₁·DDz + prCert₂·Prz = b₂³·Phi(a₁,b₁)²`

Consequence (`dvd_b2_psi_sq` … and the swapped versions, since all three
forms are symmetric in the two points): any common divisor of the secant
triple divides `b₂³·Psi₁²`, `b₂³·Phi₁²`, `b₁³·Psi₂²`, `b₁³·Phi₂²`.  Chaining
with r174's `dvd_disc_sq_of_isCoprime` (which bounds common divisors of
`(Phi, Psi)` by `Δ²` under coprimality) and the coprime-corner bookkeeping
will give the universal secant content bound `gcd ∣ Δ`-power — that
composition is the next stone (r196); it is bookkeeping on top of what is
proved here, not new certificates.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-04.
-/
import PF.SecantSizeUniversal_r193
import PF.DuplicationBezoutUniversal_r174

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.SecantContentBridge

open PrincipiaTractalis.SecantSizeUniversal
open PrincipiaTractalis.DuplicationBezout

/-! ### §1 — the forms are symmetric in the two points -/

theorem DDz_swap (a₁ b₁ a₂ b₂ : ℤ) :
    DDz a₁ b₁ a₂ b₂ = DDz a₂ b₂ a₁ b₁ := by
  rw [DDz, DDz]; ring

theorem Sfz_swap (B₂ B₄ B₆ a₁ b₁ a₂ b₂ : ℤ) :
    Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂ = Sfz B₂ B₄ B₆ a₂ b₂ a₁ b₁ := by
  rw [Sfz, Sfz]; ring

theorem Prz_swap (B₄ B₆ B₈ a₁ b₁ a₂ b₂ : ℤ) :
    Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂ = Prz B₄ B₆ B₈ a₂ b₂ a₁ b₁ := by
  rw [Prz, Prz]; ring

/-! ### §2 — diagonal degeneration: the secant forms ARE the r174 pair -/

/-- On the diagonal, the secant sum form is r174's duplication denominator. -/
theorem Sfz_diag (B₂ B₄ B₆ a b : ℤ) :
    Sfz B₂ B₄ B₆ a b a b = Psi B₂ B₄ B₆ a b := by
  rw [Sfz, Psi]; ring

/-- On the diagonal, the secant product form is r174's duplication
numerator. -/
theorem Prz_diag (B₄ B₆ B₈ a b : ℤ) :
    Prz B₄ B₆ B₈ a b a b = Phi B₄ B₆ B₈ a b := by
  rw [Prz, Phi]; ring

/-- The diagonal denominator vanishes — the secant honestly degenerates. -/
theorem DDz_diag (a b : ℤ) : DDz a b a b = 0 := by
  rw [DDz]; ring

/-! ### §3 — the elimination certificates (sympy-derived, ring-verified) -/

/-- First Bézout cofactor for the `Psi²` certificate. -/
def sfCert₁ (B₂ B₄ B₆ a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  B₂^2*a₁^2*b₁^4*b₂ + 2*B₂*B₄*a₁*b₁^5*b₂ + 8*B₂*a₁^3*b₁^3*b₂
    + 2*B₂*a₁^2*a₂*b₁^4 + B₄^2*b₁^6*b₂ + 6*B₄*a₁^2*b₁^4*b₂
    + 2*B₄*a₁*a₂*b₁^5 - 2*B₆*a₁*b₁^5*b₂ + 16*a₁^4*b₁^2*b₂
    + 12*a₁^3*a₂*b₁^3

/-- Second Bézout cofactor for the `Psi²` certificate. -/
def sfCert₂ (B₂ B₄ B₆ a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  2*B₂*a₁^2*b₁^4*b₂ - B₂*a₁*a₂*b₁^5 + 3*B₄*a₁*b₁^5*b₂ - B₄*a₂*b₁^6
    + B₆*b₁^6*b₂ + 10*a₁^3*b₁^3*b₂ - 6*a₁^2*a₂*b₁^4

/-- First Bézout cofactor for the `Phi²` certificate. -/
def prCert₁ (B₄ B₆ B₈ a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  B₄^2*a₁^2*b₁^4*b₂ + 2*B₄*B₆*a₁*b₁^5*b₂ - 2*B₄*a₁^4*b₁^2*b₂
    - B₄*a₁^3*a₂*b₁^3 + B₆^2*b₁^6*b₂ - B₆*a₁^3*b₁^3*b₂
    - B₆*a₁^2*a₂*b₁^4 + B₈*a₁^2*b₁^4*b₂ + a₁^6*b₂ + 2*a₁^5*a₂*b₁

/-- Second Bézout cofactor for the `Phi²` certificate. -/
def prCert₂ (B₄ B₆ B₈ a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  -2*B₄*a₁^2*b₁^4*b₂ + B₄*a₁*a₂*b₁^5 - 3*B₆*a₁*b₁^5*b₂ + B₆*a₂*b₁^6
    - B₈*b₁^6*b₂ + 3*a₁^4*b₁^2*b₂ - 2*a₁^3*a₂*b₁^3

/-- **The `Psi²` certificate**: eliminating the second point from
`(DDz, Sfz)` produces the square of the duplication denominator at the
first point. -/
theorem psi_sq_cert (B₂ B₄ B₆ a₁ b₁ a₂ b₂ : ℤ) :
    sfCert₁ B₂ B₄ B₆ a₁ b₁ a₂ b₂ * DDz a₁ b₁ a₂ b₂
      + sfCert₂ B₂ B₄ B₆ a₁ b₁ a₂ b₂ * Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂
      = b₂ ^ 3 * (Psi B₂ B₄ B₆ a₁ b₁) ^ 2 := by
  rw [sfCert₁, sfCert₂, DDz, Sfz, Psi]; ring

/-- **The `Phi²` certificate**: eliminating the second point from
`(DDz, Prz)` produces the square of the duplication numerator at the
first point. -/
theorem phi_sq_cert (B₄ B₆ B₈ a₁ b₁ a₂ b₂ : ℤ) :
    prCert₁ B₄ B₆ B₈ a₁ b₁ a₂ b₂ * DDz a₁ b₁ a₂ b₂
      + prCert₂ B₄ B₆ B₈ a₁ b₁ a₂ b₂ * Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂
      = b₂ ^ 3 * (Phi B₄ B₆ B₈ a₁ b₁) ^ 2 := by
  rw [prCert₁, prCert₂, DDz, Prz, Phi]; ring

/-! ### §4 — divisor transport: common divisors of the secant triple
divide the duplication squares -/

theorem dvd_b2_psi_sq {B₂ B₄ B₆ a₁ b₁ a₂ b₂ d : ℤ}
    (h₁ : d ∣ DDz a₁ b₁ a₂ b₂) (h₂ : d ∣ Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂) :
    d ∣ b₂ ^ 3 * (Psi B₂ B₄ B₆ a₁ b₁) ^ 2 := by
  rw [← psi_sq_cert]
  exact dvd_add (h₁.mul_left _) (h₂.mul_left _)

theorem dvd_b2_phi_sq {B₄ B₆ B₈ a₁ b₁ a₂ b₂ d : ℤ}
    (h₁ : d ∣ DDz a₁ b₁ a₂ b₂) (h₂ : d ∣ Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂) :
    d ∣ b₂ ^ 3 * (Phi B₄ B₆ B₈ a₁ b₁) ^ 2 := by
  rw [← phi_sq_cert]
  exact dvd_add (h₁.mul_left _) (h₂.mul_left _)

/-- The swapped version: the same divisor also controls the duplication
denominator at the SECOND point (with the first point's `b₁³`). -/
theorem dvd_b1_psi_sq {B₂ B₄ B₆ a₁ b₁ a₂ b₂ d : ℤ}
    (h₁ : d ∣ DDz a₁ b₁ a₂ b₂) (h₂ : d ∣ Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂) :
    d ∣ b₁ ^ 3 * (Psi B₂ B₄ B₆ a₂ b₂) ^ 2 := by
  rw [DDz_swap] at h₁
  rw [Sfz_swap] at h₂
  exact dvd_b2_psi_sq h₁ h₂

theorem dvd_b1_phi_sq {B₄ B₆ B₈ a₁ b₁ a₂ b₂ d : ℤ}
    (h₁ : d ∣ DDz a₁ b₁ a₂ b₂) (h₂ : d ∣ Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂) :
    d ∣ b₁ ^ 3 * (Phi B₄ B₆ B₈ a₂ b₂) ^ 2 := by
  rw [DDz_swap] at h₁
  rw [Prz_swap] at h₂
  exact dvd_b2_phi_sq h₁ h₂

/-- **The bridge, packaged**: a common divisor of the full secant triple
divides all four transported duplication squares.  r196 chains these with
r174's `dvd_disc_sq_of_isCoprime` and coprimality bookkeeping to get the
universal content bound. -/
theorem secant_divisor_bridge {B₂ B₄ B₆ B₈ a₁ b₁ a₂ b₂ d : ℤ}
    (h₁ : d ∣ DDz a₁ b₁ a₂ b₂) (h₂ : d ∣ Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂)
    (h₃ : d ∣ Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂) :
    (d ∣ b₂ ^ 3 * (Psi B₂ B₄ B₆ a₁ b₁) ^ 2)
      ∧ (d ∣ b₂ ^ 3 * (Phi B₄ B₆ B₈ a₁ b₁) ^ 2)
      ∧ (d ∣ b₁ ^ 3 * (Psi B₂ B₄ B₆ a₂ b₂) ^ 2)
      ∧ (d ∣ b₁ ^ 3 * (Phi B₄ B₆ B₈ a₂ b₂) ^ 2) :=
  ⟨dvd_b2_psi_sq h₁ h₂, dvd_b2_phi_sq h₁ h₃,
    dvd_b1_psi_sq h₁ h₂, dvd_b1_phi_sq h₁ h₃⟩

end PrincipiaTractalis.SecantContentBridge

#print axioms PrincipiaTractalis.SecantContentBridge.Sfz_diag
#print axioms PrincipiaTractalis.SecantContentBridge.Prz_diag
#print axioms PrincipiaTractalis.SecantContentBridge.psi_sq_cert
#print axioms PrincipiaTractalis.SecantContentBridge.phi_sq_cert
#print axioms PrincipiaTractalis.SecantContentBridge.secant_divisor_bridge
