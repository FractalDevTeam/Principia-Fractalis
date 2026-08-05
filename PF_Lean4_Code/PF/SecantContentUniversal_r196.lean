/-
# PF.SecantContentUniversal_r196

★★★ 2026-08-04 — THE UNIVERSAL SECANT CONTENT BOUND ★★★

The composition stone on top of r195's bridge: for `x₁ = a₁/b₁`, `x₂ = a₂/b₂`
in lowest terms, on any Weierstrass curve (b-relation `4b₈ = b₂b₆ − b₄²`),

  **`gcd(DDz, Sfz, Prz) ∣ Δ⁶`**  (`secant_content_universal`).

This is the secant-side analogue of r174's duplication content bound
`gcd(Φ,Ψ) ∣ Δ²` — the last hard certificate layer of the universal
quasi-parallelogram chain.  What r148b/r158 proved per curve (389³ for 389a1,
an extra HNF argument for 5077a1), this proves once, for every curve, from
coefficients alone.  The exponent 6 is the honest price of uniformity (the
cubing of the r174 Bézout identity; per-curve sharpening remains possible,
as with r175's κ).

Route:
1. **Twin certificates** (`psi_sq_certA`, `phi_sq_certA`, sympy-derived,
   ring-verified): the `a₂³`-weighted mates of r195's `b₂³`-weighted
   certificates — Sylvester gives the resultant both monomial weights.
2. **Corner elimination** (`dvd_of_dvd_coprime_weights`): with
   `gcd(a₂,b₂) = 1`, the two weights cancel — any common divisor `d` of the
   secant triple divides `Psi(a₁,b₁)²` and `Phi(a₁,b₁)²` outright.
3. **Cube composition** (`dvd_cube_of_bezout`): cubing r174's Bézout
   identity `F₁Φ + G₁Ψ = Δ²X⁷` puts every term in `(Φ², Ψ²)` — the squaring
   trick — so `d ∣ Δ⁶a₁²¹` and `d ∣ Δ⁶b₁²¹`.
4. **Coprime finish**: `gcd(a₁,b₁) = 1` cancels the monomials: `d ∣ Δ⁶`.

Validation: 300 random coprime pairs on each of 389a1 (Δ = 389) and 5077a1
(Δ = 5077): the bound holds; the observed gcd was 1 in every sample.

What remains for #43 after this stone: secant lower size bounds (from these
certificates, r175-style), the universal quasi-parallelogram window
(assemble with r193's upper bounds + r148e's quadratic-root heights), and
the limit passage into r171's generic canonical height = coefficient-only
bi-additivity and the universal rank pipeline.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-04.
-/
import PF.SecantContentBridge_r195

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.SecantContentUniversal

open PrincipiaTractalis.SecantSizeUniversal
open PrincipiaTractalis.SecantContentBridge
open PrincipiaTractalis.DuplicationBezout

/-! ### §1 — the `a₂³`-weighted twin certificates -/

def sfCertA₁ (B₂ B₄ B₆ a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  B₂^2*a₁^4*a₂*b₁^2 + B₂*B₄*a₁^4*b₁^2*b₂ + 4*B₂*B₄*a₁^3*a₂*b₁^3
    + B₂*B₆*a₁^3*b₁^3*b₂ + 2*B₂*B₆*a₁^2*a₂*b₁^4 + 4*B₂*a₁^5*a₂*b₁
    + 3*B₄^2*a₁^3*b₁^3*b₂ + 4*B₄^2*a₁^2*a₂*b₁^4 + 5*B₄*B₆*a₁^2*b₁^4*b₂
    + 4*B₄*B₆*a₁*a₂*b₁^5 + 2*B₄*a₁^5*b₁*b₂ + 6*B₄*a₁^4*a₂*b₁^2
    + 2*B₆^2*a₁*b₁^5*b₂ + B₆^2*a₂*b₁^6 + 2*B₆*a₁^4*b₁^2*b₂
    + 2*B₆*a₁^3*a₂*b₁^3 + 4*a₁^6*a₂

def sfCertA₂ (B₂ B₄ B₆ a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  -B₂*a₁^5*b₁*b₂ + 2*B₂*a₁^4*a₂*b₁^2 - 3*B₄*a₁^4*b₁^2*b₂
    + 5*B₄*a₁^3*a₂*b₁^3 - 2*B₆*a₁^3*b₁^3*b₂ + 3*B₆*a₁^2*a₂*b₁^4
    - 2*a₁^6*b₂ + 6*a₁^5*a₂*b₁

def prCertA₁ (B₄ B₆ B₈ a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  B₄^2*a₁^4*a₂*b₁^2 + B₄*B₆*a₁^4*b₁^2*b₂ + 4*B₄*B₆*a₁^3*a₂*b₁^3
    + B₄*B₈*a₁^3*b₁^3*b₂ + 2*B₄*B₈*a₁^2*a₂*b₁^4 + 3*B₆^2*a₁^3*b₁^3*b₂
    + 4*B₆^2*a₁^2*a₂*b₁^4 + 5*B₆*B₈*a₁^2*b₁^4*b₂ + 4*B₆*B₈*a₁*a₂*b₁^5
    + B₆*a₁^5*a₂*b₁ + 2*B₈^2*a₁*b₁^5*b₂ + B₈^2*a₂*b₁^6 + B₈*a₁^4*a₂*b₁^2

def prCertA₂ (B₄ B₆ B₈ a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  B₄*a₁^5*b₁*b₂ - 2*B₄*a₁^4*a₂*b₁^2 + 3*B₆*a₁^4*b₁^2*b₂
    - 5*B₆*a₁^3*a₂*b₁^3 + 2*B₈*a₁^3*b₁^3*b₂ - 3*B₈*a₁^2*a₂*b₁^4 + a₁^6*a₂

theorem psi_sq_certA (B₂ B₄ B₆ a₁ b₁ a₂ b₂ : ℤ) :
    sfCertA₁ B₂ B₄ B₆ a₁ b₁ a₂ b₂ * DDz a₁ b₁ a₂ b₂
      + sfCertA₂ B₂ B₄ B₆ a₁ b₁ a₂ b₂ * Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂
      = a₂ ^ 3 * (Psi B₂ B₄ B₆ a₁ b₁) ^ 2 := by
  rw [sfCertA₁, sfCertA₂, DDz, Sfz, Psi]; ring

theorem phi_sq_certA (B₄ B₆ B₈ a₁ b₁ a₂ b₂ : ℤ) :
    prCertA₁ B₄ B₆ B₈ a₁ b₁ a₂ b₂ * DDz a₁ b₁ a₂ b₂
      + prCertA₂ B₄ B₆ B₈ a₁ b₁ a₂ b₂ * Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂
      = a₂ ^ 3 * (Phi B₄ B₆ B₈ a₁ b₁) ^ 2 := by
  rw [prCertA₁, prCertA₂, DDz, Prz, Phi]; ring

/-! ### §2 — corner elimination and cube composition -/

/-- Two coprime monomial weights on the same target cancel. -/
theorem dvd_of_dvd_coprime_weights {a b X d : ℤ} {n : ℕ}
    (hco : IsCoprime a b) (h₁ : d ∣ a ^ n * X) (h₂ : d ∣ b ^ n * X) :
    d ∣ X := by
  obtain ⟨s, u, hsu⟩ : IsCoprime (a ^ n) (b ^ n) := hco.pow
  have hX : X = s * (a ^ n * X) + u * (b ^ n * X) := by
    linear_combination X * hsu.symm
  rw [hX]
  exact dvd_add (h₁.mul_left _) (h₂.mul_left _)

/-- **The squaring trick**: cubing a Bézout identity puts every term in the
ideal of the squares. -/
theorem dvd_cube_of_bezout {d A f g p q : ℤ} (h : f * p + g * q = A)
    (hp : d ∣ p ^ 2) (hq : d ∣ q ^ 2) : d ∣ A ^ 3 := by
  have hA : A ^ 3 = (f ^ 3 * p + 3 * f ^ 2 * g * q) * p ^ 2
      + (3 * f * g ^ 2 * p + g ^ 3 * q) * q ^ 2 := by
    rw [← h]; ring
  rw [hA]
  exact dvd_add (hp.mul_left _) (hq.mul_left _)

/-! ### §3 — common secant divisors control the duplication squares -/

theorem dvd_psi_sq_of_secant {B₂ B₄ B₆ a₁ b₁ a₂ b₂ d : ℤ}
    (hco₂ : IsCoprime a₂ b₂)
    (h₁ : d ∣ DDz a₁ b₁ a₂ b₂) (h₂ : d ∣ Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂) :
    d ∣ (Psi B₂ B₄ B₆ a₁ b₁) ^ 2 := by
  apply dvd_of_dvd_coprime_weights hco₂ (n := 3)
  · rw [← psi_sq_certA]
    exact dvd_add (h₁.mul_left _) (h₂.mul_left _)
  · exact dvd_b2_psi_sq h₁ h₂

theorem dvd_phi_sq_of_secant {B₄ B₆ B₈ a₁ b₁ a₂ b₂ d : ℤ}
    (hco₂ : IsCoprime a₂ b₂)
    (h₁ : d ∣ DDz a₁ b₁ a₂ b₂) (h₃ : d ∣ Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂) :
    d ∣ (Phi B₄ B₆ B₈ a₁ b₁) ^ 2 := by
  apply dvd_of_dvd_coprime_weights hco₂ (n := 3)
  · rw [← phi_sq_certA]
    exact dvd_add (h₁.mul_left _) (h₃.mul_left _)
  · exact dvd_b2_phi_sq h₁ h₃

/-! ### §4 — THE UNIVERSAL SECANT CONTENT BOUND -/

/-- **For every Weierstrass curve**: if `x₁ = a₁/b₁` and `x₂ = a₂/b₂` are in
lowest terms, every common divisor of the secant addition triple
`(DDz, Sfz, Prz)` divides `Δ⁶`.  The secant analogue of r174's
`dvd_disc_sq_of_isCoprime`, uniform in the curve. -/
theorem secant_content_universal (B₂ B₄ B₆ B₈ : ℤ)
    (hrel : 4 * B₈ = B₂ * B₆ - B₄ ^ 2) {a₁ b₁ a₂ b₂ d : ℤ}
    (hco₁ : IsCoprime a₁ b₁) (hco₂ : IsCoprime a₂ b₂)
    (h₁ : d ∣ DDz a₁ b₁ a₂ b₂) (h₂ : d ∣ Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂)
    (h₃ : d ∣ Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂) :
    d ∣ Disc B₂ B₄ B₆ B₈ ^ 6 := by
  have hΨ : d ∣ (Psi B₂ B₄ B₆ a₁ b₁) ^ 2 := dvd_psi_sq_of_secant hco₂ h₁ h₂
  have hΦ : d ∣ (Phi B₄ B₆ B₈ a₁ b₁) ^ 2 := dvd_phi_sq_of_secant hco₂ h₁ h₃
  have hX : d ∣ (Disc B₂ B₄ B₆ B₈ ^ 2 * a₁ ^ 7) ^ 3 :=
    dvd_cube_of_bezout (bezout_X B₂ B₄ B₆ B₈ a₁ b₁ hrel) hΦ hΨ
  have hY : d ∣ (Disc B₂ B₄ B₆ B₈ ^ 2 * b₁ ^ 7) ^ 3 :=
    dvd_cube_of_bezout (bezout_Y B₂ B₄ B₆ B₈ a₁ b₁ hrel) hΦ hΨ
  have hX' : d ∣ a₁ ^ 21 * Disc B₂ B₄ B₆ B₈ ^ 6 := by
    have he : (Disc B₂ B₄ B₆ B₈ ^ 2 * a₁ ^ 7) ^ 3
        = a₁ ^ 21 * Disc B₂ B₄ B₆ B₈ ^ 6 := by ring
    rwa [he] at hX
  have hY' : d ∣ b₁ ^ 21 * Disc B₂ B₄ B₆ B₈ ^ 6 := by
    have he : (Disc B₂ B₄ B₆ B₈ ^ 2 * b₁ ^ 7) ^ 3
        = b₁ ^ 21 * Disc B₂ B₄ B₆ B₈ ^ 6 := by ring
    rwa [he] at hY
  exact dvd_of_dvd_coprime_weights hco₁ hX' hY'

end PrincipiaTractalis.SecantContentUniversal

#print axioms PrincipiaTractalis.SecantContentUniversal.psi_sq_certA
#print axioms PrincipiaTractalis.SecantContentUniversal.phi_sq_certA
#print axioms PrincipiaTractalis.SecantContentUniversal.secant_content_universal
