/-
# PF.QuasiParallelogramContent389a1_r148b

★★★ 2026-07-28 — r148b: THE CONTENT BOUND `gcd(DD,Sf,Pf) ∣ 389⁴` ★★★

Completes the divisibility half of stone W2.  Composes r148a's level-1
control (`d ∣ R6(a₂,b₂)`) with the pairwise product-form certificates and
the small `R6`-vs-`F` level-2 identities (all sympy-verified,
`codex/W2_CERTIFICATES_389a1.md`) via a squaring trick that avoids the
κ~10⁹ corner cofactors entirely:

  d ∣ R6,  d ∣ F²  ⟹  d ∣ (α·R6 + β·F)² = 389⁴·b₂¹⁸  (and a₂-side)
  ⟹  d ∣ 389⁴   at fully coprime coordinate pairs.

(The report's optimal constant is 389³; we pay one extra factor of 389
for a proof that never touches the giant corners.  The height inequality
only needs SOME explicit constant.)

HONEST SCOPE.  Divisibility control only; no height inequality yet.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.QuasiParallelogramCerts389a1_r148a
import PF.E389a1RankOne_r143

namespace PrincipiaTractalis.QuasiParallelogramContent389a1

open PrincipiaTractalis.QuasiParallelogramCerts389a1
open PrincipiaTractalis.E389a1RankOne (F)

/-! ## §1 — the pairwise product certificates (sympy-verified) -/

/-- **cert B-P**: `U·DD + V·Pf = F(a₂,b₂)²·b₁³`. -/
theorem cert_BP (a₁ b₁ a₂ b₂ : ℤ) :
    (2 * a₁ * a₂ ^ 5 * b₂ + 4 * a₁ * a₂ ^ 3 * b₂ ^ 3 - a₁ * a₂ ^ 2 * b₂ ^ 4
        + a₂ ^ 6 * b₁ + 8 * a₂ ^ 4 * b₁ * b₂ ^ 2 - a₂ ^ 3 * b₁ * b₂ ^ 3
        + 13 * a₂ ^ 2 * b₁ * b₂ ^ 4 - 8 * a₂ * b₁ * b₂ ^ 5 + b₁ * b₂ ^ 6)
        * DD a₁ b₁ a₂ b₂
      + (-2 * a₁ * a₂ ^ 3 * b₂ ^ 3 - 4 * a₁ * a₂ * b₂ ^ 5 + a₁ * b₂ ^ 6
        + 3 * a₂ ^ 4 * b₁ * b₂ ^ 2 + 8 * a₂ ^ 2 * b₁ * b₂ ^ 4
        - 3 * a₂ * b₁ * b₂ ^ 5 + 3 * b₁ * b₂ ^ 6) * Pf a₁ b₁ a₂ b₂
      = F a₂ b₂ ^ 2 * b₁ ^ 3 := by
  simp only [DD, Pf, F]; ring

/-- **cert A-P**: `U·DD + V·Pf = F(a₂,b₂)²·a₁³`. -/
theorem cert_AP (a₁ b₁ a₂ b₂ : ℤ) :
    (a₁ * a₂ ^ 5 * b₂ + 13 * a₁ * a₂ ^ 4 * b₂ ^ 2 - 16 * a₁ * a₂ ^ 3 * b₂ ^ 3
        + 28 * a₁ * a₂ ^ 2 * b₂ ^ 4 - 12 * a₁ * a₂ * b₂ ^ 5 + 9 * a₁ * b₂ ^ 6
        - 4 * a₂ ^ 4 * b₁ * b₂ ^ 2 + 15 * a₂ ^ 3 * b₁ * b₂ ^ 3
        - 15 * a₂ ^ 2 * b₁ * b₂ ^ 4 + 18 * a₂ * b₁ * b₂ ^ 5) * DD a₁ b₁ a₂ b₂
      + (a₁ * a₂ ^ 6 + 8 * a₁ * a₂ ^ 4 * b₂ ^ 2 - 5 * a₁ * a₂ ^ 3 * b₂ ^ 3
        + 9 * a₁ * a₂ ^ 2 * b₂ ^ 4 - 4 * a₂ ^ 5 * b₁ * b₂
        + 3 * a₂ ^ 4 * b₁ * b₂ ^ 2 - 6 * a₂ ^ 3 * b₁ * b₂ ^ 3)
          * Pf a₁ b₁ a₂ b₂
      = F a₂ b₂ ^ 2 * a₁ ^ 3 := by
  simp only [DD, Pf, F]; ring

/-! ## §2 — the level-2 `R6`-vs-`F` identities (`151321 = 389²`) -/

theorem r6F_b (a b : ℤ) :
    (378 * a ^ 3 + 1768 * a ^ 2 * b + 2660 * a * b ^ 2 + 5303 * b ^ 3) * R6 a b
      + (-756 * a ^ 5 - 5048 * a ^ 4 * b - 1808 * a ^ 3 * b ^ 2
        + 29014 * a ^ 2 * b ^ 3 + 25052 * a * b ^ 4 + 30996 * b ^ 5) * F a b
      = 151321 * b ^ 9 := by
  simp only [R6, F]; ring

theorem r6F_a (a b : ℤ) :
    (25516 * a ^ 3 - 2896 * a ^ 2 * b + 7547 * a * b ^ 2 + 13506 * b ^ 3) * R6 a b
      + (100289 * a ^ 5 - 96272 * a ^ 4 * b + 105654 * a ^ 3 * b ^ 2
        + 215386 * a ^ 2 * b ^ 3 - 24671 * a * b ^ 4 - 49522 * b ^ 5) * F a b
      = 151321 * a ^ 9 := by
  simp only [R6, F]; ring

/-! ## §3 — the composition -/

/-- `d ∣ F(a₂,b₂)²` from the two product certificates + coprimality. -/
theorem dvd_F_sq {a₁ b₁ a₂ b₂ d : ℤ} (h : IsCoprime a₁ b₁)
    (hDD : d ∣ DD a₁ b₁ a₂ b₂) (hP : d ∣ Pf a₁ b₁ a₂ b₂) :
    d ∣ F a₂ b₂ ^ 2 := by
  have hb : d ∣ F a₂ b₂ ^ 2 * b₁ ^ 3 := by
    rw [← cert_BP a₁ b₁ a₂ b₂]
    exact dvd_add (hDD.mul_left _) (hP.mul_left _)
  have ha : d ∣ F a₂ b₂ ^ 2 * a₁ ^ 3 := by
    rw [← cert_AP a₁ b₁ a₂ b₂]
    exact dvd_add (hDD.mul_left _) (hP.mul_left _)
  have h33 : IsCoprime (a₁ ^ 3) (b₁ ^ 3) := h.pow
  obtain ⟨u, v, huv⟩ := h33
  have key : F a₂ b₂ ^ 2
      = u * (F a₂ b₂ ^ 2 * a₁ ^ 3) + v * (F a₂ b₂ ^ 2 * b₁ ^ 3) := by
    linear_combination (-(F a₂ b₂ ^ 2) : ℤ) * huv
  rw [key]
  exact dvd_add (ha.mul_left u) (hb.mul_left v)

/-- The squaring step: `d ∣ R6` and `d ∣ F²` give `d ∣ (αR6 + βF)²`. -/
private theorem dvd_sq_combination {R F' d α β c : ℤ} (hR : d ∣ R)
    (hF : d ∣ F' ^ 2) (hid : α * R + β * F' = c) : d ∣ c ^ 2 := by
  have key : c ^ 2 = (α ^ 2 * R + 2 * α * β * F') * R + β ^ 2 * F' ^ 2 := by
    linear_combination (-(α * R + β * F' + c)) * hid
  rw [key]
  exact dvd_add (hR.mul_left _) (hF.mul_left _)

/-- **★ r148b — THE CONTENT BOUND ★**  At fully coprime coordinate pairs,
any common divisor of the three addition forms divides `389⁴`. -/
theorem content_dvd_389_pow_four {a₁ b₁ a₂ b₂ d : ℤ}
    (h₁ : IsCoprime a₁ b₁) (h₂ : IsCoprime a₂ b₂)
    (hDD : d ∣ DD a₁ b₁ a₂ b₂) (hS : d ∣ Sf a₁ b₁ a₂ b₂)
    (hP : d ∣ Pf a₁ b₁ a₂ b₂) : d ∣ 389 ^ 4 := by
  have hR6 : d ∣ R6 a₂ b₂ := dvd_R6_of_dvd_forms h₁ hDD hS hP
  have hF2 : d ∣ F a₂ b₂ ^ 2 := dvd_F_sq h₁ hDD hP
  have hb : d ∣ (151321 * b₂ ^ 9) ^ 2 :=
    dvd_sq_combination hR6 hF2 (r6F_b a₂ b₂)
  have ha : d ∣ (151321 * a₂ ^ 9) ^ 2 :=
    dvd_sq_combination hR6 hF2 (r6F_a a₂ b₂)
  have hb' : d ∣ 151321 ^ 2 * (b₂ ^ 18) := by
    have : (151321 * b₂ ^ 9 : ℤ) ^ 2 = 151321 ^ 2 * b₂ ^ 18 := by ring
    rwa [this] at hb
  have ha' : d ∣ 151321 ^ 2 * (a₂ ^ 18) := by
    have : (151321 * a₂ ^ 9 : ℤ) ^ 2 = 151321 ^ 2 * a₂ ^ 18 := by ring
    rwa [this] at ha
  have h1818 : IsCoprime (a₂ ^ 18) (b₂ ^ 18) := h₂.pow
  obtain ⟨u, v, huv⟩ := h1818
  have key : (389 : ℤ) ^ 4
      = u * (151321 ^ 2 * a₂ ^ 18) + v * (151321 ^ 2 * b₂ ^ 18) := by
    have h4 : (389 : ℤ) ^ 4 = 151321 ^ 2 := by norm_num
    rw [h4]
    linear_combination (-(151321 ^ 2 : ℤ)) * huv
  rw [key]
  exact dvd_add (ha'.mul_left u) (hb'.mul_left v)

end PrincipiaTractalis.QuasiParallelogramContent389a1

#print axioms PrincipiaTractalis.QuasiParallelogramContent389a1.cert_BP
#print axioms PrincipiaTractalis.QuasiParallelogramContent389a1.cert_AP
#print axioms PrincipiaTractalis.QuasiParallelogramContent389a1.content_dvd_389_pow_four
