/-
# PF.QuasiParallelogramContent5077a1_r158

★★★ 2026-07-30 — r158: THE CONTENT BOUND `gcd(DD,Sf,Pf) ∣ 5⁴·5077⁴` ★★★

Completes the divisibility half of stone W2 for the rank-3 curve, by the same
squaring trick r148b used for 389a1 — which avoids the giant corner cofactors
entirely:

  `d ∣ R6`,  `d ∣ F²`   ⟹   `d ∣ (α·R6 + β·F)² = K²·b₂¹⁸`   (and the a₂-side)
  ⟹  `d ∣ K²`  at fully coprime coordinate pairs.

Here `K = 5² · 5077² = 644398225`, so the bound is `K² = 5⁴ · 5077⁴`.

## Why the extra factor of 5 is real

For 389a1 the corresponding constant was exactly `389² = 151321`.  Here `K` is
NOT a pure power of 5077, and that is not slack in the argument: `R6` and `F`
share a nontrivial factor modulo 5,

  `R6 ≡ 2t⁶ + 1`,  `F ≡ (t² + 2)²`,  `gcd ≡ t² + 2  (mod 5)`,

so **every** integer in the ideal `(R6, F)` is divisible by 5.  They likewise
share `t² − 184t − 1690` modulo 5077 (the exact analogue of 389a1's
`a² + 180a − 69` mod 389).  `K = 5²·5077² = 644398225` is the *minimal*
positive integer in `(R6, F) ∩ ℤ`, confirmed by integer row reduction
(Hermite normal form) over the coefficient lattice spanned by
`tⁱ·R6` (i ≤ 3) and `tʲ·F` (j ≤ 5).  So the constant cannot be improved by a
better choice of cofactors.

As in r148b we pay one squaring — the report's optimal content bound is `K`
itself, we prove `K²` — for a proof that never touches the corner
certificates.  The constant enters downstream only inside a logarithm, so a
square costs nothing structural.

## Data

`Res_{a₁}(DD, Pf) = F(a₂,b₂)²` exactly (verified), which is what makes the
pairwise certificates `cert_BP`, `cert_AP` exist with cofactors of bidegree
(1,6).  All four cofactor pairs were solved as linear systems over ℚ, checked
to be integral, and verified by `expand() == 0`; see
`codex/W2_CERTIFICATES_5077a1.md`.

HONEST SCOPE.  Divisibility control only.  NO size bounds, NO height
inequality, NO secant bridge, NO parallelogram law, NO rank-3 statement.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-30.
-/
import PF.QuasiParallelogramCerts5077a1_r157
import PF.E5077a1RankOne_r144

namespace PrincipiaTractalis.QuasiParallelogramContent5077a1

open PrincipiaTractalis.QuasiParallelogramCerts5077a1
open PrincipiaTractalis.E5077a1RankOne (F)

/-! ## §1 — the pairwise `(DD, Pf)` certificates, `ρ = F(a₂,b₂)²` -/

/-- **cert B-P**: `U·DD + V·Pf = F(a₂,b₂)²·b₁³`. -/
theorem cert_BP (a₁ b₁ a₂ b₂ : ℤ) :
    (2 * a₁ * a₂ ^ 5 * b₂ + 14 * a₁ * a₂ ^ 3 * b₂ ^ 3
        - 25 * a₁ * a₂ ^ 2 * b₂ ^ 4 + a₂ ^ 6 * b₁
        + 28 * a₂ ^ 4 * b₁ * b₂ ^ 2 - 25 * a₂ ^ 3 * b₁ * b₂ ^ 3
        + 147 * a₂ ^ 2 * b₁ * b₂ ^ 4 - 700 * a₂ * b₁ * b₂ ^ 5
        + 625 * b₁ * b₂ ^ 6) * DD a₁ b₁ a₂ b₂
      + (-2 * a₁ * a₂ ^ 3 * b₂ ^ 3 - 14 * a₁ * a₂ * b₂ ^ 5 + 25 * a₁ * b₂ ^ 6
        + 3 * a₂ ^ 4 * b₁ * b₂ ^ 2 + 28 * a₂ ^ 2 * b₁ * b₂ ^ 4
        - 75 * a₂ * b₁ * b₂ ^ 5 + 49 * b₁ * b₂ ^ 6) * Pf a₁ b₁ a₂ b₂
      = F a₂ b₂ ^ 2 * b₁ ^ 3 := by
  simp only [DD, Pf, F]; ring

/-- **cert A-P**: `U·DD + V·Pf = F(a₂,b₂)²·a₁³`. -/
theorem cert_AP (a₁ b₁ a₂ b₂ : ℤ) :
    (25 * a₁ * a₂ ^ 5 * b₂ + 147 * a₁ * a₂ ^ 4 * b₂ ^ 2
        - 1400 * a₁ * a₂ ^ 3 * b₂ ^ 3 + 3872 * a₁ * a₂ ^ 2 * b₂ ^ 4
        - 4900 * a₁ * a₂ * b₂ ^ 5 + 2401 * a₁ * b₂ ^ 6
        - 350 * a₂ ^ 4 * b₁ * b₂ ^ 2 + 2561 * a₂ ^ 3 * b₁ * b₂ ^ 3
        - 6125 * a₂ ^ 2 * b₁ * b₂ ^ 4 + 4802 * a₂ * b₁ * b₂ ^ 5)
        * DD a₁ b₁ a₂ b₂
      + (a₁ * a₂ ^ 6 + 28 * a₁ * a₂ ^ 4 * b₂ ^ 2 - 125 * a₁ * a₂ ^ 3 * b₂ ^ 3
        + 147 * a₁ * a₂ ^ 2 * b₂ ^ 4 - 14 * a₂ ^ 5 * b₁ * b₂
        + 75 * a₂ ^ 4 * b₁ * b₂ ^ 2 - 98 * a₂ ^ 3 * b₁ * b₂ ^ 3)
          * Pf a₁ b₁ a₂ b₂
      = F a₂ b₂ ^ 2 * a₁ ^ 3 := by
  simp only [DD, Pf, F]; ring

/-! ## §2 — the level-2 `R6`-vs-`F` identities (`K = 5²·5077² = 644398225`) -/

theorem r6F_b (a b : ℤ) :
    (192346 * a ^ 3 + 352800 * a ^ 2 * b + 3236422 * a * b ^ 2
        - 3981825 * b ^ 3) * R6 a b
      + (-384692 * a ^ 5 - 705600 * a ^ 4 * b + 12377064 * a ^ 3 * b ^ 2
        - 24783050 * a ^ 2 * b ^ 3 + 42890092 * a * b ^ 4
        + 18107950 * b ^ 5) * F a b
      = 644398225 * b ^ 9 := by
  simp only [R6, F]; ring

theorem r6F_a (a b : ℤ) :
    (60776400 * a ^ 3 - 22646722 * a ^ 2 * b - 630562625 * a * b ^ 2
        + 900485446 * b ^ 3) * R6 a b
      + (522845425 * a ^ 5 + 45293444 * a ^ 4 * b
        - 1804362700 * a ^ 3 * b ^ 2 + 6927821602 * a ^ 2 * b ^ 3
        - 6790943075 * a * b ^ 4 - 1121012494 * b ^ 5) * F a b
      = 644398225 * a ^ 9 := by
  simp only [R6, F]; ring

/-! ## §3 — the composition -/

/-- `d ∣ F(a₂,b₂)²` from the two pairwise certificates plus coprimality. -/
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

/-- The squaring step: `d ∣ R` and `d ∣ F'²` give `d ∣ (αR + βF')²`. -/
private theorem dvd_sq_combination {R F' d α β c : ℤ} (hR : d ∣ R)
    (hF : d ∣ F' ^ 2) (hid : α * R + β * F' = c) : d ∣ c ^ 2 := by
  have key : c ^ 2 = (α ^ 2 * R + 2 * α * β * F') * R + β ^ 2 * F' ^ 2 := by
    linear_combination (-(α * R + β * F' + c)) * hid
  rw [key]
  exact dvd_add (hR.mul_left _) (hF.mul_left _)

/-- **★ r158 — THE CONTENT BOUND ★**  At fully coprime coordinate pairs, any
common divisor of the three addition forms divides `5⁴·5077⁴`. -/
theorem content_dvd {a₁ b₁ a₂ b₂ d : ℤ}
    (h₁ : IsCoprime a₁ b₁) (h₂ : IsCoprime a₂ b₂)
    (hDD : d ∣ DD a₁ b₁ a₂ b₂) (hS : d ∣ Sf a₁ b₁ a₂ b₂)
    (hP : d ∣ Pf a₁ b₁ a₂ b₂) : d ∣ 5 ^ 4 * 5077 ^ 4 := by
  have hR6 : d ∣ R6 a₂ b₂ := dvd_R6_of_dvd_forms h₁ hDD hS hP
  have hF2 : d ∣ F a₂ b₂ ^ 2 := dvd_F_sq h₁ hDD hP
  have hb : d ∣ (644398225 * b₂ ^ 9) ^ 2 :=
    dvd_sq_combination hR6 hF2 (r6F_b a₂ b₂)
  have ha : d ∣ (644398225 * a₂ ^ 9) ^ 2 :=
    dvd_sq_combination hR6 hF2 (r6F_a a₂ b₂)
  have hb' : d ∣ 644398225 ^ 2 * b₂ ^ 18 := by
    have e : (644398225 * b₂ ^ 9 : ℤ) ^ 2 = 644398225 ^ 2 * b₂ ^ 18 := by ring
    rwa [e] at hb
  have ha' : d ∣ 644398225 ^ 2 * a₂ ^ 18 := by
    have e : (644398225 * a₂ ^ 9 : ℤ) ^ 2 = 644398225 ^ 2 * a₂ ^ 18 := by ring
    rwa [e] at ha
  have h1818 : IsCoprime (a₂ ^ 18) (b₂ ^ 18) := h₂.pow
  obtain ⟨u, v, huv⟩ := h1818
  have key : (5 : ℤ) ^ 4 * 5077 ^ 4
      = u * (644398225 ^ 2 * a₂ ^ 18) + v * (644398225 ^ 2 * b₂ ^ 18) := by
    have e : (5 : ℤ) ^ 4 * 5077 ^ 4 = 644398225 ^ 2 := by norm_num
    rw [e]
    linear_combination (-(644398225 ^ 2 : ℤ)) * huv
  rw [key]
  exact dvd_add (ha'.mul_left u) (hb'.mul_left v)

end PrincipiaTractalis.QuasiParallelogramContent5077a1

#print axioms PrincipiaTractalis.QuasiParallelogramContent5077a1.cert_BP
#print axioms PrincipiaTractalis.QuasiParallelogramContent5077a1.cert_AP
#print axioms PrincipiaTractalis.QuasiParallelogramContent5077a1.r6F_b
#print axioms PrincipiaTractalis.QuasiParallelogramContent5077a1.r6F_a
#print axioms PrincipiaTractalis.QuasiParallelogramContent5077a1.dvd_F_sq
#print axioms PrincipiaTractalis.QuasiParallelogramContent5077a1.content_dvd
