/-
# PF.E102a1RankOne_2026_11_10 — part 1: curve facts for the E_102.a1 rank chain

The per-curve obligations for feeding 102a1 into the universal layers
(r174/r176/r199/r200/r202). Everything else comes from those layers; this file
holds only what is genuinely specific to `y² + xy = x³ + x² − 2x`.

**Delta from the E_91a1 template:** E_102a1 HAS rational 2-torsion at `(0, 0)`
(audit `codex/BSD_SCOPING_UPPER_BOUND_IS_THE_GAP_2026-10-17.md`), so the
whole-curve `h2tor : ∀ R ≠ 0, 2•R ≠ 0` fails. The route must therefore use
per-point 2-torsion-freeness on the Heegner base point `P = (2, 2)` and its
orbit, rather than r200's curve-wide version. The Ψ-structure on this curve
splits as `X·Y·Q(X,Y)` where `Q` has no coprime-integer root; Ψ vanishes only
at `x = 0` (the 2-torsion point).

**What this file delivers, axiom-free, kernel-only:**

  * The b-invariants of E_102.a1: `(b₂, b₄, b₆, b₈) = (5, -4, 0, -4)`.
  * The discriminant `Disc 5 (-4) 0 (-4) = 612 ≠ 0` (LMFDB conductor 102 =
    2·3·17 has the same radical as 612 = 2²·3²·17).
  * The r174 Weierstrass relation `4·b₈ = b₂·b₆ − b₄²`.
  * `Psi_factorisation`: Ψ 5 (-4) 0 X Y = X·Y·(4X² + 5XY − 8Y²).
  * `quadratic_factor_coprime_no_solution`: the quadratic factor has no
    nonzero coprime integer solution. Proof by reduction mod 5 — the form
    `4X² − 3Y² (mod 5)` only vanishes when both X, Y ≡ 0 (mod 5),
    contradicting coprimality.
  * `Psi_ne_zero_at_nonzero`: Ψ ≠ 0 at `(x.num, x.den)` for every rational
    `x ≠ 0`, via `isCoprime_num_den` + the three factor nonvanishings.

**What this file does NOT establish:** the `rank_ge_one` theorem itself —
that requires the orbit computation `X(2^n • P)` and an infinite-range
argument. This is a prerequisite scaffold; the capstone file is future work.

HONEST SCOPE. A LOWER bound on the rank of one curve, half-built. The full
chain assembles from `MordellWeilRankLowerBound_r129` +
`NonTorsionFromOrbit_2026_10_21` once the orbit-infinity theorem is supplied.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-11-10.
-/

import PF.BSD_HeegnerRank1ProofE102a1
import PF.DuplicationBezoutUniversal_r174
import PF.DuplicationHeightUniversal_r176
import Mathlib.Tactic.NormNum

namespace PrincipiaTractalis
namespace E102a1RankOne20261110

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.BSD_HeegnerRank1ProofE102a1
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationHeight

/-! ## §1 — the b-invariants, in the integer form the universal layers want -/

theorem b₂_eq : (E_102a1.toAffine).b₂ = ((5 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₂, E_102a1]
  norm_num

theorem b₄_eq : (E_102a1.toAffine).b₄ = ((-4 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₄, E_102a1]
  norm_num

theorem b₆_eq : (E_102a1.toAffine).b₆ = ((0 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₆, E_102a1]

theorem b₈_eq : (E_102a1.toAffine).b₈ = ((-4 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₈, E_102a1]
  norm_num

/-! ## §2 — the Weierstrass relation and nonzero discriminant -/

/-- r174's `hrel` hypothesis `4·b₈ = b₂·b₆ − b₄²`: for E_102.a1 this reads
`4·(-4) = 5·0 − (-4)² = 0 - 16 = -16`. -/
theorem hrel102 : 4 * (-4 : ℤ) = 5 * 0 - (-4) ^ 2 := by decide

/-- The discriminant of E_102.a1 is `612`. Nonzero, as required by the
universal height-window layer. -/
theorem hΔ102 : Disc 5 (-4) 0 (-4) ≠ 0 := by decide

/-- Explicit value: `Disc 5 (-4) 0 (-4) = 612`. -/
theorem Disc_value : Disc 5 (-4) 0 (-4) = 612 := by decide

/-! ## §3 — structural analysis of `Ψ` on E_102.a1

For `(b₂, b₄, b₆) = (5, -4, 0)`, the universal `Psi` specialises to

  `Psi 5 (-4) 0 X Y = 4·X³·Y + 5·X²·Y² − 8·X·Y³ + 0
                    = X·Y · (4·X² + 5·X·Y − 8·Y²)`.

The quadratic form `Q(X, Y) = 4·X² + 5·X·Y − 8·Y²` has no coprime-integer
root with `Y ≠ 0`: reducing mod 5, `Q ≡ 4·X² − 3·Y² (mod 5)`, and the only
pair of residues with `4·X² ≡ 3·Y² (mod 5)` is `X ≡ Y ≡ 0 (mod 5)`, which
contradicts coprimality.
-/

/-- Explicit `Psi` factorisation on E_102.a1. -/
theorem Psi_factorisation (X Y : ℤ) :
    Psi 5 (-4) 0 X Y = X * Y * (4 * X ^ 2 + 5 * X * Y - 8 * Y ^ 2) := by
  simp [Psi]
  ring

/-- The quadratic form `4X² + 5XY − 8Y²` has no coprime-integer solution with
`Y ≠ 0`. Proof by mod-5 contradiction. -/
theorem quadratic_factor_coprime_no_solution (X Y : ℤ) (hY : Y ≠ 0)
    (hcop : IsCoprime X Y) :
    4 * X ^ 2 + 5 * X * Y - 8 * Y ^ 2 ≠ 0 := by
  intro heq
  -- Mod 5: 4X² + 5XY − 8Y² ≡ 4X² − 3Y² (mod 5), and this ≡ 0 forces 5 ∣ X
  -- and 5 ∣ Y (the only residue pair with 4X² ≡ 3Y² (mod 5) is (0, 0)).
  have h5 : (5 : ℤ) ∣ (4 * X ^ 2 + 5 * X * Y - 8 * Y ^ 2) := by
    rw [heq]; exact dvd_zero _
  -- Equivalently, 5 ∣ (4X² − 8Y²) = 4(X² − 2Y²), so 5 ∣ (X² − 2Y²).
  have h5' : (5 : ℤ) ∣ (4 * X ^ 2 - 8 * Y ^ 2) := by
    have hh : (5 : ℤ) ∣ (5 * X * Y) := ⟨X * Y, by ring⟩
    have : (4 * X ^ 2 - 8 * Y ^ 2) =
           (4 * X ^ 2 + 5 * X * Y - 8 * Y ^ 2) - 5 * X * Y := by ring
    rw [this]
    exact dvd_sub h5 hh
  have h5xy : (5 : ℤ) ∣ (X ^ 2 - 2 * Y ^ 2) := by
    have := h5'
    have hfact : (4 * X ^ 2 - 8 * Y ^ 2) = 4 * (X ^ 2 - 2 * Y ^ 2) := by ring
    rw [hfact] at this
    -- 5 ∣ 4 · (X² − 2Y²), gcd(5, 4) = 1, so 5 ∣ X² − 2Y²
    have hcop54 : IsCoprime (5 : ℤ) 4 := by decide
    exact hcop54.dvd_of_dvd_mul_left this
  -- Case-split on X mod 5 and Y mod 5 to show both must be ≡ 0.
  -- Squares mod 5: 0² = 0, 1² = 1, 2² = 4, 3² = 4, 4² = 1 → {0, 1, 4}.
  -- 2·{0, 1, 4} = {0, 2, 3}. For X² − 2Y² ≡ 0 (mod 5):
  --   X² ∈ {0,1,4}, 2Y² ∈ {0,2,3}; intersection: {0}. So X² ≡ 0 ≡ 2Y² (mod 5),
  -- hence X ≡ 0 (mod 5) and Y² ≡ 0 (mod 5) → Y ≡ 0 (mod 5).
  have hXmod : (X : ZMod 5) ^ 2 - 2 * (Y : ZMod 5) ^ 2 = 0 := by
    have : ((X ^ 2 - 2 * Y ^ 2 : ℤ) : ZMod 5) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h5xy
    push_cast at this
    linear_combination this
  -- Decide on ZMod 5 — only solution is X = 0 = Y
  have hXzero_and_Yzero : (X : ZMod 5) = 0 ∧ (Y : ZMod 5) = 0 := by
    -- The decider on `ZMod 5` finite enumeration: ∀ x y : ZMod 5, x² = 2·y² → x = 0 ∧ y = 0.
    have key : ∀ x y : ZMod 5, x ^ 2 - 2 * y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
    exact key _ _ hXmod
  -- Now 5 ∣ X and 5 ∣ Y, contradicting coprimality.
  have h5X : (5 : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X 5).mp hXzero_and_Yzero.1
  have h5Y : (5 : ℤ) ∣ Y := (ZMod.intCast_zmod_eq_zero_iff_dvd Y 5).mp hXzero_and_Yzero.2
  have hu : IsUnit (5 : ℤ) := hcop.isUnit_of_dvd' h5X h5Y
  rw [Int.isUnit_iff] at hu
  omega

/-- `Ψ ≠ 0` at every rational `x ≠ 0`. -/
theorem Psi_ne_zero_at_nonzero (x : ℚ) (hx : x ≠ 0) :
    Psi 5 (-4) 0 x.num (x.den : ℤ) ≠ 0 := by
  rw [Psi_factorisation]
  have hden : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  have hnum : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hcop : IsCoprime x.num (x.den : ℤ) := isCoprime_num_den x
  have hquad : 4 * x.num ^ 2 + 5 * x.num * (x.den : ℤ) - 8 * (x.den : ℤ) ^ 2 ≠ 0 :=
    quadratic_factor_coprime_no_solution x.num (x.den : ℤ) hden hcop
  intro h
  rcases mul_eq_zero.mp h with hab | hc
  · rcases mul_eq_zero.mp hab with ha | hb
    · exact hnum ha
    · exact hden hb
  · exact hquad hc

end E102a1RankOne20261110
end PrincipiaTractalis

#print axioms PrincipiaTractalis.E102a1RankOne20261110.b₂_eq
#print axioms PrincipiaTractalis.E102a1RankOne20261110.b₄_eq
#print axioms PrincipiaTractalis.E102a1RankOne20261110.b₆_eq
#print axioms PrincipiaTractalis.E102a1RankOne20261110.b₈_eq
#print axioms PrincipiaTractalis.E102a1RankOne20261110.hrel102
#print axioms PrincipiaTractalis.E102a1RankOne20261110.hΔ102
#print axioms PrincipiaTractalis.E102a1RankOne20261110.Disc_value
#print axioms PrincipiaTractalis.E102a1RankOne20261110.Psi_factorisation
#print axioms PrincipiaTractalis.E102a1RankOne20261110.quadratic_factor_coprime_no_solution
#print axioms PrincipiaTractalis.E102a1RankOne20261110.Psi_ne_zero_at_nonzero
