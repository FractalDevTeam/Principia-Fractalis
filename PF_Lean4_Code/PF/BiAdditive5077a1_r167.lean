/-
# PF.BiAdditive5077a1_r167

★★★ 2026-07-31 — THE HEIGHT PAIRING ON 5077a1 IS BI-ADDITIVE ★★★

Two steps, both enabled by r166b (5077a1 is torsion-free):

1. **The laws become unconditional.**  r164 and r165 carry non-torsion
   hypotheses; torsion-freeness turns those into "nonzero", and the degenerate
   cases are then checkable directly, so

       `ĥ(P+Q) + ĥ(P−Q) = 2ĥ(P) + 2ĥ(Q)`   for **all** `P, Q`
       `ĥ(k • R) = k²·ĥ(R)`                 for **all** `k, R`.

   The degenerate cases hold: at `P = 0` it is `ĥ(Q) + ĥ(−Q) = 2ĥ(Q)`
   (`canheight_neg`), at `Q = −P` it is `ĥ(0) + ĥ(2P) = 4ĥ(P)`
   (`canheight_dbl`), and symmetrically.

2. **Bi-additivity, by Jordan–von Neumann.**  A function on an abelian group
   satisfying the parallelogram identity is a quadratic form, so
   `⟨·,·⟩` is additive in each slot.  This is where the earlier claim that the
   3×3 case "needs bi-additivity the parallelogram law cannot give" was wrong:
   it gives it, once unconditional.

   The derivation used here, with `q = ĥ` and `B = ⟨·,·⟩`:
   * `4B(x,y) = q(x+y) − q(x−y)` — add the two expressions for `2B`;
   * then four instances of the law, at `(x+z, y)`, `(x−z, y)`, `(y+z, x)`,
     `(y−z, x)`.  Subtracting within each pair and adding the two results, the
     four "mixed difference" terms cancel **because `q(−u) = q(u)`**, leaving
     `q(x+y+z) − q(x+y−z) = q(x+z) − q(x−z) + q(y+z) − q(y−z)`,
     which is `4B(x+y,z) = 4B(x,z) + 4B(y,z)`.

HONEST SCOPE.  Bi-additivity of the pairing and the unconditional laws.  This
does NOT yet give rank ≥ 3: what remains is the 3×3 Sylvester step — the
analogue of r152's `regDet_eq_zero_of_relation` and r153's certified numerics,
at 3×3 instead of 2×2.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import PF.TorsionTrivial5077a1_r166b

namespace PrincipiaTractalis.BiAdditive5077a1

open PrincipiaTractalis.CanonicalHeight5077a1
open PrincipiaTractalis.CanheightParallelogram5077a1 (pairing)
open PrincipiaTractalis.CanheightMultiple5077a1 (canheight_zero canheight_neg)
open PrincipiaTractalis.TorsionTrivial5077a1 (nonTorsion_of_ne_zero)
open PrincipiaTractalis.E5077a1RankOne (E5077a1)

/-! ## §1 — the laws, unconditionally -/

/-- **The parallelogram law for every pair**, degenerate cases included. -/
theorem par (P Q : E5077a1.toAffine.Point) :
    canheight (P + Q) + canheight (P - Q) = 2 * canheight P + 2 * canheight Q := by
  by_cases hP : P = 0
  · subst hP
    rw [zero_add, zero_sub, canheight_neg, canheight_zero]; ring
  by_cases hQ : Q = 0
  · subst hQ
    rw [add_zero, sub_zero, canheight_zero]; ring
  by_cases hs : P + Q = 0
  · have hQP : Q = -P := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hs
    subst hQP
    rw [hs, canheight_zero, sub_neg_eq_add, canheight_dbl, canheight_neg]; ring
  by_cases hd : P - Q = 0
  · have hPQ : P = Q := sub_eq_zero.mp hd
    subst hPQ
    rw [hd, canheight_zero, canheight_dbl]; ring
  · exact CanheightParallelogram5077a1.canheight_parallelogram
      (nonTorsion_of_ne_zero hP) (nonTorsion_of_ne_zero hQ)
      (nonTorsion_of_ne_zero hs) (nonTorsion_of_ne_zero hd)

/-- **The multiple law for every `k` and every point.** -/
theorem mul (R : E5077a1.toAffine.Point) (k : ℤ) :
    canheight (k • R) = (k : ℝ) ^ 2 * canheight R := by
  by_cases hR : R = 0
  · subst hR; rw [smul_zero, canheight_zero]; ring
  · exact CanheightMultiple5077a1.canheight_zsmul (nonTorsion_of_ne_zero hR) k

/-! ## §2 — the pairing, and `4B = q(x+y) − q(x−y)` -/

theorem four_pairing (P Q : E5077a1.toAffine.Point) :
    4 * pairing P Q = canheight (P + Q) - canheight (P - Q) := by
  have hp := par P Q
  simp only [pairing]
  linarith [hp]

/-! ## §3 — BI-ADDITIVITY -/

/-- **★ THE PAIRING IS ADDITIVE IN ITS FIRST SLOT ★**
`⟨P+Q, R⟩ = ⟨P, R⟩ + ⟨Q, R⟩`, by Jordan–von Neumann. -/
theorem pairing_add_left (P Q R : E5077a1.toAffine.Point) :
    pairing (P + Q) R = pairing P R + pairing Q R := by
  -- the four instances of the unconditional law
  have A := par (P + R) Q
  have B := par (P - R) Q
  have C := par (Q + R) P
  have D := par (Q - R) P
  -- the mixed differences pair up under q(-u) = q(u)
  have e1 : (P + R) - Q = -((Q - R) - P) := by abel
  have e2 : (P - R) - Q = -((Q + R) - P) := by abel
  have h1 : canheight ((P + R) - Q) = canheight ((Q - R) - P) := by
    rw [e1, canheight_neg]
  have h2 : canheight ((P - R) - Q) = canheight ((Q + R) - P) := by
    rw [e2, canheight_neg]
  -- align the sum arguments
  have s1 : (P + R) + Q = (P + Q) + R := by abel
  have s2 : (P - R) + Q = (P + Q) - R := by abel
  have s3 : (Q + R) + P = (P + Q) + R := by abel
  have s4 : (Q - R) + P = (P + Q) - R := by abel
  rw [s1] at A
  rw [s2] at B
  rw [s3] at C
  rw [s4] at D
  -- assemble
  have f1 := four_pairing (P + Q) R
  have f2 := four_pairing P R
  have f3 := four_pairing Q R
  have key : canheight ((P + Q) + R) - canheight ((P + Q) - R)
      = (canheight (P + R) - canheight (P - R))
        + (canheight (Q + R) - canheight (Q - R)) := by
    linarith [A, B, C, D, h1, h2]
  linarith [f1, f2, f3, key]

/-- Additivity in the second slot, by symmetry of the pairing. -/
theorem pairing_comm (P Q : E5077a1.toAffine.Point) : pairing P Q = pairing Q P := by
  simp only [pairing, add_comm P Q]
  ring

theorem pairing_add_right (P Q R : E5077a1.toAffine.Point) :
    pairing P (Q + R) = pairing P Q + pairing P R := by
  rw [pairing_comm, pairing_add_left, pairing_comm Q P, pairing_comm R P]

end PrincipiaTractalis.BiAdditive5077a1

#print axioms PrincipiaTractalis.BiAdditive5077a1.par
#print axioms PrincipiaTractalis.BiAdditive5077a1.mul
#print axioms PrincipiaTractalis.BiAdditive5077a1.four_pairing
#print axioms PrincipiaTractalis.BiAdditive5077a1.pairing_add_left
#print axioms PrincipiaTractalis.BiAdditive5077a1.pairing_add_right
