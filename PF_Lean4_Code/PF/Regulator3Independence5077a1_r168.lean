/-
# PF.Regulator3Independence5077a1_r168

★★★ 2026-07-31 — NONZERO 3×3 REGULATOR ⟹ rank ≥ 3 ON 5077a1 ★★★

With r167's bi-additive pairing this is linear algebra.  For three points and
the Gram matrix

      ⎡ ĥP   ⟨P,Q⟩ ⟨P,R⟩ ⎤
  G = ⎢ ⟨P,Q⟩ ĥQ   ⟨Q,R⟩ ⎥ ,   `regDet3 = det G = abc + 2pqr − ar² − bq² − cp²`
      ⎣ ⟨P,R⟩ ⟨Q,R⟩ ĥR   ⎦

(writing `a = ĥP, b = ĥQ, c = ĥR, p = ⟨P,Q⟩, q = ⟨P,R⟩, r = ⟨Q,R⟩`), a relation
`m•P + n•Q + k•R = 0` with `(m,n,k) ≠ 0` forces `regDet3 = 0`.  Contrapositive:
`regDet3 ≠ 0` gives a `ℤ`-linear embedding `ℤ³ ↪ E5077a1(ℚ)`, hence rank ≥ 3.

## How bi-additivity is used

Pairing the relation against each of `P, Q, R` and using additivity and
`⟨k•X, Y⟩ = k⟨X,Y⟩` in the second slot gives the three scalar equations

  `a·m + p·n + q·k = 0`,  `p·m + b·n + r·k = 0`,  `q·m + r·n + c·k = 0`,

i.e. `G·(m,n,k)ᵗ = 0`.  Then `adj(G)·G = det(G)·I` gives `det(G)·m = 0` and
likewise for `n, k`, so `det G = 0` since some coordinate is nonzero.  The
adjugate step is done as three explicit `linear_combination` certificates
rather than through `Matrix.det`, keeping the file elementary; the first-column
cofactors are `bc − r²`, `qr − pc`, `pr − bq`, and one checks the `n` and `k`
coefficients cancel identically.

**Contrast with r152.**  At 2×2 no bi-additivity was available, so r152 used the
relation itself to rewrite `P ± Q` as multiples of a single point — a trick that
does not generalize to three points.  Here the honest bilinear route is
available because 5077a1 is torsion-free (r166b), which made the parallelogram
law unconditional (r167) and hence the pairing bi-additive.

HONEST SCOPE.  A criterion, not a rank bound for any specific triple.  Turning
it into `3 ≤ rank E5077a1(ℚ)` needs certified numerics showing `regDet3 > 0` for
three explicit points — the r153 analogue, at 3×3.  No such computation is done
here.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import PF.BiAdditive5077a1_r167

namespace PrincipiaTractalis.Regulator3Independence5077a1

open PrincipiaTractalis.CanonicalHeight5077a1
open PrincipiaTractalis.CanheightParallelogram5077a1 (pairing pairing_self)
open PrincipiaTractalis.CanheightMultiple5077a1 (canheight_zero)
open PrincipiaTractalis.BiAdditive5077a1
open PrincipiaTractalis.E5077a1RankOne (E5077a1)

/-! ## §1 — the pairing is a `ℤ`-linear form in each slot -/

theorem pairing_zero_left (Q : E5077a1.toAffine.Point) : pairing 0 Q = 0 := by
  simp only [pairing, zero_add, canheight_zero]; ring

theorem pairing_zero_right (P : E5077a1.toAffine.Point) : pairing P 0 = 0 := by
  simp only [pairing, add_zero, canheight_zero]; ring

/-- The pairing against a fixed `Q`, as an additive homomorphism. -/
noncomputable def pairHom (Q : E5077a1.toAffine.Point) :
    E5077a1.toAffine.Point →+ ℝ where
  toFun P := pairing P Q
  map_zero' := pairing_zero_left Q
  map_add' P P' := pairing_add_left P P' Q

theorem pairing_zsmul_left (P Q : E5077a1.toAffine.Point) (k : ℤ) :
    pairing (k • P) Q = (k : ℝ) * pairing P Q := by
  have h := (pairHom Q).map_zsmul P k
  simp only [pairHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  rw [h, zsmul_eq_mul]

theorem pairing_zsmul_right (P Q : E5077a1.toAffine.Point) (k : ℤ) :
    pairing P (k • Q) = (k : ℝ) * pairing P Q := by
  rw [pairing_comm, pairing_zsmul_left, pairing_comm]

/-! ## §2 — the 3×3 regulator determinant -/

/-- `det` of the Gram matrix of `ĥ` at `P, Q, R`. -/
noncomputable def regDet3 (P Q R : E5077a1.toAffine.Point) : ℝ :=
  canheight P * canheight Q * canheight R
    + 2 * pairing P Q * pairing P R * pairing Q R
    - canheight P * pairing Q R ^ 2
    - canheight Q * pairing P R ^ 2
    - canheight R * pairing P Q ^ 2

/-! ## §3 — a relation forces the determinant to vanish -/

section Relation

variable {P Q R : E5077a1.toAffine.Point} {m n k : ℤ}

/-- Pairing the relation against `P`, `Q`, `R` gives `G·(m,n,k)ᵗ = 0`. -/
theorem gram_rows (hrel : m • P + n • Q + k • R = 0) :
    canheight P * (m : ℝ) + pairing P Q * (n : ℝ) + pairing P R * (k : ℝ) = 0 ∧
    pairing P Q * (m : ℝ) + canheight Q * (n : ℝ) + pairing Q R * (k : ℝ) = 0 ∧
    pairing P R * (m : ℝ) + pairing Q R * (n : ℝ) + canheight R * (k : ℝ) = 0 := by
  have expand : ∀ X : E5077a1.toAffine.Point,
      pairing X (m • P + n • Q + k • R)
        = (m : ℝ) * pairing X P + (n : ℝ) * pairing X Q + (k : ℝ) * pairing X R := by
    intro X
    rw [pairing_add_right, pairing_add_right, pairing_zsmul_right,
      pairing_zsmul_right, pairing_zsmul_right]
  refine ⟨?_, ?_, ?_⟩
  · have h := expand P
    rw [hrel, pairing_zero_right, pairing_self] at h
    linarith [h]
  · have h := expand Q
    rw [hrel, pairing_zero_right, pairing_self] at h
    rw [pairing_comm P Q] at *
    linarith [h]
  · have h := expand R
    rw [hrel, pairing_zero_right, pairing_self] at h
    rw [pairing_comm P R, pairing_comm Q R] at *
    linarith [h]

/-- **★ A relation kills the determinant ★** -/
theorem regDet3_eq_zero_of_relation (hrel : m • P + n • Q + k • R = 0)
    (hne : ¬ (m = 0 ∧ n = 0 ∧ k = 0)) : regDet3 P Q R = 0 := by
  obtain ⟨e1, e2, e3⟩ := gram_rows hrel
  set a := canheight P; set b := canheight Q; set c := canheight R
  set p := pairing P Q; set q := pairing P R; set r := pairing Q R
  -- adj(G)·G = det(G)·I, one column at a time
  have hm : regDet3 P Q R * (m : ℝ) = 0 := by
    simp only [regDet3]
    linear_combination (b * c - r ^ 2) * e1 + (q * r - p * c) * e2
      + (p * r - b * q) * e3
  have hn : regDet3 P Q R * (n : ℝ) = 0 := by
    simp only [regDet3]
    linear_combination (q * r - p * c) * e1 + (a * c - q ^ 2) * e2
      + (p * q - a * r) * e3
  have hk : regDet3 P Q R * (k : ℝ) = 0 := by
    simp only [regDet3]
    linear_combination (p * r - b * q) * e1 + (p * q - a * r) * e2
      + (a * b - p ^ 2) * e3
  rcases not_and_or.mp hne with h | h
  · exact (mul_eq_zero.mp hm).resolve_right (Int.cast_ne_zero.mpr h)
  · rcases not_and_or.mp h with h' | h'
    · exact (mul_eq_zero.mp hn).resolve_right (Int.cast_ne_zero.mpr h')
    · exact (mul_eq_zero.mp hk).resolve_right (Int.cast_ne_zero.mpr h')

end Relation

/-! ## §4 — the criterion and the rank bound -/

theorem independent_of_regDet3_ne_zero {P Q R : E5077a1.toAffine.Point}
    (hdet : regDet3 P Q R ≠ 0) {m n k : ℤ}
    (hrel : m • P + n • Q + k • R = 0) : m = 0 ∧ n = 0 ∧ k = 0 := by
  by_contra hne
  exact hdet (regDet3_eq_zero_of_relation hrel hne)

/-- `(m,n,k) ↦ mP + nQ + kR`, as a `ℤ`-linear map. -/
noncomputable def tripleMap (P Q R : E5077a1.toAffine.Point) :
    (Fin 3 → ℤ) →ₗ[ℤ] E5077a1.toAffine.Point where
  toFun v := v 0 • P + v 1 • Q + v 2 • R
  map_add' u v := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]

/-- **★★★ r168 — NONZERO 3×3 REGULATOR ⟹ rank ≥ 3 ★★★** -/
theorem rank_ge_three_of_regDet3_ne_zero {P Q R : E5077a1.toAffine.Point}
    (hdet : regDet3 P Q R ≠ 0) :
    3 ≤ Module.rank ℤ E5077a1.toAffine.Point := by
  have hinj : Function.Injective (tripleMap P Q R) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hrel : v 0 • P + v 1 • Q + v 2 • R = 0 := hv
    obtain ⟨h0, h1, h2⟩ := independent_of_regDet3_ne_zero hdet hrel
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hrank := LinearMap.lift_rank_le_of_injective (tripleMap P Q R) hinj
  have h3 : Module.rank ℤ (Fin 3 → ℤ) = 3 := by simp
  rw [h3] at hrank
  simp only [Cardinal.lift_ofNat, Cardinal.lift_id] at hrank
  exact hrank

end PrincipiaTractalis.Regulator3Independence5077a1

#print axioms PrincipiaTractalis.Regulator3Independence5077a1.pairing_zsmul_left
#print axioms PrincipiaTractalis.Regulator3Independence5077a1.gram_rows
#print axioms PrincipiaTractalis.Regulator3Independence5077a1.regDet3_eq_zero_of_relation
#print axioms PrincipiaTractalis.Regulator3Independence5077a1.rank_ge_three_of_regDet3_ne_zero
