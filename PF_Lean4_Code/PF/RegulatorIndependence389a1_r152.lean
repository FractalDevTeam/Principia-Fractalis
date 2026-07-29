/-
# PF.RegulatorIndependence389a1_r152

★★★ 2026-07-28 — r152: NONZERO REGULATOR ⟹ INDEPENDENCE ⟹ rank ≥ 2 ★★★

The independence criterion — and it needs **no bi-additivity of the pairing**.

The standard route to `ĥ(mP+nQ) = m²ĥP + 2mn⟨P,Q⟩ + n²ĥQ` requires
polarizing the parallelogram law at half a dozen point pairs, each carrying
four non-torsion side conditions.  That is avoidable: *if a relation
`mP + nQ = 0` exists, the relation itself expresses `P ± Q` as multiples of
`P`*, and r151's multiple law finishes the computation.

Given `mP + nQ = 0` with `n ≠ 0`:

    `n(P+Q) = nP + nQ = nP − mP = (n−m)P`
    `n(P−Q) = nP − nQ = nP + mP = (n+m)P`

so by r151, `n²ĥ(P±Q) = (n∓m)²ĥP`.  Feeding these into r150's
parallelogram law `ĥ(P+Q) + ĥ(P−Q) = 2ĥP + 2ĥQ` gives `m²ĥP = n²ĥQ`, and the
same substitution in `2⟨P,Q⟩ = ĥ(P+Q) − ĥP − ĥQ` gives `n⟨P,Q⟩ = −mĥP`.
Hence

    `n²·(ĥP·ĥQ − ⟨P,Q⟩²) = m²ĥP² − m²ĥP² = 0`,

i.e. **a relation forces the regulator determinant to vanish**.  Only ONE
application of the parallelogram law is used, at the pair `(P,Q)` itself —
whose side conditions are exactly the hypotheses already in hand.

Contrapositive + the `ℤ²` embedding gives the target:

    `det ≠ 0  ⟹  2 ≤ Module.rank ℤ E389a1(ℚ)`.

HONEST SCOPE.  This is the *conditional* rank bound.  Establishing
`det ≠ 0` numerically for the LMFDB generators `P = (0,0)`, `Q = (1,0)` is
r153 (rational interval arithmetic on `canheight_window`); the unconditional
flag is r154.  Nothing here asserts a value for the regulator.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.CanheightMultiple389a1_r151

namespace PrincipiaTractalis.RegulatorIndependence389a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E389a1RankOne
open PrincipiaTractalis.CanonicalHeight389a1
open PrincipiaTractalis.CanheightParallelogram389a1
open PrincipiaTractalis.CanheightMultiple389a1
open WeierstrassCurve WeierstrassCurve.Affine

/-- The regulator determinant of a pair of points. -/
noncomputable def regDet (P Q : E389a1.toAffine.Point) : ℝ :=
  canheight P * canheight Q - pairing P Q ^ 2

/-! ## §1 — a relation forces the determinant to vanish -/

section Relation

variable {P Q : E389a1.toAffine.Point}

/-- From a relation, `n(P+Q) = (n−m)P`. -/
theorem nsmul_sum_eq {m n : ℤ} (hrel : m • P + n • Q = 0) :
    n • (P + Q) = (n - m) • P := by
  have hnQ : n • Q = -(m • P) := by
    have : m • P + n • Q = 0 := hrel
    linear_combination (norm := abel) this
  rw [smul_add, hnQ, sub_smul]
  abel

/-- From a relation, `n(P−Q) = (n+m)P`. -/
theorem nsmul_dif_eq {m n : ℤ} (hrel : m • P + n • Q = 0) :
    n • (P - Q) = (n + m) • P := by
  have hnQ : n • Q = -(m • P) := by
    have : m • P + n • Q = 0 := hrel
    linear_combination (norm := abel) this
  rw [smul_sub, hnQ, add_smul]
  abel

/-- **The two height identities forced by a relation.** -/
theorem height_sum_dif (hP : ¬ IsOfFinAddOrder P)
    (hsum : ¬ IsOfFinAddOrder (P + Q)) (hdif : ¬ IsOfFinAddOrder (P - Q))
    {m n : ℤ} (hrel : m • P + n • Q = 0) :
    (n : ℝ) ^ 2 * canheight (P + Q) = ((n : ℝ) - m) ^ 2 * canheight P ∧
    (n : ℝ) ^ 2 * canheight (P - Q) = ((n : ℝ) + m) ^ 2 * canheight P := by
  constructor
  · have h1 : canheight (n • (P + Q)) = (n : ℝ) ^ 2 * canheight (P + Q) :=
      canheight_zsmul hsum n
    have h2 : canheight ((n - m) • P) = ((n : ℝ) - m) ^ 2 * canheight P := by
      have := canheight_zsmul hP (n - m)
      push_cast at this
      exact this
    rw [← h1, nsmul_sum_eq hrel, h2]
  · have h1 : canheight (n • (P - Q)) = (n : ℝ) ^ 2 * canheight (P - Q) :=
      canheight_zsmul hdif n
    have h2 : canheight ((n + m) • P) = ((n : ℝ) + m) ^ 2 * canheight P := by
      have := canheight_zsmul hP (n + m)
      push_cast at this
      exact this
    rw [← h1, nsmul_dif_eq hrel, h2]

/-- **★ A relation forces `regDet = 0`.**  Only one use of the parallelogram
law, at the pair `(P,Q)` itself. -/
theorem regDet_eq_zero_of_relation (hP : ¬ IsOfFinAddOrder P)
    (hQ : ¬ IsOfFinAddOrder Q) (hsum : ¬ IsOfFinAddOrder (P + Q))
    (hdif : ¬ IsOfFinAddOrder (P - Q)) {m n : ℤ} (hrel : m • P + n • Q = 0)
    (hn : n ≠ 0) : regDet P Q = 0 := by
  obtain ⟨hS, hD⟩ := height_sum_dif hP hsum hdif hrel
  have hpar := canheight_parallelogram hP hQ hsum hdif
  have hnR : ((n : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hn
  -- m²ĥP = n²ĥQ, obtained by adding the two identities and using the law
  have hmn : (m : ℝ) ^ 2 * canheight P = (n : ℝ) ^ 2 * canheight Q := by
    have hsumeq : (n : ℝ) ^ 2 * (canheight (P + Q) + canheight (P - Q))
        = (((n : ℝ) - m) ^ 2 + ((n : ℝ) + m) ^ 2) * canheight P := by
      rw [mul_add, hS, hD]; ring
    rw [hpar] at hsumeq
    nlinarith [hsumeq]
  -- n⟨P,Q⟩ = −mĥP
  have hpair : (n : ℝ) * pairing P Q = -((m : ℝ) * canheight P) := by
    have hbase : 2 * pairing P Q
        = canheight (P + Q) - canheight P - canheight Q := by
      simp only [pairing]; ring
    have hstep : (n : ℝ) ^ 2 * (2 * pairing P Q)
        = -(2 * (m : ℝ) * (n : ℝ) * canheight P) := by
      rw [hbase, mul_sub, mul_sub, hS, ← hmn]
      ring
    have h2n : (2 * (n : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hnR
    have hcan : (2 * (n : ℝ)) * ((n : ℝ) * pairing P Q)
        = (2 * (n : ℝ)) * (-((m : ℝ) * canheight P)) := by
      linear_combination hstep
    exact mul_left_cancel₀ h2n hcan
  -- assemble: n²·regDet = m²ĥP² − m²ĥP² = 0
  have hkey : (n : ℝ) ^ 2 * regDet P Q = 0 := by
    simp only [regDet]
    have e1 : (n : ℝ) ^ 2 * (canheight P * canheight Q)
        = canheight P * ((n : ℝ) ^ 2 * canheight Q) := by ring
    have e2 : (n : ℝ) ^ 2 * pairing P Q ^ 2
        = ((n : ℝ) * pairing P Q) ^ 2 := by ring
    rw [mul_sub, e1, e2, ← hmn, hpair]
    ring
  have hn2 : ((n : ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 hnR
  exact (mul_eq_zero.mp hkey).resolve_left hn2

end Relation

/-! ## §2 — nonzero determinant ⟹ independence -/

/-- **★★ Independence from a nonzero regulator. ★★**  If `regDet P Q ≠ 0`
then no nontrivial integer relation holds between `P` and `Q`. -/
theorem independent_of_regDet_ne_zero {P Q : E389a1.toAffine.Point}
    (hP : ¬ IsOfFinAddOrder P) (hQ : ¬ IsOfFinAddOrder Q)
    (hsum : ¬ IsOfFinAddOrder (P + Q)) (hdif : ¬ IsOfFinAddOrder (P - Q))
    (hdet : regDet P Q ≠ 0) {m n : ℤ} (hrel : m • P + n • Q = 0) :
    m = 0 ∧ n = 0 := by
  rcases eq_or_ne n 0 with hn | hn
  · -- n = 0 : then m·P = 0, so m = 0 (P is non-torsion)
    subst hn
    simp only [zero_smul, add_zero] at hrel
    refine ⟨?_, rfl⟩
    by_contra hm
    have htor : IsOfFinAddOrder (m • P) := by
      rw [hrel]; exact zero_isOfFinAddOrder
    exact zsmul_nonTorsion hP hm htor
  · exact absurd (regDet_eq_zero_of_relation hP hQ hsum hdif hrel hn) hdet

/-! ## §3 — THE CONDITIONAL FLAG: rank ≥ 2 -/

/-- The `ℤ`-linear map `ℤ² → E(ℚ)` given by a pair of points. -/
noncomputable def pairMap (P Q : E389a1.toAffine.Point) :
    (Fin 2 → ℤ) →ₗ[ℤ] E389a1.toAffine.Point where
  toFun v := v 0 • P + v 1 • Q
  map_add' u v := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]

/-- **★★★ r152 — NONZERO REGULATOR ⟹ rank ≥ 2 ★★★**

If `P, Q, P+Q, P−Q` are non-torsion and the regulator determinant
`ĥP·ĥQ − ⟨P,Q⟩²` is nonzero, then `ℤ²` embeds `ℤ`-linearly in `E389a1(ℚ)`,
so its Mordell–Weil rank is at least `2`. -/
theorem rank_ge_two_of_regDet_ne_zero {P Q : E389a1.toAffine.Point}
    (hP : ¬ IsOfFinAddOrder P) (hQ : ¬ IsOfFinAddOrder Q)
    (hsum : ¬ IsOfFinAddOrder (P + Q)) (hdif : ¬ IsOfFinAddOrder (P - Q))
    (hdet : regDet P Q ≠ 0) :
    2 ≤ Module.rank ℤ E389a1.toAffine.Point := by
  have hinj : Function.Injective (pairMap P Q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hrel : v 0 • P + v 1 • Q = 0 := hv
    obtain ⟨h0, h1⟩ := independent_of_regDet_ne_zero hP hQ hsum hdif hdet hrel
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hrank := LinearMap.lift_rank_le_of_injective (pairMap P Q) hinj
  have h2 : Module.rank ℤ (Fin 2 → ℤ) = 2 := by
    simp
  rw [h2] at hrank
  simp only [Cardinal.lift_ofNat, Cardinal.lift_id] at hrank
  exact hrank

end PrincipiaTractalis.RegulatorIndependence389a1

#print axioms PrincipiaTractalis.RegulatorIndependence389a1.height_sum_dif
#print axioms PrincipiaTractalis.RegulatorIndependence389a1.regDet_eq_zero_of_relation
#print axioms PrincipiaTractalis.RegulatorIndependence389a1.independent_of_regDet_ne_zero
#print axioms PrincipiaTractalis.RegulatorIndependence389a1.rank_ge_two_of_regDet_ne_zero
