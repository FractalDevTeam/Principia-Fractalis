/-
# PF.CanheightParallelogram5077a1_r164

★★★ 2026-07-30 — r164: THE EXACT PARALLELOGRAM LAW FOR ĥ ON 5077a1 ★★★

The limit step for the rank-3 curve.  r163 bounds the quasi-parallelogram
*defect* by `log 1692064` uniformly.  Applying it at `(2ⁿP, 2ⁿQ)` and dividing
by `4ⁿ`, the defect of the scaled sequences is `≤ log 1692064 / 4ⁿ → 0`, so in
the limit the canonical height of r156 satisfies the parallelogram law
**exactly**:

    `ĥ(P+Q) + ĥ(P−Q) = 2·ĥ(P) + 2·ĥ(Q)`.

The constant vanishes in the limit, which is why r162 could afford the 6%
slack in `1692064 = 105754·16` rather than the true ceiling `1596851`: the
value of the constant never reaches this statement.

This is what makes `ĥ` a quadratic form on 5077a1, hence what makes a
regulator argument possible: with `⟨P,Q⟩ := (ĥ(P+Q) − ĥP − ĥQ)/2` the map
`(m,n) ↦ ĥ(mP + nQ)` becomes `m²ĥP + 2mn⟨P,Q⟩ + n²ĥQ`.

Structure (identical to 389a1's r150 — none of it is curve-specific beyond
the constant):

* `smul_ne_zero_of_nonTorsion` — `2ⁿR ≠ 0` for non-torsion `R`;
* `x_ne_at_all_levels` — if `P+Q` and `P−Q` are non-torsion then
  `x(2ⁿP) ≠ x(2ⁿQ)` for every `n` (equality would force `2ⁿ(P∓Q) = 0`);
* `scaled_defect_le` — the `4ⁿ`-scaled defect is `≤ log 1692064 / 4ⁿ`;
* `canheight_parallelogram` — the capstone, by uniqueness of limits;
* `pairing`, `canheight_sub`, `pairing_self` — the immediate corollaries.

HONEST SCOPE.  The parallelogram law for `ĥ` on 5077a1 and its immediate
corollaries, under the stated non-torsion hypotheses on `P, Q, P±Q`.  The
multiple law `ĥ(kR) = k²ĥ(R)` is the r151 analogue and is NOT proved here.

**On rank 3.**  This stone does not advance the 3×3 independence step.  r152's
route — use a relation `mP+nQ = 0` to rewrite `P±Q` as multiples of `P`, so
that one application of the parallelogram law forces `det = 0` — does not
generalize to three points.  A 3×3 Sylvester argument appears to need genuine
bi-additivity of `⟨·,·⟩`, which the parallelogram law alone does not give.
That obstruction is unchanged by this file.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-30.
-/
import PF.PointQuasiParallelogram5077a1_r163

namespace PrincipiaTractalis.CanheightParallelogram5077a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E5077a1RankOne
open PrincipiaTractalis.CanonicalHeight5077a1
open PrincipiaTractalis.PointQuasiParallelogram5077a1
open PrincipiaTractalis.QuasiParallelogramLower5077a1
open WeierstrassCurve WeierstrassCurve.Affine
open Filter Topology

/-! ## §1 — non-torsion points have nonzero dyadic multiples -/

/-- For non-torsion `R`, every `2ⁿ·R` is nonzero (hence affine). -/
theorem smul_ne_zero_of_nonTorsion {R : E5077a1.toAffine.Point}
    (hR : ¬ IsOfFinAddOrder R) (n : ℕ) : ((2 : ℤ) ^ n) • R ≠ 0 := by
  intro h0
  exact hR (isOfFinAddOrder_iff_zsmul_eq_zero.mpr
    ⟨(2 : ℤ) ^ n, by positivity, h0⟩)

/-- Affine data for a nonzero point. -/
theorem exists_affine {R : E5077a1.toAffine.Point} (hR : R ≠ 0) :
    ∃ x y, ∃ h : E5077a1.toAffine.Nonsingular x y, R = Point.some h := by
  rcases R with _ | @⟨x, y, h⟩
  · exact absurd rfl hR
  · exact ⟨x, y, h, rfl⟩

/-! ## §2 — distinct x-coordinates at every dyadic level -/

/-- If `P + Q` and `P − Q` are both non-torsion then `2ⁿP ≠ ±2ⁿQ`, hence
their x-coordinates differ, for every `n`. -/
theorem x_ne_at_all_levels {P Q : E5077a1.toAffine.Point}
    (hsum : ¬ IsOfFinAddOrder (P + Q)) (hdif : ¬ IsOfFinAddOrder (P - Q))
    (n : ℕ) {xp yp xq yq : ℚ}
    {hp : E5077a1.toAffine.Nonsingular xp yp} {hq : E5077a1.toAffine.Nonsingular xq yq}
    (hP : ((2 : ℤ) ^ n) • P = Point.some hp)
    (hQ : ((2 : ℤ) ^ n) • Q = Point.some hq) : xp ≠ xq := by
  intro hx
  subst hx
  rcases eq_or_eq_neg_of_x_eq hp hq with h | h
  · -- 2ⁿP = 2ⁿQ ⟹ 2ⁿ(P−Q) = 0 ⟹ P−Q torsion
    have h0 : ((2 : ℤ) ^ n) • (P - Q) = 0 := by
      rw [smul_sub, hP, hQ, h, sub_self]
    exact hdif (isOfFinAddOrder_iff_zsmul_eq_zero.mpr
      ⟨(2 : ℤ) ^ n, by positivity, h0⟩)
  · -- 2ⁿP = −2ⁿQ ⟹ 2ⁿ(P+Q) = 0 ⟹ P+Q torsion
    have h0 : ((2 : ℤ) ^ n) • (P + Q) = 0 := by
      rw [smul_add, hP, hQ, h, neg_add_cancel]
    exact hsum (isOfFinAddOrder_iff_zsmul_eq_zero.mpr
      ⟨(2 : ℤ) ^ n, by positivity, h0⟩)

/-! ## §3 — the scaled defect tends to zero -/

/-- **The defect at dyadic level `n`.**  Applying r163's bound to the pair
`(2ⁿP, 2ⁿQ)` and dividing by `4ⁿ`. -/
theorem scaled_defect_le {P Q : E5077a1.toAffine.Point}
    (hP : ¬ IsOfFinAddOrder P) (hQ : ¬ IsOfFinAddOrder Q)
    (hsum : ¬ IsOfFinAddOrder (P + Q)) (hdif : ¬ IsOfFinAddOrder (P - Q))
    (n : ℕ) :
    |hseq (P + Q) n + hseq (P - Q) n - 2 * hseq P n - 2 * hseq Q n|
      ≤ Real.log 1692064 / 4 ^ n := by
  -- affine data at level n
  obtain ⟨xp, yp, hp, hPn⟩ := exists_affine (smul_ne_zero_of_nonTorsion hP n)
  obtain ⟨xq, yq, hq, hQn⟩ := exists_affine (smul_ne_zero_of_nonTorsion hQ n)
  have hne : xp ≠ xq := x_ne_at_all_levels hsum hdif n hPn hQn
  -- the unscaled defect at level n
  have hdefect := lognh_defect_le hp hq hne
  -- identify the four points
  have e1 : ((2 : ℤ) ^ n) • (P + Q) = Point.some hp + Point.some hq := by
    rw [smul_add, hPn, hQn]
  have e2 : ((2 : ℤ) ^ n) • (P - Q) = Point.some hp - Point.some hq := by
    rw [smul_sub, hPn, hQn]
  -- rewrite the scaled defect
  have hexp : (0 : ℝ) < 4 ^ n := by positivity
  have key : hseq (P + Q) n + hseq (P - Q) n - 2 * hseq P n - 2 * hseq Q n
      = (lognh (Point.some hp + Point.some hq)
          + lognh (Point.some hp - Point.some hq)
          - 2 * lognh (Point.some hp) - 2 * lognh (Point.some hq)) / 4 ^ n := by
    simp only [hseq, e1, e2, hPn, hQn]
    field_simp
  rw [key, abs_div, abs_of_pos hexp]
  gcongr

/-! ## §4 — THE CAPSTONE: the exact parallelogram law -/

/-- **★★★ r150 — THE PARALLELOGRAM LAW FOR THE CANONICAL HEIGHT ★★★**

For `P, Q` with `P`, `Q`, `P+Q`, `P−Q` all non-torsion:

    `ĥ(P+Q) + ĥ(P−Q) = 2·ĥ(P) + 2·ĥ(Q)`.

The quasi-parallelogram defect is uniformly `≤ log 1692064` (r163); at dyadic
level `n` the scaled defect is `≤ log 1692064 / 4ⁿ`, which tends to `0`, while
the scaled sequences tend to the canonical heights (r156).  Uniqueness of
limits closes it. -/
theorem canheight_parallelogram {P Q : E5077a1.toAffine.Point}
    (hP : ¬ IsOfFinAddOrder P) (hQ : ¬ IsOfFinAddOrder Q)
    (hsum : ¬ IsOfFinAddOrder (P + Q)) (hdif : ¬ IsOfFinAddOrder (P - Q)) :
    canheight (P + Q) + canheight (P - Q)
      = 2 * canheight P + 2 * canheight Q := by
  set F : ℕ → ℝ := fun n =>
    hseq (P + Q) n + hseq (P - Q) n - 2 * hseq P n - 2 * hseq Q n with hF
  -- F tends to the canonical-height combination
  have hL : Tendsto F atTop
      (𝓝 (canheight (P + Q) + canheight (P - Q)
            - 2 * canheight P - 2 * canheight Q)) := by
    simp only [hF]
    exact (((tendsto_hseq (P + Q)).add (tendsto_hseq (P - Q))).sub
      ((tendsto_hseq P).const_mul 2)).sub ((tendsto_hseq Q).const_mul 2)
  -- F tends to 0 by the geometric bound
  have hZ : Tendsto F atTop (𝓝 0) := by
    have hbound : ∀ n, |F n| ≤ Real.log 1692064 / 4 ^ n := fun n =>
      scaled_defect_le hP hQ hsum hdif n
    have htend : Tendsto (fun n : ℕ => Real.log 1692064 / 4 ^ n) atTop (𝓝 0) := by
      have h4 : Tendsto (fun n : ℕ => ((1 : ℝ) / 4) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have := h4.const_mul (Real.log 1692064)
      simpa [div_eq_mul_inv, one_div, inv_pow, mul_comm] using this
    exact squeeze_zero_norm hbound htend
  -- uniqueness of limits
  have := tendsto_nhds_unique hL hZ
  linarith [this]

/-- The pairing induced by the parallelogram law. -/
noncomputable def pairing (P Q : E5077a1.toAffine.Point) : ℝ :=
  (canheight (P + Q) - canheight P - canheight Q) / 2

/-- The parallelogram law in "difference" form: `ĥ(P−Q) = ĥP + ĥQ − 2⟨P,Q⟩`. -/
theorem canheight_sub {P Q : E5077a1.toAffine.Point}
    (hP : ¬ IsOfFinAddOrder P) (hQ : ¬ IsOfFinAddOrder Q)
    (hsum : ¬ IsOfFinAddOrder (P + Q)) (hdif : ¬ IsOfFinAddOrder (P - Q)) :
    canheight (P - Q) = canheight P + canheight Q - 2 * pairing P Q := by
  have h := canheight_parallelogram hP hQ hsum hdif
  simp only [pairing]
  linarith [h]

/-- `⟨P,P⟩ = ĥ(P)` — the pairing is normalized so its diagonal is the height.
(Uses only `ĥ(2P) = 4ĥ(P)` from r156, no parallelogram needed.) -/
theorem pairing_self (P : E5077a1.toAffine.Point) : pairing P P = canheight P := by
  simp only [pairing, canheight_dbl P]
  ring

end PrincipiaTractalis.CanheightParallelogram5077a1

#print axioms PrincipiaTractalis.CanheightParallelogram5077a1.smul_ne_zero_of_nonTorsion
#print axioms PrincipiaTractalis.CanheightParallelogram5077a1.x_ne_at_all_levels
#print axioms PrincipiaTractalis.CanheightParallelogram5077a1.scaled_defect_le
#print axioms PrincipiaTractalis.CanheightParallelogram5077a1.canheight_parallelogram
#print axioms PrincipiaTractalis.CanheightParallelogram5077a1.canheight_sub
#print axioms PrincipiaTractalis.CanheightParallelogram5077a1.pairing_self
