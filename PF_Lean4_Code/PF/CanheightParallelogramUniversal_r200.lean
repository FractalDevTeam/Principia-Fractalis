/-
# PF.CanheightParallelogramUniversal_r200

★★★ 2026-08-05 — THE EXACT PARALLELOGRAM LAW, UNIVERSALLY ★★★

r150 proved the exact parallelogram law for the canonical height of 389a1.
This stone proves it for EVERY Weierstrass curve over ℚ with integer
b-invariants, nonzero discriminant, and no rational 2-torsion:

    `ĥ(P+Q) + ĥ(P−Q) = 2·ĥ(P) + 2·ĥ(Q)`.

The chain is r150's, with every per-curve input replaced by its universal
counterpart:

* the quasi-parallelogram defect bound is r199's `lognhX_defect_le`
  (`≤ log Cpar`, coefficients only);
* the height window is r179's `heightWindow_of_xdbl_ne_zero`, discharged
  by r199's `Psi_ne_zero` and `X_dbl`;
* the canonical height is r171's generic `canheight`.

The no-rational-2-torsion hypothesis `h2tor : ∀ R ≠ 0, 2•R ≠ 0` is the
honest residue: general curves have rational 2-torsion, and r179's
Ψ-nonvanishing genuinely fails there.  It replaces r150's per-point
non-torsion hypotheses (and implies the ones r150 needed, since `2ⁿR = 0`
for `R ≠ 0` forces a 2-torsion point along the way).

Structure (mirrors r150):

* `smul_ne_zero_of_two_torsion_free` — `2ⁿR ≠ 0` for `R ≠ 0`;
* `exists_affine` — affine data for a nonzero point;
* `x_ne_at_all_levels` — `x(2ⁿP) ≠ x(2ⁿQ)` for all `n`;
* `heightWindow_universal` — the r179 window, discharged universally;
* `scaled_defect_le` — the `4ⁿ`-scaled defect is `≤ log Cpar / 4ⁿ`;
* `canheight_parallelogram_universal` — the capstone, by uniqueness of
  limits;
* `canheight_sub_universal`, `pairing_self_universal` — the r150
  corollaries.

HONEST SCOPE.  The parallelogram law for the canonical height on the point
group of any rational Weierstrass curve with integer b-invariants, nonzero
discriminant, and no rational 2-torsion.  No bilinearity over ℤ, no
regulator, no rank claim.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-05.
-/
import PF.PointParallelogramUniversal_r199
import PF.DuplicationLogWindowFixed_r179

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.CanheightParallelogramUniversal

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationLogWindow
open PrincipiaTractalis.CanonicalHeightGeneric
open PrincipiaTractalis.PointParallelogramUniversal
open WeierstrassCurve WeierstrassCurve.Affine
open Filter Topology

variable {W : WeierstrassCurve.Affine ℚ} {B₂ B₄ B₆ B₈ : ℤ}
variable {xP yP xQ yQ : ℚ}

/-! ## §0 — bookkeeping -/

/-- Affine points are nonzero. -/
theorem some_ne_zero {x y : ℚ} (h : W.Nonsingular x y) :
    Point.some h ≠ 0 :=
  fun hc => Point.noConfusion hc

/-- Affine data for a nonzero point. -/
theorem exists_affine {R : W.Point} (hR : R ≠ 0) :
    ∃ x y, ∃ h : W.Nonsingular x y, R = Point.some h := by
  rcases R with _ | @⟨x, y, h⟩
  · exact absurd rfl hR
  · exact ⟨x, y, h, rfl⟩

/-- `X` sends the point at infinity to `0`. -/
theorem X_zero : X (0 : W.Point) = 0 := rfl

/-- r199's `lognhX` is the r177 `lognh` composed with `X`. -/
theorem lognhX_eq_lognh (R : W.Point) : lognhX R = lognh (X R) := by
  simp only [lognhX, lognh]
  congr 1
  exact_mod_cast naiveHeight_eq_nh (X R)

/-- The ℤ-form of the b-relation, from mathlib's over ℚ. -/
theorem b_relation_int (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ)) :
    4 * B₈ = B₂ * B₆ - B₄ ^ 2 := by
  have h := W.b_relation
  rw [h₂, h₄, h₆, h₈] at h
  exact_mod_cast h

/-! ## §1 — no rational 2-torsion: dyadic multiples stay nonzero -/

/-- With no rational 2-torsion, every `2ⁿ·R` of a nonzero `R` is nonzero. -/
theorem smul_ne_zero_of_two_torsion_free
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    {R : W.Point} (hR : R ≠ 0) (n : ℕ) : ((2 : ℤ) ^ n) • R ≠ 0 := by
  induction n with
  | zero => simpa using hR
  | succ k ih =>
      have h := h2tor (((2 : ℤ) ^ k) • R) ih
      rw [two_nsmul] at h
      rw [two_pow_succ_zsmul]
      exact h

/-! ## §2 — distinct x-coordinates at every dyadic level -/

/-- If `P + Q` and `P − Q` are both nonzero then `2ⁿP ≠ ±2ⁿQ`, hence their
x-coordinates differ, for every `n`. -/
theorem x_ne_at_all_levels
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    {P Q : W.Point} (hsum : P + Q ≠ 0) (hdif : P - Q ≠ 0)
    (n : ℕ) {xp yp xq yq : ℚ}
    {hp : W.Nonsingular xp yp} {hq : W.Nonsingular xq yq}
    (hPn : ((2 : ℤ) ^ n) • P = Point.some hp)
    (hQn : ((2 : ℤ) ^ n) • Q = Point.some hq) : xp ≠ xq := by
  intro hx
  subst hx
  rcases eq_or_eq_neg_of_x_eq hp hq with h | h
  · -- 2ⁿP = 2ⁿQ ⟹ 2ⁿ(P−Q) = 0, impossible
    have h0 : ((2 : ℤ) ^ n) • (P - Q) = 0 := by
      rw [smul_sub, hPn, hQn, h, sub_self]
    exact smul_ne_zero_of_two_torsion_free h2tor hdif n h0
  · -- 2ⁿP = −2ⁿQ ⟹ 2ⁿ(P+Q) = 0, impossible
    have h0 : ((2 : ℤ) ^ n) • (P + Q) = 0 := by
      rw [smul_add, hPn, hQn, h, neg_add_cancel]
    exact smul_ne_zero_of_two_torsion_free h2tor hsum n h0

/-! ## §3 — the r179 window, discharged universally -/

/-- `Ψ ≠ 0` at every nonzero point, from no rational 2-torsion
(r199's `Psi_ne_zero` in the ∀-form r179 asks for). -/
theorem PsiX_ne_zero (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ))
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (R : W.Point) (hR : R ≠ 0) :
    Psi B₂ B₄ B₆ (X R).num ((X R).den : ℤ) ≠ 0 := by
  obtain ⟨x, y, h, rfl⟩ := exists_affine hR
  have hy := y_ne_negY_of_two_smul_ne_zero h (h2tor _ hR)
  simpa using Psi_ne_zero h₂ h₄ h₆ h hy

/-- `X` intertwines doubling with `dblQ` away from `0`
(r199's `X_dbl` in the ∀-form r179 asks for). -/
theorem X_dbl_of_ne_zero (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (R : W.Point) (hR : R ≠ 0) :
    X (R + R) = dblQ B₂ B₄ B₆ B₈ (X R) := by
  obtain ⟨x, y, h, rfl⟩ := exists_affine hR
  have hy := y_ne_negY_of_two_smul_ne_zero h (h2tor _ hR)
  simpa using X_dbl h₂ h₄ h₆ h₈ h hy

/-- **The universal height window** on the point group of any rational
Weierstrass curve with integer b-invariants, nonzero discriminant, and no
rational 2-torsion. -/
theorem heightWindow_universal (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0) :
    HeightWindow (fun R : W.Point => lognh (X R))
      (kappa B₂ B₄ B₆ B₈ : ℝ) :=
  heightWindow_of_xdbl_ne_zero (b_relation_int h₂ h₄ h₆ h₈) hΔ X X_zero
    (PsiX_ne_zero h₂ h₄ h₆ h2tor)
    (X_dbl_of_ne_zero h₂ h₄ h₆ h₈ h2tor)

/-- The canonical height on the point group of `W`, via the generic r171
construction over the universal x-coordinate height. -/
noncomputable def canheightW (W : WeierstrassCurve.Affine ℚ) :
    W.Point → ℝ :=
  canheight (fun R : W.Point => lognh (X R))

/-! ## §4 — the scaled defect tends to zero -/

/-- **The defect at dyadic level `n`.**  Applying r199's bound to the pair
`(2ⁿP, 2ⁿQ)` and dividing by `4ⁿ`. -/
theorem scaled_defect_le (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hne : xP ≠ xQ)
    (n : ℕ) :
    |hseq (fun R : W.Point => lognh (X R))
        (Point.some hP + Point.some hQ) n
      + hseq (fun R : W.Point => lognh (X R))
          (Point.some hP - Point.some hQ) n
      - 2 * hseq (fun R : W.Point => lognh (X R)) (Point.some hP) n
      - 2 * hseq (fun R : W.Point => lognh (X R)) (Point.some hQ) n|
      ≤ Real.log (Cpar B₂ B₄ B₆ B₈) / 4 ^ n := by
  have hsum : Point.some hP + Point.some hQ ≠ 0 := add_ne_zero hP hQ hne
  have hdif : Point.some hP - Point.some hQ ≠ 0 := sub_ne_zero' hP hQ hne
  -- affine data at level n
  obtain ⟨xp, yp, hp, hPn⟩ := exists_affine
    (smul_ne_zero_of_two_torsion_free h2tor (some_ne_zero hP) n)
  obtain ⟨xq, yq, hq, hQn⟩ := exists_affine
    (smul_ne_zero_of_two_torsion_free h2tor (some_ne_zero hQ) n)
  have hnen : xp ≠ xq := x_ne_at_all_levels h2tor hsum hdif n hPn hQn
  -- the unscaled defect at level n, from r199
  have hdefect := lognhX_defect_le h₂ h₄ h₆ h₈ hΔ hp hq hnen
    (h2tor _ (some_ne_zero hp)) (h2tor _ (some_ne_zero hq))
  simp only [lognhX_eq_lognh] at hdefect
  -- identify the four points
  have e1 : ((2 : ℤ) ^ n) • (Point.some hP + Point.some hQ)
      = Point.some hp + Point.some hq := by
    rw [smul_add, hPn, hQn]
  have e2 : ((2 : ℤ) ^ n) • (Point.some hP - Point.some hQ)
      = Point.some hp - Point.some hq := by
    rw [smul_sub, hPn, hQn]
  -- rewrite the scaled defect
  have hexp : (0 : ℝ) < 4 ^ n := by positivity
  have key : hseq (fun R : W.Point => lognh (X R))
        (Point.some hP + Point.some hQ) n
      + hseq (fun R : W.Point => lognh (X R))
          (Point.some hP - Point.some hQ) n
      - 2 * hseq (fun R : W.Point => lognh (X R)) (Point.some hP) n
      - 2 * hseq (fun R : W.Point => lognh (X R)) (Point.some hQ) n
      = (lognh (X (Point.some hp + Point.some hq))
          + lognh (X (Point.some hp - Point.some hq))
          - 2 * lognh (X (Point.some hp))
          - 2 * lognh (X (Point.some hq))) / 4 ^ n := by
    simp only [hseq, e1, e2, hPn, hQn]
    field_simp
  rw [key, abs_div, abs_of_pos hexp]
  gcongr

/-! ## §5 — THE CAPSTONE: the exact parallelogram law, universally -/

/-- **★★★ r200 — THE UNIVERSAL PARALLELOGRAM LAW FOR THE CANONICAL HEIGHT ★★★**

On ANY Weierstrass curve over ℚ with integer b-invariants, nonzero
discriminant, and no rational 2-torsion, for affine `P, Q` with distinct
x-coordinates:

    `ĥ(P+Q) + ĥ(P−Q) = 2·ĥ(P) + 2·ĥ(Q)`.

The quasi-parallelogram defect is uniformly `≤ log Cpar` (r199); at dyadic
level `n` the scaled defect is `≤ log Cpar / 4ⁿ`, which tends to `0`, while
the scaled sequences tend to the canonical heights (r171).  Uniqueness of
limits closes it. -/
theorem canheight_parallelogram_universal
    (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    canheightW W (Point.some hP + Point.some hQ)
        + canheightW W (Point.some hP - Point.some hQ)
      = 2 * canheightW W (Point.some hP)
        + 2 * canheightW W (Point.some hQ) := by
  have hw := heightWindow_universal h₂ h₄ h₆ h₈ hΔ h2tor
  unfold canheightW
  set F : ℕ → ℝ := fun n =>
    hseq (fun R : W.Point => lognh (X R))
        (Point.some hP + Point.some hQ) n
      + hseq (fun R : W.Point => lognh (X R))
          (Point.some hP - Point.some hQ) n
      - 2 * hseq (fun R : W.Point => lognh (X R)) (Point.some hP) n
      - 2 * hseq (fun R : W.Point => lognh (X R)) (Point.some hQ) n with hF
  -- F tends to the canonical-height combination
  have hL : Tendsto F atTop
      (𝓝 (canheight (fun R : W.Point => lognh (X R))
            (Point.some hP + Point.some hQ)
          + canheight (fun R : W.Point => lognh (X R))
              (Point.some hP - Point.some hQ)
          - 2 * canheight (fun R : W.Point => lognh (X R)) (Point.some hP)
          - 2 * canheight (fun R : W.Point => lognh (X R))
              (Point.some hQ))) := by
    simp only [hF]
    exact (((tendsto_hseq hw _).add (tendsto_hseq hw _)).sub
      ((tendsto_hseq hw _).const_mul 2)).sub
      ((tendsto_hseq hw _).const_mul 2)
  -- F tends to 0 by the geometric bound
  have hZ : Tendsto F atTop (𝓝 0) := by
    have hbound : ∀ n, |F n| ≤ Real.log (Cpar B₂ B₄ B₆ B₈) / 4 ^ n :=
      fun n => scaled_defect_le h₂ h₄ h₆ h₈ hΔ h2tor hP hQ hne n
    have htend : Tendsto
        (fun n : ℕ => Real.log (Cpar B₂ B₄ B₆ B₈) / 4 ^ n) atTop (𝓝 0) := by
      have h4 : Tendsto (fun n : ℕ => ((1 : ℝ) / 4) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have := h4.const_mul (Real.log (Cpar B₂ B₄ B₆ B₈))
      simpa [div_eq_mul_inv, one_div, inv_pow, mul_comm] using this
    exact squeeze_zero_norm hbound htend
  -- uniqueness of limits
  have := tendsto_nhds_unique hL hZ
  linarith [this]

/-! ## §6 — the induced pairing -/

/-- The pairing induced by the parallelogram law. -/
noncomputable def pairingW (W : WeierstrassCurve.Affine ℚ)
    (P Q : W.Point) : ℝ :=
  (canheightW W (P + Q) - canheightW W P - canheightW W Q) / 2

/-- The parallelogram law in "difference" form:
`ĥ(P−Q) = ĥP + ĥQ − 2⟨P,Q⟩`. -/
theorem canheight_sub_universal
    (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    canheightW W (Point.some hP - Point.some hQ)
      = canheightW W (Point.some hP) + canheightW W (Point.some hQ)
        - 2 * pairingW W (Point.some hP) (Point.some hQ) := by
  have h := canheight_parallelogram_universal h₂ h₄ h₆ h₈ hΔ h2tor hP hQ hne
  simp only [pairingW]
  linarith [h]

/-- `⟨P,P⟩ = ĥ(P)` — the pairing is normalized so its diagonal is the
height.  (Uses only `ĥ(2P) = 4ĥ(P)` from r171, no parallelogram needed.) -/
theorem pairing_self_universal
    (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (h2tor : ∀ R : W.Point, R ≠ 0 → (2 : ℕ) • R ≠ 0)
    (P : W.Point) :
    pairingW W P P = canheightW W P := by
  have hw := heightWindow_universal h₂ h₄ h₆ h₈ hΔ h2tor
  have hd : canheightW W (P + P) = 4 * canheightW W P := by
    unfold canheightW
    exact canheight_dbl hw P
  simp only [pairingW, hd]
  ring

end PrincipiaTractalis.CanheightParallelogramUniversal

#print axioms PrincipiaTractalis.CanheightParallelogramUniversal.smul_ne_zero_of_two_torsion_free
#print axioms PrincipiaTractalis.CanheightParallelogramUniversal.x_ne_at_all_levels
#print axioms PrincipiaTractalis.CanheightParallelogramUniversal.heightWindow_universal
#print axioms PrincipiaTractalis.CanheightParallelogramUniversal.scaled_defect_le
#print axioms PrincipiaTractalis.CanheightParallelogramUniversal.canheight_parallelogram_universal
#print axioms PrincipiaTractalis.CanheightParallelogramUniversal.canheight_sub_universal
#print axioms PrincipiaTractalis.CanheightParallelogramUniversal.pairing_self_universal
