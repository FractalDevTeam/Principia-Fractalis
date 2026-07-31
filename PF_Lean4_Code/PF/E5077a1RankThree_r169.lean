/-
# PF.E5077a1RankThree_r169

★★★ 2026-07-31 — 3 ≤ rank E5077a1(ℚ) ★★★

The certified numerics that close the rank-3 arc.  r168 proves
`regDet3 ≠ 0 → 3 ≤ rank`; this file exhibits three points with
`regDet3 > 0`.

Generators `P = (−3,0)`, `Q = (−2,3)`, `R = (0,2)`.  They span an **index-2
sublattice**: the determinant is `1.66856 = 4 × 0.41714`, four times the
classical regulator, which quadruples the margin for interval arithmetic and is
why level 3 suffices.  A rank *lower* bound does not care whether the points
generate.

Ground truth, verified two independent ways for all six points (group-law triple
double vs. third iterate of `f/g`), in `codex/R169_CERTIFICATE_5077a1.md`.

The window constant is `Real.log 105754 < 11.7836`, from `2^16 ≤ 105754 < 2^17`
and mathlib's nine-decimal `log 2` bounds — the same dyadic route as r153's
`log_1728_lt`.  (The true value is 11.5688709; 11.7836 is what the bracket gives
cheaply, and only 11.7836 is used.)

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import PF.Regulator3Independence5077a1_r168
import PF.RegulatorPositive389a1_r153

namespace PrincipiaTractalis.E5077a1RankThree

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E5077a1RankOne
open PrincipiaTractalis.CanonicalHeight5077a1
open PrincipiaTractalis.CanheightParallelogram5077a1 (pairing)
open PrincipiaTractalis.Regulator3Independence5077a1
open PrincipiaTractalis.RegulatorPositive389a1 (log_bracket_rat)
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the shifted window for 5077a1 -/

theorem canheight_window_shift (R : E5077a1.toAffine.Point) (n : ℕ) :
    |canheight R - hseq R n| ≤ Real.log 105754 / 3 / 4 ^ n := by
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hw := canheight_window (((2 : ℤ) ^ n) • R)
  rw [canheight_two_pow R n] at hw
  have hkey : 4 ^ n * |canheight R - hseq R n| ≤ Real.log 105754 / 3 := by
    have e : (4 : ℝ) ^ n * (canheight R - hseq R n)
        = 4 ^ n * canheight R - lognh (((2 : ℤ) ^ n) • R) := by
      simp only [hseq]; field_simp
    calc 4 ^ n * |canheight R - hseq R n|
        = |(4 : ℝ) ^ n * (canheight R - hseq R n)| := by
          rw [abs_mul, abs_of_pos h4]
      _ = |4 ^ n * canheight R - lognh (((2 : ℤ) ^ n) • R)| := by rw [e]
      _ ≤ Real.log 105754 / 3 := hw
  rw [le_div_iff₀ h4]
  calc |canheight R - hseq R n| * 4 ^ n
      = 4 ^ n * |canheight R - hseq R n| := by ring
    _ ≤ Real.log 105754 / 3 := hkey

/-- `log 105754 < 11.7836`, via `2^16 ≤ 105754 < 2^17`. -/
theorem log_105754_lt : Real.log 105754 < 11.7836 := by
  have hlo : (2 : ℕ) ^ 16 ≤ 105754 := by norm_num
  have hhi : (105754 : ℕ) < 2 ^ (16 + 1) := by norm_num
  obtain ⟨_, h2⟩ := log_bracket_rat hlo hhi
  have hcast : ((105754 : ℕ) : ℝ) = (105754 : ℝ) := by norm_num
  rw [hcast] at h2
  norm_num at h2
  linarith [h2]

/-! ## §2 — three doublings in `X`-form -/

theorem two_zsmul_eq (R : E5077a1.toAffine.Point) : (2 : ℤ) • R = R + R := by
  rw [show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]

theorem dbl_step {x y : ℚ} (h : E5077a1.toAffine.Nonsingular x y) :
    ∃ x' y', ∃ h' : E5077a1.toAffine.Nonsingular x' y',
      Point.some h + Point.some h = Point.some h' ∧ x' = f x / g x :=
  dbl_x h

theorem X_eight_smul {x₀ y₀ : ℚ} (h₀ : E5077a1.toAffine.Nonsingular x₀ y₀) :
    X ((((2 : ℤ)) ^ 3) • Point.some h₀)
      = f (f (f x₀ / g x₀) / g (f x₀ / g x₀))
          / g (f (f x₀ / g x₀) / g (f x₀ / g x₀)) := by
  obtain ⟨x₁, y₁, h₁, e₁, hx₁⟩ := dbl_step h₀
  obtain ⟨x₂, y₂, h₂, e₂, hx₂⟩ := dbl_step h₁
  obtain ⟨x₃, y₃, h₃, e₃, hx₃⟩ := dbl_step h₂
  have h8 : (((2 : ℤ)) ^ 3) • Point.some h₀
      = (2 : ℤ) • ((2 : ℤ) • ((2 : ℤ) • Point.some h₀)) := by
    rw [smul_smul, smul_smul]; norm_num
  have s₁ : (2 : ℤ) • Point.some h₀ = Point.some h₁ := by
    rw [two_zsmul_eq]; exact e₁
  have s₂ : (2 : ℤ) • Point.some h₁ = Point.some h₂ := by
    rw [two_zsmul_eq]; exact e₂
  have s₃ : (2 : ℤ) • Point.some h₂ = Point.some h₃ := by
    rw [two_zsmul_eq]; exact e₃
  rw [h8, s₁, s₂, s₃]
  show x₃ = _
  rw [hx₃, hx₂, hx₁]

/-! ## §3 — heights of reduced fractions, and the bracket -/

theorem naiveHeight_of_reduced (a b : ℤ) (hb : b ≠ 0) (hg : Int.gcd a b = 1) :
    naiveHeight ((a : ℚ) / (b : ℚ)) = max a.natAbs b.natAbs := by
  rw [DuplicationHeightBound37a1.naiveHeight_div_int a b hb, hg]
  norm_num

theorem X_eight_of_x {R : E5077a1.toAffine.Point} {x y : ℚ}
    (h : E5077a1.toAffine.Nonsingular x y) (hR : R = Point.some h) :
    X ((((2 : ℤ)) ^ 3) • R)
      = f (f (f x / g x) / g (f x / g x)) / g (f (f x / g x) / g (f x / g x)) := by
  rw [hR]; exact X_eight_smul h

theorem height_from_x {R : E5077a1.toAffine.Point} {x y : ℚ}
    (h : E5077a1.toAffine.Nonsingular x y) (hR : R = Point.some h)
    {a b : ℤ} (hb : b ≠ 0) (hg : Int.gcd a b = 1)
    (hchain : f (f (f x / g x) / g (f x / g x))
        / g (f (f x / g x) / g (f x / g x)) = ((a : ℚ) / (b : ℚ))) :
    naiveHeight (X ((((2 : ℤ)) ^ 3) • R)) = max a.natAbs b.natAbs := by
  rw [X_eight_of_x h hR, hchain, naiveHeight_of_reduced a b hb hg]

/-- **The level-3 bracket for 5077a1**, window `11.7836/192`. -/
theorem canheight_bracket {R : E5077a1.toAffine.Point} {H j : ℕ}
    (hH : naiveHeight (X ((((2 : ℤ)) ^ 3) • R)) = H)
    (hlo : 2 ^ j ≤ H) (hhi : H < 2 ^ (j + 1)) :
    (j : ℝ) * 0.6931471803 / 64 - 11.7836 / 192 ≤ canheight R ∧
      canheight R ≤ ((j : ℝ) + 1) * 0.6931471808 / 64 + 11.7836 / 192 := by
  have hh3 : hseq R 3 = Real.log H / 64 := by
    simp only [hseq, lognh, hH]; norm_num
  have hwin := canheight_window_shift R 3
  have hwin' : |canheight R - hseq R 3| ≤ 11.7836 / 192 := by
    have hL := log_105754_lt
    have : Real.log 105754 / 3 / 4 ^ 3 < 11.7836 / 192 := by
      norm_num; linarith [hL]
    linarith [hwin, this]
  rw [hh3, abs_le] at hwin'
  obtain ⟨hw1, hw2⟩ := hwin'
  obtain ⟨hb1, hb2⟩ := log_bracket_rat hlo hhi
  refine ⟨?_, ?_⟩
  · have : (j : ℝ) * 0.6931471803 / 64 ≤ Real.log H / 64 := by linarith [hb1]
    linarith [hw1, this]
  · have : Real.log H / 64 ≤ ((j : ℝ) + 1) * 0.6931471808 / 64 := by linarith [hb2]
    linarith [hw2, this]


/-! ## §4 — the three points -/

theorem hP : E5077a1.toAffine.Nonsingular (-3) 0 := by
  rw [Affine.nonsingular_iff]
  constructor
  · rw [Affine.equation_iff]
    simp only [E5077a1_a₁, E5077a1_a₂, E5077a1_a₃, E5077a1_a₄, E5077a1_a₆]
    norm_num
  · right
    simp only [E5077a1_a₁, E5077a1_a₃]
    norm_num

theorem hQ : E5077a1.toAffine.Nonsingular (-2) 3 := by
  rw [Affine.nonsingular_iff]
  constructor
  · rw [Affine.equation_iff]
    simp only [E5077a1_a₁, E5077a1_a₂, E5077a1_a₃, E5077a1_a₄, E5077a1_a₆]
    norm_num
  · right
    simp only [E5077a1_a₁, E5077a1_a₃]
    norm_num

theorem hR : E5077a1.toAffine.Nonsingular 0 2 := by
  rw [Affine.nonsingular_iff]
  constructor
  · rw [Affine.equation_iff]
    simp only [E5077a1_a₁, E5077a1_a₂, E5077a1_a₃, E5077a1_a₄, E5077a1_a₆]
    norm_num
  · right
    simp only [E5077a1_a₁, E5077a1_a₃]
    norm_num

noncomputable def Pt : E5077a1.toAffine.Point := Point.some hP
noncomputable def Qt : E5077a1.toAffine.Point := Point.some hQ
noncomputable def Rt : E5077a1.toAffine.Point := Point.some hR

theorem xPQ : (-3 : ℚ) ≠ -2 := by norm_num
theorem xPR : (-3 : ℚ) ≠ 0 := by norm_num
theorem xQR : (-2 : ℚ) ≠ 0 := by norm_num

theorem X_sum_PQ : X (Pt + Qt) = 14 := by
  rw [Pt, Qt, QuasiParallelogramLower5077a1.X_add_eq hP hQ xPQ]
  simp only [SecantBridge5077a1.xAdd, Affine.slope_of_X_ne xPQ, Affine.addX,
    E5077a1_a₁, E5077a1_a₂]
  norm_num

theorem X_sum_PR : X (Pt + Rt) = 31/9 := by
  rw [Pt, Rt, QuasiParallelogramLower5077a1.X_add_eq hP hR xPR]
  simp only [SecantBridge5077a1.xAdd, Affine.slope_of_X_ne xPR, Affine.addX,
    E5077a1_a₁, E5077a1_a₂]
  norm_num

theorem X_sum_QR : X (Qt + Rt) = 9/4 := by
  rw [Qt, Rt, QuasiParallelogramLower5077a1.X_add_eq hQ hR xQR]
  simp only [SecantBridge5077a1.xAdd, Affine.slope_of_X_ne xQR, Affine.addX,
    E5077a1_a₁, E5077a1_a₂]
  norm_num

/-! ## §5 — the six level-3 chain values -/

theorem chainP :
    f (f (f (-3 : ℚ) / g (-3 : ℚ)) / g (f (-3 : ℚ) / g (-3 : ℚ)))
      / g (f (f (-3 : ℚ) / g (-3 : ℚ)) / g (f (-3 : ℚ) / g (-3 : ℚ)))
      = ((545923606080089475864759862141389878286294 : ℤ) : ℚ) / ((21468873121640064324499415754491247939649 : ℤ) : ℚ) := by
  simp only [f, g]; norm_num

theorem chainQ :
    f (f (f (-2 : ℚ) / g (-2 : ℚ)) / g (f (-2 : ℚ) / g (-2 : ℚ)))
      / g (f (f (-2 : ℚ) / g (-2 : ℚ)) / g (f (-2 : ℚ) / g (-2 : ℚ)))
      = ((108502953081381829947278275036681007149 : ℤ) : ℚ) / ((1801530935128745778123333338902100881 : ℤ) : ℚ) := by
  simp only [f, g]; norm_num

theorem chainR :
    f (f (f (0 : ℚ) / g (0 : ℚ)) / g (f (0 : ℚ) / g (0 : ℚ)))
      / g (f (f (0 : ℚ) / g (0 : ℚ)) / g (f (0 : ℚ) / g (0 : ℚ)))
      = ((3401164188973057249897036701 : ℤ) : ℚ) / ((165304990948342375708690225 : ℤ) : ℚ) := by
  simp only [f, g]; norm_num

theorem chainPQ :
    f (f (f (14 : ℚ) / g (14 : ℚ)) / g (f (14 : ℚ) / g (14 : ℚ)))
      / g (f (f (14 : ℚ) / g (14 : ℚ)) / g (f (14 : ℚ) / g (14 : ℚ)))
      = ((194758636939452416666372300718210467315582885239392943951986563659334493869 : ℤ) : ℚ) / ((944447999359398955605196999784658673216045600557377591215542791282471569 : ℤ) : ℚ) := by
  simp only [f, g]; norm_num

theorem chainPR :
    f (f (f (31/9 : ℚ) / g (31/9 : ℚ)) / g (f (31/9 : ℚ) / g (31/9 : ℚ)))
      / g (f (f (31/9 : ℚ) / g (31/9 : ℚ)) / g (f (31/9 : ℚ) / g (31/9 : ℚ)))
      = ((60050638892084455544628809671123254557534826259951950576409942933487910013610430267092674109018854 : ℤ) : ℚ) / ((10162890528846961895049541355898873704011327171589824736456072765373507469851011923787871381630849 : ℤ) : ℚ) := by
  simp only [f, g]; norm_num

theorem chainQR :
    f (f (f (9/4 : ℚ) / g (9/4 : ℚ)) / g (f (9/4 : ℚ) / g (9/4 : ℚ)))
      / g (f (f (9/4 : ℚ) / g (9/4 : ℚ)) / g (f (9/4 : ℚ) / g (9/4 : ℚ)))
      = ((2314981916563759274283831471203590872289727811116736114424752129 : ℤ) : ℚ) / ((19564815469337911734424959362725946628344894374222759685683456 : ℤ) : ℚ) := by
  simp only [f, g]; norm_num

/-! ## §6 — the six certified brackets -/

theorem bracket_P :
    (138 : ℝ) * 0.6931471803 / 64 - 11.7836 / 192 ≤ canheight Pt ∧
      canheight Pt ≤ ((138 : ℝ) + 1) * 0.6931471808 / 64 + 11.7836 / 192 := by
  have hH := height_from_x (R := Pt) _ rfl
    (a := 545923606080089475864759862141389878286294) (b := 21468873121640064324499415754491247939649) (by norm_num) (by norm_num) chainP
  exact canheight_bracket (j := 138) hH (by norm_num) (by norm_num)

theorem bracket_Q :
    (126 : ℝ) * 0.6931471803 / 64 - 11.7836 / 192 ≤ canheight Qt ∧
      canheight Qt ≤ ((126 : ℝ) + 1) * 0.6931471808 / 64 + 11.7836 / 192 := by
  have hH := height_from_x (R := Qt) _ rfl
    (a := 108502953081381829947278275036681007149) (b := 1801530935128745778123333338902100881) (by norm_num) (by norm_num) chainQ
  exact canheight_bracket (j := 126) hH (by norm_num) (by norm_num)

theorem bracket_R :
    (91 : ℝ) * 0.6931471803 / 64 - 11.7836 / 192 ≤ canheight Rt ∧
      canheight Rt ≤ ((91 : ℝ) + 1) * 0.6931471808 / 64 + 11.7836 / 192 := by
  have hH := height_from_x (R := Rt) _ rfl
    (a := 3401164188973057249897036701) (b := 165304990948342375708690225) (by norm_num) (by norm_num) chainR
  exact canheight_bracket (j := 91) hH (by norm_num) (by norm_num)

theorem bracket_PQ :
    (246 : ℝ) * 0.6931471803 / 64 - 11.7836 / 192 ≤ canheight (Pt + Qt) ∧
      canheight (Pt + Qt) ≤ ((246 : ℝ) + 1) * 0.6931471808 / 64 + 11.7836 / 192 := by
  have hne : (Pt + Qt) ≠ 0 := PointQuasiParallelogram5077a1.add_ne_zero hP hQ xPQ
  obtain ⟨xs, ys, hs, hEq⟩ := CanheightParallelogram5077a1.exists_affine hne
  have hxs : xs = 14 := by rw [← X_sum_PQ, hEq]; rfl
  subst hxs
  have hH := height_from_x hs hEq
    (a := 194758636939452416666372300718210467315582885239392943951986563659334493869) (b := 944447999359398955605196999784658673216045600557377591215542791282471569) (by norm_num) (by norm_num) chainPQ
  exact canheight_bracket (j := 246) hH (by norm_num) (by norm_num)

theorem bracket_PR :
    (324 : ℝ) * 0.6931471803 / 64 - 11.7836 / 192 ≤ canheight (Pt + Rt) ∧
      canheight (Pt + Rt) ≤ ((324 : ℝ) + 1) * 0.6931471808 / 64 + 11.7836 / 192 := by
  have hne : (Pt + Rt) ≠ 0 := PointQuasiParallelogram5077a1.add_ne_zero hP hR xPR
  obtain ⟨xs, ys, hs, hEq⟩ := CanheightParallelogram5077a1.exists_affine hne
  have hxs : xs = 31/9 := by rw [← X_sum_PR, hEq]; rfl
  subst hxs
  have hH := height_from_x hs hEq
    (a := 60050638892084455544628809671123254557534826259951950576409942933487910013610430267092674109018854) (b := 10162890528846961895049541355898873704011327171589824736456072765373507469851011923787871381630849) (by norm_num) (by norm_num) chainPR
  exact canheight_bracket (j := 324) hH (by norm_num) (by norm_num)

theorem bracket_QR :
    (210 : ℝ) * 0.6931471803 / 64 - 11.7836 / 192 ≤ canheight (Qt + Rt) ∧
      canheight (Qt + Rt) ≤ ((210 : ℝ) + 1) * 0.6931471808 / 64 + 11.7836 / 192 := by
  have hne : (Qt + Rt) ≠ 0 := PointQuasiParallelogram5077a1.add_ne_zero hQ hR xQR
  obtain ⟨xs, ys, hs, hEq⟩ := CanheightParallelogram5077a1.exists_affine hne
  have hxs : xs = 9/4 := by rw [← X_sum_QR, hEq]; rfl
  subst hxs
  have hH := height_from_x hs hEq
    (a := 2314981916563759274283831471203590872289727811116736114424752129) (b := 19564815469337911734424959362725946628344894374222759685683456) (by norm_num) (by norm_num) chainQR
  exact canheight_bracket (j := 210) hH (by norm_num) (by norm_num)


/-! ## §7 — THE FLAG -/

set_option maxHeartbeats 4000000 in
/-- `regDet3 > 0` for the triple, by interval arithmetic on the six brackets. -/
theorem regDet3_pos : 0 < regDet3 Pt Qt Rt := by
  obtain ⟨a1, a2⟩ := bracket_P
  obtain ⟨b1, b2⟩ := bracket_Q
  obtain ⟨c1, c2⟩ := bracket_R
  obtain ⟨s1, s2⟩ := bracket_PQ
  obtain ⟨t1, t2⟩ := bracket_PR
  obtain ⟨u1, u2⟩ := bracket_QR
  norm_num at a1 a2 b1 b2 c1 c2 s1 s2 t1 t2 u1 u2
  -- the six height bounds, as decimals
  have hA1 : (1.4332 : ℝ) ≤ canheight Pt := by linarith
  have hA2 : canheight Pt ≤ 1.5669 := by linarith
  have hB1 : (1.3032 : ℝ) ≤ canheight Qt := by linarith
  have hB2 : canheight Qt ≤ 1.4369 := by linarith
  have hC1 : (0.9241 : ℝ) ≤ canheight Rt := by linarith
  have hC2 : canheight Rt ≤ 1.0578 := by linarith
  -- the three pairings
  have hP1 : (-0.2004 : ℝ) ≤ pairing Pt Qt := by simp only [pairing]; linarith
  have hP2 : pairing Pt Qt ≤ 0.0001 := by simp only [pairing]; linarith
  have hQ1 : (0.4115 : ℝ) ≤ pairing Pt Rt := by simp only [pairing]; linarith
  have hQ2 : pairing Pt Rt ≤ 0.6120 := by simp only [pairing]; linarith
  have hR1 : (-0.1408 : ℝ) ≤ pairing Qt Rt := by simp only [pairing]; linarith
  have hR2 : pairing Qt Rt ≤ 0.0596 := by simp only [pairing]; linarith
  -- the five terms of the determinant, bounded one at a time
  -- triple products, one factor at a time (nlinarith does not do them in one go)
  have hab : (1.8677 : ℝ) ≤ canheight Pt * canheight Qt := by
    nlinarith [hA1, hB1]
  have habc : (1.7258 : ℝ)
      ≤ canheight Pt * canheight Qt * canheight Rt := by
    nlinarith [hab, hC1]
  have hpq1 : (-0.1227 : ℝ) ≤ pairing Pt Qt * pairing Pt Rt := by
    nlinarith [hP1, hP2, hQ1, hQ2]
  have hpq2 : pairing Pt Qt * pairing Pt Rt ≤ 0.0001 := by
    nlinarith [hP1, hP2, hQ1, hQ2]
  have h2pqr : (-0.0147 : ℝ)
      ≤ 2 * pairing Pt Qt * pairing Pt Rt * pairing Qt Rt := by
    nlinarith [hpq1, hpq2, hR1, hR2]
  have har : canheight Pt * pairing Qt Rt ^ 2 ≤ 0.0311 := by
    nlinarith [hA1, hA2, hR1, hR2, sq_nonneg (pairing Qt Rt)]
  have hbq : canheight Qt * pairing Pt Rt ^ 2 ≤ 0.5382 := by
    nlinarith [hB1, hB2, hQ1, hQ2, sq_nonneg (pairing Pt Rt)]
  have hcp : canheight Rt * pairing Pt Qt ^ 2 ≤ 0.0425 := by
    nlinarith [hC1, hC2, hP1, hP2, sq_nonneg (pairing Pt Qt)]
  -- 1.7258 - 0.0147 - 0.0311 - 0.5382 - 0.0425 = 1.0993 > 0
  simp only [regDet3]
  linarith [habc, h2pqr, har, hbq, hcp]

/-- **★★★ r169 — 3 ≤ rank E5077a1(ℚ) ★★★** -/
theorem E5077a1_rank_ge_three : 3 ≤ Module.rank ℤ E5077a1.toAffine.Point :=
  rank_ge_three_of_regDet3_ne_zero (ne_of_gt regDet3_pos)

end PrincipiaTractalis.E5077a1RankThree

#print axioms PrincipiaTractalis.E5077a1RankThree.canheight_bracket
#print axioms PrincipiaTractalis.E5077a1RankThree.bracket_PR
#print axioms PrincipiaTractalis.E5077a1RankThree.regDet3_pos
#print axioms PrincipiaTractalis.E5077a1RankThree.E5077a1_rank_ge_three
