/-
# PF.CanonicalHeight5077a1_r156

★★★ 2026-07-30 — THE CANONICAL HEIGHT ON 5077a1 ★★★

The canonical (Néron–Tate) height on `E5077a1(ℚ)`, for the Buhler–Gross–Zagier
rank-3 curve `y² + y = x³ − 7x + 6`, constructed exactly as r147 does it for
389a1: as the real limit `ĥ(R) := lim_n log h(x(2ⁿR)) / 4ⁿ`, from the
two-sided duplication window of r144 (lower) + r146 (upper):

  `H⁴ ≤ 105754·h(x(2P))`  and  `h(x(2P)) ≤ 114·H⁴`
  ⟹  `|log h(2R) − 4·log h(R)| ≤ log 105754`
  ⟹  `hseq R n := log h(2ⁿR)/4ⁿ` is Cauchy with explicit geometric modulus
  ⟹  `ĥ(R) := lim hseq R` exists (ℝ is complete).

Core API, matching r147 name-for-name in this namespace:
  * `canheight_nonneg  : 0 ≤ ĥ(R)`
  * `canheight_dbl     : ĥ(R + R) = 4·ĥ(R)`
  * `canheight_two_pow : ĥ(2ⁿR) = 4ⁿ·ĥ(R)`
  * `canheight_window  : |ĥ(R) − log h(R)| ≤ log 105754 / 3`
  * `finite_of_naiveHeight_le` — Northcott for ℚ
  * `canheight_eq_zero_iff_torsion`

## What differs from r147

Only the constants.  This curve's duplication constant is `κ = 105754`
rather than 1728, and the upper coefficient is 114 rather than 17.  The one
place that matters downstream is the torsion height bound: `ĥ(R) = 0` forces
`h(x(2ⁿR))³ ≤ κ`, so

  `h(x(2ⁿR)) ≤ 47`     (since 47³ = 103823 ≤ 105754 < 110592 = 48³)

against 12 for 389a1 — because there `κ = 1728 = 12³` exactly.  The r155
torsion-triviality argument would therefore need to enumerate the rationals
of height ≤ 47 rather than ≤ 12, a far larger search; this file does NOT
attempt it.

The 5077a1 side is otherwise structurally identical to 389a1: `a₃ = 1`, so
`negY x y = −y − 1` and the x-fiber factorization `(y − y₀)(y + y₀ + 1) = 0`
is unchanged, and `g_ne_zero` (r144) again rules out rational 2-torsion so
affine points stay affine under doubling.

HONEST SCOPE.  The limit, its doubling law, the window against the naive
height, and the torsion ⟺ ĥ = 0 characterization.  NO parallelogram law for
this curve (that needs the 5077a1 quasi-parallelogram certificates, the
analogue of r148a–g), hence no pairing, no regulator, and no rank-3
statement.  Nothing here asserts a value for any canonical height.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-30.
-/
import PF.DuplicationHeightUpper5077a1_r146
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PrincipiaTractalis.CanonicalHeight5077a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E5077a1RankOne
open PrincipiaTractalis.DuplicationHeightUpper5077a1
open WeierstrassCurve WeierstrassCurve.Affine
open Filter Topology

/-! ## §1 — the log-naive height on points -/

/-- The log-naive height of a point: `log H(x(R))`, with `lognh O = 0`
(`X O = 0`, `H(0) = 1`, `log 1 = 0`). -/
noncomputable def lognh (R : E5077a1.toAffine.Point) : ℝ :=
  Real.log (naiveHeight (X R))

lemma one_le_naiveHeight_real (q : ℚ) : (1 : ℝ) ≤ (naiveHeight q : ℝ) := by
  exact_mod_cast one_le_naiveHeight q

lemma naiveHeight_real_pos (q : ℚ) : (0 : ℝ) < (naiveHeight q : ℝ) :=
  lt_of_lt_of_le one_pos (one_le_naiveHeight_real q)

theorem lognh_nonneg (R : E5077a1.toAffine.Point) : 0 ≤ lognh R :=
  Real.log_nonneg (one_le_naiveHeight_real _)

lemma X_zero : X (0 : E5077a1.toAffine.Point) = 0 := rfl

@[simp] theorem lognh_zero : lognh (0 : E5077a1.toAffine.Point) = 0 := by
  unfold lognh
  rw [X_zero, naiveHeight_zero]
  norm_num

/-! ## §2 — the log-form duplication window on x-coordinates -/

/-- The r144 + r146 two-sided window `H⁴/105754 ≤ h(f x/g x) ≤ 114·H⁴`,
taken through `Real.log`. -/
private theorem log_window (x : ℚ) :
    |Real.log (naiveHeight (f x / g x)) - 4 * Real.log (naiveHeight x)|
      ≤ Real.log 105754 := by
  obtain ⟨hlow, hup⟩ := duplication_two_sided x
  have hb0 : (0 : ℝ) < (naiveHeight (f x / g x) : ℝ) := naiveHeight_real_pos _
  have ha0 : (0 : ℝ) < (naiveHeight x : ℝ) := naiveHeight_real_pos _
  have hlowR : ((naiveHeight x : ℝ)) ^ 4
      ≤ 105754 * (naiveHeight (f x / g x) : ℝ) := by exact_mod_cast hlow
  have hupR : ((naiveHeight (f x / g x) : ℝ))
      ≤ 114 * (naiveHeight x : ℝ) ^ 4 := by exact_mod_cast hup
  -- lower side: 4·log a ≤ log 105754 + log b
  have h1 : Real.log ((naiveHeight x : ℝ) ^ 4)
      ≤ Real.log (105754 * (naiveHeight (f x / g x) : ℝ)) :=
    Real.log_le_log (by positivity) hlowR
  rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hb0)] at h1
  -- upper side: log b ≤ log 114 + 4·log a ≤ log 105754 + 4·log a
  have h2 : Real.log ((naiveHeight (f x / g x) : ℝ))
      ≤ Real.log (114 * (naiveHeight x : ℝ) ^ 4) :=
    Real.log_le_log hb0 hupR
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
  have hcoef : Real.log (114 : ℝ) ≤ Real.log 105754 :=
    Real.log_le_log (by norm_num) (by norm_num)
  push_cast at h1 h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ## §3 — the doubling window on the point group -/

/-- **The doubling window**: `|log h(R + R) − 4·log h(R)| ≤ log 105754`,
for EVERY point of `E5077a1(ℚ)` including `O` (both sides vanish there;
affine points stay affine under doubling — no rational 2-torsion). -/
theorem lognh_dbl_window (R : E5077a1.toAffine.Point) :
    |lognh (R + R) - 4 * lognh R| ≤ Real.log 105754 := by
  cases R with
  | zero =>
      rw [← Point.zero_def, add_zero, lognh_zero, mul_zero, sub_zero, abs_zero]
      exact Real.log_nonneg (by norm_num)
  | @some x y h =>
      obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
      have hXd : X (Point.some h + Point.some h) = f x / g x := by
        rw [hadd]
        exact hx'
      have hXs : X (Point.some h) = x := rfl
      unfold lognh
      rw [hXd, hXs]
      exact log_window x

/-! ## §4 — the normalized sequence and its Cauchy property -/

/-- The canonical-height approximant: `hseq R n = log h(2ⁿR) / 4ⁿ`. -/
noncomputable def hseq (R : E5077a1.toAffine.Point) (n : ℕ) : ℝ :=
  lognh (((2 : ℤ) ^ n) • R) / 4 ^ n

lemma two_pow_succ_zsmul (R : E5077a1.toAffine.Point) (n : ℕ) :
    ((2 : ℤ) ^ (n + 1)) • R = ((2 : ℤ) ^ n) • R + ((2 : ℤ) ^ n) • R := by
  have h2 : ((2 : ℤ) ^ (n + 1)) = 2 ^ n + 2 ^ n := by ring
  rw [h2, add_zsmul]

lemma hseq_zero_eq (R : E5077a1.toAffine.Point) : hseq R 0 = lognh R := by
  simp [hseq]

theorem hseq_nonneg (R : E5077a1.toAffine.Point) (n : ℕ) : 0 ≤ hseq R n :=
  div_nonneg (lognh_nonneg _) (by positivity)

/-- The one-step estimate: `|hseq R (n+1) − hseq R n| ≤ log 105754 / 4^(n+1)`. -/
theorem hseq_step (R : E5077a1.toAffine.Point) (n : ℕ) :
    |hseq R (n + 1) - hseq R n| ≤ Real.log 105754 / 4 ^ (n + 1) := by
  have key := lognh_dbl_window (((2 : ℤ) ^ n) • R)
  rw [← two_pow_succ_zsmul R n] at key
  have h4pos : (0 : ℝ) < 4 ^ (n + 1) := by positivity
  have habs : ∀ L1 L0 : ℝ,
      L1 / 4 ^ (n + 1) - L0 / 4 ^ n = (L1 - 4 * L0) / 4 ^ (n + 1) := by
    intro L1 L0
    have h4 : ((4 : ℝ) ^ n) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
  calc |hseq R (n + 1) - hseq R n|
      = |(lognh (((2 : ℤ) ^ (n + 1)) • R)
          - 4 * lognh (((2 : ℤ) ^ n) • R)) / 4 ^ (n + 1)| := by
        unfold hseq
        rw [habs]
    _ = |lognh (((2 : ℤ) ^ (n + 1)) • R)
          - 4 * lognh (((2 : ℤ) ^ n) • R)| / 4 ^ (n + 1) := by
        rw [abs_div, abs_of_pos h4pos]
    _ ≤ Real.log 105754 / 4 ^ (n + 1) := by gcongr

/-- The geometric form of the step estimate, in `dist`. -/
theorem hseq_dist_step (R : E5077a1.toAffine.Point) (n : ℕ) :
    dist (hseq R n) (hseq R (n + 1)) ≤ Real.log 105754 / 4 * (1 / 4) ^ n := by
  rw [Real.dist_eq, abs_sub_comm]
  calc |hseq R (n + 1) - hseq R n|
      ≤ Real.log 105754 / 4 ^ (n + 1) := hseq_step R n
    _ = Real.log 105754 / 4 * (1 / 4) ^ n := by
        rw [div_pow, one_pow, div_mul_div_comm, mul_one, ← pow_succ']

/-- **The approximants form a Cauchy sequence** (geometric modulus,
`C = log 105754 / 4`, `r = 1/4`). -/
theorem hseq_cauchySeq (R : E5077a1.toAffine.Point) : CauchySeq (hseq R) :=
  cauchySeq_of_le_geometric (1 / 4) (Real.log 105754 / 4) (by norm_num)
    (hseq_dist_step R)

/-! ## §5 — the canonical height -/

/-- **The canonical height** on `E5077a1(ℚ)`:
`ĥ(R) = lim_{n → ∞} log h(x(2ⁿR)) / 4ⁿ`. -/
noncomputable def canheight (R : E5077a1.toAffine.Point) : ℝ :=
  limUnder atTop (hseq R)

/-- The approximants converge to the canonical height (ℝ is complete). -/
theorem tendsto_hseq (R : E5077a1.toAffine.Point) :
    Tendsto (hseq R) atTop (𝓝 (canheight R)) :=
  (hseq_cauchySeq R).tendsto_limUnder

/-- **(a) Nonnegativity**: `0 ≤ ĥ(R)`. -/
theorem canheight_nonneg (R : E5077a1.toAffine.Point) : 0 ≤ canheight R :=
  ge_of_tendsto' (tendsto_hseq R) (hseq_nonneg R)

/-- Index shift: `hseq (R + R) n = 4 · hseq R (n + 1)`. -/
lemma hseq_add_self (R : E5077a1.toAffine.Point) (n : ℕ) :
    hseq (R + R) n = 4 * hseq R (n + 1) := by
  have hsm : ((2 : ℤ) ^ n) • (R + R) = ((2 : ℤ) ^ (n + 1)) • R := by
    rw [← two_zsmul, ← mul_zsmul, ← pow_succ]
  unfold hseq
  rw [hsm]
  generalize lognh (((2 : ℤ) ^ (n + 1)) • R) = L
  have h4 : ((4 : ℝ) ^ n) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

/-- **(b) The doubling law**: `ĥ(R + R) = 4·ĥ(R)`. -/
theorem canheight_dbl (R : E5077a1.toAffine.Point) :
    canheight (R + R) = 4 * canheight R := by
  have h1 : Tendsto (fun n : ℕ => hseq R (n + 1)) atTop (𝓝 (canheight R)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_hseq R)
  have h2 : Tendsto (hseq (R + R)) atTop (𝓝 (4 * canheight R)) := by
    have hmul := h1.const_mul (4 : ℝ)
    simpa only [← hseq_add_self] using hmul
  exact tendsto_nhds_unique (tendsto_hseq (R + R)) h2

/-- **(c) The window**: `|ĥ(R) − log h(R)| ≤ log 105754 / 3`
(the geometric tail `Σ (log 105754/4)·(1/4)ⁿ = log 105754/3`). -/
theorem canheight_window (R : E5077a1.toAffine.Point) :
    |canheight R - lognh R| ≤ Real.log 105754 / 3 := by
  have hd := dist_le_of_le_geometric_of_tendsto₀ (1 / 4) (Real.log 105754 / 4)
    (by norm_num) (hseq_dist_step R) (tendsto_hseq R)
  rw [Real.dist_eq, hseq_zero_eq] at hd
  have hconst : Real.log 105754 / 4 / (1 - 1 / 4) = Real.log 105754 / 3 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, div_div]
    norm_num
  rw [hconst] at hd
  calc |canheight R - lognh R| = |lognh R - canheight R| := abs_sub_comm _ _
    _ ≤ Real.log 105754 / 3 := hd

/-- Iterated doubling law: `ĥ(2ⁿR) = 4ⁿ·ĥ(R)`. -/
theorem canheight_two_pow (R : E5077a1.toAffine.Point) (n : ℕ) :
    canheight (((2 : ℤ) ^ n) • R) = 4 ^ n * canheight R := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [two_pow_succ_zsmul, canheight_dbl, ih, pow_succ]
      ring

/-! ## §6 — Northcott for ℚ -/

/-- **Northcott for ℚ**: only finitely many rationals of bounded naive
height (inject into a finite box of `(num, den)` pairs). -/
theorem finite_of_naiveHeight_le (B : ℕ) :
    {q : ℚ | naiveHeight q ≤ B}.Finite := by
  apply Set.Finite.of_finite_image (f := fun q : ℚ => (q.num, q.den))
  · apply Set.Finite.subset
      (Set.Finite.prod (Set.finite_Icc (-(B : ℤ)) (B : ℤ)) (Set.finite_Icc 0 B))
    rintro p ⟨q, hq, rfl⟩
    have hnum : q.num.natAbs ≤ B := le_trans (num_natAbs_le_naiveHeight q) hq
    have hden : q.den ≤ B := le_trans (den_le_naiveHeight q) hq
    simp only [Set.mem_prod, Set.mem_Icc]
    omega
  · intro p _ q _ hpq
    have hn : p.num = q.num := congrArg Prod.fst hpq
    have hd : p.den = q.den := congrArg Prod.snd hpq
    rw [← Rat.num_div_den p, ← Rat.num_div_den q, hn, hd]

/-! ## §7 — fibers of the x-projection are finite -/

/-- For fixed `x`, at most two rationals `y` satisfy the 5077a1 equation:
subtracting two instances gives `(y − y₀)(y + y₀ + 1) = 0`. -/
theorem finite_equation_fiber (x : ℚ) :
    {y : ℚ | E5077a1.toAffine.Equation x y}.Finite := by
  rcases Set.eq_empty_or_nonempty {y : ℚ | E5077a1.toAffine.Equation x y}
    with he | hne
  · rw [he]; exact Set.finite_empty
  · obtain ⟨y₀, hy₀⟩ := hne
    apply Set.Finite.subset
      (Set.Finite.insert y₀ (Set.finite_singleton (-y₀ - 1)))
    intro y hy
    rw [Set.mem_setOf_eq, Affine.equation_iff] at hy
    rw [Set.mem_setOf_eq, Affine.equation_iff] at hy₀
    simp only [E5077a1_a₁, E5077a1_a₂, E5077a1_a₃, E5077a1_a₄, E5077a1_a₆]
      at hy hy₀
    have hfac : (y - y₀) * (y + y₀ + 1) = 0 := by
      linear_combination hy - hy₀
    rcases mul_eq_zero.mp hfac with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl (sub_eq_zero.mp h))
    · refine Set.mem_insert_iff.mpr (Or.inr ?_)
      rw [Set.mem_singleton_iff]
      linarith

/-! ## §8 — the coordinate embedding of the point group -/

/-- Coordinates of a point: `O ↦ none`, affine `(x, y) ↦ some (x, y)`.
(Avoids the `(0, 0) ∈ E5077a1(ℚ)` collision an `X`-only map would have.) -/
def toCoords : E5077a1.toAffine.Point → Option (ℚ × ℚ)
  | .zero => none
  | @Point.some _ _ _ x y _ => some (x, y)

theorem toCoords_injective : Function.Injective toCoords := by
  intro P Q hPQ
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | @some x' y' h' =>
          have hne : (none : Option (ℚ × ℚ)) = some (x', y') := hPQ
          exact Option.noConfusion hne
  | @some x y h =>
      cases Q with
      | zero =>
          have hne : (some (x, y) : Option (ℚ × ℚ)) = none := hPQ
          exact Option.noConfusion hne
      | @some x' y' h' =>
          have hxy : (some (x, y) : Option (ℚ × ℚ)) = some (x', y') := hPQ
          have hp : (x, y) = (x', y') := Option.some.inj hxy
          have hx : x = x' := congrArg Prod.fst hp
          have hy : y = y' := congrArg Prod.snd hp
          subst hx
          subst hy
          rfl

/-- Points of x-height ≤ 47 land in the fixed finite coordinate set. -/
lemma toCoords_mem_of_le {Q : E5077a1.toAffine.Point}
    (hle : naiveHeight (X Q) ≤ 47) :
    toCoords Q ∈ (insert none (Option.some ''
      {p : ℚ × ℚ | naiveHeight p.1 ≤ 47 ∧ E5077a1.toAffine.Equation p.1 p.2})
        : Set (Option (ℚ × ℚ))) := by
  cases Q with
  | zero => exact Set.mem_insert _ _
  | @some xq yq hq =>
      refine Set.mem_insert_iff.mpr (Or.inr ?_)
      exact ⟨(xq, yq), ⟨hle, hq.left⟩, rfl⟩

/-! ## §9 — ĥ = 0 forces a finite doubling orbit -/

/-- If `ĥ(R) = 0` then every `2ⁿR` has x-height at most 47:
`log h(2ⁿR) ≤ log 105754 / 3` ⟹ `h³ ≤ 105754` ⟹ `h ≤ 47`. -/
theorem naiveHeight_le_47_of_canheight_zero {R : E5077a1.toAffine.Point}
    (h0 : canheight R = 0) (n : ℕ) :
    naiveHeight (X (((2 : ℤ) ^ n) • R)) ≤ 47 := by
  have hw := canheight_window (((2 : ℤ) ^ n) • R)
  rw [canheight_two_pow, h0, mul_zero] at hw
  have hl : lognh (((2 : ℤ) ^ n) • R) ≤ Real.log 105754 / 3 := by
    have h := (abs_le.mp hw).1
    linarith
  unfold lognh at hl
  set q : ℚ := X (((2 : ℤ) ^ n) • R) with hq
  have h3 : Real.log ((naiveHeight q : ℝ) ^ 3) ≤ Real.log 105754 := by
    rw [Real.log_pow]
    push_cast
    linarith
  have hcube : ((naiveHeight q : ℝ)) ^ 3 ≤ 105754 :=
    (Real.log_le_log_iff (pow_pos (naiveHeight_real_pos q) 3)
      (by norm_num)).mp h3
  have hnat : naiveHeight q ^ 3 ≤ 105754 := by exact_mod_cast hcube
  by_contra hgt
  push_neg at hgt
  have h48 : 48 ≤ naiveHeight q := hgt
  have h110592 : 110592 ≤ naiveHeight q ^ 3 := by
    calc (110592 : ℕ) = 48 ^ 3 := by norm_num
      _ ≤ naiveHeight q ^ 3 := Nat.pow_le_pow_left h48 3
  exact absurd (le_trans h110592 hnat) (by norm_num)

/-- The doubling orbit of a point with `ĥ = 0` is finite. -/
theorem finite_orbit_of_canheight_zero {R : E5077a1.toAffine.Point}
    (h0 : canheight R = 0) :
    (Set.range fun n : ℕ => ((2 : ℤ) ^ n) • R).Finite := by
  have hTfin : {p : ℚ × ℚ | naiveHeight p.1 ≤ 47 ∧
      E5077a1.toAffine.Equation p.1 p.2}.Finite := by
    apply Set.Finite.subset (Set.Finite.biUnion (finite_of_naiveHeight_le 47)
      (fun x _ => Set.Finite.prod (Set.finite_singleton x)
        (finite_equation_fiber x)))
    rintro ⟨px, py⟩ ⟨h1, h2⟩
    exact Set.mem_biUnion h1 ⟨rfl, h2⟩
  have hK : (insert none (Option.some ''
      {p : ℚ × ℚ | naiveHeight p.1 ≤ 47 ∧ E5077a1.toAffine.Equation p.1 p.2})
        : Set (Option (ℚ × ℚ))).Finite :=
    Set.Finite.insert none (hTfin.image _)
  apply Set.Finite.subset (Set.Finite.preimage toCoords_injective.injOn hK)
  rintro P ⟨n, rfl⟩
  rw [Set.mem_preimage]
  exact toCoords_mem_of_le (naiveHeight_le_47_of_canheight_zero h0 n)

/-! ## §10 — the torsion characterization -/

/-- **(d) THE KEY**: `ĥ(R) = 0` forces `R` to be torsion.  The doubling
orbit is finite (Northcott + ≤ 2 points per x), so `2^m R = 2^k R` for
some `m < k`, hence `(2^m − 2^k) • R = 0` with nonzero coefficient. -/
theorem canheight_eq_zero_torsion {R : E5077a1.toAffine.Point}
    (h0 : canheight R = 0) : IsOfFinAddOrder R := by
  have hfin := finite_orbit_of_canheight_zero h0
  have hnotinj : ¬ Function.Injective (fun n : ℕ => ((2 : ℤ) ^ n) • R) :=
    fun hinj => (Set.infinite_range_of_injective hinj) hfin
  obtain ⟨m, k, hmk, hne⟩ := Function.not_injective_iff.mp hnotinj
  have hmk' : ((2 : ℤ) ^ m) • R = ((2 : ℤ) ^ k) • R := hmk
  rw [isOfFinAddOrder_iff_zsmul_eq_zero]
  refine ⟨(2 : ℤ) ^ m - (2 : ℤ) ^ k, ?_, ?_⟩
  · intro hzero
    apply hne
    have h2 : (2 : ℤ) ^ m = (2 : ℤ) ^ k := sub_eq_zero.mp hzero
    have h2n : (2 : ℕ) ^ m = 2 ^ k := by exact_mod_cast h2
    exact Nat.pow_right_injective le_rfl h2n
  · rw [sub_zsmul, hmk']
    exact add_neg_cancel _

/-- **(e) The converse**: torsion points have `ĥ = 0`.  A finite orbit has
bounded naive height (r130), so `hseq R n ≤ log B / 4ⁿ → 0`. -/
theorem canheight_of_torsion {R : E5077a1.toAffine.Point}
    (h : IsOfFinAddOrder R) : canheight R = 0 := by
  have hfinite : ((AddSubgroup.zmultiples R :
      AddSubgroup E5077a1.toAffine.Point) : Set E5077a1.toAffine.Point).Finite :=
    h.finite_zmultiples
  obtain ⟨B, hB⟩ := exists_bound_of_finite (hfinite.image X)
  have hBn : ∀ n : ℕ, naiveHeight (X (((2 : ℤ) ^ n) • R)) ≤ B := by
    intro n
    apply hB
    exact ⟨((2 : ℤ) ^ n) • R,
      AddSubgroup.mem_zmultiples_iff.mpr ⟨(2 : ℤ) ^ n, rfl⟩, rfl⟩
  have hle : ∀ n : ℕ, hseq R n ≤ Real.log B / 4 ^ n := by
    intro n
    have hlog : lognh (((2 : ℤ) ^ n) • R) ≤ Real.log B := by
      unfold lognh
      exact Real.log_le_log (naiveHeight_real_pos _) (by exact_mod_cast hBn n)
    calc hseq R n = lognh (((2 : ℤ) ^ n) • R) / 4 ^ n := rfl
      _ ≤ Real.log B / 4 ^ n := by gcongr
  have htend0 : Tendsto (fun n : ℕ => Real.log B / 4 ^ n) atTop (𝓝 0) := by
    have h4 : Tendsto (fun n : ℕ => ((1 : ℝ) / 4) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hmul := h4.const_mul (Real.log B)
    rw [mul_zero] at hmul
    have hfun : (fun n : ℕ => Real.log B * ((1 : ℝ) / 4) ^ n)
        = fun n : ℕ => Real.log B / 4 ^ n := by
      funext n
      rw [div_pow, one_pow, mul_one_div]
    rwa [hfun] at hmul
  have hsq : Tendsto (hseq R) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend0
      (hseq_nonneg R) hle
  exact tendsto_nhds_unique (tendsto_hseq R) hsq

/-- **The full characterization**: `ĥ(R) = 0 ↔ R` is torsion. -/
theorem canheight_eq_zero_iff_torsion (R : E5077a1.toAffine.Point) :
    canheight R = 0 ↔ IsOfFinAddOrder R :=
  ⟨canheight_eq_zero_torsion, canheight_of_torsion⟩

end PrincipiaTractalis.CanonicalHeight5077a1

#print axioms PrincipiaTractalis.CanonicalHeight5077a1.lognh_dbl_window
#print axioms PrincipiaTractalis.CanonicalHeight5077a1.hseq_cauchySeq
#print axioms PrincipiaTractalis.CanonicalHeight5077a1.canheight_nonneg
#print axioms PrincipiaTractalis.CanonicalHeight5077a1.canheight_dbl
#print axioms PrincipiaTractalis.CanonicalHeight5077a1.canheight_window
#print axioms PrincipiaTractalis.CanonicalHeight5077a1.canheight_two_pow
#print axioms PrincipiaTractalis.CanonicalHeight5077a1.finite_of_naiveHeight_le
#print axioms PrincipiaTractalis.CanonicalHeight5077a1.canheight_eq_zero_torsion
#print axioms PrincipiaTractalis.CanonicalHeight5077a1.canheight_of_torsion
#print axioms PrincipiaTractalis.CanonicalHeight5077a1.canheight_eq_zero_iff_torsion
