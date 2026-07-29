/-
# PF.PointQuasiParallelogram389a1_r149

★★★ 2026-07-28 — r149: THE QUASI-PARALLELOGRAM AT THE POINT LEVEL ★★★

Lifts r148f/r148g from x-coordinate algebra to the *group* `E389a1(ℚ)`.  For
two rational affine points with distinct x-coordinates:

  `h(x_P)²·h(x_Q)² ≤ 10368 · h(x(P+Q))·h(x(P−Q)) ≤ 10368·34 · h(x_P)²h(x_Q)²`

i.e. in logarithmic form, with `lognh` from r147,

  `|lognh(P+Q) + lognh(P−Q) − 2·lognh P − 2·lognh Q| ≤ log 10368`.

Everything the lower bound needed is discharged here from `x_P ≠ x_Q` alone:

* `P + Q ≠ 0` and `P − Q ≠ 0` — else `Q = −P` or `P = Q`, both forcing
  `x_P = x_Q`;
* `x(P+Q) ≠ x(P−Q)` — else the two points are equal or opposite
  (r148g's `eq_or_eq_neg_of_x_eq`), forcing `2Q = 0` or `2P = 0`, which
  r148g's `add_self_ne_zero` rules out;
* `(P+Q) + (P−Q) = 2P` and `(P+Q) − (P−Q) = 2Q` — abelian-group algebra,
  and r143's `dbl_x` identifies their x-coordinates with `f/g`.

HONEST SCOPE.  A height inequality on the group.  The *exact* parallelogram
for `canheight` (r147) is the next stone (r150): apply this at `2ⁿP, 2ⁿQ`,
divide by `4ⁿ`, let `n → ∞`.  No rank claim here.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.QuasiParallelogramLower389a1_r148g
import PF.CanonicalHeight389a1_r147

namespace PrincipiaTractalis.PointQuasiParallelogram389a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E389a1RankOne
open PrincipiaTractalis.CanonicalHeight389a1
open PrincipiaTractalis.SecantBridge389a1
open PrincipiaTractalis.QuasiParallelogramUpper389a1
open PrincipiaTractalis.QuasiParallelogramLower389a1
open WeierstrassCurve WeierstrassCurve.Affine

variable {xP yP xQ yQ : ℚ}

/-! ## §1 — the sum and difference are affine -/

/-- With distinct x-coordinates, `P + Q` is an affine point. -/
theorem add_ne_zero (hP : E389a1.toAffine.Nonsingular xP yP)
    (hQ : E389a1.toAffine.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    Point.some hP + Point.some hQ ≠ 0 := by
  rw [Point.add_of_X_ne hne]
  exact fun hc => Point.noConfusion hc

/-- With distinct x-coordinates, `P − Q` is an affine point. -/
theorem sub_ne_zero' (hP : E389a1.toAffine.Nonsingular xP yP)
    (hQ : E389a1.toAffine.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    Point.some hP - Point.some hQ ≠ 0 := by
  have hneg : -Point.some hQ
      = Point.some ((Affine.nonsingular_neg ..).mpr hQ) := Point.neg_some hQ
  rw [sub_eq_add_neg, hneg, Point.add_of_X_ne hne]
  exact fun hc => Point.noConfusion hc

/-! ## §2 — the affine data of `P ± Q` -/

/-- The x-coordinate of `P + Q`, named. -/
noncomputable def xR (xP xQ yP yQ : ℚ) : ℚ := xAdd xP xQ yP yQ

/-- The x-coordinate of `P − Q`, named. -/
noncomputable def xS (xP xQ yP yQ : ℚ) : ℚ :=
  xAdd xP xQ yP (E389a1.toAffine.negY xQ yQ)

theorem X_add (hP : E389a1.toAffine.Nonsingular xP yP)
    (hQ : E389a1.toAffine.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    X (Point.some hP + Point.some hQ) = xR xP xQ yP yQ :=
  X_add_eq hP hQ hne

theorem X_sub (hP : E389a1.toAffine.Nonsingular xP yP)
    (hQ : E389a1.toAffine.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    X (Point.some hP - Point.some hQ) = xS xP xQ yP yQ :=
  X_sub_eq hP hQ hne

/-! ## §3 — `x(P+Q) ≠ x(P−Q)` -/

/-- The x-coordinates of `P + Q` and `P − Q` are distinct.  Equality would
force `2Q = 0` or `2P = 0`, both excluded by `add_self_ne_zero`. -/
theorem xR_ne_xS (hP : E389a1.toAffine.Nonsingular xP yP)
    (hQ : E389a1.toAffine.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    xR xP xQ yP yQ ≠ xS xP xQ yP yQ := by
  intro hEq
  -- unpack the two points
  set R := Point.some hP + Point.some hQ with hRdef
  set S := Point.some hP - Point.some hQ with hSdef
  have hXR : X R = xR xP xQ yP yQ := X_add hP hQ hne
  have hXS : X S = xS xP xQ yP yQ := X_sub hP hQ hne
  -- R and S are affine, so obtain their `some` forms
  obtain ⟨xr, yr, hr, hRs⟩ : ∃ xr yr, ∃ h : E389a1.toAffine.Nonsingular xr yr,
      R = Point.some h := by
    rcases R with _ | @⟨xr, yr, hr⟩
    · exact absurd hRdef.symm (add_ne_zero hP hQ hne)
    · exact ⟨xr, yr, hr, rfl⟩
  obtain ⟨xs, ys, hs, hSs⟩ : ∃ xs ys, ∃ h : E389a1.toAffine.Nonsingular xs ys,
      S = Point.some h := by
    rcases S with _ | @⟨xs, ys, hs⟩
    · exact absurd hSdef.symm (sub_ne_zero' hP hQ hne)
    · exact ⟨xs, ys, hs, rfl⟩
  -- their x-coordinates coincide
  have hxr : xr = xR xP xQ yP yQ := by rw [← hXR, hRs]; rfl
  have hxs : xs = xS xP xQ yP yQ := by rw [← hXS, hSs]; rfl
  have hxx : xr = xs := by rw [hxr, hxs, hEq]
  subst hxx
  -- so R = S or R = −S
  rcases eq_or_eq_neg_of_x_eq hr hs with h | h
  · -- R = S ⟹ 2Q = 0
    have hRS : R = S := by rw [hRs, hSs]; exact h
    have h2Q : Point.some hQ + Point.some hQ = 0 := by
      rw [hRdef, hSdef] at hRS
      have := hRS
      abel_nf at this ⊢
      linear_combination (norm := abel) this
    exact add_self_ne_zero hQ h2Q
  · -- R = −S ⟹ 2P = 0
    have hRS : R = -S := by rw [hRs, hSs]; exact h
    have h2P : Point.some hP + Point.some hP = 0 := by
      rw [hRdef, hSdef] at hRS
      have := hRS
      abel_nf at this ⊢
      linear_combination (norm := abel) this
    exact add_self_ne_zero hP h2P

/-! ## §4 — `(P+Q) ± (P−Q) = 2P, 2Q` and their x-coordinates -/

/-- The sum of the output pair is `2P`. -/
theorem out_add (hP : E389a1.toAffine.Nonsingular xP yP)
    (hQ : E389a1.toAffine.Nonsingular xQ yQ) :
    (Point.some hP + Point.some hQ) + (Point.some hP - Point.some hQ)
      = Point.some hP + Point.some hP := by
  abel

/-- The difference of the output pair is `2Q`. -/
theorem out_sub (hP : E389a1.toAffine.Nonsingular xP yP)
    (hQ : E389a1.toAffine.Nonsingular xQ yQ) :
    (Point.some hP + Point.some hQ) - (Point.some hP - Point.some hQ)
      = Point.some hQ + Point.some hQ := by
  abel

/-- `X (P + P) = f x / g x` — r143's `dbl_x` in `X`-form. -/
theorem X_dbl (hP : E389a1.toAffine.Nonsingular xP yP) :
    X (Point.some hP + Point.some hP) = f xP / g xP := by
  obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x hP
  rw [hadd]
  show x' = f xP / g xP
  exact hx'

/-! ## §5 — THE CAPSTONE: the two-sided bound on the group -/

/-- **★★★ r149 — THE POINT-LEVEL TWO-SIDED QUASI-PARALLELOGRAM ★★★**

For two rational affine points of 389a1 with distinct x-coordinates, the
height product of `P ± Q` is pinned to `h(x_P)²h(x_Q)²` within the explicit
constants `1/10368` and `34`. -/
theorem point_two_sided (hP : E389a1.toAffine.Nonsingular xP yP)
    (hQ : E389a1.toAffine.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    naiveHeight xP ^ 2 * naiveHeight xQ ^ 2
        ≤ 10368 * (naiveHeight (X (Point.some hP + Point.some hQ))
                    * naiveHeight (X (Point.some hP - Point.some hQ))) ∧
    naiveHeight (X (Point.some hP + Point.some hQ))
        * naiveHeight (X (Point.some hP - Point.some hQ))
      ≤ 34 * naiveHeight xP ^ 2 * naiveHeight xQ ^ 2 := by
  have hXR : X (Point.some hP + Point.some hQ) = xR xP xQ yP yQ := X_add hP hQ hne
  have hXS : X (Point.some hP - Point.some hQ) = xS xP xQ yP yQ := X_sub hP hQ hne
  rw [hXR, hXS]
  -- the UPPER half is r148f applied directly
  have hupper : naiveHeight (xR xP xQ yP yQ) * naiveHeight (xS xP xQ yP yQ)
      ≤ 34 * naiveHeight xP ^ 2 * naiveHeight xQ ^ 2 := by
    simp only [xR, xS]
    exact height_prod_upper hne (eqn_of_nonsingular hP) (eqn_of_nonsingular hQ)
  refine ⟨?_, hupper⟩
  -- the LOWER half: extract the affine data of the output pair
  set R := Point.some hP + Point.some hQ with hRdef
  set S := Point.some hP - Point.some hQ with hSdef
  obtain ⟨xr, yr, hr, hRs⟩ : ∃ xr yr, ∃ h : E389a1.toAffine.Nonsingular xr yr,
      R = Point.some h := by
    rcases R with _ | @⟨xr, yr, hr⟩
    · exact absurd hRdef.symm (add_ne_zero hP hQ hne)
    · exact ⟨xr, yr, hr, rfl⟩
  obtain ⟨xs, ys, hs, hSs⟩ : ∃ xs ys, ∃ h : E389a1.toAffine.Nonsingular xs ys,
      S = Point.some h := by
    rcases S with _ | @⟨xs, ys, hs⟩
    · exact absurd hSdef.symm (sub_ne_zero' hP hQ hne)
    · exact ⟨xs, ys, hs, rfl⟩
  have hxr : xr = xR xP xQ yP yQ := by rw [← hXR, hRs]; rfl
  have hxs : xs = xS xP xQ yP yQ := by rw [← hXS, hSs]; rfl
  have hrs : xr ≠ xs := by rw [hxr, hxs]; exact xR_ne_xS hP hQ hne
  -- the two realization equations
  have hsumP : xAdd xr xs yr ys = f xP / g xP := by
    have h1 : X (Point.some hr + Point.some hs) = xAdd xr xs yr ys :=
      X_add_eq hr hs hrs
    have h2 : Point.some hr + Point.some hs
        = Point.some hP + Point.some hP := by
      rw [← hRs, ← hSs, hRdef, hSdef]
      abel
    rw [← h1, h2, X_dbl hP]
  have hsumQ : xAdd xr xs yr (E389a1.toAffine.negY xs ys) = f xQ / g xQ := by
    have h1 : X (Point.some hr - Point.some hs)
        = xAdd xr xs yr (E389a1.toAffine.negY xs ys) := X_sub_eq hr hs hrs
    have h2 : Point.some hr - Point.some hs
        = Point.some hQ + Point.some hQ := by
      rw [← hRs, ← hSs, hRdef, hSdef]
      abel
    rw [← h1, h2, X_dbl hQ]
  have hlow := height_prod_lower hP hQ hr hs hrs hsumP hsumQ
  rw [hxr, hxs] at hlow
  exact hlow

/-! ## §6 — logarithmic form, ready for the limit -/

/-- The two-sided bound in `lognh` form: the quasi-parallelogram defect on
389a1 is bounded by `log 10368`. -/
theorem lognh_defect_le (hP : E389a1.toAffine.Nonsingular xP yP)
    (hQ : E389a1.toAffine.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    |lognh (Point.some hP + Point.some hQ) + lognh (Point.some hP - Point.some hQ)
        - 2 * lognh (Point.some hP) - 2 * lognh (Point.some hQ)|
      ≤ Real.log 10368 := by
  obtain ⟨hlow, hup⟩ := point_two_sided hP hQ hne
  set R := Point.some hP + Point.some hQ
  set S := Point.some hP - Point.some hQ
  have hXP : X (Point.some hP) = xP := rfl
  have hXQ : X (Point.some hQ) = xQ := rfl
  -- positivity of all four heights, cast to ℝ
  have p1 : (0 : ℝ) < (naiveHeight (X R) : ℝ) := by exact_mod_cast naiveHeight_pos _
  have p2 : (0 : ℝ) < (naiveHeight (X S) : ℝ) := by exact_mod_cast naiveHeight_pos _
  have p3 : (0 : ℝ) < (naiveHeight xP : ℝ) := by exact_mod_cast naiveHeight_pos _
  have p4 : (0 : ℝ) < (naiveHeight xQ : ℝ) := by exact_mod_cast naiveHeight_pos _
  -- upper: log(hR·hS) ≤ log 34 + 2 log hP + 2 log hQ
  have hupR : ((naiveHeight (X R) : ℝ)) * ((naiveHeight (X S) : ℝ))
      ≤ 34 * (naiveHeight xP : ℝ) ^ 2 * (naiveHeight xQ : ℝ) ^ 2 := by
    have := (Nat.cast_le (α := ℝ)).mpr hup
    push_cast at this
    linarith [this]
  -- lower: 2 log hP + 2 log hQ ≤ log 10368 + log(hR·hS)
  have hlowR : (naiveHeight xP : ℝ) ^ 2 * (naiveHeight xQ : ℝ) ^ 2
      ≤ 10368 * (((naiveHeight (X R) : ℝ)) * ((naiveHeight (X S) : ℝ))) := by
    have := (Nat.cast_le (α := ℝ)).mpr hlow
    push_cast at this
    linarith [this]
  have logU := Real.log_le_log (by positivity) hupR
  have logL := Real.log_le_log (by positivity) hlowR
  rw [Real.log_mul (ne_of_gt p1) (ne_of_gt p2)] at logU
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at logU
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at logL
  rw [Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (ne_of_gt p1) (ne_of_gt p2)] at logL
  have h34 : Real.log 34 ≤ Real.log 10368 :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [abs_le]
  constructor
  · unfold lognh
    rw [hXP, hXQ]
    push_cast at logL ⊢
    linarith [logL]
  · unfold lognh
    rw [hXP, hXQ]
    push_cast at logU ⊢
    linarith [logU, h34]

end PrincipiaTractalis.PointQuasiParallelogram389a1

#print axioms PrincipiaTractalis.PointQuasiParallelogram389a1.add_ne_zero
#print axioms PrincipiaTractalis.PointQuasiParallelogram389a1.xR_ne_xS
#print axioms PrincipiaTractalis.PointQuasiParallelogram389a1.X_dbl
#print axioms PrincipiaTractalis.PointQuasiParallelogram389a1.point_two_sided
#print axioms PrincipiaTractalis.PointQuasiParallelogram389a1.lognh_defect_le
