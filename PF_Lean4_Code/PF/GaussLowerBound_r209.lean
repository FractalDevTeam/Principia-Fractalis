/-
# PF.GaussLowerBound_r209 — certified Hausdorff dimension LOWER bounds for the
# Gauss continued-fraction Cantor sets

Companion to `PF.GaussDimension_r208`, which supplies the level-2 covering
(UPPER) bounds.  This file supplies the matching LOWER bounds, by the
nonlinear analogue of the r207 Cantor-staircase construction: a Bernoulli
address map built from clamped-argument telescoping approximants, Hölder on
the attractor, and surjective onto `[0,1]`.

## What this file proves

**Strong separation and expansion (reusable infrastructure).**

* `gaussGap K = 1 / (K·(1 + K·(K+1)))` — the explicit minimal gap between two
  distinct level-1 Gauss cylinders.  `gaussGap 2 = 1/14`, `gaussGap 3 = 1/39`.
* `gauss_separation` — for `i ≠ j` and `x, y ∈ gaussJ K`,
  `|φ_i x − φ_j y| ≥ gaussGap K`.  Proved for GENERAL `K` from the explicit
  endpoints `φ_j(gaussJ K) = [1/(j+2), (K+1)/(1+(j+1)(K+1))]`.
* `agauss j = 1/(j+2)²` and `gauss_antilipschitz` — `|φ_j x − φ_j y| ≥ a_j·|x−y|`
  on `gaussJ K`.  Purely algebraic (Möbius difference identity); NO mean value
  theorem, NO derivative.
* `gauss_lip_real` — the matching uniform contraction `LmaxK K = ((K+1)/(K+2))²`.

**The Bernoulli address map.**

* `GaussWeights K` — a weight vector `p : Fin K → ℝ`, positive, summing to `1`,
  bounded by an explicit `c < 1`.
* `gapprox` / `gaddr` — the approximants and their telescoping limit, exactly
  the r207 pattern: clamping the *arguments* of the inverse branches
  (`gpre K j x = clampJ (1/clampJ x − (j+1))`) makes every approximant
  continuous on all of `ℝ` with no gluing conditions.
* `gfree_unique` — for each `x` at most ONE inverse branch is unclamped.  This
  is what makes the operator a `c`-contraction (`gapprox_diff`).
* `gaddr_funeq` — `A(φ_i u) = Q_i + p_i·(1 − A u)` on `gaussJ K`, with
  `Q_i = ∑_{j>i} p_j`.  The orientation flip `1 − A u` is FORCED: every Gauss
  branch reverses orientation, so the naive `A(φ_i u) = P_i + p_i·A u` is
  inconsistent with the geometry.

**Hölder and surjectivity.**

* `gaddr_holder_aux` / `gaddr_dist_le` / `gaddr_holderOn` — if `p_j ≤ a_j^s`
  for all `j`, then `A` is `s`-Hölder on `E` with constant `γ^(−s)`.  The
  descent is an induction on a COUNTER, not on cylinder words.
* `unitInterval_subset_gaddr_image` — `[0,1] ⊆ A '' E`.
* `le_dimH_of_gaussWeights` — the abstract conclusion `s ≤ dim_H E`, via
  r206's `le_dimH_of_holder_surj`.

**The two numeric instances.**

* `le_dimH_gauss_three : ENNReal.ofReal (54/100) ≤ dimH E`  (`K = 3`,
  weights `(0.4726, 0.3051, 0.2223)`).
* `le_dimH_gauss_two   : ENNReal.ofReal (39/100) ≤ dimH E`  (`K = 2`,
  weights `(0.5810, 0.4190)`).
* `dimH_gauss_three_enclosure`, `dimH_gauss_two_enclosure` — combined with
  r208.

## HONESTY STATEMENT — read this before quoting anything from this file

1. **THESE ARE BERNOULLI BOUNDS, NOT THE EQUILIBRIUM STATE.**  The lower bounds
   come from a Bernoulli (i.i.d. product) weighting of the digit alphabet, NOT
   from the Gibbs / equilibrium measure of the Gauss IFS.  A Bernoulli measure
   can never attain the dimension of a NONLINEAR conformal attractor: the
   distortion of the cylinders is not captured by any fixed digit weighting.
   The exponents certified here are therefore strictly, and knowably, below the
   truth.

2. **THE RESULTING ENCLOSURES, EXPLICITLY.**

   | | lower (this file) | upper (r208) | TRUE value |
   |---|---|---|---|
   | `K = 3` | `0.54` | `0.77` | `0.7056609…` |
   | `K = 2` | `0.39` | `0.58` | `0.5312805…` |

   The true values are Jenkinson–Pollicott's transfer-operator computations.
   **THE GAP IS NOT CLOSED HERE.**  Neither endpoint of either enclosure is an
   approximation to the true value, and neither may ever be quoted as one.

3. **WHAT WOULD CLOSE IT.**  The equilibrium state for the potential
   `−s·log|φ'|`, i.e. Ruelle–Perron–Frobenius theory for the Gauss transfer
   operator on a space of analytic/Lipschitz functions, together with the Gibbs
   property `μ(cylinder) ≍ |cylinder|^s`.  That work is **NOT STARTED** in this
   project and is **NOT SHORTENED** by anything in this file.  What this file
   does contribute to it is the strong-separation constant `gaussGap` and the
   two-sided branch estimates, which every route needs.

4. **THE ATTRACTOR IS A HYPOTHESIS, NEVER CONSTRUCTED.**  `E` is assumed to be
   contained in `gaussJ K`, nonempty, closed, forward invariant
   (`MapsTo (φ_j) E E`) and backward covered (`E ⊆ ⋃ⱼ φⱼ '' E`).  The
   Hutchinson attractor is never built, never shown nonempty, never shown
   unique.  Every theorem is a conditional statement.

   Note that FORWARD invariance is genuinely necessary for a lower bound and is
   an extra hypothesis relative to r205/r208: backward covering alone is
   satisfied by the empty set, which has dimension `0`.

5. **THE `s` VALUES ARE BELOW THE INF-MORAN ROOT, ON PURPOSE.**  With
   `a_j = 1/(j+2)²` the root of `∑_j a_j^s = 1` is `≈ 0.5410657` (`K = 3`) and
   `≈ 0.3939425` (`K = 2`).  We certify `0.54` and `0.39`, strictly below.
   Raising `s` above the root would make the weight condition `p_j ≤ a_j^s`
   incompatible with `∑ p_j = 1` — and the statement FALSE.  The inf-Moran root
   itself is below the true dimension because `a_j` is the INFIMUM of `|φ_j'|`.

6. No `sorry`, no `native_decide`, no project axioms.  All results reduce to
   `[propext, Classical.choice, Quot.sound]`.

## Relation to r207

r207 built the ternary Cantor staircase for the LINEAR IFS `x/3, (2+x)/3` and
obtained the exact dimension.  Here the IFS is nonlinear and orientation
reversing, which changes two things: the functional equation acquires the flip
`1 − A(u)`, and no choice of Bernoulli weights can be sharp.  The construction
mechanism (clamped arguments, telescoping series, at-most-one-free-branch
contraction, compact image + density) is otherwise identical.
-/

import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic
import PF.HausdorffIFS_r205
import PF.CantorDimension_r206
import PF.GaussDimension_r208

open scoped NNReal ENNReal Topology
open Set

namespace PrincipiaTractalis.GaussLowerBound

open PrincipiaTractalis.HausdorffIFS

/-! ## §0 — pure-real algebraic cores

Everything algebraic is factored through plain real variables so that no
`Fin`-cast or `set`-bound definition ever reaches `field_simp` / `nlinarith`. -/

/-- The Möbius difference identity for `t ↦ 1/(t+m)`. -/
theorem inv_shift_abs_diff {m x y : ℝ} (hx : 0 < x + m) (hy : 0 < y + m) :
    |1 / (x + m) - 1 / (y + m)| = |x - y| / ((x + m) * (y + m)) := by
  have hx' : x + m ≠ 0 := ne_of_gt hx
  have hy' : y + m ≠ 0 := ne_of_gt hy
  have h : 1 / (x + m) - 1 / (y + m) = (y - x) / ((x + m) * (y + m)) := by
    field_simp
    ring
  rw [h, abs_div, abs_of_pos (mul_pos hx hy), abs_sub_comm]

/-- **Antilipschitz core.**  On `(0,1]` the branch `t ↦ 1/(t+m)` expands
distances by at least `1/(1+m)²`. -/
theorem inv_shift_anti {m x y : ℝ} (hm : 0 < m) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    |x - y| / ((1 + m) ^ 2) ≤ |1 / (x + m) - 1 / (y + m)| := by
  have hxm : 0 < x + m := by linarith
  have hym : 0 < y + m := by linarith
  rw [inv_shift_abs_diff hxm hym]
  have hle : (x + m) * (y + m) ≤ (1 + m) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < (x + m) * (y + m) := mul_pos hxm hym
  gcongr

/-- The elementary gap identity `1/n − Q/(1+nQ) = 1/(n(1+nQ))`, together with
monotonicity in `n`. -/
theorem gap_core {n Q K : ℝ} (hQ : 0 < Q) (hn : 0 < n) (hnK : n ≤ K) :
    1 / (K * (1 + K * Q)) ≤ 1 / n - Q / (1 + n * Q) := by
  have hnQ : (0 : ℝ) < 1 + n * Q := by nlinarith
  have hK : (0 : ℝ) < K := lt_of_lt_of_le hn hnK
  have hKQ : (0 : ℝ) < 1 + K * Q := by nlinarith
  have heq : 1 / n - Q / (1 + n * Q) = 1 / (n * (1 + n * Q)) := by
    field_simp
    ring
  rw [heq]
  have hsq : n ^ 2 ≤ K ^ 2 := by nlinarith
  have hmono : n * (1 + n * Q) ≤ K * (1 + K * Q) := by
    nlinarith [mul_le_mul_of_nonneg_right hsq hQ.le]
  have hpos : (0 : ℝ) < n * (1 + n * Q) := mul_pos hn hnQ
  gcongr

/-- The separation core: if `2 ≤ n ≤ K`, `n ≤ u` and `Q > 0` then the gap
between `1/n` and `Q/(1+uQ)` is at least `1/(K(1+KQ))`. -/
theorem sep_core {n u Q K : ℝ} (hQ : 0 < Q) (hn : 0 < n) (hnu : n ≤ u) (hnK : n ≤ K) :
    1 / (K * (1 + K * Q)) ≤ 1 / n - Q / (1 + u * Q) := by
  have hnQ : (0 : ℝ) < 1 + n * Q := by nlinarith
  have huQ : (0 : ℝ) < 1 + u * Q := by nlinarith
  have h1 : Q / (1 + u * Q) ≤ Q / (1 + n * Q) := by
    gcongr
  have h2 := gap_core (n := n) (Q := Q) (K := K) hQ hn hnK
  linarith

/-! ## §1 — the invariant interval, restated -/

variable {K : ℕ}

theorem mem_gaussJ_iff {x : ℝ} : x ∈ gaussJ K ↔ 1 / ((K : ℝ) + 1) ≤ x ∧ x ≤ 1 := Iff.rfl

theorem gaussJ_pos {x : ℝ} (hx : x ∈ gaussJ K) : 0 < x := by
  have h : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
  exact lt_of_lt_of_le h hx.1

theorem gaussJ_le_one {x : ℝ} (hx : x ∈ gaussJ K) : x ≤ 1 := hx.2

/-- The real digit attached to the branch index `j : Fin K` is `j + 1`. -/
theorem gauss_digit_pos (j : Fin K) : (0 : ℝ) < ((j : ℕ) : ℝ) + 1 := by positivity

theorem gaussIFS_eq (j : Fin K) (x : ℝ) :
    gaussIFS K j x = 1 / (x + (((j : ℕ) : ℝ) + 1)) := rfl

/-! ## §2 — DELIVERABLE 1: the per-branch antilipschitz constant

`a_j = 1/(j+2)²` is the infimum of `|φ_j'|` over the invariant interval
(the derivative `1/(x+j+1)²` is smallest at the right endpoint `x = 1`). -/

/-- `agauss j = 1/(j+2)²`: the exact lower bound for `|φ_j'|` on `gaussJ K`. -/
noncomputable def agauss (j : ℕ) : ℝ := 1 / (((j : ℝ) + 2) ^ 2)

theorem agauss_pos (j : ℕ) : 0 < agauss j := by
  unfold agauss
  positivity

theorem agauss_le_one (j : ℕ) : agauss j ≤ 1 := by
  unfold agauss
  rw [div_le_one (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

@[simp] theorem agauss_zero : agauss 0 = 1 / 4 := by norm_num [agauss]
@[simp] theorem agauss_one : agauss 1 = 1 / 9 := by norm_num [agauss]
@[simp] theorem agauss_two : agauss 2 = 1 / 16 := by norm_num [agauss]

/-- **Per-branch expansion (antilipschitz) bound.**

For `x, y` in the invariant interval `gaussJ K`,
`|φ_j x − φ_j y| ≥ a_j · |x − y|` with `a_j = 1/(j+2)²`.

Proved algebraically from the Möbius difference identity; no mean value
theorem, no derivative. -/
theorem gauss_antilipschitz (j : Fin K) {x y : ℝ}
    (hx : x ∈ gaussJ K) (hy : y ∈ gaussJ K) :
    agauss (j : ℕ) * |x - y| ≤ |gaussIFS K j x - gaussIFS K j y| := by
  have hm : (0 : ℝ) < ((j : ℕ) : ℝ) + 1 := gauss_digit_pos j
  have h := inv_shift_anti (m := ((j : ℕ) : ℝ) + 1) (x := x) (y := y) hm
    (gaussJ_pos hx) (gaussJ_le_one hx) (gaussJ_pos hy) (gaussJ_le_one hy)
  have hrw : (1 + (((j : ℕ) : ℝ) + 1)) ^ 2 = (((j : ℕ) : ℝ) + 2) ^ 2 := by ring
  rw [hrw] at h
  simp only [gaussIFS_eq, agauss]
  rw [div_mul_eq_mul_div, one_mul]
  exact h

/-! ## §3 — DELIVERABLE 2: strong separation of the level-1 cylinders -/

/-- The explicit minimal gap between two distinct level-1 Gauss cylinders:
`γ K = 1 / (K · (1 + K·(K+1)))`.  `γ 2 = 1/14`, `γ 3 = 1/39`. -/
noncomputable def gaussGap (K : ℕ) : ℝ := 1 / ((K : ℝ) * (1 + (K : ℝ) * ((K : ℝ) + 1)))

@[simp] theorem gaussGap_two : gaussGap 2 = 1 / 14 := by norm_num [gaussGap]
@[simp] theorem gaussGap_three : gaussGap 3 = 1 / 39 := by norm_num [gaussGap]

theorem gaussGap_pos (hK : 1 ≤ K) : 0 < gaussGap K := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have h1 : (0 : ℝ) < 1 + (K : ℝ) * ((K : ℝ) + 1) := by nlinarith
  unfold gaussGap
  exact div_pos one_pos (mul_pos hKpos h1)

/-- Lower endpoint of the level-1 cylinder `φ_j(gaussJ K)`: `1/(j+2)`. -/
theorem gauss_cyl_lower (j : Fin K) {x : ℝ} (hx : x ∈ gaussJ K) :
    1 / (((j : ℕ) : ℝ) + 2) ≤ gaussIFS K j x := by
  have hx1 : x ≤ 1 := hx.2
  have hx0 : (0 : ℝ) < x := gaussJ_pos hx
  have hpos : (0 : ℝ) < x + (((j : ℕ) : ℝ) + 1) := by
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  rw [gaussIFS_eq]
  apply one_div_le_one_div_of_le hpos
  linarith

/-- Upper endpoint of the level-1 cylinder `φ_j(gaussJ K)`:
`(K+1)/(1 + (j+1)(K+1))`. -/
theorem gauss_cyl_upper (j : Fin K) {x : ℝ} (hx : x ∈ gaussJ K) :
    gaussIFS K j x
      ≤ ((K : ℝ) + 1) / (1 + (((j : ℕ) : ℝ) + 1) * ((K : ℝ) + 1)) := by
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hx1 : 1 / ((K : ℝ) + 1) ≤ x := hx.1
  have hpos : (0 : ℝ) < x + (((j : ℕ) : ℝ) + 1) := by
    have := gaussJ_pos hx
    linarith
  have hden : (0 : ℝ) < 1 + (((j : ℕ) : ℝ) + 1) * ((K : ℝ) + 1) := by nlinarith
  have heq : ((K : ℝ) + 1) / (1 + (((j : ℕ) : ℝ) + 1) * ((K : ℝ) + 1))
      = 1 / (1 / ((K : ℝ) + 1) + (((j : ℕ) : ℝ) + 1)) := by
    rw [div_eq_div_iff (ne_of_gt hden) (by positivity)]
    field_simp
  rw [gaussIFS_eq, heq]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **Strong separation, ordered form.**  If `i < j` then the `i`-th cylinder
lies entirely to the right of the `j`-th, separated by at least `γ K`. -/
theorem gauss_sep_lt {i j : Fin K} (hij : (i : ℕ) < (j : ℕ))
    {x y : ℝ} (hx : x ∈ gaussJ K) (hy : y ∈ gaussJ K) :
    gaussGap K ≤ gaussIFS K i x - gaussIFS K j y := by
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hij' : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hij
  have hjK : ((j : ℕ) : ℝ) + 1 ≤ (K : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hiK : ((i : ℕ) : ℝ) + 2 ≤ (K : ℝ) := by linarith
  have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlow := gauss_cyl_lower i hx
  have hupp := gauss_cyl_upper j hy
  have hcore := sep_core (n := ((i : ℕ) : ℝ) + 2) (u := ((j : ℕ) : ℝ) + 1)
    (Q := (K : ℝ) + 1) (K := (K : ℝ)) hK1 (by linarith) (by linarith) hiK
  have hgap : gaussGap K = 1 / ((K : ℝ) * (1 + (K : ℝ) * ((K : ℝ) + 1))) := rfl
  rw [hgap]
  linarith

/-- **Strong separation of the Gauss level-1 cylinders.**

For distinct branch indices `i ≠ j` and any `x, y` in the invariant interval,
`|φ_i x − φ_j y| ≥ γ K = 1/(K(1 + K(K+1)))`.

`γ 2 = 1/14`, `γ 3 = 1/39`.  This is the explicit strong-separation constant
required by every route to a Hausdorff-dimension LOWER bound. -/
theorem gauss_separation {i j : Fin K} (hij : i ≠ j)
    {x y : ℝ} (hx : x ∈ gaussJ K) (hy : y ∈ gaussJ K) :
    gaussGap K ≤ |gaussIFS K i x - gaussIFS K j y| := by
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have := gauss_sep_lt h hx hy
    calc gaussGap K ≤ gaussIFS K i x - gaussIFS K j y := this
      _ ≤ |gaussIFS K i x - gaussIFS K j y| := le_abs_self _
  · have := gauss_sep_lt h hy hx
    rw [abs_sub_comm]
    calc gaussGap K ≤ gaussIFS K j y - gaussIFS K i x := this
      _ ≤ |gaussIFS K j y - gaussIFS K i x| := le_abs_self _


/-! ## §4 — the clamped invariant interval

`clampJ K` retracts `ℝ` onto `gaussJ K = [β, 1]`, `β = 1/(K+1)`.  Exactly as in
r207, clamping inside the *arguments* of the approximants is what makes every
approximant continuous on all of `ℝ` with no gluing conditions. -/

/-- The left endpoint `β = 1/(K+1)` of the invariant interval. -/
noncomputable def betaK (K : ℕ) : ℝ := 1 / ((K : ℝ) + 1)

theorem betaK_pos : 0 < betaK K := by
  unfold betaK; positivity

theorem betaK_le_one : betaK K ≤ 1 := by
  unfold betaK
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  linarith

theorem betaK_lt_one (hK : 1 ≤ K) : betaK K < 1 := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  unfold betaK
  rw [div_lt_one (by positivity)]
  linarith

theorem gaussJ_eq_Icc : gaussJ K = Set.Icc (betaK K) 1 := rfl

theorem one_mem_gaussJ : (1 : ℝ) ∈ gaussJ K := ⟨betaK_le_one, le_rfl⟩

theorem betaK_mem_gaussJ : betaK K ∈ gaussJ K := ⟨le_rfl, betaK_le_one⟩

/-- The clamp of `ℝ` onto `gaussJ K`. -/
noncomputable def clampJ (K : ℕ) (t : ℝ) : ℝ := max (betaK K) (min t 1)

theorem clampJ_mem (t : ℝ) : clampJ K t ∈ gaussJ K := by
  refine ⟨le_max_left _ _, max_le betaK_le_one (min_le_right _ _)⟩

theorem clampJ_pos (t : ℝ) : 0 < clampJ K t := lt_of_lt_of_le betaK_pos (le_max_left _ _)

theorem clampJ_ne_zero (t : ℝ) : clampJ K t ≠ 0 := ne_of_gt (clampJ_pos t)

theorem clampJ_eq_self {t : ℝ} (ht : t ∈ gaussJ K) : clampJ K t = t := by
  have h1 : betaK K ≤ t := ht.1
  have h2 : t ≤ 1 := ht.2
  unfold clampJ
  rw [min_eq_left h2, max_eq_right h1]

theorem clampJ_of_le {t : ℝ} (ht : t ≤ betaK K) : clampJ K t = betaK K := by
  unfold clampJ
  rw [min_eq_left (ht.trans betaK_le_one), max_eq_left ht]

theorem clampJ_of_ge {t : ℝ} (ht : (1 : ℝ) ≤ t) : clampJ K t = 1 := by
  unfold clampJ
  rw [min_eq_right ht, max_eq_right betaK_le_one]

theorem continuous_clampJ : Continuous (clampJ K) :=
  continuous_const.max (continuous_id.min continuous_const)

/-! ## §5 — the clamped inverse branches

`gpre K j x = clampJ (1/clampJ x − (j+1))` is the `j`-th inverse Gauss branch,
argument-clamped on both sides.  On the `i`-th level-1 cylinder it returns the
preimage when `j = i`, the right endpoint `1` when `j < i`, and the left
endpoint `β` when `j > i` (`gpre_on_cylinder`).  That trichotomy is exactly the
mechanism which turns the averaging operator into the Bernoulli functional
equations. -/

/-- The clamped inverse branch. -/
noncomputable def gpre (K : ℕ) (j : Fin K) (x : ℝ) : ℝ :=
  clampJ K (1 / clampJ K x - (((j : ℕ) : ℝ) + 1))

theorem continuous_gpre (j : Fin K) : Continuous (gpre K j) := by
  unfold gpre
  exact continuous_clampJ.comp
    ((continuous_const.div continuous_clampJ (fun x => clampJ_ne_zero x)).sub continuous_const)

/-- The "free digit" predicate: the `j`-th inverse branch of `x` lands strictly
inside the invariant interval. -/
def gfree (K : ℕ) (j : Fin K) (x : ℝ) : Prop :=
  betaK K < 1 / clampJ K x - (((j : ℕ) : ℝ) + 1) ∧
    1 / clampJ K x - (((j : ℕ) : ℝ) + 1) < 1

/-- If the digit is not free, the clamped inverse branch sits at one of the two
endpoints. -/
theorem gpre_clamped {j : Fin K} {x : ℝ} (h : ¬ gfree K j x) :
    gpre K j x = betaK K ∨ gpre K j x = 1 := by
  unfold gfree at h
  push_neg at h
  by_cases h1 : betaK K < 1 / clampJ K x - (((j : ℕ) : ℝ) + 1)
  · exact Or.inr (clampJ_of_ge (h h1))
  · push_neg at h1
    exact Or.inl (clampJ_of_le h1)

/-- **At most one free digit.**  Two distinct inverse branches differ by a
nonzero integer, while the invariant interval has length `1 − β < 1`. -/
theorem gfree_unique {j j' : Fin K} {x : ℝ} (hj : gfree K j x) (hj' : gfree K j' x) :
    j = j' := by
  unfold gfree at hj hj'
  by_contra hne
  have hne' : (j : ℕ) ≠ (j' : ℕ) := fun h => hne (Fin.ext h)
  have hβ : 0 < betaK K := betaK_pos
  have hdiff : |(((j' : ℕ) : ℝ)) - (((j : ℕ) : ℝ))| < 1 := by
    have h1 := hj.1
    have h2 := hj.2
    have h3 := hj'.1
    have h4 := hj'.2
    rw [abs_lt]
    constructor <;> linarith
  have hint : (1 : ℝ) ≤ |(((j' : ℕ) : ℝ)) - (((j : ℕ) : ℝ))| := by
    rcases lt_or_gt_of_ne hne' with h | h
    · have hh : ((j : ℕ) : ℝ) + 1 ≤ ((j' : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt h
      have hge : (1 : ℝ) ≤ ((j' : ℕ) : ℝ) - ((j : ℕ) : ℝ) := by linarith
      exact hge.trans (le_abs_self _)
    · have hh : ((j' : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt h
      have hge : (1 : ℝ) ≤ ((j : ℕ) : ℝ) - ((j' : ℕ) : ℝ) := by linarith
      rw [abs_sub_comm]
      exact hge.trans (le_abs_self _)
  linarith

/-- The inverse branch at the right endpoint `1`: everything clamps to `β`. -/
theorem gpre_at_one (j : Fin K) : gpre K j 1 = betaK K := by
  unfold gpre
  rw [clampJ_eq_self (one_mem_gaussJ)]
  refine clampJ_of_le ?_
  have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hβ0 : (0 : ℝ) < betaK K := betaK_pos
  norm_num
  linarith

/-- The inverse branch at the left endpoint `β`: everything clamps to `1`. -/
theorem gpre_at_beta (j : Fin K) : gpre K j (betaK K) = 1 := by
  unfold gpre
  rw [clampJ_eq_self betaK_mem_gaussJ]
  refine clampJ_of_ge ?_
  have hinv : 1 / betaK K = (K : ℝ) + 1 := by
    unfold betaK
    rw [one_div_one_div]
  rw [hinv]
  have hj : ((j : ℕ) : ℝ) + 1 ≤ (K : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  linarith

/-- **The cylinder trichotomy.**  For `u` in the invariant interval and
`x = φ_i u`, the `j`-th clamped inverse branch of `x` is `1` if `j < i`, `u` if
`j = i`, and `β` if `j > i`. -/
theorem gpre_on_cylinder (i j : Fin K) {u : ℝ} (hu : u ∈ gaussJ K) :
    gpre K j (gaussIFS K i u)
      = if (j : ℕ) < (i : ℕ) then 1 else if j = i then u else betaK K := by
  have hxJ : gaussIFS K i u ∈ gaussJ K := gauss_mapsTo K i hu
  have hu0 : 0 < u := gaussJ_pos hu
  have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxpos : (0 : ℝ) < u + (((i : ℕ) : ℝ) + 1) := by linarith
  have hinv : 1 / clampJ K (gaussIFS K i u) = u + (((i : ℕ) : ℝ) + 1) := by
    rw [clampJ_eq_self hxJ, gaussIFS_eq, one_div_one_div]
  unfold gpre
  rw [hinv]
  rcases lt_trichotomy ((j : ℕ)) ((i : ℕ)) with h | h | h
  · rw [if_pos h]
    refine clampJ_of_ge ?_
    have hji : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have hβ : betaK K ≤ u := hu.1
    have hβ0 : 0 < betaK K := betaK_pos
    linarith
  · have hij : j = i := Fin.ext h
    rw [if_neg (by omega), if_pos hij, hij]
    have : u + (((i : ℕ) : ℝ) + 1) - (((i : ℕ) : ℝ) + 1) = u := by ring
    rw [this, clampJ_eq_self hu]
  · rw [if_neg (by omega), if_neg (fun hc => absurd (congrArg Fin.val hc) (by omega))]
    refine clampJ_of_le ?_
    have hij : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have hu1 : u ≤ 1 := hu.2
    have hβ : 0 < betaK K := betaK_pos
    have hβ1 : betaK K ≤ 1 := betaK_le_one
    -- u + i + 1 - (j+1) ≤ u - 1 ≤ 0 < β
    have hle : u + (((i : ℕ) : ℝ) + 1) - (((j : ℕ) : ℝ) + 1) ≤ 0 := by linarith
    linarith



/-! ## §6 — Bernoulli weights and the staircase approximants -/

/-- A Bernoulli weight vector for the `K`-branch Gauss IFS, with an explicit
uniform bound `c < 1` on the individual weights. -/
structure GaussWeights (K : ℕ) where
  /-- the weights -/
  w : Fin K → ℝ
  /-- a uniform upper bound for the weights, used as the contraction factor -/
  c : ℝ
  w_pos : ∀ j, 0 < w j
  w_sum : ∑ j, w j = 1
  w_le : ∀ j, w j ≤ c
  c_lt_one : c < 1

namespace GaussWeights

variable {K : ℕ}

theorem w_nonneg (P : GaussWeights K) (j : Fin K) : 0 ≤ P.w j := (P.w_pos j).le

theorem card_pos (P : GaussWeights K) : 0 < K := by
  rcases Nat.eq_zero_or_pos K with h | h
  · exfalso
    subst h
    have := P.w_sum
    simp at this
  · exact h

theorem c_pos (P : GaussWeights K) : 0 < P.c := by
  obtain ⟨j⟩ : Nonempty (Fin K) := Fin.pos_iff_nonempty.1 P.card_pos
  exact lt_of_lt_of_le (P.w_pos j) (P.w_le j)

end GaussWeights

/-- The `n`-th Bernoulli-staircase approximant for the Gauss IFS.  The base is
the affine ramp on the invariant interval; each step applies the clamped
averaging operator `(Φ g)(x) = 1 − ∑ⱼ pⱼ · g(gpre j x)`. -/
noncomputable def gapprox (K : ℕ) (P : GaussWeights K) : ℕ → ℝ → ℝ
  | 0, x => (clampJ K x - betaK K) / (1 - betaK K)
  | (n + 1), x => 1 - ∑ j, P.w j * gapprox K P n (gpre K j x)

variable {K : ℕ}

theorem gapprox_zero_apply (P : GaussWeights K) (x : ℝ) :
    gapprox K P 0 x = (clampJ K x - betaK K) / (1 - betaK K) := rfl

theorem gapprox_succ_apply (P : GaussWeights K) (n : ℕ) (x : ℝ) :
    gapprox K P (n + 1) x = 1 - ∑ j, P.w j * gapprox K P n (gpre K j x) := rfl

theorem one_sub_betaK_pos (P : GaussWeights K) : 0 < 1 - betaK K :=
  sub_pos.2 (betaK_lt_one P.card_pos)

theorem gapprox_mem (P : GaussWeights K) (n : ℕ) (x : ℝ) :
    0 ≤ gapprox K P n x ∧ gapprox K P n x ≤ 1 := by
  have hden : 0 < 1 - betaK K := one_sub_betaK_pos P
  induction n generalizing x with
  | zero =>
      rw [gapprox_zero_apply]
      have hmem := clampJ_mem (K := K) x
      have hlo : betaK K ≤ clampJ K x := hmem.1
      have hhi : clampJ K x ≤ 1 := hmem.2
      constructor
      · exact div_nonneg (by linarith) hden.le
      · rw [div_le_one hden]
        linarith
  | succ n ih =>
      rw [gapprox_succ_apply]
      have hle : ∑ j, P.w j * gapprox K P n (gpre K j x) ≤ ∑ j : Fin K, P.w j := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc P.w j * gapprox K P n (gpre K j x) ≤ P.w j * 1 :=
              mul_le_mul_of_nonneg_left (ih _).2 (P.w_nonneg j)
          _ = P.w j := by ring
      have hge : (0 : ℝ) ≤ ∑ j, P.w j * gapprox K P n (gpre K j x) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (P.w_nonneg j) (ih _).1
      rw [P.w_sum] at hle
      constructor <;> linarith

theorem gapprox_nonneg (P : GaussWeights K) (n : ℕ) (x : ℝ) : 0 ≤ gapprox K P n x :=
  (gapprox_mem P n x).1

theorem gapprox_le_one (P : GaussWeights K) (n : ℕ) (x : ℝ) : gapprox K P n x ≤ 1 :=
  (gapprox_mem P n x).2

/-- **The two boundary values, proved simultaneously.**  Each step of the
operator swaps them: `β ↦ 1` and `1 ↦ β` under every inverse branch. -/
theorem gapprox_bdry (P : GaussWeights K) (n : ℕ) :
    gapprox K P n (betaK K) = 0 ∧ gapprox K P n 1 = 1 := by
  have hden : 0 < 1 - betaK K := one_sub_betaK_pos P
  induction n with
  | zero =>
      rw [gapprox_zero_apply, gapprox_zero_apply,
        clampJ_eq_self (betaK_mem_gaussJ (K := K)), clampJ_eq_self (one_mem_gaussJ (K := K))]
      constructor
      · simp
      · field_simp
  | succ n ih =>
      constructor
      · rw [gapprox_succ_apply]
        have h : ∀ j : Fin K, P.w j * gapprox K P n (gpre K j (betaK K)) = P.w j := by
          intro j
          rw [gpre_at_beta j, ih.2]
          ring
        rw [Finset.sum_congr rfl fun j _ => h j, P.w_sum]
        ring
      · rw [gapprox_succ_apply]
        have h : ∀ j : Fin K, P.w j * gapprox K P n (gpre K j 1) = 0 := by
          intro j
          rw [gpre_at_one j, ih.1]
          ring
        rw [Finset.sum_congr rfl fun j _ => h j]
        simp

theorem gapprox_at_beta (P : GaussWeights K) (n : ℕ) : gapprox K P n (betaK K) = 0 :=
  (gapprox_bdry P n).1

theorem gapprox_at_one (P : GaussWeights K) (n : ℕ) : gapprox K P n 1 = 1 :=
  (gapprox_bdry P n).2

theorem gapprox_continuous (P : GaussWeights K) (n : ℕ) : Continuous (gapprox K P n) := by
  induction n with
  | zero =>
      have h : gapprox K P 0 = fun x : ℝ => (clampJ K x - betaK K) / (1 - betaK K) := rfl
      rw [h]
      exact (continuous_clampJ.sub continuous_const).div_const _
  | succ n ih =>
      have h : gapprox K P (n + 1)
          = fun x : ℝ => 1 - ∑ j, P.w j * gapprox K P n (gpre K j x) := rfl
      rw [h]
      exact continuous_const.sub
        (continuous_finset_sum _ fun j _ => continuous_const.mul (ih.comp (continuous_gpre j)))

/-! ### The Bernoulli functional equations at the approximant level -/

/-- The partial weight `Q_i = ∑_{j>i} p_j` — the total mass of the cylinders
lying strictly to the LEFT of the `i`-th one. -/
noncomputable def Wtail (P : GaussWeights K) (i : Fin K) : ℝ :=
  ∑ j : Fin K, if (i : ℕ) < (j : ℕ) then P.w j else 0

theorem Wtail_nonneg (P : GaussWeights K) (i : Fin K) : 0 ≤ Wtail P i := by
  unfold Wtail
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases h : (i : ℕ) < (j : ℕ)
  · rw [if_pos h]; exact P.w_nonneg j
  · rw [if_neg h]

/-- Splitting the total mass `1` into "strictly right of `i`", "`i`" and
"strictly left of `i`". -/
theorem Wsplit (P : GaussWeights K) (i : Fin K) :
    (∑ j : Fin K, if (j : ℕ) < (i : ℕ) then P.w j else 0) + P.w i + Wtail P i = 1 := by
  unfold Wtail
  have hre : (∑ j : Fin K, if (j : ℕ) < (i : ℕ) then P.w j else 0) + P.w i
        + (∑ j : Fin K, if (i : ℕ) < (j : ℕ) then P.w j else 0)
      = ((∑ j : Fin K, if (j : ℕ) < (i : ℕ) then P.w j else 0)
        + (∑ j : Fin K, if (i : ℕ) < (j : ℕ) then P.w j else 0)) + P.w i := by ring
  rw [hre, ← Finset.sum_add_distrib]
  have h : ∀ j : Fin K,
      ((if (j : ℕ) < (i : ℕ) then P.w j else 0) + if (i : ℕ) < (j : ℕ) then P.w j else 0)
        = P.w j - (if j = i then P.w j else 0) := by
    intro j
    rcases lt_trichotomy ((j : ℕ)) ((i : ℕ)) with h | h | h
    · rw [if_pos h, if_neg (by omega), if_neg (fun hc => absurd (congrArg Fin.val hc) (by omega))]
      ring
    · have hij : j = i := Fin.ext h
      subst hij
      rw [if_neg (lt_irrefl _), if_pos rfl]
      ring
    · have hji : ¬ ((j : ℕ) < (i : ℕ)) := by omega
      have hne : ¬ (j = i) := fun hc => absurd (congrArg Fin.val hc) (by omega)
      simp only [if_neg hji, if_pos h, if_neg hne]
      ring
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib, P.w_sum,
    Finset.sum_ite_eq' Finset.univ i (fun j => P.w j)]
  simp

/-- **The Bernoulli functional equation, approximant level.**

`g_{n+1}(φ_i u) = Q_i + p_i · (1 − g_n(u))` for `u` in the invariant interval.

The orientation flip `1 − g_n(u)` is forced: every Gauss branch reverses
orientation, and `Q_i` is the mass to the left of the `i`-th cylinder. -/
theorem gapprox_funeq (P : GaussWeights K) (n : ℕ) (i : Fin K) {u : ℝ} (hu : u ∈ gaussJ K) :
    gapprox K P (n + 1) (gaussIFS K i u)
      = Wtail P i + P.w i * (1 - gapprox K P n u) := by
  rw [gapprox_succ_apply]
  have hb1 := gapprox_at_one P n
  have hb0 := gapprox_at_beta P n
  have hterm : ∀ j : Fin K, P.w j * gapprox K P n (gpre K j (gaussIFS K i u))
      = (if (j : ℕ) < (i : ℕ) then P.w j else 0)
        + (if j = i then P.w i * gapprox K P n u else 0) := by
    intro j
    rw [gpre_on_cylinder i j hu]
    rcases lt_trichotomy ((j : ℕ)) ((i : ℕ)) with h | h | h
    · rw [if_pos h, if_pos h, if_neg (fun hc => absurd (congrArg Fin.val hc) (by omega)), hb1]
      ring
    · have hij : j = i := Fin.ext h
      subst hij
      simp
    · have hji : ¬ ((j : ℕ) < (i : ℕ)) := by omega
      have hne : ¬ (j = i) := fun hc => absurd (congrArg Fin.val hc) (by omega)
      simp only [if_neg hji, if_neg hne]
      rw [hb0]
      ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i (fun _ => P.w i * gapprox K P n u)]
  have hsplit := Wsplit P i
  simp only [Finset.mem_univ, if_true]
  have hexp : P.w i * (1 - gapprox K P n u) = P.w i - P.w i * gapprox K P n u := by ring
  rw [hexp]
  linarith

/-! ### The contraction estimate

For each `x` at most ONE inverse branch is unclamped (`gfree_unique`); the
clamped ones contribute the *same* boundary value to both approximants and
cancel.  That is where the factor `c = max_j p_j < 1` comes from. -/

theorem gapprox_diff (P : GaussWeights K) (n : ℕ) (x : ℝ) :
    |gapprox K P (n + 1) x - gapprox K P n x| ≤ P.c ^ n := by
  induction n generalizing x with
  | zero =>
      have h1 := gapprox_nonneg P 1 x
      have h2 := gapprox_le_one P 1 x
      have h3 := gapprox_nonneg P 0 x
      have h4 := gapprox_le_one P 0 x
      rw [pow_zero, abs_sub_le_iff]
      constructor <;> linarith
  | succ n ih =>
      classical
      set F : Fin K → ℝ := fun j =>
        P.w j * (gapprox K P (n + 1) (gpre K j x) - gapprox K P n (gpre K j x)) with hF
      have hsplit : ∑ j, F j
          = (∑ j, P.w j * gapprox K P (n + 1) (gpre K j x))
            - ∑ j, P.w j * gapprox K P n (gpre K j x) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [hF]; ring
      have heq : gapprox K P (n + 1 + 1) x - gapprox K P (n + 1) x = -(∑ j, F j) := by
        rw [gapprox_succ_apply, gapprox_succ_apply, hsplit]
        ring
      have hzero : ∀ j : Fin K, ¬ gfree K j x → F j = 0 := by
        intro j hj
        rcases gpre_clamped hj with h | h
        · rw [hF]
          simp only
          rw [h, gapprox_at_beta P (n + 1), gapprox_at_beta P n]
          ring
        · rw [hF]
          simp only
          rw [h, gapprox_at_one P (n + 1), gapprox_at_one P n]
          ring
      have hkey : |∑ j, F j| ≤ P.c ^ (n + 1) := by
        by_cases hex : ∃ j0 : Fin K, gfree K j0 x
        · obtain ⟨j0, hj0⟩ := hex
          have hsingle : ∑ j, F j = F j0 := by
            refine Finset.sum_eq_single j0 (fun j _ hj => hzero j ?_) (by simp)
            exact fun hf => hj (gfree_unique hf hj0)
          rw [hsingle, hF]
          simp only
          rw [abs_mul, abs_of_nonneg (P.w_nonneg j0)]
          calc P.w j0 * |gapprox K P (n + 1) (gpre K j0 x) - gapprox K P n (gpre K j0 x)|
              ≤ P.c * P.c ^ n :=
                mul_le_mul (P.w_le j0) (ih _) (abs_nonneg _) P.c_pos.le
            _ = P.c ^ (n + 1) := by rw [pow_succ]; ring
        · push_neg at hex
          have hall : ∀ j ∈ (Finset.univ : Finset (Fin K)), F j = 0 :=
            fun j _ => hzero j (hex j)
          rw [Finset.sum_eq_zero hall, abs_zero]
          exact pow_nonneg P.c_pos.le _
      rw [heq, abs_neg]
      exact hkey



/-! ## §7 — the Bernoulli address map -/

theorem gapprox_summable (P : GaussWeights K) (x : ℝ) :
    Summable fun n : ℕ => gapprox K P (n + 1) x - gapprox K P n x := by
  refine Summable.of_norm_bounded
    (summable_geometric_of_lt_one P.c_pos.le P.c_lt_one) ?_
  intro n
  rw [Real.norm_eq_abs]
  exact gapprox_diff P n x

/-- **The Bernoulli address map** for the `K`-branch Gauss IFS, defined as the
sum of the telescoping series of clamped approximants. -/
noncomputable def gaddr (K : ℕ) (P : GaussWeights K) (x : ℝ) : ℝ :=
  gapprox K P 0 x + ∑' n : ℕ, (gapprox K P (n + 1) x - gapprox K P n x)

theorem tendsto_gapprox (P : GaussWeights K) (x : ℝ) :
    Filter.Tendsto (fun n => gapprox K P n x) Filter.atTop (𝓝 (gaddr K P x)) := by
  have hs := (gapprox_summable P x).hasSum.tendsto_sum_nat
  have hrw : ∀ n : ℕ, ∑ i ∈ Finset.range n, (gapprox K P (i + 1) x - gapprox K P i x)
      = gapprox K P n x - gapprox K P 0 x :=
    fun n => Finset.sum_range_sub (fun i => gapprox K P i x) n
  simp only [hrw] at hs
  have h2 := hs.add_const (gapprox K P 0 x)
  have h3 : (fun n : ℕ => gapprox K P n x - gapprox K P 0 x + gapprox K P 0 x)
      = fun n => gapprox K P n x := by
    funext n; ring
  rw [h3] at h2
  have h4 : (∑' n : ℕ, (gapprox K P (n + 1) x - gapprox K P n x)) + gapprox K P 0 x
      = gaddr K P x := by
    rw [gaddr]; ring
  rwa [h4] at h2

theorem gaddr_of_tendsto {P : GaussWeights K} {x L : ℝ}
    (h : Filter.Tendsto (fun n => gapprox K P n x) Filter.atTop (𝓝 L)) : gaddr K P x = L :=
  tendsto_nhds_unique (tendsto_gapprox P x) h

theorem gaddr_nonneg (P : GaussWeights K) (x : ℝ) : 0 ≤ gaddr K P x :=
  ge_of_tendsto' (tendsto_gapprox P x) fun n => gapprox_nonneg P n x

theorem gaddr_le_one (P : GaussWeights K) (x : ℝ) : gaddr K P x ≤ 1 :=
  le_of_tendsto' (tendsto_gapprox P x) fun n => gapprox_le_one P n x

theorem gaddr_at_beta (P : GaussWeights K) : gaddr K P (betaK K) = 0 := by
  refine gaddr_of_tendsto ?_
  rw [show (fun n : ℕ => gapprox K P n (betaK K)) = fun _ => (0 : ℝ) from
    funext fun n => gapprox_at_beta P n]
  exact tendsto_const_nhds

theorem gaddr_at_one (P : GaussWeights K) : gaddr K P 1 = 1 := by
  refine gaddr_of_tendsto ?_
  rw [show (fun n : ℕ => gapprox K P n 1) = fun _ => (1 : ℝ) from
    funext fun n => gapprox_at_one P n]
  exact tendsto_const_nhds

theorem continuous_gaddr (P : GaussWeights K) : Continuous (gaddr K P) := by
  have h1 : Continuous fun x : ℝ => gapprox K P 0 x := gapprox_continuous P 0
  have h2 : Continuous fun x : ℝ => ∑' n : ℕ, (gapprox K P (n + 1) x - gapprox K P n x) := by
    refine continuous_tsum (u := fun n : ℕ => P.c ^ n)
      (fun n => (gapprox_continuous P (n + 1)).sub (gapprox_continuous P n))
      (summable_geometric_of_lt_one P.c_pos.le P.c_lt_one) ?_
    intro n x
    rw [Real.norm_eq_abs]
    exact gapprox_diff P n x
  exact h1.add h2

/-- **The Bernoulli functional equation.**

`A(φ_i u) = Q_i + p_i · (1 − A(u))` for `u` in the invariant interval, where
`Q_i = ∑_{j>i} p_j` is the mass of the cylinders to the left of the `i`-th.

Consequently `A` maps the `i`-th level-1 cylinder into an interval of length
exactly `p_i`. -/
theorem gaddr_funeq (P : GaussWeights K) (i : Fin K) {u : ℝ} (hu : u ∈ gaussJ K) :
    gaddr K P (gaussIFS K i u) = Wtail P i + P.w i * (1 - gaddr K P u) := by
  refine gaddr_of_tendsto ?_
  rw [← Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => gapprox K P n (gaussIFS K i u)) 1]
  rw [show (fun n : ℕ => gapprox K P (n + 1) (gaussIFS K i u))
      = fun n : ℕ => Wtail P i + P.w i * (1 - gapprox K P n u) from
    funext fun n => gapprox_funeq P n i hu]
  exact ((((tendsto_gapprox P u).const_sub 1).const_mul (P.w i)).const_add (Wtail P i))



/-! ## §8 — the Hölder estimate

The descent is an induction on a *counter* `N`, not on cylinder words: if
`|x − y| > Lmax^N` then `x` and `y` cannot have a common address prefix longer
than `N`, and peeling one branch at a time either separates them (gap `γ`) or
strictly increases the counter budget. -/

/-- A uniform contraction factor for all Gauss branches on `gaussJ K`:
`Lmax = ((K+1)/(K+2))²`.  `Lmax 2 = 9/16`, `Lmax 3 = 16/25`. -/
noncomputable def LmaxK (K : ℕ) : ℝ := (((K : ℝ) + 1) / ((K : ℝ) + 2)) ^ 2

theorem LmaxK_pos : 0 < LmaxK K := by
  unfold LmaxK
  have h : (0 : ℝ) < ((K : ℝ) + 1) / ((K : ℝ) + 2) := by positivity
  positivity

theorem LmaxK_lt_one : LmaxK K < 1 := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have h1 : ((K : ℝ) + 1) / ((K : ℝ) + 2) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have h0 : (0 : ℝ) ≤ ((K : ℝ) + 1) / ((K : ℝ) + 2) := by positivity
  unfold LmaxK
  nlinarith

theorem LmaxK_mul_sq (K : ℕ) : (1 : ℝ) = LmaxK K * (betaK K + 1) ^ 2 := by
  have hK1 : ((K : ℝ) + 1) ≠ 0 := by positivity
  have hK2 : ((K : ℝ) + 2) ≠ 0 := by positivity
  unfold LmaxK betaK
  field_simp
  ring

/-- **Lipschitz core.**  On `[b, ∞)` with `m ≥ 1`, the branch `t ↦ 1/(t+m)`
contracts by at least `L = 1/(b+1)²`. -/
theorem inv_shift_lip {m x y b L : ℝ} (hm : 1 ≤ m) (hb : 0 < b)
    (hbx : b ≤ x) (hby : b ≤ y) (hL : (1 : ℝ) = L * (b + 1) ^ 2) :
    |1 / (x + m) - 1 / (y + m)| ≤ L * |x - y| := by
  have hb1 : (0 : ℝ) < (b + 1) ^ 2 := by positivity
  have hne : ((b : ℝ) + 1) ^ 2 ≠ 0 := ne_of_gt hb1
  have hxm : (0 : ℝ) < x + m := by linarith
  have hym : (0 : ℝ) < y + m := by linarith
  have hD : (b + 1) ^ 2 ≤ (x + m) * (y + m) := by nlinarith
  have hLval : L = 1 / (b + 1) ^ 2 := by
    field_simp
    linarith
  rw [inv_shift_abs_diff hxm hym]
  calc |x - y| / ((x + m) * (y + m)) ≤ |x - y| / ((b + 1) ^ 2) := by
        gcongr
    _ = L * |x - y| := by rw [hLval]; ring

/-- Each Gauss branch contracts by the uniform factor `LmaxK K < 1` on the
invariant interval. -/
theorem gauss_lip_real (j : Fin K) {x y : ℝ} (hx : x ∈ gaussJ K) (hy : y ∈ gaussJ K) :
    |gaussIFS K j x - gaussIFS K j y| ≤ LmaxK K * |x - y| := by
  have hm : (1 : ℝ) ≤ ((j : ℕ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hbx : betaK K ≤ x := hx.1
  have hby : betaK K ≤ y := hy.1
  simp only [gaussIFS_eq]
  exact inv_shift_lip hm betaK_pos hbx hby (LmaxK_mul_sq K)

/-- Two points of the invariant interval are at distance at most `1 − β < 1`. -/
theorem gaussJ_abs_sub_lt_one {x y : ℝ} (hx : x ∈ gaussJ K) (hy : y ∈ gaussJ K) :
    |x - y| < 1 := by
  have h1 : betaK K ≤ x := hx.1
  have h2 : x ≤ 1 := hx.2
  have h3 : betaK K ≤ y := hy.1
  have h4 : y ≤ 1 := hy.2
  have hβ : 0 < betaK K := betaK_pos
  rw [abs_lt]
  constructor <;> linarith

/-- The address map contracts by exactly `p_i` along the `i`-th branch. -/
theorem gaddr_branch_abs (P : GaussWeights K) (i : Fin K) {u v : ℝ}
    (hu : u ∈ gaussJ K) (hv : v ∈ gaussJ K) :
    |gaddr K P (gaussIFS K i u) - gaddr K P (gaussIFS K i v)|
      = P.w i * |gaddr K P u - gaddr K P v| := by
  rw [gaddr_funeq P i hu, gaddr_funeq P i hv]
  have h : Wtail P i + P.w i * (1 - gaddr K P u)
      - (Wtail P i + P.w i * (1 - gaddr K P v))
      = P.w i * (gaddr K P v - gaddr K P u) := by ring
  rw [h, abs_mul, abs_of_nonneg (P.w_nonneg i), abs_sub_comm]

/-- **The Hölder descent.**  Counter form: if the two points are farther apart
than `Lmax^N`, the estimate holds. -/
theorem gaddr_holder_aux (P : GaussWeights K) {E : Set ℝ} {s : ℝ} (hs : 0 < s)
    (hEJ : E ⊆ gaussJ K) (hself : E ⊆ ⋃ j, gaussIFS K j '' E)
    (hws : ∀ j : Fin K, P.w j ≤ agauss (j : ℕ) ^ s) :
    ∀ (N : ℕ) (x y : ℝ), x ∈ E → y ∈ E → LmaxK K ^ N < |x - y| →
      |gaddr K P x - gaddr K P y| ≤ (|x - y| / gaussGap K) ^ s := by
  have hγ : 0 < gaussGap K := gaussGap_pos P.card_pos
  intro N
  induction N with
  | zero =>
      intro x y hx hy hlt
      rw [pow_zero] at hlt
      exact absurd hlt (not_lt.2 (gaussJ_abs_sub_lt_one (hEJ hx) (hEJ hy)).le)
  | succ N ih =>
      intro x y hx hy hlt
      obtain ⟨i, x', hx'E, hxeq⟩ := Set.mem_iUnion.1 (hself hx)
      obtain ⟨j, y', hy'E, hyeq⟩ := Set.mem_iUnion.1 (hself hy)
      have hx'J : x' ∈ gaussJ K := hEJ hx'E
      have hy'J : y' ∈ gaussJ K := hEJ hy'E
      by_cases hij : i = j
      · -- same branch: peel and recurse
        subst hij
        subst hxeq
        subst hyeq
        have hLpos : 0 < LmaxK K := LmaxK_pos
        have hlip := gauss_lip_real i hx'J hy'J
        have hstep : LmaxK K ^ N < |x' - y'| := by
          rw [pow_succ] at hlt
          nlinarith [pow_pos hLpos N]
        have hrec := ih x' y' hx'E hy'E hstep
        rw [gaddr_branch_abs P i hx'J hy'J]
        -- w i * (|x'-y'|/γ)^s ≤ (a i)^s * (|x'-y'|/γ)^s = (a i * (|x'-y'|/γ))^s ≤ (|x-y|/γ)^s
        have hanti := gauss_antilipschitz i hx'J hy'J
        have ha0 : 0 < agauss (i : ℕ) := agauss_pos _
        have hq0 : (0 : ℝ) ≤ |x' - y'| / gaussGap K := by positivity
        have hmono : P.w i * (|x' - y'| / gaussGap K) ^ s
            ≤ agauss (i : ℕ) ^ s * (|x' - y'| / gaussGap K) ^ s := by
          exact mul_le_mul_of_nonneg_right (hws i) (Real.rpow_nonneg hq0 s)
        have hcomb : agauss (i : ℕ) ^ s * (|x' - y'| / gaussGap K) ^ s
            = (agauss (i : ℕ) * (|x' - y'| / gaussGap K)) ^ s :=
          (Real.mul_rpow ha0.le hq0).symm
        have hinner : agauss (i : ℕ) * (|x' - y'| / gaussGap K)
            ≤ |gaussIFS K i x' - gaussIFS K i y'| / gaussGap K := by
          rw [mul_div_assoc']
          gcongr
        have hfinal : (agauss (i : ℕ) * (|x' - y'| / gaussGap K)) ^ s
            ≤ (|gaussIFS K i x' - gaussIFS K i y'| / gaussGap K) ^ s :=
          Real.rpow_le_rpow (by positivity) hinner hs.le
        calc P.w i * |gaddr K P x' - gaddr K P y'|
            ≤ P.w i * (|x' - y'| / gaussGap K) ^ s :=
              mul_le_mul_of_nonneg_left hrec (P.w_nonneg i)
          _ ≤ agauss (i : ℕ) ^ s * (|x' - y'| / gaussGap K) ^ s := hmono
          _ = (agauss (i : ℕ) * (|x' - y'| / gaussGap K)) ^ s := hcomb
          _ ≤ (|gaussIFS K i x' - gaussIFS K i y'| / gaussGap K) ^ s := hfinal
      · -- different branches: the explicit gap does it
        have hsep : gaussGap K ≤ |x - y| := by
          rw [← hxeq, ← hyeq]
          exact gauss_separation hij hx'J hy'J
        have hone : (1 : ℝ) ≤ |x - y| / gaussGap K := by
          rw [le_div_iff₀ hγ, one_mul]
          exact hsep
        have hge : (1 : ℝ) ≤ (|x - y| / gaussGap K) ^ s := by
          have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hone hs.le
          rwa [Real.one_rpow] at this
        have hA1 := gaddr_nonneg P x
        have hA2 := gaddr_le_one P x
        have hA3 := gaddr_nonneg P y
        have hA4 := gaddr_le_one P y
        have : |gaddr K P x - gaddr K P y| ≤ 1 := by
          rw [abs_sub_le_iff]
          constructor <;> linarith
        linarith



/-- **The Hölder estimate for the Bernoulli address map**, `dist` form:
`|A x − A y| ≤ γ^(−s) · |x − y|^s` for all `x, y ∈ E`. -/
theorem gaddr_dist_le (P : GaussWeights K) {E : Set ℝ} {s : ℝ} (hs : 0 < s)
    (hEJ : E ⊆ gaussJ K) (hself : E ⊆ ⋃ j, gaussIFS K j '' E)
    (hws : ∀ j : Fin K, P.w j ≤ agauss (j : ℕ) ^ s)
    {x y : ℝ} (hx : x ∈ E) (hy : y ∈ E) :
    |gaddr K P x - gaddr K P y| ≤ (1 / gaussGap K) ^ s * |x - y| ^ s := by
  have hγ : 0 < gaussGap K := gaussGap_pos P.card_pos
  rcases eq_or_lt_of_le (abs_nonneg (x - y)) with h0 | h0
  · have hxy : x = y := sub_eq_zero.1 (abs_eq_zero.1 h0.symm)
    subst hxy
    simp only [sub_self, abs_zero]
    positivity
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one h0 (LmaxK_lt_one (K := K))
    have hmain := gaddr_holder_aux P hs hEJ hself hws N x y hx hy hN
    have hrw : (|x - y| / gaussGap K) ^ s = (1 / gaussGap K) ^ s * |x - y| ^ s := by
      rw [show |x - y| / gaussGap K = (1 / gaussGap K) * |x - y| by ring,
        Real.mul_rpow (by positivity) (abs_nonneg _)]
    rwa [hrw] at hmain

/-- **`HolderOnWith` packaging** of the address map on `E`, exponent `s`,
constant `γ^(−s)`. -/
theorem gaddr_holderOn (P : GaussWeights K) {E : Set ℝ} {s : ℝ} (hs : 0 < s)
    (hEJ : E ⊆ gaussJ K) (hself : E ⊆ ⋃ j, gaussIFS K j '' E)
    (hws : ∀ j : Fin K, P.w j ≤ agauss (j : ℕ) ^ s) :
    HolderOnWith (((1 / gaussGap K) ^ s).toNNReal) s.toNNReal (gaddr K P) E := by
  have hγ : 0 < gaussGap K := gaussGap_pos P.card_pos
  have hCnn : (0 : ℝ) ≤ (1 / gaussGap K) ^ s := Real.rpow_nonneg (by positivity) s
  have hCcoe : ((((1 / gaussGap K) ^ s).toNNReal : ℝ≥0) : ℝ) = (1 / gaussGap K) ^ s :=
    Real.coe_toNNReal _ hCnn
  intro x hx y hy
  have hscoe : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.le
  have hC : ((((1 / gaussGap K) ^ s).toNNReal : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal ((1 / gaussGap K) ^ s) := by
    rw [← ENNReal.ofReal_coe_nnreal, hCcoe]
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, hscoe,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs.le, hC,
    ← ENNReal.ofReal_mul hCnn]
  exact ENNReal.ofReal_le_ofReal (gaddr_dist_le P hs hEJ hself hws hx hy)



/-! ## §9 — the address map is onto `[0,1]`

The image `A '' E` is compact, nonempty, contained in `[0,1]`, and stable under
the `K` affine maps `t ↦ Q_i + p_i(1 − t)` whose ranges tile `[0,1]`.  Hence it
is dense in `[0,1]`, hence equal to it.

This step needs the attractor hypotheses in FORWARD form: `E` nonempty, closed,
and `φ_j`-invariant.  (Backward covering alone cannot give a lower bound: the
empty set is backward-covering.) -/

/-- Tail sums of the weights, `T_k = ∑_{j ≥ k} p_j`. -/
noncomputable def Tsum (P : GaussWeights K) (k : ℕ) : ℝ :=
  ∑ j : Fin K, if k ≤ (j : ℕ) then P.w j else 0

theorem Tsum_zero (P : GaussWeights K) : Tsum P 0 = 1 := by
  unfold Tsum
  simpa using P.w_sum

theorem Tsum_card (P : GaussWeights K) : Tsum P K = 0 := by
  unfold Tsum
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj := j.isLt
  rw [if_neg (by omega)]

theorem Wtail_eq_Tsum (P : GaussWeights K) (i : Fin K) :
    Wtail P i = Tsum P ((i : ℕ) + 1) := by
  unfold Wtail Tsum
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (i : ℕ) < (j : ℕ)
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem Tsum_succ (P : GaussWeights K) {k : ℕ} (hk : k < K) :
    Tsum P k = Tsum P (k + 1) + P.w ⟨k, hk⟩ := by
  have hsingle : (∑ j : Fin K, if (j : ℕ) = k then P.w j else 0) = P.w ⟨k, hk⟩ := by
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin K)]
    · simp
    · intro b _ hb
      exact if_neg fun hc => hb (Fin.ext hc)
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  have h : ∀ j : Fin K, (if k ≤ (j : ℕ) then P.w j else 0)
      = (if k + 1 ≤ (j : ℕ) then P.w j else 0) + (if (j : ℕ) = k then P.w j else 0) := by
    intro j
    rcases lt_trichotomy ((j : ℕ)) k with h1 | h1 | h1
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
    · rw [if_pos (by omega), if_neg (by omega), if_pos h1]; ring
    · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]; ring
  unfold Tsum
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib]
  unfold Tsum at hsingle
  rw [hsingle]

/-- **The weight blocks tile `[0,1]`.**  Downward induction on the tail index. -/
theorem weight_cover (P : GaussWeights K) :
    ∀ (d k : ℕ), k + d = K → ∀ t : ℝ, 0 ≤ t → t ≤ Tsum P k →
      ∃ i : Fin K, Wtail P i ≤ t ∧ t ≤ Wtail P i + P.w i := by
  intro d
  induction d with
  | zero =>
      intro k hk t ht0 htk
      have hkK : k = K := by omega
      rw [hkK, Tsum_card] at htk
      have ht : t = 0 := le_antisymm htk ht0
      have hKpos : 0 < K := P.card_pos
      obtain ⟨i0, hi0⟩ : ∃ i : Fin K, (i : ℕ) + 1 = K :=
        ⟨⟨K - 1, by omega⟩, by simp; omega⟩
      have hw : Wtail P i0 = 0 := by rw [Wtail_eq_Tsum, hi0, Tsum_card]
      refine ⟨i0, ?_, ?_⟩
      · rw [hw, ht]
      · rw [hw, ht]
        linarith [P.w_nonneg i0]
  | succ d ih =>
      intro k hk t ht0 htk
      have hkK : k < K := by omega
      have hnext : (k + 1) + d = K := by omega
      by_cases hle : t ≤ Tsum P (k + 1)
      · exact ih (k + 1) hnext t ht0 hle
      · push_neg at hle
        refine ⟨⟨k, hkK⟩, ?_, ?_⟩
        · rw [Wtail_eq_Tsum]
          exact le_of_lt hle
        · rw [Wtail_eq_Tsum]
          have hts := Tsum_succ P hkK
          simp only []
          linarith

/-- **Density of the image.**  Every `t ∈ [0,1]` is within `c^n` of the image. -/
theorem gaddr_image_dense (P : GaussWeights K) {E : Set ℝ}
    (hEJ : E ⊆ gaussJ K) (hne : E.Nonempty)
    (hinv : ∀ j : Fin K, Set.MapsTo (gaussIFS K j) E E) :
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 → ∃ z ∈ gaddr K P '' E, |t - z| ≤ P.c ^ n := by
  intro n
  induction n with
  | zero =>
      intro t ht0 ht1
      obtain ⟨x, hx⟩ := hne
      refine ⟨gaddr K P x, ⟨x, hx, rfl⟩, ?_⟩
      rw [pow_zero, abs_le]
      have h1 := gaddr_nonneg P x
      have h2 := gaddr_le_one P x
      constructor <;> linarith
  | succ n ih =>
      intro t ht0 ht1
      obtain ⟨i, hi1, hi2⟩ :=
        weight_cover P K 0 (by omega) t ht0 (by rw [Tsum_zero]; exact ht1)
      have hwi : 0 < P.w i := P.w_pos i
      set r : ℝ := 1 - (t - Wtail P i) / P.w i with hrdef
      have hr0 : 0 ≤ r := by
        rw [hrdef, sub_nonneg, div_le_one hwi]
        linarith
      have hr1 : r ≤ 1 := by
        rw [hrdef]
        have : 0 ≤ (t - Wtail P i) / P.w i := div_nonneg (by linarith) hwi.le
        linarith
      have hteq : t = Wtail P i + P.w i * (1 - r) := by
        rw [hrdef]
        field_simp
        ring
      obtain ⟨z', hz'im, hz'⟩ := ih r hr0 hr1
      obtain ⟨u, huE, hzu⟩ := hz'im
      refine ⟨gaddr K P (gaussIFS K i u), ⟨gaussIFS K i u, hinv i huE, rfl⟩, ?_⟩
      rw [gaddr_funeq P i (hEJ huE)]
      have hexp : t - (Wtail P i + P.w i * (1 - gaddr K P u))
          = P.w i * (gaddr K P u - r) := by
        rw [hteq]; ring
      rw [hexp, abs_mul, abs_of_nonneg hwi.le]
      have hz'' : |gaddr K P u - r| ≤ P.c ^ n := by
        rw [abs_sub_comm, hzu]
        exact hz'
      calc P.w i * |gaddr K P u - r| ≤ P.c * P.c ^ n :=
            mul_le_mul (P.w_le i) hz'' (abs_nonneg _) P.c_pos.le
        _ = P.c ^ (n + 1) := by rw [pow_succ]; ring

/-- **Surjectivity onto the unit interval.** -/
theorem unitInterval_subset_gaddr_image (P : GaussWeights K) {E : Set ℝ}
    (hEJ : E ⊆ gaussJ K) (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin K, Set.MapsTo (gaussIFS K j) E E) :
    Set.Icc (0 : ℝ) 1 ⊆ gaddr K P '' E := by
  have hJc : IsCompact (gaussJ K) := isCompact_Icc
  have hcompact : IsCompact E := hJc.of_isClosed_subset hclosed hEJ
  have hclosedIm : IsClosed (gaddr K P '' E) :=
    (hcompact.image (continuous_gaddr P)).isClosed
  intro t ht
  have hmem : t ∈ closure (gaddr K P '' E) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε P.c_lt_one
    obtain ⟨z, hz, hdz⟩ := gaddr_image_dense P hEJ hne hinv n t ht.1 ht.2
    exact ⟨z, hz, by rw [Real.dist_eq]; linarith⟩
  rwa [hclosedIm.closure_eq] at hmem

/-! ## §10 — the abstract lower bound -/

theorem dimH_unitInterval : dimH (Set.Icc (0 : ℝ) 1) = 1 := by
  have h : (interior (Set.Icc (0 : ℝ) 1)).Nonempty := by
    rw [interior_Icc]
    exact ⟨1 / 2, by norm_num, by norm_num⟩
  rw [Real.dimH_of_nonempty_interior h]
  simp

/-- **ABSTRACT LOWER BOUND for the Gauss continued-fraction Cantor sets.**

Let `E ⊆ [1/(K+1), 1]` be nonempty, closed, forward invariant under the `K`
Gauss branches, and backward covered by them.  Let `p` be a Bernoulli weight
vector with `p_j ≤ (1/(j+2)^2)^s` for every branch.  Then `s ≤ dim_H E`.

This is a lower bound obtained from a BERNOULLI measure, not from the Gibbs
(equilibrium) state; it therefore never attains the true dimension. -/
theorem le_dimH_of_gaussWeights (P : GaussWeights K) {E : Set ℝ} {s : ℝ} (hs : 0 < s)
    (hEJ : E ⊆ gaussJ K) (hself : E ⊆ ⋃ j, gaussIFS K j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin K, Set.MapsTo (gaussIFS K j) E E)
    (hws : ∀ j : Fin K, P.w j ≤ agauss (j : ℕ) ^ s) :
    ENNReal.ofReal s ≤ dimH E := by
  have hr : 0 < s.toNNReal := Real.toNNReal_pos.2 hs
  have h := PrincipiaTractalis.CantorDimension.le_dimH_of_holder_surj hr
    (gaddr_holderOn P hs hEJ hself hws)
    (unitInterval_subset_gaddr_image P hEJ hne hclosed hinv)
  rwa [dimH_unitInterval, mul_one] at h



/-! ## §11 — the two numeric instances

The `s`-th powers of the branch constants `a_j = 1/(j+2)²` are certified from
below by explicit rationals through the reduction `u ≤ x^(p/q) ↔ u^q ≤ x^p`
(the reverse of r205's `nnreal_rpow_le_of_pow_le`). -/

/-- Reverse rational-power reduction: `u^q ≤ x^p` gives `u ≤ x^(p/q)`. -/
theorem le_rpow_of_pow_le {x u : ℝ} (hx : 0 ≤ x) {pn q : ℕ} (hq : q ≠ 0)
    (h : u ^ q ≤ x ^ pn) : u ≤ x ^ ((pn : ℝ) / (q : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hv : (0 : ℝ) ≤ x ^ ((pn : ℝ) / (q : ℝ)) := Real.rpow_nonneg hx _
  have key : (x ^ ((pn : ℝ) / (q : ℝ))) ^ q = x ^ pn := by
    rw [← Real.rpow_natCast (x ^ ((pn : ℝ) / (q : ℝ))) q, ← Real.rpow_mul hx,
      div_mul_cancel₀ _ hq0.ne', Real.rpow_natCast]
  refine le_of_pow_le_pow_left₀ hq hv ?_
  rw [key]
  exact h

/-! ### `K = 3`, exponent `s = 54/100`

The inf-Moran root of `∑_j (1/(j+2)²)^s = 1` for `a = (1/4, 1/9, 1/16)` sits at
`≈ 0.5410657`; we stay strictly below it at `0.54`, where
`(1/4)^0.54 + (1/9)^0.54 + (1/16)^0.54 ≈ 1.00207 > 1`, leaving room for the
rational weights `(0.4726, 0.3051, 0.2223)` which sum to exactly `1`. -/

/-- The `K = 3` Bernoulli weight vector `(0.4726, 0.3051, 0.2223)`. -/
noncomputable def gaussW3 : GaussWeights 3 where
  w := ![4726 / 10000, 3051 / 10000, 2223 / 10000]
  c := 4726 / 10000
  w_pos := by intro j; fin_cases j <;> norm_num
  w_sum := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    norm_num
  w_le := by intro j; fin_cases j <;> norm_num
  c_lt_one := by norm_num

theorem gaussW3_ws (j : Fin 3) : gaussW3.w j ≤ agauss (j : ℕ) ^ ((54 : ℝ) / 100) := by
  fin_cases j
  · show (4726 / 10000 : ℝ) ≤ agauss 0 ^ ((54 : ℝ) / 100)
    rw [agauss_zero]
    exact le_rpow_of_pow_le (x := (1 / 4 : ℝ)) (u := (4726 / 10000 : ℝ))
      (pn := 54) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (3051 / 10000 : ℝ) ≤ agauss 1 ^ ((54 : ℝ) / 100)
    rw [agauss_one]
    exact le_rpow_of_pow_le (x := (1 / 9 : ℝ)) (u := (3051 / 10000 : ℝ))
      (pn := 54) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (2223 / 10000 : ℝ) ≤ agauss 2 ^ ((54 : ℝ) / 100)
    rw [agauss_two]
    exact le_rpow_of_pow_le (x := (1 / 16 : ℝ)) (u := (2223 / 10000 : ℝ))
      (pn := 54) (q := 100) (by norm_num) (by norm_num) (by norm_num)

/-! ### `K = 2`, exponent `s = 39/100`

Inf-Moran root `≈ 0.3939425`; at `0.39`,
`(1/4)^0.39 + (1/9)^0.39 ≈ 1.00684 > 1`, and the rational weights
`(0.5810, 0.4190)` sum to exactly `1`. -/

/-- The `K = 2` Bernoulli weight vector `(0.5810, 0.4190)`. -/
noncomputable def gaussW2 : GaussWeights 2 where
  w := ![5810 / 10000, 4190 / 10000]
  c := 5810 / 10000
  w_pos := by intro j; fin_cases j <;> norm_num
  w_sum := by norm_num [Fin.sum_univ_two]
  w_le := by intro j; fin_cases j <;> norm_num
  c_lt_one := by norm_num

theorem gaussW2_ws (j : Fin 2) : gaussW2.w j ≤ agauss (j : ℕ) ^ ((39 : ℝ) / 100) := by
  fin_cases j
  · show (5810 / 10000 : ℝ) ≤ agauss 0 ^ ((39 : ℝ) / 100)
    rw [agauss_zero]
    exact le_rpow_of_pow_le (x := (1 / 4 : ℝ)) (u := (5810 / 10000 : ℝ))
      (pn := 39) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (4190 / 10000 : ℝ) ≤ agauss 1 ^ ((39 : ℝ) / 100)
    rw [agauss_one]
    exact le_rpow_of_pow_le (x := (1 / 9 : ℝ)) (u := (4190 / 10000 : ℝ))
      (pn := 39) (q := 100) (by norm_num) (by norm_num) (by norm_num)

/-! ### The two certified lower bounds -/

/-- **LOWER BOUND, `K = 3`.**  Any nonempty closed `E ⊆ [1/4, 1]` which is both
forward invariant and backward covered by the three Gauss branches
`x ↦ 1/(x+1), 1/(x+2), 1/(x+3)` has `dim_H E ≥ 0.54`.

Combined with r208's `dimH_gauss_three_le_two` this gives the enclosure
`dim_H E ∈ [0.54, 0.77]`.  The true value is `0.7056609…`; the gap is NOT
closed here. -/
theorem le_dimH_gauss_three {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3) (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 3, Set.MapsTo (gaussIFS 3 j) E E) :
    ENNReal.ofReal ((54 : ℝ) / 100) ≤ dimH E :=
  le_dimH_of_gaussWeights gaussW3 (by norm_num) hEJ hself hne hclosed hinv gaussW3_ws

/-- **LOWER BOUND, `K = 2`.**  Any nonempty closed `E ⊆ [1/3, 1]` which is both
forward invariant and backward covered by the two Gauss branches
`x ↦ 1/(x+1), 1/(x+2)` has `dim_H E ≥ 0.39`.

Combined with r208's `dimH_gauss_two_le_two` this gives the enclosure
`dim_H E ∈ [0.39, 0.58]`.  The true value is `0.5312805…`; the gap is NOT
closed here. -/
theorem le_dimH_gauss_two {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2) (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 2, Set.MapsTo (gaussIFS 2 j) E E) :
    ENNReal.ofReal ((39 : ℝ) / 100) ≤ dimH E :=
  le_dimH_of_gaussWeights gaussW2 (by norm_num) hEJ hself hne hclosed hinv gaussW2_ws



/-! ## §12 — the enclosures, stated against r208's upper bounds -/

/-- **ENCLOSURE, `K = 3`.**  `0.54 ≤ dim_H E ≤ 0.77`.

Lower bound: this file (Bernoulli address map).  Upper bound: r208
(`dimH_gauss_three_le_two`, level-2 covering).  The TRUE value is
`0.7056609…` (Jenkinson–Pollicott).  Neither side of this enclosure is an
approximation to it, and the gap is NOT closed. -/
theorem dimH_gauss_three_enclosure {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3) (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 3, Set.MapsTo (gaussIFS 3 j) E E) :
    ENNReal.ofReal ((54 : ℝ) / 100) ≤ dimH E ∧ dimH E ≤ (77 / 100 : ℝ≥0∞) :=
  ⟨le_dimH_gauss_three hEJ hself hne hclosed hinv,
    PrincipiaTractalis.GaussDimension.dimH_gauss_three_le_two hEJ hself⟩

/-- **ENCLOSURE, `K = 2`.**  `0.39 ≤ dim_H E ≤ 0.58`.

Lower bound: this file.  Upper bound: r208 (`dimH_gauss_two_le_two`).  The TRUE
value is `0.5312805…` (Jenkinson–Pollicott).  The gap is NOT closed. -/
theorem dimH_gauss_two_enclosure {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2) (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 2, Set.MapsTo (gaussIFS 2 j) E E) :
    ENNReal.ofReal ((39 : ℝ) / 100) ≤ dimH E ∧ dimH E ≤ (29 / 50 : ℝ≥0∞) :=
  ⟨le_dimH_gauss_two hEJ hself hne hclosed hinv,
    PrincipiaTractalis.GaussDimension.dimH_gauss_two_le_two hEJ hself⟩


/-! ## Axiom audit -/

#print axioms inv_shift_abs_diff
#print axioms gauss_antilipschitz
#print axioms gauss_separation
#print axioms gpre_on_cylinder
#print axioms gfree_unique
#print axioms gapprox_bdry
#print axioms gapprox_funeq
#print axioms gapprox_diff
#print axioms gaddr_funeq
#print axioms continuous_gaddr
#print axioms gauss_lip_real
#print axioms gaddr_holder_aux
#print axioms gaddr_dist_le
#print axioms gaddr_holderOn
#print axioms weight_cover
#print axioms gaddr_image_dense
#print axioms unitInterval_subset_gaddr_image
#print axioms dimH_unitInterval
#print axioms le_dimH_of_gaussWeights
#print axioms gaussW3_ws
#print axioms gaussW2_ws
#print axioms le_dimH_gauss_three
#print axioms le_dimH_gauss_two
#print axioms dimH_gauss_three_enclosure
#print axioms dimH_gauss_two_enclosure

end PrincipiaTractalis.GaussLowerBound
