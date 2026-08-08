/-
# PF.GaussLevelThree_r211 — the LEVEL-3 refinement of the Gauss
# continued-fraction Hausdorff-dimension enclosures

## What this file is

A **constant swap** into the abstract `AddrIFS` machinery of
`PF.GaussLevelTwo_r210` (Part A), instantiated on the `K³` THREE-digit Gauss
cylinders `φ_i ∘ φ_j ∘ φ_k`, `φ_d(x) = 1/(x+d)`, together with the matching
level-3 Moran/Falconer upper bounds through `PF.HausdorffIFS_r205`'s
`dimH_le_of_selfCover` (the r208 pattern).

Level 3 uses an ODD number of compositions, so the level-3 branches are
orientation-REVERSING — the same as r209's level 1, and unlike r210's level 2.
The `AddrIFS` orientation flag is therefore `flip = true` here.

## The enclosures

* `K = 3`:  `0.65 ≤ dim_H E ≤ 0.75`   (true value `0.7056609…`)
* `K = 2`:  `0.48 ≤ dim_H E ≤ 0.5625` (true value `0.5312805…`)

Widths improve on level 2 (`[0.63, 0.7625]` and `[0.46, 0.5715]`) by about
`0.033` and `0.029` respectively.

## HONESTY STATEMENT — read this before quoting anything from this file

**This is the practical ceiling of the refinement method.**  Level 4 needs 81
(resp. 16) words; the certificate cost grows exponentially while the enclosure
width shrinks only like `O(1/n)`.  The sharp value requires the equilibrium
state (Ruelle–Perron–Frobenius transfer operator), which is **not started** and
is **not approached** by refinement.  Neither endpoint below is an
approximation to the true dimension; both are certified brackets.

Further, as in r209 and r210:

* The attractor `E` is a HYPOTHESIS, never constructed: `E ⊆ gaussJ K`,
  nonempty, closed, level-1 forward invariant and level-1 backward covered.
  Level-3 self-covering and level-3 invariance follow by applying the level-1
  hypotheses three times.  Every theorem here is conditional.
* The lower exponents `13/20` and `12/25` are strictly BELOW the level-3
  inf-Moran roots (`0.6521470…` and `0.4860785…`); the upper exponents `3/4`
  and `9/16` are strictly ABOVE the level-3 sup-Moran roots (`0.7470141…` and
  `0.5603435…`).  Crossing either root would make the corresponding statement
  false.
* The bound is a BERNOULLI (i.i.d. product) weighting on three-digit cylinders,
  never the Gibbs / equilibrium state, hence never sharp.
* No `sorry`, no `native_decide`, no project axioms.  All results reduce to
  `[propext, Classical.choice, Quot.sound]`.

## The level-3 constants

For the word `w = (d₁, d₂, d₃)` the composite is the Möbius map

`Φ_w(x) = (1 + d₂(x + d₃)) / ((x + d₃) + d₁(1 + d₂(x + d₃))) = (A x + B)/(C x + D)`

with continuant matrix `[[0,1],[1,d₁]]·[[0,1],[1,d₂]]·[[0,1],[1,d₃]]`, i.e.

`A = d₂`, `B = 1 + d₂d₃`, `C = 1 + d₁d₂`, `D = d₁ + d₃ + d₁d₂d₃`, `AD − BC = −1`.

Hence `|Φ_w(x) − Φ_w(y)| = |x − y| / (P(x)P(y))` with `P(t) = Ct + D`, so on
`J = gaussJ K = [1/(K+1), 1]`

* antilipschitz constant `a_w = 1/P(1)² = 1/(C+D)²`  (`P` is largest at `x = 1`),
* Lipschitz constant `b_w = 1/P(1/(K+1))²`,
* `Φ_w` is DECREASING, cylinder `= [Φ_w(1), Φ_w(1/(K+1))]`.

Separations: `γ₃ = 1/492` for `K = 2` and `γ₃ = 1/4686` for `K = 3`, both the
exact minimal gap between consecutive level-3 cylinders.

## Word order (fixed and documented)

The `AddrIFS` index order is the order in which the inverse branches are read
off (`χ_{m'}(ψ_m u) = hi` exactly when `m' < m`).  Composing the level-1
trichotomy with r210's level-2 trichotomy gives, for the level-3 word
`(i,j,k)` versus the query word `(i',j',k')`, the value `hi` exactly when

`i' < i  ∨  (i' = i ∧ (j < j' ∨ (j' = j ∧ k' < k)))`.

So the words are sorted by **outer index ASCENDING, middle index DESCENDING,
inner index ASCENDING**.  Because the system is orientation reversing this is
the RIGHT-to-LEFT geometric order of the cylinders on the line.
-/

import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic
import PF.HausdorffIFS_r205
import PF.CantorDimension_r206
import PF.GaussDimension_r208
import PF.GaussLowerBound_r209
import PF.GaussLevelTwo_r210

open scoped NNReal ENNReal Topology
open Set

namespace PrincipiaTractalis.GaussLevelThree

open PrincipiaTractalis.HausdorffIFS
open PrincipiaTractalis.GaussLowerBound
open PrincipiaTractalis.GaussLevelTwo

set_option maxHeartbeats 4000000

/-! # §1 — pure-real cores for the three-step Möbius branch

Everything algebraic is stated for plain real variables `d1 d2 d3 x y b`, so
that no `Fin`-cast ever reaches `field_simp` / `nlinarith`. -/

/-- Closing up the third composition: `1/(u/(1+d₂u) + d₁)`. -/
theorem mob3_closed {d1 d2 u : ℝ} (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hu : 0 < u) :
    1 / (u / (1 + d2 * u) + d1) = (1 + d2 * u) / (u + d1 * (1 + d2 * u)) := by
  have h1 : (0 : ℝ) < 1 + d2 * u := by nlinarith
  have h2 : (0 : ℝ) ≤ d1 * (1 + d2 * u) := mul_nonneg hd1 h1.le
  have h3 : (0 : ℝ) < u + d1 * (1 + d2 * u) := by linarith
  rw [show u / (1 + d2 * u) + d1 = (u + d1 * (1 + d2 * u)) / (1 + d2 * u) by
        field_simp, one_div_div]

/-- **The Möbius difference identity at level 3.**  The determinant of the
three-step continuant matrix is `−1`, so the difference quotient collapses. -/
theorem mob3_abs_diff {d1 d2 d3 x y : ℝ}
    (hx : (0 : ℝ) < (x + d3) + d1 * (1 + d2 * (x + d3)))
    (hy : (0 : ℝ) < (y + d3) + d1 * (1 + d2 * (y + d3))) :
    |(1 + d2 * (x + d3)) / ((x + d3) + d1 * (1 + d2 * (x + d3)))
        - (1 + d2 * (y + d3)) / ((y + d3) + d1 * (1 + d2 * (y + d3)))|
      = |x - y| / (((x + d3) + d1 * (1 + d2 * (x + d3)))
          * ((y + d3) + d1 * (1 + d2 * (y + d3)))) := by
  rw [div_sub_div _ _ (ne_of_gt hx) (ne_of_gt hy),
    show (1 + d2 * (x + d3)) * ((y + d3) + d1 * (1 + d2 * (y + d3)))
        - ((x + d3) + d1 * (1 + d2 * (x + d3))) * (1 + d2 * (y + d3)) = y - x by ring,
    abs_div, abs_of_pos (mul_pos hx hy), abs_sub_comm]

/-- Positivity of the level-3 denominator `P(t) = (t+d₃) + d₁(1 + d₂(t+d₃))`. -/
theorem mob3_den_pos {d1 d2 d3 t : ℝ} (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (ht : 0 < t) : (0 : ℝ) < (t + d3) + d1 * (1 + d2 * (t + d3)) := by
  have h1 : (0 : ℝ) < t + d3 := by linarith
  have h2 : (0 : ℝ) < 1 + d2 * (t + d3) := by nlinarith [mul_nonneg hd2 h1.le]
  have h3 : (0 : ℝ) ≤ d1 * (1 + d2 * (t + d3)) := mul_nonneg hd1 h2.le
  linarith

/-- **Level-3 antilipschitz core.**  On `(0,1]` the three-step branch expands
distances by at least `1/P(1)²`. -/
theorem mob3_anti {d1 d2 d3 x y : ℝ} (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    |x - y| / (((1 + d3) + d1 * (1 + d2 * (1 + d3))) ^ 2)
      ≤ |(1 + d2 * (x + d3)) / ((x + d3) + d1 * (1 + d2 * (x + d3)))
          - (1 + d2 * (y + d3)) / ((y + d3) + d1 * (1 + d2 * (y + d3)))| := by
  have hPx := mob3_den_pos hd1 hd2 hd3 hx0
  have hPy := mob3_den_pos hd1 hd2 hd3 hy0
  have hM := mob3_den_pos hd1 hd2 hd3 (show (0:ℝ) < 1 by norm_num)
  have hAM : (x + d3) + d1 * (1 + d2 * (x + d3))
      ≤ (1 + d3) + d1 * (1 + d2 * (1 + d3)) := by
    nlinarith [mul_nonneg (mul_nonneg hd1 hd2) (sub_nonneg.2 hx1)]
  have hBM : (y + d3) + d1 * (1 + d2 * (y + d3))
      ≤ (1 + d3) + d1 * (1 + d2 * (1 + d3)) := by
    nlinarith [mul_nonneg (mul_nonneg hd1 hd2) (sub_nonneg.2 hy1)]
  have hpos : (0 : ℝ) < ((x + d3) + d1 * (1 + d2 * (x + d3)))
      * ((y + d3) + d1 * (1 + d2 * (y + d3))) := mul_pos hPx hPy
  have hle : ((x + d3) + d1 * (1 + d2 * (x + d3)))
      * ((y + d3) + d1 * (1 + d2 * (y + d3)))
      ≤ ((1 + d3) + d1 * (1 + d2 * (1 + d3))) ^ 2 := by
    have h := mul_le_mul hAM hBM hPy.le hM.le
    nlinarith [h]
  rw [mob3_abs_diff hPx hPy]
  gcongr

/-- **Level-3 Lipschitz core.**  On `[b, ∞)` the three-step branch contracts by
`1/P(b)²`. -/
theorem mob3_lip {d1 d2 d3 b x y : ℝ} (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (hb : 0 < b) (hx : b ≤ x) (hy : b ≤ y) :
    |(1 + d2 * (x + d3)) / ((x + d3) + d1 * (1 + d2 * (x + d3)))
        - (1 + d2 * (y + d3)) / ((y + d3) + d1 * (1 + d2 * (y + d3)))|
      ≤ (1 / (((b + d3) + d1 * (1 + d2 * (b + d3))) ^ 2)) * |x - y| := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hb hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hb hy
  have hPx := mob3_den_pos hd1 hd2 hd3 hx0
  have hPy := mob3_den_pos hd1 hd2 hd3 hy0
  have hPb := mob3_den_pos hd1 hd2 hd3 hb
  have hmx : (b + d3) + d1 * (1 + d2 * (b + d3))
      ≤ (x + d3) + d1 * (1 + d2 * (x + d3)) := by
    nlinarith [mul_nonneg (mul_nonneg hd1 hd2) (sub_nonneg.2 hx)]
  have hmy : (b + d3) + d1 * (1 + d2 * (b + d3))
      ≤ (y + d3) + d1 * (1 + d2 * (y + d3)) := by
    nlinarith [mul_nonneg (mul_nonneg hd1 hd2) (sub_nonneg.2 hy)]
  have hb2 : (0 : ℝ) < ((b + d3) + d1 * (1 + d2 * (b + d3))) ^ 2 := pow_pos hPb 2
  have hge : ((b + d3) + d1 * (1 + d2 * (b + d3))) ^ 2
      ≤ ((x + d3) + d1 * (1 + d2 * (x + d3)))
        * ((y + d3) + d1 * (1 + d2 * (y + d3))) := by
    have h := mul_le_mul hmx hmy hPb.le hPx.le
    nlinarith [h]
  rw [mob3_abs_diff hPx hPy]
  calc |x - y| / (((x + d3) + d1 * (1 + d2 * (x + d3)))
        * ((y + d3) + d1 * (1 + d2 * (y + d3))))
      ≤ |x - y| / (((b + d3) + d1 * (1 + d2 * (b + d3))) ^ 2) := by gcongr
    _ = (1 / (((b + d3) + d1 * (1 + d2 * (b + d3))) ^ 2)) * |x - y| := by ring

/-- The level-3 branch is DECREASING (odd number of orientation-reversing
compositions). -/
theorem mob3_antitone {d1 d2 d3 x y : ℝ} (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (hx0 : 0 < x) (hy0 : 0 < y) (hxy : x ≤ y) :
    (1 + d2 * (y + d3)) / ((y + d3) + d1 * (1 + d2 * (y + d3)))
      ≤ (1 + d2 * (x + d3)) / ((x + d3) + d1 * (1 + d2 * (x + d3))) := by
  have hPx := mob3_den_pos hd1 hd2 hd3 hx0
  have hPy := mob3_den_pos hd1 hd2 hd3 hy0
  rw [div_le_div_iff₀ hPy hPx]
  have key : (1 + d2 * (x + d3)) * ((y + d3) + d1 * (1 + d2 * (y + d3)))
      - (1 + d2 * (y + d3)) * ((x + d3) + d1 * (1 + d2 * (x + d3))) = y - x := by ring
  linarith

/-! # §2 — the level-3 branches and their clamped inverses -/

/-- The level-3 branch: outer digit `i`, middle digit `j`, inner digit `k`. -/
noncomputable def g3 (K : ℕ) (i j k : Fin K) : ℝ → ℝ :=
  fun x => gaussIFS K i (gaussIFS K j (gaussIFS K k x))

/-- The level-3 clamped inverse branch. -/
noncomputable def x3 (K : ℕ) (i j k : Fin K) : ℝ → ℝ :=
  fun x => gpre K k (gpre K j (gpre K i x))

theorem x3_eq_x2 (K : ℕ) (i j k : Fin K) (x : ℝ) :
    x3 K i j k x = x2 K j k (gpre K i x) := rfl

/-- The exact level-3 expansion constant `a_w = 1/(C+D)² = 1/P(1)²`. -/
noncomputable def a3 (K : ℕ) (i j k : Fin K) : ℝ :=
  1 / (((1 + (((k : ℕ) : ℝ) + 1))
        + (((i : ℕ) : ℝ) + 1) * (1 + (((j : ℕ) : ℝ) + 1) * (1 + (((k : ℕ) : ℝ) + 1)))) ^ 2)

theorem a3_pos (K : ℕ) (i j k : Fin K) : 0 < a3 K i j k := by
  have h := mob3_den_pos (d1 := ((i : ℕ) : ℝ) + 1) (d2 := ((j : ℕ) : ℝ) + 1)
    (d3 := ((k : ℕ) : ℝ) + 1) (t := 1)
    (by positivity) (by positivity) (by positivity) (by norm_num)
  unfold a3
  have h2 : (0 : ℝ) < ((1 + (((k : ℕ) : ℝ) + 1))
      + (((i : ℕ) : ℝ) + 1) * (1 + (((j : ℕ) : ℝ) + 1) * (1 + (((k : ℕ) : ℝ) + 1)))) ^ 2 :=
    pow_pos h 2
  positivity

/-- **The closed Möbius form of the level-3 branch.** -/
theorem gauss_comp3_eq (K : ℕ) (i j k : Fin K) {x : ℝ} (hx : x ∈ gaussJ K) :
    g3 K i j k x
      = (1 + (((j : ℕ) : ℝ) + 1) * (x + (((k : ℕ) : ℝ) + 1)))
        / ((x + (((k : ℕ) : ℝ) + 1))
          + (((i : ℕ) : ℝ) + 1) * (1 + (((j : ℕ) : ℝ) + 1) * (x + (((k : ℕ) : ℝ) + 1)))) := by
  have hx0 : 0 < x := gaussJ_pos hx
  have hk : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu : (0 : ℝ) < x + (((k : ℕ) : ℝ) + 1) := by linarith
  show gaussIFS K i (g2 K j k x) = _
  rw [gauss_comp_eq K j k hx, gaussIFS_eq]
  exact mob3_closed (by positivity) (by positivity) hu

theorem g3_mapsTo (K : ℕ) (i j k : Fin K) :
    Set.MapsTo (g3 K i j k) (gaussJ K) (gaussJ K) :=
  fun _ hx => gauss_mapsTo K i (gauss_mapsTo K j (gauss_mapsTo K k hx))

theorem x3_cont (K : ℕ) (i j k : Fin K) : Continuous (x3 K i j k) :=
  (continuous_gpre k).comp ((continuous_gpre j).comp (continuous_gpre i))

theorem x3_at_beta (K : ℕ) (i j k : Fin K) : x3 K i j k (betaK K) = 1 := by
  unfold x3
  rw [gpre_at_beta i, gpre_at_one j, gpre_at_beta k]

theorem x3_at_one (K : ℕ) (i j k : Fin K) : x3 K i j k 1 = betaK K := by
  unfold x3
  rw [gpre_at_one i, gpre_at_beta j, gpre_at_one k]

/-- **The level-3 cylinder trichotomy.**  Composing the level-1 trichotomy with
r210's level-2 trichotomy.  The composite branches REVERSE orientation. -/
theorem x3_cyl (K : ℕ) (i j k i' j' k' : Fin K) {u : ℝ} (hu : u ∈ gaussJ K) :
    x3 K i' j' k' (g3 K i j k u)
      = if (i' : ℕ) < (i : ℕ) ∨ ((i' : ℕ) = (i : ℕ) ∧
            ((j : ℕ) < (j' : ℕ) ∨ ((j' : ℕ) = (j : ℕ) ∧ (k' : ℕ) < (k : ℕ)))) then 1
        else if (i' : ℕ) = (i : ℕ) ∧ (j' : ℕ) = (j : ℕ) ∧ (k' : ℕ) = (k : ℕ) then u
        else betaK K := by
  have hju : g2 K j k u ∈ gaussJ K := g2_mapsTo K j k hu
  show gpre K k' (gpre K j' (gpre K i' (gaussIFS K i (g2 K j k u)))) = _
  rw [gpre_on_cylinder i i' hju]
  rcases lt_trichotomy ((i' : ℕ)) ((i : ℕ)) with h | h | h
  · rw [if_pos h, gpre_at_one j', gpre_at_beta k', if_pos (Or.inl h)]
  · have hii : i' = i := Fin.ext h
    rw [if_neg (by omega), if_pos hii]
    have hx2 : gpre K k' (gpre K j' (g2 K j k u)) = x2 K j' k' (g2 K j k u) := rfl
    rw [hx2, x2_cyl K j k j' k' hu]
    have hOuter : ((i' : ℕ) < (i : ℕ) ∨ ((i' : ℕ) = (i : ℕ) ∧
          ((j : ℕ) < (j' : ℕ) ∨ ((j' : ℕ) = (j : ℕ) ∧ (k' : ℕ) < (k : ℕ)))))
        ↔ ((j : ℕ) < (j' : ℕ) ∨ ((j' : ℕ) = (j : ℕ) ∧ (k' : ℕ) < (k : ℕ))) := by
      constructor
      · rintro (hc | ⟨-, hc⟩)
        · omega
        · exact hc
      · intro hc
        exact Or.inr ⟨h, hc⟩
    have hInner : ((i' : ℕ) = (i : ℕ) ∧ (j' : ℕ) = (j : ℕ) ∧ (k' : ℕ) = (k : ℕ))
        ↔ ((j' : ℕ) = (j : ℕ) ∧ (k' : ℕ) = (k : ℕ)) := by
      constructor
      · rintro ⟨-, hc⟩
        exact hc
      · intro hc
        exact ⟨h, hc⟩
    simp only [hOuter, hInner]
  · rw [if_neg (by omega), if_neg (fun hc => absurd (congrArg Fin.val hc) (by omega)),
      gpre_at_beta j', gpre_at_one k', if_neg (by omega), if_neg (by omega)]

/-- **At most one free level-3 word.** -/
theorem x3_uniq (K : ℕ) {x : ℝ} {i j k i' j' k' : Fin K}
    (h1 : x3 K i j k x ≠ betaK K) (h2 : x3 K i j k x ≠ 1)
    (h3 : x3 K i' j' k' x ≠ betaK K) (h4 : x3 K i' j' k' x ≠ 1) :
    i = i' ∧ j = j' ∧ k = k' := by
  have key : ∀ (p q r : Fin K), x3 K p q r x ≠ betaK K → x3 K p q r x ≠ 1 →
      gfree K p x := by
    intro p q r hA hB
    by_contra hc
    rcases gpre_clamped hc with h | h
    · refine hA ?_
      rw [x3_eq_x2, h, x2_at_beta]
    · refine hB ?_
      rw [x3_eq_x2, h, x2_at_one]
  have hii : i = i' := gfree_unique (key i j k h1 h2) (key i' j' k' h3 h4)
  subst hii
  rw [x3_eq_x2] at h1 h2 h3 h4
  obtain ⟨hj, hk⟩ := x2_uniq K h1 h2 h3 h4
  exact ⟨rfl, hj, hk⟩

/-! # §3 — the level-3 metric estimates -/

/-- **Level-3 antilipschitz bound** with the EXACT three-step constant. -/
theorem g3_anti (K : ℕ) (i j k : Fin K) {x y : ℝ} (hx : x ∈ gaussJ K) (hy : y ∈ gaussJ K) :
    a3 K i j k * |x - y| ≤ |g3 K i j k x - g3 K i j k y| := by
  rw [gauss_comp3_eq K i j k hx, gauss_comp3_eq K i j k hy]
  have h := mob3_anti (d1 := ((i : ℕ) : ℝ) + 1) (d2 := ((j : ℕ) : ℝ) + 1)
    (d3 := ((k : ℕ) : ℝ) + 1) (by positivity) (by positivity) (by positivity)
    (gaussJ_pos hx) hx.2 (gaussJ_pos hy) hy.2
  unfold a3
  rw [div_mul_eq_mul_div, one_mul]
  exact h

/-- **Level-3 uniform contraction**: the cube of the level-1 constant. -/
theorem g3_lip (K : ℕ) (i j k : Fin K) {x y : ℝ} (hx : x ∈ gaussJ K) (hy : y ∈ gaussJ K) :
    |g3 K i j k x - g3 K i j k y| ≤ LmaxK K ^ 3 * |x - y| := by
  have hL : (0 : ℝ) < LmaxK K := LmaxK_pos
  have hkx : gaussIFS K k x ∈ gaussJ K := gauss_mapsTo K k hx
  have hky : gaussIFS K k y ∈ gaussJ K := gauss_mapsTo K k hy
  have h1 := gauss_lip_real i (gauss_mapsTo K j hkx) (gauss_mapsTo K j hky)
  have h2 := gauss_lip_real j hkx hky
  have h3 := gauss_lip_real k hx hy
  calc |g3 K i j k x - g3 K i j k y|
      ≤ LmaxK K * |gaussIFS K j (gaussIFS K k x) - gaussIFS K j (gaussIFS K k y)| := h1
    _ ≤ LmaxK K * (LmaxK K * |gaussIFS K k x - gaussIFS K k y|) :=
        mul_le_mul_of_nonneg_left h2 hL.le
    _ ≤ LmaxK K * (LmaxK K * (LmaxK K * |x - y|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hL.le) hL.le
    _ = LmaxK K ^ 3 * |x - y| := by ring

theorem LmaxK_cube_lt_one (K : ℕ) : LmaxK K ^ 3 < 1 :=
  pow_lt_one₀ (LmaxK_pos (K := K)).le (LmaxK_lt_one (K := K)) (by norm_num)

theorem LmaxK_cube_pos (K : ℕ) : (0 : ℝ) < LmaxK K ^ 3 := pow_pos LmaxK_pos 3

/-- Lower (LEFT) endpoint of the level-3 cylinder, attained at `x = 1`. -/
theorem g3_ge (K : ℕ) (i j k : Fin K) {x : ℝ} (hx : x ∈ gaussJ K) :
    (1 + (((j : ℕ) : ℝ) + 1) * (1 + (((k : ℕ) : ℝ) + 1)))
        / ((1 + (((k : ℕ) : ℝ) + 1))
          + (((i : ℕ) : ℝ) + 1) * (1 + (((j : ℕ) : ℝ) + 1) * (1 + (((k : ℕ) : ℝ) + 1))))
      ≤ g3 K i j k x := by
  rw [gauss_comp3_eq K i j k hx]
  exact mob3_antitone (by positivity) (by positivity) (by positivity)
    (gaussJ_pos hx) (by norm_num) hx.2

/-- Upper (RIGHT) endpoint of the level-3 cylinder, attained at `x = β`. -/
theorem g3_le (K : ℕ) (i j k : Fin K) {x : ℝ} (hx : x ∈ gaussJ K) :
    g3 K i j k x
      ≤ (1 + (((j : ℕ) : ℝ) + 1) * (betaK K + (((k : ℕ) : ℝ) + 1)))
        / ((betaK K + (((k : ℕ) : ℝ) + 1))
          + (((i : ℕ) : ℝ) + 1)
            * (1 + (((j : ℕ) : ℝ) + 1) * (betaK K + (((k : ℕ) : ℝ) + 1)))) := by
  rw [gauss_comp3_eq K i j k hx]
  exact mob3_antitone (by positivity) (by positivity) (by positivity)
    betaK_pos (gaussJ_pos hx) hx.1

/-- The **exact** level-3 Lipschitz constant on `gaussJ K`: `1/P(1/(K+1))²`. -/
noncomputable def c3 (K : ℕ) (i j k : Fin K) : ℝ≥0 :=
  1 / (((1 / ((K : ℝ≥0) + 1) + (((k : ℕ) : ℝ≥0) + 1))
        + (((i : ℕ) : ℝ≥0) + 1)
          * (1 + (((j : ℕ) : ℝ≥0) + 1)
              * (1 / ((K : ℝ≥0) + 1) + (((k : ℕ) : ℝ≥0) + 1)))) ^ 2)

theorem c3_coe (K : ℕ) (i j k : Fin K) :
    ((c3 K i j k : ℝ≥0) : ℝ)
      = 1 / (((1 / ((K : ℝ) + 1) + (((k : ℕ) : ℝ) + 1))
          + (((i : ℕ) : ℝ) + 1)
            * (1 + (((j : ℕ) : ℝ) + 1)
                * (1 / ((K : ℝ) + 1) + (((k : ℕ) : ℝ) + 1)))) ^ 2) := by
  simp [c3]

/-- **Level-3 Lipschitz estimate** on the invariant interval. -/
theorem g3_lipschitzOnWith (K : ℕ) (i j k : Fin K) :
    LipschitzOnWith (c3 K i j k) (g3 K i j k) (gaussJ K) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  rintro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, c3_coe, gauss_comp3_eq K i j k hx,
    gauss_comp3_eq K i j k hy]
  have hb : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
  exact mob3_lip (by positivity) (by positivity) (by positivity) hb hx.1 hy.1

/-! # §4 — level-3 self-covering, invariance and boundedness -/

theorem g3_selfCover {K : ℕ} {E : Set ℝ} (hself : E ⊆ ⋃ j, gaussIFS K j '' E) :
    E ⊆ ⋃ q : Fin K × Fin K × Fin K, g3 K q.1 q.2.1 q.2.2 '' E := by
  intro x hx
  obtain ⟨i, y, hyE, hxy⟩ := Set.mem_iUnion.1 (hself hx)
  obtain ⟨j, z, hzE, hyz⟩ := Set.mem_iUnion.1 (hself hyE)
  obtain ⟨k, t, htE, hzt⟩ := Set.mem_iUnion.1 (hself hzE)
  refine Set.mem_iUnion.2 ⟨(i, j, k), t, htE, ?_⟩
  show gaussIFS K i (gaussIFS K j (gaussIFS K k t)) = x
  rw [hzt, hyz]
  exact hxy

theorem g3_invariant {K : ℕ} {E : Set ℝ} (i j k : Fin K)
    (hinv : ∀ j : Fin K, Set.MapsTo (gaussIFS K j) E E) :
    Set.MapsTo (g3 K i j k) E E :=
  fun _ hx => hinv i (hinv j (hinv k hx))

theorem gaussJ_ediam_ne_top {K : ℕ} {E : Set ℝ} (hEJ : E ⊆ gaussJ K) :
    EMetric.diam E ≠ ⊤ := by
  have h : EMetric.diam E ≤ EMetric.diam (gaussJ K) := EMetric.diam_mono hEJ
  have h2 : EMetric.diam (gaussJ K) = ENNReal.ofReal (1 - 1 / ((K : ℝ) + 1)) := by
    rw [gaussJ, Real.ediam_Icc]
  rw [h2] at h
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-! # §5 — the `K = 2` level-3 system: eight words

The eight three-digit cylinders, in the fixed `AddrIFS` order
(outer index ascending, middle descending, inner ascending), with digits
`(d₁,d₂,d₃) = (i+1, j+1, k+1)`:

| `m` | `(i,j,k)` | `(d₁,d₂,d₃)` | cylinder      | `a_w`  | `b_w`    |
|-----|-----------|--------------|---------------|--------|----------|
| 0   | (0,1,0)   | (1,2,1)      | `[5/7, 11/15]`| `1/49` | `1/25`   |
| 1   | (0,1,1)   | (1,2,2)      | `[7/10,17/24]`| `1/100`| `1/64`   |
| 2   | (0,0,0)   | (1,1,1)      | `[3/5, 7/11]` | `1/25` | `9/121`  |
| 3   | (0,0,1)   | (1,1,2)      | `[4/7, 10/17]`| `1/49` | `9/289`  |
| 4   | (1,1,0)   | (2,2,1)      | `[5/12,11/26]`| `1/144`| `9/676`  |
| 5   | (1,1,1)   | (2,2,2)      | `[7/17,17/41]`| `1/289`| `9/1681` |
| 6   | (1,0,0)   | (2,1,1)      | `[3/8, 7/18]` | `1/64` | `1/36`   |
| 7   | (1,0,1)   | (2,1,2)      | `[4/11,10/27]`| `1/121`| `1/81`   |

The cylinders run RIGHT to LEFT as `m` increases (orientation reversing); the
minimal gap is `5/12 − 17/41 = 1/492`. -/

/-- Outer index of the `m`-th level-3 word, `K = 2`. -/
def wI2 : Fin 8 → Fin 2 := ![0, 0, 0, 0, 1, 1, 1, 1]

/-- Middle index of the `m`-th level-3 word, `K = 2`. -/
def wJ2 : Fin 8 → Fin 2 := ![1, 1, 0, 0, 1, 1, 0, 0]

/-- Inner index of the `m`-th level-3 word, `K = 2`. -/
def wK2 : Fin 8 → Fin 2 := ![0, 1, 0, 1, 0, 1, 0, 1]

/-- The `m`-th level-3 branch, `K = 2`. -/
noncomputable def wpsi2 : Fin 8 → ℝ → ℝ := fun m => g3 2 (wI2 m) (wJ2 m) (wK2 m)

/-- The `m`-th level-3 clamped inverse branch, `K = 2`. -/
noncomputable def wchi2 : Fin 8 → ℝ → ℝ := fun m => x3 2 (wI2 m) (wJ2 m) (wK2 m)

theorem word_ord2 (m m' : Fin 8) :
    ((wI2 m' : ℕ) < (wI2 m : ℕ) ∨ ((wI2 m' : ℕ) = (wI2 m : ℕ) ∧
        ((wJ2 m : ℕ) < (wJ2 m' : ℕ) ∨
          ((wJ2 m' : ℕ) = (wJ2 m : ℕ) ∧ (wK2 m' : ℕ) < (wK2 m : ℕ)))))
      ↔ (m' : ℕ) < (m : ℕ) := by
  revert m m'
  decide

theorem word_eq2 (m m' : Fin 8) :
    ((wI2 m' : ℕ) = (wI2 m : ℕ) ∧ (wJ2 m' : ℕ) = (wJ2 m : ℕ)
      ∧ (wK2 m' : ℕ) = (wK2 m : ℕ)) ↔ m' = m := by
  revert m m'
  decide

theorem word_inj2 (m m' : Fin 8) (h1 : wI2 m = wI2 m') (h2 : wJ2 m = wJ2 m')
    (h3 : wK2 m = wK2 m') : m = m' := by
  revert h1 h2 h3
  revert m m'
  decide

theorem word_surj2 (i j k : Fin 2) :
    ∃ m : Fin 8, wI2 m = i ∧ wJ2 m = j ∧ wK2 m = k := by
  revert i j k
  decide

theorem wchi2_cyl (m m' : Fin 8) {u : ℝ} (hu : u ∈ gaussJ 2) :
    wchi2 m' (wpsi2 m u)
      = if (m' : ℕ) < (m : ℕ) then 1 else if m' = m then u else betaK 2 := by
  show x3 2 (wI2 m') (wJ2 m') (wK2 m') (g3 2 (wI2 m) (wJ2 m) (wK2 m) u) = _
  rw [x3_cyl 2 (wI2 m) (wJ2 m) (wK2 m) (wI2 m') (wJ2 m') (wK2 m') hu]
  by_cases h1 : (m' : ℕ) < (m : ℕ)
  · rw [if_pos h1, if_pos ((word_ord2 m m').2 h1)]
  · rw [if_neg h1, if_neg (fun hc => h1 ((word_ord2 m m').1 hc))]
    by_cases h2 : m' = m
    · rw [if_pos h2, if_pos ((word_eq2 m m').2 h2)]
    · rw [if_neg h2, if_neg (fun hc => h2 ((word_eq2 m m').1 hc))]

/-- Left endpoints of the eight level-3 cylinders, `K = 2`. -/
noncomputable def wLo2 : Fin 8 → ℝ := ![5/7, 7/10, 3/5, 4/7, 5/12, 7/17, 3/8, 4/11]

/-- Right endpoints of the eight level-3 cylinders, `K = 2`. -/
noncomputable def wHi2 : Fin 8 → ℝ := ![11/15, 17/24, 7/11, 10/17, 11/26, 17/41, 7/18, 10/27]

theorem wbd2_lo (m : Fin 8) {x : ℝ} (hx : x ∈ gaussJ 2) : wLo2 m ≤ wpsi2 m x := by
  fin_cases m <;> refine le_trans ?_ (g3_ge 2 _ _ _ hx) <;> norm_num [wLo2, wI2, wJ2, wK2]

theorem wbd2_hi (m : Fin 8) {x : ℝ} (hx : x ∈ gaussJ 2) : wpsi2 m x ≤ wHi2 m := by
  fin_cases m <;> refine le_trans (g3_le 2 _ _ _ hx) ?_ <;>
    norm_num [wHi2, wI2, wJ2, wK2, betaK]

/-- The cylinders run right to left: if `m' < m` then cylinder `m` lies entirely
to the LEFT of cylinder `m'`, separated by at least `1/492`. -/
theorem wgap2 (m m' : Fin 8) (h : (m' : ℕ) < (m : ℕ)) : wHi2 m + 1/492 ≤ wLo2 m' := by
  fin_cases m <;> fin_cases m' <;>
    first
      | exact absurd h (by decide)
      | norm_num [wLo2, wHi2]

theorem wsep2 (m m' : Fin 8) (hmm : m ≠ m') {x y : ℝ}
    (hx : x ∈ gaussJ 2) (hy : y ∈ gaussJ 2) :
    (1 : ℝ)/492 ≤ |wpsi2 m x - wpsi2 m' y| := by
  have hne : (m : ℕ) ≠ (m' : ℕ) := fun hc => hmm (Fin.ext hc)
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := wbd2_lo m hx
    have h2 := wbd2_hi m' hy
    have h3 := wgap2 m' m h
    exact le_trans (by linarith) (le_abs_self (wpsi2 m x - wpsi2 m' y))
  · have h1 := wbd2_hi m hx
    have h2 := wbd2_lo m' hy
    have h3 := wgap2 m m' h
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self (wpsi2 m' y - wpsi2 m x))

/-- The eight level-3 antilipschitz constants, `K = 2`. -/
noncomputable def wav2 : Fin 8 → ℝ := ![1/49, 1/100, 1/25, 1/49, 1/144, 1/289, 1/64, 1/121]

theorem a3_val2 (m : Fin 8) : a3 2 (wI2 m) (wJ2 m) (wK2 m) = wav2 m := by
  fin_cases m <;> norm_num [a3, wI2, wJ2, wK2, wav2]

/-- **The `K = 2` level-3 system as an `AddrIFS`.**  Eight words, orientation
REVERSING (`flip = true`), separation `1/492`, weights summing to exactly `1`.

The weight vector is r211's verified level-3 Bernoulli vector, permuted into the
`AddrIFS` word order documented in §5. -/
noncomputable def gaussThree2 : AddrIFS 8 where
  lo := betaK 2
  hi := 1
  ψ := wpsi2
  χ := wchi2
  flip := true
  a := fun m => a3 2 (wI2 m) (wJ2 m) (wK2 m)
  p := ![15056/100000, 10690/100000, 20801/100000, 15056/100000,
        8974/100000, 6423/100000, 13244/100000, 9756/100000]
  c := 20801/100000
  L := LmaxK 2 ^ 3
  γ := 1/492
  lo_lt_hi := betaK_lt_one (by norm_num)
  diam_lt_one := by have := betaK_pos (K := 2); linarith
  p_pos := by intro m; fin_cases m <;> norm_num
  p_sum := by norm_num [Fin.sum_univ_succ]
  p_le_c := by intro m; fin_cases m <;> norm_num
  c_lt_one := by norm_num
  a_pos := fun m => a3_pos 2 _ _ _
  gamma_pos := by norm_num
  L_pos := LmaxK_cube_pos 2
  L_lt_one := LmaxK_cube_lt_one 2
  anti := by intro m x y hx hy; exact g3_anti 2 (wI2 m) (wJ2 m) (wK2 m) hx hy
  lip := by intro m x y hx hy; exact g3_lip 2 (wI2 m) (wJ2 m) (wK2 m) hx hy
  sep := by intro m m' hmm x y hx hy; exact wsep2 m m' hmm hx hy
  chi_cont := fun m => x3_cont 2 _ _ _
  chi_lo := fun m => by simpa using x3_at_beta 2 (wI2 m) (wJ2 m) (wK2 m)
  chi_hi := fun m => by simpa using x3_at_one 2 (wI2 m) (wJ2 m) (wK2 m)
  chi_cyl := by intro m m' u hu; exact wchi2_cyl m m' hu
  chi_uniq := by
    intro x m m' h1 h2 h3 h4
    obtain ⟨hI, hJ, hK⟩ := x3_uniq 2 h1 h2 h3 h4
    exact word_inj2 m m' hI hJ hK

/-- The eight weight/expansion comparisons at `s = 12/25`, certified by exact
integer arithmetic through `le_rpow_of_pow_le`. -/
theorem wp2_le_rpow (m : Fin 8) : gaussThree2.p m ≤ gaussThree2.a m ^ ((12 : ℝ) / 25) := by
  have hA : gaussThree2.a m = wav2 m := a3_val2 m
  rw [hA]
  fin_cases m
  · show (15056/100000 : ℝ) ≤ (1/49 : ℝ) ^ ((12 : ℝ) / 25)
    exact le_rpow_of_pow_le (x := (1/49 : ℝ)) (u := (15056/100000 : ℝ))
      (pn := 12) (q := 25) (by norm_num) (by norm_num) (by norm_num)
  · show (10690/100000 : ℝ) ≤ (1/100 : ℝ) ^ ((12 : ℝ) / 25)
    exact le_rpow_of_pow_le (x := (1/100 : ℝ)) (u := (10690/100000 : ℝ))
      (pn := 12) (q := 25) (by norm_num) (by norm_num) (by norm_num)
  · show (20801/100000 : ℝ) ≤ (1/25 : ℝ) ^ ((12 : ℝ) / 25)
    exact le_rpow_of_pow_le (x := (1/25 : ℝ)) (u := (20801/100000 : ℝ))
      (pn := 12) (q := 25) (by norm_num) (by norm_num) (by norm_num)
  · show (15056/100000 : ℝ) ≤ (1/49 : ℝ) ^ ((12 : ℝ) / 25)
    exact le_rpow_of_pow_le (x := (1/49 : ℝ)) (u := (15056/100000 : ℝ))
      (pn := 12) (q := 25) (by norm_num) (by norm_num) (by norm_num)
  · show (8974/100000 : ℝ) ≤ (1/144 : ℝ) ^ ((12 : ℝ) / 25)
    exact le_rpow_of_pow_le (x := (1/144 : ℝ)) (u := (8974/100000 : ℝ))
      (pn := 12) (q := 25) (by norm_num) (by norm_num) (by norm_num)
  · show (6423/100000 : ℝ) ≤ (1/289 : ℝ) ^ ((12 : ℝ) / 25)
    exact le_rpow_of_pow_le (x := (1/289 : ℝ)) (u := (6423/100000 : ℝ))
      (pn := 12) (q := 25) (by norm_num) (by norm_num) (by norm_num)
  · show (13244/100000 : ℝ) ≤ (1/64 : ℝ) ^ ((12 : ℝ) / 25)
    exact le_rpow_of_pow_le (x := (1/64 : ℝ)) (u := (13244/100000 : ℝ))
      (pn := 12) (q := 25) (by norm_num) (by norm_num) (by norm_num)
  · show (9756/100000 : ℝ) ≤ (1/121 : ℝ) ^ ((12 : ℝ) / 25)
    exact le_rpow_of_pow_le (x := (1/121 : ℝ)) (u := (9756/100000 : ℝ))
      (pn := 12) (q := 25) (by norm_num) (by norm_num) (by norm_num)

theorem wselfCover2 {E : Set ℝ} (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E) :
    E ⊆ ⋃ m : Fin 8, wpsi2 m '' E := by
  intro x hx
  obtain ⟨q, z, hzE, hz⟩ := Set.mem_iUnion.1 (g3_selfCover hself hx)
  obtain ⟨m, h1, h2, h3⟩ := word_surj2 q.1 q.2.1 q.2.2
  refine Set.mem_iUnion.2 ⟨m, z, hzE, ?_⟩
  show g3 2 (wI2 m) (wJ2 m) (wK2 m) z = x
  rw [h1, h2, h3]
  exact hz

/-- **LEVEL-3 LOWER BOUND, `K = 2`.**  Any nonempty closed `E ⊆ [1/3, 1]` which
is forward invariant and backward covered by the two Gauss branches has
`dim_H E ≥ 0.48`.

Improves r210's `0.46`.  The level-3 inf-Moran root is `0.4860785…`; the true
value is `0.5312805…`. -/
theorem le_dimH_gauss_two_level_three {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2) (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 2, Set.MapsTo (gaussIFS 2 j) E E) :
    ENNReal.ofReal ((12 : ℝ) / 25) ≤ dimH E := by
  refine gaussThree2.le_dimH (by norm_num) hEJ (wselfCover2 hself) hne hclosed ?_ wp2_le_rpow
  intro m
  exact g3_invariant (wI2 m) (wJ2 m) (wK2 m) hinv

/-! ## §6 — the `K = 2` level-3 UPPER bound, exponent `9/16 = 0.5625` -/

/-- The eight level-3 Lipschitz constants, `K = 2`. -/
noncomputable def wcv2 : Fin 8 → ℝ≥0 :=
  ![1/25, 1/64, 9/121, 9/289, 9/676, 9/1681, 1/36, 1/81]

theorem c3_val2 (m : Fin 8) : c3 2 (wI2 m) (wJ2 m) (wK2 m) = wcv2 m := by
  fin_cases m <;> norm_num [c3, wI2, wJ2, wK2, wcv2]

theorem wcv2_lt_one (m : Fin 8) : wcv2 m < 1 := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_one]
  fin_cases m <;> norm_num [wcv2]

theorem wcv2_lipschitzOnWith (m : Fin 8) :
    LipschitzOnWith (wcv2 m) (wpsi2 m) (gaussJ 2) := by
  rw [← c3_val2 m]
  exact g3_lipschitzOnWith 2 (wI2 m) (wJ2 m) (wK2 m)

/-- Certified rational upper bounds for the eight `9/16`-powers. -/
noncomputable def wub2 : Fin 8 → ℝ≥0 :=
  ![16356/100000, 9639/100000, 23185/100000, 14208/100000,
    8809/100000, 5277/100000, 13323/100000, 8443/100000]

/-- The eight `9/16`-powers sum to at most `99240/100000 ≤ 1`. -/
theorem sum_wcv2_rpow_le_one :
    (∑ m : Fin 8, wcv2 m ^ ((9 : ℝ) / 16)) ≤ (1 : ℝ≥0) := by
  have e0 : ((1 : ℝ≥0) / 25) ^ ((9 : ℝ) / 16) ≤ 16356 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 9) (q := 16) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e1 : ((1 : ℝ≥0) / 64) ^ ((9 : ℝ) / 16) ≤ 9639 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 9) (q := 16) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e2 : ((9 : ℝ≥0) / 121) ^ ((9 : ℝ) / 16) ≤ 23185 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 9) (q := 16) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e3 : ((9 : ℝ≥0) / 289) ^ ((9 : ℝ) / 16) ≤ 14208 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 9) (q := 16) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e4 : ((9 : ℝ≥0) / 676) ^ ((9 : ℝ) / 16) ≤ 8809 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 9) (q := 16) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e5 : ((9 : ℝ≥0) / 1681) ^ ((9 : ℝ) / 16) ≤ 5277 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 9) (q := 16) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e6 : ((1 : ℝ≥0) / 36) ^ ((9 : ℝ) / 16) ≤ 13323 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 9) (q := 16) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e7 : ((1 : ℝ≥0) / 81) ^ ((9 : ℝ) / 16) ≤ 8443 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 9) (q := 16) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have hb : ∀ m : Fin 8, wcv2 m ^ ((9 : ℝ) / 16) ≤ wub2 m := by
    intro m
    fin_cases m
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
  refine le_trans (Finset.sum_le_sum fun m _ => hb m) ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_sum]
  norm_num [Fin.sum_univ_succ, wub2]

/-- **LEVEL-3 UPPER BOUND, `K = 2`.**  `dim_H E ≤ 9/16 = 0.5625`, improving
r210's `4/7 = 0.5714…`.  The level-3 sup-Moran root is `0.5603435…`; the true
value is `0.5312805…`, and `0.5625` is **not** an approximation to it. -/
theorem dimH_gauss_two_le_three {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2) (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E) :
    dimH E ≤ (9 / 16 : ℝ≥0∞) := by
  have hd : (((9 / 16 : ℝ≥0)) : ℝ) = (9 : ℝ) / 16 := by push_cast; norm_num
  have hcast : (∑ m : Fin 8, (wcv2 m : ℝ≥0∞) ^ (((9 / 16 : ℝ≥0)) : ℝ))
      = ((∑ m : Fin 8, wcv2 m ^ ((9 : ℝ) / 16) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_finset_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hd, ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0 : ℝ) ≤ 9 / 16)]
  have hsum : (∑ m : Fin 8, (wcv2 m : ℝ≥0∞) ^ (((9 / 16 : ℝ≥0)) : ℝ)) ≤ 1 := by
    rw [hcast]
    exact_mod_cast sum_wcv2_rpow_le_one
  have h := dimH_le_of_selfCover (S := gaussJ 2) (φ := wpsi2) (L := wcv2)
    (d := (9 / 16 : ℝ≥0)) hEJ (gaussJ_ediam_ne_top hEJ)
    (fun m => g3_mapsTo 2 _ _ _) (wselfCover2 hself)
    wcv2_lipschitzOnWith wcv2_lt_one hsum
  refine h.trans ?_
  norm_num

/-- **LEVEL-3 ENCLOSURE, `K = 2`.**  `0.48 ≤ dim_H E ≤ 0.5625`.

Improves r210's `[0.46, 0.5715]` by about `0.029` in width.  TRUE value
`0.5312805…` (Jenkinson–Pollicott).  Neither endpoint is an approximation to
it; the gap narrows but is NOT closed. -/
theorem dimH_gauss_two_enclosure_three {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2) (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 2, Set.MapsTo (gaussIFS 2 j) E E) :
    ENNReal.ofReal ((12 : ℝ) / 25) ≤ dimH E ∧ dimH E ≤ (9 / 16 : ℝ≥0∞) :=
  ⟨le_dimH_gauss_two_level_three hEJ hself hne hclosed hinv,
    dimH_gauss_two_le_three hEJ hself⟩

/-! ## Axiom audit — general layer and `K = 2` -/

#print axioms mob3_abs_diff
#print axioms mob3_anti
#print axioms mob3_lip
#print axioms mob3_antitone
#print axioms gauss_comp3_eq
#print axioms x3_cyl
#print axioms x3_uniq
#print axioms g3_anti
#print axioms g3_lip
#print axioms g3_ge
#print axioms g3_le
#print axioms g3_lipschitzOnWith
#print axioms g3_selfCover
#print axioms wchi2_cyl
#print axioms wsep2
#print axioms gaussThree2
#print axioms wp2_le_rpow
#print axioms le_dimH_gauss_two_level_three
#print axioms sum_wcv2_rpow_le_one
#print axioms dimH_gauss_two_le_three
#print axioms dimH_gauss_two_enclosure_three


/-! # §7 — the `K = 3` level-3 system: twenty-seven words

The twenty-seven three-digit cylinders, in the fixed `AddrIFS` order (outer
index ASCENDING, middle DESCENDING, inner ASCENDING), digits
`(d₁,d₂,d₃) = (i+1, j+1, k+1)`:

```
m =  0  (i,j,k) = (0, 2, 0)  (d1,d2,d3) = (1,3,1)  cyl = [7/9, 19/24]  a = 1/81  b = 1/36
m =  1  (i,j,k) = (0, 2, 1)  (d1,d2,d3) = (1,3,2)  cyl = [10/13, 31/40]  a = 1/169  b = 1/100
m =  2  (i,j,k) = (0, 2, 2)  (d1,d2,d3) = (1,3,3)  cyl = [13/17, 43/56]  a = 1/289  b = 1/196
m =  3  (i,j,k) = (0, 1, 0)  (d1,d2,d3) = (1,2,1)  cyl = [5/7, 14/19]  a = 1/49  b = 16/361
m =  4  (i,j,k) = (0, 1, 1)  (d1,d2,d3) = (1,2,2)  cyl = [7/10, 22/31]  a = 1/100  b = 16/961
m =  5  (i,j,k) = (0, 1, 2)  (d1,d2,d3) = (1,2,3)  cyl = [9/13, 30/43]  a = 1/169  b = 16/1849
m =  6  (i,j,k) = (0, 0, 0)  (d1,d2,d3) = (1,1,1)  cyl = [3/5, 9/14]  a = 1/25  b = 4/49
m =  7  (i,j,k) = (0, 0, 1)  (d1,d2,d3) = (1,1,2)  cyl = [4/7, 13/22]  a = 1/49  b = 4/121
m =  8  (i,j,k) = (0, 0, 2)  (d1,d2,d3) = (1,1,3)  cyl = [5/9, 17/30]  a = 1/81  b = 4/225
m =  9  (i,j,k) = (1, 2, 0)  (d1,d2,d3) = (2,3,1)  cyl = [7/16, 19/43]  a = 1/256  b = 16/1849
m = 10  (i,j,k) = (1, 2, 1)  (d1,d2,d3) = (2,3,2)  cyl = [10/23, 31/71]  a = 1/529  b = 16/5041
m = 11  (i,j,k) = (1, 2, 2)  (d1,d2,d3) = (2,3,3)  cyl = [13/30, 43/99]  a = 1/900  b = 16/9801
m = 12  (i,j,k) = (1, 1, 0)  (d1,d2,d3) = (2,2,1)  cyl = [5/12, 14/33]  a = 1/144  b = 16/1089
m = 13  (i,j,k) = (1, 1, 1)  (d1,d2,d3) = (2,2,2)  cyl = [7/17, 22/53]  a = 1/289  b = 16/2809
m = 14  (i,j,k) = (1, 1, 2)  (d1,d2,d3) = (2,2,3)  cyl = [9/22, 30/73]  a = 1/484  b = 16/5329
m = 15  (i,j,k) = (1, 0, 0)  (d1,d2,d3) = (2,1,1)  cyl = [3/8, 9/23]  a = 1/64  b = 16/529
m = 16  (i,j,k) = (1, 0, 1)  (d1,d2,d3) = (2,1,2)  cyl = [4/11, 13/35]  a = 1/121  b = 16/1225
m = 17  (i,j,k) = (1, 0, 2)  (d1,d2,d3) = (2,1,3)  cyl = [5/14, 17/47]  a = 1/196  b = 16/2209
m = 18  (i,j,k) = (2, 2, 0)  (d1,d2,d3) = (3,3,1)  cyl = [7/23, 19/62]  a = 1/529  b = 4/961
m = 19  (i,j,k) = (2, 2, 1)  (d1,d2,d3) = (3,3,2)  cyl = [10/33, 31/102]  a = 1/1089  b = 4/2601
m = 20  (i,j,k) = (2, 2, 2)  (d1,d2,d3) = (3,3,3)  cyl = [13/43, 43/142]  a = 1/1849  b = 4/5041
m = 21  (i,j,k) = (2, 1, 0)  (d1,d2,d3) = (3,2,1)  cyl = [5/17, 14/47]  a = 1/289  b = 16/2209
m = 22  (i,j,k) = (2, 1, 1)  (d1,d2,d3) = (3,2,2)  cyl = [7/24, 22/75]  a = 1/576  b = 16/5625
m = 23  (i,j,k) = (2, 1, 2)  (d1,d2,d3) = (3,2,3)  cyl = [9/31, 30/103]  a = 1/961  b = 16/10609
m = 24  (i,j,k) = (2, 0, 0)  (d1,d2,d3) = (3,1,1)  cyl = [3/11, 9/32]  a = 1/121  b = 1/64
m = 25  (i,j,k) = (2, 0, 1)  (d1,d2,d3) = (3,1,2)  cyl = [4/15, 13/48]  a = 1/225  b = 1/144
m = 26  (i,j,k) = (2, 0, 2)  (d1,d2,d3) = (3,1,3)  cyl = [5/19, 17/64]  a = 1/361  b = 1/256
```

The cylinders run RIGHT to LEFT as `m` increases (orientation reversing); the
minimal gap is `5/12 − 43/99 = 1/4686`. -/

/-- Outer index of the `m`-th level-3 word, `K = 3`. -/
def wI3 : Fin 27 → Fin 3 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2]

/-- Middle index of the `m`-th level-3 word, `K = 3`. -/
def wJ3 : Fin 27 → Fin 3 := ![2, 2, 2, 1, 1, 1, 0, 0, 0, 2, 2, 2, 1, 1, 1, 0, 0, 0, 2, 2, 2, 1, 1, 1, 0, 0, 0]

/-- Inner index of the `m`-th level-3 word, `K = 3`. -/
def wK3 : Fin 27 → Fin 3 := ![0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2]

/-- The `m`-th level-3 branch, `K = 3`. -/
noncomputable def wpsi3 : Fin 27 → ℝ → ℝ := fun m => g3 3 (wI3 m) (wJ3 m) (wK3 m)

/-- The `m`-th level-3 clamped inverse branch, `K = 3`. -/
noncomputable def wchi3 : Fin 27 → ℝ → ℝ := fun m => x3 3 (wI3 m) (wJ3 m) (wK3 m)

theorem word_ord3 (m m' : Fin 27) :
    ((wI3 m' : ℕ) < (wI3 m : ℕ) ∨ ((wI3 m' : ℕ) = (wI3 m : ℕ) ∧
        ((wJ3 m : ℕ) < (wJ3 m' : ℕ) ∨
          ((wJ3 m' : ℕ) = (wJ3 m : ℕ) ∧ (wK3 m' : ℕ) < (wK3 m : ℕ)))))
      ↔ (m' : ℕ) < (m : ℕ) := by
  revert m m'
  decide

theorem word_eq3 (m m' : Fin 27) :
    ((wI3 m' : ℕ) = (wI3 m : ℕ) ∧ (wJ3 m' : ℕ) = (wJ3 m : ℕ)
      ∧ (wK3 m' : ℕ) = (wK3 m : ℕ)) ↔ m' = m := by
  revert m m'
  decide

theorem word_inj3 (m m' : Fin 27) (h1 : wI3 m = wI3 m') (h2 : wJ3 m = wJ3 m')
    (h3 : wK3 m = wK3 m') : m = m' := by
  revert h1 h2 h3
  revert m m'
  decide

theorem word_surj3 (i j k : Fin 3) :
    ∃ m : Fin 27, wI3 m = i ∧ wJ3 m = j ∧ wK3 m = k := by
  revert i j k
  decide

theorem wchi3_cyl (m m' : Fin 27) {u : ℝ} (hu : u ∈ gaussJ 3) :
    wchi3 m' (wpsi3 m u)
      = if (m' : ℕ) < (m : ℕ) then 1 else if m' = m then u else betaK 3 := by
  show x3 3 (wI3 m') (wJ3 m') (wK3 m') (g3 3 (wI3 m) (wJ3 m) (wK3 m) u) = _
  rw [x3_cyl 3 (wI3 m) (wJ3 m) (wK3 m) (wI3 m') (wJ3 m') (wK3 m') hu]
  by_cases h1 : (m' : ℕ) < (m : ℕ)
  · rw [if_pos h1, if_pos ((word_ord3 m m').2 h1)]
  · rw [if_neg h1, if_neg (fun hc => h1 ((word_ord3 m m').1 hc))]
    by_cases h2 : m' = m
    · rw [if_pos h2, if_pos ((word_eq3 m m').2 h2)]
    · rw [if_neg h2, if_neg (fun hc => h2 ((word_eq3 m m').1 hc))]

/-- Left endpoints of the twenty-seven level-3 cylinders, `K = 3`. -/
noncomputable def wLo3 : Fin 27 → ℝ :=
  ![7/9, 10/13, 13/17, 5/7, 7/10, 9/13, 3/5, 4/7, 5/9, 7/16, 10/23, 13/30, 5/12, 7/17, 9/22, 3/8, 4/11, 5/14, 7/23, 10/33, 13/43, 5/17, 7/24, 9/31, 3/11, 4/15, 5/19]

/-- Right endpoints of the twenty-seven level-3 cylinders, `K = 3`. -/
noncomputable def wHi3 : Fin 27 → ℝ :=
  ![19/24, 31/40, 43/56, 14/19, 22/31, 30/43, 9/14, 13/22, 17/30, 19/43, 31/71, 43/99, 14/33, 22/53, 30/73, 9/23, 13/35, 17/47, 19/62, 31/102, 43/142, 14/47, 22/75, 30/103, 9/32, 13/48, 17/64]

theorem wbd3_lo (m : Fin 27) {x : ℝ} (hx : x ∈ gaussJ 3) : wLo3 m ≤ wpsi3 m x := by
  fin_cases m <;> refine le_trans ?_ (g3_ge 3 _ _ _ hx) <;> norm_num [wLo3, wI3, wJ3, wK3]

theorem wbd3_hi (m : Fin 27) {x : ℝ} (hx : x ∈ gaussJ 3) : wpsi3 m x ≤ wHi3 m := by
  fin_cases m <;> refine le_trans (g3_le 3 _ _ _ hx) ?_ <;>
    norm_num [wHi3, wI3, wJ3, wK3, betaK]

/-- The cylinders run right to left: if `m' < m` then cylinder `m` lies entirely
to the LEFT of cylinder `m'`, separated by at least `1/4686`. -/
theorem wgap3 (m m' : Fin 27) (h : (m' : ℕ) < (m : ℕ)) : wHi3 m + 1/4686 ≤ wLo3 m' := by
  fin_cases m <;> fin_cases m' <;>
    first
      | exact absurd h (by decide)
      | norm_num [wLo3, wHi3]

theorem wsep3 (m m' : Fin 27) (hmm : m ≠ m') {x y : ℝ}
    (hx : x ∈ gaussJ 3) (hy : y ∈ gaussJ 3) :
    (1 : ℝ)/4686 ≤ |wpsi3 m x - wpsi3 m' y| := by
  have hne : (m : ℕ) ≠ (m' : ℕ) := fun hc => hmm (Fin.ext hc)
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := wbd3_lo m hx
    have h2 := wbd3_hi m' hy
    have h3 := wgap3 m' m h
    exact le_trans (by linarith) (le_abs_self (wpsi3 m x - wpsi3 m' y))
  · have h1 := wbd3_hi m hx
    have h2 := wbd3_lo m' hy
    have h3 := wgap3 m m' h
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self (wpsi3 m' y - wpsi3 m x))

/-- The twenty-seven level-3 antilipschitz constants, `K = 3`. -/
noncomputable def wav3 : Fin 27 → ℝ :=
  ![1/81, 1/169, 1/289, 1/49, 1/100, 1/169, 1/25, 1/49, 1/81, 1/256, 1/529, 1/900, 1/144, 1/289, 1/484, 1/64, 1/121, 1/196, 1/529, 1/1089, 1/1849, 1/289, 1/576, 1/961, 1/121, 1/225, 1/361]

theorem a3_val3 (m : Fin 27) : a3 3 (wI3 m) (wJ3 m) (wK3 m) = wav3 m := by
  fin_cases m <;> norm_num [a3, wI3, wJ3, wK3, wav3]

/-- **The `K = 3` level-3 system as an `AddrIFS`.**  Twenty-seven words,
orientation REVERSING (`flip = true`), separation `1/4686`, weights summing to
exactly `1`.

The weights were computed as `p_w = ⌊(a_w^s / Z)·10⁵⌋/10⁵` at `s = 13/20` with
`Z = ∑ a_w^s = 1.0101959…`, then the shortfall `13·10⁻⁵` was pushed into terms
with headroom below `a_w^s`; both `∑ p_w = 1` exactly and `p_w ≤ a_w^s`
termwise were verified in exact rational arithmetic and are re-certified in Lean
by `wp3_le_rpow` / the `p_sum` field. -/
noncomputable def gaussThree3 : AddrIFS 27 where
  lo := betaK 3
  hi := 1
  ψ := wpsi3
  χ := wchi3
  flip := true
  a := fun m => a3 3 (wI3 m) (wJ3 m) (wK3 m)
  p := ![5689/100000, 3527/100000, 2488/100000, 7888/100000,
        4961/100000, 3527/100000, 12229/100000, 7888/100000,
        5689/100000, 2693/100000, 1680/100000, 1189/100000,
        3914/100000, 2488/100000, 1780/100000, 6630/100000,
        4383/100000, 3203/100000, 1680/100000, 1050/100000,
        744/100000, 2488/100000, 1589/100000, 1139/100000,
        4383/100000, 2928/100000, 2153/100000]
  c := 12229/100000
  L := LmaxK 3 ^ 3
  γ := 1/4686
  lo_lt_hi := betaK_lt_one (by norm_num)
  diam_lt_one := by have := betaK_pos (K := 3); linarith
  p_pos := by intro m; fin_cases m <;> norm_num
  p_sum := by norm_num [Fin.sum_univ_succ]
  p_le_c := by intro m; fin_cases m <;> norm_num
  c_lt_one := by norm_num
  a_pos := fun m => a3_pos 3 _ _ _
  gamma_pos := by norm_num
  L_pos := LmaxK_cube_pos 3
  L_lt_one := LmaxK_cube_lt_one 3
  anti := by intro m x y hx hy; exact g3_anti 3 (wI3 m) (wJ3 m) (wK3 m) hx hy
  lip := by intro m x y hx hy; exact g3_lip 3 (wI3 m) (wJ3 m) (wK3 m) hx hy
  sep := by intro m m' hmm x y hx hy; exact wsep3 m m' hmm hx hy
  chi_cont := fun m => x3_cont 3 _ _ _
  chi_lo := fun m => by simpa using x3_at_beta 3 (wI3 m) (wJ3 m) (wK3 m)
  chi_hi := fun m => by simpa using x3_at_one 3 (wI3 m) (wJ3 m) (wK3 m)
  chi_cyl := by intro m m' u hu; exact wchi3_cyl m m' hu
  chi_uniq := by
    intro x m m' h1 h2 h3 h4
    obtain ⟨hI, hJ, hK⟩ := x3_uniq 3 h1 h2 h3 h4
    exact word_inj3 m m' hI hJ hK

/-- The twenty-seven weight/expansion comparisons at `s = 13/20`, certified by
exact integer arithmetic through `le_rpow_of_pow_le`. -/
theorem wp3_le_rpow (m : Fin 27) : gaussThree3.p m ≤ gaussThree3.a m ^ ((13 : ℝ) / 20) := by
  have hA : gaussThree3.a m = wav3 m := a3_val3 m
  rw [hA]
  fin_cases m
  · show (5689/100000 : ℝ) ≤ (1/81 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/81 : ℝ)) (u := (5689/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (3527/100000 : ℝ) ≤ (1/169 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/169 : ℝ)) (u := (3527/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (2488/100000 : ℝ) ≤ (1/289 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/289 : ℝ)) (u := (2488/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (7888/100000 : ℝ) ≤ (1/49 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/49 : ℝ)) (u := (7888/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (4961/100000 : ℝ) ≤ (1/100 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/100 : ℝ)) (u := (4961/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (3527/100000 : ℝ) ≤ (1/169 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/169 : ℝ)) (u := (3527/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (12229/100000 : ℝ) ≤ (1/25 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/25 : ℝ)) (u := (12229/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (7888/100000 : ℝ) ≤ (1/49 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/49 : ℝ)) (u := (7888/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (5689/100000 : ℝ) ≤ (1/81 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/81 : ℝ)) (u := (5689/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (2693/100000 : ℝ) ≤ (1/256 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/256 : ℝ)) (u := (2693/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (1680/100000 : ℝ) ≤ (1/529 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/529 : ℝ)) (u := (1680/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (1189/100000 : ℝ) ≤ (1/900 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/900 : ℝ)) (u := (1189/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (3914/100000 : ℝ) ≤ (1/144 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/144 : ℝ)) (u := (3914/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (2488/100000 : ℝ) ≤ (1/289 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/289 : ℝ)) (u := (2488/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (1780/100000 : ℝ) ≤ (1/484 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/484 : ℝ)) (u := (1780/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (6630/100000 : ℝ) ≤ (1/64 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/64 : ℝ)) (u := (6630/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (4383/100000 : ℝ) ≤ (1/121 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/121 : ℝ)) (u := (4383/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (3203/100000 : ℝ) ≤ (1/196 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/196 : ℝ)) (u := (3203/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (1680/100000 : ℝ) ≤ (1/529 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/529 : ℝ)) (u := (1680/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (1050/100000 : ℝ) ≤ (1/1089 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/1089 : ℝ)) (u := (1050/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (744/100000 : ℝ) ≤ (1/1849 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/1849 : ℝ)) (u := (744/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (2488/100000 : ℝ) ≤ (1/289 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/289 : ℝ)) (u := (2488/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (1589/100000 : ℝ) ≤ (1/576 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/576 : ℝ)) (u := (1589/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (1139/100000 : ℝ) ≤ (1/961 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/961 : ℝ)) (u := (1139/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (4383/100000 : ℝ) ≤ (1/121 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/121 : ℝ)) (u := (4383/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (2928/100000 : ℝ) ≤ (1/225 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/225 : ℝ)) (u := (2928/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)
  · show (2153/100000 : ℝ) ≤ (1/361 : ℝ) ^ ((13 : ℝ) / 20)
    exact le_rpow_of_pow_le (x := (1/361 : ℝ)) (u := (2153/100000 : ℝ))
      (pn := 13) (q := 20) (by norm_num) (by norm_num) (by norm_num)

theorem wselfCover3 {E : Set ℝ} (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E) :
    E ⊆ ⋃ m : Fin 27, wpsi3 m '' E := by
  intro x hx
  obtain ⟨q, z, hzE, hz⟩ := Set.mem_iUnion.1 (g3_selfCover hself hx)
  obtain ⟨m, h1, h2, h3⟩ := word_surj3 q.1 q.2.1 q.2.2
  refine Set.mem_iUnion.2 ⟨m, z, hzE, ?_⟩
  show g3 3 (wI3 m) (wJ3 m) (wK3 m) z = x
  rw [h1, h2, h3]
  exact hz

/-- **LEVEL-3 LOWER BOUND, `K = 3`.**  Any nonempty closed `E ⊆ [1/4, 1]` which
is forward invariant and backward covered by the three Gauss branches has
`dim_H E ≥ 0.65`.

Improves r210's `0.63`.  The level-3 inf-Moran root is `0.6521470…`; the true
value is `0.7056609…`. -/
theorem le_dimH_gauss_three_level_three {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3) (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 3, Set.MapsTo (gaussIFS 3 j) E E) :
    ENNReal.ofReal ((13 : ℝ) / 20) ≤ dimH E := by
  refine gaussThree3.le_dimH (by norm_num) hEJ (wselfCover3 hself) hne hclosed ?_ wp3_le_rpow
  intro m
  exact g3_invariant (wI3 m) (wJ3 m) (wK3 m) hinv

/-! ## §8 — the `K = 3` level-3 UPPER bound, exponent `3/4` -/

/-- The twenty-seven level-3 Lipschitz constants, `K = 3`. -/
noncomputable def wcv3 : Fin 27 → ℝ≥0 :=
  ![1/36, 1/100, 1/196, 16/361, 16/961,
    16/1849, 4/49, 4/121, 4/225, 16/1849,
    16/5041, 16/9801, 16/1089, 16/2809, 16/5329,
    16/529, 16/1225, 16/2209, 4/961, 4/2601,
    4/5041, 16/2209, 16/5625, 16/10609, 1/64,
    1/144, 1/256]

/-- Certified rational upper bounds for the twenty-seven `3/4`-powers. -/
noncomputable def wub3 : Fin 27 → ℝ≥0 :=
  ![6805/100000, 3163/100000, 1910/100000, 9660/100000,
    4635/100000, 2838/100000, 15273/100000, 7753/100000,
    4869/100000, 2838/100000, 1338/100000, 813/100000,
    4221/100000, 2074/100000, 1283/100000, 7253/100000,
    3864/100000, 2483/100000, 1639/100000, 777/100000,
    473/100000, 2483/100000, 1232/100000, 766/100000,
    4420/100000, 2406/100000, 1563/100000]

theorem c3_val3 (m : Fin 27) : c3 3 (wI3 m) (wJ3 m) (wK3 m) = wcv3 m := by
  fin_cases m <;> norm_num [c3, wI3, wJ3, wK3, wcv3]

theorem wcv3_lt_one (m : Fin 27) : wcv3 m < 1 := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_one]
  fin_cases m <;> norm_num [wcv3]

theorem wcv3_lipschitzOnWith (m : Fin 27) :
    LipschitzOnWith (wcv3 m) (wpsi3 m) (gaussJ 3) := by
  rw [← c3_val3 m]
  exact g3_lipschitzOnWith 3 (wI3 m) (wJ3 m) (wK3 m)

/-- The twenty-seven `3/4`-powers sum to at most `98832/100000 ≤ 1`. -/
theorem sum_wcv3_rpow_le_one :
    (∑ m : Fin 27, wcv3 m ^ ((3 : ℝ) / 4)) ≤ (1 : ℝ≥0) := by
  have hb : ∀ m : Fin 27, wcv3 m ^ ((3 : ℝ) / 4) ≤ wub3 m := by
    intro m
    fin_cases m
    · exact nnreal_rpow_le_of_pow_le (x := ((1/36 : ℝ≥0))) (u := (6805/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((1/100 : ℝ≥0))) (u := (3163/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((1/196 : ℝ≥0))) (u := (1910/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/361 : ℝ≥0))) (u := (9660/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/961 : ℝ≥0))) (u := (4635/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/1849 : ℝ≥0))) (u := (2838/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((4/49 : ℝ≥0))) (u := (15273/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((4/121 : ℝ≥0))) (u := (7753/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((4/225 : ℝ≥0))) (u := (4869/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/1849 : ℝ≥0))) (u := (2838/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/5041 : ℝ≥0))) (u := (1338/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/9801 : ℝ≥0))) (u := (813/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/1089 : ℝ≥0))) (u := (4221/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/2809 : ℝ≥0))) (u := (2074/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/5329 : ℝ≥0))) (u := (1283/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/529 : ℝ≥0))) (u := (7253/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/1225 : ℝ≥0))) (u := (3864/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/2209 : ℝ≥0))) (u := (2483/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((4/961 : ℝ≥0))) (u := (1639/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((4/2601 : ℝ≥0))) (u := (777/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((4/5041 : ℝ≥0))) (u := (473/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/2209 : ℝ≥0))) (u := (2483/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/5625 : ℝ≥0))) (u := (1232/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((16/10609 : ℝ≥0))) (u := (766/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((1/64 : ℝ≥0))) (u := (4420/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((1/144 : ℝ≥0))) (u := (2406/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    · exact nnreal_rpow_le_of_pow_le (x := ((1/256 : ℝ≥0))) (u := (1563/100000 : ℝ≥0))
        (p := 3) (q := 4) (by norm_num)
        (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  refine le_trans (Finset.sum_le_sum fun m _ => hb m) ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_sum]
  norm_num [Fin.sum_univ_succ, wub3]

/-- **LEVEL-3 UPPER BOUND, `K = 3`.**  `dim_H E ≤ 3/4 = 0.75`, improving r210's
`61/80 = 0.7625`.  The level-3 sup-Moran root is `0.7470141…`; the true value is
`0.7056609…`, and `0.75` is **not** an approximation to it. -/
theorem dimH_gauss_three_le_three {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3) (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E) :
    dimH E ≤ (3 / 4 : ℝ≥0∞) := by
  have hd : (((3 / 4 : ℝ≥0)) : ℝ) = (3 : ℝ) / 4 := by push_cast; norm_num
  have hcast : (∑ m : Fin 27, (wcv3 m : ℝ≥0∞) ^ (((3 / 4 : ℝ≥0)) : ℝ))
      = ((∑ m : Fin 27, wcv3 m ^ ((3 : ℝ) / 4) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_finset_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hd, ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  have hsum : (∑ m : Fin 27, (wcv3 m : ℝ≥0∞) ^ (((3 / 4 : ℝ≥0)) : ℝ)) ≤ 1 := by
    rw [hcast]
    exact_mod_cast sum_wcv3_rpow_le_one
  have h := dimH_le_of_selfCover (S := gaussJ 3) (φ := wpsi3) (L := wcv3)
    (d := (3 / 4 : ℝ≥0)) hEJ (gaussJ_ediam_ne_top hEJ)
    (fun m => g3_mapsTo 3 _ _ _) (wselfCover3 hself)
    wcv3_lipschitzOnWith wcv3_lt_one hsum
  refine h.trans ?_
  norm_num

/-- **LEVEL-3 ENCLOSURE, `K = 3`.**  `0.65 ≤ dim_H E ≤ 0.75`.

Improves r210's `[0.63, 0.7625]` by about `0.033` in width.  TRUE value
`0.7056609…` (Jenkinson–Pollicott).  Neither endpoint is an approximation to
it; the gap narrows but is NOT closed. -/
theorem dimH_gauss_three_enclosure_three {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3) (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 3, Set.MapsTo (gaussIFS 3 j) E E) :
    ENNReal.ofReal ((13 : ℝ) / 20) ≤ dimH E ∧ dimH E ≤ (3 / 4 : ℝ≥0∞) :=
  ⟨le_dimH_gauss_three_level_three hEJ hself hne hclosed hinv,
    dimH_gauss_three_le_three hEJ hself⟩

/-! ## Axiom audit, `K = 3` -/

#print axioms wchi3_cyl
#print axioms wsep3
#print axioms gaussThree3
#print axioms wp3_le_rpow
#print axioms le_dimH_gauss_three_level_three
#print axioms sum_wcv3_rpow_le_one
#print axioms dimH_gauss_three_le_three
#print axioms dimH_gauss_three_enclosure_three


end PrincipiaTractalis.GaussLevelThree
