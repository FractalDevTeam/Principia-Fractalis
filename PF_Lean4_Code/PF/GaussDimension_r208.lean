/-
# PF.GaussDimension_r208 — LEVEL-2 Hausdorff dimension UPPER bounds for the
# Gauss continued-fraction Cantor sets

Consumes the Moran/Falconer engine `dimH_le_of_selfCover` of
`PF.HausdorffIFS_r205` and refines its §3 Gauss estimate by passing to the
**level-2** system: instead of the `K` single branches `φⱼ(x) = 1/(x+j)`, we use
the `K²` composites `φᵢ ∘ φⱼ`, whose exact Lipschitz constants on the invariant
interval are strictly smaller than the products `Lᵢ·Lⱼ` of the level-1 constants.

## What this file proves

* `gauss2` — the level-2 composite in closed Möbius form,
  `gauss2 K i j x = (x + b) / (a·x + 1 + a·b)` with `a = i+1`, `b = j+1`.

* `gaussIFS_comp_eq` — on the invariant interval `gaussJ K = [1/(K+1), 1]`,
  `gaussIFS K i (gaussIFS K j x) = gauss2 K i j x`.

* `gauss2_mapsTo`, `gauss2_lipschitzOnWith`, `cgauss2_lt_one` — the level-2
  IFS data, with the **exact** constant
  `cgauss2 K i j = ((K+1) / (a + (K+1)·(1 + a·b)))²`.

* `gauss2_selfCover` — squaring the level-1 self-covering hypothesis:
  `E ⊆ ⋃ⱼ φⱼ '' E` implies `E ⊆ ⋃_{(i,j)} (φᵢ ∘ φⱼ) '' E`.

* `dimH_gauss_le_two` — the general level-2 dimension bound.

* `dimH_gauss_three_le_two : dimH E ≤ 77/100` for `K = 3`.
* `dimH_gauss_two_le_two  : dimH E ≤ 29/50` for `K = 2`.

## HONESTY STATEMENT — read this before quoting anything from this file

1. **UPPER BOUNDS ONLY.**  Everything here is a covering estimate.  No LOWER
   bound for these sets is proved anywhere in this project.  A lower bound needs
   a Gibbs / conformal measure for the Gauss IFS fed into the mass distribution
   principle; that work is **not started**.  Nothing below computes a dimension.

2. **THESE ARE NOT APPROXIMATIONS TO THE TRUE VALUES.**  The true dimensions are
   `dim_H(E₂) ≈ 0.5312805` and `dim_H(E₃) ≈ 0.7056609` (Jenkinson–Pollicott,
   transfer-operator computation).  The numbers certified here, `29/50 = 0.58`
   and `77/100 = 0.77`, do **NOT** approach them and must **NEVER** be quoted as
   approximations to them.  They are certified upper bounds, nothing more.

3. **THE ATTRACTOR IS A HYPOTHESIS.**  Self-covering (`E ⊆ ⋃ⱼ φⱼ '' E`) together
   with `E ⊆ gaussJ K` are assumptions throughout.  The Hutchinson attractor is
   never constructed, never shown nonempty, never shown unique.  Every theorem
   is a conditional statement about any set with those two properties.

4. **WHERE THE IMPROVEMENT COMES FROM.**  r205's level-1 bound for `K = 3` has
   Moran root ≈ 0.9227.  The gain here is purely from using the *true composite
   derivative* `1/(a·x+1+a·b)²` of `φᵢ ∘ φⱼ` rather than the product of the two
   level-1 suprema; the level-2 Moran root is ≈ 0.7619 for `K = 3` and
   ≈ 0.5700 for `K = 2`.  We certify the round values `77/100` and `29/50`
   sitting just above those roots.  This is a level-2 refinement, not a new
   method: pushing further needs level-`n` cylinders or the transfer operator.

5. No `sorry`, no `native_decide`, no project axioms.  All results reduce to
   `[propext, Classical.choice, Quot.sound]`.

## Index convention

`i j : Fin K` are the r205 branch indices, so the continued-fraction *digits*
are `a = i+1` (outer) and `b = j+1` (inner):
`gauss2 K i j = gaussIFS K i ∘ gaussIFS K j` on `gaussJ K`.
-/

import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic
import PF.HausdorffIFS_r205

open scoped NNReal ENNReal Topology
open Set MeasureTheory

namespace PrincipiaTractalis.GaussDimension

open PrincipiaTractalis.HausdorffIFS

/-! ## §1 — the level-2 composite in closed form -/

/-- The level-2 Gauss map, outer index `i`, inner index `j`:
`gauss2 K i j x = (x + b) / (a·x + 1 + a·b)` with `a = i+1`, `b = j+1`.
On `gaussJ K` this equals `gaussIFS K i ∘ gaussIFS K j` (`gaussIFS_comp_eq`). -/
noncomputable def gauss2 (K : ℕ) (i j : Fin K) : ℝ → ℝ := fun x =>
  (x + (((j : ℕ) : ℝ) + 1)) /
    ((((i : ℕ) : ℝ) + 1) * x + 1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1))

/-- Points of the invariant interval are positive. -/
theorem pos_of_mem_gaussJ {K : ℕ} {x : ℝ} (hx : x ∈ gaussJ K) : (0 : ℝ) < x := by
  obtain ⟨hx1, _⟩ := hx
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
  linarith

/-- The level-2 denominator is positive on the invariant interval. -/
theorem gauss2_den_pos {K : ℕ} (i j : Fin K) {x : ℝ} (hx : x ∈ gaussJ K) :
    (0 : ℝ) < (((i : ℕ) : ℝ) + 1) * x + 1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1) := by
  have hx0 : (0 : ℝ) < x := pos_of_mem_gaussJ hx
  have ha : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **The composite is the Möbius map `gauss2`.**  On the invariant interval,
`φᵢ(φⱼ(x)) = (x + b)/(a·x + 1 + a·b)`. -/
theorem gaussIFS_comp_eq {K : ℕ} (i j : Fin K) {x : ℝ} (hx : x ∈ gaussJ K) :
    gaussIFS K i (gaussIFS K j x) = gauss2 K i j x := by
  have hx0 : (0 : ℝ) < x := pos_of_mem_gaussJ hx
  have hb : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxb : (0 : ℝ) < x + (((j : ℕ) : ℝ) + 1) := by linarith
  have hden : (0 : ℝ) <
      (((i : ℕ) : ℝ) + 1) * x + 1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1) :=
    gauss2_den_pos i j hx
  simp only [gaussIFS, gauss2]
  rw [show (1 : ℝ) / (x + (((j : ℕ) : ℝ) + 1)) + (((i : ℕ) : ℝ) + 1)
        = ((((i : ℕ) : ℝ) + 1) * x + 1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1))
            / (x + (((j : ℕ) : ℝ) + 1)) by
      field_simp
      ring, one_div_div]

/-! ## §2 — the exact level-2 Lipschitz constant -/

/-- The **exact** Lipschitz constant of `gauss2 K i j` on `gaussJ K`:
`((K+1) / (a + (K+1)·(1 + a·b)))²` with `a = i+1`, `b = j+1`.
The derivative of `gauss2 K i j` is `1/(a·x + 1 + a·b)²` (the Möbius determinant
is `1`), and the denominator is smallest at the left endpoint `x = 1/(K+1)`. -/
noncomputable def cgauss2 (K : ℕ) (i j : Fin K) : ℝ≥0 :=
  (((K : ℝ≥0) + 1) /
    ((((i : ℕ) : ℝ≥0) + 1)
      + ((K : ℝ≥0) + 1) * (1 + (((i : ℕ) : ℝ≥0) + 1) * (((j : ℕ) : ℝ≥0) + 1)))) ^ 2

theorem cgauss2_coe (K : ℕ) (i j : Fin K) :
    ((cgauss2 K i j : ℝ≥0) : ℝ)
      = (((K : ℝ) + 1) /
          ((((i : ℕ) : ℝ) + 1)
            + ((K : ℝ) + 1) * (1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1)))) ^ 2 := by
  simp [cgauss2]

theorem cgauss2_lt_one (K : ℕ) (i j : Fin K) : cgauss2 K i j < 1 := by
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have ha : (1 : ℝ) ≤ ((i : ℕ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hb : (1 : ℝ) ≤ ((j : ℕ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hden : (0 : ℝ) < (((i : ℕ) : ℝ) + 1)
      + ((K : ℝ) + 1) * (1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1)) := by positivity
  have hlt : ((K : ℝ) + 1) / ((((i : ℕ) : ℝ) + 1)
      + ((K : ℝ) + 1) * (1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1))) < 1 := by
    rw [div_lt_one hden]
    nlinarith [mul_pos hK
      (show (0 : ℝ) < (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1) by positivity)]
  have h0 : (0 : ℝ) ≤ ((K : ℝ) + 1) / ((((i : ℕ) : ℝ) + 1)
      + ((K : ℝ) + 1) * (1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1))) := by positivity
  have : ((cgauss2 K i j : ℝ≥0) : ℝ) < 1 := by
    rw [cgauss2_coe]
    nlinarith
  exact_mod_cast this

/-- Each level-2 map sends the invariant interval into itself. -/
theorem gauss2_mapsTo (K : ℕ) (i j : Fin K) :
    Set.MapsTo (gauss2 K i j) (gaussJ K) (gaussJ K) := by
  intro x hx
  rw [← gaussIFS_comp_eq i j hx]
  exact gauss_mapsTo K i (gauss_mapsTo K j hx)

/-! ### The pure-real algebraic core

Stated for plain real variables `a b α β x y` so that no `Fin`-cast or
`set`-definition ever reaches `field_simp` / `nlinarith`. -/

/-- The Möbius determinant of `t ↦ (t + b)/(a·t + 1 + a·b)` is `1`, so the
difference quotient collapses. -/
theorem mobius_abs_diff {a b x y : ℝ}
    (hDx : (0 : ℝ) < a * x + 1 + a * b) (hDy : (0 : ℝ) < a * y + 1 + a * b) :
    |(x + b) / (a * x + 1 + a * b) - (y + b) / (a * y + 1 + a * b)|
      = |x - y| / ((a * x + 1 + a * b) * (a * y + 1 + a * b)) := by
  have hx' : a * x + 1 + a * b ≠ 0 := ne_of_gt hDx
  have hy' : a * y + 1 + a * b ≠ 0 := ne_of_gt hDy
  have h : (x + b) / (a * x + 1 + a * b) - (y + b) / (a * y + 1 + a * b)
      = (x - y) / ((a * x + 1 + a * b) * (a * y + 1 + a * b)) := by
    rw [div_sub_div _ _ hx' hy']
    congr 1
    ring
  rw [h, abs_div, abs_of_pos (mul_pos hDx hDy)]

/-- **The algebraic Lipschitz estimate.**  If `a ≥ 0`, if `x, y ≥ α`, and if
`β · (a·α + 1 + a·b) = 1` (i.e. `β` is the reciprocal of the denominator at the
left endpoint), then `t ↦ (t + b)/(a·t + 1 + a·b)` is `β²`-Lipschitz on
`[α, ∞)`. -/
theorem mobius_lip {a b α β x y : ℝ} (ha : (0 : ℝ) ≤ a)
    (hβ : (0 : ℝ) < β) (hDα : (0 : ℝ) < a * α + 1 + a * b)
    (hkey : β * (a * α + 1 + a * b) = 1) (hx : α ≤ x) (hy : α ≤ y) :
    |(x + b) / (a * x + 1 + a * b) - (y + b) / (a * y + 1 + a * b)|
      ≤ β ^ 2 * |x - y| := by
  have hax : (0 : ℝ) ≤ a * (x - α) := mul_nonneg ha (sub_nonneg.2 hx)
  have hay : (0 : ℝ) ≤ a * (y - α) := mul_nonneg ha (sub_nonneg.2 hy)
  have hDx : (0 : ℝ) < a * x + 1 + a * b := by nlinarith
  have hDy : (0 : ℝ) < a * y + 1 + a * b := by nlinarith
  have hDxy : (0 : ℝ) < (a * x + 1 + a * b) * (a * y + 1 + a * b) := mul_pos hDx hDy
  rw [mobius_abs_diff hDx hDy, div_le_iff₀ hDxy]
  have hbx : (1 : ℝ) ≤ β * (a * x + 1 + a * b) := by
    nlinarith [mul_nonneg hβ.le hax]
  have hby : (1 : ℝ) ≤ β * (a * y + 1 + a * b) := by
    nlinarith [mul_nonneg hβ.le hay]
  have hmul : (1 : ℝ) * 1 ≤ (β * (a * x + 1 + a * b)) * (β * (a * y + 1 + a * b)) :=
    mul_le_mul hbx hby zero_le_one (zero_le_one.trans hbx)
  have heq : (β * (a * x + 1 + a * b)) * (β * (a * y + 1 + a * b))
      = β ^ 2 * ((a * x + 1 + a * b) * (a * y + 1 + a * b)) := by ring
  have h1 : (1 : ℝ) ≤ β ^ 2 * ((a * x + 1 + a * b) * (a * y + 1 + a * b)) := by
    rw [heq] at hmul; linarith
  nlinarith [abs_nonneg (x - y)]

/-- **The level-2 Lipschitz estimate.**  Direct algebraic route: the Möbius
determinant is `1`, so `|f x − f y| = |x − y| / (D(x)·D(y))` with
`D(t) = a·t + 1 + a·b`, and `D` is bounded below on `gaussJ K` by
`D(1/(K+1)) = (a + (K+1)(1+a·b))/(K+1)`. -/
theorem gauss2_lipschitzOnWith (K : ℕ) (i j : Fin K) :
    LipschitzOnWith (cgauss2 K i j) (gauss2 K i j) (gaussJ K) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  rintro x ⟨hx1, -⟩ y ⟨hy1, -⟩
  have hKne : ((K : ℝ) + 1) ≠ 0 := by positivity
  have ha0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) + 1 := by positivity
  have hden : (0 : ℝ) < (((i : ℕ) : ℝ) + 1)
      + ((K : ℝ) + 1) * (1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1)) := by positivity
  have hdenne : (((i : ℕ) : ℝ) + 1)
      + ((K : ℝ) + 1) * (1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1)) ≠ 0 := ne_of_gt hden
  have hβ0 : (0 : ℝ) < ((K : ℝ) + 1) / ((((i : ℕ) : ℝ) + 1)
      + ((K : ℝ) + 1) * (1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1))) := by positivity
  have hDα : (0 : ℝ) < (((i : ℕ) : ℝ) + 1) * (1 / ((K : ℝ) + 1)) + 1
      + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1) := by positivity
  have hkey : (((K : ℝ) + 1) / ((((i : ℕ) : ℝ) + 1)
        + ((K : ℝ) + 1) * (1 + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1))))
      * ((((i : ℕ) : ℝ) + 1) * (1 / ((K : ℝ) + 1)) + 1
        + (((i : ℕ) : ℝ) + 1) * (((j : ℕ) : ℝ) + 1)) = 1 := by
    field_simp
    ring
  rw [Real.dist_eq, Real.dist_eq, cgauss2_coe]
  simp only [gauss2]
  exact mobius_lip ha0 hβ0 hDα hkey hx1 hy1


/-! ## §3 — squaring the self-covering hypothesis -/

/-- **Level-2 self-covering.**  Applying `E ⊆ ⋃ⱼ φⱼ '' E` twice:
`E ⊆ ⋃ᵢ φᵢ '' E ⊆ ⋃ᵢ φᵢ '' (⋃ⱼ φⱼ '' E) = ⋃_{(i,j)} (φᵢ ∘ φⱼ) '' E`. -/
theorem gauss2_selfCover {K : ℕ} {E : Set ℝ} (hEJ : E ⊆ gaussJ K)
    (hself : E ⊆ ⋃ j, gaussIFS K j '' E) :
    E ⊆ ⋃ p : Fin K × Fin K, gauss2 K p.1 p.2 '' E := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hself hx)
  obtain ⟨y, hyE, rfl⟩ := hi
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hself hyE)
  obtain ⟨z, hzE, rfl⟩ := hj
  exact Set.mem_iUnion.2 ⟨(i, j), z, hzE, (gaussIFS_comp_eq i j (hEJ hzE)).symm⟩

/-! ## §4 — reindexing `Fin K × Fin K` to `Fin (K*K)`

r205's `dimH_le_of_selfCover` is stated with branch index `Fin K'`.  We move the
level-2 pair index across `finProdFinEquiv : Fin K × Fin K ≃ Fin (K * K)` rather
than re-deriving the whole §2 machinery of r205 over a general `Fintype` index. -/

/-- The level-2 family reindexed by `Fin (K * K)`. -/
noncomputable def gauss2' (K : ℕ) (n : Fin (K * K)) : ℝ → ℝ :=
  gauss2 K (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2

/-- The level-2 constants reindexed by `Fin (K * K)`. -/
noncomputable def cgauss2' (K : ℕ) (n : Fin (K * K)) : ℝ≥0 :=
  cgauss2 K (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2

@[simp] theorem gauss2'_apply (K : ℕ) (p : Fin K × Fin K) :
    gauss2' K (finProdFinEquiv p) = gauss2 K p.1 p.2 := by
  simp [gauss2']

@[simp] theorem cgauss2'_apply (K : ℕ) (p : Fin K × Fin K) :
    cgauss2' K (finProdFinEquiv p) = cgauss2 K p.1 p.2 := by
  simp [cgauss2']

/-! ## §5 — the general level-2 dimension bound -/

/-- **Level-2 Gauss dimension bound (UPPER only).**

For ANY set `E` inside the invariant interval `[1/(K+1), 1]` which is
self-covering under the `K` level-1 Gauss branches, and any `d` with
`∑_{(i,j)} (cgauss2 K i j)^d ≤ 1`, we get `dimH E ≤ d`.

The constants `cgauss2` are the exact level-2 (two-step cylinder) Lipschitz
constants, hence strictly better than the products of r205's level-1 constants.

The attractor is NOT constructed: self-covering is a hypothesis.  This is an
UPPER bound; no lower bound is proved. -/
theorem dimH_gauss_le_two {K : ℕ} {E : Set ℝ} {d : ℝ≥0}
    (hEJ : E ⊆ gaussJ K)
    (hself : E ⊆ ⋃ j, gaussIFS K j '' E)
    (hsum : (∑ p : Fin K × Fin K, (cgauss2 K p.1 p.2 : ℝ≥0∞) ^ (d : ℝ)) ≤ 1) :
    dimH E ≤ (d : ℝ≥0∞) := by
  have hbdd : EMetric.diam E ≠ ⊤ := by
    have h : EMetric.diam E ≤ EMetric.diam (gaussJ K) := EMetric.diam_mono hEJ
    have h2 : EMetric.diam (gaussJ K) = ENNReal.ofReal (1 - 1 / ((K : ℝ) + 1)) := by
      rw [gaussJ, Real.ediam_Icc]
    rw [h2] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  -- self-covering, reindexed
  have hself2 : E ⊆ ⋃ n : Fin (K * K), gauss2' K n '' E := by
    intro x hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 (gauss2_selfCover hEJ hself hx)
    refine Set.mem_iUnion.2 ⟨finProdFinEquiv p, ?_⟩
    rwa [gauss2'_apply]
  -- the Moran sum, reindexed
  have hsum2 : (∑ n : Fin (K * K), (cgauss2' K n : ℝ≥0∞) ^ (d : ℝ)) ≤ 1 := by
    have hre : (∑ n : Fin (K * K), (cgauss2' K n : ℝ≥0∞) ^ (d : ℝ))
        = ∑ p : Fin K × Fin K, (cgauss2 K p.1 p.2 : ℝ≥0∞) ^ (d : ℝ) := by
      refine (Fintype.sum_equiv finProdFinEquiv
        (fun p : Fin K × Fin K => (cgauss2 K p.1 p.2 : ℝ≥0∞) ^ (d : ℝ))
        (fun n : Fin (K * K) => (cgauss2' K n : ℝ≥0∞) ^ (d : ℝ)) ?_).symm
      intro p
      simp only [cgauss2'_apply]
    rw [hre]
    exact hsum
  exact dimH_le_of_selfCover (S := gaussJ K) (φ := gauss2' K) (L := cgauss2' K)
    hEJ hbdd
    (fun n => gauss2_mapsTo K _ _) hself2
    (fun n => gauss2_lipschitzOnWith K _ _)
    (fun n => cgauss2_lt_one K _ _) hsum2

/-! ## §6 — numeric instance `K = 3`, exponent `d = 77/100`

The nine level-2 constants are

`16/81, 16/169, 16/289, 4/49, 4/121, 4/225, 16/361, 16/961, 16/1849`

(these are `((K+1)/(a + (K+1)(1+ab)))² = 16/(a + 4 + 4ab)²` with `K = 3`).
At `d = 77/100` their `d`-th powers sum to `0.97922… ≤ 1`.  The Moran root is
≈ 0.76189; we certify `0.77`.  Compare r205's level-1 root ≈ 0.9227. -/

theorem cgauss2_three_00 : cgauss2 3 0 0 = 16 / 81 := by norm_num [cgauss2]
theorem cgauss2_three_01 : cgauss2 3 0 1 = 16 / 169 := by norm_num [cgauss2]
theorem cgauss2_three_02 : cgauss2 3 0 2 = 16 / 289 := by norm_num [cgauss2]
theorem cgauss2_three_10 : cgauss2 3 1 0 = 4 / 49 := by norm_num [cgauss2]
theorem cgauss2_three_11 : cgauss2 3 1 1 = 4 / 121 := by norm_num [cgauss2]
theorem cgauss2_three_12 : cgauss2 3 1 2 = 4 / 225 := by norm_num [cgauss2]
theorem cgauss2_three_20 : cgauss2 3 2 0 = 16 / 361 := by norm_num [cgauss2]
theorem cgauss2_three_21 : cgauss2 3 2 1 = 16 / 961 := by norm_num [cgauss2]
theorem cgauss2_three_22 : cgauss2 3 2 2 = 16 / 1849 := by norm_num [cgauss2]

/-- The nine `77/100`-powers sum to at most `9799/10000 ≤ 1`, kernel-checked via
the rational-power reduction `x^(p/q) ≤ u ↔ x^p ≤ u^q` of r205. -/
theorem sum_cgauss2_three_rpow_le_one :
    (∑ p : Fin 3 × Fin 3, cgauss2 3 p.1 p.2 ^ ((77 : ℝ) / 100)) ≤ (1 : ℝ≥0) := by
  have e00 : ((16 : ℝ≥0) / 81) ^ ((77 : ℝ) / 100) ≤ 2869 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 77) (q := 100) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e01 : ((16 : ℝ≥0) / 169) ^ ((77 : ℝ) / 100) ≤ 1629 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 77) (q := 100) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e02 : ((16 : ℝ≥0) / 289) ^ ((77 : ℝ) / 100) ≤ 1078 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 77) (q := 100) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e10 : ((4 : ℝ≥0) / 49) ^ ((77 : ℝ) / 100) ≤ 1453 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 77) (q := 100) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e11 : ((4 : ℝ≥0) / 121) ^ ((77 : ℝ) / 100) ≤ 725 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 77) (q := 100) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e12 : ((4 : ℝ≥0) / 225) ^ ((77 : ℝ) / 100) ≤ 450 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 77) (q := 100) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e20 : ((16 : ℝ≥0) / 361) ^ ((77 : ℝ) / 100) ≤ 908 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 77) (q := 100) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e21 : ((16 : ℝ≥0) / 961) ^ ((77 : ℝ) / 100) ≤ 428 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 77) (q := 100) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e22 : ((16 : ℝ≥0) / 1849) ^ ((77 : ℝ) / 100) ≤ 259 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 77) (q := 100) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, cgauss2_three_00, cgauss2_three_01, cgauss2_three_02,
    cgauss2_three_10, cgauss2_three_11, cgauss2_three_12,
    cgauss2_three_20, cgauss2_three_21, cgauss2_three_22]
  calc ((16 : ℝ≥0) / 81) ^ ((77 : ℝ) / 100) + ((16 : ℝ≥0) / 169) ^ ((77 : ℝ) / 100)
        + ((16 : ℝ≥0) / 289) ^ ((77 : ℝ) / 100)
      + (((4 : ℝ≥0) / 49) ^ ((77 : ℝ) / 100) + ((4 : ℝ≥0) / 121) ^ ((77 : ℝ) / 100)
        + ((4 : ℝ≥0) / 225) ^ ((77 : ℝ) / 100))
      + (((16 : ℝ≥0) / 361) ^ ((77 : ℝ) / 100) + ((16 : ℝ≥0) / 961) ^ ((77 : ℝ) / 100)
        + ((16 : ℝ≥0) / 1849) ^ ((77 : ℝ) / 100))
      ≤ (2869 / 10000 : ℝ≥0) + 1629 / 10000 + 1078 / 10000
        + (1453 / 10000 + 725 / 10000 + 450 / 10000)
        + (908 / 10000 + 428 / 10000 + 259 / 10000) := by gcongr
    _ ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num

/-- **Numeric corollary (`K = 3`).**  Any subset of `[1/4, 1]` self-covering
under the three Gauss branches `x ↦ 1/(x+1), 1/(x+2), 1/(x+3)` has Hausdorff
dimension at most `77/100`.

Improves r205's `19/20`.  This is an UPPER bound obtained from level-2 cylinder
constants.  The true value is ≈ `0.7056609`; `77/100` is **not** an
approximation to it. -/
theorem dimH_gauss_three_le_two {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3)
    (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E) :
    dimH E ≤ (77 / 100 : ℝ≥0∞) := by
  have hd : (((77 / 100 : ℝ≥0)) : ℝ) = (77 : ℝ) / 100 := by
    push_cast
    norm_num
  have hcast : (∑ p : Fin 3 × Fin 3, (cgauss2 3 p.1 p.2 : ℝ≥0∞) ^ (((77 / 100 : ℝ≥0)) : ℝ))
      = ((∑ p : Fin 3 × Fin 3, cgauss2 3 p.1 p.2 ^ ((77 : ℝ) / 100) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_finset_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hd, ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0 : ℝ) ≤ 77 / 100)]
  have hsum : (∑ p : Fin 3 × Fin 3, (cgauss2 3 p.1 p.2 : ℝ≥0∞) ^ (((77 / 100 : ℝ≥0)) : ℝ))
      ≤ 1 := by
    rw [hcast]
    exact_mod_cast sum_cgauss2_three_rpow_le_one
  have h := dimH_gauss_le_two (K := 3) (d := (77 / 100 : ℝ≥0)) hEJ hself hsum
  refine h.trans ?_
  norm_num

/-! ## §7 — numeric instance `K = 2`, exponent `d = 29/50`

The four level-2 constants are `9/49, 9/100, 9/121, 9/289`.  At `d = 29/50`
their `d`-th powers sum to `0.97691… ≤ 1`.  The Moran root is ≈ 0.56995; we
certify `0.58`. -/

theorem cgauss2_two_00 : cgauss2 2 0 0 = 9 / 49 := by norm_num [cgauss2]
theorem cgauss2_two_01 : cgauss2 2 0 1 = 9 / 100 := by norm_num [cgauss2]
theorem cgauss2_two_10 : cgauss2 2 1 0 = 9 / 121 := by norm_num [cgauss2]
theorem cgauss2_two_11 : cgauss2 2 1 1 = 9 / 289 := by norm_num [cgauss2]

/-- The four `29/50`-powers sum to at most `9772/10000 ≤ 1`. -/
theorem sum_cgauss2_two_rpow_le_one :
    (∑ p : Fin 2 × Fin 2, cgauss2 2 p.1 p.2 ^ ((29 : ℝ) / 50)) ≤ (1 : ℝ≥0) := by
  have e00 : ((9 : ℝ≥0) / 49) ^ ((29 : ℝ) / 50) ≤ 3743 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 29) (q := 50) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e01 : ((9 : ℝ≥0) / 100) ^ ((29 : ℝ) / 50) ≤ 2475 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 29) (q := 50) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e10 : ((9 : ℝ≥0) / 121) ^ ((29 : ℝ) / 50) ≤ 2216 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 29) (q := 50) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e11 : ((9 : ℝ≥0) / 289) ^ ((29 : ℝ) / 50) ≤ 1338 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 29) (q := 50) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, cgauss2_two_00, cgauss2_two_01,
    cgauss2_two_10, cgauss2_two_11]
  calc ((9 : ℝ≥0) / 49) ^ ((29 : ℝ) / 50) + ((9 : ℝ≥0) / 100) ^ ((29 : ℝ) / 50)
      + (((9 : ℝ≥0) / 121) ^ ((29 : ℝ) / 50) + ((9 : ℝ≥0) / 289) ^ ((29 : ℝ) / 50))
      ≤ (3743 / 10000 : ℝ≥0) + 2475 / 10000 + (2216 / 10000 + 1338 / 10000) := by gcongr
    _ ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num

/-- **Numeric corollary (`K = 2`).**  Any subset of `[1/3, 1]` self-covering
under the two Gauss branches `x ↦ 1/(x+1), 1/(x+2)` has Hausdorff dimension at
most `29/50`.

UPPER bound only.  The true value is ≈ `0.5312805`; `29/50 = 0.58` is **not** an
approximation to it. -/
theorem dimH_gauss_two_le_two {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2)
    (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E) :
    dimH E ≤ (29 / 50 : ℝ≥0∞) := by
  have hd : (((29 / 50 : ℝ≥0)) : ℝ) = (29 : ℝ) / 50 := by
    push_cast
    norm_num
  have hcast : (∑ p : Fin 2 × Fin 2, (cgauss2 2 p.1 p.2 : ℝ≥0∞) ^ (((29 / 50 : ℝ≥0)) : ℝ))
      = ((∑ p : Fin 2 × Fin 2, cgauss2 2 p.1 p.2 ^ ((29 : ℝ) / 50) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_finset_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hd, ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0 : ℝ) ≤ 29 / 50)]
  have hsum : (∑ p : Fin 2 × Fin 2, (cgauss2 2 p.1 p.2 : ℝ≥0∞) ^ (((29 / 50 : ℝ≥0)) : ℝ))
      ≤ 1 := by
    rw [hcast]
    exact_mod_cast sum_cgauss2_two_rpow_le_one
  have h := dimH_gauss_le_two (K := 2) (d := (29 / 50 : ℝ≥0)) hEJ hself hsum
  refine h.trans ?_
  norm_num

/-! ## Axiom audit -/

#print axioms gaussIFS_comp_eq
#print axioms cgauss2_lt_one
#print axioms gauss2_mapsTo
#print axioms gauss2_lipschitzOnWith
#print axioms gauss2_selfCover
#print axioms dimH_gauss_le_two
#print axioms sum_cgauss2_three_rpow_le_one
#print axioms dimH_gauss_three_le_two
#print axioms sum_cgauss2_two_rpow_le_one
#print axioms dimH_gauss_two_le_two

end PrincipiaTractalis.GaussDimension
