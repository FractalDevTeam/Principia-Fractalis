/-
# PF.GaussLevelTwo_r210 — the ABSTRACT separated-IFS lower bound, and its
# level-2 refinement of the Gauss continued-fraction dimension enclosures

## What this file is

**Part A** extracts the r209 lower-bound machinery from the level-1 Gauss
branches and restates it for an arbitrary finite, strongly separated,
conformal-type IFS on a compact real interval (`AddrIFS`).  Everything r209
proved concretely — the clamped staircase approximants, the at-most-one-free-
branch contraction, the Bernoulli functional equation, the counter-induction
Hölder estimate, the weight tiling of `[0,1]`, and the surjectivity of the
address map — is carried over verbatim with the Gauss constants replaced by
structure fields.  The single new ingredient is the orientation flag `flip`,
which lets the same theorem serve orientation-REVERSING systems (odd cylinder
levels: r209's level 1, and level 3) and orientation-PRESERVING ones (even
levels: level 2 here).

**Part B** instantiates Part A at level 2, i.e. on the `K²` two-digit Gauss
cylinders `φ_i ∘ φ_j`, with the exact per-cylinder expansion constants
`a_{ij} = 1/(d₁ + 1 + d₁d₂)²` (`d₁ = i+1`, `d₂ = j+1`) and the verified minimal
level-2 gaps `γ₂ = 1/430` (`K = 3`) and `γ₂ = 1/85` (`K = 2`).

## HONESTY STATEMENT — read this before quoting anything from this file

**Level-2 Bernoulli weighting, still not the Gibbs state.**  New enclosures
`[0.63, 0.77]` (`K = 3`) and `[0.46, 0.58]` (`K = 2`) versus true values
`0.7056609` and `0.5312805` — the gap narrows but does not close.  Level-3 would
need 27 (resp. 8) words and is the practical `norm_num` ceiling.  The
equilibrium state / RPF remains the only route to the sharp value and is not
started.

As a free extra, §B7 also tightens r208's UPPER halves from `77/100` to
`61/80 = 0.7625` and from `29/50` to `4/7 = 0.5714…`, giving the sharpest
enclosures this project has: `[0.63, 0.7625]` and `[0.46, 0.5715]`.  They are
still bracketing bounds, not approximations.

Further, as in r209:

* The attractor `E` is a HYPOTHESIS, never constructed: `E ⊆ gaussJ K`,
  nonempty, closed, forward invariant and backward covered.  Every theorem here
  is conditional.
* The exponents are BELOW the level-2 inf-Moran roots (`0.6353935` for `K = 3`,
  `0.4729948` for `K = 2`) on purpose; raising `s` above them would make the
  weight condition `p_w ≤ a_w^s` incompatible with `∑ p_w = 1` and the statement
  FALSE.  The inf-Moran root is itself below the truth because `a_w` is the
  INFIMUM of `|(φ_i ∘ φ_j)'|` over the interval.
* The upper halves `77/100` and `29/50` are imported unchanged from r208.
* No `sorry`, no `native_decide`, no project axioms.  All results reduce to
  `[propext, Classical.choice, Quot.sound]`.

## Why level 2 beats level 1

The level-1 Bernoulli bound loses because `inf|φ_j'| = 1/(j+2)²` is a bad
proxy for the cylinder length.  Passing to two-digit cylinders replaces the
product of two infima `1/((d₁+1)(d₂+1))²` by the true two-step infimum
`1/(d₁ + 1 + d₁d₂)²`, which is strictly larger (their ratio is
`((d₁+1)(d₂+1)/(d₁+1+d₁d₂))² > 1`).  That is the entire source of the gain
`0.54 → 0.63` and `0.39 → 0.46`.  The same mechanism at level 3 would gain
again, and Part A is written so that level 3 is a constant swap.
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

open scoped NNReal ENNReal Topology
open Set

namespace PrincipiaTractalis.GaussLevelTwo

open PrincipiaTractalis.HausdorffIFS
open PrincipiaTractalis.GaussLowerBound

/-! # PART A — the abstract separated-IFS lower bound

## §A1 — the data

`AddrIFS N` bundles: a compact interval `[lo, hi]` of length `< 1`, `N` branches
`ψ i` with clamped inverse branches `χ i`, an orientation flag, per-branch
expansion constants `a i`, Bernoulli weights `p i`, and the three geometric
constants `c` (weight bound), `L` (uniform contraction) and `γ` (separation).

The index order on `Fin N` is the order in which the cylinders are met when the
inverse branches are read off: `χ_j (ψ_i u) = hi` for `j < i`.  For an
orientation-preserving system this is the left-to-right order of the cylinders;
for an orientation-reversing one it is right-to-left. -/

/-- A finite, strongly separated, conformal-type IFS on a compact real interval,
together with the clamped inverse branches and a Bernoulli weight vector. -/
structure AddrIFS (N : ℕ) where
  /-- left endpoint of the ambient interval -/
  lo : ℝ
  /-- right endpoint of the ambient interval -/
  hi : ℝ
  /-- the branches -/
  ψ : Fin N → ℝ → ℝ
  /-- the globally defined, clamped inverse branches -/
  χ : Fin N → ℝ → ℝ
  /-- `true` if the branches reverse orientation -/
  flip : Bool
  /-- per-branch expansion (antilipschitz) constants -/
  a : Fin N → ℝ
  /-- the Bernoulli weights -/
  p : Fin N → ℝ
  /-- uniform upper bound for the weights -/
  c : ℝ
  /-- uniform contraction factor -/
  L : ℝ
  /-- separation constant -/
  γ : ℝ
  lo_lt_hi : lo < hi
  diam_lt_one : hi - lo < 1
  p_pos : ∀ i, 0 < p i
  p_sum : ∑ i, p i = 1
  p_le_c : ∀ i, p i ≤ c
  c_lt_one : c < 1
  a_pos : ∀ i, 0 < a i
  gamma_pos : 0 < γ
  L_pos : 0 < L
  L_lt_one : L < 1
  anti : ∀ (i : Fin N) {x y : ℝ}, x ∈ Set.Icc lo hi → y ∈ Set.Icc lo hi →
    a i * |x - y| ≤ |ψ i x - ψ i y|
  lip : ∀ (i : Fin N) {x y : ℝ}, x ∈ Set.Icc lo hi → y ∈ Set.Icc lo hi →
    |ψ i x - ψ i y| ≤ L * |x - y|
  sep : ∀ (i j : Fin N), i ≠ j → ∀ {x y : ℝ}, x ∈ Set.Icc lo hi → y ∈ Set.Icc lo hi →
    γ ≤ |ψ i x - ψ j y|
  chi_cont : ∀ i, Continuous (χ i)
  chi_lo : ∀ i, χ i lo = if flip then hi else lo
  chi_hi : ∀ i, χ i hi = if flip then lo else hi
  chi_cyl : ∀ (i j : Fin N) {u : ℝ}, u ∈ Set.Icc lo hi →
    χ j (ψ i u) = if (j : ℕ) < (i : ℕ) then hi else if j = i then u else lo
  chi_uniq : ∀ (x : ℝ) (i j : Fin N), χ i x ≠ lo → χ i x ≠ hi →
    χ j x ≠ lo → χ j x ≠ hi → i = j

namespace AddrIFS

variable {N : ℕ}

/-- The ambient interval. -/
def J (S : AddrIFS N) : Set ℝ := Set.Icc S.lo S.hi

theorem lo_mem_J (S : AddrIFS N) : S.lo ∈ S.J := ⟨le_rfl, S.lo_lt_hi.le⟩

theorem hi_mem_J (S : AddrIFS N) : S.hi ∈ S.J := ⟨S.lo_lt_hi.le, le_rfl⟩

theorem hi_sub_lo_pos (S : AddrIFS N) : 0 < S.hi - S.lo := sub_pos.2 S.lo_lt_hi

theorem card_pos (S : AddrIFS N) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · exfalso
    subst h
    have := S.p_sum
    simp at this
  · exact h

theorem c_pos (S : AddrIFS N) : 0 < S.c := by
  obtain ⟨i⟩ : Nonempty (Fin N) := Fin.pos_iff_nonempty.1 S.card_pos
  exact lt_of_lt_of_le (S.p_pos i) (S.p_le_c i)

theorem p_nonneg (S : AddrIFS N) (i : Fin N) : 0 ≤ S.p i := (S.p_pos i).le

/-- Two points of the ambient interval are at distance `< 1`. -/
theorem J_abs_sub_lt_one (S : AddrIFS N) {x y : ℝ} (hx : x ∈ S.J) (hy : y ∈ S.J) :
    |x - y| < 1 := by
  have h1 : S.lo ≤ x := hx.1
  have h2 : x ≤ S.hi := hx.2
  have h3 : S.lo ≤ y := hy.1
  have h4 : y ≤ S.hi := hy.2
  have hd := S.diam_lt_one
  rw [abs_lt]
  constructor <;> linarith

/-! ## §A2 — clamping and the orientation flip -/

/-- The clamp of `ℝ` onto the ambient interval. -/
noncomputable def cl (S : AddrIFS N) (t : ℝ) : ℝ := max S.lo (min t S.hi)

theorem cl_mem (S : AddrIFS N) (t : ℝ) : S.cl t ∈ S.J :=
  ⟨le_max_left _ _, max_le S.lo_lt_hi.le (min_le_right _ _)⟩

theorem cl_eq_self (S : AddrIFS N) {t : ℝ} (ht : t ∈ S.J) : S.cl t = t := by
  unfold cl
  rw [min_eq_left ht.2, max_eq_right ht.1]

theorem continuous_cl (S : AddrIFS N) : Continuous S.cl :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The orientation involution: `t ↦ 1 - t` for reversing systems, the identity
otherwise. -/
noncomputable def fl (S : AddrIFS N) (t : ℝ) : ℝ := if S.flip then 1 - t else t

theorem fl_fl (S : AddrIFS N) (t : ℝ) : S.fl (S.fl t) = t := by
  unfold fl; split <;> ring

theorem fl_abs_sub (S : AddrIFS N) (t u : ℝ) : |S.fl t - S.fl u| = |t - u| := by
  unfold fl
  split
  · rw [show (1 - t) - (1 - u) = -(t - u) by ring, abs_neg]
  · rfl

theorem fl_mem (S : AddrIFS N) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ S.fl t ∧ S.fl t ≤ 1 := by
  unfold fl
  split <;> constructor <;> linarith

theorem continuous_fl (S : AddrIFS N) : Continuous S.fl := by
  unfold fl
  split
  · exact continuous_const.sub continuous_id
  · exact continuous_id

/-! ## §A3 — the staircase approximants -/

/-- The `n`-th Bernoulli-staircase approximant: the affine ramp, then repeated
application of the clamped averaging operator. -/
noncomputable def approx (S : AddrIFS N) : ℕ → ℝ → ℝ
  | 0, x => (S.cl x - S.lo) / (S.hi - S.lo)
  | (n + 1), x => S.fl (∑ j, S.p j * S.approx n (S.χ j x))

theorem approx_zero_apply (S : AddrIFS N) (x : ℝ) :
    S.approx 0 x = (S.cl x - S.lo) / (S.hi - S.lo) := rfl

theorem approx_succ_apply (S : AddrIFS N) (n : ℕ) (x : ℝ) :
    S.approx (n + 1) x = S.fl (∑ j, S.p j * S.approx n (S.χ j x)) := rfl

theorem approx_mem (S : AddrIFS N) (n : ℕ) (x : ℝ) :
    0 ≤ S.approx n x ∧ S.approx n x ≤ 1 := by
  have hden : 0 < S.hi - S.lo := S.hi_sub_lo_pos
  induction n generalizing x with
  | zero =>
      rw [approx_zero_apply]
      have hmem := S.cl_mem x
      have hlo : S.lo ≤ S.cl x := hmem.1
      have hhi : S.cl x ≤ S.hi := hmem.2
      constructor
      · exact div_nonneg (by linarith) hden.le
      · rw [div_le_one hden]
        linarith
  | succ n ih =>
      rw [approx_succ_apply]
      have hle : ∑ j, S.p j * S.approx n (S.χ j x) ≤ ∑ j : Fin N, S.p j := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc S.p j * S.approx n (S.χ j x) ≤ S.p j * 1 :=
              mul_le_mul_of_nonneg_left (ih _).2 (S.p_nonneg j)
          _ = S.p j := by ring
      have hge : (0 : ℝ) ≤ ∑ j, S.p j * S.approx n (S.χ j x) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (S.p_nonneg j) (ih _).1
      rw [S.p_sum] at hle
      exact S.fl_mem hge hle

theorem approx_nonneg (S : AddrIFS N) (n : ℕ) (x : ℝ) : 0 ≤ S.approx n x :=
  (S.approx_mem n x).1

theorem approx_le_one (S : AddrIFS N) (n : ℕ) (x : ℝ) : S.approx n x ≤ 1 :=
  (S.approx_mem n x).2

/-- The two boundary values, proved simultaneously. -/
theorem approx_bdry (S : AddrIFS N) (n : ℕ) :
    S.approx n S.lo = 0 ∧ S.approx n S.hi = 1 := by
  have hden : 0 < S.hi - S.lo := S.hi_sub_lo_pos
  induction n with
  | zero =>
      rw [approx_zero_apply, approx_zero_apply, S.cl_eq_self S.lo_mem_J,
        S.cl_eq_self S.hi_mem_J]
      constructor
      · simp
      · field_simp
  | succ n ih =>
      by_cases hf : S.flip = true
      · constructor
        · rw [approx_succ_apply]
          have h : ∀ j : Fin N, S.p j * S.approx n (S.χ j S.lo) = S.p j := by
            intro j
            rw [S.chi_lo j, hf]
            simp only [if_true]
            rw [ih.2]
            ring
          rw [Finset.sum_congr rfl fun j _ => h j, S.p_sum]
          unfold fl
          rw [hf]
          norm_num
        · rw [approx_succ_apply]
          have h : ∀ j : Fin N, S.p j * S.approx n (S.χ j S.hi) = 0 := by
            intro j
            rw [S.chi_hi j, hf]
            simp only [if_true]
            rw [ih.1]
            ring
          rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_const_zero]
          unfold fl
          rw [hf]
          norm_num
      · simp only [Bool.not_eq_true] at hf
        constructor
        · rw [approx_succ_apply]
          have h : ∀ j : Fin N, S.p j * S.approx n (S.χ j S.lo) = 0 := by
            intro j
            rw [S.chi_lo j, hf]
            simp only [Bool.false_eq_true, if_false]
            rw [ih.1]
            ring
          rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_const_zero]
          unfold fl
          rw [hf]
          norm_num
        · rw [approx_succ_apply]
          have h : ∀ j : Fin N, S.p j * S.approx n (S.χ j S.hi) = S.p j := by
            intro j
            rw [S.chi_hi j, hf]
            simp only [Bool.false_eq_true, if_false]
            rw [ih.2]
            ring
          rw [Finset.sum_congr rfl fun j _ => h j, S.p_sum]
          unfold fl
          rw [hf]
          norm_num

theorem approx_at_lo (S : AddrIFS N) (n : ℕ) : S.approx n S.lo = 0 := (S.approx_bdry n).1

theorem approx_at_hi (S : AddrIFS N) (n : ℕ) : S.approx n S.hi = 1 := (S.approx_bdry n).2

theorem approx_continuous (S : AddrIFS N) (n : ℕ) : Continuous (S.approx n) := by
  induction n with
  | zero =>
      have h : S.approx 0 = fun x : ℝ => (S.cl x - S.lo) / (S.hi - S.lo) := rfl
      rw [h]
      exact (S.continuous_cl.sub continuous_const).div_const _
  | succ n ih =>
      have h : S.approx (n + 1)
          = fun x : ℝ => S.fl (∑ j, S.p j * S.approx n (S.χ j x)) := rfl
      rw [h]
      exact S.continuous_fl.comp
        (continuous_finset_sum _ fun j _ => continuous_const.mul (ih.comp (S.chi_cont j)))

/-! ## §A4 — head weights and the Bernoulli functional equation -/

/-- Head sums of the weights, `H_k = ∑_{j < k} p_j`. -/
noncomputable def Hsum (S : AddrIFS N) (k : ℕ) : ℝ :=
  ∑ j : Fin N, if (j : ℕ) < k then S.p j else 0

theorem Hsum_zero (S : AddrIFS N) : S.Hsum 0 = 0 := by
  unfold Hsum
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg (by omega)]

theorem Hsum_card (S : AddrIFS N) : S.Hsum N = 1 := by
  unfold Hsum
  rw [Finset.sum_congr rfl fun j _ => if_pos j.isLt]
  exact S.p_sum

theorem Hsum_succ (S : AddrIFS N) {k : ℕ} (hk : k < N) :
    S.Hsum (k + 1) = S.Hsum k + S.p ⟨k, hk⟩ := by
  have hsingle : (∑ j : Fin N, if (j : ℕ) = k then S.p j else 0) = S.p ⟨k, hk⟩ := by
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin N)]
    · simp
    · intro b _ hb
      exact if_neg fun hc => hb (Fin.ext hc)
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  have h : ∀ j : Fin N, (if (j : ℕ) < k + 1 then S.p j else 0)
      = (if (j : ℕ) < k then S.p j else 0) + (if (j : ℕ) = k then S.p j else 0) := by
    intro j
    rcases lt_trichotomy ((j : ℕ)) k with h1 | h1 | h1
    · rw [if_pos (by omega), if_pos h1, if_neg (by omega)]; ring
    · rw [if_pos (by omega), if_neg (by omega), if_pos h1]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
  unfold Hsum
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib]
  unfold Hsum at hsingle
  rw [hsingle]

theorem Hsum_succ' (S : AddrIFS N) (i : Fin N) :
    S.Hsum ((i : ℕ) + 1) = S.Hsum (i : ℕ) + S.p i := by
  have h := S.Hsum_succ i.isLt
  rwa [Fin.eta] at h

/-- The mass strictly ahead of the `i`-th cylinder, in the direction the address
map runs. -/
noncomputable def Wlead (S : AddrIFS N) (i : Fin N) : ℝ :=
  if S.flip then 1 - S.Hsum ((i : ℕ) + 1) else S.Hsum (i : ℕ)

/-- **The Bernoulli functional equation, approximant level.** -/
theorem approx_funeq (S : AddrIFS N) (n : ℕ) (i : Fin N) {u : ℝ} (hu : u ∈ S.J) :
    S.approx (n + 1) (S.ψ i u) = S.Wlead i + S.p i * S.fl (S.approx n u) := by
  rw [approx_succ_apply]
  have hb1 := S.approx_at_hi n
  have hb0 := S.approx_at_lo n
  have hterm : ∀ j : Fin N, S.p j * S.approx n (S.χ j (S.ψ i u))
      = (if (j : ℕ) < (i : ℕ) then S.p j else 0)
        + (if j = i then S.p i * S.approx n u else 0) := by
    intro j
    rw [S.chi_cyl i j hu]
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
    Finset.sum_ite_eq' Finset.univ i (fun _ => S.p i * S.approx n u)]
  simp only [Finset.mem_univ, if_true]
  have hH : (∑ j : Fin N, if (j : ℕ) < (i : ℕ) then S.p j else 0) = S.Hsum (i : ℕ) := rfl
  rw [hH]
  have hstep := S.Hsum_succ' i
  unfold Wlead fl
  split
  · rw [hstep]; ring
  · ring

/-! ## §A5 — the contraction estimate -/

theorem approx_diff (S : AddrIFS N) (n : ℕ) (x : ℝ) :
    |S.approx (n + 1) x - S.approx n x| ≤ S.c ^ n := by
  induction n generalizing x with
  | zero =>
      have h1 := S.approx_nonneg 1 x
      have h2 := S.approx_le_one 1 x
      have h3 := S.approx_nonneg 0 x
      have h4 := S.approx_le_one 0 x
      rw [pow_zero, abs_sub_le_iff]
      constructor <;> linarith
  | succ n ih =>
      classical
      set F : Fin N → ℝ := fun j =>
        S.p j * (S.approx (n + 1) (S.χ j x) - S.approx n (S.χ j x)) with hF
      have hsplit : ∑ j, F j
          = (∑ j, S.p j * S.approx (n + 1) (S.χ j x))
            - ∑ j, S.p j * S.approx n (S.χ j x) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [hF]; ring
      have heq : |S.approx (n + 1 + 1) x - S.approx (n + 1) x| = |∑ j, F j| := by
        rw [approx_succ_apply, approx_succ_apply, S.fl_abs_sub, hsplit]
      have hzero : ∀ j : Fin N, (S.χ j x = S.lo ∨ S.χ j x = S.hi) → F j = 0 := by
        intro j hj
        rcases hj with h | h
        · rw [hF]
          simp only
          rw [h, S.approx_at_lo (n + 1), S.approx_at_lo n]
          ring
        · rw [hF]
          simp only
          rw [h, S.approx_at_hi (n + 1), S.approx_at_hi n]
          ring
      have hkey : |∑ j, F j| ≤ S.c ^ (n + 1) := by
        by_cases hex : ∃ j0 : Fin N, S.χ j0 x ≠ S.lo ∧ S.χ j0 x ≠ S.hi
        · obtain ⟨j0, hj0a, hj0b⟩ := hex
          have hsingle : ∑ j, F j = F j0 := by
            refine Finset.sum_eq_single j0 (fun j _ hj => hzero j ?_) (by simp)
            by_contra hc
            push_neg at hc
            exact hj (S.chi_uniq x j j0 hc.1 hc.2 hj0a hj0b)
          rw [hsingle, hF]
          simp only
          rw [abs_mul, abs_of_nonneg (S.p_nonneg j0)]
          calc S.p j0 * |S.approx (n + 1) (S.χ j0 x) - S.approx n (S.χ j0 x)|
              ≤ S.c * S.c ^ n :=
                mul_le_mul (S.p_le_c j0) (ih _) (abs_nonneg _) S.c_pos.le
            _ = S.c ^ (n + 1) := by rw [pow_succ]; ring
        · push_neg at hex
          have hall : ∀ j ∈ (Finset.univ : Finset (Fin N)), F j = 0 := by
            intro j _
            by_cases h : S.χ j x = S.lo
            · exact hzero j (Or.inl h)
            · exact hzero j (Or.inr (hex j h))
          rw [Finset.sum_eq_zero hall, abs_zero]
          exact pow_nonneg S.c_pos.le _
      rw [heq]
      exact hkey

/-! ## §A6 — the address map -/

theorem approx_summable (S : AddrIFS N) (x : ℝ) :
    Summable fun n : ℕ => S.approx (n + 1) x - S.approx n x := by
  refine Summable.of_norm_bounded
    (summable_geometric_of_lt_one S.c_pos.le S.c_lt_one) ?_
  intro n
  rw [Real.norm_eq_abs]
  exact S.approx_diff n x

/-- **The address map**: the sum of the telescoping series of approximants. -/
noncomputable def addr (S : AddrIFS N) (x : ℝ) : ℝ :=
  S.approx 0 x + ∑' n : ℕ, (S.approx (n + 1) x - S.approx n x)

theorem tendsto_approx (S : AddrIFS N) (x : ℝ) :
    Filter.Tendsto (fun n => S.approx n x) Filter.atTop (𝓝 (S.addr x)) := by
  have hs := (S.approx_summable x).hasSum.tendsto_sum_nat
  have hrw : ∀ n : ℕ, ∑ i ∈ Finset.range n, (S.approx (i + 1) x - S.approx i x)
      = S.approx n x - S.approx 0 x :=
    fun n => Finset.sum_range_sub (fun i => S.approx i x) n
  simp only [hrw] at hs
  have h2 := hs.add_const (S.approx 0 x)
  have h3 : (fun n : ℕ => S.approx n x - S.approx 0 x + S.approx 0 x)
      = fun n => S.approx n x := by
    funext n; ring
  rw [h3] at h2
  have h4 : (∑' n : ℕ, (S.approx (n + 1) x - S.approx n x)) + S.approx 0 x = S.addr x := by
    rw [addr]; ring
  rwa [h4] at h2

theorem addr_of_tendsto (S : AddrIFS N) {x L : ℝ}
    (h : Filter.Tendsto (fun n => S.approx n x) Filter.atTop (𝓝 L)) : S.addr x = L :=
  tendsto_nhds_unique (S.tendsto_approx x) h

theorem addr_nonneg (S : AddrIFS N) (x : ℝ) : 0 ≤ S.addr x :=
  ge_of_tendsto' (S.tendsto_approx x) fun n => S.approx_nonneg n x

theorem addr_le_one (S : AddrIFS N) (x : ℝ) : S.addr x ≤ 1 :=
  le_of_tendsto' (S.tendsto_approx x) fun n => S.approx_le_one n x

theorem continuous_addr (S : AddrIFS N) : Continuous S.addr := by
  have h1 : Continuous fun x : ℝ => S.approx 0 x := S.approx_continuous 0
  have h2 : Continuous fun x : ℝ => ∑' n : ℕ, (S.approx (n + 1) x - S.approx n x) := by
    refine continuous_tsum (u := fun n : ℕ => S.c ^ n)
      (fun n => (S.approx_continuous (n + 1)).sub (S.approx_continuous n))
      (summable_geometric_of_lt_one S.c_pos.le S.c_lt_one) ?_
    intro n x
    rw [Real.norm_eq_abs]
    exact S.approx_diff n x
  exact h1.add h2

/-- **The Bernoulli functional equation.** -/
theorem addr_funeq (S : AddrIFS N) (i : Fin N) {u : ℝ} (hu : u ∈ S.J) :
    S.addr (S.ψ i u) = S.Wlead i + S.p i * S.fl (S.addr u) := by
  refine S.addr_of_tendsto ?_
  rw [← Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => S.approx n (S.ψ i u)) 1]
  rw [show (fun n : ℕ => S.approx (n + 1) (S.ψ i u))
      = fun n : ℕ => S.Wlead i + S.p i * S.fl (S.approx n u) from
    funext fun n => S.approx_funeq n i hu]
  have hcont : Filter.Tendsto (fun n : ℕ => S.fl (S.approx n u)) Filter.atTop
      (𝓝 (S.fl (S.addr u))) :=
    (S.continuous_fl.tendsto _).comp (S.tendsto_approx u)
  exact ((hcont.const_mul (S.p i)).const_add (S.Wlead i))

/-- The address map contracts by exactly `p_i` along the `i`-th branch. -/
theorem addr_branch_abs (S : AddrIFS N) (i : Fin N) {u v : ℝ}
    (hu : u ∈ S.J) (hv : v ∈ S.J) :
    |S.addr (S.ψ i u) - S.addr (S.ψ i v)| = S.p i * |S.addr u - S.addr v| := by
  rw [S.addr_funeq i hu, S.addr_funeq i hv]
  have h : S.Wlead i + S.p i * S.fl (S.addr u) - (S.Wlead i + S.p i * S.fl (S.addr v))
      = S.p i * (S.fl (S.addr u) - S.fl (S.addr v)) := by ring
  rw [h, abs_mul, abs_of_nonneg (S.p_nonneg i), S.fl_abs_sub]

/-! ## §A7 — the Hölder estimate -/

/-- **The Hölder descent**, counter form. -/
theorem addr_holder_aux (S : AddrIFS N) {E : Set ℝ} {s : ℝ} (hs : 0 < s)
    (hEJ : E ⊆ S.J) (hself : E ⊆ ⋃ i, S.ψ i '' E)
    (hps : ∀ i : Fin N, S.p i ≤ S.a i ^ s) :
    ∀ (M : ℕ) (x y : ℝ), x ∈ E → y ∈ E → S.L ^ M < |x - y| →
      |S.addr x - S.addr y| ≤ (|x - y| / S.γ) ^ s := by
  have hγ : 0 < S.γ := S.gamma_pos
  intro M
  induction M with
  | zero =>
      intro x y hx hy hlt
      rw [pow_zero] at hlt
      exact absurd hlt (not_lt.2 (S.J_abs_sub_lt_one (hEJ hx) (hEJ hy)).le)
  | succ M ih =>
      intro x y hx hy hlt
      obtain ⟨i, x', hx'E, hxeq⟩ := Set.mem_iUnion.1 (hself hx)
      obtain ⟨j, y', hy'E, hyeq⟩ := Set.mem_iUnion.1 (hself hy)
      have hx'J : x' ∈ S.J := hEJ hx'E
      have hy'J : y' ∈ S.J := hEJ hy'E
      by_cases hij : i = j
      · subst hij
        subst hxeq
        subst hyeq
        have hLpos : 0 < S.L := S.L_pos
        have hlip := S.lip i hx'J hy'J
        have hstep : S.L ^ M < |x' - y'| := by
          rw [pow_succ] at hlt
          nlinarith [pow_pos hLpos M]
        have hrec := ih x' y' hx'E hy'E hstep
        rw [S.addr_branch_abs i hx'J hy'J]
        have hanti := S.anti i hx'J hy'J
        have ha0 : 0 < S.a i := S.a_pos i
        have hq0 : (0 : ℝ) ≤ |x' - y'| / S.γ := by positivity
        have hmono : S.p i * (|x' - y'| / S.γ) ^ s
            ≤ S.a i ^ s * (|x' - y'| / S.γ) ^ s :=
          mul_le_mul_of_nonneg_right (hps i) (Real.rpow_nonneg hq0 s)
        have hcomb : S.a i ^ s * (|x' - y'| / S.γ) ^ s
            = (S.a i * (|x' - y'| / S.γ)) ^ s :=
          (Real.mul_rpow ha0.le hq0).symm
        have hinner : S.a i * (|x' - y'| / S.γ)
            ≤ |S.ψ i x' - S.ψ i y'| / S.γ := by
          rw [mul_div_assoc']
          gcongr
        have hfinal : (S.a i * (|x' - y'| / S.γ)) ^ s
            ≤ (|S.ψ i x' - S.ψ i y'| / S.γ) ^ s :=
          Real.rpow_le_rpow (by positivity) hinner hs.le
        calc S.p i * |S.addr x' - S.addr y'|
            ≤ S.p i * (|x' - y'| / S.γ) ^ s :=
              mul_le_mul_of_nonneg_left hrec (S.p_nonneg i)
          _ ≤ S.a i ^ s * (|x' - y'| / S.γ) ^ s := hmono
          _ = (S.a i * (|x' - y'| / S.γ)) ^ s := hcomb
          _ ≤ (|S.ψ i x' - S.ψ i y'| / S.γ) ^ s := hfinal
      · have hsep : S.γ ≤ |x - y| := by
          rw [← hxeq, ← hyeq]
          exact S.sep i j hij hx'J hy'J
        have hone : (1 : ℝ) ≤ |x - y| / S.γ := by
          rw [le_div_iff₀ hγ, one_mul]
          exact hsep
        have hge : (1 : ℝ) ≤ (|x - y| / S.γ) ^ s := by
          have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hone hs.le
          rwa [Real.one_rpow] at this
        have hA1 := S.addr_nonneg x
        have hA2 := S.addr_le_one x
        have hA3 := S.addr_nonneg y
        have hA4 := S.addr_le_one y
        have : |S.addr x - S.addr y| ≤ 1 := by
          rw [abs_sub_le_iff]
          constructor <;> linarith
        linarith

/-- **The Hölder estimate**, `dist` form. -/
theorem addr_dist_le (S : AddrIFS N) {E : Set ℝ} {s : ℝ} (hs : 0 < s)
    (hEJ : E ⊆ S.J) (hself : E ⊆ ⋃ i, S.ψ i '' E)
    (hps : ∀ i : Fin N, S.p i ≤ S.a i ^ s)
    {x y : ℝ} (hx : x ∈ E) (hy : y ∈ E) :
    |S.addr x - S.addr y| ≤ (1 / S.γ) ^ s * |x - y| ^ s := by
  have hγ : 0 < S.γ := S.gamma_pos
  rcases eq_or_lt_of_le (abs_nonneg (x - y)) with h0 | h0
  · have hxy : x = y := sub_eq_zero.1 (abs_eq_zero.1 h0.symm)
    subst hxy
    simp only [sub_self, abs_zero]
    positivity
  · obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one h0 S.L_lt_one
    have hmain := S.addr_holder_aux hs hEJ hself hps M x y hx hy hM
    have hrw : (|x - y| / S.γ) ^ s = (1 / S.γ) ^ s * |x - y| ^ s := by
      rw [show |x - y| / S.γ = (1 / S.γ) * |x - y| by ring,
        Real.mul_rpow (by positivity) (abs_nonneg _)]
    rwa [hrw] at hmain

/-- **`HolderOnWith` packaging** of the address map. -/
theorem addr_holderOn (S : AddrIFS N) {E : Set ℝ} {s : ℝ} (hs : 0 < s)
    (hEJ : E ⊆ S.J) (hself : E ⊆ ⋃ i, S.ψ i '' E)
    (hps : ∀ i : Fin N, S.p i ≤ S.a i ^ s) :
    HolderOnWith (((1 / S.γ) ^ s).toNNReal) s.toNNReal S.addr E := by
  have hγ : 0 < S.γ := S.gamma_pos
  have hCnn : (0 : ℝ) ≤ (1 / S.γ) ^ s := Real.rpow_nonneg (by positivity) s
  have hCcoe : ((((1 / S.γ) ^ s).toNNReal : ℝ≥0) : ℝ) = (1 / S.γ) ^ s :=
    Real.coe_toNNReal _ hCnn
  intro x hx y hy
  have hscoe : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.le
  have hC : ((((1 / S.γ) ^ s).toNNReal : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal ((1 / S.γ) ^ s) := by
    rw [← ENNReal.ofReal_coe_nnreal, hCcoe]
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, hscoe,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs.le, hC,
    ← ENNReal.ofReal_mul hCnn]
  exact ENNReal.ofReal_le_ofReal (S.addr_dist_le hs hEJ hself hps hx hy)

/-! ## §A8 — surjectivity onto `[0,1]` -/

/-- **The head blocks tile `[0,1]`.** -/
theorem hsum_cover (S : AddrIFS N) :
    ∀ (d k : ℕ), k + d = N → ∀ t : ℝ, S.Hsum k ≤ t → t ≤ 1 →
      ∃ i : Fin N, S.Hsum (i : ℕ) ≤ t ∧ t ≤ S.Hsum ((i : ℕ) + 1) := by
  intro d
  induction d with
  | zero =>
      intro k hk t htk ht1
      have hkK : k = N := by omega
      rw [hkK, S.Hsum_card] at htk
      have ht : t = 1 := le_antisymm ht1 htk
      have hNpos : 0 < N := S.card_pos
      refine ⟨⟨N - 1, by omega⟩, ?_, ?_⟩
      · have hstep := S.Hsum_succ (k := N - 1) (by omega)
        have hNN : N - 1 + 1 = N := by omega
        rw [hNN, S.Hsum_card] at hstep
        have := S.p_pos ⟨N - 1, by omega⟩
        simp only []
        linarith
      · have hNN : (⟨N - 1, by omega⟩ : Fin N).val + 1 = N := by simp; omega
        rw [hNN, S.Hsum_card, ht]
  | succ d ih =>
      intro k hk t htk ht1
      have hkK : k < N := by omega
      have hnext : (k + 1) + d = N := by omega
      by_cases hle : t ≤ S.Hsum (k + 1)
      · exact ⟨⟨k, hkK⟩, htk, hle⟩
      · push_neg at hle
        exact ih (k + 1) hnext t hle.le ht1

/-- **The weight blocks tile `[0,1]`**, in the direction the address map runs. -/
theorem wlead_cover (S : AddrIFS N) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ∃ i : Fin N, S.Wlead i ≤ t ∧ t ≤ S.Wlead i + S.p i := by
  obtain ⟨hf0, hf1⟩ := S.fl_mem h0 h1
  obtain ⟨i, hi1, hi2⟩ := S.hsum_cover N 0 (by omega) (S.fl t) (by rw [S.Hsum_zero]; exact hf0) hf1
  refine ⟨i, ?_, ?_⟩ <;>
    · have hstep := S.Hsum_succ' i
      unfold Wlead
      unfold fl at hi1 hi2
      split at hi1
      · next hfl =>
          rw [if_pos hfl] at hi2 ⊢
          rw [hstep] at hi2 ⊢
          linarith
      · next hfl =>
          rw [if_neg hfl] at hi2 ⊢
          rw [hstep] at hi2
          linarith

/-- **Density of the image.** -/
theorem addr_image_dense (S : AddrIFS N) {E : Set ℝ}
    (hEJ : E ⊆ S.J) (hne : E.Nonempty)
    (hinv : ∀ i : Fin N, Set.MapsTo (S.ψ i) E E) :
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 → ∃ z ∈ S.addr '' E, |t - z| ≤ S.c ^ n := by
  intro n
  induction n with
  | zero =>
      intro t ht0 ht1
      obtain ⟨x, hx⟩ := hne
      refine ⟨S.addr x, ⟨x, hx, rfl⟩, ?_⟩
      rw [pow_zero, abs_le]
      have h1 := S.addr_nonneg x
      have h2 := S.addr_le_one x
      constructor <;> linarith
  | succ n ih =>
      intro t ht0 ht1
      obtain ⟨i, hi1, hi2⟩ := S.wlead_cover t ht0 ht1
      have hwi : 0 < S.p i := S.p_pos i
      set q : ℝ := (t - S.Wlead i) / S.p i with hqdef
      have hq0 : 0 ≤ q := div_nonneg (by linarith) hwi.le
      have hq1 : q ≤ 1 := by
        rw [hqdef, div_le_one hwi]
        linarith
      set r : ℝ := S.fl q with hrdef
      obtain ⟨hr0, hr1⟩ := S.fl_mem hq0 hq1
      have hflr : S.fl r = q := by rw [hrdef, S.fl_fl]
      have hteq : t = S.Wlead i + S.p i * S.fl r := by
        rw [hflr, hqdef]
        field_simp
        ring
      obtain ⟨z', hz'im, hz'⟩ := ih r hr0 hr1
      obtain ⟨u, huE, hzu⟩ := hz'im
      refine ⟨S.addr (S.ψ i u), ⟨S.ψ i u, hinv i huE, rfl⟩, ?_⟩
      rw [S.addr_funeq i (hEJ huE)]
      have hexp : t - (S.Wlead i + S.p i * S.fl (S.addr u))
          = S.p i * (S.fl r - S.fl (S.addr u)) := by
        rw [hteq]; ring
      rw [hexp, abs_mul, abs_of_nonneg hwi.le, S.fl_abs_sub]
      have hz'' : |r - S.addr u| ≤ S.c ^ n := by
        rw [hzu]
        exact hz'
      calc S.p i * |r - S.addr u| ≤ S.c * S.c ^ n :=
            mul_le_mul (S.p_le_c i) hz'' (abs_nonneg _) S.c_pos.le
        _ = S.c ^ (n + 1) := by rw [pow_succ]; ring

/-- **Surjectivity onto the unit interval.** -/
theorem unitInterval_subset_addr_image (S : AddrIFS N) {E : Set ℝ}
    (hEJ : E ⊆ S.J) (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ i : Fin N, Set.MapsTo (S.ψ i) E E) :
    Set.Icc (0 : ℝ) 1 ⊆ S.addr '' E := by
  have hJc : IsCompact S.J := isCompact_Icc
  have hcompact : IsCompact E := hJc.of_isClosed_subset hclosed hEJ
  have hclosedIm : IsClosed (S.addr '' E) :=
    (hcompact.image S.continuous_addr).isClosed
  intro t ht
  have hmem : t ∈ closure (S.addr '' E) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε S.c_lt_one
    obtain ⟨z, hz, hdz⟩ := S.addr_image_dense hEJ hne hinv n t ht.1 ht.2
    exact ⟨z, hz, by rw [Real.dist_eq]; linarith⟩
  rwa [hclosedIm.closure_eq] at hmem

/-! ## §A9 — the abstract lower bound -/

/-- **ABSTRACT LOWER BOUND FOR A SEPARATED IFS ON AN INTERVAL.**

Let `S` be an `AddrIFS N` and let `E ⊆ [lo, hi]` be nonempty, closed, forward
invariant under all `N` branches and backward covered by them.  If the Bernoulli
weights satisfy `p i ≤ (a i)^s` for every branch, then `s ≤ dim_H E`.

This is the r209 argument with the Gauss constants abstracted away: a Bernoulli
(i.i.d. product) weighting, never the Gibbs / equilibrium state, hence never
sharp for a nonlinear conformal attractor. -/
theorem le_dimH (S : AddrIFS N) {E : Set ℝ} {s : ℝ} (hs : 0 < s)
    (hEJ : E ⊆ S.J) (hself : E ⊆ ⋃ i, S.ψ i '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ i : Fin N, Set.MapsTo (S.ψ i) E E)
    (hps : ∀ i : Fin N, S.p i ≤ S.a i ^ s) :
    ENNReal.ofReal s ≤ dimH E := by
  have hr : 0 < s.toNNReal := Real.toNNReal_pos.2 hs
  have h := PrincipiaTractalis.CantorDimension.le_dimH_of_holder_surj hr
    (S.addr_holderOn hs hEJ hself hps)
    (S.unitInterval_subset_addr_image hEJ hne hclosed hinv)
  rwa [dimH_unitInterval, mul_one] at h

end AddrIFS

/-! ## §A10 — consistency check: r209 re-derived from the abstract theorem

The level-1 Gauss system is an `AddrIFS K` with `flip = true`; every field is a
theorem already proved in r209.  Feeding it to `AddrIFS.le_dimH` reproduces
r209's `le_dimH_gauss_three` and `le_dimH_gauss_two` verbatim, which is the
check that the abstraction lost nothing. -/

/-- The level-1 Gauss IFS, packaged as an `AddrIFS`.  Orientation REVERSING. -/
noncomputable def gaussLevelOne (K : ℕ) (hK : 0 < K) (P : GaussWeights K) : AddrIFS K where
  lo := betaK K
  hi := 1
  ψ := gaussIFS K
  χ := gpre K
  flip := true
  a := fun j => agauss (j : ℕ)
  p := P.w
  c := P.c
  L := LmaxK K
  γ := gaussGap K
  lo_lt_hi := betaK_lt_one hK
  diam_lt_one := by have := betaK_pos (K := K); linarith
  p_pos := P.w_pos
  p_sum := P.w_sum
  p_le_c := P.w_le
  c_lt_one := P.c_lt_one
  a_pos := fun j => agauss_pos _
  gamma_pos := gaussGap_pos hK
  L_pos := LmaxK_pos
  L_lt_one := LmaxK_lt_one
  anti := by intro i x y hx hy; exact gauss_antilipschitz i hx hy
  lip := by intro i x y hx hy; exact gauss_lip_real i hx hy
  sep := by intro i j hij x y hx hy; exact gauss_separation hij hx hy
  chi_cont := continuous_gpre
  chi_lo := fun j => by simpa using gpre_at_beta j
  chi_hi := fun j => by simpa using gpre_at_one j
  chi_cyl := by intro i j u hu; exact gpre_on_cylinder i j hu
  chi_uniq := by
    intro x i j h1 h2 h3 h4
    have hi : gfree K i x := by
      by_contra hc
      rcases gpre_clamped hc with h | h
      · exact h1 h
      · exact h2 h
    have hj : gfree K j x := by
      by_contra hc
      rcases gpre_clamped hc with h | h
      · exact h3 h
      · exact h4 h
    exact gfree_unique hi hj

/-- **Consistency check.**  r209's `K = 3` lower bound, re-derived from the
abstract theorem by supplying the level-1 constants. -/
theorem le_dimH_gauss_three_abstract {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3) (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 3, Set.MapsTo (gaussIFS 3 j) E E) :
    ENNReal.ofReal ((54 : ℝ) / 100) ≤ dimH E :=
  (gaussLevelOne 3 (by norm_num) gaussW3).le_dimH (by norm_num) hEJ hself hne hclosed hinv
    gaussW3_ws

/-- **Consistency check.**  r209's `K = 2` lower bound, re-derived. -/
theorem le_dimH_gauss_two_abstract {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2) (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 2, Set.MapsTo (gaussIFS 2 j) E E) :
    ENNReal.ofReal ((39 : ℝ) / 100) ≤ dimH E :=
  (gaussLevelOne 2 (by norm_num) gaussW2).le_dimH (by norm_num) hEJ hself hne hclosed hinv
    gaussW2_ws

/-! # PART B — the level-2 Gauss system

## §B1 — pure-real cores for the two-step Möbius branch

`φ_i ∘ φ_j (x) = u / (1 + d₁·u)` with `u = x + d₂`, `d₁ = i+1`, `d₂ = j+1`.
Its difference quotient is exactly `1 / (D(x)·D(y))` with `D(t) = 1 + d₁(t+d₂)`,
so the infimum of `|(φ_i ∘ φ_j)'|` on `[β,1]` is `1/D(1)² = 1/(1+d₁(1+d₂))²`.
This is STRICTLY larger than the product `a_i·a_j = 1/((d₁+1)(d₂+1))²` of the
two level-1 infima, and that gap is the entire source of the improvement. -/

/-- Composing two inverse-shift branches. -/
theorem inv_comp_eq {u d1 : ℝ} (hu : 0 < u) (hd1 : 0 ≤ d1) :
    1 / (1 / u + d1) = u / (1 + d1 * u) := by
  have h0 : (0 : ℝ) < 1 / u := one_div_pos.2 hu
  have h1 : (0 : ℝ) < 1 / u + d1 := by linarith
  have h2 : (0 : ℝ) < 1 + d1 * u := by nlinarith
  have hune : u ≠ 0 := ne_of_gt hu
  field_simp

/-- The Möbius difference identity for `u ↦ u/(1 + d₁u)`. -/
theorem mob2_abs_diff {d1 u v : ℝ} (hu : 0 < 1 + d1 * u) (hv : 0 < 1 + d1 * v) :
    |u / (1 + d1 * u) - v / (1 + d1 * v)| = |u - v| / ((1 + d1 * u) * (1 + d1 * v)) := by
  have hu' : (1 : ℝ) + d1 * u ≠ 0 := ne_of_gt hu
  have hv' : (1 : ℝ) + d1 * v ≠ 0 := ne_of_gt hv
  rw [div_sub_div _ _ hu' hv',
    show u * (1 + d1 * v) - (1 + d1 * u) * v = u - v by ring,
    abs_div, abs_of_pos (mul_pos hu hv)]

/-- **Level-2 antilipschitz core.**  On `(0,1]` the two-step branch expands
distances by at least `1/(1 + d₁(1+d₂))²`. -/
theorem mob2_anti {d1 d2 x y : ℝ} (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    |x - y| / ((1 + d1 * (1 + d2)) ^ 2)
      ≤ |(x + d2) / (1 + d1 * (x + d2)) - (y + d2) / (1 + d1 * (y + d2))| := by
  have hu : (0 : ℝ) < 1 + d1 * (x + d2) := by nlinarith
  have hv : (0 : ℝ) < 1 + d1 * (y + d2) := by nlinarith
  rw [mob2_abs_diff hu hv, show (x + d2) - (y + d2) = x - y by ring]
  have hM : (0 : ℝ) ≤ 1 + d1 * (1 + d2) := by nlinarith
  have hAM : 1 + d1 * (x + d2) ≤ 1 + d1 * (1 + d2) := by nlinarith
  have hBM : 1 + d1 * (y + d2) ≤ 1 + d1 * (1 + d2) := by nlinarith
  have hle : (1 + d1 * (x + d2)) * (1 + d1 * (y + d2)) ≤ (1 + d1 * (1 + d2)) ^ 2 := by
    have h := mul_le_mul hAM hBM hv.le hM
    nlinarith [h]
  have hpos : (0 : ℝ) < (1 + d1 * (x + d2)) * (1 + d1 * (y + d2)) := mul_pos hu hv
  gcongr

/-- `u ↦ u/(1 + d₁u)` is increasing. -/
theorem mob2_mono {d1 u v : ℝ} (_hd1 : 0 ≤ d1) (hu : 0 < 1 + d1 * u) (hv : 0 < 1 + d1 * v)
    (huv : u ≤ v) : u / (1 + d1 * u) ≤ v / (1 + d1 * v) := by
  rw [div_le_div_iff₀ hu hv]
  nlinarith

/-! ## §B2 — the level-2 branches and their clamped inverses -/

/-- The level-2 branch: outer digit `i`, inner digit `j`. -/
noncomputable def g2 (K : ℕ) (i j : Fin K) : ℝ → ℝ :=
  fun x => gaussIFS K i (gaussIFS K j x)

/-- The level-2 clamped inverse branch. -/
noncomputable def x2 (K : ℕ) (i j : Fin K) : ℝ → ℝ :=
  fun x => gpre K j (gpre K i x)

/-- The exact level-2 expansion constant `1/(1 + d₁(1+d₂))²`. -/
noncomputable def a2 (K : ℕ) (i j : Fin K) : ℝ :=
  1 / ((1 + (((i : ℕ) : ℝ) + 1) * (1 + (((j : ℕ) : ℝ) + 1))) ^ 2)

theorem a2_pos (K : ℕ) (i j : Fin K) : 0 < a2 K i j := by
  have hi : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold a2
  have : (0 : ℝ) < 1 + (((i : ℕ) : ℝ) + 1) * (1 + (((j : ℕ) : ℝ) + 1)) := by nlinarith
  positivity

/-- The closed Möbius form of the level-2 branch. -/
theorem gauss_comp_eq (K : ℕ) (i j : Fin K) {x : ℝ} (hx : x ∈ gaussJ K) :
    g2 K i j x
      = (x + (((j : ℕ) : ℝ) + 1)) / (1 + (((i : ℕ) : ℝ) + 1) * (x + (((j : ℕ) : ℝ) + 1))) := by
  have hx0 : 0 < x := gaussJ_pos hx
  have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hi : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hu : (0 : ℝ) < x + (((j : ℕ) : ℝ) + 1) := by linarith
  unfold g2
  rw [gaussIFS_eq, gaussIFS_eq]
  exact inv_comp_eq hu (by linarith)

theorem g2_mapsTo (K : ℕ) (i j : Fin K) : Set.MapsTo (g2 K i j) (gaussJ K) (gaussJ K) :=
  fun _ hx => gauss_mapsTo K i (gauss_mapsTo K j hx)

theorem x2_cont (K : ℕ) (i j : Fin K) : Continuous (x2 K i j) :=
  (continuous_gpre j).comp (continuous_gpre i)

theorem x2_at_beta (K : ℕ) (i j : Fin K) : x2 K i j (betaK K) = betaK K := by
  unfold x2
  rw [gpre_at_beta i, gpre_at_one j]

theorem x2_at_one (K : ℕ) (i j : Fin K) : x2 K i j 1 = 1 := by
  unfold x2
  rw [gpre_at_one i, gpre_at_beta j]

/-- **The level-2 cylinder trichotomy.**  The two-digit cylinders are ordered by
the outer digit DESCENDING and the inner digit ASCENDING; the composite branches
PRESERVE orientation. -/
theorem x2_cyl (K : ℕ) (i j i' j' : Fin K) {u : ℝ} (hu : u ∈ gaussJ K) :
    x2 K i' j' (g2 K i j u)
      = if (i : ℕ) < (i' : ℕ) ∨ ((i' : ℕ) = (i : ℕ) ∧ (j' : ℕ) < (j : ℕ)) then 1
        else if (i' : ℕ) = (i : ℕ) ∧ (j' : ℕ) = (j : ℕ) then u else betaK K := by
  have hju : gaussIFS K j u ∈ gaussJ K := gauss_mapsTo K j hu
  unfold x2 g2
  rw [gpre_on_cylinder i i' hju]
  rcases lt_trichotomy ((i' : ℕ)) ((i : ℕ)) with h | h | h
  · rw [if_pos h, gpre_at_one j', if_neg (by omega), if_neg (by omega)]
  · have hii : i' = i := Fin.ext h
    rw [if_neg (show ¬ ((i' : ℕ) < (i : ℕ)) by omega), if_pos hii,
      gpre_on_cylinder j j' hu]
    rcases lt_trichotomy ((j' : ℕ)) ((j : ℕ)) with h2 | h2 | h2
    · rw [if_pos h2, if_pos (Or.inr ⟨h, h2⟩)]
    · rw [if_neg (show ¬ ((j' : ℕ) < (j : ℕ)) by omega), if_pos (Fin.ext h2 : j' = j),
        if_neg (by omega), if_pos ⟨h, h2⟩]
    · rw [if_neg (show ¬ ((j' : ℕ) < (j : ℕ)) by omega),
        if_neg (fun hc => absurd (congrArg Fin.val hc) (by omega : (j' : ℕ) ≠ (j : ℕ))),
        if_neg (by omega), if_neg (by omega)]
  · rw [if_neg (show ¬ ((i' : ℕ) < (i : ℕ)) by omega),
      if_neg (fun hc => absurd (congrArg Fin.val hc) (by omega : (i' : ℕ) ≠ (i : ℕ))),
      gpre_at_beta j', if_pos (Or.inl h)]

/-- **At most one free level-2 word.**  A level-2 inverse branch lands strictly
inside the interval only if BOTH its digits are free, and each is unique. -/
theorem x2_uniq (K : ℕ) {x : ℝ} {i j i' j' : Fin K}
    (h1 : x2 K i j x ≠ betaK K) (h2 : x2 K i j x ≠ 1)
    (h3 : x2 K i' j' x ≠ betaK K) (h4 : x2 K i' j' x ≠ 1) :
    i = i' ∧ j = j' := by
  have key : ∀ (q r : Fin K), x2 K q r x ≠ betaK K → x2 K q r x ≠ 1 →
      gfree K q x ∧ gfree K r (gpre K q x) := by
    intro q r hA hB
    have hq : gfree K q x := by
      by_contra hc
      rcases gpre_clamped hc with h | h
      · refine hB ?_
        show gpre K r (gpre K q x) = 1
        rw [h, gpre_at_beta r]
      · refine hA ?_
        show gpre K r (gpre K q x) = betaK K
        rw [h, gpre_at_one r]
    refine ⟨hq, ?_⟩
    by_contra hc
    rcases gpre_clamped hc with h | h
    · exact hA h
    · exact hB h
  obtain ⟨hi1, hj1⟩ := key i j h1 h2
  obtain ⟨hi2, hj2⟩ := key i' j' h3 h4
  have hii : i = i' := gfree_unique hi1 hi2
  subst hii
  exact ⟨rfl, gfree_unique hj1 hj2⟩

/-! ## §B3 — the level-2 metric estimates -/

/-- **Level-2 antilipschitz bound** with the EXACT two-step constant. -/
theorem g2_anti (K : ℕ) (i j : Fin K) {x y : ℝ} (hx : x ∈ gaussJ K) (hy : y ∈ gaussJ K) :
    a2 K i j * |x - y| ≤ |g2 K i j x - g2 K i j y| := by
  have hd1 : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
  have hd2 : (0 : ℝ) < ((j : ℕ) : ℝ) + 1 := by positivity
  rw [gauss_comp_eq K i j hx, gauss_comp_eq K i j hy]
  have h := mob2_anti hd1 hd2 (gaussJ_pos hx) hx.2 (gaussJ_pos hy) hy.2
  unfold a2
  rw [div_mul_eq_mul_div, one_mul]
  exact h

/-- **Level-2 uniform contraction**: the square of the level-1 constant. -/
theorem g2_lip (K : ℕ) (i j : Fin K) {x y : ℝ} (hx : x ∈ gaussJ K) (hy : y ∈ gaussJ K) :
    |g2 K i j x - g2 K i j y| ≤ LmaxK K ^ 2 * |x - y| := by
  have hL : (0 : ℝ) < LmaxK K := LmaxK_pos
  have h1 := gauss_lip_real i (gauss_mapsTo K j hx) (gauss_mapsTo K j hy)
  have h2 := gauss_lip_real j hx hy
  calc |g2 K i j x - g2 K i j y| ≤ LmaxK K * |gaussIFS K j x - gaussIFS K j y| := h1
    _ ≤ LmaxK K * (LmaxK K * |x - y|) := mul_le_mul_of_nonneg_left h2 hL.le
    _ = LmaxK K ^ 2 * |x - y| := by ring

theorem LmaxK_sq_lt_one (K : ℕ) : LmaxK K ^ 2 < 1 := by
  have h1 : (0 : ℝ) < LmaxK K := LmaxK_pos
  have h2 : LmaxK K < 1 := LmaxK_lt_one
  nlinarith

/-- Lower endpoint of the level-2 cylinder. -/
theorem g2_ge (K : ℕ) (i j : Fin K) {x : ℝ} (hx : x ∈ gaussJ K) :
    (betaK K + (((j : ℕ) : ℝ) + 1))
        / (1 + (((i : ℕ) : ℝ) + 1) * (betaK K + (((j : ℕ) : ℝ) + 1)))
      ≤ g2 K i j x := by
  have hi : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb : (0 : ℝ) < betaK K := betaK_pos
  have hxb : betaK K ≤ x := hx.1
  have hu : (0 : ℝ) < 1 + (((i : ℕ) : ℝ) + 1) * (betaK K + (((j : ℕ) : ℝ) + 1)) := by nlinarith
  have hv : (0 : ℝ) < 1 + (((i : ℕ) : ℝ) + 1) * (x + (((j : ℕ) : ℝ) + 1)) := by nlinarith
  rw [gauss_comp_eq K i j hx]
  exact mob2_mono (by linarith) hu hv (by linarith)

/-- Upper endpoint of the level-2 cylinder. -/
theorem g2_le (K : ℕ) (i j : Fin K) {x : ℝ} (hx : x ∈ gaussJ K) :
    g2 K i j x
      ≤ (1 + (((j : ℕ) : ℝ) + 1)) / (1 + (((i : ℕ) : ℝ) + 1) * (1 + (((j : ℕ) : ℝ) + 1))) := by
  have hi : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hx0 : 0 < x := gaussJ_pos hx
  have hx1 : x ≤ 1 := hx.2
  have hu : (0 : ℝ) < 1 + (((i : ℕ) : ℝ) + 1) * (1 + (((j : ℕ) : ℝ) + 1)) := by nlinarith
  have hv : (0 : ℝ) < 1 + (((i : ℕ) : ℝ) + 1) * (x + (((j : ℕ) : ℝ) + 1)) := by nlinarith
  rw [gauss_comp_eq K i j hx]
  exact mob2_mono (by linarith) hv hu (by linarith)

/-! ## §B4 — level-2 self-covering and forward invariance -/

theorem g2_selfCover {K : ℕ} {E : Set ℝ} (hself : E ⊆ ⋃ j, gaussIFS K j '' E) :
    E ⊆ ⋃ q : Fin K × Fin K, g2 K q.1 q.2 '' E := by
  intro x hx
  obtain ⟨i, y, hyE, hxy⟩ := Set.mem_iUnion.1 (hself hx)
  obtain ⟨j, z, hzE, hyz⟩ := Set.mem_iUnion.1 (hself hyE)
  refine Set.mem_iUnion.2 ⟨(i, j), z, hzE, ?_⟩
  show gaussIFS K i (gaussIFS K j z) = x
  rw [hyz, hxy]

theorem g2_invariant {K : ℕ} {E : Set ℝ} (i j : Fin K)
    (hinv : ∀ j : Fin K, Set.MapsTo (gaussIFS K j) E E) :
    Set.MapsTo (g2 K i j) E E :=
  fun _ hx => hinv i (hinv j hx)

/-! ## §B5 — the `K = 3` level-2 system: nine words

The nine two-digit cylinders, listed LEFT to RIGHT on the line, are
`(d₁,d₂) = (3,1),(3,2),(3,3),(2,1),(2,2),(2,3),(1,1),(1,2),(1,3)`:
the outer digit descends, the inner digit ascends.  Their closures are

`[5/19,2/7] [9/31,3/10] [13/43,4/13] [5/14,2/5] [9/22,3/7] [13/30,4/9]`
`[5/9,2/3] [9/13,3/4] [13/17,4/5]`

and the minimal gap between consecutive ones is `13/43 − 3/10 = 1/430`. -/

/-- Outer digit of the `m`-th level-2 word, `K = 3`. -/
def I3 : Fin 9 → Fin 3 := ![2, 2, 2, 1, 1, 1, 0, 0, 0]

/-- Inner digit of the `m`-th level-2 word, `K = 3`. -/
def D3 : Fin 9 → Fin 3 := ![0, 1, 2, 0, 1, 2, 0, 1, 2]

/-- The `m`-th level-2 branch, `K = 3`. -/
noncomputable def psi3 : Fin 9 → ℝ → ℝ := fun m => g2 3 (I3 m) (D3 m)

/-- The `m`-th level-2 clamped inverse branch, `K = 3`. -/
noncomputable def chi3 : Fin 9 → ℝ → ℝ := fun m => x2 3 (I3 m) (D3 m)

theorem ord3 (m m' : Fin 9) :
    ((I3 m : ℕ) < (I3 m' : ℕ) ∨ ((I3 m' : ℕ) = (I3 m : ℕ) ∧ (D3 m' : ℕ) < (D3 m : ℕ)))
      ↔ (m' : ℕ) < (m : ℕ) := by
  revert m m'
  decide

theorem eq3 (m m' : Fin 9) :
    ((I3 m' : ℕ) = (I3 m : ℕ) ∧ (D3 m' : ℕ) = (D3 m : ℕ)) ↔ m' = m := by
  revert m m'
  decide

theorem inj3 (m m' : Fin 9) (h1 : I3 m = I3 m') (h2 : D3 m = D3 m') : m = m' := by
  revert h1 h2
  revert m m'
  decide

theorem surj3 (i j : Fin 3) : ∃ m : Fin 9, I3 m = i ∧ D3 m = j := by
  revert i j
  decide

theorem chi3_cyl (m m' : Fin 9) {u : ℝ} (hu : u ∈ gaussJ 3) :
    chi3 m' (psi3 m u) = if (m' : ℕ) < (m : ℕ) then 1 else if m' = m then u else betaK 3 := by
  show x2 3 (I3 m') (D3 m') (g2 3 (I3 m) (D3 m) u) = _
  rw [x2_cyl 3 (I3 m) (D3 m) (I3 m') (D3 m') hu]
  by_cases h1 : (m' : ℕ) < (m : ℕ)
  · rw [if_pos h1, if_pos ((ord3 m m').2 h1)]
  · rw [if_neg h1, if_neg (fun hc => h1 ((ord3 m m').1 hc))]
    by_cases h2 : m' = m
    · rw [if_pos h2, if_pos ((eq3 m m').2 h2)]
    · rw [if_neg h2, if_neg (fun hc => h2 ((eq3 m m').1 hc))]

/-- Left endpoints of the nine level-2 cylinders. -/
noncomputable def Lo3 : Fin 9 → ℝ :=
  ![5/19, 9/31, 13/43, 5/14, 9/22, 13/30, 5/9, 9/13, 13/17]

/-- Right endpoints of the nine level-2 cylinders. -/
noncomputable def Hi3 : Fin 9 → ℝ :=
  ![2/7, 3/10, 4/13, 2/5, 3/7, 4/9, 2/3, 3/4, 4/5]

theorem bd3_lo (m : Fin 9) {x : ℝ} (hx : x ∈ gaussJ 3) : Lo3 m ≤ psi3 m x := by
  fin_cases m <;> refine le_trans ?_ (g2_ge 3 _ _ hx) <;> norm_num [Lo3, I3, D3, betaK]

theorem bd3_hi (m : Fin 9) {x : ℝ} (hx : x ∈ gaussJ 3) : psi3 m x ≤ Hi3 m := by
  fin_cases m <;> refine le_trans (g2_le 3 _ _ hx) ?_ <;> norm_num [Hi3, I3, D3, betaK]

theorem gap3 (m m' : Fin 9) (h : (m' : ℕ) < (m : ℕ)) : Hi3 m' + 1/430 ≤ Lo3 m := by
  fin_cases m <;> fin_cases m' <;>
    first
      | exact absurd h (by decide)
      | norm_num [Lo3, Hi3]

theorem sep3 (m m' : Fin 9) (hmm : m ≠ m') {x y : ℝ}
    (hx : x ∈ gaussJ 3) (hy : y ∈ gaussJ 3) :
    (1 : ℝ)/430 ≤ |psi3 m x - psi3 m' y| := by
  have hne : (m : ℕ) ≠ (m' : ℕ) := fun hc => hmm (Fin.ext hc)
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := bd3_hi m hx
    have h2 := bd3_lo m' hy
    have h3 := gap3 m' m h
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self (psi3 m' y - psi3 m x))
  · have h1 := bd3_lo m hx
    have h2 := bd3_hi m' hy
    have h3 := gap3 m m' h
    exact le_trans (by linarith) (le_abs_self (psi3 m x - psi3 m' y))

/-- The nine level-2 expansion constants, `K = 3`. -/
noncomputable def av3 : Fin 9 → ℝ := ![1/49, 1/100, 1/169, 1/25, 1/49, 1/81, 1/9, 1/16, 1/25]

theorem a2_val3 (m : Fin 9) : a2 3 (I3 m) (D3 m) = av3 m := by
  fin_cases m <;> norm_num [a2, I3, D3, av3]

/-- **The `K = 3` level-2 system as an `AddrIFS`.**  Nine words, orientation
PRESERVING, separation `1/430`, weights summing to exactly `1`. -/
noncomputable def gaussTwo3 : AddrIFS 9 where
  lo := betaK 3
  hi := 1
  ψ := psi3
  χ := chi3
  flip := false
  a := fun m => a2 3 (I3 m) (D3 m)
  p := ![846/10000, 540/10000, 388/10000, 1293/10000, 846/10000, 616/10000,
        2465/10000, 1713/10000, 1293/10000]
  c := 2465/10000
  L := LmaxK 3 ^ 2
  γ := 1/430
  lo_lt_hi := betaK_lt_one (by norm_num)
  diam_lt_one := by have := betaK_pos (K := 3); linarith
  p_pos := by intro m; fin_cases m <;> norm_num
  p_sum := by norm_num [Fin.sum_univ_succ]
  p_le_c := by intro m; fin_cases m <;> norm_num
  c_lt_one := by norm_num
  a_pos := fun m => a2_pos 3 _ _
  gamma_pos := by norm_num
  L_pos := pow_pos LmaxK_pos 2
  L_lt_one := LmaxK_sq_lt_one 3
  anti := by intro m x y hx hy; exact g2_anti 3 (I3 m) (D3 m) hx hy
  lip := by intro m x y hx hy; exact g2_lip 3 (I3 m) (D3 m) hx hy
  sep := by intro m m' hmm x y hx hy; exact sep3 m m' hmm hx hy
  chi_cont := fun m => x2_cont 3 _ _
  chi_lo := fun m => by simpa using x2_at_beta 3 (I3 m) (D3 m)
  chi_hi := fun m => by simpa using x2_at_one 3 (I3 m) (D3 m)
  chi_cyl := by intro m m' u hu; exact chi3_cyl m m' hu
  chi_uniq := by
    intro x m m' h1 h2 h3 h4
    obtain ⟨hI, hD⟩ := x2_uniq 3 h1 h2 h3 h4
    exact inj3 m m' hI hD

/-- The nine weight/expansion comparisons at `s = 63/100`, certified by exact
integer arithmetic through `le_rpow_of_pow_le`. -/
theorem p3_le_rpow (m : Fin 9) : gaussTwo3.p m ≤ gaussTwo3.a m ^ ((63 : ℝ) / 100) := by
  have hA : gaussTwo3.a m = av3 m := a2_val3 m
  rw [hA]
  fin_cases m
  · show (846/10000 : ℝ) ≤ (1/49 : ℝ) ^ ((63 : ℝ) / 100)
    exact le_rpow_of_pow_le (x := (1/49 : ℝ)) (u := (846/10000 : ℝ))
      (pn := 63) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (540/10000 : ℝ) ≤ (1/100 : ℝ) ^ ((63 : ℝ) / 100)
    exact le_rpow_of_pow_le (x := (1/100 : ℝ)) (u := (540/10000 : ℝ))
      (pn := 63) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (388/10000 : ℝ) ≤ (1/169 : ℝ) ^ ((63 : ℝ) / 100)
    exact le_rpow_of_pow_le (x := (1/169 : ℝ)) (u := (388/10000 : ℝ))
      (pn := 63) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (1293/10000 : ℝ) ≤ (1/25 : ℝ) ^ ((63 : ℝ) / 100)
    exact le_rpow_of_pow_le (x := (1/25 : ℝ)) (u := (1293/10000 : ℝ))
      (pn := 63) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (846/10000 : ℝ) ≤ (1/49 : ℝ) ^ ((63 : ℝ) / 100)
    exact le_rpow_of_pow_le (x := (1/49 : ℝ)) (u := (846/10000 : ℝ))
      (pn := 63) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (616/10000 : ℝ) ≤ (1/81 : ℝ) ^ ((63 : ℝ) / 100)
    exact le_rpow_of_pow_le (x := (1/81 : ℝ)) (u := (616/10000 : ℝ))
      (pn := 63) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (2465/10000 : ℝ) ≤ (1/9 : ℝ) ^ ((63 : ℝ) / 100)
    exact le_rpow_of_pow_le (x := (1/9 : ℝ)) (u := (2465/10000 : ℝ))
      (pn := 63) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (1713/10000 : ℝ) ≤ (1/16 : ℝ) ^ ((63 : ℝ) / 100)
    exact le_rpow_of_pow_le (x := (1/16 : ℝ)) (u := (1713/10000 : ℝ))
      (pn := 63) (q := 100) (by norm_num) (by norm_num) (by norm_num)
  · show (1293/10000 : ℝ) ≤ (1/25 : ℝ) ^ ((63 : ℝ) / 100)
    exact le_rpow_of_pow_le (x := (1/25 : ℝ)) (u := (1293/10000 : ℝ))
      (pn := 63) (q := 100) (by norm_num) (by norm_num) (by norm_num)

/-- **LEVEL-2 LOWER BOUND, `K = 3`.**  Any nonempty closed `E ⊆ [1/4, 1]` which
is forward invariant and backward covered by the three Gauss branches has
`dim_H E ≥ 0.63`.

Improves r209's `0.54`.  Still a Bernoulli bound, on two-digit cylinders; the
level-2 inf-Moran root is `0.6353935…` and the true value is `0.7056609…`. -/
theorem le_dimH_gauss_three_level_two {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3) (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 3, Set.MapsTo (gaussIFS 3 j) E E) :
    ENNReal.ofReal ((63 : ℝ) / 100) ≤ dimH E := by
  refine gaussTwo3.le_dimH (by norm_num) hEJ ?_ hne hclosed ?_ p3_le_rpow
  · intro x hx
    obtain ⟨q, z, hzE, hz⟩ := Set.mem_iUnion.1 (g2_selfCover hself hx)
    obtain ⟨m, hm1, hm2⟩ := surj3 q.1 q.2
    refine Set.mem_iUnion.2 ⟨m, z, hzE, ?_⟩
    show g2 3 (I3 m) (D3 m) z = x
    rw [hm1, hm2]
    exact hz
  · intro m
    exact g2_invariant (I3 m) (D3 m) hinv

/-- **LEVEL-2 ENCLOSURE, `K = 3`.**  `0.63 ≤ dim_H E ≤ 0.77`.

Lower bound: this file.  Upper bound: r208.  TRUE value `0.7056609…`
(Jenkinson–Pollicott).  Neither endpoint is an approximation to it; the gap
narrows (from `[0.54, 0.77]`) but is NOT closed. -/
theorem dimH_gauss_three_enclosure_two {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3) (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 3, Set.MapsTo (gaussIFS 3 j) E E) :
    ENNReal.ofReal ((63 : ℝ) / 100) ≤ dimH E ∧ dimH E ≤ (77 / 100 : ℝ≥0∞) :=
  ⟨le_dimH_gauss_three_level_two hEJ hself hne hclosed hinv,
    PrincipiaTractalis.GaussDimension.dimH_gauss_three_le_two hEJ hself⟩

/-! ## §B6 — the `K = 2` level-2 system: four words

The four two-digit cylinders, LEFT to RIGHT, are
`(d₁,d₂) = (2,1),(2,2),(1,1),(1,2)` with closures
`[4/11,2/5] [7/17,3/7] [4/7,2/3] [7/10,3/4]`, minimal gap
`7/17 − 2/5 = 1/85`. -/

/-- Outer digit of the `m`-th level-2 word, `K = 2`. -/
def I2 : Fin 4 → Fin 2 := ![1, 1, 0, 0]

/-- Inner digit of the `m`-th level-2 word, `K = 2`. -/
def D2 : Fin 4 → Fin 2 := ![0, 1, 0, 1]

/-- The `m`-th level-2 branch, `K = 2`. -/
noncomputable def psi2 : Fin 4 → ℝ → ℝ := fun m => g2 2 (I2 m) (D2 m)

/-- The `m`-th level-2 clamped inverse branch, `K = 2`. -/
noncomputable def chi2 : Fin 4 → ℝ → ℝ := fun m => x2 2 (I2 m) (D2 m)

theorem ord2 (m m' : Fin 4) :
    ((I2 m : ℕ) < (I2 m' : ℕ) ∨ ((I2 m' : ℕ) = (I2 m : ℕ) ∧ (D2 m' : ℕ) < (D2 m : ℕ)))
      ↔ (m' : ℕ) < (m : ℕ) := by
  revert m m'
  decide

theorem eq2 (m m' : Fin 4) :
    ((I2 m' : ℕ) = (I2 m : ℕ) ∧ (D2 m' : ℕ) = (D2 m : ℕ)) ↔ m' = m := by
  revert m m'
  decide

theorem inj2 (m m' : Fin 4) (h1 : I2 m = I2 m') (h2 : D2 m = D2 m') : m = m' := by
  revert h1 h2
  revert m m'
  decide

theorem surj2 (i j : Fin 2) : ∃ m : Fin 4, I2 m = i ∧ D2 m = j := by
  revert i j
  decide

theorem chi2_cyl (m m' : Fin 4) {u : ℝ} (hu : u ∈ gaussJ 2) :
    chi2 m' (psi2 m u) = if (m' : ℕ) < (m : ℕ) then 1 else if m' = m then u else betaK 2 := by
  show x2 2 (I2 m') (D2 m') (g2 2 (I2 m) (D2 m) u) = _
  rw [x2_cyl 2 (I2 m) (D2 m) (I2 m') (D2 m') hu]
  by_cases h1 : (m' : ℕ) < (m : ℕ)
  · rw [if_pos h1, if_pos ((ord2 m m').2 h1)]
  · rw [if_neg h1, if_neg (fun hc => h1 ((ord2 m m').1 hc))]
    by_cases h2 : m' = m
    · rw [if_pos h2, if_pos ((eq2 m m').2 h2)]
    · rw [if_neg h2, if_neg (fun hc => h2 ((eq2 m m').1 hc))]

/-- Left endpoints of the four level-2 cylinders. -/
noncomputable def Lo2 : Fin 4 → ℝ := ![4/11, 7/17, 4/7, 7/10]

/-- Right endpoints of the four level-2 cylinders. -/
noncomputable def Hi2 : Fin 4 → ℝ := ![2/5, 3/7, 2/3, 3/4]

theorem bd2_lo (m : Fin 4) {x : ℝ} (hx : x ∈ gaussJ 2) : Lo2 m ≤ psi2 m x := by
  fin_cases m <;> refine le_trans ?_ (g2_ge 2 _ _ hx) <;> norm_num [Lo2, I2, D2, betaK]

theorem bd2_hi (m : Fin 4) {x : ℝ} (hx : x ∈ gaussJ 2) : psi2 m x ≤ Hi2 m := by
  fin_cases m <;> refine le_trans (g2_le 2 _ _ hx) ?_ <;> norm_num [Hi2, I2, D2, betaK]

theorem gap2 (m m' : Fin 4) (h : (m' : ℕ) < (m : ℕ)) : Hi2 m' + 1/85 ≤ Lo2 m := by
  fin_cases m <;> fin_cases m' <;>
    first
      | exact absurd h (by decide)
      | norm_num [Lo2, Hi2]

theorem sep2 (m m' : Fin 4) (hmm : m ≠ m') {x y : ℝ}
    (hx : x ∈ gaussJ 2) (hy : y ∈ gaussJ 2) :
    (1 : ℝ)/85 ≤ |psi2 m x - psi2 m' y| := by
  have hne : (m : ℕ) ≠ (m' : ℕ) := fun hc => hmm (Fin.ext hc)
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := bd2_hi m hx
    have h2 := bd2_lo m' hy
    have h3 := gap2 m' m h
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self (psi2 m' y - psi2 m x))
  · have h1 := bd2_lo m hx
    have h2 := bd2_hi m' hy
    have h3 := gap2 m m' h
    exact le_trans (by linarith) (le_abs_self (psi2 m x - psi2 m' y))

/-- The four level-2 expansion constants, `K = 2`. -/
noncomputable def av2 : Fin 4 → ℝ := ![1/25, 1/49, 1/9, 1/16]

theorem a2_val2 (m : Fin 4) : a2 2 (I2 m) (D2 m) = av2 m := by
  fin_cases m <;> norm_num [a2, I2, D2, av2]

/-- **The `K = 2` level-2 system as an `AddrIFS`.**  Four words, orientation
PRESERVING, separation `1/85`, weights summing to exactly `1`. -/
noncomputable def gaussTwo2 : AddrIFS 4 where
  lo := betaK 2
  hi := 1
  ψ := psi2
  χ := chi2
  flip := false
  a := fun m => a2 2 (I2 m) (D2 m)
  p := ![2192/10000, 1608/10000, 3509/10000, 2691/10000]
  c := 3509/10000
  L := LmaxK 2 ^ 2
  γ := 1/85
  lo_lt_hi := betaK_lt_one (by norm_num)
  diam_lt_one := by have := betaK_pos (K := 2); linarith
  p_pos := by intro m; fin_cases m <;> norm_num
  p_sum := by norm_num [Fin.sum_univ_succ]
  p_le_c := by intro m; fin_cases m <;> norm_num
  c_lt_one := by norm_num
  a_pos := fun m => a2_pos 2 _ _
  gamma_pos := by norm_num
  L_pos := pow_pos LmaxK_pos 2
  L_lt_one := LmaxK_sq_lt_one 2
  anti := by intro m x y hx hy; exact g2_anti 2 (I2 m) (D2 m) hx hy
  lip := by intro m x y hx hy; exact g2_lip 2 (I2 m) (D2 m) hx hy
  sep := by intro m m' hmm x y hx hy; exact sep2 m m' hmm hx hy
  chi_cont := fun m => x2_cont 2 _ _
  chi_lo := fun m => by simpa using x2_at_beta 2 (I2 m) (D2 m)
  chi_hi := fun m => by simpa using x2_at_one 2 (I2 m) (D2 m)
  chi_cyl := by intro m m' u hu; exact chi2_cyl m m' hu
  chi_uniq := by
    intro x m m' h1 h2 h3 h4
    obtain ⟨hI, hD⟩ := x2_uniq 2 h1 h2 h3 h4
    exact inj2 m m' hI hD

/-- The four weight/expansion comparisons at `s = 23/50`. -/
theorem p2_le_rpow (m : Fin 4) : gaussTwo2.p m ≤ gaussTwo2.a m ^ ((23 : ℝ) / 50) := by
  have hA : gaussTwo2.a m = av2 m := a2_val2 m
  rw [hA]
  fin_cases m
  · show (2192/10000 : ℝ) ≤ (1/25 : ℝ) ^ ((23 : ℝ) / 50)
    exact le_rpow_of_pow_le (x := (1/25 : ℝ)) (u := (2192/10000 : ℝ))
      (pn := 23) (q := 50) (by norm_num) (by norm_num) (by norm_num)
  · show (1608/10000 : ℝ) ≤ (1/49 : ℝ) ^ ((23 : ℝ) / 50)
    exact le_rpow_of_pow_le (x := (1/49 : ℝ)) (u := (1608/10000 : ℝ))
      (pn := 23) (q := 50) (by norm_num) (by norm_num) (by norm_num)
  · show (3509/10000 : ℝ) ≤ (1/9 : ℝ) ^ ((23 : ℝ) / 50)
    exact le_rpow_of_pow_le (x := (1/9 : ℝ)) (u := (3509/10000 : ℝ))
      (pn := 23) (q := 50) (by norm_num) (by norm_num) (by norm_num)
  · show (2691/10000 : ℝ) ≤ (1/16 : ℝ) ^ ((23 : ℝ) / 50)
    exact le_rpow_of_pow_le (x := (1/16 : ℝ)) (u := (2691/10000 : ℝ))
      (pn := 23) (q := 50) (by norm_num) (by norm_num) (by norm_num)

/-- **LEVEL-2 LOWER BOUND, `K = 2`.**  Any nonempty closed `E ⊆ [1/3, 1]` which
is forward invariant and backward covered by the two Gauss branches has
`dim_H E ≥ 0.46`.

Improves r209's `0.39`.  The level-2 inf-Moran root is `0.4729948…`; the true
value is `0.5312805…`. -/
theorem le_dimH_gauss_two_level_two {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2) (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 2, Set.MapsTo (gaussIFS 2 j) E E) :
    ENNReal.ofReal ((23 : ℝ) / 50) ≤ dimH E := by
  refine gaussTwo2.le_dimH (by norm_num) hEJ ?_ hne hclosed ?_ p2_le_rpow
  · intro x hx
    obtain ⟨q, z, hzE, hz⟩ := Set.mem_iUnion.1 (g2_selfCover hself hx)
    obtain ⟨m, hm1, hm2⟩ := surj2 q.1 q.2
    refine Set.mem_iUnion.2 ⟨m, z, hzE, ?_⟩
    show g2 2 (I2 m) (D2 m) z = x
    rw [hm1, hm2]
    exact hz
  · intro m
    exact g2_invariant (I2 m) (D2 m) hinv

/-- **LEVEL-2 ENCLOSURE, `K = 2`.**  `0.46 ≤ dim_H E ≤ 0.58`.

Lower bound: this file.  Upper bound: r208.  TRUE value `0.5312805…`
(Jenkinson–Pollicott).  The gap narrows (from `[0.39, 0.58]`) but is NOT
closed. -/
theorem dimH_gauss_two_enclosure_two {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2) (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 2, Set.MapsTo (gaussIFS 2 j) E E) :
    ENNReal.ofReal ((23 : ℝ) / 50) ≤ dimH E ∧ dimH E ≤ (29 / 50 : ℝ≥0∞) :=
  ⟨le_dimH_gauss_two_level_two hEJ hself hne hclosed hinv,
    PrincipiaTractalis.GaussDimension.dimH_gauss_two_le_two hEJ hself⟩

/-! ## §B7 — tightened level-2 UPPER bounds (optional refinement of r208)

r208 certified `77/100` (`K = 3`) and `29/50` (`K = 2`), both comfortably above
the level-2 upper Moran roots `0.7618933…` and `0.5699524…`.  Pushing the
exponent down to `61/80 = 0.7625` and `4/7 = 0.5714285…` still leaves the Moran
sum below `1` (`0.99874` and `0.9976` with the rational bounds used here) and
costs nothing but bigger integers.  These are the tightest UPPER bounds this
project has for the Gauss continued-fraction sets.

They remain UPPER bounds only, and neither is an approximation to the true
value. -/

open PrincipiaTractalis.GaussDimension

/-- The nine `61/80`-powers sum to at most `99874/100000 ≤ 1`. -/
theorem sum_cgauss2_three_rpow_le_one' :
    (∑ q : Fin 3 × Fin 3, cgauss2 3 q.1 q.2 ^ ((61 : ℝ) / 80)) ≤ (1 : ℝ≥0) := by
  have e00 : ((16 : ℝ≥0) / 81) ^ ((61 : ℝ) / 80) ≤ 29038 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 61) (q := 80) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e01 : ((16 : ℝ≥0) / 169) ^ ((61 : ℝ) / 80) ≤ 16576 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 61) (q := 80) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e02 : ((16 : ℝ≥0) / 289) ^ ((61 : ℝ) / 80) ≤ 11011 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 61) (q := 80) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e10 : ((4 : ℝ≥0) / 49) ^ ((61 : ℝ) / 80) ≤ 14805 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 61) (q := 80) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e11 : ((4 : ℝ≥0) / 121) ^ ((61 : ℝ) / 80) ≤ 7433 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 61) (q := 80) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e12 : ((4 : ℝ≥0) / 225) ^ ((61 : ℝ) / 80) ≤ 4633 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 61) (q := 80) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e20 : ((16 : ℝ≥0) / 361) ^ ((61 : ℝ) / 80) ≤ 9294 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 61) (q := 80) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e21 : ((16 : ℝ≥0) / 961) ^ ((61 : ℝ) / 80) ≤ 4407 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 61) (q := 80) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e22 : ((16 : ℝ≥0) / 1849) ^ ((61 : ℝ) / 80) ≤ 2677 / 100000 :=
    nnreal_rpow_le_of_pow_le (p := 61) (q := 80) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, cgauss2_three_00, cgauss2_three_01, cgauss2_three_02,
    cgauss2_three_10, cgauss2_three_11, cgauss2_three_12,
    cgauss2_three_20, cgauss2_three_21, cgauss2_three_22]
  calc ((16 : ℝ≥0) / 81) ^ ((61 : ℝ) / 80) + ((16 : ℝ≥0) / 169) ^ ((61 : ℝ) / 80)
        + ((16 : ℝ≥0) / 289) ^ ((61 : ℝ) / 80)
      + (((4 : ℝ≥0) / 49) ^ ((61 : ℝ) / 80) + ((4 : ℝ≥0) / 121) ^ ((61 : ℝ) / 80)
        + ((4 : ℝ≥0) / 225) ^ ((61 : ℝ) / 80))
      + (((16 : ℝ≥0) / 361) ^ ((61 : ℝ) / 80) + ((16 : ℝ≥0) / 961) ^ ((61 : ℝ) / 80)
        + ((16 : ℝ≥0) / 1849) ^ ((61 : ℝ) / 80))
      ≤ (29038 / 100000 : ℝ≥0) + 16576 / 100000 + 11011 / 100000
        + (14805 / 100000 + 7433 / 100000 + 4633 / 100000)
        + (9294 / 100000 + 4407 / 100000 + 2677 / 100000) := by gcongr
    _ ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num

/-- **TIGHTENED UPPER BOUND, `K = 3`.**  `dim_H E ≤ 61/80 = 0.7625`, improving
r208's `77/100`.  The level-2 upper Moran root is `0.7618933…`; the true value
is `0.7056609…`, and `0.7625` is **not** an approximation to it. -/
theorem dimH_gauss_three_le_two' {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3) (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E) :
    dimH E ≤ (61 / 80 : ℝ≥0∞) := by
  have hd : (((61 / 80 : ℝ≥0)) : ℝ) = (61 : ℝ) / 80 := by push_cast; norm_num
  have hcast : (∑ q : Fin 3 × Fin 3, (cgauss2 3 q.1 q.2 : ℝ≥0∞) ^ (((61 / 80 : ℝ≥0)) : ℝ))
      = ((∑ q : Fin 3 × Fin 3, cgauss2 3 q.1 q.2 ^ ((61 : ℝ) / 80) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_finset_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hd, ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0 : ℝ) ≤ 61 / 80)]
  have hsum : (∑ q : Fin 3 × Fin 3, (cgauss2 3 q.1 q.2 : ℝ≥0∞) ^ (((61 / 80 : ℝ≥0)) : ℝ))
      ≤ 1 := by
    rw [hcast]
    exact_mod_cast sum_cgauss2_three_rpow_le_one'
  have h := dimH_gauss_le_two (K := 3) (d := (61 / 80 : ℝ≥0)) hEJ hself hsum
  refine h.trans ?_
  norm_num

/-- The four `4/7`-powers sum to at most `9976/10000 ≤ 1`. -/
theorem sum_cgauss2_two_rpow_le_one' :
    (∑ q : Fin 2 × Fin 2, cgauss2 2 q.1 q.2 ^ ((4 : ℝ) / 7)) ≤ (1 : ℝ≥0) := by
  have e00 : ((9 : ℝ≥0) / 49) ^ ((4 : ℝ) / 7) ≤ 3800 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 4) (q := 7) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e01 : ((9 : ℝ≥0) / 100) ^ ((4 : ℝ) / 7) ≤ 2528 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 4) (q := 7) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e10 : ((9 : ℝ≥0) / 121) ^ ((4 : ℝ) / 7) ≤ 2268 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 4) (q := 7) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have e11 : ((9 : ℝ≥0) / 289) ^ ((4 : ℝ) / 7) ≤ 1380 / 10000 :=
    nnreal_rpow_le_of_pow_le (p := 4) (q := 7) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, cgauss2_two_00, cgauss2_two_01,
    cgauss2_two_10, cgauss2_two_11]
  calc ((9 : ℝ≥0) / 49) ^ ((4 : ℝ) / 7) + ((9 : ℝ≥0) / 100) ^ ((4 : ℝ) / 7)
      + (((9 : ℝ≥0) / 121) ^ ((4 : ℝ) / 7) + ((9 : ℝ≥0) / 289) ^ ((4 : ℝ) / 7))
      ≤ (3800 / 10000 : ℝ≥0) + 2528 / 10000 + (2268 / 10000 + 1380 / 10000) := by gcongr
    _ ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num

/-- **TIGHTENED UPPER BOUND, `K = 2`.**  `dim_H E ≤ 4/7 = 0.5714285…`, improving
r208's `29/50`.  The level-2 upper Moran root is `0.5699524…`; the true value is
`0.5312805…`. -/
theorem dimH_gauss_two_le_two' {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2) (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E) :
    dimH E ≤ (4 / 7 : ℝ≥0∞) := by
  have hd : (((4 / 7 : ℝ≥0)) : ℝ) = (4 : ℝ) / 7 := by push_cast; norm_num
  have hcast : (∑ q : Fin 2 × Fin 2, (cgauss2 2 q.1 q.2 : ℝ≥0∞) ^ (((4 / 7 : ℝ≥0)) : ℝ))
      = ((∑ q : Fin 2 × Fin 2, cgauss2 2 q.1 q.2 ^ ((4 : ℝ) / 7) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_finset_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hd, ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0 : ℝ) ≤ 4 / 7)]
  have hsum : (∑ q : Fin 2 × Fin 2, (cgauss2 2 q.1 q.2 : ℝ≥0∞) ^ (((4 / 7 : ℝ≥0)) : ℝ))
      ≤ 1 := by
    rw [hcast]
    exact_mod_cast sum_cgauss2_two_rpow_le_one'
  have h := dimH_gauss_le_two (K := 2) (d := (4 / 7 : ℝ≥0)) hEJ hself hsum
  refine h.trans ?_
  norm_num

/-- **SHARPEST ENCLOSURE IN THIS PROJECT, `K = 3`.**  `0.63 ≤ dim_H E ≤ 0.7625`.
TRUE value `0.7056609…`; the gap is NOT closed. -/
theorem dimH_gauss_three_enclosure_tight {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3) (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 3, Set.MapsTo (gaussIFS 3 j) E E) :
    ENNReal.ofReal ((63 : ℝ) / 100) ≤ dimH E ∧ dimH E ≤ (61 / 80 : ℝ≥0∞) :=
  ⟨le_dimH_gauss_three_level_two hEJ hself hne hclosed hinv,
    dimH_gauss_three_le_two' hEJ hself⟩

/-- **SHARPEST ENCLOSURE IN THIS PROJECT, `K = 2`.**  `0.46 ≤ dim_H E ≤ 0.5715`.
TRUE value `0.5312805…`; the gap is NOT closed. -/
theorem dimH_gauss_two_enclosure_tight {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 2) (hself : E ⊆ ⋃ j, gaussIFS 2 j '' E)
    (hne : E.Nonempty) (hclosed : IsClosed E)
    (hinv : ∀ j : Fin 2, Set.MapsTo (gaussIFS 2 j) E E) :
    ENNReal.ofReal ((23 : ℝ) / 50) ≤ dimH E ∧ dimH E ≤ (4 / 7 : ℝ≥0∞) :=
  ⟨le_dimH_gauss_two_level_two hEJ hself hne hclosed hinv,
    dimH_gauss_two_le_two' hEJ hself⟩

/-! ## Axiom audit -/

#print axioms AddrIFS.approx_bdry
#print axioms AddrIFS.approx_funeq
#print axioms AddrIFS.approx_diff
#print axioms AddrIFS.addr_funeq
#print axioms AddrIFS.continuous_addr
#print axioms AddrIFS.addr_holder_aux
#print axioms AddrIFS.addr_dist_le
#print axioms AddrIFS.addr_holderOn
#print axioms AddrIFS.hsum_cover
#print axioms AddrIFS.wlead_cover
#print axioms AddrIFS.addr_image_dense
#print axioms AddrIFS.unitInterval_subset_addr_image
#print axioms AddrIFS.le_dimH
#print axioms gaussLevelOne
#print axioms le_dimH_gauss_three_abstract
#print axioms le_dimH_gauss_two_abstract
#print axioms mob2_anti
#print axioms x2_cyl
#print axioms x2_uniq
#print axioms g2_anti
#print axioms g2_lip
#print axioms g2_ge
#print axioms g2_le
#print axioms g2_selfCover
#print axioms chi3_cyl
#print axioms sep3
#print axioms gaussTwo3
#print axioms p3_le_rpow
#print axioms le_dimH_gauss_three_level_two
#print axioms dimH_gauss_three_enclosure_two
#print axioms chi2_cyl
#print axioms sep2
#print axioms gaussTwo2
#print axioms p2_le_rpow
#print axioms le_dimH_gauss_two_level_two
#print axioms dimH_gauss_two_enclosure_two
#print axioms sum_cgauss2_three_rpow_le_one'
#print axioms dimH_gauss_three_le_two'
#print axioms sum_cgauss2_two_rpow_le_one'
#print axioms dimH_gauss_two_le_two'
#print axioms dimH_gauss_three_enclosure_tight
#print axioms dimH_gauss_two_enclosure_tight

end PrincipiaTractalis.GaussLevelTwo
