/-
# PF.HausdorffIFS_r205 — Hausdorff dimension UPPER bounds for IFS attractors

Kernel-certified Moran/Falconer upper bound for the Hausdorff dimension of a
self-covering set under a finite family of contractions, plus the Gauss
continued-fraction branch estimates.

## What this file proves

* `dimH_le_of_bounded_covers` — a general covering engine: if a set `E` admits,
  for every `n`, a *finite* cover by sets of diameter `≤ r n` with `r n → 0`
  and with `∑ᵢ diam(tₙ i)^d` bounded by a single finite constant `C`, then
  `dimH E ≤ d`.

* `dimH_le_of_selfCover` — the Moran/Falconer upper bound.  If `E ⊆ ⋃ⱼ φⱼ '' E`
  with each `φⱼ` Lipschitz on an invariant set `S ⊇ E` with constant `Lⱼ < 1`,
  and `∑ⱼ Lⱼ^d ≤ 1`, then `dimH E ≤ d`.

* `gauss_mapsTo`, `gauss_lipschitzOnWith`, `Lgauss_lt_one` — the level-1 data
  for the Gauss continued-fraction IFS `x ↦ 1/(x + (j+1))` on the invariant
  interval `[1/(K+1), 1]`.

* `dimH_gauss_le` — the resulting dimension bound for any Gauss-self-covering
  subset of that interval.

* `dimH_gauss_three_le` — the concrete `K = 3` instance: `dimH E ≤ 19/20`.
  Weak on purpose; see item 3 of the honesty statement.

## HONESTY STATEMENT — read this before quoting anything from this file

1. **UPPER BOUND ONLY.**  Everything here is a covering (upper) estimate.  The
   matching LOWER bound requires the mass distribution principle together with
   a Gibbs / conformal measure for the IFS.  That is *not* in this file, and
   nothing here should be read as computing a dimension.

2. **THE ATTRACTOR IS NOT CONSTRUCTED.**  Self-covering, `E ⊆ ⋃ⱼ φⱼ '' E`, is a
   HYPOTHESIS throughout.  We never build the Hutchinson attractor, never prove
   it is nonempty/compact, and never prove uniqueness.  The theorems are
   conditional statements about any set with the covering property.

3. **THE GAUSS NUMBERS ARE WEAK.**  `Lgauss K j` is the *level-1* (single
   branch) Lipschitz constant, i.e. `sup |φⱼ'|` on the invariant interval.
   Level-1 constants give a genuinely crude Moran exponent.  For `K = 3` the
   root of `∑ⱼ Lⱼ^d = 1` sits near `0.9235`.  The sharp Hausdorff dimension of
   the `E₂`-type Gauss Cantor sets — Jenkinson–Pollicott's
   `0.705660908029...` for the classical two-branch set — is **NOT** claimed,
   **NOT** approached, and **NOT** derivable from anything below.  Getting near
   it needs higher-level cylinder estimates (or the transfer-operator method),
   which this file does not have.

4. No `sorry`, no `native_decide`, no project axioms.  All results reduce to
   `[propext, Classical.choice, Quot.sound]`.

## Lipschitz convention used

§2 is stated with `LipschitzOnWith` on an invariant set `S` (with
`Set.MapsTo (φ j) S S` and `E ⊆ S`), NOT with global `LipschitzWith`.  This is
forced by §3: the Gauss branches `x ↦ 1/(x + (j+1))` are not globally Lipschitz
on `ℝ`.  The global version is recovered as `dimH_le_of_selfCover_global`
(take `S = univ`).
-/

import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

open scoped NNReal ENNReal Topology
open Filter Set MeasureTheory

namespace PrincipiaTractalis.HausdorffIFS

/-! ## §1 — the general covering engine (no dynamics) -/

/-- **Covering engine.**  If `E` is covered, for every `n`, by a finite family
`t n : ι n → Set X` of sets of diameter at most `r n`, with `r n → 0`, and if
the `d`-sums `∑ᵢ diam (t n i)^d` are bounded above by one finite constant `C`,
then `dimH E ≤ d`. -/
theorem dimH_le_of_bounded_covers {X : Type*} [EMetricSpace X] {E : Set X}
    {d : ℝ≥0} {ι : ℕ → Type} [∀ n, Fintype (ι n)]
    (t : ∀ n, ι n → Set X) (r : ℕ → ℝ≥0∞)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hdiam : ∀ n i, EMetric.diam (t n i) ≤ r n)
    (hcover : ∀ n, E ⊆ ⋃ i, t n i)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hsum : ∀ n, (∑ i, EMetric.diam (t n i) ^ (d : ℝ)) ≤ C) :
    dimH E ≤ (d : ℝ≥0∞) := by
  borelize X
  refine dimH_le_of_hausdorffMeasure_ne_top (d := d) ?_
  have h1 : μH[(d : ℝ)] E
      ≤ Filter.liminf (fun n => ∑ i, EMetric.diam (t n i) ^ (d : ℝ)) Filter.atTop :=
    MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum (d : ℝ) E r hr t
      (Filter.Eventually.of_forall hdiam) (Filter.Eventually.of_forall hcover)
  have h2 : Filter.liminf (fun n => ∑ i, EMetric.diam (t n i) ^ (d : ℝ)) Filter.atTop ≤ C := by
    calc Filter.liminf (fun n => ∑ i, EMetric.diam (t n i) ^ (d : ℝ)) Filter.atTop
        ≤ Filter.liminf (fun _ : ℕ => C) Filter.atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hsum)
      _ = C := Filter.liminf_const C
  exact ne_top_of_le_ne_top hC (h1.trans h2)

/-! ## §2 — the IFS Moran/Falconer upper bound -/

section IFS

variable {X : Type*} [EMetricSpace X] {K : ℕ}

/-- Diameter of the image of a subset of the Lipschitz domain. -/
theorem ediam_image_le_of_lipschitzOnWith {Y : Type*} [EMetricSpace Y]
    {c : ℝ≥0} {f : X → Y} {S A : Set X} (hf : LipschitzOnWith c f S) (hA : A ⊆ S) :
    EMetric.diam (f '' A) ≤ (c : ℝ≥0∞) * EMetric.diam A := by
  refine EMetric.diam_le ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (hf (hA hx) (hA hy)).trans
    (mul_le_mul_left' (EMetric.edist_le_diam_of_mem hx hy) _)

/-- The cylinder piece of `E` indexed by a word `a : Fin n → Fin K`:
`piece φ E n a = φ (a 0) ∘ φ (a 1) ∘ ⋯ ∘ φ (a (n-1)) '' E`. -/
def piece (φ : Fin K → X → X) (E : Set X) : ∀ (n : ℕ), (Fin n → Fin K) → Set X
  | 0, _ => E
  | (n + 1), a => φ (a 0) '' piece φ E n (fun i : Fin n => a i.succ)

omit [EMetricSpace X] in
@[simp] theorem piece_zero (φ : Fin K → X → X) (E : Set X) (a : Fin 0 → Fin K) :
    piece φ E 0 a = E := rfl

omit [EMetricSpace X] in
theorem piece_succ (φ : Fin K → X → X) (E : Set X) (n : ℕ) (a : Fin (n + 1) → Fin K) :
    piece φ E (n + 1) a = φ (a 0) '' piece φ E n (fun i : Fin n => a i.succ) := rfl

omit [EMetricSpace X] in
theorem piece_cons (φ : Fin K → X → X) (E : Set X) (n : ℕ) (j : Fin K) (a : Fin n → Fin K) :
    piece φ E (n + 1) (Fin.cons j a) = φ j '' piece φ E n a := by
  rw [piece_succ]
  simp

omit [EMetricSpace X] in
/-- Iterating the self-covering hypothesis: the level-`n` cylinders cover `E`. -/
theorem piece_cover {φ : Fin K → X → X} {E : Set X} (hself : E ⊆ ⋃ j, φ j '' E) :
    ∀ n, E ⊆ ⋃ a : Fin n → Fin K, piece φ E n a := by
  intro n
  induction n with
  | zero =>
      intro x hx
      exact Set.mem_iUnion.2 ⟨fun i => i.elim0, hx⟩
  | succ n ih =>
      intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hself hx)
      obtain ⟨y, hyE, rfl⟩ := hj
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (ih hyE)
      refine Set.mem_iUnion.2 ⟨Fin.cons j a, ?_⟩
      rw [piece_cons]
      exact ⟨y, ha, rfl⟩

omit [EMetricSpace X] in
/-- Every cylinder stays inside the invariant set `S`. -/
theorem piece_subset {φ : Fin K → X → X} {E S : Set X} (hES : E ⊆ S)
    (hmaps : ∀ j, Set.MapsTo (φ j) S S) :
    ∀ n (a : Fin n → Fin K), piece φ E n a ⊆ S := by
  intro n
  induction n with
  | zero => intro a; exact hES
  | succ n ih =>
      intro a
      rw [piece_succ]
      rintro _ ⟨y, hy, rfl⟩
      exact hmaps _ (ih _ hy)

/-- Diameter of a cylinder: contracted by the product of the branch constants. -/
theorem piece_ediam_le {φ : Fin K → X → X} {E S : Set X} {L : Fin K → ℝ≥0}
    (hES : E ⊆ S) (hmaps : ∀ j, Set.MapsTo (φ j) S S)
    (hlip : ∀ j, LipschitzOnWith (L j) (φ j) S) :
    ∀ n (a : Fin n → Fin K),
      EMetric.diam (piece φ E n a) ≤ (∏ i, (L (a i) : ℝ≥0∞)) * EMetric.diam E := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
      intro a
      have hstep : EMetric.diam (piece φ E (n + 1) a)
          ≤ (L (a 0) : ℝ≥0∞) * EMetric.diam (piece φ E n (fun i : Fin n => a i.succ)) := by
        rw [piece_succ]
        exact ediam_image_le_of_lipschitzOnWith (hlip _) (piece_subset hES hmaps n _)
      calc EMetric.diam (piece φ E (n + 1) a)
          ≤ (L (a 0) : ℝ≥0∞) * EMetric.diam (piece φ E n (fun i : Fin n => a i.succ)) := hstep
        _ ≤ (L (a 0) : ℝ≥0∞)
              * ((∏ i : Fin n, (L (a i.succ) : ℝ≥0∞)) * EMetric.diam E) :=
            mul_le_mul_left' (ih _) _
        _ = (∏ i, (L (a i) : ℝ≥0∞)) * EMetric.diam E := by
            rw [Fin.prod_univ_succ]; ring

/-- The `d`-th power version of `piece_ediam_le`, with the exponent already
distributed over the product. -/
theorem piece_ediam_rpow_le {φ : Fin K → X → X} {E S : Set X} {L : Fin K → ℝ≥0} {d : ℝ≥0}
    (hES : E ⊆ S) (hmaps : ∀ j, Set.MapsTo (φ j) S S)
    (hlip : ∀ j, LipschitzOnWith (L j) (φ j) S) :
    ∀ n (a : Fin n → Fin K),
      EMetric.diam (piece φ E n a) ^ (d : ℝ)
        ≤ (∏ i, ((L (a i) : ℝ≥0∞) ^ (d : ℝ))) * EMetric.diam E ^ (d : ℝ) := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
      intro a
      have hstep : EMetric.diam (piece φ E (n + 1) a)
          ≤ (L (a 0) : ℝ≥0∞) * EMetric.diam (piece φ E n (fun i : Fin n => a i.succ)) := by
        rw [piece_succ]
        exact ediam_image_le_of_lipschitzOnWith (hlip _) (piece_subset hES hmaps n _)
      calc EMetric.diam (piece φ E (n + 1) a) ^ (d : ℝ)
          ≤ ((L (a 0) : ℝ≥0∞)
              * EMetric.diam (piece φ E n (fun i : Fin n => a i.succ))) ^ (d : ℝ) :=
            ENNReal.rpow_le_rpow hstep d.coe_nonneg
        _ = (L (a 0) : ℝ≥0∞) ^ (d : ℝ)
              * EMetric.diam (piece φ E n (fun i : Fin n => a i.succ)) ^ (d : ℝ) :=
            ENNReal.mul_rpow_of_nonneg _ _ d.coe_nonneg
        _ ≤ (L (a 0) : ℝ≥0∞) ^ (d : ℝ)
              * ((∏ i : Fin n, ((L (a i.succ) : ℝ≥0∞) ^ (d : ℝ))) * EMetric.diam E ^ (d : ℝ)) :=
            mul_le_mul_left' (ih _) _
        _ = (∏ i, ((L (a i) : ℝ≥0∞) ^ (d : ℝ))) * EMetric.diam E ^ (d : ℝ) := by
            rw [Fin.prod_univ_succ]; ring

/-- The Moran sum bound: `∑_words diam^d ≤ (∑ⱼ Lⱼ^d)^n · diam(E)^d ≤ diam(E)^d`. -/
theorem sum_piece_ediam_rpow_le {φ : Fin K → X → X} {E S : Set X} {L : Fin K → ℝ≥0} {d : ℝ≥0}
    (hES : E ⊆ S) (hmaps : ∀ j, Set.MapsTo (φ j) S S)
    (hlip : ∀ j, LipschitzOnWith (L j) (φ j) S)
    (hsum : (∑ j, (L j : ℝ≥0∞) ^ (d : ℝ)) ≤ 1) :
    ∀ n, (∑ a : Fin n → Fin K, EMetric.diam (piece φ E n a) ^ (d : ℝ))
        ≤ EMetric.diam E ^ (d : ℝ) := by
  intro n
  classical
  calc (∑ a : Fin n → Fin K, EMetric.diam (piece φ E n a) ^ (d : ℝ))
      ≤ ∑ a : Fin n → Fin K,
          (∏ i, ((L (a i) : ℝ≥0∞) ^ (d : ℝ))) * EMetric.diam E ^ (d : ℝ) :=
        Finset.sum_le_sum fun a _ => piece_ediam_rpow_le hES hmaps hlip n a
    _ = (∑ a : Fin n → Fin K, ∏ i, ((L (a i) : ℝ≥0∞) ^ (d : ℝ))) * EMetric.diam E ^ (d : ℝ) := by
        rw [Finset.sum_mul]
    _ = (∑ j, (L j : ℝ≥0∞) ^ (d : ℝ)) ^ n * EMetric.diam E ^ (d : ℝ) := by
        congr 1
        rw [Finset.sum_pow' Finset.univ (fun j => (L j : ℝ≥0∞) ^ (d : ℝ)) n,
          Fintype.piFinset_univ]
    _ ≤ (1 : ℝ≥0∞) ^ n * EMetric.diam E ^ (d : ℝ) := by
        exact mul_le_mul_right' (pow_le_pow_left' hsum n) _
    _ = EMetric.diam E ^ (d : ℝ) := by rw [one_pow, one_mul]

/-- **Moran / Falconer upper bound (local-Lipschitz form).**

If `E` is contained in a set `S` invariant under a finite family of maps `φⱼ`,
each Lipschitz on `S` with constant `Lⱼ < 1`, if `E` is self-covering
(`E ⊆ ⋃ⱼ φⱼ '' E`) and bounded, and if `∑ⱼ Lⱼ^d ≤ 1`, then `dimH E ≤ d`.

This is an UPPER bound; the matching lower bound is not proved anywhere in this
file.  `E` is *not* constructed: self-covering is a hypothesis. -/
theorem dimH_le_of_selfCover {φ : Fin K → X → X} {E S : Set X} {L : Fin K → ℝ≥0} {d : ℝ≥0}
    (hES : E ⊆ S)
    (hbdd : EMetric.diam E ≠ ⊤)
    (hmaps : ∀ j, Set.MapsTo (φ j) S S)
    (hself : E ⊆ ⋃ j, φ j '' E)
    (hlip : ∀ j, LipschitzOnWith (L j) (φ j) S)
    (hL1 : ∀ j, L j < 1)
    (hsum : (∑ j, (L j : ℝ≥0∞) ^ (d : ℝ)) ≤ 1) :
    dimH E ≤ (d : ℝ≥0∞) := by
  classical
  set Lmax : ℝ≥0 := Finset.univ.sup L with hLmaxDef
  have hLmax1 : Lmax < 1 := by
    rw [hLmaxDef]
    refine (Finset.sup_lt_iff ?_).2 fun j _ => hL1 j
    simp
  have hle : ∀ j, L j ≤ Lmax := by
    intro j
    rw [hLmaxDef]; exact Finset.le_sup (Finset.mem_univ j)
  have hprod : ∀ n (a : Fin n → Fin K),
      (∏ i, (L (a i) : ℝ≥0∞)) ≤ (Lmax : ℝ≥0∞) ^ n := by
    intro n a
    calc (∏ i, (L (a i) : ℝ≥0∞)) ≤ ∏ _i : Fin n, (Lmax : ℝ≥0∞) := by
          gcongr with i
          · exact hle _
      _ = (Lmax : ℝ≥0∞) ^ n := by simp
  have hr : Filter.Tendsto (fun n : ℕ => (Lmax : ℝ≥0∞) ^ n * EMetric.diam E)
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (Lmax : ℝ≥0∞) ^ n) Filter.atTop (nhds 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by exact_mod_cast hLmax1)
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hbdd)
  refine dimH_le_of_bounded_covers (ι := fun n => Fin n → Fin K)
      (t := fun n a => piece φ E n a)
      (r := fun n => (Lmax : ℝ≥0∞) ^ n * EMetric.diam E) hr ?_ (piece_cover hself)
      (C := EMetric.diam E ^ (d : ℝ))
      (ENNReal.rpow_ne_top_of_nonneg d.coe_nonneg hbdd)
      (sum_piece_ediam_rpow_le hES hmaps hlip hsum)
  intro n a
  exact (piece_ediam_le hES hmaps hlip n a).trans (mul_le_mul_right' (hprod n a) _)

/-- **Moran / Falconer upper bound (global-Lipschitz form).**  Special case of
`dimH_le_of_selfCover` with `S = Set.univ`. -/
theorem dimH_le_of_selfCover_global {φ : Fin K → X → X} {E : Set X} {L : Fin K → ℝ≥0} {d : ℝ≥0}
    (hbdd : EMetric.diam E ≠ ⊤)
    (hself : E ⊆ ⋃ j, φ j '' E)
    (hlip : ∀ j, LipschitzWith (L j) (φ j))
    (hL1 : ∀ j, L j < 1)
    (hsum : (∑ j, (L j : ℝ≥0∞) ^ (d : ℝ)) ≤ 1) :
    dimH E ≤ (d : ℝ≥0∞) :=
  dimH_le_of_selfCover (S := Set.univ) (Set.subset_univ _) hbdd
    (fun _j => Set.mapsTo_univ _ _) hself (fun j => (hlip j).lipschitzOnWith) hL1 hsum

end IFS

/-! ## §3 — the Gauss continued-fraction branches -/

/-- The `K`-branch Gauss IFS: `x ↦ 1/(x + (j+1))`, `j = 0, …, K-1`. -/
noncomputable def gaussIFS (K : ℕ) (j : Fin K) : ℝ → ℝ :=
  fun x => 1 / (x + (((j : ℕ) : ℝ) + 1))

/-- The invariant interval `[1/(K+1), 1]`. -/
def gaussJ (K : ℕ) : Set ℝ := Set.Icc (1 / ((K : ℝ) + 1)) 1

/-- Level-1 Lipschitz constant of the `j`-th Gauss branch on `gaussJ K`:
`sup |φⱼ'| = 1/(1/(K+1) + (j+1))² = ((K+1)/(1 + (j+1)(K+1)))²`. -/
noncomputable def Lgauss (K : ℕ) (j : Fin K) : ℝ≥0 :=
  (((K : ℝ≥0) + 1) / (1 + (((j : ℕ) : ℝ≥0) + 1) * ((K : ℝ≥0) + 1))) ^ 2

theorem Lgauss_coe (K : ℕ) (j : Fin K) :
    ((Lgauss K j : ℝ≥0) : ℝ)
      = (((K : ℝ) + 1) / (1 + (((j : ℕ) : ℝ) + 1) * ((K : ℝ) + 1))) ^ 2 := by
  simp [Lgauss]

theorem Lgauss_lt_one (K : ℕ) (j : Fin K) : Lgauss K j < 1 := by
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hm : (1 : ℝ) ≤ ((j : ℕ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hden : (0 : ℝ) < 1 + (((j : ℕ) : ℝ) + 1) * ((K : ℝ) + 1) := by nlinarith
  have hb : ((K : ℝ) + 1) / (1 + (((j : ℕ) : ℝ) + 1) * ((K : ℝ) + 1)) < 1 := by
    rw [div_lt_one hden]
    nlinarith
  have hb0 : (0 : ℝ) ≤ ((K : ℝ) + 1) / (1 + (((j : ℕ) : ℝ) + 1) * ((K : ℝ) + 1)) := by
    positivity
  have : ((Lgauss K j : ℝ≥0) : ℝ) < 1 := by
    rw [Lgauss_coe]
    nlinarith
  exact_mod_cast this

/-- Each Gauss branch maps the invariant interval into itself. -/
theorem gauss_mapsTo (K : ℕ) (j : Fin K) :
    Set.MapsTo (gaussIFS K j) (gaussJ K) (gaussJ K) := by
  rintro x ⟨hx1, hx2⟩
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hm1 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hmK : ((j : ℕ) : ℝ) + 1 ≤ (K : ℝ) := by
    have h := j.isLt
    have : ((j : ℕ) : ℝ) + 1 ≤ ((K : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    simpa using this
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hx1
  have hpos : (0 : ℝ) < x + (((j : ℕ) : ℝ) + 1) := by linarith
  constructor
  · show 1 / ((K : ℝ) + 1) ≤ 1 / (x + (((j : ℕ) : ℝ) + 1))
    exact one_div_le_one_div_of_le hpos (by linarith)
  · show 1 / (x + (((j : ℕ) : ℝ) + 1)) ≤ 1
    rw [div_le_one hpos]
    linarith

/-- Each Gauss branch is Lipschitz on the invariant interval with the level-1
constant `Lgauss K j`. -/
theorem gauss_lipschitzOnWith (K : ℕ) (j : Fin K) :
    LipschitzOnWith (Lgauss K j) (gaussIFS K j) (gaussJ K) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  set m : ℝ := ((j : ℕ) : ℝ) + 1 with hmdef
  have hm1 : (1 : ℝ) ≤ m := by
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hmdef]; linarith
  set a : ℝ := 1 / ((K : ℝ) + 1) with hadef
  have ha0 : (0 : ℝ) < a := by rw [hadef]; positivity
  have hxa : a ≤ x := hx1
  have hya : a ≤ y := hy1
  have hxm : (0 : ℝ) < x + m := by linarith
  have hym : (0 : ℝ) < y + m := by linarith
  have ham : (0 : ℝ) < a + m := by linarith
  -- the Lipschitz constant, as a real number
  set b : ℝ := ((K : ℝ) + 1) / (1 + m * ((K : ℝ) + 1)) with hbdef
  have hden : (0 : ℝ) < 1 + m * ((K : ℝ) + 1) := by nlinarith
  have hb0 : (0 : ℝ) < b := by rw [hbdef]; positivity
  have hcoe : ((Lgauss K j : ℝ≥0) : ℝ) = b ^ 2 := by
    rw [Lgauss_coe, hbdef, hmdef]
  -- b · (a + m) = 1
  have hkey : b * (a + m) = 1 := by
    rw [hbdef, hadef]
    field_simp
  -- the algebraic identity for the difference
  have hdiff : gaussIFS K j x - gaussIFS K j y = (y - x) / ((x + m) * (y + m)) := by
    simp only [gaussIFS, ← hmdef]
    field_simp
    ring
  have habs : |gaussIFS K j x - gaussIFS K j y| = |x - y| / ((x + m) * (y + m)) := by
    rw [hdiff, abs_div, abs_of_pos (by positivity : (0:ℝ) < (x + m) * (y + m)), abs_sub_comm]
  rw [Real.dist_eq, Real.dist_eq, habs, hcoe]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (x + m) * (y + m))]
  have hbx : (1 : ℝ) ≤ b * (x + m) := by
    nlinarith [mul_nonneg hb0.le (sub_nonneg.2 hxa)]
  have hby : (1 : ℝ) ≤ b * (y + m) := by
    nlinarith [mul_nonneg hb0.le (sub_nonneg.2 hya)]
  have hmul : (1 : ℝ) * 1 ≤ (b * (x + m)) * (b * (y + m)) :=
    mul_le_mul hbx hby zero_le_one (by positivity)
  have heq : (b * (x + m)) * (b * (y + m)) = b ^ 2 * ((x + m) * (y + m)) := by ring
  have h1 : (1 : ℝ) ≤ b ^ 2 * ((x + m) * (y + m)) := by
    rw [heq] at hmul; linarith
  nlinarith [abs_nonneg (x - y)]

/-- **Gauss continued-fraction dimension bound (UPPER only).**

For ANY set `E` inside the invariant interval `[1/(K+1), 1]` which is
self-covering under the `K` Gauss branches, and any `d` with
`∑ⱼ (Lgauss K j)^d ≤ 1`, we get `dimH E ≤ d`.

The attractor is NOT constructed here — self-covering is a hypothesis.  The
constants are level-1 only, so the resulting `d` is a weak bound. -/
theorem dimH_gauss_le {K : ℕ} {E : Set ℝ} {d : ℝ≥0}
    (hEJ : E ⊆ gaussJ K)
    (hself : E ⊆ ⋃ j, gaussIFS K j '' E)
    (hsum : (∑ j, (Lgauss K j : ℝ≥0∞) ^ (d : ℝ)) ≤ 1) :
    dimH E ≤ (d : ℝ≥0∞) := by
  have hbdd : EMetric.diam E ≠ ⊤ := by
    have h : EMetric.diam E ≤ EMetric.diam (gaussJ K) := EMetric.diam_mono hEJ
    have h2 : EMetric.diam (gaussJ K) = ENNReal.ofReal (1 - 1 / ((K : ℝ) + 1)) := by
      rw [gaussJ, Real.ediam_Icc]
    rw [h2] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  exact dimH_le_of_selfCover (S := gaussJ K) hEJ hbdd (gauss_mapsTo K) hself
    (gauss_lipschitzOnWith K) (Lgauss_lt_one K) hsum

/-! ### A concrete (deliberately weak) numeric instance: `K = 3`

The level-1 constants are `16/25`, `16/81`, `16/169`.  The Moran root of
`∑ⱼ Lⱼ^d = 1` for these numbers sits near `0.9235`; we certify the round value
`d = 19/20 = 0.95`.  This is a WEAK bound and is NOT an approximation of the
true Gauss-set dimension.  See the honesty statement at the top of the file. -/

/-- If `x^p ≤ u^q` with `q ≠ 0` then `x^(p/q) ≤ u` (real exponent, in `ℝ≥0`).
This is what lets `norm_num` discharge rational-exponent inequalities. -/
theorem nnreal_rpow_le_of_pow_le {x u : ℝ≥0} {p q : ℕ} (hq : q ≠ 0) (h : x ^ p ≤ u ^ q) :
    x ^ ((p : ℝ) / (q : ℝ)) ≤ u := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have key : (x ^ ((p : ℝ) / (q : ℝ))) ^ q = x ^ p := by
    rw [← NNReal.rpow_natCast (x ^ ((p : ℝ) / (q : ℝ))) q, ← NNReal.rpow_mul,
      div_mul_cancel₀ _ hq0.ne', NNReal.rpow_natCast]
  refine le_of_pow_le_pow_left₀ hq (zero_le u) ?_
  rw [key]
  exact h

theorem Lgauss_three_zero : Lgauss 3 0 = 16 / 25 := by norm_num [Lgauss]

theorem Lgauss_three_one : Lgauss 3 1 = 16 / 81 := by norm_num [Lgauss]

theorem Lgauss_three_two : Lgauss 3 2 = 16 / 169 := by norm_num [Lgauss]

/-- `(16/25)^(19/20) + (16/81)^(19/20) + (16/169)^(19/20) ≤ 1`, kernel-checked
via the rational-power reduction `x^(p/q) ≤ u ↔ x^p ≤ u^q`. -/
theorem sum_Lgauss_three_rpow_le_one :
    (∑ j : Fin 3, Lgauss 3 j ^ ((19 : ℝ) / 20)) ≤ (1 : ℝ≥0) := by
  rw [Fin.sum_univ_three, Lgauss_three_zero, Lgauss_three_one, Lgauss_three_two]
  have h0 : ((16 : ℝ≥0) / 25) ^ ((19 : ℝ) / 20) ≤ 66 / 100 :=
    nnreal_rpow_le_of_pow_le (p := 19) (q := 20) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have h1 : ((16 : ℝ≥0) / 81) ^ ((19 : ℝ) / 20) ≤ 22 / 100 :=
    nnreal_rpow_le_of_pow_le (p := 19) (q := 20) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have h2 : ((16 : ℝ≥0) / 169) ^ ((19 : ℝ) / 20) ≤ 11 / 100 :=
    nnreal_rpow_le_of_pow_le (p := 19) (q := 20) (by norm_num)
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  calc ((16 : ℝ≥0) / 25) ^ ((19 : ℝ) / 20) + ((16 : ℝ≥0) / 81) ^ ((19 : ℝ) / 20)
        + ((16 : ℝ≥0) / 169) ^ ((19 : ℝ) / 20)
      ≤ (66 / 100 : ℝ≥0) + 22 / 100 + 11 / 100 := by gcongr
    _ ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num

/-- **Numeric corollary (`K = 3`, weak bound).**  Any subset of `[1/4, 1]` that
is self-covering under the three Gauss branches `x ↦ 1/(x+1), 1/(x+2), 1/(x+3)`
has Hausdorff dimension at most `19/20`.

This is an honest but crude consequence of the *level-1* branch constants.  It
is NOT an approximation to the true dimension of the Gauss Cantor set. -/
theorem dimH_gauss_three_le {E : Set ℝ}
    (hEJ : E ⊆ gaussJ 3)
    (hself : E ⊆ ⋃ j, gaussIFS 3 j '' E) :
    dimH E ≤ (19 / 20 : ℝ≥0∞) := by
  have hd : (((19 / 20 : ℝ≥0)) : ℝ) = (19 : ℝ) / 20 := by
    push_cast
    norm_num
  have hcast : (∑ j : Fin 3, (Lgauss 3 j : ℝ≥0∞) ^ (((19 / 20 : ℝ≥0)) : ℝ))
      = ((∑ j : Fin 3, Lgauss 3 j ^ ((19 : ℝ) / 20) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hd, ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0 : ℝ) ≤ 19 / 20)]
  have hsum : (∑ j : Fin 3, (Lgauss 3 j : ℝ≥0∞) ^ (((19 / 20 : ℝ≥0)) : ℝ)) ≤ 1 := by
    rw [hcast]
    exact_mod_cast sum_Lgauss_three_rpow_le_one
  have h := dimH_gauss_le (K := 3) (d := (19 / 20 : ℝ≥0)) hEJ hself hsum
  refine h.trans ?_
  norm_num

/-! ## Axiom audit -/

#print axioms dimH_le_of_bounded_covers
#print axioms dimH_le_of_selfCover
#print axioms dimH_le_of_selfCover_global
#print axioms gauss_mapsTo
#print axioms gauss_lipschitzOnWith
#print axioms Lgauss_lt_one
#print axioms dimH_gauss_le
#print axioms sum_Lgauss_three_rpow_le_one
#print axioms dimH_gauss_three_le

end PrincipiaTractalis.HausdorffIFS
