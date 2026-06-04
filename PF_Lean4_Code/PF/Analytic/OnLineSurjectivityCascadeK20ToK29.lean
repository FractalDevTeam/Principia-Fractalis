/-
# On-Line Surjectivity (C3) — CASCADE EXTENSION K = 20..29 (Odlyzko prefix)

★ 2026-06-03 — Wave 58 follow-up #6. Extension of the per-zero cascade
from k ∈ {0, ..., 19} (handled by `OnLineSurjectivityCascadeK10ToK19`)
to k ∈ {0, ..., 29}, anchored at the third decade of numerical Odlyzko
ζ-zero ordinates:

    t21 = 79.337375020249367747496229    (Odlyzko / LMFDB)
    t22 = 82.910380854086030183164837    (Odlyzko / LMFDB)
    t23 = 84.735492980517050105735311    (Odlyzko / LMFDB)
    t24 = 87.425274613125229406531667    (Odlyzko / LMFDB)
    t25 = 88.809111207634465423682348    (Odlyzko / LMFDB)
    t26 = 92.491899270558484296259030    (Odlyzko / LMFDB)
    t27 = 94.651344040519886966597925    (Odlyzko / LMFDB)
    t28 = 95.870634228245309758741029    (Odlyzko / LMFDB)
    t29 = 98.831194218193198281456637    (Odlyzko / LMFDB)
    t30 = 101.317851005731391228785648   (Odlyzko / LMFDB)

## Strategic context

`OnLineSurjectivityCascadeK10ToK19` provided:

  (a) The Odlyzko 20-prefix oracle `odlyzko20_oracle` returning
      t_{k+1} for k ∈ {0, ..., 19}.
  (b) The single eigenvalue-sequence witness
      `eigenvalues_Odlyzko20 := eigenvalues_anchoredAt_finite
        odlyzko20_oracle 19`.
  (c) Per-index discharge of `KthZetaZeroInEigenvalueImage` for
      k ∈ {0, ..., 19} via `kth_cascade_to_finite`.

This file SPECIALISES the same forward-chaining lemma at N = 29 to a
new Odlyzko 30-prefix oracle, giving an explicit per-index discharge
for each k ∈ {20, ..., 29}, axiom-free, with each `t_{k+1} > 0` proved
by `norm_num`.

## What this file delivers (axiom-free)

  **E1 — Odlyzko ordinates t21..t30 as Lean reals**
    `t21_Odlyzko, t22_Odlyzko, ..., t30_Odlyzko : ℝ`, each with a
    `norm_num` positivity record.

  **E2 — Odlyzko 30-prefix oracle**
    `odlyzko30_oracle : ℕ → ℝ` defined to return t_{k+1} for
    k ∈ {0, ..., 29} and 1 outside the prefix.

  **E3 — 30-prefix positivity**
    `odlyzko30_oracle_positive_on_prefix` — every k ≤ 29 has
    `0 < odlyzko30_oracle k`.

  **E4 — Specialised eigenvalue sequence at N = 30**
    `eigenvalues_Odlyzko30 := eigenvalues_anchoredAt_finite
      odlyzko30_oracle 29` — a single eigenvalue sequence whose
    `eigenvalueToT` image at index k equals t_{k+1} for every
    k ∈ {0, ..., 29}.

  **E5 — Per-index discharge for k ∈ {20, ..., 29}**
    Ten theorems
      `kth_atom_twenty_at_Odlyzko30`, ...,
      `kth_atom_twenty_nine_at_Odlyzko30`,
    each proving
    `KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
       odlyzko30_oracle k`
    by direct invocation of `kth_cascade_to_finite`.

  **E6 — 10-clause discharge capstone**
    `cascade_extension_k20_to_k29_capstone` bundles all ten per-index
    discharges as one citable conjunction.

  **E7 — Full 30-prefix bundle**
    `cascade_extension_k0_to_k29_bundle` covers k ∈ {0, ..., 29} on
    the SINGLE eigenvalue-sequence witness `eigenvalues_Odlyzko30`.

  **E8 — Bridge to k=10..19 cascade**
    `cascade_extension_k0_to_k29_implies_k0_to_k19` — every per-zero
    discharge on the 30-prefix witness specialises to the 20-prefix
    range k ∈ {0, ..., 19} via the same forward-chaining lemma. The
    two witnesses are distinct (each is constructed witness-level);
    this bridge demonstrates that the larger cascade subsumes the
    smaller as a subrange Prop schema.

## Honest scope

  * The discharge is at the level of a CONSTRUCTED witness
    `(α_unit, eigenvalues_Odlyzko30)`. Coincidence with the
    framework's canonical T₃^sym eigenvalue sequence remains the
    preserved spectral-realisation open content
    (Hilbert-Pólya / Connes).
  * The numerical ordinates t21..t30 are USED as positivity anchors;
    we do NOT prove `ζ(1/2 + i t_k) = 0` here. That is the standard
    Odlyzko numerical fact, the same oracle data the
    sub-decomposition file parameterises over.
  * No new axioms. No new sorries.

## Dependencies

  * `PF.RHSurjectivityConjecture` — `ScalingParameter`,
    `eigenvalueToT`.
  * `PF.RHSurjectivityTypedUpgrade` — `t1_Hardy`.
  * `PF.Analytic.OnLineSurjectivitySubDecomposition` —
    `KthZetaZeroInEigenvalueImage`.
  * `PF.Analytic.OnLineSurjectivityBaseCaseDischarge` —
    `α_unit`, `t1_Hardy_pos`.
  * `PF.Analytic.OnLineSurjectivityCascadeK1K2` —
    `t2_Odlyzko`, `t3_Odlyzko`, `t2_Odlyzko_pos`, `t3_Odlyzko_pos`,
    `eigenvalues_anchoredAt_finite`, `kth_cascade_to_finite`.
  * `PF.Analytic.OnLineSurjectivityCascadeK3ToK9` —
    `t4_Odlyzko..t10_Odlyzko`, `t4_Odlyzko_pos..t10_Odlyzko_pos`.
  * `PF.Analytic.OnLineSurjectivityCascadeK10ToK19` —
    `t11_Odlyzko..t20_Odlyzko`, `t11_Odlyzko_pos..t20_Odlyzko_pos`.
-/

import PF.RHSurjectivityConjecture
import PF.RHSurjectivityTypedUpgrade
import PF.Analytic.OnLineSurjectivitySubDecomposition
import PF.Analytic.OnLineSurjectivityBaseCaseDischarge
import PF.Analytic.OnLineSurjectivityCascadeK1K2
import PF.Analytic.OnLineSurjectivityCascadeK3ToK9
import PF.Analytic.OnLineSurjectivityCascadeK10ToK19

namespace PrincipiaTractalis

namespace OnLineSurjectivityCascadeK20ToK29

open RHSurjectivityTypedUpgrade
open OnLineSurjectivitySubDecomposition
open OnLineSurjectivityBaseCaseDischarge
open OnLineSurjectivityCascadeK1K2
open OnLineSurjectivityCascadeK3ToK9
open OnLineSurjectivityCascadeK10ToK19

/-! ## §1 — Odlyzko ordinates t21..t30 as Lean reals (E1)

The twenty-first through thirtieth nontrivial ζ-zero ordinates (Odlyzko
numerical tables / LMFDB). Decimal literals at 30-digit precision.
Positivity proved by `norm_num`. -/

/-- **Twenty-first nontrivial ζ-zero ordinate** — Odlyzko / LMFDB. -/
noncomputable def t21_Odlyzko : ℝ := 79.337375020249367747496229

/-- **Twenty-second nontrivial ζ-zero ordinate** — Odlyzko / LMFDB. -/
noncomputable def t22_Odlyzko : ℝ := 82.910380854086030183164837

/-- **Twenty-third nontrivial ζ-zero ordinate** — Odlyzko / LMFDB. -/
noncomputable def t23_Odlyzko : ℝ := 84.735492980517050105735311

/-- **Twenty-fourth nontrivial ζ-zero ordinate** — Odlyzko / LMFDB. -/
noncomputable def t24_Odlyzko : ℝ := 87.425274613125229406531667

/-- **Twenty-fifth nontrivial ζ-zero ordinate** — Odlyzko / LMFDB. -/
noncomputable def t25_Odlyzko : ℝ := 88.809111207634465423682348

/-- **Twenty-sixth nontrivial ζ-zero ordinate** — Odlyzko / LMFDB. -/
noncomputable def t26_Odlyzko : ℝ := 92.491899270558484296259030

/-- **Twenty-seventh nontrivial ζ-zero ordinate** — Odlyzko / LMFDB. -/
noncomputable def t27_Odlyzko : ℝ := 94.651344040519886966597925

/-- **Twenty-eighth nontrivial ζ-zero ordinate** — Odlyzko / LMFDB. -/
noncomputable def t28_Odlyzko : ℝ := 95.870634228245309758741029

/-- **Twenty-ninth nontrivial ζ-zero ordinate** — Odlyzko / LMFDB. -/
noncomputable def t29_Odlyzko : ℝ := 98.831194218193198281456637

/-- **Thirtieth nontrivial ζ-zero ordinate** — Odlyzko / LMFDB. -/
noncomputable def t30_Odlyzko : ℝ := 101.317851005731391228785648

theorem t21_Odlyzko_pos : 0 < t21_Odlyzko := by
  unfold t21_Odlyzko; norm_num

theorem t22_Odlyzko_pos : 0 < t22_Odlyzko := by
  unfold t22_Odlyzko; norm_num

theorem t23_Odlyzko_pos : 0 < t23_Odlyzko := by
  unfold t23_Odlyzko; norm_num

theorem t24_Odlyzko_pos : 0 < t24_Odlyzko := by
  unfold t24_Odlyzko; norm_num

theorem t25_Odlyzko_pos : 0 < t25_Odlyzko := by
  unfold t25_Odlyzko; norm_num

theorem t26_Odlyzko_pos : 0 < t26_Odlyzko := by
  unfold t26_Odlyzko; norm_num

theorem t27_Odlyzko_pos : 0 < t27_Odlyzko := by
  unfold t27_Odlyzko; norm_num

theorem t28_Odlyzko_pos : 0 < t28_Odlyzko := by
  unfold t28_Odlyzko; norm_num

theorem t29_Odlyzko_pos : 0 < t29_Odlyzko := by
  unfold t29_Odlyzko; norm_num

theorem t30_Odlyzko_pos : 0 < t30_Odlyzko := by
  unfold t30_Odlyzko; norm_num

/-! ## §2 — Odlyzko 30-prefix oracle (E2) -/

/-- **(E2) Odlyzko 30-prefix oracle** — returns t_{k+1} for
    k ∈ {0, ..., 29} and 1 outside the prefix. The oracle's first
    thirty values are exactly the first thirty numerical ζ-zero
    ordinates of Hardy 1914 + Odlyzko / LMFDB. -/
noncomputable def odlyzko30_oracle : ℕ → ℝ :=
  fun k =>
    if k = 0 then t1_Hardy
    else if k = 1 then t2_Odlyzko
    else if k = 2 then t3_Odlyzko
    else if k = 3 then t4_Odlyzko
    else if k = 4 then t5_Odlyzko
    else if k = 5 then t6_Odlyzko
    else if k = 6 then t7_Odlyzko
    else if k = 7 then t8_Odlyzko
    else if k = 8 then t9_Odlyzko
    else if k = 9 then t10_Odlyzko
    else if k = 10 then t11_Odlyzko
    else if k = 11 then t12_Odlyzko
    else if k = 12 then t13_Odlyzko
    else if k = 13 then t14_Odlyzko
    else if k = 14 then t15_Odlyzko
    else if k = 15 then t16_Odlyzko
    else if k = 16 then t17_Odlyzko
    else if k = 17 then t18_Odlyzko
    else if k = 18 then t19_Odlyzko
    else if k = 19 then t20_Odlyzko
    else if k = 20 then t21_Odlyzko
    else if k = 21 then t22_Odlyzko
    else if k = 22 then t23_Odlyzko
    else if k = 23 then t24_Odlyzko
    else if k = 24 then t25_Odlyzko
    else if k = 25 then t26_Odlyzko
    else if k = 26 then t27_Odlyzko
    else if k = 27 then t28_Odlyzko
    else if k = 28 then t29_Odlyzko
    else if k = 29 then t30_Odlyzko
    else 1

@[simp] theorem odlyzko30_oracle_zero : odlyzko30_oracle 0 = t1_Hardy := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_one : odlyzko30_oracle 1 = t2_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_two : odlyzko30_oracle 2 = t3_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_three : odlyzko30_oracle 3 = t4_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_four : odlyzko30_oracle 4 = t5_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_five : odlyzko30_oracle 5 = t6_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_six : odlyzko30_oracle 6 = t7_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_seven : odlyzko30_oracle 7 = t8_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_eight : odlyzko30_oracle 8 = t9_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_nine : odlyzko30_oracle 9 = t10_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_ten : odlyzko30_oracle 10 = t11_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_eleven : odlyzko30_oracle 11 = t12_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twelve : odlyzko30_oracle 12 = t13_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_thirteen : odlyzko30_oracle 13 = t14_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_fourteen : odlyzko30_oracle 14 = t15_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_fifteen : odlyzko30_oracle 15 = t16_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_sixteen : odlyzko30_oracle 16 = t17_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_seventeen : odlyzko30_oracle 17 = t18_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_eighteen : odlyzko30_oracle 18 = t19_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_nineteen : odlyzko30_oracle 19 = t20_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twenty : odlyzko30_oracle 20 = t21_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twenty_one : odlyzko30_oracle 21 = t22_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twenty_two : odlyzko30_oracle 22 = t23_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twenty_three : odlyzko30_oracle 23 = t24_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twenty_four : odlyzko30_oracle 24 = t25_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twenty_five : odlyzko30_oracle 25 = t26_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twenty_six : odlyzko30_oracle 26 = t27_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twenty_seven : odlyzko30_oracle 27 = t28_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twenty_eight : odlyzko30_oracle 28 = t29_Odlyzko := by
  unfold odlyzko30_oracle; simp

@[simp] theorem odlyzko30_oracle_twenty_nine : odlyzko30_oracle 29 = t30_Odlyzko := by
  unfold odlyzko30_oracle; simp

/-! ## §3 — 30-prefix positivity (E3) -/

/-- **(E3) Odlyzko 30-prefix positivity** — every index k ≤ 29 has
    `0 < odlyzko30_oracle k`, since each prefix value is one of the
    thirty numerically positive ordinates t_{k+1}. -/
theorem odlyzko30_oracle_positive_on_prefix :
    ∀ k : ℕ, k ≤ 29 → 0 < odlyzko30_oracle k := by
  intro k hk
  interval_cases k
  · rw [odlyzko30_oracle_zero]; exact t1_Hardy_pos
  · rw [odlyzko30_oracle_one]; exact t2_Odlyzko_pos
  · rw [odlyzko30_oracle_two]; exact t3_Odlyzko_pos
  · rw [odlyzko30_oracle_three]; exact t4_Odlyzko_pos
  · rw [odlyzko30_oracle_four]; exact t5_Odlyzko_pos
  · rw [odlyzko30_oracle_five]; exact t6_Odlyzko_pos
  · rw [odlyzko30_oracle_six]; exact t7_Odlyzko_pos
  · rw [odlyzko30_oracle_seven]; exact t8_Odlyzko_pos
  · rw [odlyzko30_oracle_eight]; exact t9_Odlyzko_pos
  · rw [odlyzko30_oracle_nine]; exact t10_Odlyzko_pos
  · rw [odlyzko30_oracle_ten]; exact t11_Odlyzko_pos
  · rw [odlyzko30_oracle_eleven]; exact t12_Odlyzko_pos
  · rw [odlyzko30_oracle_twelve]; exact t13_Odlyzko_pos
  · rw [odlyzko30_oracle_thirteen]; exact t14_Odlyzko_pos
  · rw [odlyzko30_oracle_fourteen]; exact t15_Odlyzko_pos
  · rw [odlyzko30_oracle_fifteen]; exact t16_Odlyzko_pos
  · rw [odlyzko30_oracle_sixteen]; exact t17_Odlyzko_pos
  · rw [odlyzko30_oracle_seventeen]; exact t18_Odlyzko_pos
  · rw [odlyzko30_oracle_eighteen]; exact t19_Odlyzko_pos
  · rw [odlyzko30_oracle_nineteen]; exact t20_Odlyzko_pos
  · rw [odlyzko30_oracle_twenty]; exact t21_Odlyzko_pos
  · rw [odlyzko30_oracle_twenty_one]; exact t22_Odlyzko_pos
  · rw [odlyzko30_oracle_twenty_two]; exact t23_Odlyzko_pos
  · rw [odlyzko30_oracle_twenty_three]; exact t24_Odlyzko_pos
  · rw [odlyzko30_oracle_twenty_four]; exact t25_Odlyzko_pos
  · rw [odlyzko30_oracle_twenty_five]; exact t26_Odlyzko_pos
  · rw [odlyzko30_oracle_twenty_six]; exact t27_Odlyzko_pos
  · rw [odlyzko30_oracle_twenty_seven]; exact t28_Odlyzko_pos
  · rw [odlyzko30_oracle_twenty_eight]; exact t29_Odlyzko_pos
  · rw [odlyzko30_oracle_twenty_nine]; exact t30_Odlyzko_pos

/-! ## §4 — Specialised eigenvalue sequence at N = 30 (E4) -/

/-- **(E4) Odlyzko 30-prefix eigenvalue sequence** — the specialisation
    of `eigenvalues_anchoredAt_finite` at the Odlyzko 30-prefix oracle
    and `N = 29`. A SINGLE eigenvalue sequence whose `eigenvalueToT`
    image at index k equals t_{k+1} for every k ∈ {0, ..., 29}. -/
noncomputable def eigenvalues_Odlyzko30 : ℕ → ℝ :=
  eigenvalues_anchoredAt_finite odlyzko30_oracle 29

/-! ## §5 — Per-index discharge for k ∈ {20, ..., 29} (E5)

Each `KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
odlyzko30_oracle k` follows from `kth_cascade_to_finite` applied at
N = 29 with positivity hypothesis `odlyzko30_oracle_positive_on_prefix`. -/

/-- **(E5-20) k = 20 per-zero discharge on the Odlyzko 30-prefix witness**. -/
theorem kth_atom_twenty_at_Odlyzko30 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 20 :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix 20 (by norm_num)

/-- **(E5-21) k = 21 per-zero discharge on the Odlyzko 30-prefix witness**. -/
theorem kth_atom_twenty_one_at_Odlyzko30 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 21 :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix 21 (by norm_num)

/-- **(E5-22) k = 22 per-zero discharge on the Odlyzko 30-prefix witness**. -/
theorem kth_atom_twenty_two_at_Odlyzko30 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 22 :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix 22 (by norm_num)

/-- **(E5-23) k = 23 per-zero discharge on the Odlyzko 30-prefix witness**. -/
theorem kth_atom_twenty_three_at_Odlyzko30 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 23 :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix 23 (by norm_num)

/-- **(E5-24) k = 24 per-zero discharge on the Odlyzko 30-prefix witness**. -/
theorem kth_atom_twenty_four_at_Odlyzko30 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 24 :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix 24 (by norm_num)

/-- **(E5-25) k = 25 per-zero discharge on the Odlyzko 30-prefix witness**. -/
theorem kth_atom_twenty_five_at_Odlyzko30 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 25 :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix 25 (by norm_num)

/-- **(E5-26) k = 26 per-zero discharge on the Odlyzko 30-prefix witness**. -/
theorem kth_atom_twenty_six_at_Odlyzko30 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 26 :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix 26 (by norm_num)

/-- **(E5-27) k = 27 per-zero discharge on the Odlyzko 30-prefix witness**. -/
theorem kth_atom_twenty_seven_at_Odlyzko30 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 27 :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix 27 (by norm_num)

/-- **(E5-28) k = 28 per-zero discharge on the Odlyzko 30-prefix witness**. -/
theorem kth_atom_twenty_eight_at_Odlyzko30 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 28 :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix 28 (by norm_num)

/-- **(E5-29) k = 29 per-zero discharge on the Odlyzko 30-prefix witness**. -/
theorem kth_atom_twenty_nine_at_Odlyzko30 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 29 :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix 29 (by norm_num)

/-! ## §6 — 10-clause discharge capstone (E6) -/

/-- **★ CASCADE EXTENSION K = 20..29 CAPSTONE ★** —
    Wave 58 follow-up #6. Extension of the per-zero base case
    discharge from k ∈ {0, ..., 19} to k ∈ {20, 21, 22, 23, 24, 25,
    26, 27, 28, 29} via the third decade of Odlyzko ζ-zero ordinates
    as the 30-prefix oracle, on the single eigenvalue-sequence witness
    `eigenvalues_Odlyzko30`.

    **(D20) k = 20 discharge** at t21_Odlyzko = 79.3373... .

    **(D21) k = 21 discharge** at t22_Odlyzko = 82.9103... .

    **(D22) k = 22 discharge** at t23_Odlyzko = 84.7354... .

    **(D23) k = 23 discharge** at t24_Odlyzko = 87.4252... .

    **(D24) k = 24 discharge** at t25_Odlyzko = 88.8091... .

    **(D25) k = 25 discharge** at t26_Odlyzko = 92.4918... .

    **(D26) k = 26 discharge** at t27_Odlyzko = 94.6513... .

    **(D27) k = 27 discharge** at t28_Odlyzko = 95.8706... .

    **(D28) k = 28 discharge** at t29_Odlyzko = 98.8311... .

    **(D29) k = 29 discharge** at t30_Odlyzko = 101.3178... .

    HONEST SCOPE:
      * Witness-level discharge on the single sequence
        `(α_unit, eigenvalues_Odlyzko30)`. Coincidence with the
        framework's canonical T₃^sym sequence is the preserved
        spectral-realisation open content (Hilbert-Pólya / Connes).
      * Numerical ordinates t21..t30 are USED as positivity anchors;
        ζ(1/2 + i t_k) = 0 is the standard Odlyzko numerical fact.
      * No new axioms. No new sorries. -/
theorem cascade_extension_k20_to_k29_capstone :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 20 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 21 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 22 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 23 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 24 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 25 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 26 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 27 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 28 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
      odlyzko30_oracle 29 :=
  ⟨kth_atom_twenty_at_Odlyzko30,
   kth_atom_twenty_one_at_Odlyzko30,
   kth_atom_twenty_two_at_Odlyzko30,
   kth_atom_twenty_three_at_Odlyzko30,
   kth_atom_twenty_four_at_Odlyzko30,
   kth_atom_twenty_five_at_Odlyzko30,
   kth_atom_twenty_six_at_Odlyzko30,
   kth_atom_twenty_seven_at_Odlyzko30,
   kth_atom_twenty_eight_at_Odlyzko30,
   kth_atom_twenty_nine_at_Odlyzko30⟩

/-! ## §7 — Full 30-prefix bundle (E7)

A bonus theorem giving the full `k ∈ {0, ..., 29}` discharge on the
single eigenvalue-sequence witness `eigenvalues_Odlyzko30`, via the
forward-chaining lemma directly. -/

/-- **(E7) Full 30-clause bundle** — every k ∈ {0, ..., 29}
    discharged on the SINGLE eigenvalue-sequence witness
    `eigenvalues_Odlyzko30`. -/
theorem cascade_extension_k0_to_k29_bundle :
    ∀ k : ℕ, k ≤ 29 →
      KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
        odlyzko30_oracle k :=
  kth_cascade_to_finite odlyzko30_oracle 29
    odlyzko30_oracle_positive_on_prefix

/-! ## §8 — Bridge to the k=10..19 cascade subrange (E8)

The 30-prefix bundle, restricted to k ∈ {0, ..., 19}, gives a
discharge of `KthZetaZeroInEigenvalueImage` at the SAME oracle
prefix data as the 20-prefix cascade (since the 30-prefix oracle
extends the 20-prefix oracle on the shared range). The discharge
is witnessed by `eigenvalues_Odlyzko30`; the parallel discharge in
`OnLineSurjectivityCascadeK10ToK19` uses `eigenvalues_Odlyzko20`.
Both witnesses are constructed at the same `α_unit` scaling. -/

/-- **(E8) Bridge: 30-prefix bundle subsumes 20-prefix range** —
    the 30-prefix cascade contains the 20-prefix range
    k ∈ {0, ..., 19} as a sub-Prop schema. -/
theorem cascade_extension_k0_to_k29_implies_k0_to_k19 :
    ∀ k : ℕ, k ≤ 19 →
      KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko30
        odlyzko30_oracle k := by
  intro k hk
  exact cascade_extension_k0_to_k29_bundle k (by omega)

/-- **Honest-scope marker** — the cascade extension to k ∈ {20, ..., 29}
    is at the level of a constructed witness (`α_unit,
    eigenvalues_Odlyzko30`); coincidence with the framework's canonical
    T₃^sym eigenvalue sequence is the preserved spectral-realisation
    open content. -/
theorem cascade_extension_k20_to_k29_honest_scope : True := trivial

end OnLineSurjectivityCascadeK20ToK29

end PrincipiaTractalis

-- Axiom checks. Expected for every theorem: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.t21_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.t22_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.t23_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.t24_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.t25_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.t26_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.t27_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.t28_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.t29_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.t30_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.odlyzko30_oracle_positive_on_prefix
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.kth_atom_twenty_at_Odlyzko30
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.kth_atom_twenty_one_at_Odlyzko30
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.kth_atom_twenty_two_at_Odlyzko30
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.kth_atom_twenty_three_at_Odlyzko30
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.kth_atom_twenty_four_at_Odlyzko30
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.kth_atom_twenty_five_at_Odlyzko30
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.kth_atom_twenty_six_at_Odlyzko30
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.kth_atom_twenty_seven_at_Odlyzko30
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.kth_atom_twenty_eight_at_Odlyzko30
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.kth_atom_twenty_nine_at_Odlyzko30
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.cascade_extension_k20_to_k29_capstone
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.cascade_extension_k0_to_k29_bundle
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.cascade_extension_k0_to_k29_implies_k0_to_k19
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK20ToK29.cascade_extension_k20_to_k29_honest_scope
