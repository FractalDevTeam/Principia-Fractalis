/-
# On-Line Surjectivity (C3) — CASCADE EXTENSION K = 3..9 (Odlyzko prefix)

★ 2026-06-02 — Wave 58 follow-up #4. Extension of the per-zero cascade
from k ∈ {0, 1, 2} (handled by `OnLineSurjectivityCascadeK1K2`) to
k ∈ {0, ..., 9}, anchored at the first ten numerical Odlyzko ζ-zero
ordinates:

    t1  = 14.134725141734693790457251983562   (Hardy 1914)
    t2  = 21.022039638771554992628479593897   (Odlyzko)
    t3  = 25.010857580145688763213790992562   (Odlyzko)
    t4  = 30.424876125859513210311897530584   (Odlyzko)
    t5  = 32.935061587739189690662368964075   (Odlyzko)
    t6  = 37.586178158825671257217763480705   (Odlyzko)
    t7  = 40.918719012147495187398126914634   (Odlyzko)
    t8  = 43.327073280914999519496122165407   (Odlyzko)
    t9  = 48.005150881167159727942472749427   (Odlyzko)
    t10 = 49.773832477672302181916784678563   (Odlyzko)

## Strategic context

`OnLineSurjectivityCascadeK1K2` provided two routes:

  (a) The triple-anchor witness `eigenvalues_anchoredAt3 t1 t2 t3`
      which discharges k ∈ {0, 1, 2} simultaneously on one sequence.

  (b) The forward-chaining lemma `kth_cascade_to_finite` which
      discharges k ∈ {0, ..., N} on the sequence
      `eigenvalues_anchoredAt_finite oracle N`, GIVEN positivity of
      `oracle k` for every k ≤ N.

Route (b) already covers k ∈ {3, ..., 9} abstractly. This file
SPECIALISES route (b) at N = 9 to the actual numerical Odlyzko 10-prefix
oracle, giving an explicit per-index discharge of
`KthZetaZeroInEigenvalueImage` for each k ∈ {3, 4, 5, 6, 7, 8, 9},
axiom-free, with each `t_{k+1} > 0` proved by `norm_num`.

## What this file delivers (axiom-free)

  **E1 — Odlyzko ordinates t4..t10 as Lean reals**
    `t4_Odlyzko, t5_Odlyzko, ..., t10_Odlyzko : ℝ`, each with a
    `norm_num` positivity record.

  **E2 — Odlyzko 10-prefix oracle**
    `odlyzko10_oracle : ℕ → ℝ` defined to return t_{k+1} for
    k ∈ {0, ..., 9} and 1 outside the prefix.

  **E3 — 10-prefix positivity**
    `odlyzko10_oracle_positive_on_prefix` — every k ≤ 9 has
    `0 < odlyzko10_oracle k`.

  **E4 — Specialised eigenvalue sequence at N = 10**
    `eigenvalues_Odlyzko10 := eigenvalues_anchoredAt_finite
      odlyzko10_oracle 9` — a single eigenvalue sequence whose
    `eigenvalueToT` image at index k equals t_{k+1} for every
    k ∈ {0, ..., 9}.

  **E5 — Per-index discharge for k ∈ {3, ..., 9}**
    Seven theorems
      `kth_atom_three_at_Odlyzko10`, ...,
      `kth_atom_nine_at_Odlyzko10`,
    each proving
    `KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
       odlyzko10_oracle k`
    by direct invocation of `kth_cascade_to_finite`.

  **E6 — 7-clause discharge capstone**
    `cascade_extension_k3_to_k9_capstone` bundles all seven per-index
    discharges as one citable conjunction.

## Honest scope

  * The discharge is at the level of a CONSTRUCTED witness
    `(α_unit, eigenvalues_Odlyzko10)`. Coincidence with the
    framework's canonical T₃^sym eigenvalue sequence remains the
    preserved spectral-realisation open content
    (Hilbert-Pólya / Connes).
  * The numerical ordinates t4..t10 are USED as positivity anchors;
    we do NOT prove `ζ(1/2 + i t_k) = 0` here. That is the standard
    Odlyzko numerical fact, the same oracle data the
    sub-decomposition file parameterises over.
  * No new axioms. No new sorries.

## Build

ZERO project axioms. ZERO sorries.

Depends on:
  * `PF.RHSurjectivityConjecture` — `ScalingParameter`,
    `eigenvalueToT`.
  * `PF.RHSurjectivityTypedUpgrade` — `t1_Hardy`.
  * `PF.Analytic.OnLineSurjectivitySubDecomposition` —
    `KthZetaZeroInEigenvalueImage`.
  * `PF.Analytic.OnLineSurjectivityBaseCaseDischarge` —
    `α_unit`, `eigenvalueToT_inverse_at_positive_target`,
    `α_unit_value`, `t1_Hardy_pos`.
  * `PF.Analytic.OnLineSurjectivityCascadeK1K2` —
    `t2_Odlyzko`, `t3_Odlyzko`, `t2_Odlyzko_pos`, `t3_Odlyzko_pos`,
    `eigenvalues_anchoredAt_finite`, `kth_cascade_to_finite`.

Author: Claude Opus 4.7. 2026-06-02. Wave 58 follow-up #4.
-/

import PF.RHSurjectivityConjecture
import PF.RHSurjectivityTypedUpgrade
import PF.Analytic.OnLineSurjectivitySubDecomposition
import PF.Analytic.OnLineSurjectivityBaseCaseDischarge
import PF.Analytic.OnLineSurjectivityCascadeK1K2

namespace PrincipiaTractalis

namespace OnLineSurjectivityCascadeK3ToK9

open RHSurjectivityTypedUpgrade
open OnLineSurjectivitySubDecomposition
open OnLineSurjectivityBaseCaseDischarge
open OnLineSurjectivityCascadeK1K2

/-! ## §1 — Odlyzko ordinates t4..t10 as Lean reals (E1)

The fourth through tenth nontrivial ζ-zero ordinates (Odlyzko numerical
tables). Decimal literals at the standard published precision. Positivity
proved by `norm_num`. -/

/-- **Fourth nontrivial ζ-zero ordinate** — Odlyzko. -/
noncomputable def t4_Odlyzko : ℝ := 30.424876125859513210311897530584

/-- **Fifth nontrivial ζ-zero ordinate** — Odlyzko. -/
noncomputable def t5_Odlyzko : ℝ := 32.935061587739189690662368964075

/-- **Sixth nontrivial ζ-zero ordinate** — Odlyzko. -/
noncomputable def t6_Odlyzko : ℝ := 37.586178158825671257217763480705

/-- **Seventh nontrivial ζ-zero ordinate** — Odlyzko. -/
noncomputable def t7_Odlyzko : ℝ := 40.918719012147495187398126914634

/-- **Eighth nontrivial ζ-zero ordinate** — Odlyzko. -/
noncomputable def t8_Odlyzko : ℝ := 43.327073280914999519496122165407

/-- **Ninth nontrivial ζ-zero ordinate** — Odlyzko. -/
noncomputable def t9_Odlyzko : ℝ := 48.005150881167159727942472749427

/-- **Tenth nontrivial ζ-zero ordinate** — Odlyzko. -/
noncomputable def t10_Odlyzko : ℝ := 49.773832477672302181916784678563

theorem t4_Odlyzko_pos : 0 < t4_Odlyzko := by
  unfold t4_Odlyzko; norm_num

theorem t5_Odlyzko_pos : 0 < t5_Odlyzko := by
  unfold t5_Odlyzko; norm_num

theorem t6_Odlyzko_pos : 0 < t6_Odlyzko := by
  unfold t6_Odlyzko; norm_num

theorem t7_Odlyzko_pos : 0 < t7_Odlyzko := by
  unfold t7_Odlyzko; norm_num

theorem t8_Odlyzko_pos : 0 < t8_Odlyzko := by
  unfold t8_Odlyzko; norm_num

theorem t9_Odlyzko_pos : 0 < t9_Odlyzko := by
  unfold t9_Odlyzko; norm_num

theorem t10_Odlyzko_pos : 0 < t10_Odlyzko := by
  unfold t10_Odlyzko; norm_num

/-! ## §2 — Odlyzko 10-prefix oracle (E2) -/

/-- **(E2) Odlyzko 10-prefix oracle** — returns t_{k+1} for
    k ∈ {0, ..., 9} and 1 outside the prefix. The oracle's first ten
    values are exactly the first ten numerical ζ-zero ordinates of
    Hardy 1914 + Odlyzko. -/
noncomputable def odlyzko10_oracle : ℕ → ℝ :=
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
    else 1

@[simp] theorem odlyzko10_oracle_zero : odlyzko10_oracle 0 = t1_Hardy := by
  unfold odlyzko10_oracle; simp

@[simp] theorem odlyzko10_oracle_one : odlyzko10_oracle 1 = t2_Odlyzko := by
  unfold odlyzko10_oracle; simp

@[simp] theorem odlyzko10_oracle_two : odlyzko10_oracle 2 = t3_Odlyzko := by
  unfold odlyzko10_oracle; simp

@[simp] theorem odlyzko10_oracle_three : odlyzko10_oracle 3 = t4_Odlyzko := by
  unfold odlyzko10_oracle; simp

@[simp] theorem odlyzko10_oracle_four : odlyzko10_oracle 4 = t5_Odlyzko := by
  unfold odlyzko10_oracle; simp

@[simp] theorem odlyzko10_oracle_five : odlyzko10_oracle 5 = t6_Odlyzko := by
  unfold odlyzko10_oracle; simp

@[simp] theorem odlyzko10_oracle_six : odlyzko10_oracle 6 = t7_Odlyzko := by
  unfold odlyzko10_oracle; simp

@[simp] theorem odlyzko10_oracle_seven : odlyzko10_oracle 7 = t8_Odlyzko := by
  unfold odlyzko10_oracle; simp

@[simp] theorem odlyzko10_oracle_eight : odlyzko10_oracle 8 = t9_Odlyzko := by
  unfold odlyzko10_oracle; simp

@[simp] theorem odlyzko10_oracle_nine : odlyzko10_oracle 9 = t10_Odlyzko := by
  unfold odlyzko10_oracle; simp

/-! ## §3 — 10-prefix positivity (E3) -/

/-- **(E3) Odlyzko 10-prefix positivity** — every index k ≤ 9 has
    `0 < odlyzko10_oracle k`, since each prefix value is one of the
    ten numerically positive ordinates t_{k+1}. -/
theorem odlyzko10_oracle_positive_on_prefix :
    ∀ k : ℕ, k ≤ 9 → 0 < odlyzko10_oracle k := by
  intro k hk
  interval_cases k
  · rw [odlyzko10_oracle_zero]; exact t1_Hardy_pos
  · rw [odlyzko10_oracle_one]; exact t2_Odlyzko_pos
  · rw [odlyzko10_oracle_two]; exact t3_Odlyzko_pos
  · rw [odlyzko10_oracle_three]; exact t4_Odlyzko_pos
  · rw [odlyzko10_oracle_four]; exact t5_Odlyzko_pos
  · rw [odlyzko10_oracle_five]; exact t6_Odlyzko_pos
  · rw [odlyzko10_oracle_six]; exact t7_Odlyzko_pos
  · rw [odlyzko10_oracle_seven]; exact t8_Odlyzko_pos
  · rw [odlyzko10_oracle_eight]; exact t9_Odlyzko_pos
  · rw [odlyzko10_oracle_nine]; exact t10_Odlyzko_pos

/-! ## §4 — Specialised eigenvalue sequence at N = 10 (E4) -/

/-- **(E4) Odlyzko 10-prefix eigenvalue sequence** — the specialisation
    of `eigenvalues_anchoredAt_finite` at the Odlyzko 10-prefix oracle
    and `N = 9`. A SINGLE eigenvalue sequence whose `eigenvalueToT`
    image at index k equals t_{k+1} for every k ∈ {0, ..., 9}. -/
noncomputable def eigenvalues_Odlyzko10 : ℕ → ℝ :=
  eigenvalues_anchoredAt_finite odlyzko10_oracle 9

/-! ## §5 — Per-index discharge for k ∈ {3, ..., 9} (E5)

Each `KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
odlyzko10_oracle k` follows from `kth_cascade_to_finite` applied at
N = 9 with positivity hypothesis `odlyzko10_oracle_positive_on_prefix`. -/

/-- **(E5-3) k = 3 per-zero discharge on the Odlyzko 10-prefix witness**. -/
theorem kth_atom_three_at_Odlyzko10 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 3 :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix 3 (by norm_num)

/-- **(E5-4) k = 4 per-zero discharge on the Odlyzko 10-prefix witness**. -/
theorem kth_atom_four_at_Odlyzko10 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 4 :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix 4 (by norm_num)

/-- **(E5-5) k = 5 per-zero discharge on the Odlyzko 10-prefix witness**. -/
theorem kth_atom_five_at_Odlyzko10 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 5 :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix 5 (by norm_num)

/-- **(E5-6) k = 6 per-zero discharge on the Odlyzko 10-prefix witness**. -/
theorem kth_atom_six_at_Odlyzko10 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 6 :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix 6 (by norm_num)

/-- **(E5-7) k = 7 per-zero discharge on the Odlyzko 10-prefix witness**. -/
theorem kth_atom_seven_at_Odlyzko10 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 7 :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix 7 (by norm_num)

/-- **(E5-8) k = 8 per-zero discharge on the Odlyzko 10-prefix witness**. -/
theorem kth_atom_eight_at_Odlyzko10 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 8 :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix 8 (by norm_num)

/-- **(E5-9) k = 9 per-zero discharge on the Odlyzko 10-prefix witness**. -/
theorem kth_atom_nine_at_Odlyzko10 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 9 :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix 9 (by norm_num)

/-! ## §6 — 7-clause discharge capstone (E6) -/

/-- **★ CASCADE EXTENSION K = 3..9 CAPSTONE ★** —
    Wave 58 follow-up #4. Extension of the per-zero base case
    discharge from k ∈ {0, 1, 2} to k ∈ {3, 4, 5, 6, 7, 8, 9} via the
    first ten Odlyzko ζ-zero ordinates as the 10-prefix oracle, on the
    single eigenvalue-sequence witness `eigenvalues_Odlyzko10`.

    **(D3) k = 3 discharge** at t4_Odlyzko = 30.4248... .

    **(D4) k = 4 discharge** at t5_Odlyzko = 32.9351... .

    **(D5) k = 5 discharge** at t6_Odlyzko = 37.5862... .

    **(D6) k = 6 discharge** at t7_Odlyzko = 40.9187... .

    **(D7) k = 7 discharge** at t8_Odlyzko = 43.3271... .

    **(D8) k = 8 discharge** at t9_Odlyzko = 48.0052... .

    **(D9) k = 9 discharge** at t10_Odlyzko = 49.7738... .

    HONEST SCOPE:
      * Witness-level discharge on the single sequence
        `(α_unit, eigenvalues_Odlyzko10)`. Coincidence with the
        framework's canonical T₃^sym sequence is the preserved
        spectral-realisation open content (Hilbert-Pólya / Connes).
      * Numerical ordinates t4..t10 are USED as positivity anchors;
        ζ(1/2 + i t_k) = 0 is the standard Odlyzko numerical fact.
      * No new axioms. No new sorries. -/
theorem cascade_extension_k3_to_k9_capstone :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 3 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 4 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 5 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 6 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 7 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 8 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 9 :=
  ⟨kth_atom_three_at_Odlyzko10,
   kth_atom_four_at_Odlyzko10,
   kth_atom_five_at_Odlyzko10,
   kth_atom_six_at_Odlyzko10,
   kth_atom_seven_at_Odlyzko10,
   kth_atom_eight_at_Odlyzko10,
   kth_atom_nine_at_Odlyzko10⟩

/-! ## §7 — Full 10-prefix bundle (bonus)

A bonus theorem combining the k ∈ {0, 1, 2} cascade (from
`OnLineSurjectivityCascadeK1K2`'s `kth_cascade_to_finite` at the same
Odlyzko 10-prefix oracle) with the k ∈ {3, ..., 9} cascade of this file,
to give a single 10-clause bundle on the single eigenvalue-sequence
witness `eigenvalues_Odlyzko10`. -/

/-- **(Bonus) k = 0 on the Odlyzko 10-prefix witness**. -/
theorem kth_atom_zero_at_Odlyzko10 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 0 :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix 0 (by norm_num)

/-- **(Bonus) k = 1 on the Odlyzko 10-prefix witness**. -/
theorem kth_atom_one_at_Odlyzko10 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 1 :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix 1 (by norm_num)

/-- **(Bonus) k = 2 on the Odlyzko 10-prefix witness**. -/
theorem kth_atom_two_at_Odlyzko10 :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
      odlyzko10_oracle 2 :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix 2 (by norm_num)

/-- **(Bonus 10-clause bundle)** — every k ∈ {0, ..., 9} discharged on
    the SINGLE eigenvalue-sequence witness `eigenvalues_Odlyzko10`. -/
theorem cascade_extension_k0_to_k9_bundle :
    ∀ k : ℕ, k ≤ 9 →
      KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko10
        odlyzko10_oracle k :=
  kth_cascade_to_finite odlyzko10_oracle 9
    odlyzko10_oracle_positive_on_prefix

/-- **Honest-scope marker** — the cascade extension to k ∈ {3, ..., 9}
    is at the level of a constructed witness (`α_unit,
    eigenvalues_Odlyzko10`); coincidence with the framework's canonical
    T₃^sym eigenvalue sequence is the preserved spectral-realisation
    open content. -/
theorem cascade_extension_k3_to_k9_honest_scope : True := trivial

end OnLineSurjectivityCascadeK3ToK9

end PrincipiaTractalis

-- Axiom checks. Expected for every theorem: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.t4_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.t5_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.t6_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.t7_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.t8_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.t9_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.t10_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.odlyzko10_oracle_positive_on_prefix
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.kth_atom_three_at_Odlyzko10
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.kth_atom_four_at_Odlyzko10
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.kth_atom_five_at_Odlyzko10
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.kth_atom_six_at_Odlyzko10
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.kth_atom_seven_at_Odlyzko10
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.kth_atom_eight_at_Odlyzko10
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.kth_atom_nine_at_Odlyzko10
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.cascade_extension_k3_to_k9_capstone
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.cascade_extension_k0_to_k9_bundle
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK3ToK9.cascade_extension_k3_to_k9_honest_scope
