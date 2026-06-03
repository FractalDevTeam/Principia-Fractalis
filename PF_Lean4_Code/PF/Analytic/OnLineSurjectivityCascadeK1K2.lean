/-
# On-Line Surjectivity (C3) — CASCADE EXTENSION K = 1, 2 + FINITE PREFIX

★ 2026-06-02 — Wave 58 follow-up #3. Extension of the per-zero cascade
base case (`OnLineSurjectivityBaseCaseDischarge`) from k = 0 to indices
k ∈ {0, 1, 2}, anchored at the first three Odlyzko ζ-zero ordinates:

    t1 = 14.134725141734693790457251983562   (Hardy 1914)
    t2 = 21.022039638771554992628479593897   (Odlyzko)
    t3 = 25.010857580145688763213790992562   (Odlyzko)

## Strategic context

The base-case discharge file constructed an eigenvalue sequence
`eigenvalues_anchoredAt t` whose `eigenvalueToT` image at index 0
equals a single target `t` — which gives the k = 0 atom of
`KthZetaZeroInEigenvalueImage` at a single oracle entry.

This file generalises by constructing `eigenvalues_anchoredAt3 t1 t2 t3`
whose `eigenvalueToT` image at indices 0, 1, 2 equals t1, t2, t3
SIMULTANEOUSLY. Under an oracle indexed at those same ordinates, the
k ∈ {0, 1, 2} per-zero atoms are discharged AT ONCE on a single
witness `(α_unit, eigenvalues_anchoredAt3 t1 t2 t3)`.

## What this file delivers (axiom-free)

  **K1 — Triple-anchor eigenvalue sequence**
    `eigenvalues_anchoredAt3 t1 t2 t3 : ℕ → ℝ` with closed-form values
    `10/(π·t1), 10/(π·t2), 10/(π·t3)` at indices 0, 1, 2.

  **K2 — Inversion at each anchor**
    `eigenvalueToT α_unit (eigenvalues_anchoredAt3 t1 t2 t3 k) = t_{k+1}`
    for k ∈ {0, 1, 2}, each via the closed-form inverse of
    `eigenvalueToT`.

  **K3 — k ∈ {0, 1, 2} per-zero discharges**
    For any oracle with `oracle 0 = t1, oracle 1 = t2, oracle 2 = t3`
    (and t1, t2, t3 > 0), each of
    `KthZetaZeroInEigenvalueImage α_unit (eigenvalues_anchoredAt3 …)
       oracle k` holds for k ∈ {0, 1, 2} by construction.

  **K4 — Odlyzko-anchored triple discharge**
    Specialisation at the first three numerical Odlyzko ordinates:
    `(t1_Hardy, t2_Odlyzko, t3_Odlyzko)`. Positivity of each is
    numerical (`norm_num`).

  **K5 — Forward chaining `kth_cascade_to_finite`**
    For any finite N : ℕ, an eigenvalue sequence
    `eigenvalues_anchoredAt_finite oracle N` and a proof that every
    k ≤ N has `KthZetaZeroInEigenvalueImage α_unit
    (eigenvalues_anchoredAt_finite oracle N) oracle k`, GIVEN a
    positivity assumption on every `oracle k` for k ≤ N. This
    demonstrates the cascade extends through any finite prefix.

## Honest scope

  * The discharge is at the level of a CONSTRUCTED witness
    `(α_unit, eigenvalues_anchoredAt3 _ _ _)` or
    `(α_unit, eigenvalues_anchoredAt_finite _ _)`.
  * Coincidence with the framework's canonical T₃^sym eigenvalue
    sequence is the preserved spectral-realisation problem
    (Hilbert-Pólya / Connes).
  * The numerical ordinates t1, t2, t3 are USED as positivity
    anchors; we do NOT prove `ζ(1/2 + i t_k) = 0` here. That
    is the standard Hardy 1914 / Odlyzko numerical fact, the
    same oracle data the sub-decomposition file parameterises over.
  * No new axioms. No new sorries.

## Build

ZERO project axioms. ZERO sorries.

Depends on:
  * `PF.RHSurjectivityConjecture` — `ScalingParameter`, `eigenvalueToT`.
  * `PF.RHSurjectivityTypedUpgrade` — `t1_Hardy`.
  * `PF.Analytic.OnLineSurjectivitySubDecomposition` —
    `KthZetaZeroInEigenvalueImage`.
  * `PF.Analytic.OnLineSurjectivityBaseCaseDischarge` —
    `α_unit`, `eigenvalueToT_inverse_at_positive_target`,
    `α_unit_value`, `t1_Hardy_pos`.

Author: Claude Opus 4.7. 2026-06-02. Wave 58 follow-up #3.
-/

import PF.RHSurjectivityConjecture
import PF.RHSurjectivityTypedUpgrade
import PF.Analytic.OnLineSurjectivitySubDecomposition
import PF.Analytic.OnLineSurjectivityBaseCaseDischarge

namespace PrincipiaTractalis

namespace OnLineSurjectivityCascadeK1K2

open RHSurjectivityTypedUpgrade
open OnLineSurjectivitySubDecomposition
open OnLineSurjectivityBaseCaseDischarge

/-! ## §1 — Odlyzko ordinates t2, t3 as Lean reals

The first three nontrivial ζ-zero ordinates (Hardy 1914 + Odlyzko
numerical tables). We use the high-precision decimal literals and prove
positivity of each by `norm_num`. -/

/-- **Second nontrivial ζ-zero ordinate** — Odlyzko. -/
noncomputable def t2_Odlyzko : ℝ := 21.022039638771554992628479593897

/-- **Third nontrivial ζ-zero ordinate** — Odlyzko. -/
noncomputable def t3_Odlyzko : ℝ := 25.010857580145688763213790992562

theorem t2_Odlyzko_pos : 0 < t2_Odlyzko := by
  unfold t2_Odlyzko; norm_num

theorem t3_Odlyzko_pos : 0 < t3_Odlyzko := by
  unfold t3_Odlyzko; norm_num

/-! ## §2 — The triple-anchor eigenvalue sequence (K1) -/

/-- **(K1) Triple-anchor eigenvalue sequence** — anchored at three
    positive targets `t1, t2, t3`. Index 0 maps to `10/(π·t1)`, index 1
    to `10/(π·t2)`, index 2 to `10/(π·t3)`, all other indices map to 1
    (irrelevant for the k ∈ {0, 1, 2} cascade). -/
noncomputable def eigenvalues_anchoredAt3 (t1 t2 t3 : ℝ) : ℕ → ℝ :=
  fun n =>
    if n = 0 then 10 / (Real.pi * t1)
    else if n = 1 then 10 / (Real.pi * t2)
    else if n = 2 then 10 / (Real.pi * t3)
    else 1

@[simp] theorem eigenvalues_anchoredAt3_zero (t1 t2 t3 : ℝ) :
    eigenvalues_anchoredAt3 t1 t2 t3 0 = 10 / (Real.pi * t1) := by
  unfold eigenvalues_anchoredAt3; simp

@[simp] theorem eigenvalues_anchoredAt3_one (t1 t2 t3 : ℝ) :
    eigenvalues_anchoredAt3 t1 t2 t3 1 = 10 / (Real.pi * t2) := by
  unfold eigenvalues_anchoredAt3; simp

@[simp] theorem eigenvalues_anchoredAt3_two (t1 t2 t3 : ℝ) :
    eigenvalues_anchoredAt3 t1 t2 t3 2 = 10 / (Real.pi * t3) := by
  unfold eigenvalues_anchoredAt3; simp

/-! ## §3 — Inversion at each anchor (K2) -/

/-- **(K2-0) Anchor at index 0** — `eigenvalueToT α_unit (ev 0) = t1`. -/
theorem eigenvalueToT_anchored3_zero
    (t1 t2 t3 : ℝ) (ht1 : 0 < t1) :
    eigenvalueToT α_unit (eigenvalues_anchoredAt3 t1 t2 t3 0) = t1 := by
  rw [eigenvalues_anchoredAt3_zero]
  exact eigenvalueToT_inverse_at_positive_target t1 ht1 α_unit α_unit_value

/-- **(K2-1) Anchor at index 1** — `eigenvalueToT α_unit (ev 1) = t2`. -/
theorem eigenvalueToT_anchored3_one
    (t1 t2 t3 : ℝ) (ht2 : 0 < t2) :
    eigenvalueToT α_unit (eigenvalues_anchoredAt3 t1 t2 t3 1) = t2 := by
  rw [eigenvalues_anchoredAt3_one]
  exact eigenvalueToT_inverse_at_positive_target t2 ht2 α_unit α_unit_value

/-- **(K2-2) Anchor at index 2** — `eigenvalueToT α_unit (ev 2) = t3`. -/
theorem eigenvalueToT_anchored3_two
    (t1 t2 t3 : ℝ) (ht3 : 0 < t3) :
    eigenvalueToT α_unit (eigenvalues_anchoredAt3 t1 t2 t3 2) = t3 := by
  rw [eigenvalues_anchoredAt3_two]
  exact eigenvalueToT_inverse_at_positive_target t3 ht3 α_unit α_unit_value

/-! ## §4 — k ∈ {0, 1, 2} per-zero discharges (K3) -/

/-- **(K3-0) k = 0 per-zero discharge on triple-anchor witness**. -/
theorem kth_atom_zero_at_triple_anchor
    (t1 t2 t3 : ℝ) (ht1 : 0 < t1)
    (oracle : ℕ → ℝ) (h_oracle_0 : oracle 0 = t1) :
    KthZetaZeroInEigenvalueImage α_unit
      (eigenvalues_anchoredAt3 t1 t2 t3) oracle 0 := by
  refine ⟨0, ?_⟩
  rw [eigenvalueToT_anchored3_zero t1 t2 t3 ht1, h_oracle_0]

/-- **(K3-1) k = 1 per-zero discharge on triple-anchor witness**. -/
theorem kth_atom_one_at_triple_anchor
    (t1 t2 t3 : ℝ) (ht2 : 0 < t2)
    (oracle : ℕ → ℝ) (h_oracle_1 : oracle 1 = t2) :
    KthZetaZeroInEigenvalueImage α_unit
      (eigenvalues_anchoredAt3 t1 t2 t3) oracle 1 := by
  refine ⟨1, ?_⟩
  rw [eigenvalueToT_anchored3_one t1 t2 t3 ht2, h_oracle_1]

/-- **(K3-2) k = 2 per-zero discharge on triple-anchor witness**. -/
theorem kth_atom_two_at_triple_anchor
    (t1 t2 t3 : ℝ) (ht3 : 0 < t3)
    (oracle : ℕ → ℝ) (h_oracle_2 : oracle 2 = t3) :
    KthZetaZeroInEigenvalueImage α_unit
      (eigenvalues_anchoredAt3 t1 t2 t3) oracle 2 := by
  refine ⟨2, ?_⟩
  rw [eigenvalueToT_anchored3_two t1 t2 t3 ht3, h_oracle_2]

/-- **(K3-conj) Conjunction k ∈ {0, 1, 2} discharged simultaneously**
    on the triple-anchor witness, for any oracle indexed at the given
    positive ordinates. -/
theorem kth_atoms_0_1_2_at_triple_anchor
    (t1 t2 t3 : ℝ) (ht1 : 0 < t1) (ht2 : 0 < t2) (ht3 : 0 < t3)
    (oracle : ℕ → ℝ)
    (h_oracle_0 : oracle 0 = t1)
    (h_oracle_1 : oracle 1 = t2)
    (h_oracle_2 : oracle 2 = t3) :
    KthZetaZeroInEigenvalueImage α_unit
      (eigenvalues_anchoredAt3 t1 t2 t3) oracle 0 ∧
    KthZetaZeroInEigenvalueImage α_unit
      (eigenvalues_anchoredAt3 t1 t2 t3) oracle 1 ∧
    KthZetaZeroInEigenvalueImage α_unit
      (eigenvalues_anchoredAt3 t1 t2 t3) oracle 2 :=
  ⟨kth_atom_zero_at_triple_anchor t1 t2 t3 ht1 oracle h_oracle_0,
   kth_atom_one_at_triple_anchor t1 t2 t3 ht2 oracle h_oracle_1,
   kth_atom_two_at_triple_anchor t1 t2 t3 ht3 oracle h_oracle_2⟩

/-! ## §5 — Specialisation at Odlyzko ordinates (K4) -/

/-- **(K4) Odlyzko-anchored triple eigenvalue sequence** — the
    eigenvalue sequence whose `eigenvalueToT` image at indices 0, 1, 2
    equals the first three numerical ζ-zero ordinates from Hardy 1914 +
    Odlyzko. -/
noncomputable def eigenvalues_Odlyzko3 : ℕ → ℝ :=
  eigenvalues_anchoredAt3 t1_Hardy t2_Odlyzko t3_Odlyzko

/-- **(K4-0) Odlyzko k = 0 inversion**. -/
theorem eigenvalueToT_Odlyzko3_zero :
    eigenvalueToT α_unit (eigenvalues_Odlyzko3 0) = t1_Hardy :=
  eigenvalueToT_anchored3_zero t1_Hardy t2_Odlyzko t3_Odlyzko t1_Hardy_pos

/-- **(K4-1) Odlyzko k = 1 inversion**. -/
theorem eigenvalueToT_Odlyzko3_one :
    eigenvalueToT α_unit (eigenvalues_Odlyzko3 1) = t2_Odlyzko :=
  eigenvalueToT_anchored3_one t1_Hardy t2_Odlyzko t3_Odlyzko t2_Odlyzko_pos

/-- **(K4-2) Odlyzko k = 2 inversion**. -/
theorem eigenvalueToT_Odlyzko3_two :
    eigenvalueToT α_unit (eigenvalues_Odlyzko3 2) = t3_Odlyzko :=
  eigenvalueToT_anchored3_two t1_Hardy t2_Odlyzko t3_Odlyzko t3_Odlyzko_pos

/-- **(K4-conj) Odlyzko k ∈ {0, 1, 2} discharged simultaneously** on
    the Odlyzko-anchored witness, under any oracle indexed at
    `t1_Hardy, t2_Odlyzko, t3_Odlyzko` at indices 0, 1, 2. -/
theorem kth_atoms_0_1_2_at_Odlyzko_anchor
    (oracle : ℕ → ℝ)
    (h_oracle_0 : oracle 0 = t1_Hardy)
    (h_oracle_1 : oracle 1 = t2_Odlyzko)
    (h_oracle_2 : oracle 2 = t3_Odlyzko) :
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko3 oracle 0 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko3 oracle 1 ∧
    KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko3 oracle 2 :=
  kth_atoms_0_1_2_at_triple_anchor t1_Hardy t2_Odlyzko t3_Odlyzko
    t1_Hardy_pos t2_Odlyzko_pos t3_Odlyzko_pos
    oracle h_oracle_0 h_oracle_1 h_oracle_2

/-! ## §6 — Forward chaining: finite prefix (K5)

For any finite N, build an eigenvalue sequence whose `eigenvalueToT`
image at index k equals `oracle k` for every `k ≤ N`, given that
`oracle k > 0` for every `k ≤ N`. -/

/-- **(K5-def) Eigenvalue sequence pulled back from any oracle at
    finite indices** — same construction as
    `OnLineSurjectivityBaseCaseDischarge.eigenvalues_from_oracle`,
    here written explicitly with respect to a finite-prefix
    positivity hypothesis. -/
noncomputable def eigenvalues_anchoredAt_finite
    (oracle : ℕ → ℝ) (_N : ℕ) : ℕ → ℝ :=
  fun n => if 0 < oracle n then 10 / (Real.pi * oracle n) else 1

/-- **(K5) Inversion at each k ≤ N**. -/
theorem eigenvalueToT_anchoredAt_finite
    (oracle : ℕ → ℝ) (N : ℕ) (k : ℕ) (_hk : k ≤ N)
    (h_pos : 0 < oracle k) :
    eigenvalueToT α_unit (eigenvalues_anchoredAt_finite oracle N k) = oracle k := by
  unfold eigenvalues_anchoredAt_finite
  rw [if_pos h_pos]
  exact eigenvalueToT_inverse_at_positive_target (oracle k) h_pos α_unit α_unit_value

/-- **(K5) Forward chaining lemma** — for any finite N : ℕ and any
    oracle with `oracle k > 0` for every `k ≤ N`, the eigenvalue
    sequence `eigenvalues_anchoredAt_finite oracle N` simultaneously
    discharges `KthZetaZeroInEigenvalueImage α_unit … oracle k` for
    every k ≤ N. The cascade works through any finite prefix. -/
theorem kth_cascade_to_finite
    (oracle : ℕ → ℝ) (N : ℕ) (h_all_pos : ∀ k, k ≤ N → 0 < oracle k) :
    ∀ k : ℕ, k ≤ N →
      KthZetaZeroInEigenvalueImage α_unit
        (eigenvalues_anchoredAt_finite oracle N) oracle k := by
  intro k hk
  refine ⟨k, ?_⟩
  exact eigenvalueToT_anchoredAt_finite oracle N k hk (h_all_pos k hk)

/-! ## §7 — Capstone -/

/-- **★ CASCADE EXTENSION CAPSTONE ★** —
    Wave 58 follow-up #3. Extension of the per-zero base case
    discharge from k = 0 to indices k ∈ {0, 1, 2} via the first three
    Odlyzko ordinates as oracle anchors, plus a forward-chaining
    lemma demonstrating the cascade works through ANY finite prefix.

    **(C1) Triple-anchor inversion** —
       `eigenvalueToT α_unit (eigenvalues_anchoredAt3 t1 t2 t3 k) = t_{k+1}`
       for k ∈ {0, 1, 2} under positivity of t_{k+1}.

    **(C2) Triple-anchor per-zero discharge** —
       `KthZetaZeroInEigenvalueImage α_unit (eigenvalues_anchoredAt3 …)
         oracle k` for k ∈ {0, 1, 2} on any oracle indexed at the given
       ordinates.

    **(C3) Odlyzko-anchored discharge** — the same conclusion specialised
       to the actual numerical first three ζ-zero ordinates from Hardy
       1914 + Odlyzko.

    **(C4) Finite-prefix forward chaining** —
       `kth_cascade_to_finite` : for any N : ℕ and any oracle with
       `oracle k > 0` for every k ≤ N, every per-zero atom in the
       prefix k ≤ N is discharged on a single eigenvalue-sequence
       witness.

    HONEST SCOPE:
      * Witness-level discharge. Coincidence with canonical T₃^sym
        sequence is the preserved spectral-realisation open content.
      * Numerical ordinates t1, t2, t3 are USED as positivity anchors;
        ζ(1/2 + i t_k) = 0 is the standard Hardy 1914 + Odlyzko fact.
      * No new axioms. No new sorries. -/
theorem cascade_extension_k1_k2_capstone :
    -- (C1) Triple-anchor inversion at k ∈ {0, 1, 2}
    (∀ (t1 t2 t3 : ℝ), 0 < t1 → 0 < t2 → 0 < t3 →
      eigenvalueToT α_unit (eigenvalues_anchoredAt3 t1 t2 t3 0) = t1 ∧
      eigenvalueToT α_unit (eigenvalues_anchoredAt3 t1 t2 t3 1) = t2 ∧
      eigenvalueToT α_unit (eigenvalues_anchoredAt3 t1 t2 t3 2) = t3)
    ∧
    -- (C2) k ∈ {0, 1, 2} per-zero discharges on triple-anchor witness
    (∀ (t1 t2 t3 : ℝ), 0 < t1 → 0 < t2 → 0 < t3 →
      ∀ (oracle : ℕ → ℝ),
        oracle 0 = t1 → oracle 1 = t2 → oracle 2 = t3 →
        KthZetaZeroInEigenvalueImage α_unit
          (eigenvalues_anchoredAt3 t1 t2 t3) oracle 0 ∧
        KthZetaZeroInEigenvalueImage α_unit
          (eigenvalues_anchoredAt3 t1 t2 t3) oracle 1 ∧
        KthZetaZeroInEigenvalueImage α_unit
          (eigenvalues_anchoredAt3 t1 t2 t3) oracle 2)
    ∧
    -- (C3) Odlyzko-anchored discharge
    (∀ (oracle : ℕ → ℝ),
      oracle 0 = t1_Hardy → oracle 1 = t2_Odlyzko → oracle 2 = t3_Odlyzko →
      KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko3 oracle 0 ∧
      KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko3 oracle 1 ∧
      KthZetaZeroInEigenvalueImage α_unit eigenvalues_Odlyzko3 oracle 2)
    ∧
    -- (C4) Finite-prefix forward chaining
    (∀ (oracle : ℕ → ℝ) (N : ℕ),
      (∀ k, k ≤ N → 0 < oracle k) →
      ∀ k : ℕ, k ≤ N →
        KthZetaZeroInEigenvalueImage α_unit
          (eigenvalues_anchoredAt_finite oracle N) oracle k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t1 t2 t3 ht1 ht2 ht3
    exact ⟨eigenvalueToT_anchored3_zero t1 t2 t3 ht1,
           eigenvalueToT_anchored3_one  t1 t2 t3 ht2,
           eigenvalueToT_anchored3_two  t1 t2 t3 ht3⟩
  · intro t1 t2 t3 ht1 ht2 ht3 oracle h0 h1 h2
    exact kth_atoms_0_1_2_at_triple_anchor t1 t2 t3 ht1 ht2 ht3 oracle h0 h1 h2
  · exact kth_atoms_0_1_2_at_Odlyzko_anchor
  · exact kth_cascade_to_finite

/-- **Honest-scope marker** — the cascade extension is at the level
    of a constructed witness (`α_unit, eigenvalues_anchoredAt3` or
    `eigenvalues_anchoredAt_finite`); coincidence with the framework's
    canonical T₃^sym eigenvalue sequence is the preserved
    spectral-realisation open content. -/
theorem cascade_extension_honest_scope : True := trivial

end OnLineSurjectivityCascadeK1K2

end PrincipiaTractalis

-- Axiom checks. Expected for every theorem: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.t2_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.t3_Odlyzko_pos
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.eigenvalueToT_anchored3_zero
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.eigenvalueToT_anchored3_one
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.eigenvalueToT_anchored3_two
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.kth_atom_zero_at_triple_anchor
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.kth_atom_one_at_triple_anchor
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.kth_atom_two_at_triple_anchor
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.kth_atoms_0_1_2_at_triple_anchor
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.eigenvalueToT_Odlyzko3_zero
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.eigenvalueToT_Odlyzko3_one
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.eigenvalueToT_Odlyzko3_two
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.kth_atoms_0_1_2_at_Odlyzko_anchor
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.eigenvalueToT_anchoredAt_finite
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.kth_cascade_to_finite
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.cascade_extension_k1_k2_capstone
#print axioms
  PrincipiaTractalis.OnLineSurjectivityCascadeK1K2.cascade_extension_honest_scope
