/-
# PF.YangMills.SpectralInclusion_2026_10_08

★ 2026-10-08 — Lane 6: make the Lean match its docstring for the
Yang–Mills OS Hamiltonian's spectral inclusion.

## The defect this file closes

`PF/YM_ClayLiteralClosureAttempt.lean` makes, in three separate
docstrings, a spectral-inclusion claim of the shape

    Spec(H) ⊆ {0} ∪ [Δ, ∞)

Specifically, the goal specification quoted verbatim in the docstring of
`ym_clay_literal_mass_gap` is

    theorem ym_clay_literal_mass_gap :
        ∃ (H : Type) [_ : InnerProductSpace ℝ H] [_ : CompleteSpace H]
          (Hamil : H →L[ℝ] H) (Δ : ℝ),
            0 < Δ ∧ Δ ≠ 1 ∧
            (∀ E : ℝ, E ∈ specSet Hamil → E = 0 ∨ E ≥ Δ)

but the theorem as shipped there replaces the final clause by

            (∀ E : ℝ, E ∈ ({1/2, 3/2} : Set ℝ) → E = 0 ∨ E ≥ Δ)

— a clause which does not mention `Hamil` at all, and is therefore a
statement about the two rationals `1/2` and `3/2` rather than about the
spectrum of any operator. The same substitution appears in
`H_OS_mass_gap_one_half`, whose minimality clause also quantifies over
the literal doubleton instead of over `specSet_H_OS`.

The missing ingredient — `specSet_H_OS ⊆ {1/2, 3/2}`, i.e. the assertion
that the exhibited eigenvalues are the ONLY ones — was supplied on
2026-10-07 as `H_OS_specSet_subset_pair` / `H_OS_specSet_eq_pair` in that
same file. What was NOT done is the second half of the repair: restating
the goal-form and mass-gap theorems with the operator-quantified clause
the docstrings advertise. This file does that, additively, without
touching the existing module.

## What this file proves

All statements are about the FIXED operator `H_OS_Wightman`, using the
generic eigenvalue-spectrum predicate `specSet` from
`YM_ClayLiteralClosureAttempt` (not the specialised `specSet_H_OS`), so
the clauses genuinely mention the operator:

  (1) `specSet_H_OS_Wightman_eq` — the generic predicate applied to
      `H_OS_Wightman` is the specialised `specSet_H_OS`. Lets the
      2026-10-07 inclusion transfer to the goal-form statement.

  (2) `specSet_H_OS_Wightman_eq_pair` — `specSet H_OS_Wightman = {1/2, 3/2}`
      in generic form.

  (3) `H_OS_zero_notMem_specSet` — `0 ∉ specSet H_OS_Wightman`. The `{0}`
      branch of the advertised `{0} ∪ [Δ, ∞)` is VACUOUS for this
      operator; the inclusion is strictly stronger than the docstring form.

  (4) `H_OS_specSet_subset_Ici` — `specSet H_OS_Wightman ⊆ [1/2, ∞)`.
      This is the strongest form of the advertised inclusion.

  (5) `H_OS_specSet_subset_zero_union_Ici` — the advertised
      `Spec(H) ⊆ {0} ∪ [1/2, ∞)` verbatim, as a corollary of (4).

  (6) `H_OS_specSet_zero_or_ge_half` — the same in clause form,
      `∀ E ∈ specSet H_OS_Wightman, E = 0 ∨ E ≥ 1/2`: exactly the
      conjunct the shipped `ym_clay_literal_mass_gap` weakened away.

  (7) `H_OS_specSet_subset_Icc` — `specSet H_OS_Wightman ⊆ [1/2, 3/2]`.
      Two-sided: there is nothing above `3/2` either, so the `[Δ, ∞)`
      half-line in the docstring is loose, not tight.

  (8) `H_OS_isLeast_specSet` / `H_OS_isGreatest_specSet` — `1/2` is the
      least and `3/2` the greatest spectral value. `1/2` is therefore the
      OPTIMAL gap constant: no larger `Δ` satisfies the inclusion.

  (9) `H_OS_mass_gap_one_half_specSet` — `H_OS_mass_gap_one_half` with its
      minimality clause restored to range over `specSet H_OS_Wightman`
      instead of over the literal doubleton.

 (10) `ym_clay_literal_mass_gap_specSet_quantified` — `ym_clay_literal_mass_gap`
      with the original quantifier restored: the final clause now reads
      `∀ E : ℝ, E ∈ specSet Hamil → E = 0 ∨ E ≥ Δ`, matching the goal
      specification quoted in that theorem's own docstring. The two
      membership conjuncts `1/2 ∈ specSet Hamil` and `3/2 ∈ specSet Hamil`
      are retained because the quoted specification is, on its own,
      satisfiable by trivial witnesses (see the scope note below); they
      are what make the existential non-vacuous.

## ★ SCOPE — mandatory before citing anything in this file

`H_OS_Wightman` is the 2×2 real symmetric matrix `!![1, 1/2; 1/2, 1]`
lifted to a continuous linear map on `EuclideanSpace ℝ (Fin 2)`. Every
theorem below is finite-dimensional linear algebra about that matrix.

  - It is NOT a quantum Yang–Mills theory on `ℝ⁴`. The carrier is
    2-dimensional; the Clay Hilbert space is the infinite-dimensional
    GNS space of a reflection-positive Schwinger functional.
  - No object of type `Measure (𝓢'(ℝ⁴))` exists anywhere in this corpus,
    so there is no gauge measure for any of this to be the spectrum OF.
  - "Hamiltonian", "spectrum" and "mass gap" here denote the
    linear-algebra notions for a 2×2 matrix, not the Wightman-axiomatic
    notions of the Clay problem.

## ★ What the repaired docstring still overclaims

The file header of `YM_ClayLiteralClosureAttempt` labels item (6) a
Yang–Mills spectrum claim. After this file, the *mathematical* content of
that item is fully proved. What remains overclaimed is purely the
INTERPRETATION, and it is not repairable by any Lean proof about this
operator:

  (a) The existential goal form quoted in that docstring —
      `∃ H, ∃ Hamil, ∃ Δ, 0 < Δ ∧ Δ ≠ 1 ∧ ∀ E ∈ specSet Hamil, E = 0 ∨ E ≥ Δ`
      — is satisfiable by trivial witnesses (e.g. `H := ℝ`,
      `Hamil := 2 • id`, `Δ := 1/2`), so the existential statement
      (10) carries no Clay content even with the quantifier restored. Its
      value is that it is now a true statement ABOUT an operator; the
      operator-fixed theorems (3)–(8) are where the content is.

  (b) `Δ = 1/2` is a dimensionless eigenvalue of a chosen 2×2 matrix. It
      is not a mass in any units, and nothing connects it to a
      physical gap.

  (c) The GNS lift from this 2-dimensional shadow to the literal
      infinite-dimensional OS-reconstructed Hilbert space remains open;
      `YM_ClayLiteralClosureAttempt` isolates it as the named open Prop
      `GNSReconstructionOnSchwartzDualOpen`. Nothing downstream of that
      Prop is non-vacuous until a measure on `𝓢'(ℝ⁴)` with a proved
      characteristic functional exists.

## Build

Zero project axioms. Zero sorries. No `native_decide`, no `axiom`, no
`Prop := True` anchors. Additive: no existing file is modified.

Author: Lane 6 (YM spectral inclusion), 2026-10-08.
-/

import PF.YM_ClayLiteralClosureAttempt
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace PrincipiaTractalis
namespace YangMills
namespace SpectralInclusion_2026_10_08

open PrincipiaTractalis
open PrincipiaTractalis.YM_ClayLiteralClosureAttempt

/-! ## §1 — Transfer: the generic predicate at `H_OS_Wightman`

`YM_ClayLiteralClosureAttempt` carries two spectrum sets: the specialised
`specSet_H_OS` (used for the 2026-10-07 inclusion proof) and the generic
`specSet` (used in the goal-form theorem). They are the same set at
`H_OS_Wightman`; this lemma is what lets the inclusion reach the goal
form. -/

/-- **The generic spectrum predicate at `H_OS_Wightman` is `specSet_H_OS`.**
    Both unfold to `{E | ∃ v ≠ 0, H_OS_Wightman v = E • v}`. -/
theorem specSet_H_OS_Wightman_eq :
    specSet H_OS_Wightman = specSet_H_OS := rfl

/-- **Exact spectrum, generic form**: `specSet H_OS_Wightman = {1/2, 3/2}`.
    The 2026-10-07 `H_OS_specSet_eq_pair` transported along §1.

    Honest scope: exact eigenvalue set of the 2×2 real symmetric matrix
    `!![1, 1/2; 1/2, 1]`. NO Clay Yang–Mills content. -/
theorem specSet_H_OS_Wightman_eq_pair :
    specSet H_OS_Wightman = ({1 / 2, 3 / 2} : Set ℝ) := by
  rw [specSet_H_OS_Wightman_eq]
  exact H_OS_specSet_eq_pair

/-- **Membership in the generic spectrum forces `E ∈ {1/2, 3/2}`.**
    The workhorse behind every bound in §2. -/
theorem mem_specSet_H_OS_Wightman_eq_or
    {E : ℝ} (hE : E ∈ specSet H_OS_Wightman) :
    E = 1 / 2 ∨ E = 3 / 2 := by
  rw [specSet_H_OS_Wightman_eq] at hE
  have h := H_OS_specSet_subset_pair hE
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

/-! ## §2 — ★★★ THE DOCSTRING'S SPECTRAL INCLUSION, PROVED ★★★

The advertised shape is `Spec(H) ⊆ {0} ∪ [Δ, ∞)` with `Δ = 1/2`. For this
operator the `{0}` branch is vacuous, so we prove the strictly stronger
`Spec(H) ⊆ [1/2, ∞)` first and derive the advertised form from it. -/

/-- **`0` is NOT in the spectrum.** The `{0}` branch of the advertised
    `{0} ∪ [Δ, ∞)` is vacuous for `H_OS_Wightman`: the operator is
    invertible, both eigenvalues being strictly positive. -/
theorem H_OS_zero_notMem_specSet : (0 : ℝ) ∉ specSet H_OS_Wightman := by
  intro h0
  rcases mem_specSet_H_OS_Wightman_eq_or h0 with h | h <;> norm_num at h

/-- **★★★ THE SPECTRAL INCLUSION, STRONGEST FORM ★★★** —
    `specSet H_OS_Wightman ⊆ [1/2, ∞)`.

    Every spectral value of the OS Hamiltonian is at least `1/2`. This is
    the content the three docstrings of `YM_ClayLiteralClosureAttempt`
    asserted and whose absence forced the shipped theorems to quantify
    over a literal doubleton instead of over the operator's spectrum.

    Honest scope: a statement about the 2×2 real symmetric matrix
    `!![1, 1/2; 1/2, 1]`. NO Clay Yang–Mills content. -/
theorem H_OS_specSet_subset_Ici :
    specSet H_OS_Wightman ⊆ Set.Ici (1 / 2 : ℝ) := by
  intro E hE
  have h : (1 / 2 : ℝ) ≤ E := by
    rcases mem_specSet_H_OS_Wightman_eq_or hE with h | h <;> linarith
  exact Set.mem_Ici.mpr h

/-- **★★★ `Spec(H) ⊆ {0} ∪ [Δ, ∞)` — the docstring's claim verbatim ★★★**,
    at `Δ = 1/2`. A corollary of `H_OS_specSet_subset_Ici`; the `{0}`
    summand is not needed (`H_OS_zero_notMem_specSet`), but this is the
    exact shape the docstrings advertise.

    Honest scope: 2×2 real symmetric matrix. NO Clay Yang–Mills content. -/
theorem H_OS_specSet_subset_zero_union_Ici :
    specSet H_OS_Wightman ⊆ ({0} : Set ℝ) ∪ Set.Ici (1 / 2 : ℝ) :=
  fun _ hE => Set.mem_union_right _ (H_OS_specSet_subset_Ici hE)

/-- **The inclusion in clause form** — `∀ E ∈ specSet H_OS_Wightman,
    E = 0 ∨ E ≥ 1/2`.

    This is EXACTLY the conjunct that the shipped `ym_clay_literal_mass_gap`
    replaced by `∀ E ∈ ({1/2, 3/2} : Set ℝ), E = 0 ∨ E ≥ Δ`. Unlike that
    weakening, this clause mentions the operator. -/
theorem H_OS_specSet_zero_or_ge_half (E : ℝ) (hE : E ∈ specSet H_OS_Wightman) :
    E = 0 ∨ E ≥ (1 / 2 : ℝ) :=
  Or.inr (H_OS_specSet_subset_Ici hE)

/-- **Two-sided bound** — `specSet H_OS_Wightman ⊆ [1/2, 3/2]`.

    Records that the half-line `[Δ, ∞)` of the docstring is LOOSE: the
    spectrum is a bounded two-point set, not a half-line's worth of
    anything. -/
theorem H_OS_specSet_subset_Icc :
    specSet H_OS_Wightman ⊆ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ) := by
  intro E hE
  rcases mem_specSet_H_OS_Wightman_eq_or hE with h | h
  · exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-! ## §3 — Optimality of the constant `Δ = 1/2`

`1/2` is attained, so it is the largest constant for which the inclusion
of §2 holds. Any claim of a gap larger than `1/2` for this operator is
false, not merely unproved. -/

/-- **`1/2` is the LEAST spectral value** — attained, and a lower bound.
    Hence `Δ = 1/2` is the optimal constant in `Spec(H) ⊆ [Δ, ∞)`: no
    larger `Δ` works. -/
theorem H_OS_isLeast_specSet : IsLeast (specSet H_OS_Wightman) (1 / 2 : ℝ) :=
  ⟨by rw [specSet_H_OS_Wightman_eq]; exact H_OS_spectrum_contains_one_half,
   fun _ hE => H_OS_specSet_subset_Ici hE⟩

/-- **`3/2` is the GREATEST spectral value.** With `H_OS_isLeast_specSet`
    this pins the spectrum between two attained endpoints. -/
theorem H_OS_isGreatest_specSet :
    IsGreatest (specSet H_OS_Wightman) (3 / 2 : ℝ) := by
  refine ⟨by rw [specSet_H_OS_Wightman_eq]; exact H_OS_spectrum_contains_three_halves,
          fun E hE => ?_⟩
  rcases mem_specSet_H_OS_Wightman_eq_or hE with h | h <;> linarith

/-! ## §4 — The two shipped theorems, with their quantifiers restored

Neither statement below is new mathematics; each is the existing theorem
of `YM_ClayLiteralClosureAttempt` with the literal-doubleton stand-in
replaced by the operator's actual spectrum, which §2 now makes provable.
The originals are left untouched in place. -/

/-- **`H_OS_mass_gap_one_half`, repaired.** The shipped version's
    minimality clause is `∀ Δ ∈ ({1/2, 3/2} : Set ℝ), Δ_gap ≤ Δ`, which
    does not mention the operator. Here it ranges over
    `specSet H_OS_Wightman`.

    Honest scope: 2×2 real symmetric matrix. NO Clay Yang–Mills content. -/
theorem H_OS_mass_gap_one_half_specSet :
    ∃ Δ_gap : ℝ, 0 < Δ_gap ∧
      Δ_gap ∈ specSet H_OS_Wightman ∧
      (∀ Δ ∈ specSet H_OS_Wightman, Δ_gap ≤ Δ) :=
  ⟨1 / 2, by norm_num, H_OS_isLeast_specSet.1,
   fun _ hΔ => H_OS_isLeast_specSet.2 hΔ⟩

/-- **★★★ `ym_clay_literal_mass_gap`, with the original quantifier
    restored ★★★**

    The shipped theorem's final conjunct is
    `∀ E : ℝ, E ∈ ({1/2, 3/2} : Set ℝ) → E = 0 ∨ E ≥ Δ`. Here it is
    `∀ E : ℝ, E ∈ specSet Hamil → E = 0 ∨ E ≥ Δ`, matching the goal
    specification quoted verbatim in that theorem's own docstring.

    The two membership conjuncts are retained from the shipped version
    because they are what rules out trivial witnesses; see (a) in the
    file header for why the existential alone is weak.

    ★ Honest scope: `Hamil` is instantiated at the 2×2 real symmetric
    matrix `!![1, 1/2; 1/2, 1]` on `EuclideanSpace ℝ (Fin 2)`. This is NOT
    a Clay Yang–Mills discharge. No object of type `Measure (𝓢'(ℝ⁴))`
    exists in this corpus. -/
theorem ym_clay_literal_mass_gap_specSet_quantified :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
      (_ : CompleteSpace H)
      (Hamil : H →L[ℝ] H) (Δ : ℝ),
        0 < Δ ∧ Δ ≠ 1 ∧
        (1 / 2 : ℝ) ∈ specSet Hamil ∧
        (3 / 2 : ℝ) ∈ specSet Hamil ∧
        (∀ E : ℝ, E ∈ specSet Hamil → E = 0 ∨ E ≥ Δ) := by
  refine ⟨H_Wightman, inferInstance, inferInstance, inferInstance,
          H_OS_Wightman, (1 / 2 : ℝ), by norm_num, by norm_num, ?_, ?_, ?_⟩
  · rw [specSet_H_OS_Wightman_eq]
    exact H_OS_spectrum_contains_one_half
  · rw [specSet_H_OS_Wightman_eq]
    exact H_OS_spectrum_contains_three_halves
  · exact fun E hE => H_OS_specSet_zero_or_ge_half E hE

/-! ## §5 — Axiom-freeness verification -/

#print axioms specSet_H_OS_Wightman_eq
#print axioms specSet_H_OS_Wightman_eq_pair
#print axioms mem_specSet_H_OS_Wightman_eq_or
#print axioms H_OS_zero_notMem_specSet
#print axioms H_OS_specSet_subset_Ici
#print axioms H_OS_specSet_subset_zero_union_Ici
#print axioms H_OS_specSet_zero_or_ge_half
#print axioms H_OS_specSet_subset_Icc
#print axioms H_OS_isLeast_specSet
#print axioms H_OS_isGreatest_specSet
#print axioms H_OS_mass_gap_one_half_specSet
#print axioms ym_clay_literal_mass_gap_specSet_quantified

end SpectralInclusion_2026_10_08
end YangMills
end PrincipiaTractalis
