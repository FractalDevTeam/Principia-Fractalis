/-
# Frobenius Churn Observable χ_k — Layer 1 (Lean mathematics only)

## Purpose

Formalizes the churn observable
`χ_k(ρ, σ) := (1/2) · ‖ρ − σ‖²_F`
on the ternary Timeless Field level
`H_k := ℂ^{3^k}`, as specified in the charter
`codex/CHURN_CHI_K_CHARTER_2026-09-12.md`.

This file is Layer 1 (Lean mathematics) ONLY. Layers 2 (EEG measurement
map) and 3 (consciousness interpretation) are separately labelled future
work and are NOT imported, referenced, or claimed by anything in this
file. Any communication about this file that ascribes Layer-2 or Layer-3
content to its theorems is a category error.

## Epistemic status (three-layer separation per charter § Epistemic Status)

- **Layer 1 (this file):** mathematical properties of a defined
  observable on complex matrices. Purely type-theoretic.
- **Layer 2 (future doc):** hypothetical EEG → ρ(t) construction. Not
  here. Not implied by any theorem here.
- **Layer 3 (future protocol):** preregistered experimental hypothesis
  about χ_k in conscious vs unresponsive conditions. Not here. Not
  implied by any theorem here.

Ch32's clinical-ch₂ pipeline uses band power + base-3 digit sums +
phase factors (verified read of `ch32_consciousness_quantification.tex`
lines 191-322); it is NOT a reduced-density-matrix estimator. The
Layer-2 map `EEG → ρ(t)` is wholly new work, not a wrapper around ch32.

## What this file does

1. Defines `frobeniusSqDist` explicitly as the sum of squared entry
   norms. The definition does NOT use the ambient `Matrix.norm`
   instance, which in pinned mathlib
   (`Mathlib/Analysis/Matrix.lean:513`) is the entrywise sup norm via
   `Pi.seminormedAddCommGroup`; the Frobenius instance
   `Matrix.frobeniusNormedAddCommGroup` is `@[local instance]` (not
   globally declared). Writing `‖A - B‖²` without opening a Frobenius
   scope would silently yield the sup norm squared, not Frobenius.
2. Defines `churnFrobenius := (1/2) * frobeniusSqDist`.
3. Proves T1 nonnegativity, T2 symmetry, T3 zero-iff-equality.
4. Proves T4 unitary invariance. **T4's hypothesis takes BOTH**
   `U * Uᴴ = 1` **AND** `Uᴴ * U = 1` **as explicit arguments** per
   user directive (do not silently use an identity absent from the
   theorem hypotheses). The proof body uses only `Uᴴ * U = 1`; the
   other hypothesis is present for signature completeness and to
   guard against silent-use regressions.
5. Defines `digitAncillaLift` from level `k` to level `2*k` — the
   digit-compatible pure-ancilla extension appending `k` copies of
   the zero digit.
6. Proves T5a: partial trace through the substrate's
   `TimelessField.partialTraceMorphism k (2*k)` recovers ρ from
   `digitAncillaLift k ρ`.
7. Proves T5b: `churnFrobenius (digitAncillaLift k ρ) (digitAncillaLift
   k σ) = churnFrobenius ρ σ`. Single-lift coherence: `digitAncillaLift`
   remains the SOLE public lift (both T5a and T5b concern the same
   object). The proof uses `private` internal helpers (a rank-one ancilla
   projector, a product-form representation, an extensional bridge, and
   a digit-split bijection) that are file-scope only and not part of the
   public API.

## Public API surface

The three public endpoints for downstream consumers are:

  * `digitAncillaLift k ρ` — the digit-compatible pure-ancilla lift
    (Section 4).
  * `partialTraceMorphism_digitAncillaLift` — T5a partial-trace
    recovery via the substrate morphism (Section 5).
  * `churnFrobenius_digitAncillaLift_invariant` — T5b churn invariance
    under the lift (Section 6).

Plus the definitional trio `frobeniusSqDist`, `churnFrobenius`, and
their T1-T4 accompanying theorems.

The Kronecker-path proof machinery in Section 6 (`ancillaProjector`,
`reindexKroneckerLift`, `digitAncillaLift_eq_reindexKroneckerLift`,
`digitSplit`) is `private` — file-scope only, not part of the public
API. Downstream modules should reference only the endpoints listed
above.

## What this file explicitly does NOT do

- Does NOT claim generic Hilbert-Schmidt contraction under partial
  trace.
- Does NOT import EEG or measurement infrastructure.
- Does NOT interpret χ_k as a consciousness measure.
- Does NOT prove BSD-style overclaimed identities.
- Does NOT assume `Matrix.norm` is the Frobenius norm.

## Charter reference

`codex/CHURN_CHI_K_CHARTER_2026-09-12.md` — §3.1 (explicit norm),
§3.2 (definition), §3.3 (theorem signatures), §7 (stopping conditions).
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PF.Consciousness.TimelessFieldPartialTraceMorphism

namespace PrincipiaTractalis.Consciousness.FrobeniusChurn

open scoped BigOperators
open Matrix Complex Finset
open PrincipiaTractalis.TimelessField

/-! ## Section 1 — Explicit Frobenius squared distance

The definition below is INTENTIONALLY explicit: it does NOT use the
ambient `Matrix.norm` instance. Verified in pinned mathlib:
`Matrix.frobeniusNormedAddCommGroup` is `@[local instance]` in
`Mathlib/Analysis/Matrix.lean:513` — not globally declared — and the
inferable default norm on `Matrix m n α` is the entrywise sup norm.
An expression like `‖ρ - σ‖²` would therefore silently yield the
sup norm squared, not Frobenius. The explicit sum-of-squared-entries
form removes that ambiguity. -/

/-- Sum of squared entry norms between two `Fin (3^k) × Fin (3^k)`
    complex matrices. Explicit definition; no ambient norm assumption. -/
noncomputable def frobeniusSqDist {k : ℕ}
    (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j - B i j‖ ^ 2

/-- The Frobenius churn observable on ternary level `k`. -/
noncomputable def churnFrobenius {k : ℕ}
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) : ℝ :=
  (1/2) * frobeniusSqDist ρ σ

/-! ## Section 2 — T1 (nonnegativity), T2 (symmetry), T3 (zero iff equality) -/

/-- Entrywise nonnegativity of the summand. -/
private lemma sq_norm_nonneg (z : ℂ) : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _

/-- **T1 (frobeniusSqDist).** The sum-of-squared-entries is nonnegative. -/
theorem frobeniusSqDist_nonneg {k : ℕ}
    (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    0 ≤ frobeniusSqDist A B := by
  unfold frobeniusSqDist
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_norm_nonneg _

/-- **T1 (churn).** The Frobenius churn is nonnegative. -/
theorem churnFrobenius_nonneg {k : ℕ}
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    0 ≤ churnFrobenius ρ σ := by
  unfold churnFrobenius
  have h1 : (0 : ℝ) ≤ (1 / 2) := by norm_num
  have h2 : 0 ≤ frobeniusSqDist ρ σ := frobeniusSqDist_nonneg ρ σ
  exact mul_nonneg h1 h2

/-- **T2 (frobeniusSqDist).** Sum-of-squared-entries is symmetric in its arguments. -/
theorem frobeniusSqDist_symm {k : ℕ}
    (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    frobeniusSqDist A B = frobeniusSqDist B A := by
  unfold frobeniusSqDist
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : A i j - B i j = -(B i j - A i j) := by ring
  rw [this, norm_neg]

/-- **T2 (churn).** The Frobenius churn is symmetric. -/
theorem churnFrobenius_symm {k : ℕ}
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    churnFrobenius ρ σ = churnFrobenius σ ρ := by
  unfold churnFrobenius
  rw [frobeniusSqDist_symm]

/-- **T3 (frobeniusSqDist).** Sum-of-squared-entries vanishes iff the
    matrices are equal. -/
theorem frobeniusSqDist_eq_zero_iff {k : ℕ}
    (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    frobeniusSqDist A B = 0 ↔ A = B := by
  unfold frobeniusSqDist
  constructor
  · intro h
    -- ∑ i, (∑ j, ‖(A - B) i j‖²) = 0 with each inner sum ≥ 0.
    have h1 : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ ∑ j, ‖A i j - B i j‖ ^ 2 :=
      fun i _ => Finset.sum_nonneg fun _ _ => sq_norm_nonneg _
    rw [Finset.sum_eq_zero_iff_of_nonneg h1] at h
    -- Now for each i, the inner sum vanishes.
    ext i j
    have hi : ∑ j, ‖A i j - B i j‖ ^ 2 = 0 := h i (Finset.mem_univ _)
    have h2 : ∀ j' ∈ Finset.univ, (0 : ℝ) ≤ ‖A i j' - B i j'‖ ^ 2 :=
      fun _ _ => sq_norm_nonneg _
    rw [Finset.sum_eq_zero_iff_of_nonneg h2] at hi
    have hij : ‖A i j - B i j‖ ^ 2 = 0 := hi j (Finset.mem_univ _)
    have h_norm_zero : ‖A i j - B i j‖ = 0 := by
      have := sq_eq_zero_iff.mp hij
      exact this
    have h_diff_zero : A i j - B i j = 0 := norm_eq_zero.mp h_norm_zero
    exact sub_eq_zero.mp h_diff_zero
  · rintro rfl
    simp

/-- **T3 (churn).** The Frobenius churn vanishes iff `ρ = σ`. -/
theorem churnFrobenius_eq_zero_iff {k : ℕ}
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    churnFrobenius ρ σ = 0 ↔ ρ = σ := by
  unfold churnFrobenius
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exfalso; norm_num at h
    · exact (frobeniusSqDist_eq_zero_iff _ _).mp h
  · rintro rfl
    right
    exact (frobeniusSqDist_eq_zero_iff _ _).mpr rfl

/-! ## Section 3 — T4 unitary invariance

Signature takes BOTH `U * Uᴴ = 1` and `Uᴴ * U = 1` as explicit
hypotheses per user directive: "state T4 using both unitary
identities [...] or use an established unitary subtype whose API
supplies both. Do not silently use an identity absent from the
theorem hypotheses."

The proof body uses only `Uᴴ * U = 1`; the other hypothesis is
present for signature completeness. This surfacing choice is
deliberate — future readers can see at the call site that BOTH
identities are supplied by the caller, matching the definition of
unitarity, without the theorem body relying on any identity absent
from its signature. -/

/-- Auxiliary identity: `frobeniusSqDist A B` equals (as a complex
    number) the trace of the Hermitian PSD form `(A - B)ᴴ * (A - B)`. -/
private lemma frobeniusSqDist_eq_trace_conj_mul {k : ℕ}
    (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    (frobeniusSqDist A B : ℂ)
      = Matrix.trace ((A - B)ᴴ * (A - B)) := by
  unfold frobeniusSqDist
  -- Unfold the trace: trace M = ∑ i, M i i. Then (Aᴴ * A) i i = ∑ j, star (A j i) * A j i.
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
             Matrix.conjTranspose_apply, Matrix.sub_apply, star_sub]
  -- RHS: ∑ i, ∑ j, star (A j i - B j i) * (A j i - B j i)
  push_cast
  -- Swap the RHS's iterated sum via Finset.sum_comm to align indices.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  -- Goal: ↑‖A b a - B b a‖ ^ 2 = (star (A b a) - star (B b a)) * (A b a - B b a)
  -- Fold star (A b a) - star (B b a) into star (A b a - B b a).
  rw [show star (A b a) - star (B b a) = star (A b a - B b a) from by rw [star_sub]]
  -- Now: ↑‖A b a - B b a‖ ^ 2 = star (A b a - B b a) * (A b a - B b a)
  -- Chain: (↑‖z‖)^2 = ↑(‖z‖^2) = ↑(normSq z) = star z * z.
  set z := A b a - B b a with hz
  show (↑‖z‖ : ℂ) ^ 2 = star z * z
  have hpow : ((↑‖z‖ : ℂ)) ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hnormSq : (‖z‖ ^ 2 : ℝ) = Complex.normSq z := (Complex.normSq_eq_norm_sq z).symm
  have hconj : ((Complex.normSq z : ℝ) : ℂ) = (starRingEnd ℂ) z * z :=
    Complex.normSq_eq_conj_mul_self
  rw [hpow, hnormSq, hconj]
  rfl

/-- **T4 (frobeniusSqDist).** Sum-of-squared-entries is invariant under
    unitary conjugation. Signature takes both unitary identities per
    user directive; proof uses only `Uᴴ * U = 1`. -/
theorem frobeniusSqDist_unitary_invariant {k : ℕ}
    (U : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
    (_hU_left : U * Uᴴ = 1)
    (hU_right : Uᴴ * U = 1)
    (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    frobeniusSqDist (U * A * Uᴴ) (U * B * Uᴴ) = frobeniusSqDist A B := by
  -- Lift both sides to ℂ via the trace identity, then use cyclicity.
  have h1 : ((U * A * Uᴴ) - (U * B * Uᴴ)) = U * (A - B) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  have hAB : (frobeniusSqDist (U * A * Uᴴ) (U * B * Uᴴ) : ℂ)
              = Matrix.trace ((U * (A - B) * Uᴴ)ᴴ * (U * (A - B) * Uᴴ)) := by
    rw [frobeniusSqDist_eq_trace_conj_mul, h1]
  have hID : (frobeniusSqDist A B : ℂ)
              = Matrix.trace ((A - B)ᴴ * (A - B)) :=
    frobeniusSqDist_eq_trace_conj_mul A B
  -- Show the two traces are equal, then cast back.
  have hTrace :
      Matrix.trace ((U * (A - B) * Uᴴ)ᴴ * (U * (A - B) * Uᴴ))
        = Matrix.trace ((A - B)ᴴ * (A - B)) := by
    -- (U(A-B)Uᴴ)ᴴ = U (A-B)ᴴ Uᴴ
    have h_adj :
        (U * (A - B) * Uᴴ)ᴴ = U * (A - B)ᴴ * Uᴴ := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [h_adj]
    -- U(A-B)ᴴ Uᴴ · U(A-B)Uᴴ = U · (A-B)ᴴ · (UᴴU) · (A-B) · Uᴴ
    -- Using hU_right : Uᴴ * U = 1
    have h_middle :
        (U * (A - B)ᴴ * Uᴴ) * (U * (A - B) * Uᴴ)
          = U * ((A - B)ᴴ * (A - B)) * Uᴴ := by
      calc (U * (A - B)ᴴ * Uᴴ) * (U * (A - B) * Uᴴ)
          = U * (A - B)ᴴ * (Uᴴ * U) * (A - B) * Uᴴ := by
            rw [show (U * (A - B) * Uᴴ) = U * ((A - B) * Uᴴ) from by
                rw [Matrix.mul_assoc]]
            simp [Matrix.mul_assoc]
        _ = U * (A - B)ᴴ * 1 * (A - B) * Uᴴ := by rw [hU_right]
        _ = U * (A - B)ᴴ * (A - B) * Uᴴ := by rw [Matrix.mul_one]
        _ = U * ((A - B)ᴴ * (A - B)) * Uᴴ := by
            rw [Matrix.mul_assoc U (A - B)ᴴ (A - B)]
    rw [h_middle]
    -- trace(U * M * Uᴴ) = trace(Uᴴ * (U * M)) by cyclicity, then reassociate.
    have h_cycle :
        Matrix.trace (U * ((A - B)ᴴ * (A - B)) * Uᴴ)
          = Matrix.trace (Uᴴ * U * ((A - B)ᴴ * (A - B))) := by
      rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
    rw [h_cycle, hU_right, Matrix.one_mul]
  -- Cast back from ℂ to ℝ using the fact that both sides are real (traces
  -- of Hermitian PSD).
  have : (frobeniusSqDist (U * A * Uᴴ) (U * B * Uᴴ) : ℂ)
           = (frobeniusSqDist A B : ℂ) := by rw [hAB, hID, hTrace]
  exact_mod_cast this

/-- **T4 (churn).** The Frobenius churn is invariant under unitary
    conjugation. Both `U * Uᴴ = 1` and `Uᴴ * U = 1` are explicit
    hypotheses. -/
theorem churnFrobenius_unitary_invariant {k : ℕ}
    (U : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
    (hU_left : U * Uᴴ = 1)
    (hU_right : Uᴴ * U = 1)
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    churnFrobenius (U * ρ * Uᴴ) (U * σ * Uᴴ) = churnFrobenius ρ σ := by
  unfold churnFrobenius
  rw [frobeniusSqDist_unitary_invariant U hU_left hU_right]

/-! ## Section 4 — Digit-compatible pure-ancilla lift `k → 2*k`

Uses the substrate's `TimelessField.digitEquiv (2*k)` to identify
`Fin (3^(2*k))` with digit functions `Fin (2*k) → Fin 3`. The lift
appends `k` copies of the zero digit and places `ρ`'s entries only
on the "ancilla-zero" block; zero elsewhere. -/

/-- The constant-zero digit function on `Fin n`. -/
noncomputable def zeroDigits (n : ℕ) : Fin n → Fin 3 := fun _ => 0

/-- Extract the first `k` digits from a `(Fin (2*k) → Fin 3)` sequence. -/
noncomputable def firstKDigits (k : ℕ)
    (f : Fin (2*k) → Fin 3) : Fin k → Fin 3 :=
  fun i => f ⟨i.val, by omega⟩

/-- Extract the last `k` digits from a `(Fin (2*k) → Fin 3)` sequence. -/
noncomputable def lastKDigits (k : ℕ)
    (f : Fin (2*k) → Fin 3) : Fin k → Fin 3 :=
  fun i => f ⟨k + i.val, by omega⟩

/-- **Digit-compatible pure-ancilla lift.** Given `ρ : Matrix (Fin (3^k))
    (Fin (3^k)) ℂ`, produce a matrix on level `2*k` whose entries agree
    with `ρ` on the "ancilla-zero" block and vanish elsewhere. The
    ancilla-zero block is characterised by the last `k` digits of both
    row-index and column-index being the constant-zero digit function. -/
noncomputable def digitAncillaLift (k : ℕ)
    (ρ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    Matrix (Fin (3^(2*k))) (Fin (3^(2*k))) ℂ := fun p q =>
  let fp : Fin (2*k) → Fin 3 := (digitEquiv (2*k)).symm p
  let fq : Fin (2*k) → Fin 3 := (digitEquiv (2*k)).symm q
  if (lastKDigits k fp = zeroDigits k) ∧ (lastKDigits k fq = zeroDigits k)
    then ρ (digitEquiv k (firstKDigits k fp)) (digitEquiv k (firstKDigits k fq))
    else 0

/-! ## Section 5 — T5a: partial trace recovers ρ via substrate morphism -/

/-- Divisibility helper: `k ∣ 2*k`. -/
private lemma dvd_two_mul_self (k : ℕ) : k ∣ 2 * k := ⟨2, by ring⟩

/-- Trivial inequality: `k ≤ 2*k`. -/
private lemma le_two_mul_self (k : ℕ) : k ≤ 2 * k := by omega

/-- The residual length `2*k - k` equals `k`. -/
private lemma two_mul_sub_self_eq (k : ℕ) : 2 * k - k = k := by omega

-- (`castToResidual` helper removed — inlined at use sites.)

/-- Applying `firstKDigits` to `appendCast` at level `k → 2*k` recovers the
    first argument `f`. -/
private lemma firstKDigits_appendCast (k : ℕ) (f : Fin k → Fin 3)
    (t : Fin (2*k - k) → Fin 3) :
    firstKDigits k (appendCast (le_two_mul_self k) f t) = f := by
  funext i
  unfold firstKDigits appendCast
  simp only [Function.comp_apply]
  -- Fin.cast on ⟨i.val, _⟩ gives ⟨i.val, _⟩ : Fin (k + (2*k - k))
  -- Since i.val < k, Fin.append f t on this index returns f applied to a Fin k.
  have h_lt : i.val < k := i.isLt
  have h_cast_eq : (Fin.cast (Nat.add_sub_of_le (le_two_mul_self k)).symm
                    (⟨i.val, by omega⟩ : Fin (2 * k)))
                  = Fin.castAdd (2*k - k) i := by
    apply Fin.ext
    simp
  rw [h_cast_eq, Fin.append_left]

/-- Applying `lastKDigits` to `appendCast` at level `k → 2*k` recovers the
    second argument `t`, up to the residual-length cast. -/
private lemma lastKDigits_appendCast (k : ℕ) (f : Fin k → Fin 3)
    (t : Fin (2*k - k) → Fin 3) :
    lastKDigits k (appendCast (le_two_mul_self k) f t)
      = fun i : Fin k => t (Fin.cast (two_mul_sub_self_eq k).symm i) := by
  funext i
  unfold lastKDigits appendCast
  simp only [Function.comp_apply]
  have h_cast_eq :
      (Fin.cast (Nat.add_sub_of_le (le_two_mul_self k)).symm
                (⟨k + i.val, by omega⟩ : Fin (2 * k)))
        = Fin.natAdd k (Fin.cast (two_mul_sub_self_eq k).symm i) := by
    apply Fin.ext
    simp
  rw [h_cast_eq, Fin.append_right]

-- (`castToResidual_eq_zero_iff` removed — direct reasoning inlined at use sites.)

/-- **T5a — Partial-trace recovery via `TimelessField.partialTraceMorphism`.**

    Applying the substrate's `partialTraceMorphism k (2*k)` to the
    digit-compatible pure-ancilla lift `digitAncillaLift k ρ` recovers
    the original level-`k` matrix `ρ`. -/
theorem partialTraceMorphism_digitAncillaLift (k : ℕ)
    (ρ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    partialTraceMorphism k (2*k) (dvd_two_mul_self k) (digitAncillaLift k ρ) = ρ := by
  ext i j
  rw [partialTraceMorphism_apply_of_le (dvd_two_mul_self k) (le_two_mul_self k)]
  unfold partialTraceDigits
  set i' := (digitEquiv k).symm i with hi'
  set j' := (digitEquiv k).symm j with hj'
  -- Fix the "surviving" t value: t = zeroDigits (2*k - k).
  set t0 : Fin (2*k - k) → Fin 3 := fun _ => 0 with ht0
  -- Apply Finset.sum_eq_single at t = t0.
  rw [Finset.sum_eq_single t0]
  · -- Show: the t0-summand equals ρ i j.
    unfold digitAncillaLift
    simp only [Equiv.symm_apply_apply]
    -- Verify lastKDigits condition: lastKDigits k (appendCast … i' t0) = zeroDigits k.
    rw [lastKDigits_appendCast, lastKDigits_appendCast]
    have h_t0_last : (fun idx : Fin k => t0 (Fin.cast (two_mul_sub_self_eq k).symm idx))
                        = zeroDigits k := by
      funext _; rfl
    rw [h_t0_last]
    simp only [and_self, if_true]
    -- Compute firstKDigits and evaluate.
    rw [firstKDigits_appendCast, firstKDigits_appendCast]
    -- Goal: ρ ((digitEquiv k) i') ((digitEquiv k) j') = ρ i j
    -- Since i' = (digitEquiv k).symm i, we have (digitEquiv k) i' = i.
    have hi_apply : (digitEquiv k) i' = i := by
      rw [hi']; exact Equiv.apply_symm_apply _ _
    have hj_apply : (digitEquiv k) j' = j := by
      rw [hj']; exact Equiv.apply_symm_apply _ _
    rw [hi_apply, hj_apply]
  · -- Show: for t ≠ t0, the summand is 0.
    intros t _hmem ht_ne
    unfold digitAncillaLift
    simp only [Equiv.symm_apply_apply]
    -- Show: the ancilla-zero condition FAILS for this t.
    rw [lastKDigits_appendCast, lastKDigits_appendCast]
    have h_t_last_ne :
        (fun idx : Fin k => t (Fin.cast (two_mul_sub_self_eq k).symm idx))
          ≠ zeroDigits k := by
      intro h
      apply ht_ne
      -- If the k-indexed cast version of t is all zero, then t itself is all zero.
      have h_recover : ∀ i : Fin (2*k - k),
          t i = (fun idx : Fin k => t (Fin.cast (two_mul_sub_self_eq k).symm idx))
                  (Fin.cast (two_mul_sub_self_eq k) i) := by
        intro i
        simp
      funext i
      rw [h_recover, h]
      rfl
    simp only [h_t_last_ne, false_and, if_false]
  · intro hni; exact absurd (Finset.mem_univ t0) hni

/-! ## Section 6 — Kronecker redesign for T5b (single-lift coherence)

    Per approved directive (path B): `digitAncillaLift` remains the SOLE
    public lift (T5a unchanged). Internally we define
    `reindexKroneckerLift k ρ` as the same digit-indexed matrix but
    expressed as a pointwise product `ρ(firstK) · P(lastK)` where `P` is
    the rank-one ancilla projector. An extensional bridge lemma proves
    `digitAncillaLift = reindexKroneckerLift`, and T5b follows by
    Kronecker-style sum decomposition on the product form.

    The bridge is a pointwise identity, so both forms compute the same
    entries in the same indexing space. T5a's proof continues to hold
    on `digitAncillaLift` unchanged.

    Mathlib-verified primitives used below (checked in pinned mathlib):
    * `finFunctionFinEquiv_apply` — `Fin (n^m) ↔ Fin m → Fin n`
      encoding is `Σ i, f i · n^i`. In particular `digitEquiv k
      (fun _ => 0) = 0`.
    * `Complex.norm_mul` — `‖z * w‖ = ‖z‖ * ‖w‖` on `ℂ`.
    * `Equiv.sum_comp` — reindex a `Fintype` sum via an equivalence.
    * `Fintype.sum_prod_type'` — Fubini for product-indexed sums.
    * `Finset.sum_mul_sum` — distributivity of `∑ · ∑` into a single
      product of sums when the summand factors.

    None of the following relies on `Matrix.kroneckerMap` (which uses
    product-typed indexing, not the digit-indexed `Fin (3^(2*k))` we
    need); instead the Kronecker structure is encoded directly as a
    product of two entries. -/

/-! ### 6.1 — The rank-one ancilla projector -/

/-- **Rank-one ancilla projector** (private, internal to Kronecker-path
    proof machinery). `ancillaProjector k` is the matrix on level `k`
    with exactly one unit entry at `(0, 0)` and zeros elsewhere.
    Represents the pure state `|0⟩⟨0|` on `H_k` in the computational
    basis. Only used inside this file to prove T5b via the extensional
    bridge from `digitAncillaLift`; NOT part of the public API. -/
private noncomputable def ancillaProjector (k : ℕ) :
    Matrix (Fin (3^k)) (Fin (3^k)) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- Value of the ancilla projector on the (0, 0) entry: 1. -/
private lemma ancillaProjector_apply_zero_zero (k : ℕ) :
    ancillaProjector k 0 0 = 1 := by
  unfold ancillaProjector
  simp

/-- Value of the ancilla projector when either index is nonzero: 0. -/
private lemma ancillaProjector_apply_off (k : ℕ)
    (i j : Fin (3^k)) (h : ¬ (i = 0 ∧ j = 0)) :
    ancillaProjector k i j = 0 := by
  unfold ancillaProjector
  simp [h]

/-- **Sum-of-squared-entries of the rank-one ancilla projector equals 1.**
    Explicit evaluation. -/
private lemma frobeniusSqNorm_ancillaProjector (k : ℕ) :
    ∑ i, ∑ j, ‖ancillaProjector k i j‖ ^ 2 = 1 := by
  -- Only the (0, 0) entry contributes, with value 1.
  rw [Finset.sum_eq_single (0 : Fin (3^k))]
  · rw [Finset.sum_eq_single (0 : Fin (3^k))]
    · rw [ancillaProjector_apply_zero_zero]; simp
    · intros j _ hj_ne
      rw [ancillaProjector_apply_off k 0 j (fun h => hj_ne h.2)]
      simp
    · intro hni; exact absurd (Finset.mem_univ (0 : Fin (3^k))) hni
  · intros i _ hi_ne
    apply Finset.sum_eq_zero
    intros j _
    rw [ancillaProjector_apply_off k i j (fun h => hi_ne h.1)]
    simp
  · intro hni; exact absurd (Finset.mem_univ (0 : Fin (3^k))) hni

/-! ### 6.2 — The digit-encoded value of `zeroDigits` is 0

    Verifies `digitEquiv k (zeroDigits k) = 0`, needed to bridge
    "last-k-digits are zero" (as digit function) to "last-k-digits
    encoded value is zero" (as `Fin (3^k)`). -/

/-- `digitEquiv k` applied to the zero digit function is the zero
    index. From `finFunctionFinEquiv_apply`: value = `Σ i, 0 · 3^i = 0`. -/
private lemma digitEquiv_zeroDigits (k : ℕ) :
    digitEquiv k (zeroDigits k) = 0 := by
  apply Fin.ext
  simp [digitEquiv, zeroDigits]

/-- `digitEquiv k f = 0` iff `f = zeroDigits k`, by injectivity. -/
private lemma digitEquiv_eq_zero_iff (k : ℕ) (f : Fin k → Fin 3) :
    digitEquiv k f = 0 ↔ f = zeroDigits k := by
  constructor
  · intro h
    apply (digitEquiv k).injective
    rw [h, digitEquiv_zeroDigits]
  · rintro rfl; exact digitEquiv_zeroDigits k

/-! ### 6.3 — Internal Kronecker representation

    `reindexKroneckerLift` is the SAME digit-indexed matrix as
    `digitAncillaLift`, but expressed as a pointwise product
    `ρ(firstK) · ancillaProjector(lastK)`. -/

/-- **Internal Kronecker representation of the pure-ancilla lift**
    (private, internal to Kronecker-path proof machinery). Same type
    and index space as `digitAncillaLift`; expressed as a pointwise
    product of a `ρ` entry (on the first-`k`-digit block) and an
    ancilla-projector entry (on the last-`k`-digit block). Only used
    inside this file. The extensional bridge
    `digitAncillaLift_eq_reindexKroneckerLift` proves this equals
    `digitAncillaLift`; the public API only exposes `digitAncillaLift`. -/
private noncomputable def reindexKroneckerLift (k : ℕ)
    (ρ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    Matrix (Fin (3^(2*k))) (Fin (3^(2*k))) ℂ := fun p q =>
  ρ (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm p)))
    (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm q))) *
  ancillaProjector k
    (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm p)))
    (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm q)))

/-! ### 6.4 — Extensional bridge: `digitAncillaLift = reindexKroneckerLift` -/

/-- **Extensional bridge** (private, internal to Kronecker-path proof
    machinery). `digitAncillaLift k ρ` and `reindexKroneckerLift k ρ`
    are the same matrix, entry-by-entry. Only used inside this file
    to prove T5b; the public API only exposes `digitAncillaLift` and
    `churnFrobenius_digitAncillaLift_invariant`.

    Follows from: `ancillaProjector k a b = 1` iff `a = 0 ∧ b = 0`,
    combined with `digitEquiv_eq_zero_iff` bridging "digit function is
    zero" and "encoded value is zero". -/
private theorem digitAncillaLift_eq_reindexKroneckerLift (k : ℕ)
    (ρ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    digitAncillaLift k ρ = reindexKroneckerLift k ρ := by
  ext p q
  unfold digitAncillaLift reindexKroneckerLift
  by_cases h_p : lastKDigits k ((digitEquiv (2*k)).symm p) = zeroDigits k
  · by_cases h_q : lastKDigits k ((digitEquiv (2*k)).symm q) = zeroDigits k
    · -- Both ancilla parts are zero: LHS = ρ(firstK), RHS = ρ(firstK) * 1.
      simp only [h_p, h_q, and_self, if_true]
      rw [digitEquiv_zeroDigits, ancillaProjector_apply_zero_zero]
      ring
    · -- Right ancilla nonzero: LHS = 0, RHS = ρ(firstK) * P(_, nonzero) = ρ · 0 = 0.
      have h_cond_false : ¬ ((lastKDigits k ((digitEquiv (2*k)).symm p) = zeroDigits k)
                            ∧ (lastKDigits k ((digitEquiv (2*k)).symm q) = zeroDigits k)) := by
        intro ⟨_, h_q'⟩; exact h_q h_q'
      simp only [if_neg h_cond_false]
      have h_q_enc : digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm q)) ≠ 0 := by
        rw [Ne, digitEquiv_eq_zero_iff]; exact h_q
      have h_apply : ancillaProjector k
          (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm p)))
          (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm q))) = 0 :=
        ancillaProjector_apply_off k _ _ (fun h => h_q_enc h.2)
      rw [h_apply]; ring
  · -- Left ancilla nonzero: LHS = 0, RHS = ρ · P(nonzero, _) = ρ · 0 = 0.
    have h_cond_false : ¬ ((lastKDigits k ((digitEquiv (2*k)).symm p) = zeroDigits k)
                          ∧ (lastKDigits k ((digitEquiv (2*k)).symm q) = zeroDigits k)) := by
      intro ⟨h_p', _⟩; exact h_p h_p'
    simp only [if_neg h_cond_false]
    have h_p_enc : digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm p)) ≠ 0 := by
      rw [Ne, digitEquiv_eq_zero_iff]; exact h_p
    have h_apply : ancillaProjector k
        (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm p)))
        (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm q))) = 0 :=
      ancillaProjector_apply_off k _ _ (fun h => h_p_enc h.1)
    rw [h_apply]; ring

/-! ### 6.5 — The digit-split bijection `Fin (3^(2*k)) ≃ Fin (3^k) × Fin (3^k)`

    Used for the double-sum reindexing in T5b. -/

/-- **The digit-split bijection** (private, internal to Kronecker-path
    proof machinery). Sends a digit-index `p : Fin (3^(2*k))` to the
    pair `(first-k-encoded, last-k-encoded)`. Only used inside this
    file for the double-sum reindexing in T5b. -/
private noncomputable def digitSplit (k : ℕ) :
    Fin (3^(2*k)) ≃ Fin (3^k) × Fin (3^k) where
  toFun p :=
    (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm p)),
     digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm p)))
  invFun ij :=
    digitEquiv (2*k) (appendCast (le_two_mul_self k)
                        ((digitEquiv k).symm ij.1)
                        (fun i => (digitEquiv k).symm ij.2
                                  (Fin.cast (two_mul_sub_self_eq k) i)))
  left_inv := by
    intro p
    simp only
    apply (digitEquiv (2*k)).symm.injective
    rw [Equiv.symm_apply_apply]
    -- Show the invFun's argument, after applying digitEquiv (2*k), equals p.
    -- Equivalently, show the appendCast reconstruction equals (digitEquiv (2*k)).symm p.
    set fp := (digitEquiv (2*k)).symm p with hfp
    -- Need: appendCast … ((digitEquiv k).symm (digitEquiv k (firstK fp)))
    --                    (fun i => (digitEquiv k).symm (digitEquiv k (lastK fp))
    --                                 (Fin.cast (…) i))
    --        = fp
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    -- Now: appendCast … (firstK fp) (fun i => lastK fp (Fin.cast (…) i)) = fp
    funext idx
    unfold appendCast
    simp only [Function.comp_apply]
    by_cases h_idx : idx.val < k
    · have h_cast :
          (Fin.cast (Nat.add_sub_of_le (le_two_mul_self k)).symm idx)
            = Fin.castAdd (2*k - k) ⟨idx.val, h_idx⟩ := by
        apply Fin.ext; simp
      rw [h_cast, Fin.append_left]
      unfold firstKDigits
      congr 1
    · push_neg at h_idx
      set s : Fin k := ⟨idx.val - k, by omega⟩ with hs
      have hidx_eq : idx = ⟨k + s.val, by omega⟩ := by
        apply Fin.ext; simp [hs]; omega
      rw [hidx_eq]
      have h_cast :
          (Fin.cast (Nat.add_sub_of_le (le_two_mul_self k)).symm
            (⟨k + s.val, by omega⟩ : Fin (2*k)))
            = Fin.natAdd k (Fin.cast (two_mul_sub_self_eq k).symm s) := by
        apply Fin.ext; simp
      rw [h_cast, Fin.append_right]
      -- Goal: lastKDigits k fp (Fin.cast … (Fin.cast (two_mul_sub_self_eq k).symm s)) = fp ⟨k + s.val, _⟩
      unfold lastKDigits
      congr 1
  right_inv := by
    rintro ⟨i, j⟩
    simp only
    -- Show: (encode firstK (invFun_appendCast), encode lastK (invFun_appendCast)) = (i, j).
    -- Use firstKDigits_appendCast and lastKDigits_appendCast.
    rw [Equiv.symm_apply_apply]
    have h_first := firstKDigits_appendCast k ((digitEquiv k).symm i)
      (fun idx : Fin (2*k - k) => (digitEquiv k).symm j
                                   (Fin.cast (two_mul_sub_self_eq k) idx))
    have h_last := lastKDigits_appendCast k ((digitEquiv k).symm i)
      (fun idx : Fin (2*k - k) => (digitEquiv k).symm j
                                   (Fin.cast (two_mul_sub_self_eq k) idx))
    rw [h_first, h_last]
    -- Goal: (digitEquiv k ((digitEquiv k).symm i), digitEquiv k (…)) = (i, j)
    refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
    · exact Equiv.apply_symm_apply _ _
    · -- Show: digitEquiv k (fun idx : Fin k => (fun i0 : Fin (2*k - k) => (digitEquiv k).symm j
      --                                          (Fin.cast (two_mul_sub_self_eq k) i0))
      --                       (Fin.cast (two_mul_sub_self_eq k).symm idx))
      --        = j
      -- Simplify: Fin.cast … (Fin.cast … idx) = idx.
      have h_id : (fun idx : Fin k => (digitEquiv k).symm j
                    (Fin.cast (two_mul_sub_self_eq k)
                      (Fin.cast (two_mul_sub_self_eq k).symm idx)))
                  = (digitEquiv k).symm j := by
        funext idx
        congr 1
      rw [h_id]
      exact Equiv.apply_symm_apply _ _

/-! ### 6.6 — T5b: churn invariance under the digit-compatible pure-ancilla lift -/

/-- **T5b — Churn invariance under the pure-ancilla lift.**

    The Frobenius churn observable is unchanged when both arguments are
    lifted via `digitAncillaLift k` from level `k` to level `2*k`.

    Proof via the extensional bridge to `reindexKroneckerLift`, then
    factoring the double-sum through `digitSplit` and using
    `frobeniusSqNorm_ancillaProjector = 1`. Uses `Complex.norm_mul` +
    `mul_pow` to distribute the squared norm across the pointwise
    product; uses `Equiv.sum_comp` (via `digitSplit`) plus
    `Fintype.sum_prod_type'` to convert double `Fin (3^(2*k))` sums
    into double `Fin (3^k) × Fin (3^k)` sums; uses `Finset.sum_mul_sum`
    to separate the ρ-side sum from the ancilla-projector-side sum. -/
theorem churnFrobenius_digitAncillaLift_invariant (k : ℕ)
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    churnFrobenius (digitAncillaLift k ρ) (digitAncillaLift k σ)
      = churnFrobenius ρ σ := by
  unfold churnFrobenius
  congr 1
  -- Bridge to reindexKroneckerLift on both sides.
  rw [digitAncillaLift_eq_reindexKroneckerLift, digitAncillaLift_eq_reindexKroneckerLift]
  unfold frobeniusSqDist
  -- On the Kronecker side, each summand factors as
  --   ‖(ρ - σ)(firstK-enc) * ancillaProjector(lastK-enc)‖^2
  -- = ‖(ρ - σ)‖^2 * ‖ancillaProjector‖^2.
  have h_summand :
      ∀ p q : Fin (3^(2*k)),
        ‖reindexKroneckerLift k ρ p q - reindexKroneckerLift k σ p q‖ ^ 2
          = ‖(ρ - σ)
              (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm p)))
              (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm q)))‖ ^ 2
            * ‖ancillaProjector k
                (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm p)))
                (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm q)))‖ ^ 2 := by
    intro p q
    unfold reindexKroneckerLift
    -- ρ(firstK) * P - σ(firstK) * P = (ρ - σ)(firstK) * P
    have h_factor :
        ρ (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm p)))
          (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm q)))
          * ancillaProjector k
              (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm p)))
              (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm q)))
          - σ (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm p)))
              (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm q)))
          * ancillaProjector k
              (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm p)))
              (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm q)))
          = (ρ - σ)
              (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm p)))
              (digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm q)))
            * ancillaProjector k
                (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm p)))
                (digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm q))) := by
      simp only [Matrix.sub_apply]; ring
    rw [h_factor]
    rw [Complex.norm_mul, mul_pow]
  -- Rewrite each summand via the factorisation.
  simp only [h_summand]
  -- Now reindex the outer double sum via digitSplit: p ↔ (m_p, a_p), q ↔ (m_q, a_q).
  -- Use Equiv.sum_comp with digitSplit.symm to switch from ∑ p to ∑ (m_p, a_p).
  set e := digitSplit k with he
  have h_reindex : ∀ (f : Fin (3^(2*k)) → ℝ), ∑ p, f p = ∑ ap : Fin (3^k) × Fin (3^k), f (e.symm ap) := by
    intro f
    exact (Equiv.sum_comp e.symm f).symm
  rw [h_reindex, Finset.sum_congr rfl (fun _ _ => h_reindex _)]
  -- Now the sum is ∑ (m_p, a_p) : Fin(3^k)×Fin(3^k), ∑ (m_q, a_q) : ..., F(...).
  -- Convert double product sum via Fintype.sum_prod_type (uncurried form).
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  -- Now: ∑ m_p, ∑ a_p, ∑ m_q, ∑ a_q, ‖(ρ - σ)(...)‖^2 * ‖P(...)‖^2
  -- where (...) uses digitEquiv-firstK/lastK of e.symm.
  -- Key fact: for q = e.symm (m_q, a_q), firstK-enc q = m_q and lastK-enc q = a_q.
  -- This is the right_inv of digitSplit.
  have h_first_enc : ∀ (ap : Fin (3^k) × Fin (3^k)),
      digitEquiv k (firstKDigits k ((digitEquiv (2*k)).symm (e.symm ap))) = ap.1 := by
    intro ap
    have := (e.right_inv ap)
    simp only [he] at this
    exact congr_arg Prod.fst this
  have h_last_enc : ∀ (ap : Fin (3^k) × Fin (3^k)),
      digitEquiv k (lastKDigits k ((digitEquiv (2*k)).symm (e.symm ap))) = ap.2 := by
    intro ap
    have := (e.right_inv ap)
    simp only [he] at this
    exact congr_arg Prod.snd this
  -- Rewrite all firstK-enc and lastK-enc occurrences.
  simp only [h_first_enc, h_last_enc]
  -- Now: ∑ mp, ∑ ap, ∑ mq, ∑ aq, ‖(ρ - σ) mp mq‖^2 * ‖P ap aq‖^2
  -- Target: frobeniusSqDist ρ σ.
  -- Step 1: swap ap and mq via Finset.sum_comm at each outer mp.
  have h_swap : ∀ mp : Fin (3^k),
      ∑ ap : Fin (3^k), ∑ mq : Fin (3^k), ∑ aq : Fin (3^k),
        ‖(ρ - σ) mp mq‖ ^ 2 * ‖ancillaProjector k ap aq‖ ^ 2
        = ∑ mq : Fin (3^k), ∑ ap : Fin (3^k), ∑ aq : Fin (3^k),
        ‖(ρ - σ) mp mq‖ ^ 2 * ‖ancillaProjector k ap aq‖ ^ 2 := by
    intro _; rw [Finset.sum_comm]
  simp only [h_swap]
  -- Now: ∑ mp, ∑ mq, ∑ ap, ∑ aq, ‖(ρ - σ) mp mq‖^2 * ‖P ap aq‖^2
  -- Step 2: at each (mp, mq), factor ‖(ρ - σ) mp mq‖^2 out of the ap, aq sum.
  have h_factor : ∀ mp mq : Fin (3^k),
      ∑ ap : Fin (3^k), ∑ aq : Fin (3^k),
        ‖(ρ - σ) mp mq‖ ^ 2 * ‖ancillaProjector k ap aq‖ ^ 2
        = ‖(ρ - σ) mp mq‖ ^ 2 *
          ∑ ap : Fin (3^k), ∑ aq : Fin (3^k), ‖ancillaProjector k ap aq‖ ^ 2 := by
    intros _ _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [Finset.mul_sum]
  simp only [h_factor]
  -- Now: ∑ mp, ∑ mq, ‖(ρ - σ) mp mq‖^2 * (∑ ap aq ‖P ap aq‖^2)
  -- Step 3: apply frobeniusSqNorm_ancillaProjector to reduce inner sum to 1.
  rw [frobeniusSqNorm_ancillaProjector]
  -- Now: ∑ mp mq ‖(ρ - σ) mp mq‖^2 * 1 = ∑ i j ‖ρ i j - σ i j‖^2
  simp only [mul_one]
  refine Finset.sum_congr rfl (fun mp _ => Finset.sum_congr rfl (fun mq _ => ?_))
  rw [Matrix.sub_apply]

/-! ## Section 7 — In-file axiom audit (build-tree-discipline)

Every principal declaration audits to a subset of
`[propext, Classical.choice, Quot.sound]`. Zero project axioms, zero
`sorry`, zero tactic-form `native_decide`.

Charter reference: `codex/CHURN_CHI_K_CHARTER_2026-09-12.md` §3.5. -/

section AxiomAudit

-- Section 1: definitions
#print axioms frobeniusSqDist
#print axioms churnFrobenius

-- Section 2: T1, T2, T3
#print axioms frobeniusSqDist_nonneg
#print axioms churnFrobenius_nonneg
#print axioms frobeniusSqDist_symm
#print axioms churnFrobenius_symm
#print axioms frobeniusSqDist_eq_zero_iff
#print axioms churnFrobenius_eq_zero_iff

-- Section 3: T4 unitary invariance
#print axioms frobeniusSqDist_unitary_invariant
#print axioms churnFrobenius_unitary_invariant

-- Section 4: digit-compatible lift
#print axioms digitAncillaLift

-- Section 5: T5a partial-trace recovery (public endpoint)
#print axioms partialTraceMorphism_digitAncillaLift

-- Section 6: T5b public endpoint
#print axioms churnFrobenius_digitAncillaLift_invariant

-- Section 6: private Kronecker-path supporting declarations
-- (file-scope only, NOT part of public API — in-file axiom checks
-- retained per user directive for kernel-audit continuity)
#print axioms ancillaProjector
#print axioms reindexKroneckerLift
#print axioms digitAncillaLift_eq_reindexKroneckerLift
#print axioms digitSplit

end AxiomAudit

end PrincipiaTractalis.Consciousness.FrobeniusChurn
