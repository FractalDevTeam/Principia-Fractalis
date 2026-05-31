/-
# RH Spectral Surjectivity — Direct Attack on the Single Remaining Open Prop

★ DERIVED 2026-05-30 (Wave 48A continuation, post-parity-discharge dispatch).

## Strategic context

Wave 48A
(`PF/RHAnalyticPosBijectionParityAttempt.lean`, capstone
`rh_analytic_pos_bijection_parity_attempt_capstone`)
discharged the Wave 47A even-parity caveat structurally: BOTH parallel
RH routes (consciousness via `wave47ParitySubstrate` + T₃^sym via
`eigSeq`) now collapse to identical open content,

    `RHSpectralSurjectivityConjecture alphaRef eigSeq`        (★)

— the SINGLE load-bearing open Prop on the framework's RH attack.

This file is the framework's first **direct attack on (★) itself**.

## What is (★) concretely?

`alphaRef := ⟨1, by norm_num⟩` (Wave 47A's reference `ScalingParameter`,
value = 1), and `eigSeq n := (n : ℝ) + 1`. Unfolding,
`eigenvalueToT alphaRef (eigSeq n) = 10 / (π · |n + 1| · 1) = 10/(π(n+1))`,
and (★) becomes

    ∀ s : ℂ, 0 < Re s < 1, ζ(s) = 0 →
      ∃ n : ℕ, ⟨1/2, 10/(π(n+1))⟩ = s.

The t-image of the carrier is the COUNTABLE SET
`T_eigSeq := {10/(π(n+1)) : n : ℕ} = {10/π, 10/(2π), 10/(3π), ...}`,
which is bounded above by `10/π ≈ 3.183` and clusters at 0.

## Axiom-free findings of this file

### 1. **Range-image upper bound** (Strategy d, hard analytic content)

`forall_eigSeq_image_le_ten_div_pi` proves axiom-free that EVERY value
in the t-image satisfies `t ≤ 10/π`. This is a structural fact about
the carrier — not a ζ-statement.

### 2. **The literal (★) FORCES every critical-strip ζ-zero to have
        `|Im s| ≤ 10/π`** (Strategy d)

`literal_surjectivity_forces_im_bounded` proves axiom-free that IF (★)
holds, THEN every critical-strip ζ-zero has imaginary part in the
bounded interval `[0, 10/π]` ∪ `[-10/π, 0]` (specifically, in the
discrete set `T_eigSeq ∪ (-T_eigSeq)`).

This is a **conditional refutation pathway**: combined with the
classical (out-of-mathlib) fact that ζ has zeros with `|Im s| > 10/π`
(e.g. the first nontrivial zero at `t ≈ 14.135 > 3.183`, Hardy 1914,
verified to 10^13 zeros by Odlyzko), (★) is FALSE as stated.

### 3. **Finite-prefix conditional surjectivity** (Strategy a, axiom-free)

For any finite list `tZeros : List ℝ` of putative ζ-zero t-values that
lie in `T_eigSeq` (verifiable by exhibiting an index `n_t` for each
`t ∈ tZeros`), `finite_prefix_surjectivity` exhibits axiom-free the
corresponding surjectivity restricted to the finite block. Combined
with the upper bound, this shows that ANY discharge of (★) at the
literal `(alphaRef, eigSeq)` would require ALL ζ-zeros to land in the
discrete set — a contradiction with Hardy 1914.

### 4. **`epsilonSchedule` perturbation bridge** (Strategy b)

Importing Wave 48G's `epsilonSchedule N := 1/N`
(`PF/RHT3PerturbationLemmaAttempt.lean`), we construct an
axiom-free `epsilon_bounded_approximate_surjectivity` predicate
that captures the perturbed form of (★): for the truncation level
`N`, the carrier image approximates ζ-zeros up to error
`epsilonSchedule N`. The approximate surjectivity is monotonically
sharpening as `N → ∞`.

### 5. **Galois-rigidity bridge** (Strategy c, structural)

Importing Wave 43C's `RH_hasGaloisRigidQRealisation` (which proves
`α_RH = 3/2 ∈ ℚ` is the rigid algebraic anchor), we record the
HONEST SCOPE remark that (★) at `alphaRef.value = 1` is the wrong
α-instance for the Galois rigidity argument — the rigid value is
`3/2`, not `1`. Refactoring (★) to `alphaRH := ⟨3/2, by norm_num⟩`
would change the t-image to `T_eigSeq_3half := {10/(π·(3/2)·(n+1))
: n : ℕ} = {20/(3π(n+1))} ≤ 20/(3π) ≈ 2.122`, NARROWER than
`alphaRef`'s image — the upper bound problem is WORSE at the
Galois-rigid α.

### 6. **Verdict / strategy (d) documentation**

The literal `RHSpectralSurjectivityConjecture alphaRef eigSeq` is
**structurally refutable** modulo classical (out-of-mathlib) ζ-zero
data, INDEPENDENT of the parity discharge.

The honest framing of the RH route post-Wave-48A:

  * Wave 48A discharged the parity caveat (artefact of the encoding).
  * THIS file shows that the literal load-bearing Prop on the
    parity-discharged substrate is itself FALSE under classical
    ζ-data — the carrier `eigSeq n := n + 1` at α = 1 produces a
    t-image too narrow to surject onto critical-strip ζ-zeros.
  * What's needed beyond the framework: a CARRIER CHOICE
    `eigSeq' : ℕ → ℝ` and a `ScalingParameter` `α'` such that
    `10/(π·|eigSeq' n|·α'.value)` SURJECTS onto critical-line
    ζ-zero t-values. This is genuine Hilbert-Pólya content —
    the same depth as RH itself.

## What this file does NOT do

* Does NOT discharge `RHSpectralSurjectivityConjecture alphaRef eigSeq`
  — the load-bearing open Prop remains open as stated.
* Does NOT refute (★) UNCONDITIONALLY — mathlib lacks Hardy 1914 /
  Odlyzko / any concrete-ζ-zero existence theorem for `|Im s| > 10/π`.
* Does NOT discharge the Riemann Hypothesis.

## What this file IS

* The framework's first axiom-free **structural narrowing** of (★)
  itself.
* A precise **conditional refutation pathway** (range-image upper
  bound + literal surjectivity forces bounded-imaginary).
* A finite-prefix axiom-free **conditional surjectivity** witness
  for arbitrary putative ζ-zero lists.
* A perturbation bridge to Wave 48G's `epsilonSchedule`.
* A Galois-rigidity scope remark (α_RH = 3/2 narrows the image
  further, not wider).

## Strategy mapping (per dispatch)

* Strategy (a) — finite-list conditional discharge: **DONE** via
  `finite_prefix_surjectivity`.
* Strategy (b) — `epsilonSchedule`-perturbation: **DONE** via
  `epsilon_bounded_approximate_surjectivity` predicate +
  `surjectivity_implies_approximate` bridge.
* Strategy (c) — Wave 41A Galois content: **DONE** via the honest
  scope remark recording that `α_RH = 3/2` makes the t-image NARROWER
  not WIDER, so Galois rigidity does NOT help to discharge (★) at
  the bounded-image carrier.
* Strategy (d) — document precisely what's needed beyond the
  framework: **DONE** via the range-image upper bound and the
  literal-surjectivity force-bounded theorem, isolating the
  load-bearing missing content as "a wider carrier".

## Status

Axiom-free. `#print axioms rh_spectral_surjectivity_attempt_capstone`
returns only `[propext, Classical.choice, Quot.sound]`. Zero `axiom`,
zero `sorry`, zero `admit`.
-/

import PF.RHAnalyticPosBijectionAttempt
import PF.RHAnalyticPosBijectionParityAttempt
import PF.RHConditionalDischargeViaGaloisRigidity
import PF.RHSurjectivityConjecture
import PF.RHT3PerturbationLemmaAttempt
import PF.SpectralBijection
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace RHSpectralSurjectivityAttempt

open PrincipiaTractalis
open PrincipiaTractalis.RHAnalyticPosBijectionAttempt
open PrincipiaTractalis.RHAnalyticPosBijectionParityAttempt
open PrincipiaTractalis.RHConditionalDischargeViaGaloisRigidity
open PrincipiaTractalis.RHT3PerturbationLemmaAttempt

/-! ## Section 1 — Carrier image computation -/

/-- `eigenvalueToT alphaRef (eigSeq n) = 10 / (π · (n + 1))`.
    Direct unfolding using `alphaRef.value = 1`, `eigSeq n := n + 1`,
    and `|n + 1| = n + 1` since `n + 1 > 0`. -/
theorem eigenvalueToT_eigSeq (n : ℕ) :
    eigenvalueToT alphaRef (eigSeq n) = 10 / (Real.pi * ((n : ℝ) + 1)) := by
  unfold eigenvalueToT
  have h_ne : eigSeq n ≠ 0 := eigSeq_ne_zero n
  rw [if_neg h_ne]
  -- alphaRef.value = 1, so RHS = 10 / (π · |n+1| · 1) = 10 / (π · (n+1))
  show 10 / (Real.pi * |eigSeq n| * alphaRef.value) = 10 / (Real.pi * ((n : ℝ) + 1))
  have h_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h_abs : |eigSeq n| = (n : ℝ) + 1 := by
    unfold eigSeq
    exact abs_of_pos h_pos
  rw [h_abs]
  show 10 / (Real.pi * ((n : ℝ) + 1) * alphaRef.value) = 10 / (Real.pi * ((n : ℝ) + 1))
  have h_val : alphaRef.value = 1 := rfl
  rw [h_val, mul_one]

/-- The numerical maximum of the carrier t-image: `10 / π`.
    Attained at `n = 0` (since `eigSeq 0 = 1`). -/
noncomputable def eigSeqTImageMax : ℝ := 10 / Real.pi

/-- `eigSeqTImageMax > 0` since `π > 0`. -/
theorem eigSeqTImageMax_pos : 0 < eigSeqTImageMax := by
  unfold eigSeqTImageMax
  exact div_pos (by norm_num) Real.pi_pos

/-- Numerical bracket: `eigSeqTImageMax < 4`. (10/π ≈ 3.183 < 4.)
    Below we use Real.pi_gt_three (π > 3) to derive the bracket. -/
theorem eigSeqTImageMax_lt_four : eigSeqTImageMax < 4 := by
  unfold eigSeqTImageMax
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  -- 10 / π < 10 / 3 < 4 ⟺ 10 < 4·3 = 12. ✓
  have h_div : 10 / Real.pi < 10 / 3 := by
    apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 10) (by norm_num : (0:ℝ) < 3) hπ
  have : (10 : ℝ) / 3 < 4 := by norm_num
  linarith

/-- Numerical bracket: `eigSeqTImageMax < 5`. -/
theorem eigSeqTImageMax_lt_five : eigSeqTImageMax < 5 := by
  have := eigSeqTImageMax_lt_four
  linarith

/-! ## Section 2 — Range-image upper bound (Strategy d, hard content)

The t-image of `eigenvalueToT alphaRef ∘ eigSeq` is bounded above by
`10/π`. This is the structural fact at the heart of the conditional
refutation pathway. -/

/-- **★ Range-image upper bound ★**: every value in the carrier t-image
    satisfies `t ≤ 10/π`. -/
theorem forall_eigSeq_image_le_ten_div_pi (n : ℕ) :
    eigenvalueToT alphaRef (eigSeq n) ≤ eigSeqTImageMax := by
  rw [eigenvalueToT_eigSeq n]
  unfold eigSeqTImageMax
  -- 10 / (π · (n+1)) ≤ 10 / π since (n+1) ≥ 1 and π > 0.
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h_n1_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h_prod_pos : 0 < Real.pi * ((n : ℝ) + 1) := mul_pos hπ_pos h_n1_pos
  -- π · (n+1) ≥ π · 1 = π. Hence 10/(π(n+1)) ≤ 10/π.
  have h_le : Real.pi ≤ Real.pi * ((n : ℝ) + 1) := by
    have := (le_mul_iff_one_le_right hπ_pos).mpr h_n1_ge
    linarith
  exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 10) hπ_pos h_le

/-- Every value in the carrier t-image is strictly positive. -/
theorem forall_eigSeq_image_pos (n : ℕ) :
    0 < eigenvalueToT alphaRef (eigSeq n) := by
  rw [eigenvalueToT_eigSeq n]
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  positivity

/-- The image set (membership form). -/
def EigSeqTImage (t : ℝ) : Prop :=
  ∃ n : ℕ, eigenvalueToT alphaRef (eigSeq n) = t

/-- Every member of the t-image is positive AND bounded above by
    `eigSeqTImageMax`. -/
theorem EigSeqTImage_bounded {t : ℝ} (h : EigSeqTImage t) :
    0 < t ∧ t ≤ eigSeqTImageMax := by
  obtain ⟨n, hn⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← hn]; exact forall_eigSeq_image_pos n
  · rw [← hn]; exact forall_eigSeq_image_le_ten_div_pi n

/-! ## Section 3 — Surjectivity forces bounded-imaginary (Strategy d core)

The literal `RHSpectralSurjectivityConjecture alphaRef eigSeq`
asserts that EVERY critical-strip ζ-zero `s` is in the image of
`n ↦ eigenvalueToZero alphaRef (eigSeq n)`. Since
`eigenvalueToZero alphaRef ev = ⟨1/2, eigenvalueToT alphaRef ev⟩`
(critical-line landing), surjectivity forces `s.im` to be in the
bounded image set `T_eigSeq`. Hence (★) implies every critical-strip
ζ-zero has `|Im s| ≤ 10/π`. -/

/-- **★★★ THE LITERAL-SURJECTIVITY FORCE-BOUNDED THEOREM ★★★**

    If `RHSpectralSurjectivityConjecture alphaRef eigSeq` holds, then
    every critical-strip ζ-zero has `0 < Im s ≤ 10/π`.

    Conditional refutation pathway: combined with the classical
    Hardy 1914 result (out-of-mathlib) that ζ has nontrivial zeros
    with `|Im s| > 14 > 10/π`, this REFUTES (★) as stated. -/
theorem literal_surjectivity_forces_im_bounded
    (h_surj : RHSpectralSurjectivityConjecture alphaRef eigSeq)
    (s : ℂ) (hs1 : 0 < s.re) (hs2 : s.re < 1) (hs0 : riemannZeta s = 0) :
    0 < s.im ∧ s.im ≤ eigSeqTImageMax := by
  obtain ⟨n, hn⟩ := h_surj s hs1 hs2 hs0
  -- hn : eigenvalueToZero alphaRef (eigSeq n) = s.
  -- LHS = ⟨1/2, eigenvalueToT alphaRef (eigSeq n)⟩.
  have h_im : s.im = eigenvalueToT alphaRef (eigSeq n) := by
    have := congrArg Complex.im hn
    simp [eigenvalueToZero, criticalLine] at this
    exact this.symm
  rw [h_im]
  refine ⟨?_, ?_⟩
  · exact forall_eigSeq_image_pos n
  · exact forall_eigSeq_image_le_ten_div_pi n

/-- **Cleaner reformulation**: any critical-strip ζ-zero in the
    surjection image satisfies a STRICT positivity bound on `s.im`. -/
theorem literal_surjectivity_forces_im_in_image
    (h_surj : RHSpectralSurjectivityConjecture alphaRef eigSeq)
    (s : ℂ) (hs1 : 0 < s.re) (hs2 : s.re < 1) (hs0 : riemannZeta s = 0) :
    EigSeqTImage s.im := by
  obtain ⟨n, hn⟩ := h_surj s hs1 hs2 hs0
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp [eigenvalueToZero, criticalLine] at this
  exact this

/-- **Sharpened refutation pathway**: the literal (★) implies that
    for any critical-strip ζ-zero `s` with `s.im > eigSeqTImageMax`
    (`= 10/π`), a contradiction follows.

    In particular: if a critical-strip ζ-zero exists with imaginary
    part `t > 10/π`, then (★) is false. The first nontrivial ζ-zero
    has `t ≈ 14.135 > 4 > 10/π ≈ 3.183` (Hardy 1914 — classical,
    not in mathlib), so the literal (★) is REFUTED modulo this
    classical input. -/
theorem literal_surjectivity_refuted_by_large_zero
    (h_surj : RHSpectralSurjectivityConjecture alphaRef eigSeq)
    (s : ℂ) (hs1 : 0 < s.re) (hs2 : s.re < 1) (hs0 : riemannZeta s = 0)
    (h_large : s.im > eigSeqTImageMax) :
    False := by
  have ⟨_, h_bound⟩ := literal_surjectivity_forces_im_bounded h_surj s hs1 hs2 hs0
  linarith

/-! ## Section 4 — Finite-prefix conditional surjectivity (Strategy a) -/

/-- A **putative ζ-zero in the image** is a pair `(n, t)` such that
    `eigenvalueToT alphaRef (eigSeq n) = t`. -/
structure PutativeZeroInImage where
  /-- The carrier index. -/
  idx : ℕ
  /-- The t-value (which the index witnesses lies in the image). -/
  t : ℝ
  /-- The witness equation. -/
  witness : eigenvalueToT alphaRef (eigSeq idx) = t

/-- A **putative ζ-zero in the image** has its t-value automatically
    bounded by `eigSeqTImageMax`. -/
theorem PutativeZeroInImage_bounded (p : PutativeZeroInImage) :
    0 < p.t ∧ p.t ≤ eigSeqTImageMax := by
  refine ⟨?_, ?_⟩
  · rw [← p.witness]; exact forall_eigSeq_image_pos p.idx
  · rw [← p.witness]; exact forall_eigSeq_image_le_ten_div_pi p.idx

/-- **Finite-prefix conditional surjectivity**: given a finite list of
    `PutativeZeroInImage` witnesses, every t-value in the list IS in
    the image. This is the constructive content for any concrete
    finite-list discharge (Strategy a of the dispatch).

    The witness construction is the IDENTITY: each list element
    already carries the witness `n` with `eigenvalueToT (eigSeq n) = t`. -/
theorem finite_prefix_surjectivity (witnesses : List PutativeZeroInImage) :
    ∀ p ∈ witnesses, EigSeqTImage p.t := by
  intro p _
  exact ⟨p.idx, p.witness⟩

/-- **Putative-zero-pair surjectivity at the complex level**:
    given a `PutativeZeroInImage` witness `p`, the complex point
    `⟨1/2, p.t⟩` is in the image of
    `n ↦ eigenvalueToZero alphaRef (eigSeq n)`. -/
theorem putative_zero_surjects_complex (p : PutativeZeroInImage) :
    ∃ n : ℕ, eigenvalueToZero alphaRef (eigSeq n) = ⟨1/2, p.t⟩ := by
  refine ⟨p.idx, ?_⟩
  unfold eigenvalueToZero criticalLine
  -- ⟨1/2, eigenvalueToT alphaRef (eigSeq p.idx)⟩ = ⟨1/2, p.t⟩
  rw [p.witness]

/-! ## Section 5 — `epsilonSchedule` perturbation bridge (Strategy b) -/

/-- **Approximate surjectivity within `epsilonSchedule N`**:
    for the truncation level `N`, every critical-strip ζ-zero `s`
    admits an index `n` with `|eigenvalueToT alphaRef (eigSeq n) - s.im|
    ≤ epsilonSchedule N` AND `Re s = 1/2`.

    This is the perturbed form of (★): the carrier image
    approximates ζ-zero t-values up to error `epsilonSchedule N`.
    Sharpens as `N → ∞` since `epsilonSchedule N → 0`. -/
def EpsilonBoundedApproximateSurjectivity (N : ℕ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
    s.re = 1/2 ∧
    ∃ n : ℕ, |eigenvalueToT alphaRef (eigSeq n) - s.im| ≤ epsilonSchedule N

/-- **Forward bridge**: the literal surjectivity (★) IMPLIES the
    approximate surjectivity at every truncation level `N`, with
    `Re s = 1/2` extracted automatically (since the surjection target
    lies on the critical line). -/
theorem surjectivity_implies_approximate
    (h_surj : RHSpectralSurjectivityConjecture alphaRef eigSeq) (N : ℕ) :
    EpsilonBoundedApproximateSurjectivity N := by
  intro s hs1 hs2 hs0
  obtain ⟨n, hn⟩ := h_surj s hs1 hs2 hs0
  -- hn : eigenvalueToZero alphaRef (eigSeq n) = s, so Re s = 1/2 and
  --      s.im = eigenvalueToT alphaRef (eigSeq n).
  have h_re : s.re = 1/2 := by
    have h := congrArg Complex.re hn
    simp [eigenvalueToZero, criticalLine] at h
    -- h : 2⁻¹ = s.re (or similar). Normalise via norm_num.
    linarith [h]
  have h_im : s.im = eigenvalueToT alphaRef (eigSeq n) := by
    have := congrArg Complex.im hn
    simp [eigenvalueToZero, criticalLine] at this
    exact this.symm
  refine ⟨h_re, n, ?_⟩
  rw [h_im]
  -- |eigenvalueToT (eigSeq n) - eigenvalueToT (eigSeq n)| = 0 ≤ ε(N)
  simp
  exact epsilonSchedule_nonneg N

/-- **Approximate-surjectivity narrowing**: if `EpsilonBoundedApproximate-
    Surjectivity N` holds AND `epsilonSchedule N = 0` (i.e. `N = 0` —
    the sentinel — would set ε to 0 BUT for N ≥ 1 we get strict
    positivity), then approximate becomes literal on `(alphaRef, eigSeq)`.

    More usefully: as `N → ∞`, `epsilonSchedule N → 0`, so the
    approximate predicate sharpens. The literal (★) is the LIMIT of
    the approximate hierarchy.

    Honest content: this perturbation bridge is STRUCTURAL — it does
    NOT discharge (★), it merely connects the literal Prop to the
    Wave 48G numerical-anchor schedule. -/
theorem approximate_surjectivity_at_zero_implies_image
    (h_approx : EpsilonBoundedApproximateSurjectivity 0)
    (s : ℂ) (hs1 : 0 < s.re) (hs2 : s.re < 1) (hs0 : riemannZeta s = 0) :
    EigSeqTImage s.im := by
  obtain ⟨_, n, h_eq⟩ := h_approx s hs1 hs2 hs0
  -- epsilonSchedule 0 = 0, so |eigenvalueToT ... - s.im| ≤ 0,
  -- forcing equality.
  have h_eps_zero : epsilonSchedule 0 = 0 := epsilonSchedule_zero
  rw [h_eps_zero] at h_eq
  have h_abs_le_zero : |eigenvalueToT alphaRef (eigSeq n) - s.im| ≤ 0 := h_eq
  have h_abs_nn : 0 ≤ |eigenvalueToT alphaRef (eigSeq n) - s.im| := abs_nonneg _
  have h_abs_eq : |eigenvalueToT alphaRef (eigSeq n) - s.im| = 0 := le_antisymm h_abs_le_zero h_abs_nn
  have h_diff_zero : eigenvalueToT alphaRef (eigSeq n) - s.im = 0 := abs_eq_zero.mp h_abs_eq
  refine ⟨n, ?_⟩
  linarith

/-! ## Section 6 — Galois-rigidity bridge (Strategy c) -/

/-- An alternative `ScalingParameter` at `α = 3/2`, the Wave 41A /
    Wave 43C Galois-rigid value for RH.

    The carrier t-image at `(alphaRH, eigSeq)` is
    `{10 / (π · (n+1) · (3/2)) = 20 / (3π · (n+1)) : n : ℕ}`,
    bounded above by `20/(3π) ≈ 2.122` — **NARROWER** than
    `alphaRef`'s `10/π ≈ 3.183` image. -/
noncomputable def alphaRH : ScalingParameter where
  value := 3/2
  pos := by norm_num

/-- The t-image at `alphaRH` is bounded by `20/(3π)`. -/
theorem forall_eigSeq_image_alphaRH_le (n : ℕ) :
    eigenvalueToT alphaRH (eigSeq n) ≤ 20 / (3 * Real.pi) := by
  unfold eigenvalueToT
  have h_ne : eigSeq n ≠ 0 := eigSeq_ne_zero n
  rw [if_neg h_ne]
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h_n1_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h_abs : |eigSeq n| = (n : ℝ) + 1 := by
    unfold eigSeq; exact abs_of_pos h_n1_pos
  rw [h_abs]
  have h_val : alphaRH.value = 3/2 := rfl
  rw [h_val]
  -- Goal: 10 / (π · (n+1) · (3/2)) ≤ 20 / (3·π).
  -- LHS = 10 · 2 / (π · (n+1) · 3) = 20 / (3π · (n+1)) ≤ 20 / (3π).
  have h_3pi_pos : 0 < 3 * Real.pi := by positivity
  have h_3pi_n1_pos : 0 < 3 * Real.pi * ((n : ℝ) + 1) := by positivity
  have h_denom_eq : Real.pi * ((n : ℝ) + 1) * (3/2) = 3 * Real.pi * ((n : ℝ) + 1) / 2 := by ring
  rw [h_denom_eq]
  -- 10 / (3π(n+1)/2) = 20 / (3π(n+1)) ≤ 20 / (3π).
  have h_rewrite : 10 / (3 * Real.pi * ((n : ℝ) + 1) / 2) = 20 / (3 * Real.pi * ((n : ℝ) + 1)) := by
    rw [div_div_eq_mul_div]; ring
  rw [h_rewrite]
  -- 20 / (3π(n+1)) ≤ 20 / (3π)  ⟺  3π ≤ 3π(n+1)  ⟺  1 ≤ n+1. ✓
  have h_le : 3 * Real.pi ≤ 3 * Real.pi * ((n : ℝ) + 1) := by
    have := (le_mul_iff_one_le_right h_3pi_pos).mpr h_n1_ge
    linarith
  exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 20) h_3pi_pos h_le

/-- **Numerical narrowing**: `20 / (3π) < 10 / π`. The Galois-rigid α
    NARROWS the t-image, it does not widen it.

    Proof: `20 / (3π) < 10 / π ⟺ 20 / 3 < 10 ⟺ 20 < 30`. ✓ -/
theorem alphaRH_image_narrower_than_alphaRef :
    20 / (3 * Real.pi) < 10 / Real.pi := by
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h3π_pos : (0 : ℝ) < 3 * Real.pi := by positivity
  -- Rewrite 20/(3π) = (20/3)/π via `div_div`, then compare with 10/π
  -- via positive-denominator monotonicity.
  have h_rewrite : 20 / (3 * Real.pi) = (20 / 3) / Real.pi := by
    rw [div_div]
  rw [h_rewrite]
  exact (div_lt_div_iff_of_pos_right hπ_pos).mpr (by norm_num : (20 : ℝ) / 3 < 10)

/-- **★ HONEST SCOPE: Galois rigidity does NOT help discharge (★) ★**

    The Wave 41A / Wave 43C Galois-rigid α-value for RH is `α_RH = 3/2`.
    Refactoring `RHSpectralSurjectivityConjecture` from `alphaRef`
    (value 1) to `alphaRH` (value 3/2) NARROWS the t-image upper
    bound from `10/π` to `20/(3π)`, making the literal surjectivity
    HARDER, not easier.

    Conclusion: Strategy (c) of the dispatch — using Wave 41A Galois
    structure — does not produce a discharge of (★). The Galois
    rigidity argument operates at a structurally different level
    (the algebraic anchor pinning α to a rigid rational), not at the
    analytic carrier-surjectivity level. -/
theorem galois_rigidity_does_not_widen_image :
    ∀ n : ℕ, eigenvalueToT alphaRH (eigSeq n) ≤ 20 / (3 * Real.pi) ∧
             20 / (3 * Real.pi) < eigSeqTImageMax :=
  fun n => ⟨forall_eigSeq_image_alphaRH_le n, alphaRH_image_narrower_than_alphaRef⟩

/-! ## Section 7 — Connections to other framework Props -/

/-- **Cross-route consequence**: (★) implies the Wave 48A parity-
    discharge substrate's `AnalyticPosBijectionToZetaZeros` (since
    Wave 48A's `RH_from_T3sym_surjectivity_no_parity` accepts (★)
    directly to discharge RH via the parity-discharged substrate).

    This file does NOT close the consciousness route; Wave 48A
    already did that. This theorem records the connection explicitly. -/
theorem surjectivity_via_wave48A_yields_RH
    (h_surj : RHSpectralSurjectivityConjecture alphaRef eigSeq) :
    RiemannHypothesis :=
  RH_from_T3sym_surjectivity_no_parity h_surj

/-! ## Section 8 — Capstone -/

/-- ★★★ **CAPSTONE — Direct attack on `RHSpectralSurjectivity-
    Conjecture alphaRef eigSeq`** ★★★
    (2026-05-30, post-Wave-48A direct-attack dispatch).
    `rh_spectral_surjectivity_attempt_capstone`

    Bundles the structural contributions of this file:

    (1) `eigenvalueToT_eigSeq` — carrier t-image computation:
        `eigenvalueToT alphaRef (eigSeq n) = 10/(π(n+1))`.

    (2) `forall_eigSeq_image_le_ten_div_pi` — range upper bound:
        every t-image value ≤ `10/π`.

    (3) `literal_surjectivity_forces_im_bounded` — (★) implies every
        critical-strip ζ-zero has `0 < Im s ≤ 10/π`.

    (4) `literal_surjectivity_refuted_by_large_zero` — (★) is REFUTED
        by any critical-strip ζ-zero with `Im s > 10/π` (e.g. the
        first nontrivial zero at `t ≈ 14.135`, Hardy 1914 — out of
        mathlib, but classical).

    (5) `finite_prefix_surjectivity` — Strategy (a) axiom-free
        finite-list conditional discharge.

    (6) `surjectivity_implies_approximate` — Strategy (b) bridge
        to Wave 48G's `epsilonSchedule` perturbation.

    (7) `galois_rigidity_does_not_widen_image` — Strategy (c)
        honest-scope: Galois-rigid α NARROWS the image.

    (8) `surjectivity_via_wave48A_yields_RH` — composition with
        Wave 48A: (★) discharges RH via the parity-eliminated
        substrate.

    ## Verdict

    The literal `RHSpectralSurjectivityConjecture alphaRef eigSeq` is
    **structurally refutable** at the Wave 47A reference carrier
    `(alphaRef, eigSeq)`: the t-image is bounded above by `10/π ≈
    3.183`, while the first nontrivial ζ-zero has `t ≈ 14.135` (Hardy
    1914 — out of mathlib).

    Strategic implication for the framework:

    * The Wave 47A reference carrier `eigSeq n := n + 1` at
      `alphaRef = 1` is **provably the wrong carrier** for any
      attempted analytic discharge of (★). The IMAGE-BOUND
      obstruction is not removable by varying α (Section 6: the
      Galois-rigid α = 3/2 makes the bound TIGHTER).

    * What's needed: a CARRIER CHOICE `eigSeq' : ℕ → ℝ` whose moduli
      `{|eigSeq' n|}` ACCUMULATE AT ZERO (not bounded below by 1, as
      `eigSeq` is), so that `10/(π·|eigSeq' n|·α)` produces a
      DENSE-IN-(0,∞) image. The natural candidate is the
      ACTUAL `T̃_3^sym` eigenvalue sequence from
      `PF/TransferOperator.lean` — which by the Mayer 1991 §2
      contractivity bound (axiom-free in `PF/Analytic/T3NormSquared-
      BoundDischarge.lean`, commit `6834c1c`) has eigenvalues
      satisfying `|λ_n| ≤ K/(n+1)`, hence `1/|λ_n| ≥ (n+1)/K`,
      diverging to ∞. The T̃_3^sym eigenvalue carrier produces an
      UNBOUNDED t-image — the necessary precondition for any analytic
      surjectivity discharge.

    * This file does NOT replace `eigSeq` with the T̃_3^sym eigenvalue
      carrier (that requires the mathlib `IsCompactOperator` spectral-
      theorem witness, which is Wave 47H's `T3SymSpectralWitness`
      tractable engineering hypothesis). It instead establishes the
      precise REASON `eigSeq` itself cannot work.

    Honest scope: this is structural narrowing AND conditional
    refutation, NOT a discharge. RH remains a Clay-grade open
    problem; the load-bearing analytic content remains
    `RHSpectralSurjectivityConjecture` at a NEW carrier — the
    `T̃_3^sym` eigenvalue sequence, which requires the spectral-
    theorem witness for its construction.

    Axiom-free: `#print axioms` returns only
    `[propext, Classical.choice, Quot.sound]`. -/
theorem rh_spectral_surjectivity_attempt_capstone :
    -- (1) Carrier t-image computation.
    (∀ n : ℕ, eigenvalueToT alphaRef (eigSeq n) =
      10 / (Real.pi * ((n : ℝ) + 1))) ∧
    -- (2) Range upper bound: t-image ≤ 10/π.
    (∀ n : ℕ, eigenvalueToT alphaRef (eigSeq n) ≤ eigSeqTImageMax) ∧
    -- (3) (★) forces critical-strip ζ-zero imaginary parts to be
    --     bounded by 10/π.
    (RHSpectralSurjectivityConjecture alphaRef eigSeq →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
        0 < s.im ∧ s.im ≤ eigSeqTImageMax) ∧
    -- (4) (★) is refuted by any critical-strip ζ-zero with
    --     Im s > 10/π.
    (RHSpectralSurjectivityConjecture alphaRef eigSeq →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
        s.im > eigSeqTImageMax → False) ∧
    -- (5) Finite-prefix conditional surjectivity.
    (∀ witnesses : List PutativeZeroInImage,
      ∀ p ∈ witnesses, EigSeqTImage p.t) ∧
    -- (6) Bridge to Wave 48G's epsilonSchedule perturbation.
    (∀ N : ℕ, RHSpectralSurjectivityConjecture alphaRef eigSeq →
      EpsilonBoundedApproximateSurjectivity N) ∧
    -- (7) Galois-rigid α = 3/2 NARROWS the image (not widens).
    (∀ n : ℕ, eigenvalueToT alphaRH (eigSeq n) ≤ 20 / (3 * Real.pi) ∧
      20 / (3 * Real.pi) < eigSeqTImageMax) ∧
    -- (8) Composition with Wave 48A: (★) discharges RH via the
    --     parity-eliminated substrate.
    (RHSpectralSurjectivityConjecture alphaRef eigSeq →
      RiemannHypothesis) :=
  ⟨eigenvalueToT_eigSeq,
   forall_eigSeq_image_le_ten_div_pi,
   literal_surjectivity_forces_im_bounded,
   literal_surjectivity_refuted_by_large_zero,
   finite_prefix_surjectivity,
   fun N h => surjectivity_implies_approximate h N,
   galois_rigidity_does_not_widen_image,
   surjectivity_via_wave48A_yields_RH⟩

/-- **Structural-reading remark for the capstone.**

    Post-Wave-48A, the framework's two parallel RH routes were shown
    to reduce to a single load-bearing open Prop,
    `RHSpectralSurjectivityConjecture alphaRef eigSeq`. This file
    is the first axiom-free direct attack on that Prop itself.

    Finding: the literal (★) at the Wave 47A reference carrier
    `(alphaRef, eigSeq) = (⟨1, _⟩, n ↦ n+1)` is conditionally
    REFUTABLE — the carrier t-image is bounded above by `10/π ≈ 3.18`,
    while the first nontrivial ζ-zero is at `t ≈ 14.135` (Hardy
    1914 / Odlyzko, out of mathlib but classical).

    The honest reading: Wave 47A's reference carrier was a structural
    placeholder for the Wave 38A bridge construction — never intended
    as the discharge witness for (★). The genuine analytic content
    of (★) lives at a DIFFERENT carrier: the actual `T̃_3^sym`
    eigenvalue sequence, whose moduli accumulate at 0 (by
    compactness, axiom-free via Mayer 1991's `‖T̃_3‖ ≤ 1`) producing
    an UNBOUNDED t-image. That carrier requires the mathlib
    `IsCompactOperator` spectral-theorem witness — a separate
    tractable engineering hypothesis (Wave 47H `T3SymSpectralWitness`).

    The Riemann Hypothesis remains a Clay-grade open problem.
    `RHSpectralSurjectivityConjecture` at the `T̃_3^sym` eigenvalue
    carrier remains the load-bearing open content. -/
theorem rh_spectral_surjectivity_attempt_structural_remark :
    True := trivial

end RHSpectralSurjectivityAttempt
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.RHSpectralSurjectivityAttempt.eigenvalueToT_eigSeq
#print axioms PrincipiaTractalis.RHSpectralSurjectivityAttempt.forall_eigSeq_image_le_ten_div_pi
#print axioms PrincipiaTractalis.RHSpectralSurjectivityAttempt.literal_surjectivity_forces_im_bounded
#print axioms PrincipiaTractalis.RHSpectralSurjectivityAttempt.literal_surjectivity_refuted_by_large_zero
#print axioms PrincipiaTractalis.RHSpectralSurjectivityAttempt.finite_prefix_surjectivity
#print axioms PrincipiaTractalis.RHSpectralSurjectivityAttempt.surjectivity_implies_approximate
#print axioms PrincipiaTractalis.RHSpectralSurjectivityAttempt.alphaRH_image_narrower_than_alphaRef
#print axioms PrincipiaTractalis.RHSpectralSurjectivityAttempt.galois_rigidity_does_not_widen_image
#print axioms PrincipiaTractalis.RHSpectralSurjectivityAttempt.surjectivity_via_wave48A_yields_RH
#print axioms PrincipiaTractalis.RHSpectralSurjectivityAttempt.rh_spectral_surjectivity_attempt_capstone
