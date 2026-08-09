/-
# r218: The non-commuting digit-position system.

★ 2026-08-07 r218 — the promotion of the framework's scalar digit character
`ω^{D₃(n)}` to a NON-COMMUTING ordered product over digit positions. ★

## What this file is

The corpus contains two structurally unrelated programmes that have been filed
under one name:

* **(A)** the Dirichlet series of the 3-multiplicative function `n ↦ ω^{D₃(n)}`,
  `D₃` = base-3 digit sum.  This is ORDER-BLIND: `D₃` factors through the digit
  multiset, so its "transfer matrix" is `1 × 1` — a scalar.  Kernel results:
  `PF/SigmaAbscissa_r212.lean` (σ(α) = log₃|1 + 2cos πα|) and
  `PF/EulerFactorThree_r214.lean` (the 3-Euler factor).

* **(B)** Ruelle–Mayer transfer operators over WORDS.  ORDER-SENSITIVE, and
  genuinely operator-valued.  Kernel results: r188c / r191 / r192, and
  `PF/TwoStateTransfer_r213.lean`.

This file is the promotion that makes (A) an INSTANCE of (B).  Replace the
scalar weight `ω^d` carried at each digit position by an arbitrary element
`M d` of a (possibly non-commutative) semiring — concretely a matrix — and take
the ORDERED product over digit positions:

    wordWeight M d  =  M (d 0) * M (d 1) * ⋯ * M (d (k-1)) ,   d : Fin k → Fin 3 .

The digit-block identity survives verbatim (§2), the scalar system is recovered
exactly as the `c • 1` sub-system (§3), and §4 exhibits two digit tuples with
the SAME multiset and DIFFERENT weight — which no scalar digit weight can do.

## Why this matters to the manuscript

The manuscript already reaches for exactly this, and does not name it.

`ch21_p_vs_np.tex:181` defines the NP-class energy with the term

    Σ_{i=1}^{|c|}  i · D(c_i)          ← a POSITION WEIGHT

at precisely the point where `NP ≠ P` is supposed to come from — the
"certificate branching structure".  Forty-five lines later, `ch21:226` builds
the phase of `H_NP` out of `W(x,c) = Σ_i D(c_i) + D(encode(x,c))`, the
UNWEIGHTED digital sum.  So `H_NP` mixes an order-SENSITIVE energy with an
order-BLIND phase.  Nothing in the corpus says which of the two the operator is
supposed to be, and no object is defined that could carry both.  This file
defines one.

`r212`'s σ(α) is the `1 × 1` case of §2: `chi_scalar` (§3) shows the scalar
digit character is exactly the sub-system `M d = ω^d • 1`, and
`sum_pow_digitSum` is r212's `digitBlock_sum` in tuple form
(`digitBlock_sum_tuple_eq_range` proves they agree).  The scalar system
provably reaches only composition-determined data — that is r212 §7 (σ ∈ {0,1}
forces α rational, so the six irrational α are unreachable), and it is the same
fact in another domain as `PF/TwoStateTransfer_r213.lean` §4 (at junction
weight 1 only the multiset of site weights survives).

## SCOPE — plainly

**This file is a DEFINITION plus a structural theorem.**

It proves nothing about the Riemann Hypothesis, BSD, P vs NP, Yang–Mills,
Navier–Stokes, or any Millennium problem.  It does not, by itself, produce a
continuous spectrum, and it produces no new α-value.  What it does is REMOVE A
STRUCTURAL OBSTRUCTION: as long as the digit weight is a scalar, the transfer
operator of the digit system is a `1 × 1` matrix, its spectrum is a single
point, and no amount of analysis downstream can make it anything else.  With a
matrix weight the operator can have a nontrivial spectrum.  Whether it does,
for any weight of interest, is not decided here and is not claimed here.

Nothing below should be cited as evidence for any claim about computation,
complexity classes, or physics.

## Choice of setting, and why

§1–§2 are stated over an arbitrary `Semiring R` (associativity plus
distributivity is all the induction uses).  Nothing is gained by fixing
matrices there, and two things are lost: the scalar case would stop being a
literal instantiation (it would need a `1 × 1` embedding and an extraction),
and the Gelfand step of §6 would need a norm on matrices, which mathlib only
supplies through scoped instances.  So:

* `R` arbitrary semiring — §1, §2, §5.
* `R = ℂ` — the r212 recovery (§3a).  This is a genuine instantiation, not an
  analogy: r212's identity is `sum_wordWeight` with `R = ℂ`.
* `R` an arbitrary `ℂ`-algebra — the scalar sub-system `ω^d • 1` (§3b).  This
  covers `Matrix (Fin m) (Fin m) ℂ` for every `m`, so "r212 is the `1 × 1`
  shadow" is a statement about every `m` at once.
* `R = Matrix (Fin 2) (Fin 2) ℂ` — the order-sensitivity witness (§4), where a
  concrete non-commuting pair is needed.
* `R` a complex Banach algebra — the spectral-radius statement (§6).

Every theorem whose statement the request specified in terms of
`Matrix (Fin m) (Fin m) ℂ` typechecks unchanged at that instance, and §3b/§4
are stated there directly.

## Order convention

`wordWeight M d = M (d 0) * M (d 1) * ⋯ * M (d (k-1))`: index order, left to
right, LEAST significant digit first.  This is `Nat.digits`' own little-endian
order, which is what makes §5 go through with no reversal.  It is fixed once
here and never varied.

## Cross-reference

`codex/FRAMEWORK_TRANSLATION_2026-08-06.md` §3 ("THE BRIDGE — already in the
manuscript, unnamed"), which is where this stone was specified, and
`codex/STEELMAN_2026-08-06.md`.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Axiom audit at the end of the file.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import PF.SigmaAbscissa_r212

namespace PrincipiaTractalis.DigitWordSystem

open scoped BigOperators

/-! ## §0  Reindexing digit tuples

`Fin k → Fin 3` is the type of base-3 digit tuples of length `k`, with LEADING
ZEROS RETAINED.  This is the whole reason we do not index by `Nat.digits`:
`Nat.digits 3` drops leading zeros, so it is not a bijection onto tuples of a
fixed length, and the count in §2 would be wrong.  §5 reconnects the two.
-/

/-- Splitting a digit tuple into (least significant digit, the rest). -/
def consEquiv (k : ℕ) : Fin 3 × (Fin k → Fin 3) ≃ (Fin (k + 1) → Fin 3) where
  toFun p := Fin.cons p.1 p.2
  invFun d := (d 0, Fin.tail d)
  left_inv p := by simp
  right_inv d := Fin.cons_self_tail d

/-- Sum over digit tuples of length `k+1`, split on the least significant
digit. -/
lemma sum_tuple_succ {M : Type*} [AddCommMonoid M] {k : ℕ}
    (F : (Fin (k + 1) → Fin 3) → M) :
    (∑ d : Fin (k + 1) → Fin 3, F d) =
      ∑ a : Fin 3, ∑ t : Fin k → Fin 3, F (Fin.cons a t) := by
  have h := Fintype.sum_equiv (consEquiv k)
      (fun p : Fin 3 × (Fin k → Fin 3) => F (Fin.cons p.1 p.2)) F (fun _ => rfl)
  rw [← h, Fintype.sum_prod_type]

/-- Splitting `range (N * b)` into `N` consecutive blocks of length `b`.
(Used in §5.  This is the same elementary split r212 uses; it is `private`
there, so it is reproved here rather than imported.) -/
private lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (b : ℕ) (f : ℕ → M) :
    ∀ N : ℕ, ∑ n ∈ Finset.range (N * b), f n
      = ∑ m ∈ Finset.range N, ∑ d ∈ Finset.range b, f (m * b + d) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have h : (N + 1) * b = N * b + b := by ring
      rw [h, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-! ## §1  Digit tuples and the word weight

`M : Fin 3 → R` assigns to each base-3 digit an element of `R`.  `wordWeight`
takes the ORDERED product along the tuple.  When `R` is non-commutative this
depends on the order of the digits, not only on how many of each there are —
that is the entire content of the promotion, and §4 is the witness.
-/

section Word

variable {R : Type*} [Monoid R]

/-- **The word weight.**  The ordered product `M (d 0) * M (d 1) * ⋯ *
M (d (k-1))` of the digit weights along the tuple `d`, least significant digit
first. -/
def wordWeight (M : Fin 3 → R) {k : ℕ} (d : Fin k → Fin 3) : R :=
  (List.ofFn fun i => M (d i)).prod

@[simp] lemma wordWeight_nil (M : Fin 3 → R) (d : Fin 0 → Fin 3) :
    wordWeight M d = 1 := by
  simp [wordWeight]

/-- Peel the least significant digit off the left of the product. -/
lemma wordWeight_succ (M : Fin 3 → R) {k : ℕ} (d : Fin (k + 1) → Fin 3) :
    wordWeight M d = M (d 0) * wordWeight M (Fin.tail d) := by
  simp [wordWeight, List.ofFn_succ, Fin.tail]

@[simp] lemma wordWeight_cons (M : Fin 3 → R) {k : ℕ} (a : Fin 3) (d : Fin k → Fin 3) :
    wordWeight M (Fin.cons a d) = M a * wordWeight M d := by
  rw [wordWeight_succ]
  simp

/-- Peel the MOST significant digit off the right of the product.  This is the
form §5 needs: appending a leading zero is a `Fin.snoc`. -/
lemma wordWeight_snoc (M : Fin 3 → R) {k : ℕ} (d : Fin k → Fin 3) (a : Fin 3) :
    wordWeight M (Fin.snoc d a) = wordWeight M d * M a := by
  rw [wordWeight, wordWeight, List.ofFn_succ']
  simp [List.concat_eq_append, List.prod_append]

/-- Two-digit words, spelled out.  Used by §4. -/
lemma wordWeight_pair (M : Fin 3 → R) (a b : Fin 3) :
    wordWeight M ![a, b] = M a * M b := by
  simp [wordWeight, List.ofFn_succ]

/-- In a COMMUTATIVE monoid the ordered product collapses to the unordered
one — the order of the digits becomes invisible.  This single lemma is why
programme (A) can never see more than the digit multiset. -/
lemma wordWeight_eq_prod {S : Type*} [CommMonoid S] (M : Fin 3 → S) {k : ℕ}
    (d : Fin k → Fin 3) : wordWeight M d = ∏ i, M (d i) :=
  List.prod_ofFn

end Word

/-! ## §2  THE MATRIX DIGIT-BLOCK IDENTITY

The exact generalization of the scalar identity

    Σ_{n < 3^k} ω^{D₃(n)} = (1 + ω + ω²)^k

that `r212` and `r214` rest on.  The scalar `1 + ω + ω²` becomes the element
`χ = M 0 + M 1 + M 2`, and the `k`-th power is a genuine `k`-fold product of a
possibly non-commuting element.
-/

section Block

variable {R : Type*} [Semiring R]

/-- `χ = M 0 + M 1 + M 2` — the one-step transfer element of the digit system.
In the scalar case this is `1 + ω + ω²` (see `chi_scalar`). -/
def chi (M : Fin 3 → R) : R := M 0 + M 1 + M 2

lemma chi_eq_sum (M : Fin 3 → R) : chi M = ∑ a : Fin 3, M a := by
  rw [Fin.sum_univ_three]; rfl

/-- **THE MATRIX DIGIT-BLOCK IDENTITY (§2).**  The sum of the ordered word
weights over ALL `3^k` base-3 digit tuples of length `k` — leading zeros
retained — is the `k`-th power of `χ = M 0 + M 1 + M 2`.

For `R = ℂ` and `M d = ω^d` this is exactly r212's `digitBlock_sum`.  For `R`
a matrix ring it is the transfer-operator form: the block sum is a power of one
fixed operator, so the growth of the block sums is governed by the SPECTRUM of
that operator rather than by a single number (§6). -/
theorem sum_wordWeight (M : Fin 3 → R) (k : ℕ) :
    ∑ d : Fin k → Fin 3, wordWeight M d = chi M ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [sum_tuple_succ, pow_succ', ← ih, chi_eq_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => wordWeight_cons M a t

/-- The statement of §2 at the setting the request names: `m × m` complex
matrices, `m` arbitrary.  This is `sum_wordWeight` instantiated, not a new
theorem; it is restated so the matrix form is quotable on its own. -/
theorem sum_wordWeight_matrix {m : ℕ} (M : Fin 3 → Matrix (Fin m) (Fin m) ℂ) (k : ℕ) :
    ∑ d : Fin k → Fin 3, wordWeight M d = (M 0 + M 1 + M 2) ^ k :=
  sum_wordWeight M k

end Block

/-! ## §3  THE SCALAR SPECIALIZATION — r212 is the `1 × 1` shadow

### §3a  `R = ℂ`: r212's identity, verbatim, as an instantiation

`digitSum d = ∑ i, (d i : ℕ)` IS the base-3 digit sum `D₃` of the number whose
digit tuple is `d`.  It depends only on the MULTISET of digits: permuting `d`
does not change it (`digitSum_perm`).  So the scalar digit character sees only
composition-determined data — which is exactly why r212 reaches only the three
RATIONAL α-values of the framework's table of nine, and provably misses all six
irrational ones (r212 §7).  The same fact in another domain is
`PF/TwoStateTransfer_r213.lean` §4.
-/

/-- The base-3 digit sum of a digit tuple: `D₃`. -/
def digitSum {k : ℕ} (d : Fin k → Fin 3) : ℕ := ∑ i, (d i : ℕ)

/-- **`digitSum` is order-blind.**  Permuting the digit positions leaves it
unchanged: it is a function of the digit MULTISET alone.  This is the precise
statement of the limitation §4 then shows the matrix system escapes. -/
theorem digitSum_perm {k : ℕ} (d : Fin k → Fin 3) (σ : Equiv.Perm (Fin k)) :
    digitSum (d ∘ σ) = digitSum d :=
  Fintype.sum_equiv σ _ _ fun _ => rfl

/-- The scalar digit weight of r212, as a weight family: `d ↦ ω^d`. -/
def scalarWeightsC (ω : ℂ) : Fin 3 → ℂ := fun d => ω ^ (d : ℕ)

@[simp] lemma scalarWeightsC_apply (ω : ℂ) (d : Fin 3) :
    scalarWeightsC ω d = ω ^ (d : ℕ) := rfl

/-- The word weight of the scalar system is `ω` to the DIGIT SUM. -/
theorem wordWeight_scalarC (ω : ℂ) {k : ℕ} (d : Fin k → Fin 3) :
    wordWeight (scalarWeightsC ω) d = ω ^ digitSum d := by
  rw [wordWeight_eq_prod, digitSum]
  exact Finset.prod_pow_eq_pow_sum _ _ _

@[simp] lemma chi_scalarC (ω : ℂ) : chi (scalarWeightsC ω) = 1 + ω + ω ^ 2 := by
  simp [chi, scalarWeightsC]

/-- **r212's digit-block identity, in tuple form.**  This is `sum_wordWeight`
with `R = ℂ` — a literal instantiation of §2, not an analogue of it. -/
theorem sum_pow_digitSum (ω : ℂ) (k : ℕ) :
    ∑ d : Fin k → Fin 3, ω ^ digitSum d = (1 + ω + ω ^ 2) ^ k := by
  have h := sum_wordWeight (scalarWeightsC ω) k
  rw [chi_scalarC] at h
  rw [← h]
  exact Finset.sum_congr rfl fun d _ => (wordWeight_scalarC ω d).symm

/-- The tuple-indexed block sum and r212's `Nat.digits`-indexed block sum are
the same number.  (Both are `(1 + ω + ω²)^k`; this records the identification
explicitly rather than leaving it to the reader.) -/
theorem digitBlock_sum_tuple_eq_range (ω : ℂ) (k : ℕ) :
    (∑ d : Fin k → Fin 3, ω ^ digitSum d)
      = ∑ n ∈ Finset.range (3 ^ k), ω ^ ((Nat.digits 3 n).sum) := by
  rw [sum_pow_digitSum, PrincipiaTractalis.SigmaAbscissa.digitBlock_sum]

/-! ### §3b  The scalar sub-system inside any `ℂ`-algebra

`M d = ω^d • 1` is the scalar digit character embedded in `R`.  Its word
weights are scalar multiples of `1`, its `χ` is `(1 + ω + ω²) • 1`, and the
whole system is r212's up to that embedding.  Specialized to
`R = Matrix (Fin m) (Fin m) ℂ` these are the statements the request names.
-/

section Scalar

variable {R : Type*} [Semiring R] [Algebra ℂ R]

/-- The scalar digit weight embedded in `R`: `M d = ω^d • 1`. -/
def scalarWeights (ω : ℂ) : Fin 3 → R := fun d => (ω ^ (d : ℕ)) • (1 : R)

@[simp] lemma scalarWeights_apply (ω : ℂ) (d : Fin 3) :
    (scalarWeights ω : Fin 3 → R) d = (ω ^ (d : ℕ)) • (1 : R) := rfl

/-- **The scalar system's word weight is `ω^{D₃}` times the identity.**

`digitSum d = ∑ i, (d i : ℕ)` is the base-3 DIGIT SUM.  So in the scalar case
the word weight sees only the digit sum — hence only the MULTISET of digits,
never their order.  That is exactly why r212 reaches only composition-determined
data, and it is what §4 shows the matrix system is not bound by. -/
theorem wordWeight_scalar (ω : ℂ) {k : ℕ} (d : Fin k → Fin 3) :
    wordWeight (scalarWeights ω : Fin 3 → R) d = (ω ^ digitSum d) • (1 : R) := by
  induction k with
  | zero => simp [digitSum]
  | succ n ih =>
      rw [wordWeight_succ, ih (Fin.tail d), scalarWeights_apply, smul_mul_smul_comm,
        one_mul, ← pow_add]
      congr 1
      rw [digitSum, digitSum, Fin.sum_univ_succ]
      rfl

/-- **`χ = (1 + ω + ω²) • 1` in the scalar system.**  The one-step transfer
element of programme (A) is a SCALAR multiple of the identity — its spectrum is
a single point, whatever `R` is.  That is the structural obstruction this stone
removes. -/
@[simp] theorem chi_scalar (ω : ℂ) :
    chi (scalarWeights ω : Fin 3 → R) = (1 + ω + ω ^ 2) • (1 : R) := by
  simp only [chi, scalarWeights_apply]
  rw [← add_smul, ← add_smul]
  norm_num

/-- The scalar block identity as a consequence of §2. -/
theorem sum_wordWeight_scalar (ω : ℂ) (k : ℕ) :
    ∑ d : Fin k → Fin 3, (ω ^ digitSum d) • (1 : R) = ((1 + ω + ω ^ 2) ^ k) • (1 : R) := by
  have h := sum_wordWeight (scalarWeights ω : Fin 3 → R) k
  rw [chi_scalar, smul_pow, one_pow] at h
  rw [← h]
  exact Finset.sum_congr rfl fun d _ => (wordWeight_scalar ω d).symm

end Scalar

/-- §3b at the setting the request names: `m × m` complex matrices. -/
theorem chi_scalar_matrix {m : ℕ} (ω : ℂ) :
    chi (scalarWeights ω : Fin 3 → Matrix (Fin m) (Fin m) ℂ)
      = (1 + ω + ω ^ 2) • (1 : Matrix (Fin m) (Fin m) ℂ) :=
  chi_scalar ω

/-- §3b at the setting the request names: `m × m` complex matrices. -/
theorem wordWeight_scalar_matrix {m k : ℕ} (ω : ℂ) (d : Fin k → Fin 3) :
    wordWeight (scalarWeights ω : Fin 3 → Matrix (Fin m) (Fin m) ℂ) d
      = (ω ^ digitSum d) • (1 : Matrix (Fin m) (Fin m) ℂ) :=
  wordWeight_scalar ω d

/-! ## §4  ORDER-SENSITIVITY — the sharpness witness

Same digit multiset, different order, different weight.

The two weights are the standard `SL₂(ℤ)` generators

    M 1 = !![1,1;0,1] = T ,      M 2 = !![1,0;1,1] = Tᵀ ,

with `M 0 = 1`.  These are the continuant matrices of the continued-fraction /
Gauss-map arc (`PF/GaussLevelTwo_r210.lean`, `PF/GaussLevelThree_r211.lean`,
and the Mayer transfer-operator arc r188/r190): the product of continuant
matrices along a word IS the convergent of the corresponding continued
fraction, and it is order-sensitive for exactly the reason below.

    M 1 * M 2 = !![2,1;1,1] ,      M 2 * M 1 = !![1,1;1,2] .

As little-endian digit tuples (least significant digit first, the convention of
§1 and of `Nat.digits`), `![1,2]` is the number `1 + 2·3 = 7 = 21₃` and
`![2,1]` is `2 + 1·3 = 5 = 12₃`.  (Read big-endian they are 5 and 7; either
way it is the pair {5, 7}.)  Both have digit sum `D₃ = 3`.

**So no scalar digit weight can separate 5 from 7, and this system does.**
That is the whole point of the promotion, in one example.
-/

/-- The witness weights: `1`, and the two `SL₂(ℤ)` generators. -/
def witnessWeights : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, !![1, 1; 0, 1], !![1, 0; 1, 1]]

@[simp] lemma witnessWeights_zero : witnessWeights 0 = 1 := rfl
@[simp] lemma witnessWeights_one : witnessWeights 1 = !![1, 1; 0, 1] := rfl
@[simp] lemma witnessWeights_two : witnessWeights 2 = !![1, 0; 1, 1] := rfl

lemma witness_prod_12 :
    witnessWeights 1 * witnessWeights 2 = !![2, 1; 1, 1] := by
  rw [witnessWeights_one, witnessWeights_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

lemma witness_prod_21 :
    witnessWeights 2 * witnessWeights 1 = !![1, 1; 1, 2] := by
  rw [witnessWeights_one, witnessWeights_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- **THE SHARPNESS WITNESS (§4).**  Two base-3 digit tuples with the SAME
digit multiset have DIFFERENT word weights.  The ordered product genuinely sees
the order of the digits. -/
theorem wordWeight_order_sensitive :
    wordWeight witnessWeights ![1, 2] ≠ wordWeight witnessWeights ![2, 1] := by
  rw [wordWeight_pair, wordWeight_pair, witness_prod_12, witness_prod_21]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp at h00

/-- **The other half of the witness.**  The scalar digit system CANNOT separate
those two tuples: their digit sums are equal (both `3`).  So the separation in
`wordWeight_order_sensitive` is unavailable to every scalar digit weight
whatsoever, `ω^{D₃}` included. -/
theorem digitSum_order_blind :
    (∑ i, ((![1, 2] : Fin 2 → Fin 3) i : ℕ)) = (∑ i, ((![2, 1] : Fin 2 → Fin 3) i : ℕ)) := by
  simp [Fin.sum_univ_two]

/-- Both tuples have digit sum `3`: these are the base-3 digit tuples of `5`
and `7`. -/
theorem digitSum_witness_eq_three :
    digitSum (![1, 2] : Fin 2 → Fin 3) = 3 ∧ digitSum (![2, 1] : Fin 2 → Fin 3) = 3 := by
  constructor <;> · rw [digitSum]; simp [Fin.sum_univ_two]

/-- The two statements together, as the separation they are: every scalar digit
weight assigns these two tuples the SAME value, and the matrix system does
not. -/
theorem scalar_cannot_separate_but_matrix_can (ω : ℂ) :
    wordWeight (scalarWeightsC ω) ![1, 2] = wordWeight (scalarWeightsC ω) ![2, 1] ∧
      wordWeight witnessWeights ![1, 2] ≠ wordWeight witnessWeights ![2, 1] := by
  refine ⟨?_, wordWeight_order_sensitive⟩
  rw [wordWeight_scalarC, wordWeight_scalarC, digitSum_witness_eq_three.1,
    digitSum_witness_eq_three.2]

/-! ## §5  `M 0 = 1` recovers the `Nat.digits` picture

`Nat.digits 3 n` drops leading zeros, so it does not index tuples of a fixed
length.  §2 therefore had to be stated over `Fin k → Fin 3`.  This section
reconnects the two, and shows exactly what the hypothesis `M 0 = 1` buys:
padding with leading zeros becomes free, so the word weight of a NUMBER is
well defined independently of how many digits one chooses to write.

In the scalar case `M 0 = ω^0 = 1` holds automatically — which is precisely
why r212 and r214 never needed a padding argument.
-/

/-- The length-`k` base-3 digit tuple of `n`, little-endian, leading zeros
retained. -/
def digitTuple (n k : ℕ) : Fin k → Fin 3 :=
  fun i => ⟨n / 3 ^ (i : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The digits of `digitTuple` really are the digits of `Nat.digits 3`. -/
lemma div_pow_mod_eq_getD : ∀ (i n : ℕ), n / 3 ^ i % 3 = (Nat.digits 3 n).getD i 0 := by
  intro i
  induction i with
  | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 3) hn]
        simp
  | succ j ih =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 3) hn, List.getD_cons_succ, ← ih (n / 3),
          pow_succ', Nat.div_div_eq_div_mul]

/-- **The `Nat.digits` bridge, entrywise.**  The `i`-th entry of `digitTuple n k`
is the `i`-th base-3 digit of `n` in mathlib's sense, with `0` past the end. -/
theorem digitTuple_val (n k : ℕ) (i : Fin k) :
    ((digitTuple n k i : Fin 3) : ℕ) = (Nat.digits 3 n).getD (i : ℕ) 0 :=
  div_pow_mod_eq_getD (i : ℕ) n

/-- Peeling the least significant digit of `n`. -/
lemma digitTuple_cons (m : ℕ) (a : Fin 3) (k : ℕ) :
    digitTuple (m * 3 + (a : ℕ)) (k + 1) = Fin.cons a (digitTuple m k) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · have ha := a.isLt
    apply Fin.ext
    simp only [digitTuple, Fin.cons_zero, Fin.val_zero, pow_zero, Nat.div_one]
    omega
  · intro j
    have ha := a.isLt
    have hdiv : (m * 3 + (a : ℕ)) / 3 = m := by omega
    apply Fin.ext
    simp only [digitTuple, Fin.cons_succ, Fin.val_succ]
    rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]

/-- **PADDING INVARIANCE (§5).**  If `M 0 = 1`, appending a LEADING ZERO to a
digit tuple does not change its word weight.  (`Fin.snoc` appends at the most
significant end, which is the leading end in the little-endian convention of
§1.) -/
theorem wordWeight_pad {R : Type*} [Monoid R] (M : Fin 3 → R) (h0 : M 0 = 1)
    {k : ℕ} (d : Fin k → Fin 3) :
    wordWeight M (Fin.snoc d 0) = wordWeight M d := by
  rw [wordWeight_snoc, h0, mul_one]

section Digits

variable {R : Type*} [Semiring R]

/-- **The `n < 3^k` form of §2.**  Summing the word weight over the first `3^k`
NATURAL NUMBERS, each written with exactly `k` base-3 digits, gives `χ^k`.

Note this needs no hypothesis on `M`: with a fixed digit length `k` the
leading zeros are genuinely there and are genuinely weighted by `M 0`.  It is
the comparison ACROSS lengths that needs `M 0 = 1` (`wordWeight_pad`,
`digitTuple_stable`). -/
theorem sum_range_wordWeight (M : Fin 3 → R) (k : ℕ) :
    ∑ n ∈ Finset.range (3 ^ k), wordWeight M (digitTuple n k) = chi M ^ k := by
  induction k with
  | zero => simp
  | succ j ih =>
      have hpow : (3 : ℕ) ^ (j + 1) = 3 ^ j * 3 := by ring
      rw [hpow, sum_range_mul_split 3 (fun n => wordWeight M (digitTuple n (j + 1))) (3 ^ j)]
      have step : ∀ m ∈ Finset.range (3 ^ j),
          ∑ d ∈ Finset.range 3, wordWeight M (digitTuple (m * 3 + d) (j + 1))
            = chi M * wordWeight M (digitTuple m j) := by
        intro m _
        rw [← Fin.sum_univ_eq_sum_range
          (fun d => wordWeight M (digitTuple (m * 3 + d) (j + 1))) 3]
        have hterm : ∀ a : Fin 3,
            wordWeight M (digitTuple (m * 3 + (a : ℕ)) (j + 1))
              = M a * wordWeight M (digitTuple m j) := by
          intro a; rw [digitTuple_cons, wordWeight_cons]
        rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.sum_mul, ← chi_eq_sum]
      rw [Finset.sum_congr rfl step, ← Finset.mul_sum, ih, pow_succ']

/-- The two forms of the block sum — over digit TUPLES and over the NUMBERS
`n < 3^k` — agree.  This is the `Nat.digits`-side statement of §2. -/
theorem sum_range_eq_sum_tuple (M : Fin 3 → R) (k : ℕ) :
    ∑ n ∈ Finset.range (3 ^ k), wordWeight M (digitTuple n k)
      = ∑ d : Fin k → Fin 3, wordWeight M d := by
  rw [sum_range_wordWeight, sum_wordWeight]

end Digits

section Stable

variable {R : Type*} [Monoid R]

/-- Writing `n < 3^k` with one extra digit appends a leading zero. -/
lemma digitTuple_succ_of_lt {n k : ℕ} (hn : n < 3 ^ k) :
    digitTuple n (k + 1) = Fin.snoc (digitTuple n k) 0 := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · apply Fin.ext
    rw [Fin.snoc_last]
    simp only [digitTuple, Fin.val_last]
    rw [Nat.div_eq_of_lt hn]
    rfl
  · intro j
    apply Fin.ext
    rw [Fin.snoc_castSucc]
    simp [digitTuple]

/-- **PADDING STABILITY (§5).**  With `M 0 = 1` the word weight of a number does
not depend on how many digits it is written with. -/
theorem digitTuple_stable (M : Fin 3 → R) (h0 : M 0 = 1) {n k : ℕ} (hn : n < 3 ^ k) :
    wordWeight M (digitTuple n (k + 1)) = wordWeight M (digitTuple n k) := by
  rw [digitTuple_succ_of_lt hn, wordWeight_pad M h0]

/-- **The word weight of a NATURAL NUMBER.**  Written with exactly as many
base-3 digits as `Nat.digits 3` gives it — no padding. -/
def natWeight (M : Fin 3 → R) (n : ℕ) : R :=
  wordWeight M (digitTuple n (Nat.digits 3 n).length)

/-- **THE `Nat.digits` BRIDGE (§5).**  If `M 0 = 1` then for EVERY digit length
`k` at least the true length, the padded word weight equals `natWeight M n`.
So `natWeight` is the canonical value and `digitTuple`-indexing at any
sufficient length computes it. -/
theorem wordWeight_digitTuple_eq_natWeight (M : Fin 3 → R) (h0 : M 0 = 1) (n : ℕ) :
    ∀ k : ℕ, (Nat.digits 3 n).length ≤ k → wordWeight M (digitTuple n k) = natWeight M n := by
  intro k
  induction k with
  | zero =>
      intro hk
      have : (Nat.digits 3 n).length = 0 := Nat.le_zero.mp hk
      rw [natWeight, this]
  | succ j ih =>
      intro hk
      rcases Nat.lt_or_ge j (Nat.digits 3 n).length with hj | hj
      · have : (Nat.digits 3 n).length = j + 1 := by omega
        rw [natWeight, this]
      · have hn : n < 3 ^ j :=
          lt_of_lt_of_le (Nat.lt_base_pow_length_digits (by norm_num : (1:ℕ) < 3))
            (Nat.pow_le_pow_right (by norm_num) hj)
        rw [digitTuple_stable M h0 hn, ih hj]

/-- `M` read on `ℕ`.  Every digit produced by `Nat.digits 3` is `< 3`; the
value at `x ≥ 3` is `1` and is never used. -/
def natRead (M : Fin 3 → R) (x : ℕ) : R := if h : x < 3 then M ⟨x, h⟩ else 1

lemma natRead_of_lt (M : Fin 3 → R) {x : ℕ} (h : x < 3) : natRead M x = M ⟨x, h⟩ := by
  rw [natRead, dif_pos h]

/-- **`natWeight` really is the ordered product of `M` over the base-3 digits of
`n`**, in `Nat.digits`' own little-endian order.  This is the full
`Nat.digits` bridge: with no hypothesis at all, the tuple-indexed word weight
at the true digit length is the product along `Nat.digits 3 n`; with `M 0 = 1`
(`wordWeight_digitTuple_eq_natWeight`) every padded length computes it too. -/
theorem natWeight_eq_digits_prod (M : Fin 3 → R) (n : ℕ) :
    natWeight M n = ((Nat.digits 3 n).map (natRead M)).prod := by
  rw [natWeight, wordWeight]
  congr 1
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  have hlen : i < (Nat.digits 3 n).length := by simpa using h2
  have hval : ((digitTuple n (Nat.digits 3 n).length ⟨i, hlen⟩ : Fin 3) : ℕ)
      = (Nat.digits 3 n)[i] := by
    rw [digitTuple_val]
    exact List.getD_eq_getElem _ 0 hlen
  have hlt : (Nat.digits 3 n)[i] < 3 := by
    rw [← hval]; exact (digitTuple n (Nat.digits 3 n).length ⟨i, hlen⟩).isLt
  simp only [List.getElem_ofFn, List.getElem_map]
  rw [natRead_of_lt M hlt]
  congr 1
  exact Fin.ext hval

end Stable

/-! ## §6  (P2) The abscissa becomes a spectral radius

§2 says the block sum of length `k` IS `χ^k`.  Gelfand's formula then says the
growth exponent of the block sums is the SPECTRAL RADIUS of `χ` — not a single
number read off a scalar, but the radius of a genuine spectrum.

In the scalar case `χ = (1 + ω + ω²) • 1` has spectrum the single point
`1 + ω + ω²`, so its spectral radius is `‖1 + ω + ω²‖`, and at `ω = e^{iπα}`
that is `|1 + 2 cos πα|` (r212 §2) — whose `log₃` is r212's `σ(α)`.
**So "r212 is the `1 × 1` case" is a theorem here, not a remark.**

What is NOT claimed: that any particular matrix weight has a spectral radius
different from the scalar one, still less that any of them is relevant to any
Millennium problem.  §6 says only that the growth exponent is now a spectral
quantity and therefore CAN be more than a point.
-/

section Spectral

open Filter Topology ENNReal

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **GELFAND FOR THE DIGIT SYSTEM (§6).**  The `k`-th root of the norm of the
length-`k` block sum converges to the spectral radius of `χ`.  Immediate from
§2 and mathlib's Gelfand formula — the content is that §2 makes the block sum
literally a power. -/
theorem tendsto_blockSum_spectralRadius (M : Fin 3 → A) :
    Tendsto (fun k : ℕ => ((‖∑ d : Fin k → Fin 3, wordWeight M d‖₊ : ℝ≥0∞)) ^ (1 / k : ℝ))
      atTop (𝓝 (spectralRadius ℂ (chi M))) := by
  have h : (fun k : ℕ => ((‖∑ d : Fin k → Fin 3, wordWeight M d‖₊ : ℝ≥0∞)) ^ (1 / k : ℝ))
      = fun k : ℕ => ((‖chi M ^ k‖₊ : ℝ≥0∞)) ^ (1 / k : ℝ) := by
    funext k; rw [sum_wordWeight]
  rw [h]
  exact spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (chi M)

end Spectral

/-- The spectrum of a complex number, viewed in the `ℂ`-algebra `ℂ`, is that
number. -/
lemma spectrum_complex_self (z : ℂ) : spectrum ℂ z = {z} := by
  ext x
  simp [spectrum.mem_iff, Algebra.algebraMap_self, sub_eq_zero, isUnit_iff_ne_zero]

/-- The spectral radius of a complex number is its norm. -/
lemma spectralRadius_complex (z : ℂ) : spectralRadius ℂ z = (‖z‖₊ : ENNReal) := by
  rw [spectralRadius, spectrum_complex_self]
  simp

/-- **THE `1 × 1` CASE IS r212 (§6).**  The spectral radius of the scalar
digit system's `χ` is `‖1 + ω + ω²‖`.  Compare r212's
`norm_one_add_exp_add_exp_sq`: at `ω = e^{iθ}` this is `|1 + 2 cos θ|`, and
r212's `σ(α)` is its `log₃`. -/
theorem spectralRadius_chi_scalarC (ω : ℂ) :
    spectralRadius ℂ (chi (scalarWeightsC ω)) = (‖1 + ω + ω ^ 2‖₊ : ENNReal) := by
  rw [chi_scalarC, spectralRadius_complex]

/-- At `ω = e^{iθ}` the spectral radius of the scalar `χ` is `|1 + 2 cos θ|` —
r212 §2 (`norm_one_add_exp_add_exp_sq`), now read as a spectral quantity. -/
theorem spectralRadius_chi_exp_toReal (θ : ℝ) :
    (spectralRadius ℂ (chi (scalarWeightsC (Complex.exp ((θ : ℂ) * Complex.I))))).toReal
      = |1 + 2 * Real.cos θ| := by
  rw [spectralRadius_chi_scalarC, ENNReal.coe_toReal, coe_nnnorm]
  exact PrincipiaTractalis.SigmaAbscissa.norm_one_add_exp_add_exp_sq θ

/-- **THE STATEMENT THE STONE EXISTS TO MAKE.**  r212's abscissa `σ(α)` IS the
`log₃` of the spectral radius of the digit system's transfer element `χ`, in
the scalar (`1 × 1`) case.  Everything r212 computes about `σ` is therefore a
computation about a spectrum consisting of a single point; §2 is what allows
that point to be replaced by an operator spectrum. -/
theorem sigma_eq_logb_spectralRadius (α : ℝ) :
    PrincipiaTractalis.SigmaAbscissa.sigma α
      = Real.logb 3 (spectralRadius ℂ (chi (scalarWeightsC
          (Complex.exp (((Real.pi * α : ℝ) : ℂ) * Complex.I))))).toReal := by
  rw [spectralRadius_chi_exp_toReal]
  rfl

/-! ## Axiom audit

House rule: an axiom claim that `lake env lean` does not re-run is not a
verified claim.  Every main theorem of this file is listed below.  All must
report only `[propext, Classical.choice, Quot.sound]`. -/

-- §0 reindexing
#print axioms PrincipiaTractalis.DigitWordSystem.sum_tuple_succ

-- §1 the word weight
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_nil
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_succ
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_cons
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_snoc
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_pair
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_eq_prod

-- §2 THE MATRIX DIGIT-BLOCK IDENTITY
#print axioms PrincipiaTractalis.DigitWordSystem.chi_eq_sum
#print axioms PrincipiaTractalis.DigitWordSystem.sum_wordWeight
#print axioms PrincipiaTractalis.DigitWordSystem.sum_wordWeight_matrix

-- §3a the scalar specialization over ℂ (r212)
#print axioms PrincipiaTractalis.DigitWordSystem.digitSum_perm
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_scalarC
#print axioms PrincipiaTractalis.DigitWordSystem.chi_scalarC
#print axioms PrincipiaTractalis.DigitWordSystem.sum_pow_digitSum
#print axioms PrincipiaTractalis.DigitWordSystem.digitBlock_sum_tuple_eq_range

-- §3b the scalar sub-system in a ℂ-algebra, and its matrix instance
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_scalar
#print axioms PrincipiaTractalis.DigitWordSystem.chi_scalar
#print axioms PrincipiaTractalis.DigitWordSystem.sum_wordWeight_scalar
#print axioms PrincipiaTractalis.DigitWordSystem.chi_scalar_matrix
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_scalar_matrix

-- §4 ORDER-SENSITIVITY: the sharpness witness
#print axioms PrincipiaTractalis.DigitWordSystem.witness_prod_12
#print axioms PrincipiaTractalis.DigitWordSystem.witness_prod_21
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_order_sensitive
#print axioms PrincipiaTractalis.DigitWordSystem.digitSum_order_blind
#print axioms PrincipiaTractalis.DigitWordSystem.digitSum_witness_eq_three
#print axioms PrincipiaTractalis.DigitWordSystem.scalar_cannot_separate_but_matrix_can

-- §5 the Nat.digits picture
#print axioms PrincipiaTractalis.DigitWordSystem.div_pow_mod_eq_getD
#print axioms PrincipiaTractalis.DigitWordSystem.digitTuple_val
#print axioms PrincipiaTractalis.DigitWordSystem.digitTuple_cons
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_pad
#print axioms PrincipiaTractalis.DigitWordSystem.sum_range_wordWeight
#print axioms PrincipiaTractalis.DigitWordSystem.sum_range_eq_sum_tuple
#print axioms PrincipiaTractalis.DigitWordSystem.digitTuple_succ_of_lt
#print axioms PrincipiaTractalis.DigitWordSystem.digitTuple_stable
#print axioms PrincipiaTractalis.DigitWordSystem.wordWeight_digitTuple_eq_natWeight
#print axioms PrincipiaTractalis.DigitWordSystem.natRead_of_lt
#print axioms PrincipiaTractalis.DigitWordSystem.natWeight_eq_digits_prod

-- §6 the spectral-radius form
#print axioms PrincipiaTractalis.DigitWordSystem.tendsto_blockSum_spectralRadius
#print axioms PrincipiaTractalis.DigitWordSystem.spectrum_complex_self
#print axioms PrincipiaTractalis.DigitWordSystem.spectralRadius_complex
#print axioms PrincipiaTractalis.DigitWordSystem.spectralRadius_chi_scalarC
#print axioms PrincipiaTractalis.DigitWordSystem.spectralRadius_chi_exp_toReal
#print axioms PrincipiaTractalis.DigitWordSystem.sigma_eq_logb_spectralRadius

end PrincipiaTractalis.DigitWordSystem
