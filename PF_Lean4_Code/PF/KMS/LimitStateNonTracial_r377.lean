/-
# r377: the level states are TOWER-COMPATIBLE, and non-tracial — gate (A)'s
remaining half

★ 2026-10-29 r377 — the `Tr(xₖ)` cancellation, and an explicit non-traciality
witness ★

## The computation this file is about

A family of level states defines a state on `T_∞` only if it is compatible with
the embeddings, `ω_{k+1}(ι a) = ω_k(a)`. For the product-type family of
r370–r371 it is, and the reason is a cancellation:

    X_{k+1} = reindex (X_k ⊗ₖ x_k)        (r370's `embed_mul_newFactor`)

    Tr(X_{k+1} · ι a) = Tr(X_k a) · Tr(x_k)
    Tr(X_{k+1})       = Tr(X_k)   · Tr(x_k)

so the new factor's trace **cancels between numerator and denominator** and the
normalisation is preserved exactly. The hypothesis it needs is `Tr(x_k) ≠ 0`,
which positive-definiteness supplies (r371).

This is the same shape as the corpus's own `substrateEmbedMatrix_normalized_trace`
(r87.b), which is the `x_k = 1` case: there the factor is `3` and it cancels
against `3^{k+1}/3^k`. The product-type family generalises it to an arbitrary
positive new factor — and *that* is what breaks traciality, because the
normalised trace is recovered only when every `x_k` is central.

## Non-traciality, with a witness

`ω_X` is tracial exactly when `X` is central: the defect is

    Tr(X·ab) − Tr(X·ba) = Tr((Xa − aX)·b),

visibly zero for all `b` iff `X` commutes with everything. §2 exhibits the
failure concretely for the r370 witness weight `diag(1,2,1)`:

    a = E₀₁, b = E₁₀ :   Tr(X·ab) = 1,  Tr(X·ba) = 2.

So `ω_X(ab) ≠ ω_X(ba)`. **The level-1 state of the witness family is not a
trace.**

## The observation that makes this gate (A)'s half, and not another conditional

r372's non-identity conclusion needed `LevelMapInjective`, because it compared
*elements* of `T_∞`. **Non-traciality does not**, because it compares *values in
`ℂ`*: if `Ω` is any functional on `T_∞` with `Ω(ι_k c) = ω_k(c)`, then from
`ω_k(ab) ≠ ω_k(ba)` and `ι_k` being a ring homomorphism,

    Ω(ι a · ι b) = ω_k(ab) ≠ ω_k(ba) = Ω(ι b · ι a),

so `Ω` is not tracial — with no injectivity hypothesis anywhere. That asymmetry
between r372 and this file is worth noticing: comparing scalars is cheaper than
comparing elements.

`limitState_not_tracial_of_level` states exactly that implication.

## What is NOT claimed

**The limit functional is not constructed here.** §1 proves the compatibility
that a construction consumes, and §3 proves that any functional restricting to
the level states is non-tracial — but assembling `Ω` itself needs a `Quotient`
descent over mathlib's `DirectLimit` setoid, and the substrate's tower maps are
`→+*` rather than `→ₐ`, so `DirectLimit.Module.lift` does not apply off the
shelf. That is plumbing with a known route, and it is the honest residue.

Also not claimed: continuity of `Ω`, that it extends to the `C*` completion
`TimelessFieldCompletion`, or that it is a KMS state *on `T_∞`* for the
descended automorphism of r372. And nothing here contradicts r113: a
non-tracial functional is simply outside the scope of a theorem about tracial
states — see `codex/KMS_OBSTRUCTION_RECHECK_2026-10-28.md`.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.KMS.ProductWeightPositive_r371
import PF.SubstrateUHFPreTraceDirectLimit

set_option autoImplicit false

namespace PF.KMS

open Matrix
open scoped Kronecker
open scoped ComplexOrder
open PrincipiaTractalis.SubstrateBase3Embed
open PrincipiaTractalis.SubstrateUHFPreTraceDirectLimit

/-! ## §1 — The level states are compatible with the tower -/

/-- The weight at level `k+1`, multiplied by an embedded element, is a single
reindexed kronecker product. The new factor commutes past the embedded element
(r370) and then recombines. -/
theorem productWeight_mul_embed (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) (k : ℕ)
    (a : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    productWeight x (k + 1) * substrateEmbedMatrix k a
      = Matrix.reindex (levelStepEquiv k) (levelStepEquiv k)
          ((productWeight x k * a) ⊗ₖ x k) := by
  rw [productWeight]
  calc substrateEmbedMatrix k (productWeight x k) * newFactor k (x k)
          * substrateEmbedMatrix k a
      = substrateEmbedMatrix k (productWeight x k)
          * (newFactor k (x k) * substrateEmbedMatrix k a) := by noncomm_ring
    _ = substrateEmbedMatrix k (productWeight x k)
          * (substrateEmbedMatrix k a * newFactor k (x k)) := by
          rw [← newFactor_commute k a (x k)]
    _ = substrateEmbedMatrix k (productWeight x k * a) * newFactor k (x k) := by
          rw [substrateEmbedMatrix_mul]; noncomm_ring
    _ = Matrix.reindex (levelStepEquiv k) (levelStepEquiv k)
          ((productWeight x k * a) ⊗ₖ x k) := embed_mul_newFactor k _ _

/-- The numerator scales by `Tr(x_k)`. -/
theorem trace_productWeight_mul_embed (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (k : ℕ) (a : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    (productWeight x (k + 1) * substrateEmbedMatrix k a).trace
      = (productWeight x k * a).trace * (x k).trace := by
  rw [productWeight_mul_embed, trace_reindex_self, Matrix.trace_kronecker]

/-- And so does the denominator. -/
theorem trace_productWeight_succ (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (k : ℕ) :
    (productWeight x (k + 1)).trace
      = (productWeight x k).trace * (x k).trace := by
  rw [productWeight, embed_mul_newFactor, trace_reindex_self,
    Matrix.trace_kronecker]

/-- **★★★ r377: the level states are tower-compatible ★★★**

`ω_{k+1}(ι a) = ω_k(a)`. The new factor's trace cancels. -/
theorem gibbs_tower_compatible (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hx : ∀ k, (x k).PosDef) (k : ℕ)
    (a : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    gibbsFunctional (productWeight x (k + 1)) (substrateEmbedMatrix k a)
      = gibbsFunctional (productWeight x k) a := by
  haveI : Nonempty (Fin (3^k)) := ⟨⟨0, Nat.pos_of_ne_zero (by positivity)⟩⟩
  have hxk : (x k).trace ≠ 0 := ne_of_gt (hx k).trace_pos
  have hXk : (productWeight x k).trace ≠ 0 :=
    ne_of_gt (productWeight_posDef x hx k).trace_pos
  simp only [gibbsFunctional, trace_productWeight_mul_embed,
    trace_productWeight_succ]
  field_simp

/-! ## §2 — Non-traciality, with an explicit witness -/

/-- The traciality defect of `ω_X` is the trace defect of `X`. -/
theorem gibbs_not_tracial {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.trace ≠ 0) {a b : Matrix (Fin n) (Fin n) ℂ}
    (h : (X * (a * b)).trace ≠ (X * (b * a)).trace) :
    gibbsFunctional X (a * b) ≠ gibbsFunctional X (b * a) := by
  simp only [gibbsFunctional]
  intro hcontra
  exact h (by field_simp at hcontra; exact hcontra)

/-- The second half of the witness pair: `E₁₀`. -/
def witnessElem' : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

/-- **★★★ r377: the witness weight's state is NOT a trace ★★★**

For `X = diag(1,2,1)`, `a = E₀₁`, `b = E₁₀`: `Tr(X·ab) = 1` but
`Tr(X·ba) = 2`. -/
theorem witnessWeight_trace_defect :
    (witnessWeight * (witnessElem * witnessElem')).trace
      ≠ (witnessWeight * (witnessElem' * witnessElem)).trace := by
  simp only [witnessWeight, witnessElem, witnessElem', Matrix.trace_fin_three,
    Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_val']
  norm_num

/-- `Tr(diag(1,2,1)) = 4`. No positive-definiteness needed — the trace is a
computation. -/
lemma witnessWeight_trace : witnessWeight.trace = 4 := by
  simp only [witnessWeight, Matrix.trace_fin_three, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_val']
  norm_num

theorem witnessWeight_state_not_tracial :
    gibbsFunctional witnessWeight (witnessElem * witnessElem')
      ≠ gibbsFunctional witnessWeight (witnessElem' * witnessElem) := by
  refine gibbs_not_tracial ?_ witnessWeight_trace_defect
  rw [witnessWeight_trace]
  norm_num

/-! ## §3 — Non-traciality transfers to the limit WITHOUT injectivity -/

private abbrev TObj : ℕ → Type := fun k => Matrix (Fin (3^k)) (Fin (3^k)) ℂ

private noncomputable abbrev TMap :
    ∀ i j : ℕ, i ≤ j → (TObj i →+* TObj j) :=
  fun i j h => PrincipiaTractalis.SubstrateDirectLimit.substrateRingHomIter i j h

/-- The level map is multiplicative — it is mathlib's `of`, a `RingHom`. -/
lemma levelMap_mul (k : ℕ) (c d : TObj k) :
    PrincipiaTractalis.SubstrateDirectLimit.substrateLevelToTimelessField k c
        * PrincipiaTractalis.SubstrateDirectLimit.substrateLevelToTimelessField k d
      = PrincipiaTractalis.SubstrateDirectLimit.substrateLevelToTimelessField k (c * d) :=
  (map_mul (DirectLimit.Ring.of TObj TMap k) c d).symm

/-- **★★★ r377: any functional restricting to the level states is non-tracial ★★★**

Unlike r372's non-identity conclusion, this needs **no** injectivity of the
level map: the comparison is between values in `ℂ`, not between elements of
`T_∞`. -/
theorem limitState_not_tracial_of_level
    {Ω : PrincipiaTractalis.SubstrateDirectLimit.TimelessFieldRing → ℂ}
    {X : ∀ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ} (k : ℕ)
    (hΩ : ∀ (j : ℕ) (c : Matrix (Fin (3^j)) (Fin (3^j)) ℂ),
      Ω (PrincipiaTractalis.SubstrateDirectLimit.substrateLevelToTimelessField j c)
        = gibbsFunctional (X j) c)
    {a b : Matrix (Fin (3^k)) (Fin (3^k)) ℂ}
    (hab : gibbsFunctional (X k) (a * b) ≠ gibbsFunctional (X k) (b * a)) :
    Ω (PrincipiaTractalis.SubstrateDirectLimit.substrateLevelToTimelessField k a
        * PrincipiaTractalis.SubstrateDirectLimit.substrateLevelToTimelessField k b)
      ≠ Ω (PrincipiaTractalis.SubstrateDirectLimit.substrateLevelToTimelessField k b
        * PrincipiaTractalis.SubstrateDirectLimit.substrateLevelToTimelessField k a) := by
  rw [levelMap_mul, levelMap_mul, hΩ, hΩ]
  exact hab

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.productWeight_mul_embed
#print axioms PF.KMS.trace_productWeight_mul_embed
#print axioms PF.KMS.trace_productWeight_succ
#print axioms PF.KMS.gibbs_tower_compatible
#print axioms PF.KMS.gibbs_not_tracial
#print axioms PF.KMS.witnessWeight_trace
#print axioms PF.KMS.witnessWeight_trace_defect
#print axioms PF.KMS.witnessWeight_state_not_tracial
#print axioms PF.KMS.limitState_not_tracial_of_level
