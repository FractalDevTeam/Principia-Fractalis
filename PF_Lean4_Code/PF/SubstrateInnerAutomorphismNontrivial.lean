/-
# The substrate automorphism group is NOT trivial — so the trace quotient
# destroys real structure.

★ 2026-09-17 r334 — companion to r333. r333 proved the invariant
`ch04:461` quotients by is a one-point set. On its own that is ambiguous:
a quotient can be a point because the group is a point. This file removes
the ambiguity.

`Aut(T∞)` contains a nontrivial inner automorphism. So the group being
quotiented is provably larger than `{id}`, while r333 says its image under
the trace invariant is exactly one point. The trace does not fail to
separate because there is nothing to separate — it fails because it is
blind. ★

## The statement that matters

  `trace_blind_to_nontrivial_endo` :
      ∃ α, IsContUnitalAlgEndo α ∧ α ≠ id ∧ (fun x => UHF_trace (α x)) = UHF_trace

Read together with r333 (`inducedTraces_encard_eq_one`), this says the map
"automorphism ↦ its induced trace functional" is constant on a domain that
is provably not a single point. The construction at `ch04:455-461` therefore
does not merely fail to give four dimensions; it discards structure that
the substrate actually has.

## Consequence for the repair

The right quotient for a UHF factor is by the INNER automorphisms —
`Out(T∞) = Aut(T∞)/Inn(T∞)` — not by the trace-preserving ones. This file
establishes the first half of what that needs: `Inn(T∞) ≠ {id}`. Whether
`Out(T∞)` is itself nontrivial is NOT settled here and is not claimed.

## Witness

Conjugation by the unipotent unit `u = 1 + E₀₁` at substrate level 1, whose
two-sided inverse is `1 − E₀₁` because `E₀₁ · E₀₁ = 0`. Conjugation moves
`E₁₀`:

    (1 + E₀₁) · E₁₀ · (1 − E₀₁) = E₁₀ + E₀₀ − E₁₁ − E₀₁ ≠ E₁₀

separated by the `(0,0)` entry: `1` on the left, `0` on the right. The
witness is transported to `T∞` by `levelToCompletion_injective` (r217.c),
exactly as r217 transports its noncommutativity witness.

Unitarity is NOT used and NOT needed: the definition of an inner
automorphism requires only a two-sided inverse.

## Scope

* Continuity is carried as a hypothesis, as in r333.
* Nothing here is about `Out(T∞)` being nontrivial, about `π₀`, or about
  any topology on the automorphism group.
* Nothing here is about physics. It is a statement about an operator
  algebra.

Kernel-only: [propext, Classical.choice, Quot.sound]. Zero project axioms.
-/

import PF.SubstrateAutomorphismQuotientCollapse
import PF.SubstrateNotCommutative_r217
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateInnerAutomorphismNontrivial

open Matrix
open SubstrateTimelessFieldCompletion
open SubstrateUHFPreTraceDirectLimit
open SubstrateCompletionSimplicity
open SubstrateNotCommutative
open SubstrateAutomorphismQuotientCollapse

/-! ## §1 — Conjugation by a two-sided unit is a continuous unital ℂ-algebra endomorphism -/

/-- **`conjBy u v x = u * x * v`.** When `u*v = v*u = 1` this is the inner
    automorphism determined by `u`. Invertibility is expressed by carrying the
    two-sided inverse explicitly, so no `Units` bundling is needed. -/
noncomputable def conjBy (u v x : TimelessFieldCompletion) : TimelessFieldCompletion :=
  u * x * v

/-- Conjugation by a two-sided unit satisfies every hypothesis of r333. In
    particular r333 applies to it, so it preserves the trace. -/
theorem conjBy_isContUnitalAlgEndo (u v : TimelessFieldCompletion)
    (huv : u * v = 1) (hvu : v * u = 1) :
    IsContUnitalAlgEndo (conjBy u v) where
  continuous := by
    show Continuous fun x => u * x * v
    exact (continuous_const.mul continuous_id).mul continuous_const
  add := fun x y => by
    show u * (x + y) * v = u * x * v + u * y * v
    rw [mul_add, add_mul]
  smul := fun c x => by
    show u * (c • x) * v = c • (u * x * v)
    rw [mul_smul_comm, smul_mul_assoc]
  mul := fun x y => by
    show u * (x * y) * v = (u * x * v) * (u * y * v)
    have h : (u * x * v) * (u * y * v) = u * x * (v * u) * (y * v) := by
      simp only [mul_assoc]
    rw [h, hvu, mul_one]
    simp only [mul_assoc]
  unital := by
    show u * 1 * v = 1
    rw [mul_one, huv]

/-! ## §2 — The unipotent witness at substrate level 1 -/

/-- Index `0` of `Fin (3^1)`. -/
def i0 : Fin (3 ^ 1) := ⟨0, by norm_num⟩
/-- Index `1` of `Fin (3^1)`. -/
def i1 : Fin (3 ^ 1) := ⟨1, by norm_num⟩

theorem i0_ne_i1 : i0 ≠ i1 := by decide

/-- `E₀₁ · E₀₁ = 0`, because the inner indices `1` and `0` differ. -/
theorem E01_sq :
    (single i0 i1 (1 : ℂ) : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ) * single i0 i1 1 = 0 :=
  single_mul_single_of_ne (1 : ℂ) i0 i1 i0 (Ne.symm i0_ne_i1) (1 : ℂ)

/-- The unipotent unit `u = 1 + E₀₁`. -/
noncomputable def uMat : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ := 1 + single i0 i1 1
/-- Its two-sided inverse `v = 1 − E₀₁`. -/
noncomputable def vMat : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ := 1 - single i0 i1 1

theorem uMat_mul_vMat : uMat * vMat = 1 := by
  simp only [uMat, vMat, mul_sub, add_mul, one_mul, mul_one, E01_sq]
  abel

theorem vMat_mul_uMat : vMat * uMat = 1 := by
  simp only [uMat, vMat, sub_mul, mul_add, one_mul, mul_one, E01_sq]
  abel

/-- Explicit expansion of the conjugate: `(1+E₀₁)·E₁₀·(1−E₀₁) = E₁₀ + E₀₀ − E₁₁ − E₀₁`. -/
theorem conj_expand :
    uMat * single i1 i0 (1 : ℂ) * vMat
      = single i1 i0 1 + single i0 i0 1 - single i1 i1 1 - single i0 i1 1 := by
  have e1 : (single i0 i1 (1 : ℂ) : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ) * single i1 i0 1
      = single i0 i0 1 := by rw [single_mul_single_same]; norm_num
  have e2 : (single i1 i0 (1 : ℂ) : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ) * single i0 i1 1
      = single i1 i1 1 := by rw [single_mul_single_same]; norm_num
  have e3 : (single i0 i0 (1 : ℂ) : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ) * single i0 i1 1
      = single i0 i1 1 := by rw [single_mul_single_same]; norm_num
  simp only [uMat, vMat, add_mul, one_mul, mul_sub, mul_one, e1, e2, e3]
  abel

/-- **Conjugation by `u` moves `E₁₀`.** Separated by the `(0,0)` entry:
    the conjugate has entry `1` there, `E₁₀` has `0`. -/
theorem conj_moves_matrix :
    uMat * single i1 i0 (1 : ℂ) * vMat ≠ single i1 i0 (1 : ℂ) := by
  have a1 : (single i1 i0 (1 : ℂ) : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ) i0 i0 = 0 :=
    single_apply_of_ne i1 i0 1 i0 i0 (by decide)
  have a2 : (single i0 i0 (1 : ℂ) : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ) i0 i0 = 1 :=
    single_apply_same i0 i0 1
  have a3 : (single i1 i1 (1 : ℂ) : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ) i0 i0 = 0 :=
    single_apply_of_ne i1 i1 1 i0 i0 (by decide)
  have a4 : (single i0 i1 (1 : ℂ) : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) ℂ) i0 i0 = 0 :=
    single_apply_of_ne i0 i1 1 i0 i0 (by decide)
  intro hcon
  rw [conj_expand] at hcon
  have h := congrFun (congrFun hcon i0) i0
  simp only [Matrix.add_apply, Matrix.sub_apply, a1, a2, a3, a4] at h
  norm_num at h

/-! ## §3 — Transport to the substrate and the payoff -/

/-- The unit in `T∞`. -/
noncomputable def uInf : TimelessFieldCompletion := levelToCompletion 1 uMat
/-- Its two-sided inverse in `T∞`. -/
noncomputable def vInf : TimelessFieldCompletion := levelToCompletion 1 vMat

theorem uInf_mul_vInf : uInf * vInf = 1 := by
  rw [uInf, vInf, ← map_mul, uMat_mul_vMat, map_one]

theorem vInf_mul_uInf : vInf * uInf = 1 := by
  rw [uInf, vInf, ← map_mul, vMat_mul_uMat, map_one]

/-- **★ r334.1 — there is a nontrivial inner automorphism of `T∞`. ★** -/
theorem conjBy_uInf_ne_id : conjBy uInf vInf ≠ id := by
  intro hcon
  have h := congrFun hcon (levelToCompletion 1 (single i1 i0 (1 : ℂ)))
  rw [conjBy, uInf, vInf, ← map_mul, ← map_mul] at h
  exact conj_moves_matrix (levelToCompletion_injective 1 h)

/-- **★★★ r334.2 — THE TRACE IS BLIND TO STRUCTURE THAT EXISTS ★★★**

    There is a continuous unital ℂ-algebra endomorphism of `T∞` that is not
    the identity, yet induces exactly the canonical trace.

    With r333's `inducedTraces_encard_eq_one`: the map
    "endomorphism ↦ induced trace functional" is constant on a domain that is
    provably not a single point. The quotient at `ch04:461` discards real
    structure. -/
theorem trace_blind_to_nontrivial_endo :
    ∃ α : TimelessFieldCompletion → TimelessFieldCompletion,
      IsContUnitalAlgEndo α ∧ α ≠ id ∧ (fun x => UHF_trace (α x)) = UHF_trace := by
  refine ⟨conjBy uInf vInf, conjBy_isContUnitalAlgEndo uInf vInf uInf_mul_vInf vInf_mul_uInf,
    conjBy_uInf_ne_id, ?_⟩
  exact inducedTrace_eq
    (conjBy_isContUnitalAlgEndo uInf vInf uInf_mul_vInf vInf_mul_uInf)

/-- **r334.3 — the gauge condition of `ch04:461` does not cut down `Aut`.**
    An explicit non-identity map satisfying it. -/
theorem gauge_condition_does_not_separate :
    ∃ α : TimelessFieldCompletion → TimelessFieldCompletion,
      α ≠ id ∧ ∀ x, UHF_trace (α x) = UHF_trace x := by
  refine ⟨conjBy uInf vInf, conjBy_uInf_ne_id, ?_⟩
  exact trace_preserved
    (conjBy_isContUnitalAlgEndo uInf vInf uInf_mul_vInf vInf_mul_uInf)

/-! ## §4 — Axiom audit -/

#print axioms conjBy_isContUnitalAlgEndo
#print axioms uMat_mul_vMat
#print axioms vMat_mul_uMat
#print axioms conj_expand
#print axioms conj_moves_matrix
#print axioms conjBy_uInf_ne_id
#print axioms trace_blind_to_nontrivial_endo
#print axioms gauge_condition_does_not_separate

end SubstrateInnerAutomorphismNontrivial
end PrincipiaTractalis
