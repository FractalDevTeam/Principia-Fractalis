/-
# r359: Completeness for infinitely many sites, on the substrate carrier

★ 2026-10-28 r359 — the inductive-limit completeness ★

## The question r354 left open, and the carrier it was asked about

`TernaryNetCompleteness_r354` proves two things about an arbitrary site set `ι`:

* `net_eq_iSup_finite` (`:234`) — `𝒜(ι) = ⨆ S : Finset ι, 𝒜(S)`, with no
  finiteness hypothesis, and
* `completeness` (`:257`) — `𝒜(ι) = ⊤`, but only for `[Fintype ι]`.

Its header records what would settle the infinite case as "a free-basis theorem
for `PiTensorProduct` over an infinite index", which is 0 files in mathlib.

**That price is specific to the tensor-product carrier.** The framework's actual
substrate is not `⨂[ℂ] (_ : ι), M₃` for infinite `ι` — it is `T_∞`, the
inductive limit of the matrix tower (`SubstrateDirectLimit.lean:176`). On that
carrier completeness is reachable, because the limit is a quotient of the sigma
type over finite levels: every element already lives at some finite stage, and
at a finite stage r354's `completeness` applies.

So this file does not close r354's question as posed. It proves the statement
on the carrier the framework actually uses, and says plainly which is which.

## What is proved

* `substrate_exhausted` — every `z : T_∞` is `substrateLevelToTimelessField k x`
  for some level `k` and some `x : M_{3^k}(ℂ)`.
* `substrate_exhausted_by_net` — the same, with `x` written as the image of a
  net element under r358's algebra isomorphism.
* `substrate_completeness` — every `z : T_∞` is the image of an element of the
  **region algebra of the full finite site set** `Fin k`. That is completeness
  in the inductive-limit sense: the substrate is exhausted by the local algebras
  of finite regions.

## One measured correction to my own earlier note

I recorded the step as "one `DirectLimit.exists_of` argument". That lemma
(`Mathlib/Algebra/Colimit/Ring.lean:92`) is for mathlib's *other* direct limit,
the `FreeCommRing`/`Ideal.Quotient` construction, and does not apply to the
`Colimit/DirectLimit.lean` carrier `SubstrateDirectLimit` uses. Three `exact?`
probes confirmed no packaged surjectivity lemma fires here. The carrier is a
`Quotient` of `Σ k, M_{3^k}(ℂ)` — the `⟦⟨i, x⟩⟧` notation throughout that file
— so the right tool is `Quotient.exists_rep`. Same one-step cost, different
lemma.

## Axiom budget

Zero project axioms; the three kernel axioms only.
-/

import PF.TernaryNetMatrixAlgBridge_r358
import PF.TernaryNetCompleteness_r354
import PF.SubstrateDirectLimit

namespace PrincipiaTractalis
namespace TernaryNetInfiniteCompleteness

open TernaryNetMatrixBridge TernaryNetMatrixAlgBridge SubstrateDirectLimit

/-! ## §1 — Every element of `T_∞` lives at a finite level

The substrate carrier is `DirectLimit` from `Mathlib.Algebra.Colimit.DirectLimit`,
which is a `Quotient` of `Σ k, M_{3^k}(ℂ)`. Surjectivity of the level embedding
is therefore `Quotient.exists_rep`, and `substrateLevelToTimelessField` is
definitionally `fun x => ⟦⟨k, x⟩⟧`. -/

theorem substrate_exhausted (z : TimelessFieldRing) :
    ∃ (k : ℕ) (x : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ),
      substrateLevelToTimelessField k x = z := by
  obtain ⟨⟨k, x⟩, hz⟩ := Quotient.exists_rep z
  exact ⟨k, x, hz⟩

/-! ## §2 — Written through the net

r358's `netAlgEquivLevel k : Net k ≃ₐ[ℂ] Level k` lets the same element be
named by a point of the locality net rather than by a raw matrix. -/

theorem substrate_exhausted_by_net (z : TimelessFieldRing) :
    ∃ (k : ℕ) (a : Net k),
      substrateLevelToTimelessField k (netAlgEquivLevel k a) = z := by
  obtain ⟨k, x, hz⟩ := substrate_exhausted z
  refine ⟨k, (netAlgEquivLevel k).symm x, ?_⟩
  rw [AlgEquiv.apply_symm_apply]
  exact hz

/-! ## §3 — Completeness, in the inductive-limit sense

The substrate is exhausted by the local algebras of **finite** regions. At each
level the whole net is the region algebra of the full site set — that is r354's
`completeness`, which holds exactly because `Fin k` is a `Fintype`. -/

theorem substrate_completeness (z : TimelessFieldRing) :
    ∃ (k : ℕ) (a : Net k),
      a ∈ TernaryNetIsotony.regionAlgebra (Fin k) (Set.univ : Set (Fin k)) ∧
      substrateLevelToTimelessField k (netAlgEquivLevel k a) = z := by
  obtain ⟨k, a, hz⟩ := substrate_exhausted_by_net z
  refine ⟨k, a, ?_, hz⟩
  rw [TernaryNetCompleteness.completeness (Fin k)]
  exact Algebra.mem_top

/-! ## §4 — Non-vacuity

The statement is not vacuous: `T_∞` is nontrivial, so there is something to
exhaust, and the witness at level `k` is genuinely a net element. -/

theorem substrate_completeness_witness_exists :
    ∃ (k : ℕ) (a : Net k),
      a ∈ TernaryNetIsotony.regionAlgebra (Fin k) (Set.univ : Set (Fin k)) :=
  ⟨0, 1, by rw [TernaryNetCompleteness.completeness (Fin 0)]; exact Algebra.mem_top⟩

/-! ## §5 — What is NOT claimed

`r354`'s open question is about the **tensor-product** carrier: whether
`regionAlgebra ι Set.univ = ⊤` holds in `⨂[ℂ] (_ : ι), M₃` for infinite `ι`.
This file does not settle that, in either direction, and does not bear on it:
nothing below mentions an infinite site set. What it establishes is the
corresponding statement on `T_∞`, which is the carrier the framework's substrate
results (r100–r113) are actually about, and the carrier algebraic quantum field
theory uses — there the quasi-local algebra *is* the inductive limit of the
local algebras, by construction rather than by theorem.

Covariance, the sixth Haag–Kastler axiom, remains open and is blocked on
`Aut(T_∞)`: UHF C\*-algebra theory is 0 files in mathlib at this pin. -/

theorem scope_tensor_carrier_untouched : True := trivial

end TernaryNetInfiniteCompleteness
end PrincipiaTractalis
