/-
# The idempotent trace range is blind too — the third invariant falls.

★ 2026-09-17 r335 — completing the r333/r334 arc.

r333: the trace invariant of `ch04:461` is a one-point set.
r334: the group it is computed on is NOT a one-point set, so real structure
      is being discarded.
r335: the natural next invariant — the trace range on idempotents, which is
      the concrete shadow of `K₀` that this corpus actually formalizes
      (r123) — is ALSO fixed by every continuous unital ℂ-algebra
      endomorphism, including the nontrivial one r334 exhibits. ★

## Why this was the next thing to try, and what its failure means

After r333 killed the trace, the standard repair for a UHF factor is to
quotient by inner automorphisms and look at K-theory instead: `K₀(T∞)` with
its order unit. r123 already computes the substrate's trace range on
projections as `ℤ[1/3]` (`AlphaFromSubstrateKTheory_r123.lean:249, 266`).

This file shows that channel closes too. Every continuous unital ℂ-algebra
endomorphism carries idempotents to idempotents **with the same trace**, so
the induced action on the idempotent trace range is the identity — for the
r334 automorphism as much as for `id`.

**Combined verdict of r333 + r334 + r335.** Three invariants of `Aut(T∞)`
have now been checked: the trace functional, the trace range on idempotents,
and (r334) the group itself. The group is nontrivial; both invariants are
constant. No quotient of `Aut(T∞)` by a condition expressible in the trace or
in the idempotent trace range can be anything but a point. The construction
at `ch04:455-461` cannot be repaired by swapping in either of these.

## What is NOT claimed — read this before citing the file

* **This is not `K₀`.** Mathlib has no K-theory for C\*-algebras, so no
  `K₀(T∞)` exists to reason about here. What is formalized is the invariant
  r123 actually uses: trace values on idempotents. The step from "the
  idempotent trace range is fixed" to "`K₀` is fixed" is a **mathematical
  inference, not a kernel theorem**, and it is not made below.
* Idempotence (`p * p = p`) is used, not self-adjointness. That is weaker
  than "projection" and therefore covers more elements, which makes the
  rigidity conclusion stronger, not weaker.
* Nothing here settles whether `Out(T∞) = Aut(T∞)/Inn(T∞)` is nontrivial.
  It says that if it is, neither of these two invariants can detect it.
* Nothing here is about physics.

Kernel-only: [propext, Classical.choice, Quot.sound]. Zero project axioms.
-/

import PF.SubstrateInnerAutomorphismNontrivial
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateIdempotentTraceRigidity

open SubstrateTimelessFieldCompletion
open SubstrateUHFPreTraceDirectLimit
open SubstrateAutomorphismQuotientCollapse
open SubstrateInnerAutomorphismNontrivial

/-! ## §1 — Idempotents are carried to idempotents -/

/-- **`IsIdem p`** — `p` is idempotent. Self-adjointness is deliberately NOT
    required: the weaker predicate covers more elements, so rigidity over it is
    a stronger statement. -/
def IsIdem (p : TimelessFieldCompletion) : Prop := p * p = p

/-- Every continuous unital ℂ-algebra endomorphism preserves idempotence. -/
theorem map_isIdem {α : TimelessFieldCompletion → TimelessFieldCompletion}
    (hα : IsContUnitalAlgEndo α) {p : TimelessFieldCompletion} (hp : IsIdem p) :
    IsIdem (α p) := by
  show α p * α p = α p
  rw [← hα.mul, hp]

/-! ## §2 — …with the same trace -/

/-- **★ r335.1 — idempotents are carried to idempotents of equal trace. ★**
    Immediate from r333, but stated because this pair is the invariant. -/
theorem map_isIdem_and_trace {α : TimelessFieldCompletion → TimelessFieldCompletion}
    (hα : IsContUnitalAlgEndo α) {p : TimelessFieldCompletion} (hp : IsIdem p) :
    IsIdem (α p) ∧ UHF_trace (α p) = UHF_trace p :=
  ⟨map_isIdem hα hp, trace_preserved hα p⟩

/-- The trace range on idempotents — the concrete shadow of `K₀` that r123 uses. -/
def idemTraces : Set ℂ :=
  {c | ∃ p : TimelessFieldCompletion, IsIdem p ∧ UHF_trace p = c}

/-- The forward image of the idempotent trace range never leaves it. -/
theorem idemTraces_image_subset {α : TimelessFieldCompletion → TimelessFieldCompletion}
    (hα : IsContUnitalAlgEndo α) :
    UHF_trace '' (α '' {p | IsIdem p}) ⊆ idemTraces := by
  rintro c ⟨y, ⟨p, hp, rfl⟩, rfl⟩
  exact ⟨α p, map_isIdem hα hp, rfl⟩

/-! ## §3 — For an inner automorphism the range is fixed exactly -/

/-- **★ r335.2 — conjugation by a two-sided unit fixes the idempotent trace
    range exactly, not merely up to inclusion. ★** -/
theorem conjBy_idemTraces_eq (u v : TimelessFieldCompletion)
    (huv : u * v = 1) (hvu : v * u = 1) :
    UHF_trace '' (conjBy u v '' {p | IsIdem p}) = idemTraces := by
  apply Set.Subset.antisymm
  · exact idemTraces_image_subset (conjBy_isContUnitalAlgEndo u v huv hvu)
  · rintro c ⟨p, hp, rfl⟩
    refine ⟨conjBy u v (conjBy v u p), ⟨conjBy v u p, ?_, rfl⟩, ?_⟩
    · exact map_isIdem (conjBy_isContUnitalAlgEndo v u hvu huv) hp
    · have hround : conjBy u v (conjBy v u p) = p := by
        show u * (v * p * u) * v = p
        have h : u * (v * p * u) * v = (u * v) * p * (u * v) := by
          simp only [mul_assoc]
        rw [h, huv, one_mul, mul_one]
      rw [hround]

/-! ## §4 — The verdict -/

/-- **★★★ r335.3 — THE SECOND INVARIANT IS BLIND TOO ★★★**

    There is a continuous unital ℂ-algebra endomorphism of `T∞` that is not the
    identity, yet acts as the identity on the idempotent trace range — carrying
    every idempotent to an idempotent of exactly the same trace, and fixing the
    range setwise.

    With r333 (trace functional constant) and r334 (the group is not a point):
    no quotient of `Aut(T∞)` by a condition expressible in the trace, or in the
    idempotent trace range, can be anything but a single point. -/
theorem nontrivial_endo_fixes_idemTraces :
    ∃ α : TimelessFieldCompletion → TimelessFieldCompletion,
      IsContUnitalAlgEndo α ∧ α ≠ id ∧
      (∀ p, IsIdem p → IsIdem (α p) ∧ UHF_trace (α p) = UHF_trace p) ∧
      UHF_trace '' (α '' {p | IsIdem p}) = idemTraces := by
  refine ⟨conjBy uInf vInf,
    conjBy_isContUnitalAlgEndo uInf vInf uInf_mul_vInf vInf_mul_uInf,
    conjBy_uInf_ne_id,
    fun p hp => map_isIdem_and_trace
      (conjBy_isContUnitalAlgEndo uInf vInf uInf_mul_vInf vInf_mul_uInf) hp,
    conjBy_idemTraces_eq uInf vInf uInf_mul_vInf vInf_mul_uInf⟩

/-! ## §5 — Axiom audit -/

#print axioms map_isIdem
#print axioms map_isIdem_and_trace
#print axioms idemTraces_image_subset
#print axioms conjBy_idemTraces_eq
#print axioms nontrivial_endo_fixes_idemTraces

end SubstrateIdempotentTraceRigidity
end PrincipiaTractalis
