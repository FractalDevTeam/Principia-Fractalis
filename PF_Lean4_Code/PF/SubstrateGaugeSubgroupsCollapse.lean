/-
# The claimed gauge subgroups lie inside the kernel of the ch04:461 quotient.

★ 2026-09-17 r336 — a second, independent internal contradiction in Chapter 4,
found by reading Thm 4.19 against Thm 4.18.

`ch04:493-500` (Thm 4.19, Fundamental Forces from Subgroups) asserts
`U(1), SU(2), SU(3) ⊂ Aut(T∞)`, and `ch04:518-524` spells out how they act:

    α_θ(a) = e^{iθQ} a e^{-iθQ}      (the U(1) / electromagnetism example)

That is conjugation by a unit. By r333 every such map preserves the canonical
trace, so it lies in `Aut₀(T∞)` — the subgroup `ch04:461` divides OUT.

**So the forces are quotiented away by the construction that is supposed to
produce the spacetime they act on.** Thm 4.18 and Thm 4.19 cannot both do the
work the chapter asks of them: whatever `Aut(T∞)/Aut₀(T∞)` is, every gauge
transformation implemented by conjugation is trivial in it.

This is independent of the r333 collapse. Even if `Aut₀` had been a proper
subgroup and the quotient had been large, conjugation-implemented gauge groups
would still sit inside `Aut₀` and still die in the quotient. The contradiction
is structural, not a consequence of the trace being unique.

## What is proved below

* `ConjFamily.trace_preserving` — every member of a conjugation-implemented
  family satisfies the `ch04:461` gauge condition.
* `ConjFamily.inducedTrace_const` — the whole family induces one and the same
  trace functional, namely `UHF_trace`. The family is entirely inside `Aut₀`.
* `gauge_family_collapses_but_is_nontrivial` — and this is not because such
  families are trivial: an explicit two-element family whose members are
  genuinely different maps, both annihilated by the quotient.

## What is NOT claimed

* No claim that `U(1)`, `SU(2)` or `SU(3)` embed in `Aut(T∞)` at all. The
  chapter asserts that; it is not proved anywhere in the corpus and is not
  proved here. What is proved is conditional in the honest direction: **to the
  extent that such a subgroup acts by conjugation — which is the only action
  the chapter exhibits — it lies in `Aut₀`.**
* Nothing about `Diff(T∞)` (the gravity line, `ch04:496`), which the chapter
  does not define.
* No topology or continuity in the group parameter is used or needed, so
  nothing here depends on these being Lie groups.
* Nothing here is about physics. It is a statement about conjugation in an
  operator algebra.

Kernel-only: [propext, Classical.choice, Quot.sound]. Zero project axioms.
-/

import PF.SubstrateIdempotentTraceRigidity
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateGaugeSubgroupsCollapse

open SubstrateTimelessFieldCompletion
open SubstrateUHFPreTraceDirectLimit
open SubstrateAutomorphismQuotientCollapse
open SubstrateInnerAutomorphismNontrivial

/-! ## §1 — Conjugation-implemented families -/

/-- **A gauge family implemented by conjugation**, indexed by any parameter type
    `G`. This is the shape of `ch04:521`: `α_θ(a) = e^{iθQ} a e^{-iθQ}`, with
    `g θ = e^{iθQ}` and `h θ = e^{-iθQ}`.

    No group structure, topology, or continuity in `θ` is imposed: the result
    below does not need them, so it applies to any such family whatsoever. -/
structure ConjFamily (G : Type*) where
  /-- the implementing unit -/
  g : G → TimelessFieldCompletion
  /-- its two-sided inverse -/
  h : G → TimelessFieldCompletion
  gh : ∀ t, g t * h t = 1
  hg : ∀ t, h t * g t = 1

variable {G : Type*}

/-- The action of a family member. -/
noncomputable def ConjFamily.act (F : ConjFamily G) (t : G) :
    TimelessFieldCompletion → TimelessFieldCompletion :=
  conjBy (F.g t) (F.h t)

/-- Every member is a continuous unital ℂ-algebra endomorphism, so r333 applies. -/
theorem ConjFamily.isEndo (F : ConjFamily G) (t : G) :
    IsContUnitalAlgEndo (F.act t) :=
  conjBy_isContUnitalAlgEndo (F.g t) (F.h t) (F.gh t) (F.hg t)

/-! ## §2 — Every member satisfies the gauge condition of ch04:461 -/

/-- **★ r336.1 — every conjugation-implemented gauge transformation preserves
    the trace, hence lies in `Aut₀(T∞)`. ★** -/
theorem ConjFamily.trace_preserving (F : ConjFamily G) (t : G)
    (x : TimelessFieldCompletion) :
    UHF_trace (F.act t x) = UHF_trace x :=
  trace_preserved (F.isEndo t) x

/-- **★ r336.2 — the entire family induces one and the same trace functional. ★**
    The family is constant as seen by the `ch04:461` invariant. -/
theorem ConjFamily.inducedTrace_const (F : ConjFamily G) (t : G) :
    (fun x => UHF_trace (F.act t x)) = UHF_trace :=
  inducedTrace_eq (F.isEndo t)

/-- Any two members are indistinguishable to the invariant. -/
theorem ConjFamily.inducedTrace_agree (F : ConjFamily G) (s t : G) :
    (fun x => UHF_trace (F.act s x)) = (fun x => UHF_trace (F.act t x)) := by
  rw [F.inducedTrace_const s, F.inducedTrace_const t]

/-! ## §3 — …and this is not because such families are trivial -/

/-- A two-element conjugation family: the identity, and the r334 automorphism. -/
noncomputable def witnessFamily : ConjFamily Bool where
  g := fun b => if b then uInf else 1
  h := fun b => if b then vInf else 1
  gh := by intro b; cases b <;> simp [uInf_mul_vInf]
  hg := by intro b; cases b <;> simp [vInf_mul_uInf]

theorem witnessFamily_true : witnessFamily.act true = conjBy uInf vInf := rfl

theorem witnessFamily_false : witnessFamily.act false = id := by
  funext x
  show (1 : TimelessFieldCompletion) * x * 1 = x
  rw [one_mul, mul_one]

/-- **★★★ r336.3 — THE FORCES ARE QUOTIENTED AWAY ★★★**

    There is a conjugation-implemented family whose two members are genuinely
    different maps, yet every member induces exactly `UHF_trace` and therefore
    lies in `Aut₀(T∞)`.

    So the `ch04:461` quotient identifies every gauge transformation of this
    shape with the identity. Thm 4.19 places the forces inside `Aut(T∞)`;
    Thm 4.18 divides out everything trace-preserving. Conjugation-implemented
    gauge groups are trace-preserving. The two theorems cannot both stand. -/
theorem gauge_family_collapses_but_is_nontrivial :
    ∃ F : ConjFamily Bool,
      (∀ t, (fun x => UHF_trace (F.act t x)) = UHF_trace) ∧
      F.act true ≠ F.act false := by
  refine ⟨witnessFamily, fun t => witnessFamily.inducedTrace_const t, ?_⟩
  rw [witnessFamily_true, witnessFamily_false]
  exact conjBy_uInf_ne_id

/-! ## §4 — Axiom audit -/

#print axioms ConjFamily.isEndo
#print axioms ConjFamily.trace_preserving
#print axioms ConjFamily.inducedTrace_const
#print axioms ConjFamily.inducedTrace_agree
#print axioms witnessFamily_false
#print axioms gauge_family_collapses_but_is_nontrivial

end SubstrateGaugeSubgroupsCollapse
end PrincipiaTractalis
