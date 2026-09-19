/-
# Aut(T∞) ⧸ Aut₀(T∞) collapses: the bundled trace-preserving subgroup is ⊤.

STATUS: TARGETED BUILD VERIFIED 2026-09-19. The command
`lake build PF.SubstrateAutQuotientCollapse` completed all 3212 jobs. Every
public endpoint in the audit block below reports exactly
`[propext, Classical.choice, Quot.sound]`; no project axiom is introduced.

## Target

The book states `M⁴ = Aut(T∞)/Aut₀(T∞)`, where `Aut₀` is the group of gauge
automorphisms preserving the trace. This module formalizes that quotient with
an actual bundled automorphism group and an actual group quotient.

  * `SubstrateAut` — the bundled group `T∞ ≃⋆ₐ[ℂ] T∞` of unital ℂ-linear
    *-algebra automorphisms of `T∞ = TimelessFieldCompletion`.
  * `TracePreserving` — the subgroup `{g | ∀ x, UHF_trace (g x) = UHF_trace x}`,
    defined by the literal pointwise condition. Its closure proofs do not use
    the collapse theorem.
  * `substrateAut_continuous` — every `g` is continuous. This is derived from
    the mathlib fact that *-homomorphisms between C*-algebras are contractive
    (the `CStarAlgebra` instance is r59). It is not assumed.
  * `uhf_trace_comp_aut_isTracialState` — `UHF_trace ∘ g` is an
    `IsTracialState`.
  * `substrateAut_preserves_trace` — so, by `substrate_UHF_trace_unique`,
    `UHF_trace ∘ g = UHF_trace`.
  * `tracePreserving_eq_top` — `TracePreserving = ⊤`.
  * `tracePreserving_normal` — `Normal`, obtained only by rewriting to `⊤`.
  * `substrateAutQuotient_subsingleton`, `substrateAutQuotient_classes_eq`,
    `substrateAutQuotient_no_injection_fin_two` — the quotient
    `SubstrateAut ⧸ TracePreserving` has at most one element.
  * `substrateAut_nonempty`, `one_mem_tracePreserving`,
    `substrateAutQuotient_nonempty` — non-vacuity (identity automorphism).

## Epistemic ledger

  * Kernel theorem: the bundled trace-preservation,
    subgroup-equals-top, and quotient-subsingleton statements above.
  * Mathematical inference: if the book's `Aut₀(T∞)` is literally the group of
    all trace-preserving automorphisms, its stated quotient `Aut/Aut₀` is a
    single point. So it cannot carry a 4-manifold structure.
  * Unformalized bridge: nothing here identifies `T∞ ≃⋆ₐ[ℂ] T∞` with every
    physical or gauge automorphism the prose intends, and nothing here makes any
    manifold or dimension argument. This module does NOT show that spacetime
    cannot emerge by some other mechanism (a different group, a non-trace
    condition for `Aut₀`, a topologized or non-inner quotient, etc.). It only
    shows that the literal quotient, as stated, collapses.
-/

import PF.SubstrateTraceUniqueness
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.GroupTheory.QuotientGroup.Defs

namespace PrincipiaTractalis
namespace SubstrateAutQuotientCollapse

open SubstrateTimelessFieldCompletion SubstrateTraceUniqueness
open SubstrateUHFPreTraceDirectLimit SubstrateUHFTraceCauchySchwarz
open SubstrateUHFTraceIsTracial

/-! ## §1 — The bundled automorphism group. -/

/-- `Aut(T∞)`: unital ℂ-linear *-algebra automorphisms of the substrate
    C*-algebra `T∞ = TimelessFieldCompletion` (mathlib `StarAlgEquiv`). -/
abbrev SubstrateAut : Type :=
  TimelessFieldCompletion ≃⋆ₐ[ℂ] TimelessFieldCompletion

/-- Every bundled automorphism is continuous. It is 1-Lipschitz because
    *-homomorphisms between C*-algebras are contractive
    (`NonUnitalStarAlgHom.norm_apply_le`). Derived, not assumed. -/
theorem substrateAut_continuous (g : SubstrateAut) :
    Continuous (g : TimelessFieldCompletion → TimelessFieldCompletion) := by
  have hlip : LipschitzWith 1
      (g : TimelessFieldCompletion → TimelessFieldCompletion) := by
    intro x y
    rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le g (x - y)
  exact hlip.continuous

/-! ## §2 — The literal trace-preserving subgroup `Aut₀`. -/

/-- `Aut₀(T∞)`: automorphisms preserving the substrate trace pointwise. The
    closure proofs use only the definition, not §3. -/
def TracePreserving : Subgroup SubstrateAut where
  carrier := {g | ∀ x, UHF_trace (g x) = UHF_trace x}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb x
    show UHF_trace (a (b x)) = UHF_trace x
    rw [ha, hb]
  inv_mem' := by
    intro a ha x
    show UHF_trace (a.symm x) = UHF_trace x
    have h := ha (a.symm x)
    rw [StarAlgEquiv.apply_symm_apply] at h
    exact h.symm

theorem mem_tracePreserving (g : SubstrateAut) :
    g ∈ TracePreserving ↔ ∀ x, UHF_trace (g x) = UHF_trace x :=
  Iff.rfl

/-! ## §3 — Every bundled automorphism preserves the unique trace. -/

/-- `UHF_trace ∘ g` is a tracial state: continuity comes from §1, and the
    algebraic fields come from `g` being a unital *-algebra map. -/
theorem uhf_trace_comp_aut_isTracialState (g : SubstrateAut) :
    IsTracialState (fun x => UHF_trace (g x)) where
  continuous :=
    UHF_trace_uniformContinuous.continuous.comp (substrateAut_continuous g)
  add x y := by
    rw [map_add]
    exact UHF_trace_add _ _
  smul c x := by
    rw [map_smul]
    exact UHF_trace_smul _ _
  tracial x y := by
    rw [map_mul, map_mul]
    exact UHF_trace_mul_comm _ _
  unital := by
    rw [map_one]
    exact uhf_trace_isTracialState.unital

/-- **Trace preservation.** Every bundled automorphism of `T∞` preserves
    `UHF_trace`, by uniqueness of the tracial state (r113). -/
theorem substrateAut_preserves_trace (g : SubstrateAut)
    (x : TimelessFieldCompletion) : UHF_trace (g x) = UHF_trace x :=
  substrate_UHF_trace_unique _ (uhf_trace_comp_aut_isTracialState g) x

/-- **`Aut₀ = Aut`.** The literal trace-preserving subgroup is `⊤`. -/
theorem tracePreserving_eq_top : TracePreserving = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun g => substrateAut_preserves_trace g

/-- Normality, obtained only after `TracePreserving = ⊤`. -/
instance tracePreserving_normal : TracePreserving.Normal := by
  rw [tracePreserving_eq_top]
  infer_instance

/-! ## §4 — The quotient `Aut(T∞) ⧸ Aut₀(T∞)` collapses. -/

/-- **Quotient collapse.** `SubstrateAut ⧸ TracePreserving` is a subsingleton. -/
theorem substrateAutQuotient_subsingleton :
    Subsingleton (SubstrateAut ⧸ TracePreserving) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
  refine QuotientGroup.eq.mpr ?_
  rw [tracePreserving_eq_top]
  exact Subgroup.mem_top _

/-- All quotient classes are equal. -/
theorem substrateAutQuotient_classes_eq (g h : SubstrateAut) :
    (g : SubstrateAut ⧸ TracePreserving) = (h : SubstrateAut ⧸ TracePreserving) :=
  @Subsingleton.elim _ substrateAutQuotient_subsingleton _ _

/-- There is no injection `Fin 2 → Aut(T∞) ⧸ Aut₀(T∞)`: the quotient cannot
    even separate two points. -/
theorem substrateAutQuotient_no_injection_fin_two :
    ¬ ∃ f : Fin 2 → SubstrateAut ⧸ TracePreserving, Function.Injective f := by
  rintro ⟨f, hf⟩
  exact absurd (hf (@Subsingleton.elim _ substrateAutQuotient_subsingleton
    (f 0) (f 1))) (by decide)

/-! ## §5 — Non-vacuity. -/

/-- The automorphism group is inhabited by the identity. -/
theorem substrateAut_nonempty : Nonempty SubstrateAut :=
  ⟨StarAlgEquiv.refl⟩

/-- The identity satisfies the literal trace-preservation condition. -/
theorem one_mem_tracePreserving : (1 : SubstrateAut) ∈ TracePreserving :=
  TracePreserving.one_mem

/-- The quotient is inhabited, so with §4 it is exactly one point. -/
theorem substrateAutQuotient_nonempty :
    Nonempty (SubstrateAut ⧸ TracePreserving) :=
  ⟨((1 : SubstrateAut) : SubstrateAut ⧸ TracePreserving)⟩

/-! ## §6 — Axiom audit. -/

#print axioms substrateAut_continuous
#print axioms mem_tracePreserving
#print axioms uhf_trace_comp_aut_isTracialState
#print axioms substrateAut_preserves_trace
#print axioms tracePreserving_eq_top
#print axioms tracePreserving_normal
#print axioms substrateAutQuotient_subsingleton
#print axioms substrateAutQuotient_classes_eq
#print axioms substrateAutQuotient_no_injection_fin_two
#print axioms substrateAut_nonempty
#print axioms one_mem_tracePreserving
#print axioms substrateAutQuotient_nonempty

end SubstrateAutQuotientCollapse
end PrincipiaTractalis
