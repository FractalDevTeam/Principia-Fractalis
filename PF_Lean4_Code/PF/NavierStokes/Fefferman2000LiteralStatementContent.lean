/-
# What the "literal Clay NS statement" Prop actually contains — kernel-visible

2026-11-03. **Additive. Nothing is renamed, weakened or withdrawn.** Every
declaration in `Fefferman2000_LiteralClayNS3D_Statement_2026_06_19` is left
byte-identical, and every theorem in it remains true.

This file does for the Fefferman-2000 literal-statement module exactly what
`PF/NavierStokesTypedContent_r215.lean` did for `NS_Solution`: it turns a prose
reading into kernel facts, so the reader does not have to take anyone's word
for what the Props say. `ch22`'s "External Settlement" section already carries
the r215 results and cites them by name; this closes the same gap one level up,
on the module whose *name* promises the Clay statement.

## Why this file exists

`ch22` discloses the typed layer's content in the manuscript, and does it well.
But a referee clones the Lean corpus and greps it. Prose in a 1083-page book
does not travel with a `git clone`. The disclosure has to be in the kernel, next
to the definitions, or it is not where it will be looked for.

## What is measured here

The module's four Clay clauses, as written:

```
IsLiteralDivergenceFree u_0 := ∀ ξ, (∑ i : Fin 3, (1:ℝ)) ≥ 0 ∧ u_0 = u_0
HasBoundedEnergy        u   := ∃ C, C ≥ 0 ∧ ∀ t, 0 ≤ t → C ≥ 0
SatisfiesLiteralNSE   u _p _ν := ∀ t, 0 ≤ t → u t = u t
MatchesInitialDatum    u u_0 := u 0 = u_0
```

* `IsLiteralDivergenceFree` is `3 ≥ 0 ∧ u_0 = u_0`. It holds for **every**
  `u_0`, divergence-free or not. Its own source comment says "placeholder
  structural Prop".
* `HasBoundedEnergy` never mentions `u` after the binder: `C := 0` discharges
  it. It holds for every field and cannot distinguish two.
* `SatisfiesLiteralNSE` is `u t = u t` — reflexivity — with the pressure and
  the viscosity discarded by `_p` and `_ν`. **The momentum equation
  `∂_t u + (u·∇)u + ∇p = ν Δu` quoted in its docstring does not appear in it.**
* `MatchesInitialDatum` is the only clause that constrains `u`.

So the whole statement reduces to *"for every `u_0` there is a time-dependent
field whose value at `t = 0` is `u_0`"*, and the constant field
`fun _ => u_0` witnesses it. §2 proves that:
`clay_literal_NS3D_statement_holds` closes
`Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000` outright, with a
time-independent witness, zero pressure and `ν = 1`.

**A six-line proof of a Prop named for a Millennium Problem is the proof that
the Prop is not that problem.** That is the whole content of this file, and it
is the strongest available form of the disclosure: not a complaint, a theorem.

§2 also shows the five-anchor bridge needs no anchors —
`substrate_forces_literal_clay_NS_bridge_holds` discharges
`Substrate_Forces_Literal_Clay_NS_Bridge` while discarding all five
published-mathematics hypotheses — which is why
`substrate_to_literal_clay_NS_bridge_conditional` can be the identity function
on its own hypothesis.

## What is NOT claimed, explicitly

Following r215's register: **this is a reading, not a refutation.** Every
theorem in the Fefferman module is true, and so is every theorem here. Nothing
below says anything whatever about the Navier–Stokes problem — not that global
regularity holds, not that it fails, not that it is closer or further. The Clay
problem is untouched, exactly as `ch22` records. Nor does anything here bear on
the 2026 external results, which concern the **forced** equation while Fefferman
statement (B) is the **unforced** one.

And it does not touch the 31-file `PF/NavierStokes/FujitaKato1964/` layer, which
contains real mathematics — Leray-projector Fourier symbols and their
idempotence, heat-semigroup multipliers, convective-derivative components,
Schwartz and Sobolev machinery — with zero `sorry` and zero `: True`. The
defect is localised to these four Props, and a reading that smeared that layer
would itself be an error.

Zero project axioms. Author: Pablo Cohen + Claude Opus 5. 2026-11-03.
-/

import PF.NavierStokes.Fefferman2000_LiteralClayNS3D_Statement_2026_06_19
import Mathlib.Tactic

namespace PrincipiaTractalis.Fefferman2000LiteralStatementContent

open PF.NavierStokes.Fefferman2000_LiteralClayNS3D_Statement_2026_06_19

/-! ## §1 — The four clauses, clause by clause -/

/-- **`IsLiteralDivergenceFree` holds at every initial field.** It unfolds to
    `3 ≥ 0 ∧ u_0 = u_0`, so it does not test divergence. -/
theorem isLiteralDivergenceFree_trivial (u_0 : LiteralNSInitialField) :
    IsLiteralDivergenceFree u_0 :=
  fun _ => ⟨by norm_num, rfl⟩

/-- **…hence it is equivalent to `True`.** Stated so the kernel, not the
    reader, certifies it. -/
theorem isLiteralDivergenceFree_iff_true (u_0 : LiteralNSInitialField) :
    IsLiteralDivergenceFree u_0 ↔ True :=
  ⟨fun _ => trivial, fun _ => isLiteralDivergenceFree_trivial u_0⟩

/-- **`HasBoundedEnergy` holds at every field**, witnessed by `C = 0`. -/
theorem hasBoundedEnergy_trivial (u : LiteralNSTimeDependentField) :
    HasBoundedEnergy u :=
  ⟨0, le_refl 0, fun _ _ => le_refl 0⟩

/-- …hence equivalent to `True`. -/
theorem hasBoundedEnergy_iff_true (u : LiteralNSTimeDependentField) :
    HasBoundedEnergy u ↔ True :=
  ⟨fun _ => trivial, fun _ => hasBoundedEnergy_trivial u⟩

/-- **`HasBoundedEnergy` cannot distinguish two fields** — `u` does not occur
    in its body after the binder, so no energy of any field is constrained. -/
theorem hasBoundedEnergy_blind_to_the_field
    (u v : LiteralNSTimeDependentField) :
    HasBoundedEnergy u ↔ HasBoundedEnergy v :=
  ⟨fun _ => hasBoundedEnergy_trivial v, fun _ => hasBoundedEnergy_trivial u⟩

/-- **`SatisfiesLiteralNSE` holds at every field, pressure and viscosity.**
    It unfolds to `∀ t ≥ 0, u t = u t`. The momentum equation in its docstring
    is not in its statement. -/
theorem satisfiesLiteralNSE_trivial
    (u : LiteralNSTimeDependentField) (p : LiteralNSPressureField) (ν : ℝ) :
    SatisfiesLiteralNSE u p ν :=
  fun _ _ => rfl

/-- …hence equivalent to `True`. -/
theorem satisfiesLiteralNSE_iff_true
    (u : LiteralNSTimeDependentField) (p : LiteralNSPressureField) (ν : ℝ) :
    SatisfiesLiteralNSE u p ν ↔ True :=
  ⟨fun _ => trivial, fun _ => satisfiesLiteralNSE_trivial u p ν⟩

/-- **★ The momentum clause is blind to the pressure and the viscosity. ★**
    Both are discarded by the `_p` and `_ν` binders, so no choice of either
    can fail it — and a Navier–Stokes momentum equation must constrain both. -/
theorem satisfiesLiteralNSE_blind_to_pressure_and_viscosity
    (u : LiteralNSTimeDependentField)
    (p q : LiteralNSPressureField) (ν μ : ℝ) :
    SatisfiesLiteralNSE u p ν ↔ SatisfiesLiteralNSE u q μ :=
  ⟨fun _ => satisfiesLiteralNSE_trivial u q μ,
   fun _ => satisfiesLiteralNSE_trivial u p ν⟩

/-! ## §2 — ★ THE LITERAL CLAY STATEMENT IS A THEOREM ★ -/

/-- **★★ `Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000` holds. ★★**

    Witness: the **time-independent** field `fun _ => u_0`, zero pressure, and
    `ν = 1`. Three of the four clauses are tautologies and the fourth,
    `MatchesInitialDatum`, is satisfied by `rfl`.

    A Prop named for a Millennium Problem that closes in six lines is not that
    problem. This theorem is the disclosure, in the strongest form available. -/
theorem clay_literal_NS3D_statement_holds :
    Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000 :=
  fun u_0 _ =>
    ⟨fun _ => u_0, fun _ => 0, 1, by norm_num, rfl,
     satisfiesLiteralNSE_trivial _ _ _, hasBoundedEnergy_trivial _⟩

/-- …hence equivalent to `True`. -/
theorem clay_literal_NS3D_statement_iff_true :
    Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000 ↔ True :=
  ⟨fun _ => trivial, fun _ => clay_literal_NS3D_statement_holds⟩

/-- **★ The five-anchor bridge needs no anchors. ★**

    `Substrate_Forces_Literal_Clay_NS_Bridge` is discharged while discarding
    Fujita–Kato, Leray, Sobolevskii, Beale–Kato–Majda and
    Caffarelli–Kohn–Nirenberg, because its conclusion holds unconditionally.
    That is why `substrate_to_literal_clay_NS_bridge_conditional` can be the
    identity function on its own hypothesis. -/
theorem substrate_forces_literal_clay_NS_bridge_holds :
    Substrate_Forces_Literal_Clay_NS_Bridge :=
  fun _ _ _ _ _ => clay_literal_NS3D_statement_holds

/-! ## §3 — The witness requires no time evolution -/

/-- **★ A field constant in time satisfies every clause. ★**

    The statement asks for a solution of an evolution equation; a field that
    does not evolve meets it. This is the precise sense in which the Props
    contain no dynamics. -/
theorem constant_field_satisfies_every_clause (u_0 : LiteralNSInitialField) :
    MatchesInitialDatum (fun _ => u_0) u_0 ∧
    SatisfiesLiteralNSE (fun _ => u_0) (fun _ => 0) 1 ∧
    HasBoundedEnergy (fun _ => u_0) ∧
    IsLiteralDivergenceFree u_0 :=
  ⟨rfl, satisfiesLiteralNSE_trivial _ _ _, hasBoundedEnergy_trivial _,
   isLiteralDivergenceFree_trivial u_0⟩

/-- **`MatchesInitialDatum` is the only clause that constrains the field.** It
    is not a tautology: it pins `u 0`, and two fields differing at `0` cannot
    both satisfy it for the same datum. -/
theorem matchesInitialDatum_is_not_trivial
    (u : LiteralNSTimeDependentField) (u_0 : LiteralNSInitialField)
    (h : MatchesInitialDatum u u_0) :
    u 0 = u_0 := h

/-! ## §4 — Capstone -/

/-- The disclosure, bundled for citation. -/
structure LiteralClayNSContentDisclosure : Prop where
  /-- The divergence-free clause holds at every field. -/
  div_free_is_free : ∀ u_0, IsLiteralDivergenceFree u_0 ↔ True
  /-- The energy clause holds at every field. -/
  energy_is_free : ∀ u, HasBoundedEnergy u ↔ True
  /-- The energy clause cannot distinguish two fields. -/
  energy_blind : ∀ u v, HasBoundedEnergy u ↔ HasBoundedEnergy v
  /-- The momentum clause holds at every field, pressure and viscosity. -/
  momentum_is_free : ∀ u p ν, SatisfiesLiteralNSE u p ν ↔ True
  /-- The momentum clause is blind to pressure and viscosity. -/
  momentum_blind : ∀ u p q ν μ,
    SatisfiesLiteralNSE u p ν ↔ SatisfiesLiteralNSE u q μ
  /-- The literal Clay statement is a theorem. -/
  clay_statement_holds : Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000
  /-- The five-anchor bridge needs no anchors. -/
  bridge_needs_no_anchors : Substrate_Forces_Literal_Clay_NS_Bridge

/-- **★★ THE DISCLOSURE ★★** — every clause-level fact above, in one citable
    theorem.

    **A reading, not a refutation**: each theorem in the Fefferman module is
    true, and each theorem here is true. Explicitly NOT claimed: anything at
    all about the Navier–Stokes problem. The Clay problem is untouched, as
    `ch22` records; and the 2026 external blow-up results concern the
    **forced** equation, while Fefferman statement (B) is the **unforced**
    one. -/
theorem literal_clay_NS_content_disclosure : LiteralClayNSContentDisclosure :=
  { div_free_is_free := isLiteralDivergenceFree_iff_true
    energy_is_free := hasBoundedEnergy_iff_true
    energy_blind := hasBoundedEnergy_blind_to_the_field
    momentum_is_free := satisfiesLiteralNSE_iff_true
    momentum_blind := satisfiesLiteralNSE_blind_to_pressure_and_viscosity
    clay_statement_holds := clay_literal_NS3D_statement_holds
    bridge_needs_no_anchors := substrate_forces_literal_clay_NS_bridge_holds }

end PrincipiaTractalis.Fefferman2000LiteralStatementContent

/-! ## Axiom audit — LIVE -/

#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.isLiteralDivergenceFree_trivial
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.isLiteralDivergenceFree_iff_true
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.hasBoundedEnergy_trivial
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.hasBoundedEnergy_iff_true
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.hasBoundedEnergy_blind_to_the_field
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.satisfiesLiteralNSE_trivial
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.satisfiesLiteralNSE_iff_true
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.satisfiesLiteralNSE_blind_to_pressure_and_viscosity
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.clay_literal_NS3D_statement_holds
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.clay_literal_NS3D_statement_iff_true
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.substrate_forces_literal_clay_NS_bridge_holds
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.constant_field_satisfies_every_clause
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.matchesInitialDatum_is_not_trivial
#print axioms PrincipiaTractalis.Fefferman2000LiteralStatementContent.literal_clay_NS_content_disclosure
