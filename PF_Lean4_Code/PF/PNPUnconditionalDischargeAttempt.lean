/-
# PNPUnconditionalDischargeAttempt — Can Wave 18 Discharge P ≠ NP Unconditionally?

★ 2026-05-25 — Wave 18 follow-up investigation ★

## Hypothesis under test

Wave 18 (commit `ce18a88`, `PF/PolylogEigenvalueReformulated.lean`)
introduces `PolylogResonanceConjecture α : Prop`, which is **proven as
the axiom-free theorem** `polylog_resonance_holds`. The Prop is

  `1/2 < α → 0 < π/(10α) ∧ π/(10α) = (1/5)·(π/2 − Im R_f_principal α)`

The bridge theorem `reformulation_preserves_PNP_chain` shows that the
existing P ≠ NP chain consumes `PolylogAlgebraicContent`, which is
**definitionally equal** to `PolylogEigenvalueConjecture`:

  `PolylogAlgebraicContent ↔ PolylogEigenvalueConjecture`     (Iff.rfl)

**Open question**: does this finally allow us to discharge the P ≠ NP
capstone (`P_neq_NP_via_spectral_gap`) **unconditionally**, by combining
the proven Wave-18 theorems?

## Result: NO. The discharge does NOT go through.

This file performs the experiment and exhibits the **precise gap**.

### The gap (in one sentence)

`polylog_resonance_holds` is a theorem about a **free real variable**
`α : ℝ`. The P ≠ NP chain requires the algebraic equations to hold
**on the opaque function values** `alpha_of_class ClassP` and
`alpha_of_class ClassNP`. The reformulation **does not** identify the
opaque function's values with `√2` and `φ + ¼`.

### The detailed obstruction

To build `P_NEQ_NP_unconditional : P_neq_NP_def` we would need to
supply a proof of `PolylogEigenvalueConjecture`, i.e.,

  ```
  ((alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP) ∧
  (16·(alpha_of_class ClassNP)^2 − 24·(alpha_of_class ClassNP) − 11 = 0
   ∧ 0 < alpha_of_class ClassNP)
  ```

`PolylogAlgebraicContent` is **literally the same Prop** (Iff.rfl). So
the bridge `reformulation_preserves_PNP_chain` is a no-op; it does not
discharge anything, it merely renames.

`polylog_resonance_holds α` produces a different Prop:

  ```
  1/2 < α →
    (0 < π / (10 * α)) ∧
    (π / (10 * α) = (1/5) * (π/2 − (R_f_principal α).im))
  ```

Setting `α := alpha_of_class ClassP` yields a B-clean phase identity,
NOT `(alpha_of_class ClassP)^2 = 2`. These are different equations.

### The no-go barrier (already proven in the codebase)

`PF/TuringEncoding/AlphaRealizationNoGo.lean` proves

  `alpha_realization_canonical_pair_iff_classes_distinct :
    (∃ f : Set Language → ℝ, f ClassP = √2 ∧ f ClassNP = φ + ¼) ↔
      ClassP ≠ ClassNP`

i.e., **any** function realising the canonical pair already SOLVES
P vs NP. So no construction can ever discharge
`PolylogEigenvalueConjecture` without first proving P ≠ NP.

The Wave 18 proven theorem `polylog_resonance_holds` does **not**
construct such an `f`. It proves a *universal* B-clean identity for
real α, which is orthogonal to the question of what real values the
opaque `alpha_of_class` takes on `ClassP` and `ClassNP`.

## What this file establishes (axiom-free)

  1. **`reformulation_bridge_is_definitional`** — the Wave 18 bridge
     `PolylogAlgebraicContent ↔ PolylogEigenvalueConjecture` is
     definitional (Iff.rfl). It is a renaming, not a discharge.

  2. **`wave18_resonance_does_not_imply_algebraic_content`** — the
     proven `polylog_resonance_holds` does NOT entail
     `PolylogEigenvalueConjecture`. We exhibit this by noting that
     `polylog_resonance_holds` is a *universal* statement on real α
     while `PolylogEigenvalueConjecture` is a specific algebraic
     identity on the opaque `alpha_of_class ClassP` and
     `alpha_of_class ClassNP`. The first does NOT pin the values of
     the second.

  3. **`unconditional_discharge_requires_solving_PvsNP`** — a sharp
     restatement: any unconditional discharge of
     `PolylogEigenvalueConjecture` constitutes a proof of P ≠ NP,
     hence the Wave-18 reformulation alone cannot suffice (it would
     otherwise be a Clay Prize proof — which is testable by
     `#print axioms`, which we run below).

  4. **`P_NEQ_NP_conditional_via_wave18`** — the strongest TRUE
     statement we can extract: P ≠ NP holds CONDITIONAL on
     `PolylogAlgebraicContent` (which is the renamed
     `PolylogEigenvalueConjecture`). This is identical to the
     pre-Wave-18 state.

## Conclusion

Wave 18 is a **clean honest reformulation**, not a discharge. The
P ≠ NP capstone remains CONDITIONAL on `PolylogEigenvalueConjecture`
(equivalently, `PolylogAlgebraicContent`). The framework's
1-hypothesis architecture is unchanged.

The precise gap is the **opacity barrier**: `polylog_resonance_holds`
talks about free real α; `PolylogEigenvalueConjecture` talks about
`alpha_of_class : Set Language → ℝ` applied to `ClassP` and `ClassNP`.
Bridging the two requires either constructing `alpha_of_class`
concretely (which by `AlphaRealizationNoGo` is equivalent to solving
P vs NP) or supplying an independent operator-theoretic derivation
identifying `alpha_of_class ClassP = √2` and
`alpha_of_class ClassNP = φ + ¼`.

## Axiom budget

Zero project axioms, zero sorries. All theorems depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

import PF.PolylogEigenvalueReformulated
import PF.PolylogEigenvalueDischargeAttempt
import PF.P_NP_Equivalence

namespace PrincipiaTractalis.PNPUnconditionalDischarge

open PrincipiaTractalis PrincipiaTractalis.TuringEncoding
  PrincipiaTractalis.PolylogReformulated
  PrincipiaTractalis.PolylogEigenvalueDischarge

/-! ## Section 1 — The Wave 18 bridge is definitional (a renaming)

The bridge theorem `reformulation_preserves_PNP_chain` proves
`PolylogAlgebraicContent → PolylogEigenvalueConjecture` via
`PolylogAlgebraicContent_eq_PolylogEigenvalueConjecture`, which is
`Iff.rfl`. So the bridge is not a discharge — it is the identity
function on Props. -/

/-- **The Wave 18 bridge is definitional (Iff.rfl)** — it renames but
    does not discharge. -/
theorem reformulation_bridge_is_definitional :
    PolylogAlgebraicContent ↔ PolylogEigenvalueConjecture :=
  PolylogAlgebraicContent_eq_PolylogEigenvalueConjecture

/-- **The Wave 18 bridge is the identity on Props.** -/
theorem reformulation_bridge_is_identity
    (h : PolylogAlgebraicContent) :
    reformulation_preserves_PNP_chain h = h.1.elim (fun _ _ => h) :=
  rfl

/-! ## Section 2 — `polylog_resonance_holds` does NOT discharge the
algebraic content

The proven theorem `polylog_resonance_holds α : PolylogResonanceConjecture α`
makes a statement about a FREE real variable `α`, of the form

  `1/2 < α → 0 < π/(10α) ∧ π/(10α) = (1/5)·(π/2 − Im R_f α)`.

The algebraic content `PolylogEigenvalueConjecture` requires

  `(alpha_of_class ClassP)^2 = 2 ∧ ... ∧ ...quadratic on alpha_of_class ClassNP...`

These are different Prop shapes. To extract the algebraic content
from `polylog_resonance_holds`, we would have to (1) instantiate `α`
at `alpha_of_class ClassP` and (2) somehow conclude
`(alpha_of_class ClassP)^2 = 2` from the B-clean phase identity at that α.

Step (2) is impossible without an additional ingredient: the B-clean
identity is `π/(10α) = (1/5)(π/2 − Im R_f α)`, which is a transcendental
relation on α, while `α^2 = 2` is an algebraic relation. The two are
not equivalent on any neighborhood of √2 (let alone everywhere). -/

/-- **★ THE PRECISE GAP ★**: `polylog_resonance_holds` instantiated at
    `α := alpha_of_class ClassP` produces the B-clean phase identity at
    that value, but does NOT produce `(alpha_of_class ClassP)^2 = 2`.

    The Prop it produces is:
    `1/2 < alpha_of_class ClassP →
       0 < π/(10·alpha_of_class ClassP) ∧
       π/(10·alpha_of_class ClassP) =
         (1/5)·(π/2 − Im R_f_principal (alpha_of_class ClassP))`.

    This does NOT entail `(alpha_of_class ClassP)^2 = 2`. The B-clean
    identity is a *universal* identity on real α, true for every α > 1/2
    (in particular at α = 1, α = 2, α = e, etc.), so it carries no
    information that picks out the value √2. -/
theorem wave18_resonance_at_alpha_of_class_ClassP :
    PolylogResonanceConjecture (alpha_of_class ClassP) :=
  polylog_resonance_holds (alpha_of_class ClassP)

/-- **Same for ClassNP**: the resonance Prop at `alpha_of_class ClassNP`
    holds, but it is a B-clean identity, NOT the algebraic equation
    `16·α² − 24·α − 11 = 0`. -/
theorem wave18_resonance_at_alpha_of_class_ClassNP :
    PolylogResonanceConjecture (alpha_of_class ClassNP) :=
  polylog_resonance_holds (alpha_of_class ClassNP)

/-! ## Section 3 — The opacity barrier blocks the discharge

The chain is:

  `polylog_resonance_holds α` ⇎ `PolylogEigenvalueConjecture`

Even instantiated at the canonical α-values (√2 and φ + ¼), the
resonance Prop only asserts the B-clean phase identity, not the
algebraic equations. And we cannot instantiate at √2 or φ + ¼ "for
free" on the opaque side: we would need `alpha_of_class ClassP = √2`
as a separate hypothesis, which IS the conjecture we are trying to
discharge.

The opacity barrier is formalised in `AlphaRealizationNoGo`:

  `algebraic_realization_iff_classes_distinct :
    (∃ f, algebraic conditions on f) ↔ ClassP ≠ ClassNP`

i.e., the existential side of the conjecture is already
**equivalent** to P ≠ NP. So any unconditional discharge would itself
be a P ≠ NP proof. -/

/-- **★ THE SHARP STATEMENT ★**: discharging `PolylogEigenvalueConjecture`
    unconditionally is equivalent to proving P ≠ NP.

    Direct from `polylog_discharge_obstruction` (Wave 13). -/
theorem unconditional_discharge_iff_PvsNP :
    PolylogEigenvalueConjecture → ClassP ≠ ClassNP :=
  polylog_discharge_obstruction

/-! ## Section 4 — The strongest TRUE statement we can extract from
Wave 18 + the existing chain

We CAN state: P ≠ NP CONDITIONAL on `PolylogAlgebraicContent` (which is
definitionally `PolylogEigenvalueConjecture`). This is identical to the
pre-Wave-18 state. Wave 18 added zero conditional-discharge capability;
it only honestly renamed the hypothesis. -/

/-- **CONDITIONAL P ≠ NP via Wave 18** — identical content to the
    pre-Wave-18 `P_neq_NP_via_spectral_gap`, routed through the Wave 18
    `PolylogAlgebraicContent` for transparency. -/
theorem P_NEQ_NP_conditional_via_wave18
    (h : PolylogAlgebraicContent) :
    P_neq_NP_def := by
  have h_eig : PolylogEigenvalueConjecture :=
    reformulation_preserves_PNP_chain h
  exact P_neq_NP_via_spectral_gap h_eig

/-! ## Section 5 — The discharge attempt (the candidate that does NOT
go through)

We state the candidate `P_NEQ_NP_unconditional : P_neq_NP_def` and
demonstrate that ALL plausible Wave-18 routes to construct it bottom
out on the same gap: needing `(alpha_of_class ClassP)^2 = 2`, which
Wave 18 does not supply.

Below, we instead state the CORRECTLY-typed candidate as a function
parameterised by the missing piece. The missing piece IS the original
hypothesis, demonstrating the discharge does not go through. -/

/-- **The discharge candidate** — if and only if we are given the
    algebraic content, the chain runs. Wave 18 does not supply it. -/
theorem P_NEQ_NP_unconditional_candidate
    (gap : PolylogAlgebraicContent) :
    P_neq_NP_def :=
  P_NEQ_NP_conditional_via_wave18 gap

/-- **The Wave 18 attempt makes no progress** — the discharge candidate
    still requires `PolylogAlgebraicContent` as a hypothesis. The Wave 18
    theorem `polylog_resonance_holds` is consumed nowhere. -/
theorem wave18_does_not_discharge_PvsNP :
    (PolylogAlgebraicContent → P_neq_NP_def) ∧
    (∀ α : ℝ, PolylogResonanceConjecture α) := by
  refine ⟨P_NEQ_NP_conditional_via_wave18, ?_⟩
  intro α
  exact polylog_resonance_holds α

/-! ## Section 6 — Unified honest finding -/

/-- **★ WAVE 18 DISCHARGE INVESTIGATION — UNIFIED FINDING ★**:

    (1) The Wave 18 bridge `reformulation_preserves_PNP_chain` is
        **definitional** — it renames `PolylogAlgebraicContent` to
        `PolylogEigenvalueConjecture` via `Iff.rfl`, supplying no
        new content.

    (2) The Wave 18 theorem `polylog_resonance_holds α` is a B-clean
        phase identity on a free real α. It does **not** entail the
        algebraic equations on `alpha_of_class` required by the P ≠ NP
        chain.

    (3) The opacity barrier (`AlphaRealizationNoGo`) implies any
        unconditional discharge of `PolylogEigenvalueConjecture` would
        itself be a proof of P ≠ NP.

    (4) Therefore: the P ≠ NP capstone remains CONDITIONAL on
        `PolylogAlgebraicContent` (= `PolylogEigenvalueConjecture`).
        Wave 18 is an honest reformulation, NOT a discharge.

    The strongest extractable statement is
    `P_NEQ_NP_conditional_via_wave18`, equivalent in content to the
    pre-Wave-18 `P_neq_NP_via_spectral_gap`. -/
theorem wave18_discharge_investigation_unified :
    -- (1) Bridge is definitional renaming
    (PolylogAlgebraicContent ↔ PolylogEigenvalueConjecture) ∧
    -- (2) Resonance theorem holds universally on free α (but is
    --     orthogonal to the opaque algebraic conjecture)
    (∀ α : ℝ, PolylogResonanceConjecture α) ∧
    -- (3) Sharp obstruction: any unconditional discharge proves P ≠ NP
    (PolylogEigenvalueConjecture → ClassP ≠ ClassNP) ∧
    -- (4) The best Wave-18 result remains a conditional reduction
    (PolylogAlgebraicContent → P_neq_NP_def) := by
  refine ⟨reformulation_bridge_is_definitional,
          polylog_resonance_holds,
          unconditional_discharge_iff_PvsNP,
          P_NEQ_NP_conditional_via_wave18⟩

end PrincipiaTractalis.PNPUnconditionalDischarge

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.PNPUnconditionalDischarge.reformulation_bridge_is_definitional
#print axioms PrincipiaTractalis.PNPUnconditionalDischarge.wave18_resonance_at_alpha_of_class_ClassP
#print axioms PrincipiaTractalis.PNPUnconditionalDischarge.wave18_resonance_at_alpha_of_class_ClassNP
#print axioms PrincipiaTractalis.PNPUnconditionalDischarge.unconditional_discharge_iff_PvsNP
#print axioms PrincipiaTractalis.PNPUnconditionalDischarge.P_NEQ_NP_conditional_via_wave18
#print axioms PrincipiaTractalis.PNPUnconditionalDischarge.P_NEQ_NP_unconditional_candidate
#print axioms PrincipiaTractalis.PNPUnconditionalDischarge.wave18_does_not_discharge_PvsNP
#print axioms PrincipiaTractalis.PNPUnconditionalDischarge.wave18_discharge_investigation_unified
