/-
# Hodge substrate markers and the Hardy/Odlyzko anchors — what they are, in the kernel

**Date**: 2026-11-23 (Legion).

## Why this file exists

The 2026-11-21 vacuity triage classified 259 `Prop := True` declarations into
8 ASSERTED, 165 conjoined and 86 correctly-scoped bibliography. Its instrument
captures declaration names with `(\w+)`, which **cannot match a dotted name**.
Seven declarations of the form

```lean
def <Namespace>.<Structure>.<field> (_X : <Structure>) : Prop := True
```

were therefore structurally invisible to it. Each has a `*_holds` companion
discharged by `trivial`, which is exactly the triage's own ASSERTED pattern, and
five are carried as conjuncts of capstones. The true ASSERTED count is **15, not
8**.

This file makes each of the seven say what it is, in the kernel, so no future
scanner — and no reader — has to infer it.

## What is NOT wrong here

**Every one of these seven has an honest docstring.** They say "Prop-level
marker", "recorded as `True`", "definitionally", and the CY3 one states its
reason outright: "we lack mathlib's `CanonicalBundle` infrastructure, so we
record this as `True`". Nothing was concealed. The defect is that the *theorem
names* and the *capstone conjunct lists* do not inherit that honesty, so a
reader meeting

```
hodge_axis_framework_level_millennium_answer     (Hodge_FrameworkMillenniumAnswer.lean:57)
```

at conjunct `X.canonical_trivial` (line 85) sees a theorem titled "FRAMEWORK-LEVEL
HODGE MILLENNIUM ANSWER" appearing to establish that every Calabi-Yau 3-fold
substrate has trivial canonical bundle, `K_X ≃ 𝒪_X`. The same marker rides inside
`Hodge_bulletproof_substrate_closure` (`Hodge_SubstrateBulletproofClosure.lean:27`,
conjunct at line 46) under the banner "BULLETPROOF", and in
`Wave18MasterCapstone.lean:465`.

`poincareDual_h` likewise makes `h^{2,2} = h^{1,1}` look established
(`HodgeCalabiYau3FoldDim22Substrate.lean:350, :436, :499, :546`,
`Wave21MasterCapstone.lean:233`); `is_uniruled` makes the substrate look proved
uniruled (`HodgeCodim2UniruledThreefoldVoisin2018Attempt.lean:662, :680`).

## The removal condition, MEASURED not asserted

These are `True` because mathlib at this pin cannot express the statements. Grep
over `.lake/packages/mathlib/Mathlib` at `v4.24.0-rc1`, count of files mentioning
each identifier:

| identifier | files |
|---|---|
| `canonicalBundle` | 0 |
| `CanonicalBundle` | 0 |
| `canonicalDivisor` | 0 |
| `CalabiYau` | 0 |
| `HodgeDecomposition` | 0 |
| `HodgeStructure` | 0 |
| `AlgebraicCycle` | 0 |
| `ChowGroup` | 0 |
| `PoincareDuality` / `poincareDuality` | 0 |

So these markers are **not** repairable by renaming or by a cleverer proof: each
needs upstream mathlib geometry that does not exist yet. `KaehlerDifferential`
(17 files) is the only nearby primitive. That is the exit condition — when a
canonical-sheaf API lands, `canonical_trivial` becomes statable and these
disclosures should be replaced by the real content, not merely deleted.

## The Hardy/Odlyzko anchors

`PF/Analytic/Hardy1914_NonemptyZetaOnLineZeros_Anchor.lean` defines

```lean
def Hardy1914_OnLineZetaZerosInfinite_Anchor : Prop := True   -- :134
def Riemann_FirstZero_Verified_Anchor        : Prop := True   -- :166
```

and then, under docstrings reading **"★★★★★ SUBSTRATE-LEVEL DISCHARGE of atomic
fact (b) ★★★★★"**:

```lean
theorem hardy1914_anchor_yields_nonempty_substrate_implication    -- :234
    (_h : Hardy1914_OnLineZetaZerosInfinite_Anchor) :
    Hardy1914_OnLineZetaZerosInfinite_Anchor := _h
```

The conclusion is the **anchor**, not the atomic fact
`PositiveOnLineZetaZeroOrdinatesNonempty` the docstring names. Both theorems are
the identity function on `True`. The 2026-11-21 repair
(`PF/Analytic/Hardy1914_Faithful_2026_11_21.lean`) was additive and left these in
place, so they are still the declarations a reader finds first.

## Scope

**Nothing is renamed, weakened, withdrawn or deleted.** No new mathematics is
claimed: every theorem below is `rfl` or `trivial` on a definitional unfolding.
That is the point — a `rfl` is the strongest possible evidence that a marker
carries no content, because it says the marker *is* the constant.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-23.
-/

import PF.HodgeCalabiYau3FoldSubstrate
import PF.HodgeCalabiYau3FoldDim22Substrate
import PF.HodgeCodim2UniruledThreefoldVoisin2018Attempt
import PF.HodgeCodim2AbelianThreefoldEscapeAttempt
import PF.HodgeDim4CY4Substrate
import PF.HodgeCodim2CmAbelian5FoldAttempt
import PF.HodgeCodim2CmAbelian6FoldAttempt
import PF.Analytic.Hardy1914_NonemptyZetaOnLineZeros_Anchor

namespace PF.Referee.HodgeMarkerAndAnchorDisclosure

open PrincipiaTractalis.HodgeCalabiYau3Fold (HodgeCalabiYau3FoldSubstrate)
open PrincipiaTractalis.HodgeCalabiYau3FoldDim22 (HodgeCY3Dim22Substrate)
open PrincipiaTractalis.HodgeCodim2UniruledThreefoldVoisin2018Attempt
  (UniruledThreefoldCodim2Substrate)
open PrincipiaTractalis.HodgeCodim2AbelianThreefoldEscape (Abelian3FoldDim22Substrate)
open PrincipiaTractalis.HodgeDim4CY4 (HodgeCY4Substrate)
open PrincipiaTractalis.HodgeCodim2CmAbelian5FoldAttempt (CmAbelian5FoldCodim2Substrate)
open PrincipiaTractalis.HodgeCodim2CmAbelian6FoldAttempt (CmAbelian6FoldCodim2Substrate)

/-! ## §1 — The seven dotted-name markers ARE the constant `True`

Each theorem states that the marker, **as a function**, equals `fun _ => True`.
That is strictly stronger than "it holds for every substrate": it says the
marker cannot distinguish any two substrates whatsoever, because it does not
look at its argument. -/

/-- `K_X ≃ 𝒪_X` on a Calabi-Yau 3-fold substrate is the constant `True`. -/
theorem cy3_canonical_trivial_is_const_true :
    HodgeCalabiYau3FoldSubstrate.canonical_trivial = fun _ => True := rfl

/-- Poincaré duality `h^{2,2} = h^{1,1}` on a CY3 `(2,2)`-substrate is the
    constant `True`. -/
theorem cy3dim22_poincareDual_h_is_const_true :
    HodgeCY3Dim22Substrate.poincareDual_h = fun _ => True := rfl

/-- Uniruledness of the codim-2 threefold substrate is the constant `True`. -/
theorem uniruled_is_uniruled_is_const_true :
    UniruledThreefoldCodim2Substrate.is_uniruled = fun _ => True := rfl

/-- Mumford/Weil algebraicity on an abelian-3-fold substrate is the constant
    `True`. The docstring correctly cites Mumford, Weil 1977 and
    Birkenhake-Lange §17.5 as establishing this classically; what is recorded
    here is that the *corpus* does not. -/
theorem abelian3fold_Mumford_algebraicity_is_const_true :
    Abelian3FoldDim22Substrate.Mumford_algebraicity = fun _ => True := rfl

/-- `K_X ≃ 𝒪_X` on a Calabi-Yau 4-fold substrate is the constant `True`. -/
theorem cy4_canonical_trivial_is_const_true :
    HodgeCY4Substrate.canonical_trivial = fun _ => True := rfl

/-- `K_X ≃ 𝒪_X` on the CM abelian 5-fold substrate is the constant `True`. -/
theorem cm5_canonical_trivial_is_const_true :
    CmAbelian5FoldCodim2Substrate.canonical_trivial = fun _ => True := rfl

/-- `K_X ≃ 𝒪_X` on the CM abelian 6-fold substrate is the constant `True`. -/
theorem cm6_canonical_trivial_is_const_true :
    CmAbelian6FoldCodim2Substrate.canonical_trivial = fun _ => True := rfl

/-! ## §2 — Therefore the capstone conjuncts carrying them are free

`hodge_axis_framework_level_millennium_answer`'s conjunct (H7) includes
`X.canonical_trivial`; `Hodge_bulletproof_substrate_closure`'s conjunct at line
46 is the same. These hold for every substrate with no hypothesis, so they
cannot be evidence about any particular variety. -/

theorem cy3_canonical_trivial_free (X : HodgeCalabiYau3FoldSubstrate) :
    X.canonical_trivial := trivial

theorem cy3dim22_poincareDual_h_free (X : HodgeCY3Dim22Substrate) :
    X.poincareDual_h := trivial

theorem uniruled_is_uniruled_free (X : UniruledThreefoldCodim2Substrate) :
    X.is_uniruled := trivial

/-! ## §3 — The Hardy/Odlyzko anchors are `True`, and their "discharges" are
`True → True` -/

open PrincipiaTractalis.Hardy1914_NonemptyZetaOnLineZeros_Anchor
  (Hardy1914_OnLineZetaZerosInfinite_Anchor Riemann_FirstZero_Verified_Anchor)

theorem hardy1914_anchor_is_True :
    Hardy1914_OnLineZetaZerosInfinite_Anchor = True := rfl

theorem riemann_firstzero_anchor_is_True :
    Riemann_FirstZero_Verified_Anchor = True := rfl

/-- **The ★★★★★ "substrate-level discharge" has type `True → True`.**

    `hardy1914_anchor_yields_nonempty_substrate_implication` is
    `(_h : A) : A := _h` with `A = True`, so its type is literally
    `True → True`. It discharges nothing; in particular it does not conclude
    `PositiveOnLineZetaZeroOrdinatesNonempty`, which is the atomic fact its
    docstring names. -/
theorem hardy1914_discharge_type_is_True_imp_True :
    (Hardy1914_OnLineZetaZerosInfinite_Anchor →
      Hardy1914_OnLineZetaZerosInfinite_Anchor) = (True → True) := rfl

/-- Same for the Odlyzko first-zero anchor. -/
theorem odlyzko_discharge_type_is_True_imp_True :
    (Riemann_FirstZero_Verified_Anchor →
      Riemann_FirstZero_Verified_Anchor) = (True → True) := rfl

/-! ## §4 — One citable bundle -/

/-- **`hodge_markers_and_anchors_disclosed`** — the nine facts above in one
theorem, for a referee who wants a single citation.

Seven Hodge substrate markers are the constant `True`; both RH typed anchors
are `True`. Every component is `rfl`. Nothing here claims mathematics; it
records, in the kernel, the content of declarations whose names suggest more
than they carry, and §"removal condition" in this file's header states exactly
what upstream mathlib work would let them be replaced by real statements. -/
theorem hodge_markers_and_anchors_disclosed :
    (HodgeCalabiYau3FoldSubstrate.canonical_trivial = fun _ => True) ∧
    (HodgeCY3Dim22Substrate.poincareDual_h = fun _ => True) ∧
    (UniruledThreefoldCodim2Substrate.is_uniruled = fun _ => True) ∧
    (Abelian3FoldDim22Substrate.Mumford_algebraicity = fun _ => True) ∧
    (HodgeCY4Substrate.canonical_trivial = fun _ => True) ∧
    (CmAbelian5FoldCodim2Substrate.canonical_trivial = fun _ => True) ∧
    (CmAbelian6FoldCodim2Substrate.canonical_trivial = fun _ => True) ∧
    (Hardy1914_OnLineZetaZerosInfinite_Anchor = True) ∧
    (Riemann_FirstZero_Verified_Anchor = True) :=
  ⟨cy3_canonical_trivial_is_const_true,
   cy3dim22_poincareDual_h_is_const_true,
   uniruled_is_uniruled_is_const_true,
   abelian3fold_Mumford_algebraicity_is_const_true,
   cy4_canonical_trivial_is_const_true,
   cm5_canonical_trivial_is_const_true,
   cm6_canonical_trivial_is_const_true,
   hardy1914_anchor_is_True,
   riemann_firstzero_anchor_is_True⟩

end PF.Referee.HodgeMarkerAndAnchorDisclosure

/-! ## §Axiom audit -/
#print axioms PF.Referee.HodgeMarkerAndAnchorDisclosure.cy3_canonical_trivial_is_const_true
#print axioms PF.Referee.HodgeMarkerAndAnchorDisclosure.cy3dim22_poincareDual_h_is_const_true
#print axioms PF.Referee.HodgeMarkerAndAnchorDisclosure.hardy1914_discharge_type_is_True_imp_True
#print axioms PF.Referee.HodgeMarkerAndAnchorDisclosure.hodge_markers_and_anchors_disclosed
