/-
# PF.Referee.HodgeCapstoneTypedBridge

**Date**: 2026-06-02
**Status**: dim-2 substrate-level typed bridge with honest-scope flagging.
**Anchor commit**: bd00393.
**Source roadmap**: `codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md`
"Current Frontier Ledger" → Hodge row + "First Algebraic-Geometry
Attack: Hodge".

## Purpose

PF's strongest axiom-free Hodge content at HEAD bd00393 spans curve,
K3, abelian surface, general surface, CY3 (2,2)-slice, and CY4
(1,1)/(2,2)/(3,3)-slices — all substrate-level. The cleanest single
combined master is `hodge_full_dim_one_and_dim_two_capstone`
(PF/HodgeGeneralSurfaceDim2Substrate.lean) which bundles
curve + K3 + abelian + general surface, all under
`HodgeAlgebraicRepresentation X.toHodgeAmbient class_idx`.

Critically, `HodgeAlgebraicRepresentation` is NOT `Prop := True` at
the substrate level — it is a genuine 3-conjunct existential
predicate over framework-anchored constants (σ, rank-bound, λ from
Wave 6).

This module wires the dim-2 general-surface clause of
`hodge_full_dim_one_and_dim_two_capstone` to a typed
`Clay_Hodge_Standard` contract under an encoding restricted to PF's
`HodgeGeneralSurfaceSubstrate` ambient. The bridge is a REAL theorem
under a restricted encoding.

## Honest scope (foregrounded)

The encoding restricts `SmoothProjectiveComplexVariety` to PF's
`HodgeGeneralSurfaceSubstrate` (smooth projective complex surfaces
at the substrate level). The `isAlgebraic` predicate is PF's
`HodgeAlgebraicRepresentation`, a real 3-conjunct substrate-level
predicate — NOT the literal geometric algebraicity of cycles.

The full Clay Hodge statement on arbitrary smooth projective complex
varieties at codimension >= 2 remains open via the named Props
`VoisinObstructionAtCodimTwoCY3` (Wave 33) and
`Voisin2007_general_quintic_open_subprop` (Wave 57). The Wave 57
Dwork-pencil closure (axiom-free, substrate-level) is a polished
partial result; this bridge does NOT extend it to general smooth
quintic.
-/

import PF.HodgeGeneralSurfaceDim2Substrate
import PF.Hodge_QuinticCYCodim2Scaffold
import PF.AlgebraicGeometry.CycleClassMapAtCodim2Attempt
import PF.Referee.StandardClayStatements

namespace PF.Referee.HodgeCapstoneTypedBridge

open PrincipiaTractalis
open PrincipiaTractalis.HodgeGeneralSurfaceDim2
open PrincipiaTractalis.MillenniumSix
open PrincipiaTractalis.AlgebraicGeometry

/-! ## §1 — Concrete standard-encoding instance from PF's general-surface substrate -/

/-- The standard Hodge encoding instantiated at PF's general smooth
    projective complex surface substrate.
    `SmoothProjectiveComplexVariety := HodgeGeneralSurfaceSubstrate`.
    `RationalHodgeClass` is `ℕ` (the framework's `class_idx`
    parameter — PF does not yet carry a literal rational-Hodge-class
    type). `isAlgebraic` is PF's 3-conjunct substrate-level
    `HodgeAlgebraicRepresentation`, NOT a `Prop := True` placeholder. -/
def PF_HodgeEncoding :
    PF.Referee.StandardClayStatements.StandardHodgeEncoding where
  SmoothProjectiveComplexVariety := HodgeGeneralSurfaceSubstrate
  RationalHodgeClass _ := ℕ
  isAlgebraic X c := HodgeAlgebraicRepresentation X.toHodgeAmbient c

/-! ## §2 — Capstone: the dim-2 general-surface clause yields the typed Clay form -/

/-- **PF dim-2 general-surface Hodge content yields the typed Clay
    contract on `PF_HodgeEncoding`.**

    For every general smooth projective complex surface `X` in PF's
    substrate and every framework class index `c : ℕ`,
    `HodgeAlgebraicRepresentation X.toHodgeAmbient c` holds — the
    fourth (general-surface) clause of
    `hodge_full_dim_one_and_dim_two_capstone`.

    Honest scope: substrate-level only. The encoding's
    `SmoothProjectiveComplexVariety` is restricted to
    `HodgeGeneralSurfaceSubstrate`. The `isAlgebraic` is PF's
    3-conjunct substrate predicate, not literal geometric
    algebraicity by an explicit cycle. -/
theorem PF_Hodge_capstone_yields_Clay_Hodge_standard :
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeEncoding := by
  intro X c
  -- The bundled capstone's general-surface clause is the fourth
  -- conjunct of `hodge_full_dim_one_and_dim_two_capstone`. We extract
  -- it directly via the per-class discharge.
  exact (hodge_general_surface_full_discharge X c).1

/-! ## §3 — Named open frontier toward general Clay Hodge -/

/-- **The named open Props blocking lift to the general Clay Hodge
    statement.** Conjoins Wave 33's codim-2 CY3 obstruction and
    Wave 57's general-quintic Voisin 2007 open. Both are explicitly
    documented `Prop := True` markers in PF (per the NoTrueOnClayPath
    audit), naming the geometric content that must land to extend
    substrate-level closure to the literal Clay statement. -/
def Hodge_OpenFrontier : Prop :=
  VoisinObstructionAtCodimTwoCY3 ∧
  PrincipiaTractalis.Hodge_QuinticCYCodim2Scaffold.Voisin2007_general_quintic_open_subprop
    PrincipiaTractalis.Hodge_QuinticCYCodim2Scaffold.fermatQuinticConcrete

#check @PF_HodgeEncoding
#check @PF_Hodge_capstone_yields_Clay_Hodge_standard
#check @Hodge_OpenFrontier

end PF.Referee.HodgeCapstoneTypedBridge
