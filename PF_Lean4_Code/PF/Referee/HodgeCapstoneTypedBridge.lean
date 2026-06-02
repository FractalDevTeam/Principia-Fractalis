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

import PF.HodgeCurveDim1Substrate
import PF.HodgeK3Dim2Substrate
import PF.HodgeAbelianSurfaceDim2Substrate
import PF.HodgeGeneralSurfaceDim2Substrate
import PF.HodgeCalabiYau3FoldDim22Substrate
import PF.HodgeDim4CY4Substrate
import PF.Hodge_QuinticCYCodim2Scaffold
import PF.AlgebraicGeometry.CycleClassMapAtCodim2Attempt
import PF.Referee.StandardClayStatements

namespace PF.Referee.HodgeCapstoneTypedBridge

open PrincipiaTractalis
open PrincipiaTractalis.HodgeCurveDim1
open PrincipiaTractalis.HodgeK3Dim2
open PrincipiaTractalis.HodgeAbelianSurfaceDim2
open PrincipiaTractalis.HodgeGeneralSurfaceDim2
open PrincipiaTractalis.HodgeCalabiYau3FoldDim22
open PrincipiaTractalis.HodgeDim4CY4
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

/-! ## §4 — Multi-substrate Hodge encodings (curve / K3 / abelian / CY3 / CY4)

Beyond the dim-2 general-surface encoding (`PF_HodgeEncoding`) above,
PF carries five additional axiom-free substrate-level full discharges:

* `hodge_dim_one_full_discharge` on `HodgeCurveSubstrate`
* `hodge_K3_dim_two_full_discharge` on `HodgeK3Substrate`
* `hodge_abelian_surface_full_discharge` on `HodgeAbelianSurfaceSubstrate`
* `hodge_calabi_yau_3fold_dim22_full_discharge` on `HodgeCY3Dim22Substrate`
* `hodge_CY4_full_discharge_at_{11,22,33}` on `HodgeCY4Substrate`

This section supplies a typed bridge per substrate. Each encoding
specialises `Clay_Hodge_Standard` to the substrate's `toHodgeAmbient`
ambient and the substrate-level `HodgeAlgebraicRepresentation`. None
of these is the full Clay Hodge statement; each is the typed Clay
shape **restricted to one substrate class**. -/

/-- Hodge encoding restricted to PF's K3 surface substrate (dim 2). -/
def PF_HodgeK3Encoding :
    PF.Referee.StandardClayStatements.StandardHodgeEncoding where
  SmoothProjectiveComplexVariety := HodgeK3Substrate
  RationalHodgeClass _ := ℕ
  isAlgebraic X c := HodgeAlgebraicRepresentation X.toHodgeAmbient c

theorem PF_HodgeK3_capstone_yields_Clay_Hodge_standard :
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeK3Encoding := by
  intro X c
  exact (hodge_K3_dim_two_full_discharge X c).1

/-- Hodge encoding restricted to PF's CY3 (2,2)-slice substrate (dim 3). -/
def PF_HodgeCY3Dim22Encoding :
    PF.Referee.StandardClayStatements.StandardHodgeEncoding where
  SmoothProjectiveComplexVariety := HodgeCY3Dim22Substrate
  RationalHodgeClass _ := ℕ
  isAlgebraic X c := HodgeAlgebraicRepresentation X.toHodgeAmbient c

theorem PF_HodgeCY3Dim22_capstone_yields_Clay_Hodge_standard :
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeCY3Dim22Encoding := by
  intro X c
  exact (hodge_calabi_yau_3fold_dim22_full_discharge X c).1

/-- Hodge encoding restricted to PF's CY4 substrate (dim 4),
    (1,1)-slice projection. -/
def PF_HodgeCY4At11Encoding :
    PF.Referee.StandardClayStatements.StandardHodgeEncoding where
  SmoothProjectiveComplexVariety := HodgeCY4Substrate
  RationalHodgeClass _ := ℕ
  isAlgebraic X c := HodgeAlgebraicRepresentation X.toHodgeAmbient11 c

theorem PF_HodgeCY4At11_capstone_yields_Clay_Hodge_standard :
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeCY4At11Encoding := by
  intro X c
  exact (hodge_CY4_full_discharge_at_11 X c).1

/-- Hodge encoding restricted to PF's CY4 substrate (dim 4),
    (2,2)-slice projection. -/
def PF_HodgeCY4At22Encoding :
    PF.Referee.StandardClayStatements.StandardHodgeEncoding where
  SmoothProjectiveComplexVariety := HodgeCY4Substrate
  RationalHodgeClass _ := ℕ
  isAlgebraic X c := HodgeAlgebraicRepresentation X.toHodgeAmbient22 c

theorem PF_HodgeCY4At22_capstone_yields_Clay_Hodge_standard :
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeCY4At22Encoding := by
  intro X c
  exact (hodge_CY4_full_discharge_at_22 X c).1

/-- Hodge encoding restricted to PF's CY4 substrate (dim 4),
    (3,3)-slice projection. -/
def PF_HodgeCY4At33Encoding :
    PF.Referee.StandardClayStatements.StandardHodgeEncoding where
  SmoothProjectiveComplexVariety := HodgeCY4Substrate
  RationalHodgeClass _ := ℕ
  isAlgebraic X c := HodgeAlgebraicRepresentation X.toHodgeAmbient33 c

theorem PF_HodgeCY4At33_capstone_yields_Clay_Hodge_standard :
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeCY4At33Encoding := by
  intro X c
  exact (hodge_CY4_full_discharge_at_33 X c).1

/-! Note on omitted substrates: `HodgeCurveSubstrate` and
    `HodgeAbelianSurfaceSubstrate` live in `Type 1` (they carry
    `Type`-valued fields for `Points` / `torus_endomorphisms`), so
    they do not fit directly into
    `StandardHodgeEncoding.SmoothProjectiveComplexVariety : Type`.
    A `ULift` wrapper or a universe-polymorphic
    `StandardHodgeEncoding` would lift them in; deferred to a future
    session to avoid scope creep. -/

/-! ## §5 — Multi-substrate capstone

Bundles three substrate-level typed Clay bridges (K3, general
surface, CY3 (2,2)-slice) plus the original general-surface bridge. -/

/-- **★ Multi-substrate Hodge typed-bridge capstone ★**
    Every PF Hodge substrate class that fits in `Type` (K3,
    general surface, CY3 (2,2)-slice) yields a typed
    `Clay_Hodge_Standard` witness on its substrate-restricted
    encoding.

    Honest scope: each witness is substrate-level. The encoding's
    `SmoothProjectiveComplexVariety` is restricted to one PF
    substrate type per witness; `isAlgebraic` is the 3-conjunct
    `HodgeAlgebraicRepresentation`. The general smooth-projective-
    complex-variety Clay statement at codim ≥ 2 remains open. -/
theorem PF_Hodge_multisubstrate_capstone :
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeK3Encoding ∧
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeEncoding ∧
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeCY3Dim22Encoding ∧
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeCY4At11Encoding ∧
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeCY4At22Encoding ∧
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard PF_HodgeCY4At33Encoding :=
  ⟨ PF_HodgeK3_capstone_yields_Clay_Hodge_standard
  , PF_Hodge_capstone_yields_Clay_Hodge_standard
  , PF_HodgeCY3Dim22_capstone_yields_Clay_Hodge_standard
  , PF_HodgeCY4At11_capstone_yields_Clay_Hodge_standard
  , PF_HodgeCY4At22_capstone_yields_Clay_Hodge_standard
  , PF_HodgeCY4At33_capstone_yields_Clay_Hodge_standard ⟩

#check @PF_HodgeEncoding
#check @PF_Hodge_capstone_yields_Clay_Hodge_standard
#check @Hodge_OpenFrontier

end PF.Referee.HodgeCapstoneTypedBridge
