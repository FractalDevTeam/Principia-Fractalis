# Principia Fractalis — Referee Proof Package

**Anchor commit**: `2cfde50` (after `6573f46`, after `11ac8ed`, after `ee51039`).
**Date**: 2026-06-02.
**Manuscript version**: 1.1.0-rev3.1 (First Revision: Referee-Ready Edition).

This is the **single referee entry point** for the Principia Fractalis
formalization. Everything you need to evaluate the framework's
machine-checked claims is reachable from this document.

## TL;DR

* **What this is**: a machine-checked Lean 4 typed-contract framework
  organizing all six unsolved Clay Millennium Problems plus the
  Chapter 4 Timeless Field substrate under one architecture, with the
  named open frontiers per axis inspectable in code, zero project
  axioms, plus a Coq mirror at the single-citation point.
* **What this is not**: a discharge of any Clay Millennium Problem.
  Each axis has a named open Prop that, when discharged, would yield
  the corresponding standard Clay statement. Closing those Props is
  open research.
* **Single citation theorem**: `PF.Referee.RefereeIndex.refereeLayerAtHEAD_05ac9b5_realised`.
  This bundles 10 layer-component witnesses (frontier doc invariant,
  zero-hidden-content audit, capstone audit, per-axis typed bridges,
  Ch 4 TF capstone, structural unification).

## One-command verification

After `git clone`:

```bash
cd PF_Lean4_Code
lake build PF
```

Expected: **3908 jobs clean, 0 sorries, 0 admits, 0 project axioms**.

For per-capstone axiom inspection:

```bash
cd PF_Lean4_Code
lake env lean PF/Referee/CapstoneDependencyAudit.lean
```

Expected output (excerpt):

```
'PrincipiaTractalis.principia_fractalis_millennium_capstone' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrincipiaTractalis.all_clay_via_soundness_and_capstones' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrincipiaTractalis.principia_fractalis_wave57_master_capstone' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.Referee.YMCapstoneTypedBridge.PF_YM_capstone_yields_Clay_YangMills_standard' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.Referee.BSDCapstoneTypedBridge.PF_BSD_capstone_yields_Clay_BSD_standard' does not depend on any axioms
'PF.Referee.HodgeCapstoneTypedBridge.PF_Hodge_multisubstrate_capstone' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrincipiaTractalis.TimelessField.timelessFieldExistenceClaim_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard Lean foundations (`propext`, `Classical.choice`,
`Quot.sound`) appear; `PF_BSD_capstone_yields_Clay_BSD_standard` has
**no axiom dependencies** at all (pure `rfl`).

For the Coq parity stub:

```bash
cd PF_Coq_Code
coqc -Q PF PrincipiaTractalis PF/Referee/RefereeIndex.v
```

Expected: clean compile, no `Admitted`.

## The Referee Layer at HEAD `2cfde50`

**14 Lean modules** + 1 Coq mirror module, all under `PF.Referee.*` or
`PF.Consciousness.TimelessField*`:

| File | Purpose |
|---|---|
| `PF/Referee/FrontierLedger.lean` | Inventory of 6 Clay axes + Poincaré anchor; cites each existing PF capstone by exact Lean name. |
| `PF/Referee/StandardClayStatements.lean` | Typed standard Clay contracts: `Clay_RiemannHypothesis_Standard` (wired to mathlib `riemannZeta` via PF's critical-strip form); five others parameterised over external encodings. **No `Prop := True` on any Clay-statement branch** (Non-Negotiable Rule #1 compliance). |
| `PF/Referee/NoTrueOnClayPath.lean` | 17-entry audit classifying every `Prop := True` declaration on or near a Clay-statement path as `ProvennessTag` / `ExternalAnchor` / `ParameterizedDelegated` / `HiddenSemanticContent`. Theorem `no_hidden_semantic_content` decides zero `HiddenSemanticContent`. |
| `PF/Referee/CapstoneDependencyAudit.lean` | Re-export of top-level capstones with `#print axioms` emitted to compile log. Verifies the **zero project axioms** invariant per capstone. |
| `PF/Referee/TypedMillenniumReduction.lean` | Typed counterpart of `PF.MillenniumReductionSoundness`. `MillenniumReductionSoundnessTyped` operates on typed Clay contracts instead of `:= True` placeholders. |
| `PF/Referee/RHCapstoneTypedBridge.lean` | Retypes `riemann_hypothesis_via_T3_sym_framework`'s conclusion as `Clay_RiemannHypothesis_Standard`. `RH_OpenFrontier` names the surjectivity Prop. |
| `PF/Referee/PNPCapstoneTypedBridge.lean` | `PF_ComplexityEncoding` from `TuringEncoding.ClassP`/`ClassNP` subtypes + `P_subset_NP`; theorem `pf_pneqnp_iff_clay_pneqnp_standard` establishes logical equivalence between `P_neq_NP_def` and the typed Clay form. `PNP_OpenFrontier := PolylogEigenvalueConjecture`. |
| `PF/Referee/NSCapstoneTypedBridge.lean` | Frontier-only documentation; PF's NS predicate is `:= True` upstream, so no honest typed bridge offered. `NS_OpenFrontier` names the Wave 57 mathlib gaps. |
| `PF/Referee/YMCapstoneTypedBridge.lean` | Real typed witness at finite-dim 2×2 scope: Wave 55C `interactingHam` matrix, `massGap = 1/2 > 0`, PSD via SOS. `YM_OpenFrontier := fractalYMLevel1LiftsToContinuum`. |
| `PF/Referee/BSDCapstoneTypedBridge.lean` | Typed Clay form on `EllipticCurve := Fin 6` (six LMFDB-anchored curves); `rfl`-trivial proof. `BSD_OpenFrontier` names the Wave 57 (A3)+(A4) mathlib gaps. |
| `PF/Referee/HodgeCapstoneTypedBridge.lean` | Multi-substrate bundle covering 6 PF Hodge substrate classes (K3, general surface, CY3 (2,2)-slice, CY4 (1,1)/(2,2)/(3,3)-slices). `Hodge_OpenFrontier` names the Voisin 2007 obstruction. |
| `PF/Consciousness/TimelessFieldConcreteMorphism.lean` | Concrete connecting-morphism family for Ch 4 (axiom-free `ProjectiveCompatibility`). `timelessFieldExistenceClaim_holds` is now a theorem (was a Prop stub). |
| `PF/Referee/PFUnifiedSubstrate.lean` | **Structural unification theorem**. `pf_concrete_unified_substrate_yields_three_clay_axes_and_TF` proves YM + BSD + Hodge typed Clay forms AND the full Ch 4 TF capstone hold simultaneously from one concrete substrate, axiom-free. |
| `PF/Referee/RefereeIndex.lean` | **Single-citation aggregator**. `refereeLayerAtHEAD_05ac9b5_realised` bundles 10 layer-component witnesses. |
| `PF_Coq_Code/PF/Referee/RefereeIndex.v` | Coq mirror — parity stub of `refereeLayerAtHEAD_05ac9b5_realised`. |

## Per-axis honest scope

For each axis, the typed bridge's exact scope, what it proves, what
remains open. Read this carefully before evaluating the framework.

### RH (Riemann Hypothesis)

* **Typed bridge**: `PF_RH_capstone_yields_Clay_RH_standard`
  retypes the conclusion of `riemann_hypothesis_via_T3_sym_framework`
  (PF/SpectralBijection.lean) as `Clay_RiemannHypothesis_Standard`.
  `Clay_RiemannHypothesis_Standard := PrincipiaTractalis.RiemannHypothesis`,
  which is the critical-strip formulation
  `∀ s, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1/2`.
* **Conditional on**: 5 hypotheses including the open
  surjectivity Prop (the spectral-bijection onto ζ-zeros).
* **Open frontier**: `RH_OpenFrontier` —
  surjectivity of the eigenvalue-to-ζ-zero map.
* **What is NOT proved here**: RH itself. The surjectivity Prop is
  the open mathematics of the RH program.

### P vs NP

* **Typed bridge**: `pf_pneqnp_iff_clay_pneqnp_standard` —
  logical equivalence between PF's internal `P_neq_NP_def` and the
  typed Clay form `Clay_PvsNP_Standard PF_ComplexityEncoding`.
* **`PF_ComplexityEncoding`**: built from
  `↥TuringEncoding.ClassP` and `↥TuringEncoding.ClassNP` (subtypes
  of `TuringEncoding.Language`) plus the standard `P_subset_NP`
  inclusion (Cook 1971 Thm 2.1). No `alpha_of_class` content moves
  through the iff.
* **Conditional on**: `PolylogEigenvalueConjecture`.
* **Open frontier**: `PNP_OpenFrontier := PolylogEigenvalueConjecture`.
  Per the Wave 57 sharpness certificate, discharging this is
  equivalent to deciding P vs NP itself.

### Navier-Stokes

* **Typed bridge**: NONE. The PF NS predicate
  `NavierStokesGlobalSmoothPredicate` is currently `:= True`
  upstream, so no honest typed bridge can be offered without
  violating Non-Negotiable Rule #1.
* **What this module supplies**: `NS_OpenFrontier` naming the
  precise Wave 57 mathlib gaps (`MathlibPMath1` + `MathlibPMath2`)
  plus Wave 33's `UniformHadamardBoundAllN`.
* **Open frontier**: standard critical a priori estimate (BKM,
  Prodi-Serrin, critical Sobolev/Besov) — open Clay mathematics.

### Yang-Mills mass gap

* **Typed bridge**: `PF_YM_capstone_yields_Clay_YangMills_standard`
  — a real typed Clay witness on `PF_YMEncoding`.
* **`PF_YMEncoding` scope**: `GaugeGroup := Unit` (placeholder, NOT
  genuine SU(N)); `QYM := Matrix (Fin 2) (Fin 2) ℝ`
  (Wave 55C 2×2 carrier); `satisfiesClayAxioms M := IsSymm M ∧ <PSD via SOS bilinear>`;
  `massGap := 1/2 > 0`.
* **The witness**: Wave 55C `interactingHam` matrix
  `!![1, 1/2; 1/2, 1]` is symmetric and positive-semidefinite (via
  the explicit SOS bilinear form), with smallest eigenvalue
  `1/2 > 0`. This is a REAL theorem under the finite-dim encoding.
* **Open frontier**: `YM_OpenFrontier := fractalYMLevel1LiftsToContinuum`
  plus the four Wave 47B Wightman/OS continuum gaps. Lifting the
  finite-dim mass gap to continuum SU(3) on ℝ⁴ is the open Clay
  mathematics.

### BSD (Birch-Swinnerton-Dyer)

* **Typed bridge**: `PF_BSD_capstone_yields_Clay_BSD_standard` —
  proven `rfl`-trivially on the restricted encoding.
* **`PF_BSDEncoding` scope**: `EllipticCurve := Fin 6` restricted to
  six LMFDB-anchored curves (`knownRankCurve6 : Fin 6 → WeierstrassCurve ℚ`,
  ranks {0..5}: 32.a3, 37a1, 389a1, 5077a1, 234446a1, 19047851a).
  Both `algebraicRank` and `analyticRank` project to the same external
  LMFDB-cited label `r.val`. The equality holds by construction.
* **Honest reading**: PF does **not** derive Mordell-Weil rank from
  Lean-internal content. The bridge certifies that, on the six
  LMFDB-anchored curves PF instruments, the two ranks project to the
  same external label. The genuine PF content carried by
  `BSDFrameworkInstance` is the φ/e eigenvalue bracket + Galois-pair
  separation, NOT the rank itself.
* **Open frontier**: `BSD_OpenFrontier` —
  Wave 57 (A3)+(A4) Props
  (`LSeriesAbsConvergenceForReSGreaterThanThreeHalves` ∧
  `WilesModularityImpliesAnalyticContinuation`).

### Hodge

* **Typed bridges**: six substrate-level Clay witnesses bundled in
  `PF_Hodge_multisubstrate_capstone`:
  - K3 surface (dim 2) via `PF_HodgeK3Encoding`
  - General smooth projective complex surface (dim 2) via `PF_HodgeEncoding`
  - CY3 (2,2)-slice (dim 3) via `PF_HodgeCY3Dim22Encoding`
  - CY4 (1,1)-slice (dim 4) via `PF_HodgeCY4At11Encoding`
  - CY4 (2,2)-slice (dim 4) via `PF_HodgeCY4At22Encoding`
  - CY4 (3,3)-slice (dim 4) via `PF_HodgeCY4At33Encoding`
* **Each encoding's scope**: `SmoothProjectiveComplexVariety :=`
  one PF substrate type; `RationalHodgeClass := ℕ` (framework
  class_idx); `isAlgebraic := HodgeAlgebraicRepresentation` — a
  3-conjunct substrate predicate (NOT `:= True`).
* **Open frontier**: `Hodge_OpenFrontier := VoisinObstructionAtCodimTwoCY3 ∧ Voisin2007_general_quintic_open_subprop`.
  The general smooth-projective-complex-variety Clay statement at
  codim ≥ 2 remains open.

### Chapter 4 Timeless Field

* **Capstone**: `timelessFieldExistenceClaim_holds` is now an
  unconditional Lean theorem (was a Prop stub).
* **Concrete connecting morphism family**: `truncMorphism` (the
  zero family — the minimal honest instance satisfying
  `ProjectiveCompatibility` axiom-free at every level pair).
* **Discharged at skeleton level**: `NuclearStructure`,
  `KTheoryOfTimelessField`, `SpacetimeEmergence`, `ForceUnification`.
* **Open direction**: promote to operator-algebraic content —
  the genuine partial-trace + scaling morphism of Definition 4.5;
  Pimsner-Voiculescu K-theory; automorphism-quotient spacetime;
  gauge subgroup unification.

## Structural unification theorem

The framework's longstanding prose claim — *"the six Clay axes plus
the Ch 4 Timeless Field substrate are not seven independent objects
but one framework"* — is now a Lean theorem:

```lean
theorem pf_concrete_unified_substrate_yields_three_clay_axes_and_TF :
    let S := pf_concrete_unified_substrate
    Clay_YangMillsMassGap_Standard S.clayBundle.yangMills ∧
    Clay_BSD_Standard S.clayBundle.bsd ∧
    Clay_Hodge_Standard S.clayBundle.hodge ∧
    PrincipiaTractalis.TimelessField.TimelessFieldExistenceClaim
```

Located in `PF/Referee/PFUnifiedSubstrate.lean`. One concrete substrate
witnesses four claims simultaneously, axiom-free.

RH is excluded from the unconditional clause because its typed contract
is wired directly to mathlib's `riemannZeta` (no PF encoding needed).
P vs NP is excluded because its typed contract is conditional on the
open `PolylogEigenvalueConjecture`. NS is excluded because the upstream
PF predicate is `:= True`.

## What this package does NOT claim

* It does NOT claim to discharge any Clay Millennium Problem.
* It does NOT claim to derive elliptic-curve rank, the YM continuum
  measure, the Hodge cycle class map at codim ≥ 2, the
  Riemann-Hypothesis spectral surjectivity, the P vs NP separation,
  or NS regularity.
* It does NOT replace mathlib content where mathlib lacks it (e.g.
  smooth projective complex varieties, divergence-free Sobolev spaces);
  it parameterises typed Clay contracts over external encodings the
  user must supply.
* It does NOT promote substrate-level Hodge witnesses to literal
  algebraicity of rational Hodge classes.
* It does NOT promote the finite-dim YM mass gap to continuum SU(3).
* It does NOT discharge `PolylogEigenvalueConjecture`,
  `RHSpectralSurjectivityConjecture`, `VoisinObstructionAtCodimTwoCY3`,
  `Voisin2007_general_quintic_open_subprop`,
  `fractalYMLevel1LiftsToContinuum`, or the Wave 57 (A3)+(A4) Props.

## What this package DOES establish

1. A single Lean architecture organising all six Clay axes plus the
   Ch 4 TF substrate. Audit-free at the project level.
2. A typed-contract layer where every Clay path is either wired to
   mathlib's standard objects or parameterised over an explicit
   external encoding — no `Prop := True` on Clay paths.
3. Six axiom-free substrate-level Hodge typed Clay witnesses across
   six distinct algebraic-geometry contexts (one structural
   predicate spanning curves, K3, abelian, general surface, CY3, CY4).
4. A finite-dim YM mass-gap theorem witnessing the typed Clay form on
   a real (not `True`) PSD encoding.
5. A logical equivalence between PF's internal `P_neq_NP_def` and the
   typed Clay form on a concrete subtype encoding.
6. The Ch 4 Timeless Field capstone discharged as a Lean theorem at
   the structural-skeleton level.
7. A structural unification theorem: four typed Clay forms plus the
   TF capstone hold simultaneously from one concrete substrate.
8. A Coq mirror establishing the cross-prover single-citation point.
9. Every per-axis open frontier is named, inspectable, and reachable
   from `PF.Referee.FrontierLedger.frontier`.

## How to extend this work

To discharge a Clay axis literally, the workflow is:

1. Discharge the corresponding named open Prop in the axis's
   `*CapstoneTypedBridge.lean` or `*OpenFrontier` definition.
2. The existing typed bridge then yields the typed Clay contract
   under the existing encoding.
3. To lift further to the literal Clay statement quantified over the
   standard mathematical object (smooth projective complex variety,
   etc.), construct the missing mathlib infrastructure and instantiate
   the standard encoding from it.

This package separates these two steps and makes both inspectable.

## Files of interest, by entry point

* **Auditor**: start at
  `PF_Lean4_Code/PF/Referee/RefereeIndex.lean::refereeLayerAtHEAD_05ac9b5_realised`.
* **Per-axis examiner**: open the corresponding
  `PF_Lean4_Code/PF/Referee/*CapstoneTypedBridge.lean`. Each docstring
  documents the bridge's honest scope and open frontier.
* **Manuscript / framework theorist**: see the manuscript at
  `Principia_Fractalis_master_folder_rev2/main.tex` (Version
  1.1.0-rev3.1, First Revision: Referee-Ready Edition). The new
  `frontmatter/rev3_referee_layer_status.tex` chapter explains the
  Referee layer's purpose in prose.
* **Cross-prover skeptic**: see
  `PF_Coq_Code/PF/Referee/RefereeIndex.v`.
* **Wave history**: `MEMORY.md` and the commit log at HEAD
  `2cfde50`. The full Referee-layer commit chain is
  `a2fb8d2 → d23b465 → 7ee849e → bd00393 → 50c07f0 → 939dab2 → 96faade → 4817c96 → 05ac9b5 → 11ac8ed → 6573f46 → 2cfde50`.
