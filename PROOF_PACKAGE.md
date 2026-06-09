# Proof Package — Principia Fractalis

**Package version:** 2026-06-09 (substrate-level v2.5.0 manuscript / Lean 4 v4.24.0-rc1)
**Maintainer:** Pablo Cohen
**Adjacent docs:** [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md), [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md), [`docs/CLAY_PER_AXIS_CITATION_CARDS.md`](docs/CLAY_PER_AXIS_CITATION_CARDS.md)

This document is the **single source of truth** for the load-bearing
theorem citations of Principia Fractalis. Every claim made in
`README.md`, the manuscript, or the published papers should be cite-
able from the witnesses listed here. The audit cycle 2026-06-09 verified
the witnesses exist; the discharge-status column tells the truth about
what they prove.

---

## The canonical single-citation theorem

```
PF.Referee.PerelmanAnchoredSimultaneousClosure.perelman_anchor_yields_simultaneous_clay_closure
```

**Lean source:** [`PF_Lean4_Code/PF/Referee/PerelmanAnchoredSimultaneousClosure.lean`](PF_Lean4_Code/PF/Referee/PerelmanAnchoredSimultaneousClosure.lean)

**Manuscript form:** [`Principia_Fractalis_master_folder/chapters/ch34A_substrate_theorem.tex`](Principia_Fractalis_master_folder/chapters/ch34A_substrate_theorem.tex)

**Honest scope (in code):** From the file's own documentation —
*"NOT a literal Clay-statement-form discharge in mathlib's elliptic-curve
/ Sobolev / Wightman / Hodge / Turing-machine sense for any of the six
unsolved Clay problems."* This is the substrate-level meta-theorem;
literal-form discharge requires the open work in [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md).

---

## Per-axis witnesses

For each Clay axis, the package lists:

- **Substrate-level witness** — the Lean theorem PF proves
- **Residual** — the named open gap from [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md)
- **Mathlib touchpoint** — whether the bridge references real mathlib types

### Riemann Hypothesis

| Field | Content |
|---|---|
| Substrate witness | `hilbert_polya_formulations_equivalent`, `hilbert_polya_implies_RH` |
| Lean file | `PF_Lean4_Code/PF/Referee/RHCapstoneTypedBridge.lean` |
| Mathlib touchpoint | **Yes** — `Complex.riemannZeta` referenced via `PF/RHSurjectivityConjecture.lean` |
| Residual | P4 — `RHSpectralSurjectivityConjecture` |

### P vs NP

| Field | Content |
|---|---|
| Substrate witness | `enum_to_class_separation_bridge_iff_literal_P_neq_NP` |
| Lean file | `PF_Lean4_Code/PF/P_NP_Complete_Proof.lean` (headline `P_NEQ_NP`); `PF_Lean4_Code/PF/PNeqNP_SpectralGap_Consolidated.lean` |
| Mathlib touchpoint | Partial — `ClassP`/`ClassNP` defined over real polynomial-time bounds in `PF/TuringEncoding/Complexity.lean`; spectral side uses stipulated real constants |
| Residual | P1 (PolylogEigenvalueConjecture), P3 (alpha_of_class), P2 (operator-side LinearPMap) |

### Yang–Mills

| Field | Content |
|---|---|
| Substrate witness | `ym_continuum_mass_gap_three_halves` |
| Lean file | `PF_Lean4_Code/PF/YangMills/Bridge5_YM_SubstrateDischarge.lean` |
| Mathlib touchpoint | Partial — `Matrix.specialUnitaryGroup (Fin 2) ℂ` referenced (SU(2)); OS/SW/GJ axioms are `Prop := True` |
| Residual | P6 — `fractalYMMassGap` + continuum OS-Wightman gauge field theory upstream |

### BSD

| Field | Content |
|---|---|
| Substrate witness | `bsd_rank_one_E37a1_via_heegner_and_GZ_K` |
| Lean file | `PF_Lean4_Code/PF/BSD_HeegnerRank1ProofE91a1.lean` and related |
| Mathlib touchpoint | Partial — `WeierstrassCurve ℚ` referenced; `BSD_equality_holds` predicate is `True` |
| Residual | P7 — `fractalBSDRankEquality`; Gross–Zagier + Kolyvagin cited not formalized; rank ≥ 2 entirely open |

### Navier–Stokes

| Field | Content |
|---|---|
| Substrate witness | `ns_smoothness_composite_substrate_discharge` |
| Lean file | `PF_Lean4_Code/PF/MillenniumSixReductions.lean`; `PF/NavierStokes/*.lean` (20+ attempt files) |
| Mathlib touchpoint | Minimal — `NavierStokesGlobalSmoothness := ∀(_:Unit), ∃(_:Unit), True`; some files import `Mathlib.Analysis.Distribution.SchwartzSpace` |
| Residual | P5 — `fractalEmergenceNoBlowup` + literal Leray–Hopf smoothness on ℝ³ upstream |

### Hodge

| Field | Content |
|---|---|
| Substrate witness | `hodge_clay_gap_isolated_to_voisin_2007` |
| Lean file | `PF_Lean4_Code/PF/AlgebraicGeometry/Bridge4_Hodge_SubstrateDischarge.lean` and `PF/Hodge*Substrate.lean` |
| Mathlib touchpoint | Minimal — `HodgeAmbient = (ℕ, ℕ, ℕ)` triple; predicate satisfied by trivial witnesses |
| Residual | P8 — Voisin 2007 obstruction on general smooth quintic outside Dwork locus |

### Poincaré

| Field | Content |
|---|---|
| Substrate witness | `framework_alpha_values_match_rigidity` (second projection) |
| Lean file | `PF_Lean4_Code/PF/PerelmanAnchoredAlphaCascade.lean` |
| Mathlib touchpoint | None; α_Poincaré = 1 anchored to Perelman 2002–2003 (Hamilton-Ricci flow) |
| Residual | None — Perelman 2002–2003 is the settled Clay solution |

---

## Cross-Millennium algebraic invariants (machine-verified)

Bundled in `CrossMillenniumSharedInvariants`. The 11 invariants are
**fully proved real-number identities** — pure algebra, no conjectures:

```
α_P² = α_YM                α_RH² = 9/4              α_QG² = 2π
α_Hodge² = α_Hodge + 1     α_NS = 2·α_BSD           α_NS = α_YM·α_BSD
α_YM = α_Poincaré + 1      α_RH·α_NS = α_NS + α_BSD α_RH·α_YM = 3
α_NP − α_Hodge = 1/4       α_QG² = α_YM·π
```

**Lean file:** `PF_Lean4_Code/PF/CrossMillennium/CrossMillenniumSharedInvariants.lean`

This is the substrate's algebraic content — the seven α-values are not
algebraically independent, they satisfy a tight identity web. This is
the **real result** of the framework's substrate-level work.

---

## α-rigidity (the substrate's α-skeleton)

```
α_YM = 2          α_RH = 3/2          α_Poincaré = 1
α_Hodge = φ       α_BSD = 3π/4        α_NS = 3π/2
α_NP = φ + 1/4    α_P = √2            α_QG = √(2π)
```

**Witness:** `framework_alpha_values_match_rigidity` (and abstract
rigidity capstone `alpha_system_rigidity` in
`CrossMillenniumDerivedConsequences`).

These nine values + their algebraic web (above) constitute the
substrate's commitment. The framework's claim is that this rigid
algebraic structure forces the per-axis Clay outcomes.

---

## Falsifiability

Eight typed Lean propositions (F1–F8) in
`PF_Lean4_Code/PF/Referee/FrameworkFalsifiabilityConditions.lean` —
each a refutation condition with numeric thresholds and named
experimental protocols. Cataloged in [`README.md`](README.md) section
"Empirical Falsifiability".

Operationalizable today: F2 (ch₂ ∈ [0.94, 0.96]), F3 (Λ_eff/Λ₀
deviation), F4 (H₀ bracket), F6 (Ω_Λ bracket), F5 Heron-class softer
variant.

---

## Cosmology (machine-verified)

| Result | Witness | Source |
|---|---|---|
| Λ_eff suppression of 120 orders | `naive_vs_observed_ratio_log` | `PF/Cosmology/LambdaEffParameterFreeCapstone.lean` (78π·0.95·1.1875 ≈ 120·ln(10)) |
| Dark-energy density 0.7 in [0.65, 0.75] | `darkEnergyDensity_in_bracket` | `PF/Cosmology/` |
| Hubble bracket 67.4 < 69.8 < 73.0 | `hubble_framework_brackets_local_and_cmb` | `PF/Cosmology/` |
| Toy energy-conservation identity | `energy_conserved_toy` | `PF/Cosmology/` |

---

## Consciousness (machine-verified)

| Result | Witness | Source |
|---|---|---|
| ch₂ = 0.95 threshold | `threshold_ch2_eq_zero_point_95` | `PF/Consciousness/QuantumClassicalDecoherenceThreshold.lean` (`threshold_ch2 := 19/20` by definition) |
| Φ_IIT entropy inequality | `ch2_le_one_minus_exp_neg_phi_over_two` | `PF/Consciousness/Ch2PhiBridgeDischarge.lean` — real entropy inequality on Schmidt spectra |
| Deprecated universal Φ bridge | `ch2_phi_bridge_universal_form_unsatisfiable` (NEGATIVE result) | `PF/Consciousness/Ch2PhiBridge.lean` — author-killed wrong claim |

---

## Provenance and updating

When any load-bearing theorem changes location or signature, update:

1. This file (PROOF_PACKAGE.md) — the row above
2. [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md) if a residual moves
3. [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) if an axiom-shape commitment changes
4. [`CHANGELOG.md`](CHANGELOG.md) — chronological record

The publishing gate ([`docs/governance/PUBLISHING_GATE.md`](docs/governance/PUBLISHING_GATE.md))
requires the four documents to be in sync before any external claim.
