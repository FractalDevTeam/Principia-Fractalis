# Open Problems — Principia Fractalis

**Catalog version:** 2026-06-09 (audit cycle)
**Maintainer:** Pablo Cohen
**Adjacent docs:** [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md), [`PROOF_PACKAGE.md`](PROOF_PACKAGE.md), [`CHANGELOG.md`](CHANGELOG.md), [`docs/governance/PUBLISHING_GATE.md`](docs/governance/PUBLISHING_GATE.md)

This document catalogs the **named open problems** of the framework — the
mathematical content that is currently encoded as Lean propositions or
explicit hypotheses but is not yet discharged. The framework's overall
"0 project axioms / 8360 jobs clean" claim refers to Lean kernel axioms;
the open problems below are typed propositions / explicit hypotheses
that load-bearing theorems consume.

A peer-reviewer should read this document alongside [`README.md`](README.md)'s
"What Is NOT Discharged" section.

---

## Problem P1 — `PolylogEigenvalueConjecture`

**Source:** `PF_Lean4_Code/PF/TuringEncoding/Operators.lean`, ~line 165.

**Statement:**
```lean
def PolylogEigenvalueConjecture : Prop :=
    ((alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP) ∧
    (16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP)
     - 11 = 0 ∧ 0 < alpha_of_class ClassNP)
```

**Status:** Open. Consumed as an explicit hypothesis by every load-bearing
theorem on the P vs NP side (notably `P_NEQ_NP` in
`PF/P_NP_Complete_Proof.lean`). Discharging this Prop requires original
mathematical research: showing that the function
`alpha_of_class : Set Language → ℝ` actually takes the algebraic values
`√2` on `ClassP` and `φ + 1/4` on `ClassNP`.

**Honest scope:** the conjecture is at least as strong as `ClassP ≠ ClassNP`,
so a proof of the conjecture would constitute a proof of P ≠ NP. This is
why it is open.

**Related attempts:**
- `PF/TuringEncoding/PolylogEigenvalueClosureAttempt.lean`
- `PF/TuringEncoding/AlphaOfClassSetLevelAttempt.lean`
- `PF/TuringEncoding/AlphaRealizationNoGo.lean` (documents why the
  attempted derivation does not close)

---

## Problem P2 — Operator-side spectral identification (`KatoRellichInput`)

**Source:** `PF_Lean4_Code/PF/Operators/VAlphaExplicit.lean` defines
`KatoRellichInput α`. `PF/Operators/KatoRellichDischarge.lean` proves
this Prop is **false** for every `α > 0` by Hellinger–Toeplitz: a symmetric
*total* `LinearMap` on a complete inner-product space is automatically
continuous, but the diagonal coefficients `v_alpha_coeff α (2^k)` grow
without bound.

**Status of structural framework:** `PF/Operators/VAlphaPMap.lean`
(added 2026-06-09) provides the **correct architectural fix** by switching
from `LinearMap` (forces bounded) to `LinearPMap` (permits unbounded on
a dense proper subspace). The Hellinger–Toeplitz refutation no longer
applies because there is no continuity-on-whole-space claim.

**Status of substantive proof:** `VAlphaPMap.lean` carries 4 isolated
sorries marking the Finsupp ↔ span bridge that needs filling. The
operator's symmetry on the basis is proved (`h_alpha_basis_symm`).
Identification of the ground-state eigenvalue with `π/(10α)` remains
the substantive P vs NP content (this is Problem P1's spectral form).

---

## Problem P3 — `alpha_of_class` non-opaqueness

**Source:** `PF_Lean4_Code/PF/TuringEncoding/Operators.lean` declares
`opaque alpha_of_class : Set Language → ℝ`.

**Status:** Open. The function has no body — it is provided axiomatically
to the framework, with values constrained only by P1 (the conjecture).
The right fix is either:

1. **A real definition** that derives the values from the TM model.
   Equivalent to proving P1.
2. **An explicit-parameter refactor** so every theorem consuming
   `alpha_of_class` takes it as a parameter. This is a multi-file
   structural change; tractable but laborious.

Until either is done, the opacity must be acknowledged in every external
presentation.

---

## Problem P4 — `RHSpectralSurjectivityConjecture`

**Source:** `PF_Lean4_Code/PF/RHSurjectivityConjecture.lean`.

**Statement:**
```lean
def RHSpectralSurjectivityConjecture
    (α : ScalingParameter) (eigenvalues : ℕ → ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
    ∃ n : ℕ, eigenvalueToZero α (eigenvalues n) = s
```

**Status:** Open. This says PF's eigenvalues surject onto the nontrivial
zeros of ζ. The Hilbert–Pólya program asks essentially this question;
PF reduces the Clay RH statement to the surjectivity here. The
surjectivity is itself strictly stronger than RH (RH says zeros lie on
Re(s) = 1/2; this says the framework's eigenvalues realize *all* such
zeros).

**This is the only bridge that touches Mathlib's actual `Complex.riemannZeta`.**
Other Clay bridges work over framework-internal types.

---

## Problem P5 — `fractalEmergenceNoBlowup` (NS)

**Source:** `PF_Lean4_Code/PF/MillenniumSixReductions.lean`.

```lean
def fractalEmergenceNoBlowup (α : ℝ) : Prop :=
  α = 3 * Real.pi / 2 →
  ∀ (vortex_data : Unit), ∃ (emergence_resolution : Unit), True
```

**Status:** Currently the predicate has `Unit`-typed witnesses, so it is
tautologically inhabitable. The **literal Clay statement** (Leray–Hopf
smoothness on ℝ³) requires Mathlib formalizations of Sobolev spaces,
Bochner integrals, and the BKM criterion that **do not yet exist in
mathlib**. The discharge route remains:

1. **Substrate-level**: prove the existing Lean target (vacuous-target
   discharge already in `ns_smoothness_composite_substrate_discharge`).
2. **Literal-level**: needs years of mathlib upstream work on
   Navier–Stokes PDE infrastructure.

Multiple attempted upgrades exist under `PF/NavierStokes/` (the V2/V3/V4
series, the Fujita–Kato 1964 decomposition, the BKM 1984 formalization,
the Leray–Hopf bootstrap) — each climbs a level but none reaches the
literal Clay statement.

---

## Problem P6 — `fractalYMMassGap`

**Source:** `PF_Lean4_Code/PF/MillenniumSixReductions.lean`.

```lean
def fractalYMMassGap (α : ℝ) : Prop :=
  α = 2 →
  ∃ (ω_c : ℝ), 0 < ω_c ∧ resonanceCoefficient ω_c = 0 ∧
  ∃ (Δ_fYM : ℝ), 0 < Δ_fYM ∧ Δ_fYM = 197.2 * ω_c
```

**Status:** Open. The literal Clay statement (continuum SU(N) Wightman
gauge field theory with positive mass gap) requires Mathlib formalizations
of gauge fields, BRST cohomology, and Osterwalder–Schrader axioms that
do not yet exist. `PF/YangMills/Bridge5_YM_SubstrateDischarge.lean`
imports `Matrix.specialUnitaryGroup (Fin 2) ℂ` — real SU(2) — but the
OS/SW/GJ axioms are encoded as `Prop := True` pending mathlib upstream.

---

## Problem P7 — `fractalBSDRankEquality`

**Source:** `PF_Lean4_Code/PF/MillenniumSixReductions.lean`.

**Status:** Open. The current Lean target is
`∀ E : WeierstrassCurve ℚ, BSD_equality_holds E` with
`BSD_equality_holds := True`. `WeierstrassCurve` is a real mathlib type;
the predicate is vacuous.

The substrate-level rank-1 cascade
(`bsd_rank_one_E37a1_via_heegner_and_GZ_K`) is conditional on
Gross–Zagier + Kolyvagin, which are **cited but not formalized** in
mathlib. Rank ≥ 2 with the leading-term formula remains entirely open.

---

## Problem P8 — Hodge `Voisin 2007` obstruction

**Source:** `PF_Lean4_Code/PF/MillenniumSixReductions.lean` +
`PF/AlgebraicGeometry/Bridge4_Hodge_SubstrateDischarge.lean`.

**Status:** Open. The current Lean target uses `HodgeAmbient = (ℕ, ℕ, ℕ)`
with three trivial existential witnesses. No cohomology, no (p, p)
decomposition, no algebraic-cycle infrastructure. PF has multi-substrate
work (K3, Abelian, CY3 (2,2), CY4 (1,1)/(2,2)/(3,3)) at the
*structural* level but the Voisin 2007 obstruction on the general
smooth quintic outside the Dwork locus remains the named gap.

---

## Problem P9 — 143-problem empirical corpus needs real data

**Source:** `PF_Lean4_Code/PF/Empirical/HundredFortyThreeProblems.lean`.

**Status:** Currently the dataset is built via
`List.replicate 72 (canonicalEntry .P) ++ List.replicate 71 (canonicalEntry .NP)`
with `alphaMeasured := canonicalAlpha c`. The capstone
`universal_fractal_coherence` holds by definitional unfolding.

**Progress 2026-06-09:** `PF/Empirical/HundredFortyThreeProblems_Parametric.lean`
provides the parametric version where the dataset is a parameter and
the capstone is a real implication ("if every measurement is in
{√2, φ+¼}, then coherence holds"). Migration path:

1. Assemble the real 143-problem dataset as `List Problem` from the
   project's data layer (CSV + Python in `4_DATA_AND_EVIDENCE/`).
2. Encode the real `alphaMeasured` values into the Lean list.
3. Apply `universal_fractal_coherence_parametric` to obtain a
   non-tautological coherence statement.

---

## Problem P10 — IBM 9-way hardware empirical anchor

**Source:** `PF_Lean4_Code/PF/Referee/FrameworkFalsifiabilityConditions.lean`
encodes `IBM_hardware_nine_way_random_match_probability_bound` at
`10⁻¹⁵`. Current IBM Quantum gate fidelities are ~10⁻³ to 10⁻⁴, so the
sharp falsifier is below hardware resolution.

**Status:** The Heron-class softer variant
`IBM_Ten_Way_Disagreement_HeronClass_Softer` (threshold 10⁻³) is
operationalizable on current hardware. The 10⁻¹⁵ form is the
substrate's *prediction*; the 10⁻³ form is the *empirically-testable*
falsifier. Open work: actual measurement on Heron-class chips with
analysis against the prediction.

---

## Problem P11 — Mathlib upstream formalizations

For NS, YM, Hodge to reach **literal Clay-statement-form** Lean
discharges, mathlib needs (community-effort):

- Sobolev / Bochner-space Navier–Stokes PDE infrastructure
- Osterwalder–Schrader / Wightman gauge field axioms
- Hodge classes on Calabi–Yau varieties + Chow ring infrastructure
- Gross–Zagier + Kolyvagin (for BSD rank ≥ 1 with leading term)
- BRST cohomology connecting to dim E₆ = 78

These are multi-year community items. PF's role at the framework level
is providing the substrate prediction; the literal-form discharge waits
on upstream.

---

## Status table — at-a-glance

| Problem | Layer | Status 2026-06-09 |
|---|---|---|
| P1 — PolylogEigenvalueConjecture | P vs NP core | Open. Strictly ≥ P ≠ NP. |
| P2 — KatoRellichInput → LinearPMap | Operator side | Architecturally addressed via `VAlphaPMap.lean`; 4 sorries left. |
| P3 — alpha_of_class opacity | P vs NP scaffolding | Open. Tied to P1. |
| P4 — RHSpectralSurjectivity | RH bridge | Open. Strictly ≥ RH. |
| P5 — fractalEmergenceNoBlowup | NS bridge | Open. Vacuous target until mathlib upstream. |
| P6 — fractalYMMassGap | YM bridge | Open. Vacuous target until mathlib upstream. |
| P7 — fractalBSDRankEquality | BSD bridge | Open. Conditional on GZ + Kolyvagin. |
| P8 — Voisin 2007 obstruction | Hodge bridge | Open. Substrate work at structural level only. |
| P9 — 143-problem dataset | Empirical | Parametric version added 2026-06-09; needs real data. |
| P10 — IBM 9-way hardware data | Empirical | Heron-class softer falsifier is testable. |
| P11 — Mathlib upstream | Cross-cutting | Multi-year community work. |
