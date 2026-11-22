# Per-chapter Lean gate — all 36 chapters, 13 appendices, back matter

**Date:** 2026-11-22. **Tree:** `/home/xluxx/pf-legion-20261120/PF_Lean4_Code`
(10,856 `.lean`). **Book:** `Principia_Fractalis_master_folder` (56 `.tex` in
`chapters/`, `appendices/`, `backmatter/`).
**Index built over:** 381,979 PF names + 279,244 mathlib names, 11,010 PF
namespaces, 23,277 PF module tokens.

## What this gate asks, and why it is new

The 2026-11-14 citation audit (`LEAN_CITATION_AUDIT_2026-11-14.tsv`, 591 rows)
asked whether each cited Lean name **exists**. It could not ask whether the
name's module **compiles**, because until 2026-11-21 `lean_lib PF` carried no
`globs`, so `lake build PF` only ever built `PF.lean`'s hand-maintained
1,301-import closure. 1,438 modules had never been compiled by anything.

This gate asks four questions per file: cited / resolves / **compiled** /
**vacuous**.

## Result

| | |
|---|---|
| citations found | **772** (655 unique) |
| resolve to a PF declaration | **428** |
| **of those, in a COMPILED module** | **428 — 100%, zero uncompiled** |
| resolve to mathlib | 41 |
| resolve to a PF namespace / module | 25 |
| filenames or data artifacts (not Lean) | 55 |
| genuinely vacuous (`True`-valued) | **1** |
| genuinely absent | **1** |

**Every Lean name the book cites, in every chapter and appendix, now resolves
to a module that compiles.** That was not true before 2026-11-22.

## Per-file table

| zone | file | cite | uniq | PF | compiled | vacuous | mlib | struct | file | unres |
|---|---|---|---|---|---|---|---|---|---|---|
| ch | ch01_numbers | 7 | 7 | 4 | 4 | 0 | 3 | 0 | 0 | 0 |
| ch | ch02_complex | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | ch03_resonance | 2 | 2 | 1 | 1 | 0 | 0 | 0 | 1 | 0 |
| ch | ch04_timeless_field | 18 | 15 | 14 | 14 | **1** | 1 | 0 | 0 | 0 |
| ch | ch05_peixoto | 4 | 4 | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| ch | ch06_consciousness | 14 | 14 | 14 | 14 | 0 | 0 | 0 | 0 | 0 |
| ch | ch07_constants | 2 | 2 | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| ch | ch08_field_equations | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | ch09_spectral_unity | 11 | 11 | 10 | 10 | 0 | 1 | 0 | 0 | 0 |
| ch | ch10_hydrodynamic | 6 | 2 | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| ch | ch11_geometric_unity | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | ch12_qft_consciousness | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | ch13_solutions_dynamics | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | ch14_symmetries_conservation | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | ch15_computational_methods | 4 | 4 | 0 | 0 | 0 | 0 | 0 | 2 | 2 |
| ch | ch16_spectral_foundations | 12 | 10 | 6 | 6 | 0 | 0 | 3 | 1 | 0 |
| ch | ch17_operator_theory | 5 | 5 | 4 | 4 | 0 | 0 | 0 | 1 | 0 |
| ch | ch18_spectral_measures | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | ch19_physical_applications | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 0 |
| ch | ch20_rev2_dirichlet_eta_inserts | 32 | 31 | 20 | 20 | 0 | 3 | 1 | 4 | 3 |
| ch | ch20_riemann_hypothesis | 46 | 38 | 26 | 26 | 0 | 3 | 1 | 4 | 4 |
| ch | ch21_p_vs_np | 13 | 9 | 8 | 8 | 0 | 0 | 0 | 0 | 1 |
| ch | ch22_navier_stokes | 23 | 16 | 12 | 12 | 0 | 0 | 0 | 0 | 4 |
| ch | ch23_yang_mills | 18 | 13 | 5 | 5 | 0 | 4 | 1 | 3 | 0 |
| ch | ch24_birch_swinnerton_dyer | 31 | 21 | 12 | 12 | 0 | 2 | 1 | 0 | 6 |
| ch | ch25_hodge_conjecture | 4 | 4 | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| ch | ch26_cosmological_constant | 3 | 3 | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| ch | ch27_dark_energy_expansion | 5 | 4 | 3 | 3 | 0 | 0 | 0 | 1 | 0 |
| ch | ch28_early_universe | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| ch | ch29_observational_tests | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| ch | ch30_clinical_consciousness | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | ch31_neuroscience_iit | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | ch32_consciousness_quantification | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | ch33_numerical_methods | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch | **ch34A_substrate_theorem** | **109** | 85 | **66** | **66** | 0 | 4 | 2 | 0 | 13 |
| ch | **ch34_verification** | 82 | 71 | **51** | **51** | 0 | 4 | 0 | 4 | 12 |
| ch | ch35_software | 9 | 9 | 0 | 0 | 0 | 0 | 0 | 8 | 1 |
| app | appA_zeros | 5 | 5 | 0 | 0 | 0 | 0 | 0 | 5 | 0 |
| app | appB_brst … appG_notation | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| app | appH_numerical_validation | 10 | 10 | 1 | 1 | 0 | 0 | 0 | 9 | 0 |
| app | **appI_lean_cross_reference** | **142** | 127 | **85** | **85** | **1** | 9 | 6 | 0 | 27 |
| app | appJ_refinement_pass | 91 | 79 | 54 | 54 | **1** | 5 | 1 | 3 | 16 |
| app | appK_residual_compaction | 34 | 30 | 3 | 3 | 0 | 0 | 9 | 7 | 11 |
| app | appL_substrate_bundle_closure | 14 | 8 | 1 | 1 | 0 | 2 | 0 | 0 | 5 |
| app | appM_toe_diagram | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 0 |
| app | appN_chapter_diagnostic_sheet | 12 | 12 | 11 | 11 | 0 | 0 | 0 | 0 | 1 |
| app | appendix_grothendieck | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| back | lexicon / author / epilogue / glossary | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| | **TOTAL (56 files)** | **772** | **655** | **428** | **428** | 3→**1** | 41 | 25 | 55 | 106→**1** |

## The two real findings

**1. ch04 cites a vacuous declaration.**
`scope_tensor_carrier_untouched` is `theorem … : True := trivial`
(`PF/TernaryNetInfiniteCompleteness_r359.lean:128`). Cited in
`ch04_timeless_field.tex`. It carries no content.

**2. ch20 cites a mathlib lemma that does not exist, and the near-miss
matters mathematically.**
The book cites `riemannZeta_ne_zero_of_one_**le**_re` (twice: in
`ch20_riemann_hypothesis.tex` and the rev-2 Dirichlet-eta inserts). Mathlib
`v4.24.0-rc1` has:

* `riemannZeta_ne_zero_of_one_**lt**_re` — `NumberTheory/LSeries/Dirichlet.lean:313`
* `LFunction_ne_zero_of_one_**le**_re` — `NumberTheory/LSeries/Nonvanishing.lean:394`
  (Dirichlet L-functions, not ζ)

`Re > 1` non-vanishing is elementary from the Euler product. Non-vanishing **on
the line** `Re = 1` is Hadamard / de la Vallée Poussin. The citation as written
claims the closed-line result for ζ, which mathlib does not supply under that
name. Either repoint to `_one_lt_re` and scope the claim, or cite the Dirichlet
L-function lemma and say so.

## Corrections to this gate's own first pass — recorded so the numbers are usable

A first pass reported **229 missing** and **3 vacuous**. Both were wrong, and in
the same direction: the instrument's blind spots, reported as the book's defects.

* It indexed only `PF/`, so **every mathlib name** counted as missing
  (`MemLp`, `riemannZeta`, `SchwartzMap`, `WeierstrassCurve`, `Iff.rfl`,
  `Int.Fermat42.not_fermat_42`, `DifferentiableOn.analyticOnNhd`).
* It saw only **top-level declarations**, so structure **fields** counted as
  missing — `u0.isDivFree` (129 uses in PF), `PFSubstrateConsequences.NS_via_substrate`.
* It treated **filenames and data artifacts** as Lean names — `riemann_zeros.csv`,
  `PF.lean`, `requirements.txt`, `evolve.c`, `principia_fractalis.core`,
  `*.json`.
* Its 3-line vacuity window caught a **neighbouring** `True`, so
  `Clay_NavierStokes_Standard` was flagged vacuous when it is
  `∀ u0, E.isSchwartzDivFree u0 → E.hasGlobalSmoothSolution u0`.

Nine of fourteen "absent" names were verified present on individual check:
`PF.SpectralGap.P_neq_NP`, `PF.Analytic.XiPositive.Xi_Positive_At_15`,
`BSD_HeegnerRank1Proof.bsd_rank_one_E37a1_via_heegner_and_GZ_K`,
`Ch24Descent2TorsionRatBridge_2026_10_17.Ecurve_rank_eq_zero`,
`Fermat42Sub.exists_minimal`, and the mathlib/core names above.

**Do not quote the 229 or the 3.** The usable numbers are 428/428 compiled,
1 vacuous citation, 1 absent citation.

## Scope — what this gate does NOT check

It checks the book→Lean interface only: that cited names exist, compile, and
are not `True`. It does not check the book's **prose arithmetic**, which has its
own campaign (`CHAPTER_AUDIT_LEDGER_2026-10-05.md`, last modified 2026-11-15)
and which a green Lean corpus cannot validate. ch24's false "rank E(ℚ) = 0
(proven)", ch25's "22 divisors" on a K3 with ρ ≤ 20, ch20's boxed `4.44 × 10⁶`
against its own printed `14.2267` — none of those are visible to this gate.
Compiling is necessary and not sufficient.
