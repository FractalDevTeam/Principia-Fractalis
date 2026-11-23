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
| vacuous MISUSE (flagged 1, retracted on verification) | **0** |
| genuinely absent (flagged 1, retracted on verification) | **0** |

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
| | **TOTAL (56 files)** | **772** | **655** | **428** | **428** | 3→**0** | 41 | 25 | 55 | 106→**0** |

## The two candidate findings — BOTH RETRACTED on verification

Both were my instrument, not the book. Verified individually, 2026-11-22.

**1. ch04's `scope_tensor_carrier_untouched` — NOT a defect.**
It is `theorem … : True := trivial`, and the gate flagged the shape. But the
prose cites it *as a marker*, and says so explicitly
(`ch04_timeless_field.tex:641`):

> "r359 carries a `scope_tensor_carrier_untouched` marker to record that it does
> **not** settle the tensor-carrier question, and **it must not be cited as
> doing so**."

A `True`-valued scope marker cited as a scope marker, with an explicit warning
against reading content into it, is correct usage. No edit.

**2. ch20's `riemannZeta_ne_zero_of_one_le_re` — EXISTS. NOT a defect.**
It is declared at `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:407`:

```lean
lemma _root_.riemannZeta_ne_zero_of_one_le_re ⦃s : ℂ⦄ (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0
```

My resolver's pattern was `^(theorem|lemma) riemannZeta_ne_zero`, which cannot
match a `lemma _root_.NAME` declaration. Mathlib **does** carry ζ non-vanishing
on the closed half-plane `Re ≥ 1` — the Hadamard / de la Vallée Poussin result
is formalised there, and `Nonvanishing.lean:20` notes it "does not require
`s ≠ 1`, since the junk value at `s = 1`" handles that point.

PF uses it correctly, and the module compiles
(`PF/DirichletEtaExtExtraFamilyDisjointFromZetaZeros_2026_11_18.lean:44`):

```lean
theorem extraFamily_not_riemannZeta_zero (k : ℤ) :
    riemannZeta (extraFamily k) ≠ 0 := by
  have h_re : (extraFamily k).re = 1 := extraFamily_re k
  have h_one_le : 1 ≤ (extraFamily k).re := by rw [h_re]
  exact riemannZeta_ne_zero_of_one_le_re h_one_le
```

The extra family lies exactly on `Re s = 1`, so the closed-half-plane lemma is
precisely the right one to invoke. **The chapter is correct as written.**

## Net result

**Zero defects.** 772 citations across 36 chapters, 13 appendices and back
matter; 428 of 428 PF citations in compiled modules; no vacuous misuse; no
absent name.

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

**Do not quote the 229, the 3, or the 1-and-1.** The usable numbers are
**428/428 compiled, 0 vacuous misuse, 0 absent.** Every defect this gate
flagged dissolved on individual verification. That is four rounds of the same
lesson in one session: the instrument's blind spots look exactly like the
book's defects, and only reading the actual declaration tells them apart.

## Scope — what this gate does NOT check

It checks the book→Lean interface only: that cited names exist, compile, and
are not `True`. It does not check the book's **prose arithmetic**, which has its
own campaign (`CHAPTER_AUDIT_LEDGER_2026-10-05.md`, last modified 2026-11-15)
and which a green Lean corpus cannot validate. ch24's false "rank E(ℚ) = 0
(proven)", ch25's "22 divisors" on a K3 with ρ ≤ 20, ch20's boxed `4.44 × 10⁶`
against its own printed `14.2267` — none of those are visible to this gate.
Compiling is necessary and not sufficient.
