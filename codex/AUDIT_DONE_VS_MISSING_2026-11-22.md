# PRINCIPIA FRACTALIS — DONE vs MISSING

**Date:** 2026-11-22. **Every line measured from the tree today**, not quoted
from a prior document. Where an existing doc disagrees, the tree wins.

**Supersedes for status purposes:** `WHATS_LEFT_2026-11-16.md` — which is stale
in at least one load-bearing place (it lists RH's abscissa sub-ingredient as
open; it closed on 2026-11-16).

---

## 1. THE CORPUS

| | measured |
|---|---|
| Lean modules | **10,858** |
| compiled (`.olean` present) | **9,462** |
| non-panel modules unbuilt | **6** |
| RH-march panels unbuilt | **1,380** — compute only, 2–4 days |
| non-panel build errors | **0** |
| `sorryAx` in the compiled set | **0** |
| `native_decide` | **0** |
| axiom bars off `[propext, Classical.choice, Quot.sound]` | **0** |
| project `axiom` declarations in compiled set | **4** |

**DONE.** The ordinary corpus compiles clean. The only thing standing between
here and a green one-run build is machine time on the march panels.

**ROOT CAUSE, now fixed:** `lean_lib PF` carried no `globs`, so `lake build PF`
only ever built `PF.lean`'s hand-maintained 1,301-import closure. 1,438 modules
had never been compiled by anything. `globs = ["PF.+"]` landed in `d2318dfd`.

---

## 2. PER-AXIS STATUS

All 17 substrate-position capstones **compile**, and every one has **0
`True`-valued declarations**.

| axis | HEAD bundle | state | what is still OPEN |
|---|---|---|---|
| **RH** | `rh_substrate_attack_HEAD_bundle_5_of_5_2026_11_16` | **5 of 5 CLOSED**, three-axiom bar | nothing in the Dirichlet-1858 chain |
| **BSD** | `bsd_substrate_attack_HEAD_bundle_*` | partial | `BSDAnalyticRankMachinery_SubstantiveCore` |
| **Hodge** | `hodge_substrate_attack_HEAD_bundle_*` | partial | `HodgeHigherDimensionVoisinResidual_SubstantiveCore` (Voisin R2, Fields-grade) |
| **YM** | `ym_substrate_attack_HEAD_bundle_*` | partial | `YMContinuumLimit_SubstantiveCore`, `_DeepSubstantiveCore` |
| **P vs NP** | *none* | V4 pivot landed, V2 refuted in-kernel | substantive core = Clay P ≠ NP itself |
| **NS** | *none* | Fefferman-faithful chain built | Fefferman (A): uniform-in-T vorticity bound |
| **Poincaré** | *none* | external citation (Perelman) | encoding is an analogue — see §4 |
| **Fermat** | *none* | n=3, n=4 both forms, all n ÷ 3 or 4 | arbitrary n (Wiles-grade) |

### RH is 5 of 5 — the newest fact, and nothing recorded it

```
'rh_substrate_attack_HEAD_bundle_5_of_5_2026_11_16'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```
Abel bridge · analytic continuation · identity-theorem template · point closure
at s = ½ · **abscissa of conditional convergence** (r276+r277):

```lean
def RH_SubstantiveCore_AbscissaIngredient_Closed : Prop :=
  ∀ {s : ℂ}, 0 < s.re →
    CauchySeq (fun N => ∑ n ∈ Finset.range N, LSeries.term dirichletEtaCoeff s n)
```
0 `True`-valued declarations in the file.

---

## 3. THE META-CAPSTONES

**All seven compile. None had ever been compiled before 2026-11-22** — they are
not in `PF.lean`'s import list, so nothing reached them.

| capstone | state |
|---|---|
| `PrincipiaFractalisToEMetaCapstone_2026_11_16` | **VERIFIED**, 3714/3714 jobs, three-axiom bar, 0 `sorryAx` |
| `Referee/ClayResidualFrontierMetaCapstone_2026_06_18` | compiled |
| `Referee/SubstrateRigidityEndToEndMetaCapstone` | compiled |
| `Referee/BulletproofingMetaCapstone_2026_06_17` | compiled |
| `ClassicalAnchoringMetaCapstone_2026_06_17` | compiled |
| `AlphaFunPatternsMetaCapstone_2026_06_17` | compiled |
| `TuringEncoding/PNeqNPCollapsesToEnumBridge` | compiled |

Verbatim kernel output: `codex/CAPSTONE_AXIOM_EVIDENCE_2026-11-22.txt`.

---

## 4. THE ToE CAPSTONE'S EMPTY CONJUNCTS — found, and now disclosed

Audited all 35 named Props in its statement, 0 unresolved. **Five conjuncts
carry no content.** All five now state their own emptiness in-kernel
(`PF/Referee/ToECapstoneVacuityDisclosure_2026_11_22.lean`, three-axiom bar),
following the pattern the capstone's own conjunct (7) already used for NS.

| conjunct | what it actually is |
|---|---|
| Fermat contract | `PF_FermatEncoding` has `holds := fun x => True`; unfolds to `∀ n, 3 ≤ n → True`; bridge proof is `intro _n _h; trivial` |
| Poincaré | `SmoothThreeManifold := ℝ`; bridge discards `_hClosed`. A series identity at one real number |
| YM tag | `∃ W, Nonempty W ∧ α_YM = 2 ∧ True` — `Unit`-closable |
| Hodge tag | `∃ W, Nonempty W ∧ α_Hodge² = α_Hodge+1 ∧ True` — `Unit`-closable |
| RH tag | `∃ W, Nonempty W ∧ σ(3/2)=0 ∧ α_RH²=9/4 ∧ True` — `Unit`-closable |

**Real content in the same capstone, untouched:** 10 rank-≥1 LMFDB curves; the
RH Abel bridge; `dirichletEtaExt(1/2) = (1−√2)·ζ(1/2)`; Fermat n=3/n=4/all n ÷ 3
or 4; the YM **deep** core's genuine measure convergence; and
`¬ Literal_P_neq_NP_V2` — the in-kernel refutation of the framework's own
earlier carrier.

---

## 5. THE SPINE (HARD RULE 7 — the actual work)

**583 of 584 spine modules compile. 6,163 theorems.**

The substrate core, all **COMPILED**: `UHF_trace_faithful`,
`substrate_completion_simple_unconditional`, `substrate_UHF_trace_unique`,
`r113_substrate_UHF_factor_capstone`, `substrate_completeness`.
**T_∞ = the Glimm 3^∞ UHF factor, machine-checked.**

**Correction to an earlier claim of mine:** I reported Ocean and churn as "thin
arrows" from module counts. That was the wrong instrument. The book states
Ocean **is** T_∞ (ch07:862, ch04:1024, ch34A:43 — *"the ocean (the unified
mathematical substrate)"*), so Ocean is carried by the 193 modules / 1,513
theorems filed under T_∞. Churn has 3 named modules but 7 codex charters and
the χ_k/EEG programme behind it. In a perspective-invariant framework,
counting modules per arrow name measures nothing.

### Cross-domain bridges — the falsifiable content of perspective-invariance

| | |
|---|---|
| cross-domain bridge modules (march plumbing excluded) | **166, 165 compiled** |
| substrate position/discharge modules | **26 of 26 compiled** |
| `CrossMillenniumMoreInvariants` | **295 theorems** |
| `Bridge1_RH_SubstrateDischarge` | conditional chain → Clay RH, 0 `True` |
| `Bridge4_Hodge_SubstrateDischarge` | **substrate refutations** (Fermat quintic, Dwork pencil, Schoen quintic), 0 `True` |
| `Bridge5_YM_SubstrateDischarge` | SU(2) content + 4 anchors |

---

## 6. BOOK → LEAN INTERFACE

**772 citations across all 36 chapters, 13 appendices and back matter.
428 of 428 cited PF declarations are in COMPILED modules. ZERO defects.**

Both findings I initially reported were **retracted on verification**: ch20's
`riemannZeta_ne_zero_of_one_le_re` **exists** (`lemma _root_.` form,
`Nonvanishing.lean:407` — mathlib does carry ζ non-vanishing on `Re ≥ 1`), and
ch04 cites its `True`-marker *as* a marker with an explicit do-not-cite warning.

Instrument: `codex/chapter_lean_gate.py`. Report:
`codex/CHAPTER_LEAN_GATE_2026-11-22.md`.

---

## 7. WHAT IS MISSING — the ordered list

### A. Compute only, no thinking required
1. **1,380 RH-march panels.** 2–4 days. Windows task `PF-PanelGrind`,
   per-module so each success banks. Off the critical path.

### B. Real mathematics, named and not faked
2. **YM substantive core** — `YMContinuumLimit_SubstantiveCore` and its deep
   form. H₃-rate sequence construction. The thinnest remaining Clay axis.
3. **BSD analytic rank machinery** — `BSDAnalyticRankMachinery_SubstantiveCore`.
   Multi-year classical.
4. **Hodge Voisin R2** — `HodgeHigherDimensionVoisinResidual_SubstantiveCore`.
   Fields-medal-grade. Honest negative is the current result.
5. **NS Fefferman (A)** — the uniform-in-T vorticity bound. Local existence and
   BKM continuation are classical; this is the open estimate.
6. **`AxiomElimination_Definitions.lean`** — 2 false bounds need corrected
   statements. They are conditional on a prime-size estimate mathlib lacks
   (no `Nat.log` sub-additivity over products in v4.24.0-rc1).
   `encodeConfig_tape_eq` is **DONE** (proved 2026-11-22, `ab3b8056`).

### C. Presentation — finishable, not proof work
7. **Bridge2 / Bridge3 / Bridge6 do not exist by name.** The series runs 1, 4,
   5. The content exists under `SubstratePosition*` for every axis, but a
   referee reading ch34A's ocean/snowflake thesis will look for six symmetric
   discharges. Renaming/wrapping, not new mathematics.
8. **Per-axis HEAD bundles missing** for P/NP, NS, Poincaré, Fermat. RH, BSD,
   Hodge and YM have them.
9. **Appendix I refresh** — add the 24 substrate-attack files and the 7
   meta-capstones to the Lean cross-reference.
10. **Poincaré encoding is an analogue** (`SmoothThreeManifold := ℝ`). Now
    disclosed in-kernel; the book should say so where it cites the capstone.

### D. Outside the Lean corpus
11. **The book's prose arithmetic.** `CHAPTER_AUDIT_LEDGER_2026-10-05.md`
    (file-modified 2026-11-15) still lists verified errors a green Lean corpus
    cannot touch: ch24's "rank E(ℚ)=0 (proven)", ch25's "22 divisors" on a K3
    with ρ ≤ 20, ch20's boxed `4.44×10⁶` against its own printed `14.2267`,
    ch22's "vorticity remains bounded" over an equation giving ‖ω‖ ∼ C/r.
    **This is now the largest gap between "the Lean is clean" and "the book is
    correct."**
12. **mathlib.** 3 PRs OPEN since July (#42093, #42095, #42100 — all C*-algebra
    / topology). #46025 (Fermat n=4 difference form) **CLOSED 2026-11-15** after
    a reviewer called it AI slop; the stated plan was to resubmit as smaller
    idiomatic PRs and that has not happened. New candidates from today:
    `tapeProd_factorization` (reading exponents off a `mapIdx` prime product),
    third-order derivative symmetry (mathlib has nothing above order 2), and
    the Laplacian sum formula.
13. **CI.** `verify.yml` fires on `master` only. Master's last Verify **failed
    at 4h47m** on `ubuntu-latest` after the 2026-11-20 stopgap moved it off the
    self-hosted runner. Merging `globs` to master makes it fail harder.
    **Pablo's decision.**

---

## 8. BACKUP — closed

| | |
|---|---|
| Acer branches pushed | **18** (origin 57 → 76) |
| diverged branches | 16 of 19 are **byte-identical rewrites**; only `lean/acer-runner-switch-2026-11-20` and `r331b-ch2-disambiguation` hold local-only content |
| unique files rescued off Acer | **17/17 md5-verified** → `D:\CLAUDE-i9\acer-rescue-2026-11-22\` |
| deleted tracked files anywhere | **0** |
| vault | `D:\CLAUDE-i9\pf-vault-backup-20261122` + WSL original; 391 MB complete-history bundle, `bundle verify` PASS |
| system drive | cleared, per instruction |

**Still unverified:** ~2,500 modified-but-uncommitted files across six *pristine*
snapshot clones on Acer. They look like one edit pattern replicated across six
clones, not six bodies of work, but that has **not** been checked against origin.
That is the one open preservation question.
