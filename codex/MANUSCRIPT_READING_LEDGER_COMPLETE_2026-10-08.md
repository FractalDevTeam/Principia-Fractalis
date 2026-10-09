# Manuscript reading ledger — COMPLETE PASS, 2026-10-08

Author: Pablo Cohen + Claude Opus 5.
Commit at pass start `0ef96a27`; commit now `088fffe1`. Branch `master`, 113 ahead of
`origin/master`, UNPUSHED. Toolchain: Lean 4.24.0-rc1 / Lake 5.0.0 / mathlib `eed770a4`
/ Rocq 9.1.0.

**STATUS: PASS COMPLETE. 68 files, 38,995 lines, all read in full.**
Method: `cat -n` / `sed -n` line-by-line. No `rg`, no summaries, no prior AI reports used
as substitutes for reading. Nine reader passes; every load-bearing claim re-verified
against source by the coordinating session before entry here. Claims that failed
re-verification are recorded in §7 as STRUCK.

No manuscript mutation. No Lean/API mutation. No rename sweep. Commits `3cdd430c` and
`088fffe1` remain QUARANTINED. All six authorial questions remain deferred (§8).

---

## 1. THE STRUCTURAL FINDING

The self-audit layer is real, dated, and in several places excellent. **Its scope is the
defect.** The layer covers the chapter body and stops at three boundaries:

| Zone | Files | Self-audit markers | Verification ledger |
|---|---|---|---|
| ch01–ch35 body | 35 | present, dated, mostly accurate | present in nearly all |
| appendices A–I | 10 | **7 of 10 carry ZERO** | **ABSENT in 9 of 10** (appI only) |
| appendices J, K, L | 3 | **ZERO in all three** | **ABSENT in all three** |
| back matter (glossary, author, epilogue) | 3 | **ZERO in all three** (verified: 0 markers, 528 lines) | **ABSENT in all three** |

2,478 lines of appJ/K/L plus 528 lines of back matter are entirely outside the guard.

**The second half of the finding, and it is the repair direction:** the Lean corpus is
*more honest than the book*. `PF.lean:798` documents the Weinstein module as
"four typed Props ... := True", names an "honest-scope discriminator ... separates
concrete-witness clauses from typed-Prop clauses", and closes "NOT a Clay discharge;
structural encoding of Ch 11 only. ZERO project axioms."
`PF/AlphaSkeletonUniqueness_r128.lean:14-34` states outright: "**Wrong arity** ...
**Wrong P-vs-NP constant** ... **The corpus carries two different reals under two
near-identical names.**" `appI` L411-424 correctly records that the legacy Coq mirrors
are `Theorem name : True. Proof. exact I. Qed.`

The honest text already exists. It has not been propagated outward to the unguarded
files. Three recurring failure modes:

1. **Corrections do not reach restatements.** ch27's `-0.85` correction leaves `-0.95`
   standing in its Conclusion *and in its own verification ledger* (L745). ch30's L254
   metric correction leaves the transposed values in a second table (L343) and in an
   exercise telling students to verify the false match (L891). ch08 L630 and ch14 L657
   are ledgers still printing numbers their own 2026-10 corrections withdrew.
2. **Corrections do not reach other chapters.** The 590/588 dof pair that ch29 L391
   proves impossible is printed bare in ch27 L438/L443. ch27's withdrawn `-0.95`
   reappears unflagged in ch28 L643 and ch29 L603/L635.
3. **The highest-severity defects are structural, and all unflagged.** Measures whose
   own definitions cannot reach their thresholds; data replaced by predictions;
   fabricated verification checks.

---

## 2. PUBLICATION-BLOCKING — verified directly by the coordinating session

### 2.1 ch35 grants an MIT license the project does not grant
`LICENSE` = "PRINCIPIA FRACTALIS NON-COMMERCIAL RESEARCH LICENSE / Copyright (c) 2025
Pablo Cohen / **All Rights Reserved**". `CITATION.cff` = `license: "CC-BY-NC-4.0"`.
ch35 L766-772 prints a full MIT grant including the right to "sell copies".
Also: clone URL `github.com/pcohen/principia-fractalis` (3 occurrences) vs the real
remote `github.com/FractalDevTeam/Principia-Fractalis`; `CITATION.cff` quoted with every
field wrong (version 1.0.0 vs 2.6.1; placeholder ORCID `0000-0000-0000-0000` vs the real
`0009-0002-0734-5565`).
**Decision required before any further distribution.**

### 2.2 Two human-subjects sections with zero research-ethics documentation
Verified by exhaustive grep of both files.

| | ch30 (847 patients, 7 centres, 2015-2024) | appC (412 patients) |
|---|---|---|
| IRB / institutional review / ethics committee / ethics approval | **0** | **0** |
| informed consent (study) | **0** | **0** — §"Informed Consent" L414 governs prospective *clinical use* only |
| Helsinki / HIPAA / GDPR / de-identification | **0** | **0** |
| trial registration / preregistration / ClinicalTrials | **0** | **0** |
| funding / conflict of interest | **0** | **0** |
| inclusion or exclusion criteria | **0** | **0** |
| "retrospective" / "prospective" | 1 / 1 | **0 / 0** — design never stated |
| cross-validation / held-out set | **0** | **0** |

ch30 additionally prints an identifiable case — L430 "38-year-old male, basilar artery
stroke", L436 `Patient spelled: "I AM AWARE. PLEASE HELP."`, L438 "Family was preparing
to withdraw life support" — and reaches a care threshold at L714: "**Palliative
withdrawal may be ethically justified**" below ch_2 0.50, in a stratum its own L484
reports as 12 of 189 recovered (6.3%).
appC reaches L331-333 "Critical Decision Point: ch_2 < 0.50 at 72 hours ... Consider
withdrawal of life-sustaining therapy only with multidisciplinary consensus", on a
prognostic row (L325) of **0% good / 100% poor with no stratum n and no CI**.

### 2.3 The clinical measure cannot reach its own threshold
`appC` L185-232 `compute_ch2`: `F[i,j] = (Li-Lj)/(1+Li*Lj)` is antisymmetric, so
`trace(F@F) = -||F||_F^2 <= 0`, hence `ch2 = 1/(1+exp(-10*(ch2_raw-0.5))) <= 1/(1+e^5)
= 0.00669`. Executed on six random 19x19 coherence matrices: outputs 1.0e-7, 3.4e-11,
2.1e-13, 9.6e-14, 8.5e-16, 1.0e-8. Every clinical band above "coma" is unreachable and
every patient classifies as comatose.
Same class, independently: ch30 L197 `ch_2^clinical` normalised by `1/(M*5)`;
ch34 L305/L328 `(Tr(W^2) - (Tr W)^2)/(2||W||_F^2) <= 1/2` for every real `W` (proved by
Cauchy-Schwarz; ch06's own 2026-10-03/05 remarks state the cap) while L338 prints 0.963
and L345 requires `> 0.95`; appendix_lexicon L242 the same formula against the same
threshold.
**Safety-critical.** ch30 and appC thresholds also contradict appH L342-346, whose own
empirical values ("Normal Waking ch_2 ~ 0.6", "Sleep (NREM) ~ 0.3") classify a healthy
awake adult as *vegetative* and a sleeping one as *comatose* under appC L247-248.

### 2.4 A measurement replaced by the prediction, labelled "(corrected)"
`appH` L204, inside a table titled "Universal Constant sigma_c = 0.95 Across All
Domains" whose every other row reads 0.95:
`CMB Anomalies & ch_2^cosmic = 0.60 +/- 0.05 -> 0.95 (corrected)`
(0.95 - 0.60)/0.05 = **7.0 sigma**. No mechanism, no systematic, no date, no citation.

### 2.5 appA: three of four tabulated high-altitude zeros are not those zeros
Recomputed with `mpmath.zetazero`, dps=40:

| n | appA L105-108 claims | actual t_n |
|---|---|---|
| 1000 | 1419.422481061186155553338 | 1419.42248094599568646599 (diverges at digit 12) |
| 2000 | 2771.421680003894900731678 | **2515.28648292471288003819** |
| 5000 | 6373.803858964906432855864 | **5447.86199830129985641216** |
| 10000 | 11477.505264622853184623892 | **9877.78265400550114277410** |

The claimed values are systematically too large and consistent with an *asymptotic
estimate* printed to 25 digits as though computed. The `|zeta(1/2+it_n)|` column does
not reproduce either: at the true t_1, |zeta| = 1.929e-49 against a claimed 2.3e-51
(84x). Reader-measured, not re-checked here: zeros 11-20 wrong from digits 19-40, with
the corresponding |zeta| entries off by 16-34 orders. L230 also credits "This work" with
**10^14** zeros in an appendix that computes 10,000.

### 2.6 Bibliography: two fabricated `note` fields, two cited sources absent
```
@article{vazirani2018quantum,  Vazirani & Vidick,
  title = {Fully Device-Independent Quantum Key Distribution},
  note  = {Quantum complexity and oracle robustness} }
@article{aaronson2020quantum,  Aaronson & Chen,
  title = {Complexity-Theoretic Foundations of Quantum Supremacy Experiments},
  note  = {P vs NP oracle independence and natural proofs} }
```
ch17 L610 cites both for "the P vs NP separation is resilient only under specific oracle
conditions and cannot rely on 'natural' proof constructions." One is a QKD paper; the
other is quantum supremacy. The real sources (Baker-Gill-Solovay 1975,
Razborov-Rudich 1997) are not cited. Cited by name with no entry at all: `berti`
(ch19 L341), `glimm1960` (appI L46), `voisin2007` (appI L248).
Bibliography holds **388** entries; ch34 L718 claims 366.

### 2.7 The documented software suite does not exist
Verified absent from the entire tree: `principia_fractalis/`, `pyproject.toml`,
`setup.py`, `requirements.txt`, `tests/`. **Zero** `test_*.py` outside `ARCHIVE/`.
`tools/audit.sh` exists only at `ARCHIVE/2026-06-08-cleanup/dirs/tools/audit.sh`.
`PF_Coq` does not exist (the tree has `PF_Coq_Code`).
Consequences: appD (192 lines of API reference) documents nothing that exists; ch35's
Quick Start (`pip install -r requirements.txt` -> `pytest tests/ -v` ->
"47 passed in 124.3s") and its "47 unit tests, 90%+ coverage" describe nothing; appI's
reproduction recipe fails at `cd PF_Coq && make` (L398) and at `bash tools/audit.sh`
(L402), so the zero-project-axioms claim at L403-404 cannot be run as written.
appA/appD/appF/appH reference **16 data files that are MISSING**; 6 of appH's 10 JSON
datasets are absent and the other 4 exist only inside `ARCHIVE/2026-06-08-cleanup/`.

### 2.8 Back matter: eight unscoped Clay discharges, zero scope markers
Verified: glossary 117 lines / **0** markers; author 137 / **0**; epilogue 274 / **0**.
- glossary L46 "Hodge Conjecture: ... **Solved in this framework** through consciousness crystallization."
- glossary L54 "Millennium Prize Problems: ... **This framework solves all remaining six.**"
- glossary L56 "Navier-Stokes ... **Solved here** through fractal-enhanced dissipation."
- glossary L64 "P versus NP: ... **Solved here** through spectral gap analysis: Delta = 0.0891219046."
- glossary L70 "Riemann Hypothesis: ... **Proven here** through self-adjoint operator construction."
- glossary L90 "Yang-Mills ... **Solved here**: Delta_YM = 420.43 MeV."
- author L36 "**Complete solutions to all six** remaining Clay Millennium Prize Problems"
- epilogue L46 "**The Millennium Problems are solved**"

Against appK L1004-1007, which states the session "**does not close any Clay-grade
conjecture**", and against every chapter ledger ("NOT proven here and remains open").
Two of the eight publish numbers their own chapters retracted: `Delta_YM = 420.43 MeV`
is refuted by ch23's 2026-08-06 ledger (`omega_c = 2.13198462` "does not exist"), and
`Delta = 0.0891219046` is contradicted by ch07's 2026-10-07 correction, which records
`PF/SpectralGap.lean` certifying the gap as **0.0539677287**.

### 2.9 ch20 rests on a theorem ch03 declares REFUTED
ch03 L497 names the chain in its own words: "ch03 -> ch09 (§ch:spectral_unity) -> ch20
rests on this theorem", where ch03 L481 reads "**REFUTED** --- Theorem thm:rh-resonance
asserts ...". Verified in ch20: **zero** occurrences of "refut", **zero** of
"rh-resonance", and its only chapter references are `ch:consciousness`, `ch:constants`,
`ch:resonance`, `ch:timeless-field` — **ch09 is never referenced**. The refuted claim is
restated at L104 as "Forces all zeros to Re(s) = 1/2" inside unproved
`thm:alpha-three-halves`. None of ch20's four verification paragraphs mentions it.

### 2.10 ch21 does not disclose the degenerate `ClassP`
Verified: ch21 contains **zero** occurrences of `ClassP`, `ClassNP`, `InClassP`. The only
chapter file mentioning `ClassP` anywhere is ch34A. Under the current PF definitions
`InClassP` carries a context-invariance condition forcing every represented language to
be `emptyset` or `univ`, so the machine-checked `ClassP != ClassNP` concerns a defective
proxy encoding and does not formalize the standard Clay problem. Neither of ch21's two
ledgers records this; L1455's "PROVEN but not about complexity" bullet lists only the
alpha-algebra and the 2026-05-18 brackets.

### 2.11 appL's prover of record is the version the project forbids
`PF_Coq_Code/TOOLCHAIN.md` L13: "**`coqc --version` must print `9.1.0`. If it prints
`8.18.0`, stop — nothing you build will be usable.**" L31: "8.18.0 has **no mathcomp**,
so `PF_Real/` cannot build at all under it"; L32: the `.vo` files are
"**binary-incompatible**".
appL names **Coq 8.18** four times (L4, L365, L426, L438) as the prover of record,
including in the three-prover parity section — and `PF_Real/` (4 files, **110**
declarations, verified) is precisely the one genuinely re-proved Coq layer.

### 2.12 appL's anchor inventories do not match the corpus
`ProjectiveSpace` — claimed at appL L150 as the Hodge "literal mathlib carrier" — is
**ABSENT from the entire Lean corpus** (verified). appL L140 claims an `Iff.rfl` bridge
to "mathlib's analytic-rank/algebraic-rank equality"; mathlib4 has no analytic rank for
elliptic curves, and the corpus's own semantic-bridge file records both sides as
framework-defined (`algebraicRankV5 = analyticRankV5`), as appJ L382-388 states.
Reader-measured, not re-checked here: of the 52 named anchors, substantial fractions are
absent from the cited files (3 of 8 RH, 2 of 8 PNP, 2 of 5 NS, 2 of 7 YM, 5 of 7 Hodge,
5 of 10 empirical), with real anchors omitted; seven cited file paths do not resolve; and
all 52 are `Prop := True` while counted at L459-462 as "109 **New theorems** ...
axiom-free".

### 2.13 `H^2 = 78 = dim E_6` is three arithmetic tautologies
`PF/Consciousness/WeinsteinGUResonantRescue.lean`, verified verbatim:
```lean
theorem brst_H2_eq_78 : (78 : N) = 78 := rfl
theorem brst_H2_sm_decomposition : 78 = 48 + 26 + 4 := by decide
theorem brst_H2_matches_E6_dim_aux : (78 : N) = 78 := ...dim_E6_eq_78
```
Docstring: "The BRST cohomology dimension of GU with RQG correction matches the observed
Standard Model + gravity particle count of 78 DOF." No BRST complex, no cohomology group,
no E_6 root system appears. The decomposition's physics labels are also wrong: "26 gauge
boson DOF" against the Standard Model's 12 gauge bosons.
appI L339 attributes this, plus `|Psi_RQG|^2 = ch_2 = 0.95` and the `R^13 -> R^4`
projection, to `App~\ref{app:weinstein}` — and **none of `|Psi_RQG|`, 0.95, R^13->R^4,
78, E_6 or H^2 appears anywhere in appE** (120 lines, read in full).
Mitigating and important: `PF.lean:798` discloses all of this accurately. The book does
not.

### 2.14 ch19 prints "This is not a coincidence" on numbers wrong by 20 orders
ch19 L117 boxed formula `m_n^2 = M_Pl^2 exp[-2pi/|zeta'(rho_n)|]`, recomputed at dps=30:

| | ch19 L135-137 | computed |
|---|---|---|
| rho_1 | 0.5 MeV (electron?) | 2.32e17 GeV |
| rho_2 | 105 MeV (muon?) | 7.70e17 GeV |
| rho_3 | 1.8 GeV (tau?) | 1.24e18 GeV |

L140-142: "The first three zeros give masses remarkably close to the three charged
leptons! **This is not a coincidence.**" The ledger labels the conjecture "numerological";
it does not reach the fabricated check beneath it. L520 and the L485-490 exercise depend
on it.

### 2.15 appF publishes a circular RH proof carrying `\qed`
appF L48-50, verbatim:
```
This violates the Riemann Hypothesis (all zeros on critical line).
Therefore, no zeros exist for $\Re(s) > 1/2$. \qed
```
RH is assumed at L48 to conclude RH's content at L50. L41 additionally asserts
"Gamma(1-s_0) != 0", but Gamma(1-s) has poles at s = 1,2,3,..., so the displayed product
is 0*infinity; and "sin(pi s_0/2) != 0 (not at integer)" fails at s_0 = 2,4,6,..., all of
which satisfy Re(s_0) > 1/2.

---

## 3. ARITHMETIC RE-VERIFIED AS WRONG (sample; exact anchors)

| Anchor | Printed | Recomputed |
|---|---|---|
| ch21 L444 | 0.5988854382 | **0.5988104758** |
| ch21 L532 | sin(2.221441469) = 0.798635510 | **0.7956932016** |
| ch21 L533 | phi = 1.941495408 | **1.9416110387** |
| ch21 L534 | -0.847127424 | **-0.8528711517** |
| ch21 L539 | 0.9427... | **0.9329582786** |
| ch21 L993 | \|0.1330222423 - pi(sqrt5-1)/(30sqrt2)\| < 1e-10 | **0.0414938202** |
| ch21 L1114 | P(all 143 by chance) < 1e-43 at 95% baseline | 0.95^143 = **6.523e-4** |
| ch21 L1570 | "Verify that D(27) = 0" | 27 = 1000_3, **D(27) = 1** |
| ch20 L425 | alpha* = (ch_2 - 0.95)/R_f ~ 5e-6 | **exactly 0** at the chapter's own threshold (L52, L428) |
| ch20 L501 | "the second-lowest ratio observed" | 0.226 is the **minimum** of the eight |
| ch22 L274 | R_f(3pi/2, s) = sum e^{i3pi D(n)/2}/n^s | phase shown is **alpha = 3/2**, not 3pi/2 |
| ch29 L262-268 | "13 BAO measurements" | itemised list gives **9** |
| ch29 L302 | row labelled d_A(0.38) = 1533 (LCDM) | 1533 is comoving D_M; d_A = D_M/(1+z) = **1111** |
| ch08 L262 | exp[-(1e-30)(1e80)] ~ 1e-120 | exponent is **1e50**; 1e-120 = e^-276.3 |
| ch11 L37 | dim Spin(13,1) = 8192 | n(n-1)/2 = **91**; so A_14 = 73, not 8174 |
| lexicon L253 | exp(pi^2/12) ~ 707.1 | **2.276108** |
| lexicon L256 | kappa = 5.00e-6 | **2.007e-8** (249x) |
| appF L147 | (0.95)^-122 = 5e-3 | **5.2206e+2** (the positive power was computed) |
| appH L7/L37 | "exponential convergence" | deviation x N = 0.812 on all 8 rows: a pure **1/N** law |
| appE L62 | "This 1% reduction exactly cancels" | 0.99% vs a 1.908% deficit (**1.93x**) |
| appK L819 | 1e-5 propagates to ~0.13 | 78pi*0.95 = 232.8, so **0.0023** (56x) |

## 4. STALE AND SELF-INCONSISTENT COUNTS

- `lake build PF` is **5149** jobs today. The book prints 4044 (ch34 L692), 4186 (appJ L18),
  4724 (ch34 L851, appI L21), 5105 (appI L30), 5147 (ch34 L693), 8360 (appJ L435),
  8648-8652 (appK L37/L406/L959). Seven figures, none current.
- `.lean` under `PF/` is **6376**; ch34 L693 says 6373. Closure is **1455**; it says 1452.
  (Both drifts are from this session's own additions.)
- `PF_Coq_Code` holds **765** `.v`; appI L418's "110 theorems" is correct for `PF_Real/`
  but appI nowhere mentions Rocq, 9.1.0, or the current 683/683.
- `m_C` carries four incompatible values across ch12-ch14 (2.7e27 eV, 1e-5 eV, 1e-22 eV,
  1e-3 eV); ch12 L336's correction flags two.
- `Delta` carries four values (0.0891219046, 0.05397, 0.1330222423, 0.08127);
  `PF/TuringEncoding/SpectralGapInconsistencyAnalysis.lean` proves them pairwise unequal.
- Two alpha-dictionaries coexist: `PF.lean:96` `alpha_PvsNP := 5/4` against the book's
  `alpha_NP = phi + 1/4`. `PF/AlphaSkeletonUniqueness_r128.lean` flags it; appI L208
  prints 5/4 unflagged.
- **14 wrong chapter cross-references** (appB L4, appC L4, appD L4,
  appF L27/29/52/54/85/121/123/153/164, appH L455/456) — and appH L452 asserts
  "All cross-references validated".
- Systematic chapter-minus-4 offset in exercise cross-refs: ch15 L599, ch17 L547, ch19 L497.

## 5. THEOREM-ENVIRONMENT INVENTORY

Chapters with **zero** `\begin{proof}`: ch29 (7 theorems), ch32 (8). ch34 has zero
theorem environments at all. ch30 has one, and its computed values contradict the theorem
it closes. Unproved theorem-class environments: ch31 11/12, ch33 6/7, ch21 10 + 4
sketch-only, ch20 5 + 2, ch22 5, ch08 10 of 11, ch14 6 of 6.
Across ch31-ch33 alone: **23 of 27**. Most are empirical assertions or textbook citations
typeset as theorems. All four ch11 proofs that are not numerically refuted defer to
`\cite{cohen2025weinstein}`, which `bibliography.bib:3221` records as
`howpublished = {Unpublished manuscript}` by the book's own author.

## 6. WHAT HELD UP — recorded so it is not re-litigated

- Criteria (a) olean currency, (b) axioms subset {propext, Classical.choice, Quot.sound},
  (c) no sorry/sorryAx/native_decide/project axioms: **zero failures** across the whole
  1455-module closure. ch34 L693's clean verdict is confirmed on a corpus 2.7x the June one.
- Every `sorry` / `native_decide` grep hit in the appI-cited Lean files is **comment
  prose**, verified line by line. Not a defect; recorded so it is not chased again.
- appI invents no theorem names and no module paths: **42 of 42** tested names FOUND.
- All 17 `\includegraphics` figures in appH are PRESENT.
- appK's algebra is sound where it is checkable: the 29 simultaneous identities, the
  Fibonacci ladder, the 9 pentagonal cyclotomic identities, the reciprocal/square quartet
  (18 entries), the log layer, the Hodge and NP towers, the P discriminant 29-12sqrt5, and
  the 45-clause master capstone all re-derived and verified.
- appK L989-1007 is the best-scoped passage in the three appendices.
- appI L243-246 (BSD de-scoping) and L411-424 (the Coq parity ledger) are exemplary.
- ch24 is the best-scoped Clay chapter; ch03's pi/10 entry (EMPIRICAL / OPEN) and
  ch06's `rem:c2-scoping-2026-07-01` are both already the correct positions.
- `sigma(alpha) = log_3|1 + 2cos(pi alpha)|` (r212) remains the corpus's one genuine,
  non-circular base-3 alpha-selection mechanism.

## 7. READER CLAIMS STRUCK ON RE-VERIFICATION

1. **ch34 L698 "all 18 Wave 58 `.v` files"** — reported stale against 683/765. The claim
   is scoped to Wave 58; `PF_Coq_Code/PF/Wave58/` holds 49 files and 18 is defensible as
   a headline subset. STRUCK.
2. **ch34 L693 "self-refuting grep claim"** — reported as containing "A grep for
   2026-10-03 over this chapter returns zero matches". L693 read in full: that sentence is
   **not there**. The two `2026-10-03` hits are in L598, a different correction. STRUCK as
   misattributed.
3. **ch34 L693's counts** — stale by 3 files and 2 jobs, and the drift is from this
   session's own additions. Downgraded from "decay" to bookkeeping.
4. **appC "no consent statement"** — there IS a §"Informed Consent" at L414. It governs
   prospective clinical use, not the N=412 study. Narrowed, not struck: the study-level
   gap in §2.2 stands.
5. **ch30 "consent appears twice"** — it appears **once** (L316). Corrected in the
   direction of worse.

## 8. SIX AUTHORIAL QUESTIONS — ALL STILL DEFERRED

1. ch08 `Theta(ch_2 - 0.95)`: reading R1 or R2 (R1 raises a Gisin-Polchinski signalling
   hazard; R2 does not). The same gate recurs unflagged at ch12 L386.
2. ch09 vs ch07: which of `lambda_0(H_P)`, `lambda_0(H_NP)` is larger. ch17 L614 uses the
   opposite sign order from ch07 L176.
3. ch07 `thm:p-np-gap`: which operator the printed digits denote.
4. The consciousness-strata dimension in the Grothendieck appendix: which invariant
   (set dimension is excluded — `dim` rises while `S_t` shrinks).
5. ch10 `d_f`: which multifractal model, or whether a spectrum `D(h)` replaces a single `d_f`.
6. ch07 pi/10: whether to restate as the product invariant `alpha * lambda = pi/10` with
   `pi/h(H_3) = pi/10` as candidate origin, per ch03 and the version log.

## 9. STANDING CONSTRAINTS

1. Both commits remain QUARANTINED. `0ef96a27` also requires review: its §2 and its title
   claim ("it is i*pi, not pi/10") exceed what its proofs establish; `i*pi` is a chain-rule
   prefactor and `pi/10` is the `alpha*lambda` product invariant. Its four Lean
   declarations are PROVISIONAL pending exact audit.
2. No manuscript mutation, no Lean/API mutation, no rename sweep without Pablo's approval.
3. Gate sweep read-only and not to be relaunched. 909 PRISTINE / 546 FAILED = **62.5%**
   of 1455; zero build-artifact failures; all 546 semantic. Per-criterion: (d)=67,
   (d2)=275, (e)=372, (f)=129. ch34 reports no pristine rate at all.
4. Preserve all dirty, untracked, backup and user-owned work. 44 `*.prefix_2026-10-07*`
   backups, and `PF_Lean4_Code/PF/Analytic/RiemannXiTopEdge_r331c.lean` (standing
   instruction), confirmed present.
5. Next after this pass: the exact Lean audit with direct elaboration and `#print axioms`
   of `PF/SigmaAbscissa_r212.lean`, `PF/H3CoxeterOrigin.lean`,
   `PF/PoincareAlphaFromH3CoxeterHalfArg.lean`, `PF/NSAlphaFromH3ExponentSum_r340.lean`,
   `PF/SpectralGap.lean`, `PF/Consciousness/RfAlphaScalingConstantBase3.lean`, and the
   exact ChernWeil / consciousness-measure definitions used by ch04, 06, 07, 18, 30, 31.
6. Still open from the earlier directives: all six claimed mathlib gaps audited against
   both the pin and current master (2 of 6 done; at least `Unitary.conjStarAlgAut` and
   `StarSubalgebra.coe_iSup_of_directed` are present on master); a read-only rename
   inventory; the OpenAI index discrepancy (56 families in CONTENTS.md vs 372 claimed);
   deconfliction of `codex/` writers.

---

## 10. PROVENANCE AND A DATA-PRESERVATION WARNING

Nine reader passes produced roughly 500 individually anchored findings. Their raw output
files on the coordinating host are **0 bytes** — the reports were delivered in-band only.
This ledger records the verified publication-blocking set, the structural inventory, and
representative anchors. **The full per-chapter detail is not on disk anywhere.** If the
line-by-line inventory is wanted as a durable artifact, the per-file passes must be re-run
with output written directly to `codex/` rather than returned in-band.

`codex/` is treated as CONTENDED: an earlier data race in this session was caused by a
read-modify-write with no version check. This file is written as a new dated artifact and
overwrites nothing. It is NOT committed.
