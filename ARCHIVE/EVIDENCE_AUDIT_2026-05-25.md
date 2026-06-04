# Evidence_and_Data_for_GitHub Audit — 2026-05-25

Author: audit pass (read-only)
Scope: every cite of an external evidence file from the rev 2 manuscript chapters
       (`Principia_Fractalis_master_folder_rev2/chapters/`) and the
       `Evidence_and_Data_for_GitHub/` payload that backs them.

## Inventory

Evidence_and_Data_for_GitHub/ (recursive)

- Total files: 95
- By extension: .json = 84, .py = 5, .md = 3, .csv = 2, .png = 1
- Subdirectories: Academic_Impact_Analytics, Hodge_Conjecture_Proofs,
  IBM_Quantum_Verification, Master_Documentation, Python_Analysis_Scripts,
  Riemann_Hypothesis_Proofs, Scaling_Convergence_Analysis

Top-level evidence files explicitly cited from the manuscript live in:
- `Evidence_and_Data_for_GitHub/Riemann_Hypothesis_Proofs/complete_riemann_proof_results.json` (1.3 KB)
- `Evidence_and_Data_for_GitHub/Hodge_Conjecture_Proofs/hodge_complete_results_20250614_025444.json` (5.8 KB)
- `Evidence_and_Data_for_GitHub/Hodge_Conjecture_Proofs/hodge_complete_1800_lines.md` (94 KB, 2530 lines)
- `Evidence_and_Data_for_GitHub/alpha_sqrt2_derivation.py` (26 KB)
- `Evidence_and_Data_for_GitHub/fractal_continuation_derivation.py` (11 KB)
- `Evidence_and_Data_for_GitHub/IBM_Quantum_Verification/143 Problems Solved On IBM.py` (68 KB, 812 lines)
- `Evidence_and_Data_for_GitHub/IBM_Quantum_Verification/143 Problems Solved On IBM Results.csv` (47 KB, 143 data rows)

The remaining 88 files are auxiliary copies (timestamped variants, duplicates
suffixed " (1).json", scaling-study sweeps) not directly cited from chapters.

## Manuscript ↔ Evidence cross-reference

The chapters' explicit external-evidence cites fall into two buckets:
(A) BibTeX `\cite{cohen2025*}` keys to data artifacts, and
(B) `\texttt{...}` mentions of files at repo root or in
    `Evidence_and_Data_for_GitHub/`.

| Cite key / path | Chapter | Evidence path checked | Status | Notes |
| --- | --- | --- | --- | --- |
| `\cite{cohen2025riemanndata}` | Ch 20 line 439 | `Evidence_and_Data_for_GitHub/Riemann_Hypothesis_Proofs/complete_riemann_proof_results.json` | PRESENT | Bib entry `howpublished` field names this exact basename. |
| `\cite{cohen2025hodgedata}` | Ch 25 line 457 | `Evidence_and_Data_for_GitHub/Hodge_Conjecture_Proofs/hodge_complete_results_20250614_025444.json` | PRESENT | Bib entry `howpublished` field names this exact basename. |
| `\texttt{Evidence_and_Data_for_GitHub/alpha_sqrt2_derivation.py}` | Ch 21 line 1276 | same | PRESENT | 723 lines incl. `digital_sum_base3`, `(1+z+z^2)^N` generating function. |
| `\texttt{Evidence_and_Data_for_GitHub/fractal_continuation_derivation.py}` | Ch 20 line 295 | same | PRESENT | `s = 0.182049937912121`, `m = -1`, target $\pi/(10\sqrt 2)$, Jonquières expansion. |
| `\texttt{Evidence_and_Data_for_GitHub/Hodge_Conjecture_Proofs/hodge_complete_1800_lines.md}` | (referenced as the long Hodge writeup) | same | PRESENT | 2530 lines (note in header: "preserved as alternative α-parametrisation"). |
| `\texttt{complete_riemann_proof_results.json}` | Ch 20 line 439 | `Riemann_Hypothesis_Proofs/complete_riemann_proof_results.json` | PRESENT | Same artifact as `cohen2025riemanndata`. |
| `\texttt{hodge_complete_results_20250614_025444.json}` | Ch 25 line 457 | `Hodge_Conjecture_Proofs/hodge_complete_results_20250614_025444.json` | PRESENT | Same artifact as `cohen2025hodgedata`. |
| Implied: 143-problem dataset | Ch 21 §"Computational Validation Across 143 Problems" | `IBM_Quantum_Verification/143 Problems Solved On IBM Results.csv` | PRESENT | 143 rows. Confirmed peak_alpha = 1.5 (RH), 1.868 (P vs NP). Not cited by explicit `\cite{}` or `\texttt{}` — implicit only. |
| `\texttt{ALPHA_UNIQUENESS_CERTIFICATION.md}` | Ch 7 line 189; Ch 9 line 117; Ch 21 lines 24, 446, 535, 1280 | (repo root expected per chapter prose) | **MISSING** | Cited 6 times for "Nov 11 2025, 50-digit precision" certification of `λ_0(H_NP) = 0.168176418230`. Not found anywhere in repo. |
| `\texttt{BOSS_DIVISION_PROOFS_SCAFFOLDING_COMPLETE.md}` | Ch 9 line 120; Ch 21 lines 24, 439, 1280 | (repo root expected per chapter prose) | **MISSING** | Cited 4 times as v3.3.1 errata correction log. Not found. |
| `\texttt{Principia_Fractalis_v3.3.1_ERRATA_CORRECTED_20251108.pdf}` | Ch 9 line 120; Ch 21 line 24 | (repo root expected) | **MISSING** | November 2025 errata PDF. Not found. |
| `\texttt{p_neq_np_spectral.tex}` | Ch 21 line 24 (described as "Pabs's arXiv submission") | (would be under `Papers/` if present) | **MISSING** | Not in `Papers/`. `Papers/` contains only `paper_A_framework.tex`, `paper_B_formal_verification.tex`, `paper_C_empirical_quantum_signatures.tex`. |
| `\texttt{feedback_close_the_loop.md}` | Ch 26 line 316 | `/home/xluxx/.claude/projects/-home-xluxx/memory/feedback_close_the_loop.md` | MOVED (intended location) | The chapter calls it a "memory file" so it is correctly identified as a personal memory artifact, not a repo file. Lives in Claude memory store. Treat as PRESENT-in-memory. |
| `\texttt{ALPHA_UNIQUENESS_CERTIFICATION.md}` / `\texttt{BOSS_DIVISION_*}` / `\texttt{...ERRATA....pdf}` (consolidated) | Ch 7, 9, 21 | — | **MISSING (load-bearing)** | These four file cites are the primary documentary backing for the v3.3.1 numerical correction story (`0.1330` → `0.168176418230`). Their absence is the single biggest evidence gap. |
| `\texttt{MATHEMATICAL_VALIDATION_REPORT.md}` | Ch 20 line 285 | `/home/xluxx/Principia-Fractalis/MATHEMATICAL_VALIDATION_REPORT.md` | PRESENT (repo root) | — |
| `\texttt{DERIVATION_ANALYSIS_alpha_NP.md}` | Ch 20 line 285; Ch 21 line 1269 | `/home/xluxx/Principia-Fractalis/DERIVATION_ANALYSIS_alpha_NP.md` | PRESENT | — |
| `\texttt{OPEN_PROBLEMS.md}` | Ch 21 lines 662, 1259 | `/home/xluxx/Principia-Fractalis/OPEN_PROBLEMS.md` | PRESENT | — |
| `\texttt{AXIOM_AUDIT.md}` | Ch 21 line 1259 | `/home/xluxx/Principia-Fractalis/AXIOM_AUDIT.md` | PRESENT | — |
| `\texttt{REVISION_GUIDE.md}` | Ch 20 line 295; Ch 21 lines 1276 (+); Ch 23 line 519 | `/home/xluxx/Principia-Fractalis/REVISION_GUIDE.md` | PRESENT | — |
| `\texttt{RESEARCH_ROADMAP.md}` | Ch 16 line 441; Ch 22 line 445; Ch 23 line 333; Ch 25 line 494 | `/home/xluxx/Principia-Fractalis/RESEARCH_ROADMAP.md` | PRESENT | — |
| `\texttt{THE_REAL_SCIENCE.md}` | — (mentioned only in `\texttt{}` form in supporting docs) | `/home/xluxx/Principia-Fractalis/THE_REAL_SCIENCE.md` | PRESENT | — |
| `\texttt{PRISTINE_CERTIFICATION.md}` | (chapter cite) | `/home/xluxx/Principia-Fractalis/PRISTINE_CERTIFICATION.md` | PRESENT | — |

## Content sanity check on top-5 PRESENT files

1. **`Riemann_Hypothesis_Proofs/complete_riemann_proof_results.json`**
   Contains `convergence_analysis.scaling_convergence` with
   `N_values = [10,20,30,40,50,60,80,100]` and
   `limit = 0.08126700914373787`. Ch 20 line 439 claims "limiting spectral
   gap $\Delta = 0.08127$ for $N \in \{10,20,30,40,50,60,80,100\}$". Numbers
   match to the digits cited. **Matches manuscript claim.**

2. **`Hodge_Conjecture_Proofs/hodge_complete_results_20250614_025444.json`**
   Contains `calabi_yau.N_basis = 30`, `statistics.mean_concentration = 0.6309682…`,
   `statistics.max_concentration = 0.989343…`, plus K3, Abelian, complete-intersection
   sections. Ch 25 line 457 claims "mean concentration 0.6310, maximum 0.9893 for
   Calabi-Yau test cases at basis dimension $N=30$". **Matches to 4 decimals.**

3. **`alpha_sqrt2_derivation.py`** (26 KB, dated 2025-11-30 in header)
   Header: "DERIVATION: Self-Adjointness Forces d_H = sqrt(2) for Radix-3
   Digital Sum Operators". Contains `digital_sum_base3`, `digital_sum_counts`,
   generating function `(1+z+z^2)^N`. Ch 21 line 1276 says this script "uses
   the finite generating function $(1+z+z^2)^N$ for the P-class case". **Matches.**

4. **`fractal_continuation_derivation.py`** (11 KB)
   Header solution: "s = 0.182049937912121, m = -1" giving
   `Re[Li_s^[-1](z)] = 0.222144146907916 = pi/(10*sqrt(2))`. Ch 20 line 295 says
   the script "contains the proposed numerical fix for the principal-branch
   problem ($s \approx 0.182$, $m = -1$ in the Jonquières expansion)".
   **Matches exactly.**

5. **`IBM_Quantum_Verification/143 Problems Solved On IBM Results.csv`**
   143 data rows. Spot-check confirmed: RH `peak_alpha = 1.5` (row 2);
   P vs NP `peak_alpha = 1.8680000000000003` (row 4 — matches `φ + 1/4 ≈ 1.868034`
   to 4 decimals). Manuscript cross-claims (the framework memory of
   "hardware-measured peak_alpha = 1.5 EXACT for RH and 1.868 for P vs NP")
   are reproduced verbatim in this CSV. **Matches.** No `\cite{}` or
   `\texttt{}` ties the chapter prose to this exact file, but Ch 21 §"Computational
   Validation Across 143 Problems" is the implied consumer.

## Missing / Stub priority list

Severity grades reflect downstream load-bearing on rev 2 manuscript claims.

**HIGH severity — load-bearing for v3.3.1 numerical-correction narrative**

1. `ALPHA_UNIQUENESS_CERTIFICATION.md` (cited 6× across Ch 7, 9, 21)
   - Bears the load: "50-digit-precision certification that the certified
     empirical $\lambda_0(H_{NP}) = 0.168176418230$ matches the closed form
     $\pi/(10(\varphi+1/4))$ to $5\times10^{-11}$".
   - Without it, the manuscript's "matches to $10^{-10}$" claim has no
     reproducible artifact in the repo.
   - Remediation: either (a) author the .md from the underlying mpmath
     computation (one short script suffices — the algebra is decidable), or
     (b) replace each `\texttt{ALPHA_UNIQUENESS_CERTIFICATION.md}` with a
     Lean theorem name in `PF/SpectralGap.lean` already certifying the bracket,
     or (c) add a pointer to the existing 143-problem CSV row whose
     `peak_alpha = 1.868` is the empirical anchor.

2. `BOSS_DIVISION_PROOFS_SCAFFOLDING_COMPLETE.md` (cited 4× across Ch 9, 21)
   - Bears the load: the "correction log" for the
     `0.1330222423 → 0.168176418230` retraction.
   - Without it, the v3.3.1 errata story is unverifiable. Same remediation
     options as above.

3. `Principia_Fractalis_v3.3.1_ERRATA_CORRECTED_20251108.pdf` (cited 2× in Ch 9, 21)
   - Bears the load: the published-errata anchor for the v3.3.1 numerical
     change. Not present as PDF or as `.tex` source. Remediation: either
     produce the errata document or rewrite the cite as "v3.3.1 internal
     correction (this manuscript, §X)".

4. `p_neq_np_spectral.tex` (cited 1× in Ch 21 as "Pabs's arXiv submission
   (Feb 2026)")
   - Per memory file `principia_turing_arxiv_bridge_2026-05-24.md` Pabs has a
     DRAFT arxiv submission that is NOT yet on arxiv; this `.tex` may be that
     draft, but it is not under `Papers/` and not anywhere in the repo.
   - Remediation: locate / commit the draft into `Papers/`, or downgrade the
     in-text claim ("Pabs's arXiv submission … uses the corrected values
     throughout") to "draft arXiv submission in preparation".

**LOW severity — soft references**

5. `feedback_close_the_loop.md` (Ch 26)
   - Cited explicitly as a "memory file"; lives in Claude memory store, not
     the repo. Treated as PRESENT-in-memory; no action needed unless a
     referee wants in-repo provenance, in which case copy the relevant
     paragraph into a repo-root doc.

**No STUBs detected** among the 7 directly-cited evidence files; all five
JSON/py/md targets opened contained substantive content matching the
manuscript's numerical claims.

**Auxiliary files (88 of 95)**: many timestamped variants and " (1).json"
duplicates. Not load-bearing for any chapter cite I located. Optional
hygiene action: prune duplicates or document the timestamped-variant
convention.

## Self-citation status (`cohen2025*` / `cohen2026*` keys)

Actual usage in chapters via `\cite{}`:

| Cite key | Cited from | Bib entry kind | Backing artifact | Status |
| --- | --- | --- | --- | --- |
| `cohen2025riemanndata` | Ch 20 | `@misc`, `howpublished = complete_riemann_proof_results.json` | `Riemann_Hypothesis_Proofs/complete_riemann_proof_results.json` | PRESENT, content matches |
| `cohen2025hodgedata` | Ch 25 | `@misc`, `howpublished = hodge_complete_results_20250614_025444.json` | `Hodge_Conjecture_Proofs/hodge_complete_results_20250614_025444.json` | PRESENT, content matches |
| `cohen_corroborating_2026` | (chapter) | `@unpublished` | None — placeholder | PROMISSORY (no file) |
| `cohen_systematic_review_2026` | (chapter) | `@unpublished` | None — placeholder | PROMISSORY (no file) |

Bibliography entries that exist but are **never actually `\cite{}`'d** in any
chapter (all dataset/in-preparation placeholders): `cohen2025riemann`,
`cohen2025consciousness`, `cohen2025peixoto`, `cohen2025omega`,
`cohen2025grothendieck`, `cohen2025technicalappendix`, `cohen2025xenon`,
`cohen2025cnt`, `cohen2025cosmology`, `cohen2025software`, `cohen2025book`.
These are inert — no chapter prose breaks if their backing files do not
exist, but they bulk up the bibliography. Optional remediation: prune unused
entries, or migrate them to a separate "in-preparation" section.

The memory line "Cited external artifacts (cohen2025*) are MISSING."
(from `principia_five_bricks_full_status_2026-05-23.md`) was **partially
falsified** by this audit: the two cite keys actually referenced from chapters
(`cohen2025riemanndata`, `cohen2025hodgedata`) DO map to present files with
matching content. The memory item likely referred to the broader set of
unused-but-defined placeholder entries (and to the missing
`ALPHA_UNIQUENESS_CERTIFICATION.md` / `BOSS_DIVISION_*` / `ERRATA.pdf` /
`p_neq_np_spectral.tex` set above), which remains accurate as a concern.

No assertions about external arxiv presence are made; arxiv hosting is not
verifiable from the local filesystem.
