# Principia Fractalis — Revision Guide for rev3

*Living document. Updated 2026-04-27. Pabs's actionable per-chapter punch list, consolidating the 2026-04-26/27 verification audits, the V01 catalog reconciliation, and the manuscript-level rigor pass. Each item links to the canonical audit document (V01) where applicable.*

---

## Status legend

- 🔴 **MUST-FIX before referee submission** — internal inconsistency or false numerical claim
- 🟠 **SHOULD-FIX for rigor** — derivation gap, hand-wave, or missing methodology
- 🟡 **NICE-TO-FIX** — placeholder content, stale docstring, or documentation drift
- 🟢 **DISCLOSED, no action required** — already cited as conjecture or open question

---

## Frontmatter

🟢 The "Verification check pending V01 reconciliation" section in `frontmatter/rev2_formalization_status.tex` cites the canonical V01 audit documents (`DERIVATION_ANALYSIS_alpha_NP.md`, `MATHEMATICAL_VALIDATION_REPORT.md`) and the `fractal_continuation_derivation.py` numerical fix. Last touched commit `a315725`.

🟡 The "8 axioms remain" frontmatter claim refers to the canonical `PF_Lean4_Code/PF/` library only. The repository's top-level `*.lean` files (e.g. `YM_Equivalence.lean`, `RH_Equivalence.lean`, `BSD_Equivalence.lean`) carry an additional ~240 axioms not in the canonical count. The frontmatter could explicitly disclose this scope distinction.

---

## Ch 20 — Riemann Hypothesis

### 🟠 Self-adjointness derivation (Theorem 20.2)

The 2026-04-26 verification pass found that with the operator and inner product as transcribed verbatim, $\tilde{T}_3$ is not self-adjoint on $L^2([0,1], dx/x)$. Pabs's own `MATHEMATICAL_VALIDATION_REPORT.md` (2025-11-30) catalogs three specific errors:

- §2.2: For Li_1, monodromy shifts are purely imaginary — cannot move the principal-branch real part from −0.465 to +0.222
- §2.4: Sine identity is numerically false (0.933 vs claimed 0.412)
- §2.5: Eigenvalue ratio inconsistent (claimed (√5−1)/3 = 0.412 vs (legacy) empirical 0.5988) — **CLOSED by v3.3.1 (2026-05-20 propagation)**: the legacy 0.5988 empirical was a buggy-pipeline artifact; certified empirical ratio is √2/(φ+1/4) ≈ 0.7570, matching the canonical Lean closed form exactly. The (√5−1)/3 prediction remains REFUTED. See `MATHEMATICAL_VALIDATION_REPORT.md` v3.3.1 reconciliation header.

**Recommended action**: Either adopt `Evidence_and_Data_for_GitHub/fractal_continuation_derivation.py`'s numerical fix (s ≈ 0.182, m = −1 in the Jonquières expansion) and revise the chapter accordingly, or demote Theorem 20.2 to a Conjecture.

### 🟡 HS-norm √3 claim (line ~252)

Already covered by the post-rev-2 disclosure. A singular-kernel transfer operator is not generically Hilbert-Schmidt on L²(dx/x); the previously claimed HS norm √3 was unrelated to a literal HS computation. Should be replaced with a precise statement of what bounds the operator actually satisfies (e.g., "trace-class on a holomorphic-Bergman subspace") or removed.

### 🟢 Numerical eigenvalue table (§20.5) and α* fit (§20.6)

Currently cited by the post-rev-2 frontmatter as "computed against the operator that the verification pass did not confirm". If Theorem 20.2 is downgraded or the operator redesigned, these numerics need recomputation against the redesigned operator.

---

## Ch 21 — P vs NP

### 🟠 α_P = √2 and α_NP = φ + 1/4 derivation

Pabs's `DERIVATION_ANALYSIS_alpha_NP.md` (2025-11-30) explicitly catalogs these as "ASSERTED but NOT RIGOROUSLY DERIVED". Four specific gaps:
- No explicit derivation of G_NP(z)
- Reality condition not solved from first principles  
- 1/4 correction has no derivation
- φ-from-certificate-trees connection is heuristic

Numerical match is solid; the closed-form derivation is not. Recommended: add a "Derivation status" remark per the V01 audit document, or use the demoted "Conjecture" framing.

### 🔴 Generating function transcription (line 286)

Manuscript transcribes $\sum_m N_m^{(3)} z^m = \prod_{k=0}^\infty (1 + z + z^2 \cdot 3^k)$.

**This is divergent as written** — the $3^k$ multiplier makes the coefficient of $z^2$ a divergent sum. Pabs's actual derivation script `Evidence_and_Data_for_GitHub/alpha_sqrt2_derivation.py` uses the well-defined finite product $(1 + z + z^2)^N$ taken in a limit.

**Recommended action**: replace the line-286 formula with the correct finite-N → ∞ limit form (a one-line edit aligning with the derivation script).

### 🟢 Lean 4 formalization

The arithmetic spectral-gap-positivity result is independent of the closed-form gaps and is a genuine Lean 4 theorem. The three BOOK-CORE axioms (`operator_collapse_hypothesis`, `p_eq_np_spectrum_collapse`, `turingTimeComplexity`) are honestly disclosed as conditional in `AXIOM_AUDIT.md`.

---

## Ch 22 — Navier–Stokes

### 🔴 Topological Stability theorem (line 194) proof error

Proof at lines 198–224 claims $\int(u' \cdot \nabla)u_0 \cdot u' \, dx = 0$ for divergence-free perturbations. **This integral is the Reynolds–Orr energy production term** (Joseph 1976; Drazin–Reid 2004), which is the standard source of hydrodynamic instabilities, not zero.

Counter-rotating vortex pairs are empirically known to be unstable to 3D Crow-type and elliptic instabilities at moderate Reynolds number (Crow 1970; Leweke–Williamson 1998; Kerswell 2002).

**Recommended action**: Either (i) restrict the perturbation class to one that genuinely makes the production term vanish, (ii) replace with an energy-stability-Reynolds-number bound (the standard formulation), or (iii) demote Theorem 22.X to a conjecture pending a different mechanism.

### 🟠 No-blowup theorem (line 303) — Step 4 inconsistency

Step 4 (lines 346-357) asserts $\lim |u| = 0$ AND $\lim |\omega|/r^{-1} = C < \infty$ simultaneously. These are **mutually inconsistent** under Biot-Savart (which gives $u \sim \log r$ when $\omega \sim 1/r$). Step 5 also lacks a contradiction argument or T*-supremum closure.

If the no-blowup chain depends on Topological Stability above, the chain breaks. A coordinated revision should restructure or flag as conjectural.

### 🟢 Coq formalization disclosure

`PF_Coq/theories/Contracts/NavierStokes.v` Theorem `PF_NS_Solution` carries the ⚠ CONDITIONAL THEOREM disclosure block (commit `58e8ce8`).

---

## Ch 23 — Yang–Mills

### 🔴 Mass gap formula dimensional error (line ~374)

$\Delta = \hbar c \cdot \omega_c \cdot \pi/10 = 420.43$ MeV claimed.

- $\hbar c \approx 197.3$ MeV·fm
- $\omega_c \approx 2.13$ is dimensionless
- Product: ~132 MeV·fm, **not 420.43 MeV**

The chapter silently drops the fm. Even drops aside, the magnitude is off by 3.18× from the claimed value.

**What WOULD give 420.43 MeV**: $m_{\text{proton}} c^2 \cdot \omega_c \cdot \pi/10 = 421$ MeV (within 0.1%), but no derivation explains why proton mass should appear in a glueball gap formula. The $4.07\times$ ratio to lattice $m_{0^{++}} \approx 1710$ MeV suggests reverse-engineering.

**Recommended action**: Either (i) introduce an explicit independently-motivated length scale $r_0 \approx 0.314$ fm, (ii) replace $\hbar c$ with a genuine mass scale, or (iii) reframe the formula with the prefactor declared independently and the lattice match labeled as consistency-check rather than prediction.

### 🟢 YM-cluster theorems

Already disclosed: each Lean 4 theorem in `PF/YangMillsMeasure.lean` carries a ⚠ CURRENT PROOF CAVEAT docstring noting they are proven against `CovarianceOperator.quadraticForm := 0`.

---

## Ch 24 — Birch and Swinnerton-Dyer

### 🔴 Self-adjointness phase-symmetry argument (Theorem 24.X proof sketch)

Proof invokes "statistical conjugation symmetry" $D(p) \equiv -D(p) \pmod 4$ (i.e., base-3 digit sum of every prime is even). **Empirically false**: $D(5) = D(12_3) = 3$ (odd), $D(7) = D(21_3) = 3$ (odd), $D(11) = D(102_3) = 3$ (odd).

**Recommended action**: Either (i) restrict to a subset of primes where the symmetry holds, (ii) replace with a different mechanism (measure-weighted averaging not requiring pointwise digit-sum parity), or (iii) demote to conjecture.

### 🟠 thm:spectral-concentration-bsd (line 285) missing proof

Stated without an attached proof environment. The underlying claim (multiplicity = rank at $\varphi/e$) is axiomatized as `rank_equals_multiplicity` in `PF_Coq/theories/Contracts/BSD.v`.

### 🟡 "100% success on tested curves with conductor < 100,000"

Numerical claim (chapter §339 area). Should reference the underlying dataset by file name and commit hash.

---

## Ch 25 — Hodge Conjecture

### 🔴 σ_c = 0.95 reverse-engineered decomposition (Theorem 25.X)

Decomposition $\sigma_c = 6/\pi^2 + \epsilon_{\mathrm{quantum}} = 0.6079 + 0.3421 = 0.95$.

The "quantum correction" $\epsilon_{\mathrm{quantum}} \approx 0.3421$ has **no first-principles derivation** anywhere in the chapter. It is numerically chosen to make the sum equal 0.95.

**Recommended action**: Either (i) provide an independent derivation of $\epsilon_{\mathrm{quantum}}$, or (ii) restate the threshold as an empirical observation.

### 🔴 α-dictionary inconsistency (this chapter vs supplementary proof)

This chapter uses $\alpha = \varphi = (1+\sqrt{5})/2$ for the Hodge spectral operator.

The supplementary 2492-line proof at `Evidence_and_Data_for_GitHub/Hodge_Conjecture_Proofs/hodge_complete_1800_lines.md` (line 335) uses $\alpha = \pi/2$ for the **same operator**.

These are two different operators with different spectra. **They cannot both be canonical.**

**Recommended action**: Pick one (already declared rev2 manuscript's α = φ as canonical in commit `73ee703`); update the supplementary file to match, or document both as distinct constructions. Note added at the top of `hodge_complete_1800_lines.md` documenting the divergence.

### 🟠 thm:hodge-concentration (line 323) missing quantitative argument

"Proof sketch" at lines 330-345 says rationality + Hodge condition + Galois "force eigenvalue coefficients to satisfy $\sum |c_n|^2 \geq 0.95 \|\xi\|^2$". No quantitative argument for *why* the constant is 0.95. The "ratchet effect" sentence is metaphor.

---

## Ch 31 — Neuroscience / IIT

### 🟠 LLM ch_2 datapoints (Proposition prop:llm)

Numerical estimates (GPT-4: 0.42 ± 0.15; LLaMA-3: 0.34 ± 0.10; Claude-3: 0.51 ± 0.11) appear in a Proposition environment but no LLM-specific ch_2 measurement protocol is described. The ch_2 protocol given earlier in the chapter is for EEG-like temporal data.

**Recommended action**: Either (i) describe the LLM measurement protocol explicitly (which sample inputs, what spectral-resonance pipeline, what gives ±0.11 uncertainty), or (ii) move the numerical claims to a Conjecture/Speculation environment.

---

## Cross-cutting

### 🔴 Three different α-Millennium dictionaries

The canonical files use different conventions for α across the Millennium-Problem operators:
- rev2 ch25 (Hodge): α = φ
- `hodge_complete_1800_lines.md`: α = π/2 for Hodge
- ch21 (P vs NP): α_P = √2, α_NP = φ + 1/4
- ch20 (RH): α = √2 in the H_P setup
- ch23 (YM): α_YM = 2

**Recommended action**: Establish a single per-Millennium-problem α-dictionary in the frontmatter or in a new appendix, and ensure every chapter and supplementary file references it consistently.

### 🟠 The "π/10 universal factor"

Appears in ch21, ch23, ch24, ch25 as if it has a derivation. **It does not** — appears phenomenologically and is cited circularly across chapters. A referee will catch this within an hour.

**Recommended action**: Either provide a single unified derivation of why π/10 is the "universal scale-bridging constant" across all five Millennium operators, or label it explicitly as an empirically-observed common factor.

### 🟠 Coq formalization parity

Coq has 253 axioms (broader scope than Lean's canonical 8); ~33 Lean axiom eliminations from earlier rev2 work have not been ported to Coq. The Millennium-claim "Theorems" in `Contracts/{NavierStokes, BSD, Hodge}.v` carry ⚠ CONDITIONAL THEOREM disclosure blocks (commit `58e8ce8`) but have not been demoted to `Lemma` declarations.

### 🟡 Lean4Lean (third formalization layer)

Currently quarantined to `experimental/PF_L4L_future/`. Lakefile path was fixed (commit `e0ab8f7` → `2e511f7`); full restoration requires either expanding the canonical PF/ scope (inflates the 8-axiom claim) or rewriting L4L's `rfl`-based agreement proofs (changes design intent). Pending architectural decision.

### 🟡 Bibliography placeholders

18 `cohen2025*` self-citations marked "In preparation" or `Unpublished manuscript` — honest disclosure but should be replaced with arXiv IDs / DOIs once papers are uploaded.

### 🟢 226 orphan bib entries

Bibliography has 367 entries; only ~141 unique cite commands across chapters. The 226 unused entries are legitimate background reference material; not removed.

---

## Recommended sequence for rev3

1. **🔴 must-fix tier (4 items)**: Ch21 generating function transcription (one-line edit), Ch22 Topological Stability (operator-redesign or conjecture-demote), Ch23 mass gap formula (dimensional/derivation fix), Ch24 phase-symmetry (replace or demote), Ch25 σ_c = 0.95 (derivation or empirical), Ch25 α-dictionary (already partially fixed)
2. **🟠 should-fix tier**: derivation gaps in ch20, 21, 24, 25, 31 — each adds a "Derivation status" remark or revises a claim
3. **🟡 nice-to-fix tier**: bibliography placeholders, L4L architectural decision, Coq parity port, π/10 universal-factor disclosure

**Estimated rev3 scope**: 100-150 lines of manuscript edits (mostly demoting Theorems to Conjectures or adding derivation-status remarks); 1-2 weeks of focused work; no new mathematical research required (existing V01 audit catalog already supplies the disclosures).

---

*Each tier-classification reflects what a peer reviewer would catch within 1 hour (🔴), within 1 day (🟠), within 1 week (🟡), or already disclosed (🟢). The mandate "everything verifiable in three languages" is best served by completing tier 🔴 + 🟠 before the rev3 release, with tier 🟡 as future work.*
