# Publication Suite — Principia Fractalis

**For**: Pablo Cohen
**Date**: 2026-06-06
**HEAD**: `202e671`
**Status**: Publication-ready. Honest scope preserved across all papers.

This document is a plain-language guide to what to post, where, in what order, and with what framing. Read this first. Then use `POSTING_CHECKLIST.md` for the step-by-step. Use `ARXIV_ENDORSEMENT_OUTREACH.md` for the draft messages you will send.

---

## 1. What is in this suite

### 1.1 The five papers (in `Papers/`)

1. **`clay_substrate_reformulation_v1.pdf`** — Master paper (14 pages). The unified substrate-level reformulation of all six remaining Clay axes via one mechanism. This is the headline paper.

2. **`clay_RH_via_substrate_v2.pdf`** — Phase 1 (8 pages). Riemann Hypothesis as the substrate-level entry vector. Targets the analytic number theory audience.

3. **`clay_six_simultaneous_closure_v1.pdf`** — Phase 2 (10 pages). The simultaneous-closure mechanism. ONE bundle, six Clay-Standards on canonical encodings.

4. **`clay_PvsNP_via_substrate_v2.pdf`** — Phase 3 (7 pages). P vs NP substrate-level reformulation. Highest application ceiling.

5. **`principia_fractalis_keystone_v1.pdf`** — Phase 4 (10 pages). The keystone — consciousness operator, ZPE bundle, cosmological brackets. What the substrate is FOR beyond the Clay axes.

### 1.2 The supporting material

6. **852-page manuscript** at `Principia_Fractalis_master_folder/main.pdf` — V2.1.1. The full structural text. Link from each paper's bibliography.

7. **Lean 4 codebase** at `PF_Lean4_Code/` — 8226 jobs clean, kernel-only axioms `[propext, Classical.choice, Quot.sound]`, zero project axioms.

8. **Coq parity mirror** at `PF_Coq_Code/` — 243 `.v` files mirroring the Lean namespace. Parity-only (about 75% of definitions are `: Prop := True` typed mirrors). Do not present this as independent semantic verification.

9. **Lean4Lean re-verification harness** at `PF_Lean4Lean/` — 4039 jobs clean. Same-language Path-C second pass through Lean's kernel from a separate Lake package. Build-hash robustness, not an independent type-checker.

---

## 2. Posting order — recommended

Three tiers. Tier 1 is what you post yourself today. Tier 2 needs an endorser. Tier 3 is direct outreach to specific people.

### Tier 1: ResearchGate / Academia.edu / Google Scholar

You post these yourself. No endorsement needed. Use the order below. Each paper cross-links to the others in its bibliography.

#### 2.1 Order

**Paper 1 — Master paper first**

- File: `Papers/clay_substrate_reformulation_v1.pdf`
- Title to use: *A Substrate-Level Reformulation of the Six Remaining Clay Millennium Problems via the Principia Fractalis Framework*
- One-paragraph abstract for the posting page:

  > This paper presents a substrate-level reformulation of the six remaining Clay Millennium Problems (Riemann Hypothesis, P vs NP, Navier–Stokes, Yang–Mills, BSD, Hodge) via the Principia Fractalis framework. This is not a Clay-prize claim. The six axes are not discharged at the literal mathlib tier required by the Clay rules. The mechanism is: (i) an alpha-skeleton with editorial convention alpha_Poincaré = 1 motivated by Perelman 2003; (ii) eleven framework-internal arithmetic compatibility identities on nine chosen alpha-values; (iii) canonical encodings of each axis on the framework's own carriers; (iv) a simultaneous-closure theorem producing all six Clay-Standard contracts on the canonical encodings. Machine-verified in Lean 4 with kernel-only axioms [propext, Classical.choice, Quot.sound]. Independent expert review and substantial revision explicitly invited.

- Tags / keywords: `formal verification`, `Lean 4`, `Clay Millennium Problems`, `Riemann Hypothesis`, `P vs NP`, `Navier-Stokes`, `Yang-Mills`, `BSD`, `Hodge conjecture`, `proof assistants`, `mathematical logic`
- Cross-link: phase papers 1–4 are companions.

**Paper 2 — Phase 1 RH paper second** (entry vector for the analytic number theory audience)

- File: `Papers/clay_RH_via_substrate_v2.pdf`
- Title to use: *Phase 1: A Substrate-Level Reformulation of the Riemann Hypothesis via Principia Fractalis*
- One-paragraph abstract:

  > Phase 1 of a four-paper sequence. Substrate-level reformulation of the Riemann Hypothesis axis on the framework's T3-symmetric transfer operator. Not a Clay-prize claim for RH. The substrate-level RH content remains conditional on the published Hilbert-Polya program and on Mayer 1991's symmetric-quotient spectral correspondence, both preserved as named typed residuals. The alpha-skeleton constraint alpha_RH = 3/2 is pinned by two framework-internal arithmetic identities under the editorial convention alpha_Poincaré = 1 motivated by Perelman 2003. Machine-verified in Lean 4. Kernel-only axioms.

- Tags: `Riemann Hypothesis`, `Hilbert-Polya program`, `transfer operator`, `Mayer 1991`, `Lean 4 formalization`, `analytic number theory`
- Cross-link: master paper + Phase 2.

**Paper 3 — Phase 4 keystone third** (the consciousness / ZPE / cosmology reach — the "what is this FOR" paper)

- File: `Papers/principia_fractalis_keystone_v1.pdf`
- Title to use: *Phase 4 Keystone: Substrate-Level Consciousness Operator, Weinstein-GU Bundle, and Cosmological Brackets via Principia Fractalis*
- One-paragraph abstract:

  > Phase 4 keystone of a four-paper sequence. The framework's substrate is used beyond the Clay axes for a substrate-level consciousness operator C with Chern-character threshold ch_2 = 19/20 on a finite-dimensional 3x3 witness; a Weinstein–Geometric-Unity 11-field BRST cohomology bundle H^2 = 78 = 48+26+4; a Lambda_eff suppression bridge; and H_0 and Omega_Lambda brackets consistent with Planck 2018 and LDN 2025 within stated windows. None of these are Clay discharges. None are engineering blueprints. None are point-precision physics predictions. Machine-verified in Lean 4 with kernel-only axioms.

- Tags: `consciousness`, `quantum coherence`, `dark energy`, `Hubble constant`, `BRST cohomology`, `Geometric Unity`, `cosmology`, `Lean 4 formalization`
- Cross-link: master + Phases 1, 2, 3.

**Paper 4 — Phase 2 simultaneous closure fourth** (the technical mechanism)

- File: `Papers/clay_six_simultaneous_closure_v1.pdf`
- Title to use: *Phase 2: The Simultaneous-Closure Mechanism on Canonical Encodings of the Six Remaining Clay Millennium Problems*
- One-paragraph abstract:

  > Phase 2 of a four-paper sequence. Substrate-level simultaneous-closure mechanism: under the editorial convention alpha_Poincaré = 1 plus a single seven-field bundle (five typed residuals plus two True-markers), the six Clay-Standard contracts hold simultaneously on the framework's canonical encodings through one Lean theorem. Kernel-only axioms. Not a Clay-prize claim. The encodings differ from the literal mathlib carriers in named, disclosed ways (substrate-shadow vs literal Chow; finite-dim Fin 2 to R vs L^2; six-piece framework-Prop conjunction vs literal PDE; etc).

- Tags: `Clay Millennium Problems`, `formal verification`, `proof assistants`, `Lean 4`, `simultaneous closure`
- Cross-link: master + Phases 1, 3, 4.

**Paper 5 — Phase 3 P vs NP fifth** (technical axis detail)

- File: `Papers/clay_PvsNP_via_substrate_v2.pdf`
- Title to use: *Phase 3: A Substrate-Level Reformulation at the P vs NP Axis via Principia Fractalis*
- One-paragraph abstract:

  > Phase 3 of a four-paper sequence. Substrate-level reformulation at the P vs NP axis: chosen value alpha_PvsNP = 5/4 pinned by the eleven framework-internal arithmetic identities; an unconditional biconditional Clay_PvsNP_Standard at canonical encoding equivalent to ClassP not equal ClassNP; the open Clay conjecture itself is the named open residual. The framework's Machine type is not an operational Turing machine — its accepts and steps fields are free functions with no operational semantics. Not a constructive polynomial-time SAT algorithm. Not a literal mathlib-tier discharge.

- Tags: `P vs NP`, `complexity theory`, `Cook-Karp`, `Lean 4 formalization`, `proof assistants`
- Cross-link: master + Phases 1, 2, 4.

**Paper 6 — 852-page manuscript as foundational text**

- File: `Principia_Fractalis_master_folder/main.pdf`
- Title: *Principia Fractalis, Second Edition*
- Posting purpose: foundational text. Link from each paper's bibliography. Do not lead with this.
- For each paper above's posting page, add a line: *Foundational manuscript: Principia Fractalis, Second Edition (852 pp.), available from the GitHub repository.*

#### 2.2 Across all Tier 1 postings — required honest-scope marker

Every posting page must include this short paragraph (copy-paste this verbatim):

> **Honest scope.** This is a substrate-level reformulation. It is not a Clay-prize claim. The six remaining Clay axes are not discharged at the literal mathlib tier required by the Clay rules. The contribution is structural — that the six axes admit substrate-level joint treatment via one mechanism, machine-verified in Lean 4 with kernel-only axioms. Independent expert review and substantial revision are explicitly invited.

This protects you from the predictable "this isn't a Clay proof" criticism. You said it first.

---

### Tier 2: arXiv via Lean prover community endorsement

You cannot post to arXiv directly. You need an endorser. The path is through the Lean prover community.

#### 2.3 The specific posting steps

1. **Join Lean Zulip chat** at `https://leanprover.zulipchat.com`. Free account. Sign up with your gmail.

2. **Post in `#new members`** — introduce yourself plus the framework. Use the draft message in `ARXIV_ENDORSEMENT_OUTREACH.md`. Keep it short. Lead with honest scope.

3. **Post in `#Machine Learning for Theorem Proving`** OR **`#general`** — describe the Lean 4 work: 8226 jobs clean, kernel-only axioms, simultaneous-closure mechanism, Lean4Lean re-verification harness. Link the GitHub. Use the second draft message in the outreach doc.

4. **Ask for endorsement on arXiv** — specifically for **math.LO** (mathematical logic) or **cs.LO** (logic in computer science). The master paper (`clay_substrate_reformulation_v1.pdf`) is what to submit. Do not ask for a math.NT or math.AG endorsement — those classifications would invite Clay-prize scrutiny on a paper that does not claim that.

5. **Be specific about what the work is**: machine-verified substrate-level reformulation, NOT a Clay-prize claim. Carry the same honest-scope marker into the Zulip thread.

#### 2.4 What to do if the Zulip community pushes back

- If someone says "this isn't a Clay proof": agree with them. Say so first. That is exactly what the papers say.
- If someone says "the encoding isn't canonical Turing/Cook-Karp": agree. The Phase 3 paper foregrounds this on page 1.
- If someone says "the 143-problem coherence is a definitional restatement": agree. The master paper retracts the `p < 10^{-43}` figure as established evidence (Section 7.1).
- If someone offers to read the Lean tree: thank them, give them the GitHub link, and ask what kernel-axiom posture they would like to see additionally checked.

The community is generally welcoming to honest, well-formalized work. Honest scope is your protection.

---

### Tier 3: Direct outreach

Specific people to email. Draft text for each is in `ARXIV_ENDORSEMENT_OUTREACH.md`. Suggested first contacts in priority order:

#### 2.5 The four targets

1. **Kevin Buzzard** (Imperial College London) — formalization community leader, runs the Lean Forward / Xena project, has championed Lean in mathematics. Most likely to engage.

2. **Patrick Massot** (Université Paris-Saclay) — Lean formalization infrastructure, sphere eversion project, mathlib core contributor.

3. **Heather Macbeth** (Fordham University) — accessible Lean formalization style, has published on Lean methodology.

4. **Terence Tao** (UCLA) — high volume, but he has engaged with careful Lean-formalized work (Equational Theories Project, PFR formalization). More cautious approach needed.

#### 2.6 What to ask for

Either of:
- Endorsement on arXiv math.LO or cs.LO for the master paper.
- Feedback on the formalization approach.

Either is a win. Do not ask for both at the same time in the first email.

---

## 3. Honest scope summary

State this plainly in every interaction:

**The framework IS:**
- A substrate-level reformulation of the six remaining Clay axes via 11 framework-internal arithmetic identities and a simultaneous-closure mechanism on canonical encodings.
- Machine-verified in Lean 4 with kernel-only axioms `[propext, Classical.choice, Quot.sound]`.
- A pre-registration of 7 of 9 alpha-values for IBM Quantum hardware measurement (2 currently observed-consistent; 7 pre-registered).

**The framework IS NOT:**
- A Clay-prize claim.
- A discharge of any of the six remaining Clay axes at the literal mathlib tier required by the Clay rules.
- A constructive polynomial-time SAT algorithm.
- A point-prediction physics framework.
- An engineering blueprint for ZPE devices.

The work is substrate-level. Present it honestly. Independent expert review and substantial revision are invited.

---

## 4. What to do if challenged

Common challenges and the correct response. Use these verbatim if needed.

### 4.1 "This isn't a Clay discharge"

> Correct. The paper says so explicitly, on page 1, in the opening framed box. The work is a substrate-level reformulation, not a Clay discharge. The contribution is structural — that the six axes admit substrate-level joint treatment via one mechanism. Independent expert review and substantial revision are invited.

### 4.2 "The empirical anchors are weak"

> Acknowledged. The 143-problem coherence is currently a modeling assumption, not derived from independently collected per-problem measurements. The master paper retracts the `p < 10^{-43}` figure as established evidence (Section 7.1). The IBM 9-way is 2 measured-consistent plus 7 pre-registered. The pre-registration framing is scientifically credible if treated honestly.

### 4.3 "The Lean encoding isn't canonical Turing / Cook-Karp"

> Correct. The framework's `Machine` type is not an operational Turing machine. Its `accepts` and `steps` fields are free functions. The classes `ClassP` and `ClassNP` built atop this structure are substrate-shadows. The Phase 3 paper foregrounds this on page 1. The contribution is the biconditional plus the alpha-skeleton pinning, not a Cook-Karp-tier proof.

### 4.4 "Most of the 23-problem reach record is `: True` markers"

> Acknowledged. The master paper, Section 6, states this openly: 15 of 17 fields in the reach record are typed as `: True`. The substantive per-axis content lives in the separate framework-attack modules cited by name in the record file header. The record itself is a citation index, not a discharge.

### 4.5 "Why should anyone take this seriously"

> Three reasons. First, kernel-only axioms `[propext, Classical.choice, Quot.sound]` and zero project axioms across 8226 Lean jobs. Second, honest scope is preserved throughout — every claim is sourced to a specific Lean file's own `HONEST SCOPE` section. Third, the simultaneous-closure mechanism on canonical encodings is a structurally novel object whether or not the named residuals close at the literal mathlib tier. Evaluate the mechanism, not the headline.

---

## 5. What success looks like

- **Week 1**: All five papers and the manuscript posted to ResearchGate, Academia.edu, Google Scholar. Lean Zulip introduction posted.
- **Week 2–4**: Follow-up engagement on Zulip. First direct outreach email sent (Kevin Buzzard).
- **Month 2–3**: arXiv endorsement secured or refused; if secured, master paper submitted to arXiv math.LO or cs.LO.
- **Month 3+**: Independent expert engagement; revisions per honest review.

This is for humanity. Honest scope is the protection. The work stands or falls on whether the mechanism is structurally illuminating — not on whether the Clay rules are satisfied.

---

## 6. If anything goes sideways

Re-read this document. Then re-read the honest-scope marker. Then re-read what the framework IS and IS NOT.

If you cannot tell whether a claim is honest, ask Claude. Do not improvise an answer that drifts toward overclaiming.

You have done the work. The papers are honest. The Lean kernel reports zero project axioms. The rest is communication.

— end —
