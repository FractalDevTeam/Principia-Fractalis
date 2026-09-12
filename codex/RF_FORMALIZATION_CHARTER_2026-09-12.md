# R_f INFRASTRUCTURE SURVEY AND CORRECTED CAMPAIGN — 2026-09-12

## §0. CORRECTION NOTICE

The initial draft of this file (committed and immediately superseded) proposed a fresh R_f formalization campaign — module `PF/FractalResonance.lean` to be created from scratch, statement cards R_f.1 through R_f.5. **That draft was uninformed and is retracted.**

The `R_f(α, s)` function per manuscript ch03 Def 3.3 **is already formalized** in the tree and imported into `PF.lean`. This charter was drafted before performing the survey the collaboration contract mandates before "any evaluative statement about the framework."

The corrected charter below reports the actual state of the R_f infrastructure and redirects to genuinely open research targets.

## §1. WHAT IS ALREADY IN THE TREE

**Primary file: `PF/Consciousness/FractalResonance.lean` (385 lines)** — namespace `PrincipiaTractalis.Consciousness`.

Landed (axiom-free, `[propext, Classical.choice, Quot.sound]` on inspection):

| item | Lean identifier | book reference |
|---|---|---|
| Phase factor definition | `phaseFactor α n := Complex.exp (I·π·α·D_3(n))` | ch03 eq (3.4) |
| Summand | `fractalResonanceTerm_complex α s n` | ch03 eq (3.2) |
| **R_f itself** | `fractalResonance α s := ∑' n, if n = 0 then 0 else …` | **ch03 Def 3.3** |
| Unit modulus of phase | `norm_phaseFactor` | ch03 Thm 3.1 Step 1 |
| Summand norm bound | `norm_fractalResonanceTerm_complex` | ch03 Thm 3.1 Step 3 |
| **Absolute convergence for Re(s) > 1** | `fractalResonance_summable_of_re_gt_one` | **ch03 Thm 3.1 first half** |
| Convergence witness | `fractalResonance_convergent_of_re_gt_one` | (same) |
| **α = 0 gives ζ** | `fractalResonance_alpha_zero` | **ch03 Prop 3.4 / eq (3.9)** |
| Digit-sum evaluations | `digitalSum3_one`, `_two`, `_three`, `_four` | ch03 worked example lines 65-73 |
| `phaseFactor 1 1 = -1` | `phaseFactor_one_at_one` | ch03 eq (3.5) worked example |
| Bridge to real-β form | `fractalResonance_eq_real` | connects to `MillenniumSixReductions.fractalResonanceSeries` |
| PFClass bridge | `fractalResonance_at_class`, `..._values`, `..._summable` | connects R_f to the six-class α enum |
| P/NP spectral gap via R_f | `complexity_spectral_gap_via_resonance_holds` **THEOREM** | ch03 Thm 3.3 — actually proven, not open, via `PF/SpectralGap.lean` |
| Chapter headline | `chapter_three_headline` | conjunction of the above three main facts |

**Additional infrastructure elsewhere:**

- `PF/MillenniumSixReductions.lean` — earlier real-β version `fractalResonanceSeries α β`
- `PF/Consciousness/RfAtAlphaOneIsNegEta.lean` — specific evaluation `R_f(1, 1) = -log 2` (via η)
- `PF/Analytic/RfNumericalRefutation.lean` — numerical refutations at α = √2, s = 1
- `PF/Analytic/BCleanPhaseIdentity.lean` — `R_f_principal` (principal branch identity)
- `PF/EulerFactorThree_r214.lean` — Euler-factor at 3: `(1 − 3^{−s}) · R_f(α, s) = Σ_{3∤n} …` — a genuine repair result (r214, 2026-08-07)

**Import status:** `PF/Consciousness/FractalResonance.lean` is imported in `PF.lean` (verified 2026-09-12). Its declarations are part of the top-level PF build closure.

## §2. WHAT IS GENUINELY OPEN IN THE R_f ARC (per the file itself and the book)

The file `PF/Consciousness/FractalResonance.lean` §8 explicitly encodes the manuscript's `🔴 research` content as `Prop`s (not axioms, not theorems), following the corpus discipline:

| open Prop (in Lean) | book claim | book verdict |
|---|---|---|
| `rh_resonance_at_three_halves` | R_f(3/2, s) zeros on `Re s = 1/2` ↔ ζ zeros on `Re s = 1/2` | manuscript: "Proof deferred to Chapter 7" |
| `universal_pi_over_ten_factor` | limit of R_f(α, s_c)/(α − α_c) equals (π/10) · ξ(α_c, s_c) | manuscript: `\begin{observation}` (empirical) |
| `resonanceCoefficient_xi` | opaque function `ℝ → ℂ → ℝ` | placeholder; derivation is open content |

**Not yet stated in Lean, not yet in any file:**

- **Analytic continuation** to `ℂ ∖ {1}` (ch03 Thm 3.1 SECOND HALF). Book asserts "by methods analogous to ζ (contour integration, functional equation approach)" but the book itself gives no explicit proof. This is a *genuine research question*: does R_f satisfy a Riemann-zeta-style functional equation?
- **Meromorphy at s = 1** (ch03 Prop 3.4 (2)-(3)). The book claims pole "absent or shifted" for `α ≠ 0`. Not stated as a Lean object.
- **Growth estimates in the critical strip** (ch03 Lemma "Vertical Strip Behavior"). Not in Lean.
- **The Universal π/10 Factor** (ch03 §"The Universal π/10 Factor"). Empirical per the book; stated as Prop; unproved.

## §3. WHAT THIS INFORMATION IMPLIES ABOUT THE ROADMAP

Redirected priority order for the R_f arc (Direction A refined):

**Priority 1 — the α = 0 base case is DONE. But is it CONNECTED to mathlib's `riemannZeta`?**

The file's `fractalResonance_alpha_zero` proves `R_f(0, s) = ∑' n, if n = 0 then 0 else 1/n^s` — the *Dirichlet series* form. Mathlib's `Complex.riemannZeta` is the *analytically-continued* function whose Dirichlet-series form holds only for `Re s > 1`.

A one-lemma bridge is straightforward to add:

```lean
theorem fractalResonance_alpha_zero_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    fractalResonance 0 s = Complex.riemannZeta s
```

using mathlib's `zeta_eq_tsum_one_div_nat_add_one_cpow` or equivalent Dirichlet-form identity. This is the *actually-missing* atomic-level R_f→ζ bridge lemma. **Estimated ~20 lines.**

**Priority 2 — meromorphy and vertical-strip behavior (ch03 §Domain of Definition, §Growth Estimates).**

Book Prop 3.4 (2)-(3) and the "Vertical Strip Behavior" lemma. Neither is stated in Lean. Both are ζ-adjacent: mathlib has `riemannZeta` meromorphy machinery; the R_f version reduces to `Complex.riemannZeta` + phase-factor absorption.

**Estimated scope:** meromorphy statement + proof by transfer through the α=0 identity ≈ 100 lines. The strip growth estimate is harder; defer to a follow-on unless mathlib already has a suitable general Dirichlet-series growth lemma.

**Priority 3 — analytic continuation to `ℂ ∖ {1}` (ch03 Thm 3.1 second half).**

Book asserts but does not prove. Cases:
- For `α = 0`, R_f = ζ and mathlib's `Complex.riemannZeta` supplies continuation — one-line theorem.
- For general `α ≠ 0`, no functional equation is known (or at least not derived in the book). Whether R_f admits continuation is a genuine research question.

**Position:** the "α = 0" special case can be formalized cheaply (using ζ). The general-α case is a research target requiring first-principles work not present in the book.

**Priority 4 — Euler-factor extensions (r214 was the first repair).**

`PF/EulerFactorThree_r214.lean` proved `(1 − 3^{−s}) · R_f(α, s) = Σ_{3∤n} e^{iπα D_3(n)}/n^s`. The book's Euler-product decomposition (referenced in ch09 for spectral unity) may admit further factorizations by primes ≠ 3. Book/repo research question.

**Priority 5 — the π/10 factor (ch03 §The Universal π/10 Factor).**

Book labels this an empirical observation. To move from Prop to theorem would require either (a) a first-principles derivation from R_f's phase structure, or (b) a formalization of the empirical evidence base. Not clearly reducible to standard mathlib apparatus.

## §4. WHAT REPLACES THE ORIGINAL CHARTER

Replaced by two campaigns of much smaller scope, plus a corrections/audit action:

### Campaign R_f-Bridge — Priority 1

**Target:** land the `fractalResonance_alpha_zero_eq_riemannZeta` bridge lemma (bridging Dirichlet-series form to mathlib's analytically-continued `riemannZeta`).

**Ceiling:** 1 day. **Scope:** ~20 lines. **Deliverable:** the bridge as a lemma in `PF/Consciousness/FractalResonance.lean`, immediately followed by an axiom audit.

### Campaign R_f-Meromorphy — Priority 2

**Target:** land the `Complex.MeromorphicOn`-formatted statement of R_f meromorphy on `ℂ` with singularity at most at `s = 1`.

**Ceiling:** 1 week. **Scope:** ~100 lines. **Deliverable:** meromorphy witness for R_f at α = 0 (via ζ transfer). General-α meromorphy is deferred to follow-on.

### Action R_f-Audit — infrastructure hygiene

**Target:** run `#print axioms` on every landed R_f theorem in `PF/Consciousness/FractalResonance.lean`, verify all read `[propext, Classical.choice, Quot.sound]`, and add an in-file audit block per the `build-tree-discipline` memory rule ("a stone lands with its `#print axioms` block and its `PF.lean` import line").

**Ceiling:** 1 day. **Scope:** ~15 lines of audit directives at file end.

## §5. THE LESSON

The collaboration contract states: *"Never judge from samples. Before any evaluative statement about the framework: read (or dispatch agents to read) the relevant book chapters, papers, and codex records."*

Yesterday's substrate-rigidity work took the book at chapter level (ch04 = T_∞); today's initial R_f charter did not extend the courtesy to ch03. Correcting that now, and adopting a standing rule:

**Every new Lean campaign starts with a `SURVEY` file that grep-inventories the existing tree for adjacent identifiers before proposing new modules.** Charter files may only be committed *after* the survey confirms non-duplication.

This is the operational form of Pablo's directive: *"see the big picture. book guides Lean. Lean should be all-encompassing explanation of the book. Fractal."*

The fractal is already partially there. Formalization work should extend and connect existing pieces, not recapitulate them.

---

## §6. IMMEDIATE ACTIONS (this session)

1. This corrected charter committed. **DONE** — commit `1c09ea4d`.
2. Execute Campaign R_f-Bridge (the ~20-line ζ bridge lemma). **DONE** — commit `b4693127`. Landed `fractalResonance_alpha_zero_eq_riemannZeta` at `PF/Consciousness/FractalResonance.lean:205-219`.
3. Execute Action R_f-Audit (the axiom-block sweep). **DONE** — commit `c4a3b819`. Landed §10 audit block covering ten declarations (later extended to twelve at commit `36b75b1b`); all audit to `[propext, Classical.choice, Quot.sound]`.
4. Look at what's next per the true fractal expansion. **PARTIAL** — Priority 2 (α = 0 sub-case) discharged same session at commit `36b75b1b`, adding two theorems:
   * `exists_analytic_continuation_fractalResonance_alpha_zero` (`FractalResonance.lean:230-255`): analytic continuation on `ℂ ∖ {1}` witnessed by `riemannZeta`.
   * `fractalResonance_alpha_zero_residue_one` (`FractalResonance.lean:257-278`): simple-pole residue 1 at `s = 1`.
   Priority 2 general-α case and Priorities 3-5 are all genuine open research (no known functional equation, empirical π/10 factor). Ch05-ch09 survey done at `codex/CH09_SPECTRAL_UNITY_SURVEY_2026-09-12.md`; the tree's 2026-05-14 Stage 41 cleanup that stripped H_P/H_NP operators is the established honest scope, not an oversight — restoring them requires original research per `PF/TuringEncoding/Operators.lean` own commentary. `appI_lean_cross_reference.tex` updated at commit `2ad1d880` to cite T_infinity_rigidity + all three new R_f declarations.

## §7. CHARTER CLOSURE (2026-09-12)

**Priority 1 CLOSED.** R_f-Bridge landed, R_f-Audit landed.

**Priority 2 CLOSED (α = 0 sub-case only).** Meromorphic-extension-via-ζ and simple-pole residue proven for α = 0. Original ~100-line estimate collapsed to ~50 lines including documentation because the R_f-Bridge (Priority 1) reduces the meromorphy claim at α = 0 to a direct transfer through `differentiableAt_riemannZeta` + `riemannZeta_residue_one`. **General-α meromorphy remains genuine open research** and is intentionally NOT stated as a Lean object.

**Priority 3 (analytic continuation for general α) — OPEN RESEARCH.** Manuscript asserts but does not prove. No known functional equation for `R_f(α, ·)` at α ≠ 0. Not a formalization task.

**Priority 4 (Euler-factor extensions) — DEFERRED.** `PF/EulerFactorThree_r214.lean` remains the sole such factorization; extensions to primes ≠ 3 are not book-guided.

**Priority 5 (π/10 factor) — EMPIRICAL PER BOOK.** Encoded as Prop `universal_pi_over_ten_factor` in `FractalResonance.lean` §8. Book calls it `\begin{observation}`, not a theorem.

**Standing rule (from §5) IN EFFECT.** Any future R_f-adjacent Lean campaign must begin with a survey. Any survey-agent recommendation must be verified against the book source before charter drafting — the ch09 H_α unification rejection (recorded in `codex/CH09_SPECTRAL_UNITY_SURVEY_2026-09-12.md`) is the enforcement precedent.

*Charter opened 2026-09-12, corrected 2026-09-12 same session, closed 2026-09-12 same session. Five commits landed on `r331b-provenance`: `1c09ea4d`, `b4693127`, `c4a3b819`, `36b75b1b`, `2ad1d880`, `755c0493`. Book-guides-Lean discipline enforced end-to-end: survey before propose, book-verify before charter, honest scope over speculative extension.*
