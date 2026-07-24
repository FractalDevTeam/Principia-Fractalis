# Book rigor-ledger spec (2026-07-23)

Goal: give every chapter of the book the same honest treatment ch04 received —
a clear **Verification status** ledger that labels each major claim by its real
epistemic status. **Additive only. Delete nothing.** The book's prose and vision
stay; we add truthful labels so a hostile expert cannot dismiss it on sight.

## Ground truth — what is actually machine-verified (kernel, zero project axioms)

The ONLY chapter-level scientific content that is machine-verified is the
**operator-algebra substrate** (arc r102–r113, HEAD `91cc1a01`):

- `T∞` (= the base-3 UHF C\*-algebra `M_{3^∞}`) is constructed with a canonical
  tracial state that is **faithful** (`UHF_trace_faithful`), the algebra is
  **C\*-simple** (`substrate_completion_simple_unconditional`), and the trace is
  **unique** (`substrate_UHF_trace_unique`) — together: **T∞ is the Glimm 3^∞ UHF
  factor** (`r113_substrate_UHF_factor_capstone`). This underpins ch04.
- Some formalized operator content (T₃^sym self-adjointness, spectral-measure
  toys) exists for ch16–18, partial.
- The cross-Millennium **algebraic identities** among the framework's constants
  (α_P²=α_YM, etc.) are TRUE **as arithmetic about values the framework defines**
  (`α_P := √2`, `α_NP := φ+¼`, …). They say nothing about the Millennium problems.

Everything else in the book is NOT machine-verified.

## The four labels (use these exact tags)

1. **PROVEN (kernel-verified)** — machine-checked in Lean 4, zero project axioms.
   Only the substrate operator-algebra results above qualify.
2. **CONDITIONAL REDUCTION** — a machine-checked implication "IF [named open
   proposition] THEN [claim]", where the antecedent is unproven/open. The six
   Millennium chapters are here. NOT a proof of the claim.
3. **ASSERTED (not derived)** — a value or relation stated/chosen, not derived
   from first principles (e.g. `α_NP = φ+¼`, per codex/DERIVATION_ANALYSIS_alpha_NP.md).
4. **EMPIRICAL HYPOTHESIS — UNTESTED / NOT INDEPENDENTLY VALIDATED** — a physical,
   cosmological, clinical, or consciousness claim that only experiment can settle;
   a proof assistant cannot establish it. Includes the 97.3% clinical figure,
   cosmological brackets, IIT/consciousness claims, dark-energy/Hubble claims.

## Template (imitate ch04 exactly)

At the end of each chapter's main results (Level-3/research section if present,
else after the chapter's central theorem/claim), insert a block:

```
\paragraph{Verification status (2026-07-23).}
To hold this chapter to the standard of the machine-checked corpus, here is the
honest status of its principal claims:
\begin{itemize}
\item \textbf{[label]} — <one-line statement of the claim>. <why it has this
  status; cite the Lean name if PROVEN, the open Prop if CONDITIONAL, the
  DERIVATION_ANALYSIS/assumption if ASSERTED, or "awaits experiment" if EMPIRICAL>.
\end{itemize}
```

Where a specific line asserts something as established that is not (e.g. "we prove
X" for a conditional or empirical X), add a one-sentence inline honest-scope note
next to it — do NOT delete the original sentence. Match ch04's wording style
(see the "Machine-verification status of Theorem~\ref{thm:existence-uniqueness}"
paragraph and the "Verification note" on the Nuclear-Structure lemma).

## Hard rules
- Additive + light inline flags only. No deletions, no rewrites of the vision.
- Every chapter's central claim(s) must get at least one labeled bullet.
- Be strict: if closing a claim would resolve a Millennium problem, it is
  CONDITIONAL or (if merely asserted) note it plainly — never PROVEN.
- Keep LaTeX valid; do not touch any file outside your assigned chapters.
- Preserve existing labels/refs; if you reference a chapter/theorem, use an
  existing `\ref`/`\label` or plain text.
