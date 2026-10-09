# scientific_work provenance — what `pablo_context/scientific_work/` actually is

Date: 2026-10-08. Author: Pablo Cohen + Claude Opus. READ-ONLY pass, nothing in
that directory modified. Recorded so this directory is never re-investigated from
scratch (rule 1).

`/Storage 2TB/home/xluxx/pablo_context/scientific_work/` is **original / ancestor
material that predates the book**, not a copy of the live corpus. Of 94 unique
`.py` (109 with version-dups), only `143 Problems Solved On IBM.py` also exists in
the live tree, and only in `ARCHIVE/2026-06-08-cleanup/`.

## Breakdown
- **~85 engineering scripts, NOT the math corpus:** fractal encryption/compression,
  blockchain mesh (`frac_net`, `elastic_node`, `fracnet`), multi-agent Ollama
  orchestration (`deepagent*`, `sci3/4/5`, `uiai-1..7`, `scientific_multiagent*`),
  password crackers, `FractalBrainOS`, GUIs. Many are byte-identical version dups
  (`sci3.py`=`sci4.py`=111578 B; `uiai-4/5/6`≈144 KB). Not relevant to PF's
  mathematical claims.
- **`latex_documents/` (24 .tex):** the **ancestor per-problem manuscripts** that
  became the book chapters — "The Ocean of Timeless Existence",
  "Consciousness-Modified/Extended General Relativity", "Mathematical Rescue of
  Weinstein's Geometric Unity", "energy_destruction_proof", one per Clay problem.
  Drafts; the book is the deliverable, so these are history, not a second source.
- **`Proofs/` figures + JSON:** the **source data behind appH** (appendix numerical
  validation) and the appA/ch20 Riemann material.
- **`python_code/143 Problems Solved On IBM.py` + `160 problems.py`:** the
  provenance for ch21's "143 problems / 100% coherence" and ch34/appI's "IBM
  empirical validation".

## FINDING 1 — the IBM "143 problems" result, from source

The source demonstrates, mechanically, what ch21's own ledger (L1468) already
calls CIRCULAR — and sharpens it:

1. **Local simulator, not IBM hardware.** Backend is `AerSimulator(method='automatic')`
   (L504, L564). The real-hardware path (`QiskitRuntimeService(channel='ibm_quantum',
   token=api_token)`, L483) needs a token and **falls back to the simulator** (L563:
   "Falling back to simulator"). "Solved On IBM" is a local Aer simulation.
2. **142 problems, not 143** (`grep '"id":'` = 142).
3. **"Coherence" is a classical deterministic formula, not a quantum measurement.**
   The score is `np.mean(|fractal_resonance_function|²)`, and
   `fractal_resonance_function` is a classical `Σ (cos+i·sin)(π·α·digitalSum·(1+freq/50))/nˣ`.
   The AerSimulator result does not enter the coherence score.
4. **"100%" is a string-match clamp on already-solved problems.** Verbatim L211-214:
   ```
   base_coherence = 0.5 + 0.5 * xi
   if "solved" in known_result.lower():
       return min(1.0, base_coherence + 0.5)
   return base_coherence
   ```
   The only entry whose `known_result` contains "solved" is Poincaré
   ("Solved by Perelman"), which then gets +0.5 and clamps to 1.0. The high scores
   are assigned by string match to problems already known solved.
5. **Dimensions are NOT the book's α-skeleton.** P-vs-NP `fractal_dimension = 1.618`
   (φ, vs book α_P=√2, α_NP=φ+¼); NS `1.667` (5/3, the superseded value, vs
   α_NS=3π/2); YM `2.15` (vs 2); Hodge `2.1` (vs φ). Sourced to "Smale (1998)".

So ch21 L1112's "P(all 143 by chance) < 10⁻⁴³ assuming a 95% baseline" has no basis:
there are no 143 independent Bernoulli trials — it is one classical formula clamped
to its ceiling. (Independently, 0.95¹⁴³ = 6.5×10⁻⁴, not <10⁻⁴³, per the reading pass.)

## FINDING 2 — the Riemann "150-digit verification", from source

`Proofs/high_precision_verification_results.json`: `precision_digits: 150` is the
**arithmetic precision**, not the correspondence accuracy. The "verified
correspondences" map eigenvalues to ζ-zeros at **distance 0.09–0.68** with
**|ζ| up to 1.24** — i.e. not at zeros. First entry: `s_predicted` imaginary part
**14.2267** vs `exact_zero` **14.1347** — the exact 0.092 gap appA/appH flagged.
`Proofs/complete_riemann_analysis_results.json`: the `high_precision_verification`
correspondences array is **empty**, and theoretical/empirical scaling `ratio =
31136` (and `1272` in `complete_riemann_proof_results.json`) — the systematic
scaling factor ch20 L349's `\manuscriptcorrection` already names.

## FINDING 3 — Hodge JSON carries the stale "sacred points"

`Proofs/hodge_conjecture_complete_proof.json`: `sacred_points = [1, 1.618, 2, 2.718,
3.14159]` = [1, φ, 2, e, π] — the stale set (appG L119 / lexicon), not the
α-skeleton (√(2π), 3π/2, 3π/4, φ+¼).

## VERDICT
These source artifacts **confirm the reading-pass findings at the data level, in
Pablo's own files.** The active-tree ledgers already carry the corrections
(ch20 L349 manuscriptcorrection; ch21 L1468 "CIRCULAR — IBM empirical validation";
appH). So this is provenance confirmation, not new defects — with one sharper
statement now available from source: the IBM "100% coherence" is a string-match
clamp on already-solved problems, which is stronger and more specific than
"circular". The figures appH displays are real and were generated here; the JSONs
behind them show the overstatement in the data itself.

## BOOK-SIDE ACTION (behind the current manuscript freeze; not done here)
Every place that cites "143 problems / IBM / 100% coherence" as positive evidence
— ch21 §statistical-significance, ch34/appI "IBM empirical validation" — should be
scoped to: a local-simulator run of a classical resonance formula whose headline
figure is a clamp. The book's own ledgers already point this way; propagate it to
the restatements (same pattern as the rest of the parity work).
