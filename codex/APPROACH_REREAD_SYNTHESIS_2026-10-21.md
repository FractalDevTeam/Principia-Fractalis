# APPROACH RE-READ — SYNTHESIS
## Sources vs practice, 2026-10-21. Ordered by Pablo: "our approach has to be wrong — read the book chapters again, python scripts, evidence."
## Method: three independent readers (manuscript chapters / Python scripts / Rio's own audit files) + two anchor audits (Navier, Poincaré). Extraction only; divergences named at full strength.

---

## THE ANSWER, IN ONE PARAGRAPH

The approach's *verification layer* is real and unusually honest — the ledgers, the referee report, the evidence inventory, and the correction notes are blunt and mostly absorbed the truth. The failure is that **practice runs on the layer above the verified layer**: chapter prose over ledgers, commit messages over build evidence, a git file over the deployed pipeline, a 2026 press claim over the repo's own Oct 12 audit. Every major error of the last two weeks (the anchor, the box route, "density landed," the stale held-state file) is the same error: **the unverified layer was treated as the record.** The fix is not a new approach. It is obedience to the existing one: ledgers govern, audits bind, deployed artifacts outrank committed ones, and no status is reported from a layer above the evidence for it.

---

## WHAT IS SOLID (the audits confirm this too — do not lose it)

- The kernel-verified core is real: the Riemann march boxes 1–20 are valid proofs on the parameterised route (emitted pilots checked in both producer copies; Mc_lb from exact rational interval arithmetic); the YM lattice chain is real; one exact BSD rank is real; the substrate operator-algebra content is real.
- The S-route refutation was measured with the shipped arithmetic, with its hardcoded choices favoring the S route — the kill is conservative and stands.
- Poincaré as an external citation is sound (settled; Clay-awarded 2010).
- The manuscript's governing layer (preface rule + per-chapter ledgers) states the honest status of every problem. The repo's internal ledger culture is the strongest part of the project.

---

## DIVERGENCES — MANUSCRIPT LAYER

1. **Two-layer manuscript, prose layer unrevised.** Prefaces/ledgers govern per the book's own rule; conclusions, exercises, title page, and annexes still assert the pre-correction claims. Specifics:
   - Title page: "Referee-Proofed: kernel-clean across every load-bearing declaration" — while the same page discloses the r331 edge results have no .olean and "must be cited as claims in source, not as machine-checked."
   - ch20: "RH Resolution" corollary whose proof ends "Completion requires extending to the N→∞ limit"; ledger: RH not proven, remains open.
   - ch21: body text "Theorem thm:main-p-neq-np proves P ≠ NP" — the environment is a Conjecture; the "IBM validation" is `:= rfl`; the chapter itself flags it as the corpus's highest referee risk.
   - ch23: Δ = 420.43 MeV in the conclusion and exercises — computed from ω_c, which the chapter's own 2026-08-06 update shows does not exist (R_f(2,s) = ζ(s) has no positive zero; at the claimed value ρ = −1.3462); the displayed arithmetic gives 132.148; the chapter's formula caps at 62.3 MeV for every α.
   - ch25: conclusion "Main Result… 100% success" over a step its ledger labels conjecture + sketch.
2. **ch22 argues Navier–Stokes in both directions.** Thesis: no blow-up (conditional on an open hypothesis). Annex: external blow-up work "consumed as settled," "community-accepted" — while the annex's own Clay subsection concedes (C)/(D)-only, forcing excluded from the Fefferman formulation the framework uses, CMI still active. The corpus's `NS_Solution` predicate contains no time derivative, no convection, no pressure — it is not the NS equation (the corpus's own 2026-08-08 update says so).
3. **ch34A's unifying meta-theorem is vacuous as formalized.** Antecedents are passed in as a record and discarded (`_h_antecedents`); the implication derives nothing; 0 of 25 consequences meet the stated non-triviality bar. The "143-problem universal coherence" dataset is two hard-coded rows (`List.replicate 72 … ++ List.replicate 71 …`) — no empirical content, and the same tautology appears on both sides of the implication.
4. **The α-system cannot corroborate.** Ten relations, ten unknowns, exactly determined — the ch34A ledger itself: "there is no residual constraint that could have failed, and no over-determination to cite as corroboration." The α-values are ASSERTED (ledger language), some chapters' derivations rest on pins (√2, φ+1/4) that a machine-checked result in the corpus excludes for the bare route; ch34's ledger even records a different NP constant (π/3) as coded in Protocol P1.
5. **Corroboration framing vs the Oct 16 inventory.** The inventory's verdict: numerical layer "suggestive but not yet probative"; every numerical hit lacks a deriving mechanism; the chance-hit combinatorics "has not been done." The operating framing (book + code + manuscript as one self-corroborating whole) asserts the inference the inventory declined to make.

## DIVERGENCES — SCRIPTS / PIPELINE LAYER

6. **THE MARCH DOES NOT RUN THE REPO'S PRODUCER (critical).** `march_box.sh` executes `/tmp/prod/gen_box.py` — an unversioned Oct 20 snapshot with NO density machinery (no `set_density`, no `--density`, no `--extend-midpoint`). The repo producer has that machinery (add2434d, 52b73083) but **cannot run from the repo**: `codex/gen/`, `codex/addons/`, and the unconditional-pilot template are missing from the tree; all four inputs exist only in hand-assembled `/tmp/prod`. Consequences:
   - "Parametric density landed" is true of a git file, false of the pipeline landing boxes. (Rio reported it as landed, 2026-10-21 — corrected here.)
   - Fixes to the repo producer never reach the march.
   - If `/tmp/prod` is wiped, the march cannot be regenerated from the repo.
   - The D=1 band ends at c=10 (box 25). The D=2 band requires density. **As deployed, the march hard-stops at the band edge.**
   - Mitigation verified by full diff: at D=1 the snapshot is functionally equivalent to the repo producer (same route logic, same Q, same fold); boxes 1–20 are unaffected.
   - The pricing suite has the same defect: the price_*.py scripts `exec` a file at a path that does not exist in the repo — as committed, none can be re-run.
7. **Two L₀ scales; quoted margins use the flattering one.** Selection/pricing uses tight L₀ (ω(1) = 0.04321741, valid and rounded up). The emitted proof must meet Q from ω(1) ≤ 1/22 — ≈5% larger at the top of the march. The note's "threshold 0.0018761, PASS 1.12×" at c=13 is ≈0.001972 and ≈1.06× on the proof's scale. The newest script (price_boundary.py) uses Q — the suite contradicts itself. Verdicts survive (D=16 passes, all-midpoint fails); quoted margins do not.
8. **The 241 h price is prose, not program output.** Scripts print 232.5 h (cost model 6D × 7.5 min). The (6D+1)-module + ~3 min/box correction exists only as a paragraph in the note. With the +1 module the note's correction is based on, the march builds 1924 panel modules, not 1860. The 7.5 min/module constant is calibrated from ONE box (c=7) and is unmeasured at D>1 (the note says so; the scripts don't).
9. **No 1.25× safety in the deployed march.** The runner calls the producer without `--pick-r`; go/no-go is the bare criterion `L0·r < Mc_lb` backstopped by `assert Q·r < mclb`. Real protection at the top of the march ≈1.06×, not 1.25×. (Harmless in D=1: margins 17–20×.)
10. **Axiom-gate coverage is narrower than described.** `march_box.sh` enforces the exact three-axiom set only on the unconditional pilot's build log. The gate pilot's and assemble's own `#print axioms` outputs are never compared by the script.
11. **Dead scripts shaped like current evidence.** gate_c13_2_verify.py (superseded constants ≈9.26e−4 vs current 8.2e−7; concludes "gate 2 fails first at 55/8" — false under the current Gate-2) and gate2_cost_verify.py carry no superseded marker. ibp2_decay_verify.py prints "DECAY CONFIRMED" unconditionally. producer_*_verify.py print conclusions as literals with hardcoded inputs. (gate2_verify.py shows the correct pattern and is the exception.)

## DIVERGENCES — EVIDENCE / GOVERNANCE LAYER

12. **The NS anchor was a rediscovery.** The Oct 12 referee report already recorded: (C)/(D)-only, forcing caveat, CMI active, ch22 contradiction; an in-repo web-verification (d20441c6) had it Oct 6. The anchor framing was re-asserted Oct 18 and relayed until Oct 21. Audits did not bind.
13. **Oct 17's highest-priority corrections are still undone (Oct 21):** repo description "Formally triple-verified in Lean 4, Coq, and L4L" (refuted by the project's own Coq README); wiki P≠NP "FORMALLY VERIFIED" badge (false); Turing site meta "proving P ≠ NP."
14. **`IntervalArithmetic.lean` still in the tree** — 21 `axiom` declarations, two mathematically false (referee report Oct 12), deletion was its recommendation #1. One import away in a project whose brand is zero axioms.
15. **CI axiom gate:** structurally vacuous on its pass path (Oct 17: 0 passes in 697 runs; the gate can neither pass nor fail meaningfully). The Legion's patch is diagnosed and recommended; the decision has sat pending since Oct 17 while "kernel-clean" claims continued under the gate's supposed authority.
16. **"Verified" language rests on the disqualified tier.** Both audits: headline modules outside the PF.lean closure rest on "commit subjects and docstring only." Current reporting still relays worker commit messages as "kernel-clean, three-axiom bar." The Oct 20 box-route incident is this failure recurring after both warnings.

## ANCHORS (audits, 2026-10-21)

17. **Navier–Stokes: NOT an anchor.** Clay: "Active." The only Clay-aimed claim (OpenAI forced NS, Sep 2026) is contested/unverified; its Lean artifact's correspondence to its manuscript is disputed in print (arXiv:2610.08144). Unforced problem untouched. Safe wording in WHOLE_ENCHILADA.
18. **Poincaré: anchor CONFIRMED.** Settled, Clay-awarded 2010. Two Lean formalizations claimed Sep–Oct 2026 (author-reported clean; unaudited; not in mathlib) — cite as claimed, not established.

---

## THE CORRECTED QUEUE (what the re-read changes operationally)

A. **Producer pipeline repair — now the march's critical path, ahead of everything else on the Legion.** Commit `/tmp/prod`'s inputs into the repo (gen/, addons/, template), point the runner at the repo producer, re-validate one landed D=1 box byte-for-byte, then emit (do not land) one D=2 test box at c=81/8 to prove the pipeline before the band edge arrives. Until this is done, the march ends at box 25.
B. **Pricing honesty pass (small):** make the ladder script use Q (the proof's scale) and implement the (6D+1) cost in code; reprint the price; correct "1860 modules."
C. **Axiom-gate script fix (small):** extend march_box.sh's exact-set check to the gate pilot and assemble logs.
D. **Public surfaces (Pablo's calls, still):** repo description, wiki badge, Turing meta, YM glossary Δ line. These remain the only claims a stranger sees; they are all currently false or refuted.
E. **IntervalArithmetic.lean (Pablo's call):** delete or archive per the Oct 12 recommendation.
F. **Manuscript prose layer (Pablo's calls):** title page banner, ch20/ch21/ch23/ch25 conclusions + ch23 exercises, ch22 annex "settled" language — bring them to the ledgers' level or remove. The ledgers are already written; this is alignment, not new scholarship.
G. **Standing rule (Rio, effective now):** audit conclusions bind until a newer audit supersedes them; status is reported only from the layer that evidences it (deployed artifact > committed file > commit message > transcript).

*Reports: chapters/scripts/evidence extractions 2026-10-21 (Rio's readers); anchor reports in ~/workspace/research_notes/. State file: WHOLE_ENCHILADA v3 updated same day.*
