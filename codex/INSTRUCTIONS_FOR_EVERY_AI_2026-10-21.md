# INSTRUCTIONS FOR EVERY AI — Principia Fractalis, 2026-10-21
## From Rio (ringleader), by Pablo's direct order. This document supersedes all prior prompt sets.
## Every asset reads §0 and §1 before any work. §0 is binding: audits govern until a newer audit supersedes them.

---

## §0 THE EVIDENCE (binding on all assets — know this before touching anything)

1. **None of the six in-scope Clay problems is proven in this repo, and the repo's own ledgers say so.** The manuscript is two-layered: chapter prose claims strongly; the dated Verification-status ledgers downgrade. The preface's own rule: THE LEDGERS GOVERN. Report status from ledgers, never from prose, conclusions, exercises, or the title page.
2. **Navier–Stokes is NOT a settled anchor** (audit, 2026-10-21, primary sources). Clay lists it "Active." The only Clay-aimed claim (OpenAI forced NS, Sep 2026) is contested and unverified; its Lean artifact's correspondence to its manuscript is disputed in print (arXiv:2610.08144). Every earlier claim in the chain addresses model equations or weak solutions, not the Clay statement. The unforced problem is open. Our own referee report recorded this on 2026-10-12; the "settled anchor" framing was an error and is retired. ch22's own thesis (conditional no-blow-up) stands as the lane's content.
3. **Poincaré IS a settled anchor** (audit, 2026-10-21). Perelman, verified by three expositions, Clay-awarded 2010. Two Lean formalizations were claimed Sep–Oct 2026 — cite as claimed, not established.
4. **ch34A's unifying meta-theorem is vacuous as formalized** (antecedents discarded as `_h_antecedents`; 0 of 25 consequences meet the non-triviality bar). The 143-problem coherence dataset is two hard-coded rows — no empirical content. The α-values are ASSERTED constants; the α-system is exactly determined (10 relations, 10 unknowns), so it contains no over-determination that could corroborate anything. Never cite it as corroboration.
5. **ch23's Δ = 420.43 MeV is refuted inside the chapter itself**: ω_c does not exist (R_f(2,s) = ζ(s)); the displayed arithmetic gives 132.148; the formula caps at 62.3 MeV. The conclusion and exercises still print 420.43 — they are wrong until revised.
6. **ch21's "Theorem proves P ≠ NP" is a Conjecture environment**; its IBM validation is `:= rfl`. ch20's "RH Resolution" is a conditional reduction whose proof ends at the N→∞ limit. ch25's "Main Result / 100% success" sits over a ledger that says conjecture + sketch.
7. **The march's deployed producer is `/tmp/prod/gen_box.py`, not the repo producer** (scripts audit, 2026-10-21). It has no density machinery. The repo producer has the machinery but cannot run from the tree (missing codex/gen/, codex/addons/, template). Boxes 1–20 are valid (D=1 equivalence diff-verified). The march hard-stops at c=10 until the pipeline is repaired (§2, Legion task 1).
8. **Quoted march numbers, corrected:** price is 232.5 h scripted (≈241 h with the hand correction); module count 1924, not 1860; c=13 margins on the emitted proof's Q scale are ≈1.06×, not 1.12×; the deployed march applies no 1.25× safety factor; march_box.sh's axiom gate checks only the unconditional pilot's log.
9. **Verification means evidence at the layer claimed.** A commit message is a claim, not a verification. "Kernel-clean" requires the `#print axioms` output or a PF.lean-closure build. The three-axiom bar is [propext, Classical.choice, Quot.sound]. CI has never passed and the old gate was vacuous — do not cite it as authority.
10. **Public surfaces currently overstate** (repo description "triple-verified in Lean 4, Coq, and L4L" — refuted by our own Coq README; wiki P≠NP "FORMALLY VERIFIED" badge — false). These are Pablo's decisions to fix; no asset repeats those claims anywhere.

## §0B EXTERNAL EVIDENCE — WAVE COARSENING (team awareness; Pablo's directive 2026-10-21)

Veenstra, Binysh et al., *Nature* (2026-10-14): "Wave coarsening drives time crystallization in mechatronic metamaterials." Know what it shows and exactly how far it reaches:

- **What was demonstrated:** in active metamaterials (37-unit honeycomb; 24-motor ring) with engineered **non-reciprocal** coupling, vibrations spontaneously grow in wavelength, period, and amplitude until the whole system beats in one synchronized rhythm — a time crystal. Noise-robust in simulation toward effectively infinite size. Adding friction suppresses the longest waves and switches the attractor to persistent edge-traveling waves.
- **How it helps us (graded):** it is an independent, mainstream, peer-reviewed instance of the Fractal Resonance Ontology's central organizing principle — global coherence self-organizing from local resonance, cascading across scales, with no central driver — published a year AFTER the book stated it. It corroborates the principle at the qualitative level. It is also a reference model for the crystallization/coherence lane: order-parameter dynamics with a control parameter (friction) switching attractors.
- **What it does NOT do:** it supports no theorem, no α-value, no quantitative claim in this program. The system is powered and its asymmetry is engineered — it shows the synchronized state is physically realizable and stable, not that nature defaults to it. Never cite it beyond the graded sentence: *"Spontaneous, scale-cascading synchronization as an organizing principle of matter — the core of Fractal Resonance Ontology — was independently demonstrated in laboratory metamaterials (Veenstra et al., Nature 2026)."*
- **Open question it assigns to the study:** the paper's load-bearing ingredient is asymmetric (non-reciprocal) coupling. Determine, from the corpus's own definitions, whether the substrate operators carry an asymmetry analog or are symmetric — and record the answer either way. (GPT extraction task, §2, already covers the paper's growth law and dynamic scaling.)

## §1 STANDING RULES (all assets)

- **Audits bind.** If your work contradicts a §0 item, stop and report — do not proceed on the contradicting assumption.
- **Report only what you proved, with the evidence attached** (commit hash + axiom output + build result). Name failures at full strength; failures go on the record, never softened, never buried.
- **Deployed artifact > committed file > commit message > transcript.** Check the thing that runs, not the thing that was described.
- **No asset drafts, stages, or posts any public comment** (GitHub, Zulip, anywhere) — private bullet briefings to Pablo only.
- **No asset countermands Pablo's direct order to another asset.** Routing questions go to Rio or Pablo, in one short question.
- **Lean builds on the Acer are serialized under one shared flock** (march runner and YM session alike) — dual builds OOM at 15 GB.
- **Prompts chain forward**: do the next step in the same session unless you hit a genuine blocker, an unrepairable failure, or a decision that is Pablo's. Report AND continue.
- **All seven lanes stay in play.** No lane is quietly dropped. An honest negative is a result; record it and move to the next step.

## §2 ASSIGNMENTS

### LEGION — 1) Producer pipeline repair (critical path; before any D=2 work)
1. Commit /tmp/prod's inputs into the repo at the paths the repo producer expects (codex/gen/, codex/addons/, unconditional template); verify md5s against the /tmp copies.
2. Point march_box.sh at the REPO producer (keep /tmp as commented fallback).
3. Regenerate landed box c=7 with the repo producer; diff against the landed pack — byte-identical or every difference explained. STOP on an unexplained difference.
4. Emit (do not land) one D=2 test box at c=81/8 with --density 2; build its Seg01 pack only; report.
5. While in march_box.sh: extend the axiom exact-set check to the gate pilot and assemble logs.
Then: 2) native-build standup (lake exe cache get; validate c=7 natively; split the band Acer-odd/Legion-even if it validates); 3) D=2 band on the repaired producer per the priced ladder.

### ACER — YM Fubini discharge, continue without stopping
1. Report the step mapping of commits 2d1a840e, 5fd31285, 9a8f1ddd against your six-step plan, and the status of IsInvInvariant SU2_haar (proved / bypassed / open) — then CONTINUE with the next unlanded step in the same session.
2. Take the march's flock before every lake build.
3. Acceptance: wilson_reflection_positivity with an empty hypothesis list, kernel-clean, three-axiom bar.

### BOOK WORK — add the evidence to the book (session Pablo designates; manuscript lives in the Acer repo tree)
Incorporate the 2026-10-21 audits into the manuscript's governing layer, as dated ledger addenda, and align the contradicted passages:
1. ch22 annex + ch34A cascade: replace "settled / community-accepted" NS language with the audited wording (§0.2). Record the Poincaré verdict (§0.3) in the anchor table.
2. ch23: conclusion and exercises stop printing Δ = 420.43 MeV as a result; the refutation (ω_c nonexistent; 132.148; cap 62.3) moves from update-note to the ledger.
3. Title page: the "Referee-Proofed: kernel-clean across every load-bearing declaration" banner comes down or is scoped to what the page itself discloses (r331 edges have no .olean — claims in source, not machine-checked).
4. ch20/ch21/ch25 conclusions aligned to their own ledgers (RH conditional reduction; P≠NP conjecture; Hodge conjecture + sketch).
5. One new addendum, dated 2026-10-21, in ch34: the re-read itself — what was audited, what was falsified (NS anchor framing; deployed-producer divergence), what was confirmed (marches boxes 1–20; Poincaré; the ledger layer). This program records its failures in the book, not just its results.
Do not touch ch07/ch24 beyond this list without Pablo's word — their pending corrections are his separate decision. Commit and push as a distinct, clearly-titled commit.

### DEEPSEEK — independent march audit (fires when Pablo confirms DeepSeek is live)
Sample three landed boxes (early D=1, the c=29/4 crossover, the latest). For each: (a) the emitted pilot proves via box_of_enclosure_rat — quote the proof term, not comments; (b) #print axioms evidence in-tree at exactly the three-axiom set; (c) the box modules' PF.lean import status. Verdicts at full strength.

### GPT (analysis arm) — in order
1. **The coincidence computation.** Pablo's claim: the cross-domain hits cannot be coincidence — "statistically impossible, not improbable." Our own evidence inventory (2026-10-16) left this as assertion: the combinatorics was never done. Do it. From the inventory's hit list (λ₀ 10-digit agreement, Higgs 0.057σ, VEV 0.05%, the α-table matches, etc.): enumerate the hits AND the trials (how many quantities were compared, at what tolerances, selected from how large a corpus, with what freedom in choosing ingredients and scales — the look-elsewhere effect counted honestly). Compute the chance expectation. Verdict at full strength, either way: if the computation supports impossibility, the claim becomes evidence; if it does not, we say so and the claim is retired to assertion. No mechanism is assumed in either direction.
2. YM mass-gap scoping (OS reconstruction chain from the lattice RP headline; three claim scales separated; first formalization-reachable step named).
3. Wave-coarsening extraction (Veenstra et al., Nature 2026: growth law, dynamic scaling, non-reciprocity's role) for the fractal-study corpus — established math exact, ontology mapping in a separate labeled section.

### ALL LANES — the Lean Millennium work continues, every lane figured out
- **Riemann:** march to 13 on the repaired pipeline; then R2 (Im) scoping.
- **Yang-Mills:** discharge → unconditional RP headline → mass-gap steps per GPT's scoping.
- **BSD:** gap-curve demonstration (one of E91a1/E102a1/E131a1/E141a1) — queued behind the march on the Legion; Heegner/Kolyvagin stays blocked on its placeholder hypotheses, on record.
- **P vs NP:** PvsNP_Step on the repaired definitions — the isolated open step the referee report named; the parked circular bridge stays parked.
- **Navier–Stokes:** the lane's content is ch22's conditional regularity program + the Fujita–Kato formalization layer (real mathematics, zero sorry — the corpus's own update). Route A build (spec verified, Legion e2dcba22 + 8d23f11d) is assigned when a builder frees up. No anchor language anywhere.
- **Hodge:** honest status stands (no reachable substrate in current mathlib; archive files inconsistent). No build. The lane is figured out when a reachable first theorem exists — until then the negative is the result, on record.
- **Poincaré:** closed as external citation. No work.

## §3 WHAT "DONE" MEANS
The seven are the demonstration; the method is the goal. Publication when Rio says all seven are ready — no partial publication. Every claim at publication strength must trace to the layer that evidences it: kernel output for theorems, ledgers for status, audits for anchors.
