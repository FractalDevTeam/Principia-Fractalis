# Lessons from Anthropic's FLT Formalization → Principia Fractalis Pipeline

**Sources read in full:** Anthropic research post (Sep 4, 2026); Anthropic timeline/excerpts PDF; Buzzard's Xena blog + comment thread (Sep 4–6); TNW coverage (Sep 6); Prove2Me paper, Chen–Marwaha–Lu–Yuen–Peng, arXiv:2608.28433v2.

**Headline facts:** 11 days, ~6B output tokens (internal model ≈ Fable 5.1), 29,511 theorems in the final tree (+~533k local helper lemmas), 13M lines (10.5M non-boilerplate), 3 axioms, zero sorry. First attempt (no coordination platform) **failed** — agents lost project state; failed runs contributed only ~7% of final lines. The fix was Prove2Me + a Claude-Code multi-agent harness, **not a better model**. Buzzard audited: ~100 non-definition/non-proof lines, all benign. Compile: 5h52m on 96 cores / 512 GiB.

**The single most transferable data point:** Vinogradov's Three Primes Theorem formalized in **3 days on 3 personal Claude Max plans**. Prove2Me case studies: 151K-line textbook mission closed by 6 agents on **2 consumer subscriptions (~$400)**; 81K-line research paper on ~3 subscriptions in 16 days. The datacenter was needed for FLT's *scale*, not the method. Everything below except the flagged bucket runs on two laptops + subscriptions.

---

## Technique-by-technique

### 1. Statement/proof separation ("cards")
- **What they did:** Every theorem is an immutable standalone object — NL description + preamble (imports) + Lean statement ending in `:= by sorry`. Proofs are separate files declaring `theorem solution` whose *type* must exactly match the card's type (Curry–Howard type-check, no shared file editing). A card can have multiple independent proofs; disproofs (proof of `¬statement`) are first-class.
- **2-laptop?** Yes — this is the core insight and it's cheap. It's a schema, not compute.
- **Adaptation:** Your certificate-generation → per-module serialized build already gestures at this. Go further: make every r331c/d lemma a card — one file per statement (sorry'd), one file per proof, type-match enforced by a script (compile proof file, `#check` that `solution`'s type defeq-matches the card). Kills merge conflicts between the two machines and makes any lemma independently re-provable/replaceable without touching downstream files.

### 2. Proof-sketches: import *open* theorems
- **What they did:** A proof may import cards that are **not yet proved**. That proof is a "sketch": target closed *conditional* on its children. When the last child flips to Proved, status propagates up the DAG automatically (FLT's root closed by cascade "within seconds" — R=T and Ribet level-lowering resolved in the same minute as FLT itself). Naive sorry-filling in shared files was explicitly identified as the thing that does NOT scale: recompilation of the downstream cone + non-atomizable work.
- **2-laptop?** Yes. This is *more* valuable on small compute, because it lets you commit top-down structure without paying compile cost for unfinished leaves.
- **Adaptation:** For r331c/d, write the full contour/sector skeleton NOW as sketches: zero-count identity → contour evaluation → sector bounds → finite-height RH, each conditional on named open leaves. A ~50-line SQLite/JSON DAG with statuses + a propagation script replaces Prove2Me's DB trigger. Your "root reads PROVED" moment becomes mechanical, not a manual assembly at the end.

### 3. Per-card isolated compilation
- **What they did:** Each proof compiles alone against only its children's *statements* (never their proofs). No monolithic rebuild during the campaign; the full chained build happened **once, at the end**, as the acceptance check. This is why 13M lines was tractable at all.
- **2-laptop?** Yes — this is precisely the trick a 2-laptop budget needs most. Your per-module serialized builds are the coarse version; go per-lemma.
- **Adaptation:** Compile each proof against a frozen statement-only interface file. Keep Mathlib compiled once (shared `.olean` cache, `lake exe cache get`); incremental card compiles are then seconds-to-minutes. Reserve one machine's overnight hours for the periodic full chained build (their cadence, scaled: they chained once at the end; you should chain per milestone).

### 4. DAG as shared memory (the fix for the failed first attempt)
- **What they did:** Agents' context degrades over long runs; the first swarm "lost track of the project's state and stopped collaborating." The DAG of statements *is* the durable project state — any fresh agent reads open leaves and picks work. Agents also kept a shared plan file with per-branch time estimates ("weeks"/"days"/"months") that they re-priced as evidence came in (Mazur: "1–3 weeks" → "days" → proved same evening; a "weeks" wall closed in 2h16m).
- **2-laptop?** Yes, and it directly targets your stated constraints (executive dysfunction, session resets): the state lives in the DAG, not in anyone's context window.
- **Adaptation:** One `STATE.md`/DB per campaign: open leaves, difficulty estimate, who/what is on it, last-touched. Every Claude session starts by reading it and ends by updating it. Re-price estimates aggressively downward when a proof lands faster than expected — their estimates were wrong (long) far more often than wrong (short).

### 5. Statement review BEFORE proof attempt (anti-sorry-leakage, layer 1)
- **What they did:** "Before a statement was worked on, other agents usually checked that it was true as written. This caught several false statements early." Concrete catches in the log: unbounded-denominator claim (Day 3), a "model domination" lemma that passed one review and was killed by a *computed* counterexample before anyone wrote a proof against it (Day 11), a false K1 caught and the whole corrected subtree proved 2h40m later (Day 9). Reviewers who *computed* beat reviewers who *argued*.
- **2-laptop?** Yes — it's cheap (statement review is far cheaper than proof attempt) and has the best ROI of anything in the corpus.
- **Adaptation:** Institute a two-pass gate on every new r331c/d card: (a) an independent Claude session tries to *disprove* or numerically stress the statement (your zero-count identity work is perfectly suited — evaluate the contour integrand numerically at random heights, check sector bounds at sampled points); (b) only then is it queued for proving. Rule from Day 11: reviews must compute, not argue.

### 6. Human-audited core, agent-free interior (anti-sorry-leakage, layer 2)
- **What they did:** Prove2Me "missions": humans audit ONLY the goal statement, its definitions, and ordered milestone lemmas — nothing else. Soundness argument: the trusted object is the Lean kernel's acceptance of the *audited* statements; intermediate lemmas matter only insofar as they close audited goals, so agents may generate them freely and even wrongly. Audit uses **sub-agent read-back**: an auditor agent that has never seen the source translates the Lean back to LaTeX, unfolding definitions and exposing every binder/hypothesis; the human compares source-LaTeX vs read-back-LaTeX. (Motivation: a cited Lean-as-judge audit found only ~43% of AI-proved statements faithful — statement drift, not proof error, is the failure mode at scale.)
- **2-laptop?** Yes. This is the highest-leverage safeguard for *you specifically*: your kernel-three axiom audits verify the proof; read-back verifies the **statement means what you think** — which is the actual risk in converting "proven zero-count identity" into "finite-height RH theorem." A vacuous or subtly-weakened r331c/d root statement would pass every kernel check you run.
- **Adaptation:** Fix the audited core of r331c/d in advance: the final theorem statement, the sector/contour definitions, and 5–15 milestone lemmas. For each, run a fresh context-free Claude session: "translate this Lean declaration to precise LaTeX, unfold all project-local definitions, list every hypothesis including implicit ones." You (Pablo) compare against the paper statement. Everything below the milestones needs no audit.

### 7. Milestones as canonical checkpoints
- **What they did:** Ordered, captain-attested lemma-level targets, NL statement transcribed verbatim from the source + link to its canonical formalization. Purpose: idempotence (parallel agents converge on ONE formalization instead of incompatible restatements) and authority (downstream builds on a milestone without re-auditing). When all milestones proved and connected, the root auto-resolves.
- **2-laptop?** Yes; essential for the **book queue** — the milestone list per chapter *is* Buzzard-style blueprint structure, mechanized. (Note the FLT blueprint itself — 86 pages for phase one — was the human-community route; Anthropic's run replaced the document with the DAG+milestones and adapted 106 files from Imperial/flt-regular rather than re-deriving. Lesson: harvest existing formal work; never re-prove what Mathlib/FLT-project/flt-regular already has.)
- **Adaptation:** For each queued book chapter: agent drafts milestone list from the text → you audit statements (read-back, §6) → agents farm the interior. This is the whole book-formalization workflow.

### 8. Parallelism / subgoal farming
- **What they did:** "Dozens" of agents in parallel: provers, statement-reviewers, and cross-checkers, coordinating only through the DAG + a discussion channel (progress posts, corrections, "lessons learned"; agents caught each other's errors — e.g. the `gotsman_linial` disproof → corrected re-statement → branch closed). Humans issued only priority nudges ("push Mazur to be done soon").
- **2-laptop?** Partially. Dozens of simultaneous frontier-model agents is a datacenter luxury; 3–8 concurrent sessions across two Max-tier subscriptions is realistic (that is *exactly* the Vinogradov configuration).
- **Adaptation:** Role-split rather than count-split: machine A runs 1–2 prover sessions on open leaves; machine B runs the reviewer/disprover + the serialized builds. A shared append-only `LOG.md` is the discussion channel. Your role is the captain: audit the core, nudge priorities, nothing else.

### 9. Error repair & proof-search patterns (from the reasoning excerpts)
- **What they did (recurring patterns in the PDF):**
  - *Numerical/finite certification before formal work* — check identities at concrete points (the 19a1 curve point-check, the h=2 quaternion class number via mass formula) before trusting a card.
  - *Route-switching, not route-forcing* — when the sheaf route stuck, switch to Milnor patching; when zero-counting needed unserved machinery, "too heavy, go with averaging plan." Agents priced routes by what was already **served** (proved on the platform) and preferred assembly-of-served-cards over new theory.
  - *Park-and-replace* — a hard analytic statement was parked and replaced by an algebraic equivalent that reads off served infrastructure (Igusa leaf, Day 10).
  - *Cheap-shortcut probes on "months"-class walls* — before accepting a Ribet-class dependency, check whether the specific object (Frey curve discriminant) satisfies it for free.
  - *Environment freezing* — 31% of bytes were generated preambles switching off instances/simp lemmas so each proof's environment holds still; heavy per-file heartbeat overrides. Ugly but effective at avoiding cross-file breakage.
- **2-laptop?** All yes. These are prompting/protocol patterns, zero marginal compute.
- **Adaptation:** Bake into your prover prompt: (1) numerically verify the statement first; (2) list which existing modules serve the goal; prefer assembly; (3) if stuck 30 min, propose an equivalent restatement on served ground rather than grinding; (4) for any "hard" dependency, probe whether your *specific* object (your zero-count certificate, your fixed height T) gives a shortcut the general theorem doesn't. Adopt frozen preambles per module (you already serialize builds; add `set_option` isolation headers so proofs don't break when siblings change).

### 10. Verification cadence & endgame
- **What they did:** Three tiers. (i) Continuous: per-card compile on acceptance. (ii) Milestone: subtree "PROVED" propagation. (iii) Endgame, and they were *disciplined* about claiming: the platform mark was explicitly labeled "proved on prove2me, pending the independent re-check," then — next morning — all 29,511 cards recompiled from source off-site; next day the whole tree built as a single chained Lean project (fails unless exactly `propext`, `Classical.choice`, `Quot.sound`, no sorry, and derives Mathlib's own FLT statement); then **two third-party checkers**: `comparator` (statement-match vs a reference file importing only Mathlib + full kernel replay) and `nanoda` (independent Rust kernel). Buzzard added a fourth layer: agent-flag every line that is not a definition or proof, human-inspect the residue (~100 lines).
- **2-laptop?** Entirely. comparator and nanoda are free, open tools; a chained build of your project is hours, not their 96-core 6h.
- **Adaptation for r331c/d:** Adopt the full endgame verbatim: (a) chained single-project build; (b) `#print axioms` on the root = exactly three (you do this); **add** (c) a comparator run against a reference file containing the r331c/d statement written independently, importing only Mathlib — this closes the "restricted intermediate definitions weaken the final statement" hole, which their comparator step was explicitly designed for; (d) nanoda replay; (e) the Buzzard grep: agent lists every non-def/non-proof line (custom tactics, `set_option`s, `macro`s, `axiom`s), you read all of them. Also copy the claiming discipline: "proved in-pipeline, pending recheck" until (a)–(e) pass.

### 11. Search + reuse via NL descriptions (Formalpedia)
- **What they did:** Every card carries a mandatory standardized NL description; a search API indexes them; agents must search-before-submitting to reuse rather than restate. Failure to do this at FLT scale produced the known pathology: ~40% of statements verbatim-duplicated across files, one lemma re-declared in 300+ files.
- **2-laptop?** Yes — grep/embedding search over a few thousand descriptions is trivial, and at your scale dedup actually works (at theirs it didn't).
- **Adaptation:** Add an NL-description header to every certificate/lemma file; index with ripgrep or a small embedding store; prover prompt step 0 = search it. Between r331c/d and the book queue this becomes your cross-campaign library — proved contour/analytic lemmas serve the books directly.

---

## Datacenter-only (honest bucket)

- **6B output tokens in 11 days** (~$300k at Fable 5.1 list price; internal cost lower). Two subscriptions deliver maybe 2–3 orders of magnitude less. Consequence: you cannot brute-force "months-class" walls by parallel attempt-spam; you must rely on §9's route-switching and the disprove-first gate to avoid wasting tokens on false or overpriced statements. This is the *only* fundamental gap — the Prove2Me table shows method transfers at 10³ less spend.
- **Dozens of simultaneous frontier agents with sub-minute DAG polling.** Their 39-second cascade detection and 3-agents-notice-in-25-seconds redundancy is swarm-scale. You get the same correctness with hourly polling; you lose only latency.
- **96-core / 512 GiB chained builds & 500 GB-RAM interactive editing.** Irrelevant unless you let duplication explode. Their 13M-line pathology (2-in-5 duplicate statements, 20× Mathlib compile time) is a *symptom of unlimited tokens*, not a requirement of the method. Your budget forces the discipline that makes builds fit on a laptop — treat that as an advantage.
- **An internal research model ahead of released Fable 5.1.** Mildly better per-attempt yield; the Prove2Me case studies closed comparable missions with released consumer models, so this is a rate multiplier, not an enabler.
- **A dedicated human team on call for priority nudges + a platform moderator.** You are one person; mitigate by shrinking the audited core (§6) and letting propagation (§2) replace project management.

---

## Top 5 adoptions, ranked by expected speedup ÷ implementation cost

1. **Card schema + sketch-DAG with auto-propagation (§1+§2+§4).** ~1–2 days to build (JSON/SQLite + type-match script + propagation). Directly fixes the two things that kill 2-laptop campaigns: cross-session state loss and monolithic rebuilds. This was *the* difference between their failed and successful runs — highest confidence transfer.
2. **Disprove-before-prove statement gate with computed (numerical) checks (§5, §9).** ~Half a day: a reviewer prompt + a numerics harness (you already have certificate-generation machinery to repurpose). False statements are the most expensive token sink on a small budget; they caught "several" pre-proof and one post-review.
3. **Read-back audit of the r331c/d core (§6).** ~1 day for a dozen statements. Protects the campaign's entire value: a kernel-perfect proof of a drifted finite-height-RH statement is worthless, and your current kernel-three audit does not detect drift. Cited base rate for unaudited AI statements: ~43% faithful.
4. **Comparator + nanoda + Buzzard-grep endgame (§10).** ~Half a day to wire, run per milestone. Free external credibility — for a claimed RH-adjacent result, third-party-replayable checks and a hand-inspected non-proof residue are what make the announcement survivable.
5. **Milestone-driven book pipeline with search-before-submit (§7+§11).** ~1 day per book to draft+audit milestones; then the queue becomes farming. Slower payoff than 1–4 but converts the book queue from open-ended projects into the same mechanical loop as r331c/d, with a shared reusable library.

*Not adopted, deliberately:* their duplication-tolerant style (40% duplicate statements, per-file heartbeat overrides at 2000× default) — affordable only with their compute; on two laptops it would sink your build times. Adopt the frozen-preamble idea (§9) but with dedup enforced by §11.
