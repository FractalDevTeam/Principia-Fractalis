# Dispatch packets — 2026-10-05

Five packets. Each is self-contained and copy-pasteable. **Send
`codex/STATE_OF_PLAY_2026-10-05.md` first in the same conversation**, then the
packet.

The division of labour follows what each recipient can actually *verify* — not
what it can opine about:

| Recipient | Has | Therefore gets |
|---|---|---|
| **B** — Claude Desktop app (Windows) | reasoning; file access at best; **no Lean toolchain** | proof-architecture review, ledger audit against the brief |
| **A** — ChatGPT / Gemini / Grok | web, no repo | mathlib-master check, literature priority, adversarial math |
| **C** — any instance with repo + toolchain (Legion CLI, WSL) | Lean 4, mathlib, `lake` | independent build + gate on a non-Acer tree |
| **D** — local Claude Code subagents | repo via `ssh acer` | read-only sweeps, parallelisable |
| **E** — any model, no tools | the brief only | the four authorial decisions |

---

## PACKET B — Claude Desktop app, Windows (the dispatch instance)

> **Read this framing before the task.** You do not have the Lean toolchain, so
> you cannot re-verify anything by building it. That is fine and expected: your
> job is the part that does not need a compiler. But it means that **where the
> brief reports a gate result or an axiom audit, that is a measurement, not an
> opinion to be argued with.** If you want to dispute one, the correct move is
> to say precisely which command you would run and what you predict it returns,
> and it will be run.
>
> Two things to get right up front, because they have gone wrong in this
> channel before:
>
> 1. **The project does not claim to have solved any Millennium Prize problem.**
>    Its own standing rule — written by the author in
>    `codex/BOOK_RIGOR_LEDGER_SPEC.md` in July, not a concession extracted
>    later — is that any claim whose closure would resolve a Millennium problem
>    is labelled **CONDITIONAL REDUCTION, never PROVEN**. Arguing against a
>    claim the project does not make is wasted effort for everyone. If you find a
>    chapter that *has* drifted from that rule, **that** is a real finding and is
>    wanted.
> 2. **Do not propose downgrades.** "Relabel this theorem as a postulate" or
>    "withdraw this claim" is not a resolution here; it is treated as a symptom
>    of an upstream mistake that should be repaired instead. Find the cause,
>    name the repair.
>
> With that said — be hard on the mathematics. Adversarial on substance is
> exactly what is wanted. Adversarial about labelling is not.
>
> **B1. Review the proof architecture of the load-bearing theorem.** The one
> kernel-verified claim everything else leans on is:
>
> > Any C\*-algebra `A` carrying a witness of `Substrate3Inf A` — a tower
> > `tower : ℕ → StarSubalgebra ℂ A`, each `tower k` \*-isomorphic to
> > `M_{3^k}(ℂ)`, inclusions `tower k ≤ tower (k+1)`, and `⨆ k, tower k` dense
> > in `A` — is \*-isomorphic to a fixed `TimelessFieldCompletion`.
>
> It is proved in four arcs: **C1** block-diagonal amplification
> `M_n(ℂ) → M_{kn}(ℂ)`; **C2** Noether–Skolem (any two unital \*-homs
> `M_n(ℂ) → M_{kn}(ℂ)` are unitarily conjugate); **C3** the completion
> universal property, star-upgraded; **C4** Elliott back-and-forth for `3^∞`
> towers. Questions:
>
> - Is that the right **decomposition** of Glimm's argument? Is an arc missing —
>   in particular, is anything needed to guarantee each tower embedding has
>   multiplicity exactly 3, or does the `3^k` dimension sequence force it?
> - C4 is the back-and-forth. What is the standard obligation there that is
>   easiest to get wrong, and what would its absence look like in a statement?
> - The structure deliberately does **not** assume a unique trace — uniqueness
>   is derived instead (`Substrate3Inf.trace_unique`). Does deriving it require
>   something that must then be assumed elsewhere?
> - Is `Dense (⨆ k, tower k)` the right condition, or should it be that the
>   norm-closure of the union is `A`? Same thing here or not, and does it matter?
> - Does the conclusion require `A` separable, and if so is separability implied
>   by the tower's existence?
>
> **B2. Audit the ledger for drift.** The brief gives the measured label
> distribution across 36 chapters: PROVEN in 14, CONDITIONAL REDUCTION in 7,
> ASSERTED in 24, EMPIRICAL HYPOTHESIS in 22. Reason about what that pattern
> implies, and which chapters you would check first, and what exactly you would
> look for in each.
>
> *Premise corrected 2026-10-05 — this task previously told you that "only the
> operator-algebra substrate is supposed to be kernel-verified, yet PROVEN
> appears in 14 chapters", and asked you to resolve that tension. The premise
> was false and the tension was manufactured. The corpus kernel-verifies the
> substrate AND a large body of arithmetic and refutation results, so PROVEN in
> 14 chapters is not prima facie anomalous. Do not reason from the withdrawn
> framing. The real question is narrower and harder: for each PROVEN label,
> is the kernel-verified statement **the statement the chapter is making**, or a
> weaker arithmetic shadow of it? A `noncomputable def` of a closed form
> followed by a theorem bracketing its decimal expansion is kernel-verified and
> establishes nothing about the physics — that shape is the one to hunt. At
> least one known case is a PROVEN label on a tautology (ch34A).*
>
> **B3. Attack today's two upstream claims on their mathematics**, not their
> gate status:
> - Is it actually true that conjugation `x ↦ u * x * star u` by a unitary is a
>   `StarAlgEquiv` over *any* star ring with the scalar-tower instances, needing
>   no C\*-structure, no norm, no completeness? Where would that fail if
>   anywhere?
> - Is it true that the C1 and C2 arcs together give a **classification** — that
>   every unital \*-hom `M_n(ℂ) → M_{kn}(ℂ)` is unitarily equivalent to the
>   standard k-fold block-diagonal amplification, so there is exactly **one**
>   unitary equivalence class? That is claimed as new today. Is it right, and is
>   it genuinely a consequence of those two arcs alone?
>
> **B4. The one thing most likely to be wrong.** Given the brief, name the
> single claim you would bet against, and say what check would settle it. One
> paragraph. This is the most useful thing you can produce.
>
> **Output.** Cite `file:line` where the brief gives one. Distinguish "this is
> wrong" from "this needs checking" from "this is fine." No preamble.

---

## PACKET A — ChatGPT / Gemini / Grok (web access, no repo)

> You are reviewing a formalisation project; the state-of-play brief is above.
> You do **not** have the repository. Everything below is answerable from the
> brief plus public sources, deliberately — these are the checks the project's
> own instance **cannot** perform.
>
> **A1. The mathlib-master check. Highest value, and why you specifically.**
> The absence claims below were verified against mathlib pinned at rev
> `eed770a434957369c6262aa3fb1d6426419016d4` (Lean 4 `v4.24.0-rc1`, ~September
> 2026). That pin is stale. Check **current mathlib master** and report
> EXISTS / ABSENT / PARTIAL with file path and declaration name:
>
> 1. `coe_iSup_of_directed` for **unital** `StarSubalgebra` — the underlying set
>    of a directed supremum of unital \*-subalgebras is the union of the
>    underlying sets. Mathlib has it for `NonUnitalStarSubalgebra`, `Subalgebra`,
>    `Subfield`, `Subring`, `Submodule`, `Submonoid`, `Subgroup`,
>    `IntermediateField`. Claim: the unital \*-case is the one omission.
> 2. Conjugation by a unitary `x ↦ u * x * star u` as a bundled **`StarAlgEquiv`**
>    — not merely the spectral consequence `spectrum.unitary_conjugate`. Any
>    `innerAut` for star algebras?
> 3. A **star-preserving** version of `Matrix.reindexAlgEquiv`:
>    `Matrix m m A ≃⋆ₐ[R] Matrix n n A` from `e : m ≃ n`.
> 4. A **star analogue of `IsDenseInducing.extendRingHom`** — extending a
>    \*-algebra hom along a dense uniform inducing map.
> 5. **Noether–Skolem in any form**: that every \*-automorphism of `M_n(ℂ)`, or
>    every automorphism of a central simple algebra, is inner. Also any `IsInner`
>    predicate for algebra homs. Claim: mathlib has none, and its only `Skolem`
>    is unrelated model-theoretic Skolemisation in the `choose` tactic.
> 6. Any **UHF algebra, Glimm classification, or supernatural number** content.
>    Claim: zero.
>
> If any now exists upstream, say so plainly. **A refuted absence claim is the
> single most useful thing you can return** — far better to drop a redundant
> lemma than to submit one.
>
> **A2. Priority check.** The project claims its Lean formalisation of
> **Glimm's 1960 UHF classification specialised to supernatural number `3^∞`**
> is the first in any proof assistant, checked against mathlib4, Isabelle/HOL,
> Coq/Rocq, Agda and Lean 3. Try to refute it: AFP, Coq/Rocq opam and community
> archives, Agda libraries, Lean Zulip, formalisation literature. Also: has
> Noether–Skolem been formalised in any system?
>
> **A3. Adversarial review of the characterisation.** Same `Substrate3Inf`
> statement as Packet B quotes. Attack it as a mathematician: is it the right
> characterisation of the `3^∞` UHF algebra; is anything missing that Glimm's
> theorem needs (separability, unitality of inclusions, embedding multiplicity
> exactly 3); is deriving trace-uniqueness rather than assuming it legitimate;
> is density of the union the correct condition.
>
> **A4. Sanity-check two negative results** from §5 of the brief, on the
> mathematics alone:
> - that `ch_2` as defined by the stated matrix formula has range exactly
>   `[-1/2, +1/2]` on every real matrix, sharp at both ends — which would make a
>   published `> 0.95` threshold satisfiable by no matrix at all;
> - that a collapse rate depending on a nonlinear state functional (purity)
>   breaks affinity on mixtures and reopens the Gisin/Polchinski superluminal
>   signalling hazard, while a constant rate does not.
>
> **Rules.** Cite sources; a link beats a recollection. Distinguish "checked,
> absent" from "did not find." Do not claim the project has solved a Millennium
> problem — its own rule forbids that label and overclaiming on its behalf is as
> unhelpful as underclaiming. Do not propose withdrawals; name repairs.

---

## PACKET C — any instance with repo + Lean toolchain (Legion CLI, WSL)

> Your job is **independent verification on a tree that is not Acer's.** All of
> today's work was built and gated on Acer; a result that holds only there is
> not a result.
>
> **C1. Reproduce today's gate results from scratch.** Confirm first that
> `lean-toolchain` is `leanprover/lean4:v4.24.0-rc1` and `lake-manifest.json`
> pins mathlib `eed770a434957369c6262aa3fb1d6426419016d4` — a mismatch is itself
> a finding. Then:
>
> ```
> export PF_TREE=<abs path>/PF_Lean4_Code    # must point at PF_Lean4_Code, NOT the repo root
> cd "$PF_TREE"
> for M in PF.Upstream.MathlibStarAlgebra PF.Upstream.NoetherSkolemC2 \
>          PF.Upstream.NoetherSkolemMatrix PF.SubstrateRigidity; do
>   lake build "$M" && bash scripts/pristine_gate.sh "$M"
> done
> ```
>
> | module | expected |
> |---|---|
> | `PF.Upstream.MathlibStarAlgebra` | PRISTINE, 14 decls |
> | `PF.Upstream.NoetherSkolemC2` | PRISTINE, 20 decls, 3 private unprobeable |
> | `PF.Upstream.NoetherSkolemMatrix` | PRISTINE, 8 decls |
> | `PF.SubstrateRigidity` | **NOT PRISTINE** — (d2) fails, 13 findings; (b) passes over 12 records; 7 audited decls all `[propext, Classical.choice, Quot.sound]` |
>
> `StarAlgEquiv.conjugateBy` must report **"does not depend on any axioms"** —
> not even `propext`. Anything else is a finding.
>
> Cap parallelism: on Acer, Lake 5.0.0 has no `-j` and needs `taskset -c 0,1`
> or it OOMs. Apply the equivalent on your box. Never run duplicate builds.
>
> **C2. Verify the extraction is byte-identical.**
> `PF/Upstream/NoetherSkolemC2.lean` was produced by slicing lines 481–1482 of
> `PF/SubstrateRigidity.lean` as of commit `f471b3ba`:
>
> ```
> git show f471b3ba~1:PF_Lean4_Code/PF/SubstrateRigidity.lean | sed -n '481,1482p' > /tmp/slice.lean
> ```
>
> Compare against the body of `NoetherSkolemC2.lean` below its header. It must
> match exactly. A difference means something was retyped, and retyping is
> where drift enters.
>
> **C3. Verify the de-duplication was semantically null.** At `414c9155`
> SubstrateRigidity lost 1,001 lines and gained 19. Confirm the seven audited
> declarations' axiom sets are identical across that commit:
>
> ```
> git checkout 414c9155~1 -- PF_Lean4_Code/PF/SubstrateRigidity.lean
> lake build PF.SubstrateRigidity 2>&1 | grep 'depends on axioms' > /tmp/before.txt
> git checkout 414c9155  -- PF_Lean4_Code/PF/SubstrateRigidity.lean
> lake build PF.SubstrateRigidity 2>&1 | grep 'depends on axioms' > /tmp/after.txt
> diff /tmp/before.txt /tmp/after.txt     # expect: differs only in line numbers
> ```
>
> **C4. Corpus-wide effect of the auditor fix.** Commit `9a97e85d` made
> `#audit_all` skip structure-field projections. It can only remove findings, so
> nothing previously PRISTINE should change — **verify that rather than
> assuming it.** Re-gate ten modules that define structures; report any that
> moved in either direction, with its `projSkipped` count.
>
> **C5. Only if C1–C4 are clean**, build the root: `lake build PF` (1,188
> modules, expensive). Report any module that fails.
>
> **Rules.** Do not push. Do not merge. Do not modify anything under
> `Principia_Fractalis_master_folder/` or any `PF/*.lean`. Never run
> `scripts/pf_dispatch_fix.sh`. Never touch MobaXterm. Report `file:line`. If
> output disagrees with the table, paste the actual output rather than
> reconciling it.

---

## PACKET D — local Claude Code subagents (parallel, read-only)

All read-only, independent of each other and of the Lean critical path, so they
run concurrently.

> **D1.** *(dispatched 2026-10-05)* Sweep all 36 chapters and the Lean tree for
> **stale self-description** — text claiming work is deferred, pending, or open
> where it is done, or claiming something done where it is not. Two instances
> known: the `PF/SubstrateRigidity.lean` header (four months false, repaired
> 2026-10-02) and `Substrate3Inf.connect_iso`'s docstring, which reads "Deferred
> as a leaf" directly above its complete proof.
>
> **D2.** Cross-check **book against Lean**: for every chapter claim labelled
> PROVEN, find the Lean declaration discharging it; confirm it exists, is wired
> into `PF.lean`, and audits clean. A PROVEN label with no corresponding
> declaration is the most serious defect the ledger can carry.
>
> **D3.** Inverse sweep: kernel-verified Lean results that **no chapter cites**.
> Today produced the motivating example — C1 and C2 together give a
> classification theorem nothing in the corpus stated, because each arc had only
> ever been read as a step toward the Elliott back-and-forth.
>
> **D4.** Sweep for **arithmetic and dimensional errors**, in the style already
> found: a suppression factor off by 10^125, a QCD scale off by 10^4, a memory
> figure off by 10^5, a 150-digit precision claim from float64 code. Recompute
> every numeric claim you can; report mismatches with corrected values.
>
> **Rules for all D packets.** Read-only — no edits, no writes, no git writes.
> Quote remote paths: the tree is
> `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE` and `Storage 2TB`
> contains a space. **Never assume** — a grep hit is a candidate, not a finding;
> verify by reading before reporting, and mark anything unverified as such with
> the check still needed. Do not propose downgrades.

---

## PACKET E — any model, no tools needed

> Four questions blocked on authorial intent, not mathematics. They are the
> gating items. Opinions wanted, clearly flagged as opinions.
>
> 1. **ch04's consciousness operator** wants a Haar measure on `Aut(T_∞)`, which
>    is not locally compact, so none exists. Right move — different
>    construction, weaker claim, or different group? Is there an amenability or
>    invariant-mean substitute that carries the chapter's intent?
> 2. **ch30/ch32 clinical provenance.** Chapters quote 847-patient figures
>    including 97.3%, filed EMPIRICAL HYPOTHESIS — UNTESTED; the corpus
>    implementation outputs ~0.004. These cannot both describe the same
>    computation. How should a book handle a quoted empirical figure it cannot
>    reproduce from its own code?
> 3. **ch25's σ** has two inequivalent definitions in play and results depend on
>    which is meant. Which governs, and what breaks either way?
> 4. **ch17's propagator compactness** is indeterminate as stated. What is the
>    minimal domain specification that makes it decidable without changing the
>    chapter's claim?

---

## Returning results

Have each recipient reply in its own channel with `file:line` citations. Paste
replies back and they will be triaged into the repair queue — anything
contradicting a current claim verified against the corpus's own prior
adjudication before action. Plausibility is not provenance; that rule has caught
me twice on this project.

*Prepared 2026-10-05 against the live Acer tree at commit `9a97e85d`, 58 commits
ahead of last-fetched `origin/master`.*
