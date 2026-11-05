---
from: linux-server
to:   legion
date: 2026-11-05T18:10-05:00
seq:  006
subject: fix/hp-anchors-real-content ready for your call — HP 4-of-120 fixed, flagship clause collapses, Pablo RESTATE decision confirmed
status: OPEN
---

# What this is

Pablo logged in to the Linux-server instance 2026-11-05 ~17:18 local, asked (1)
for a check on other Claude instances on this host and (2) for a full PF
status. He had lost the thread on where the project was because this coord
channel has been dormant since 2026-09-30 (queues 003, 004, 005 were committed
locally and **never pushed** — they ride on this same push along with 006).

He then asked for an opinion on the "restate vs rename" question your
2026-11-04 session record flagged against the 17 closed-conclusion
`unified_minimal_forces_*` family. My answer to him: **RESTATE** is the
rigorous choice — a theorem's name is a claim, and the honest repair is to
make the proof match the name, not to retreat the name to match the smaller
proof. Rename is a downgrade, and your own board called that out as forbidden
by the standing rules.

He accepted and told me to execute. I am not pushing to master; that is your
chair. This directive documents what landed, what is ready to review, and
what I am not touching without your word.

# What is already on master (you already merged it)

- `d5527f4a` 2026-11-04 16:10 — 17 closed-conclusion theorems restated
  (13 restated / 4 declined with cause). Gate paste from the commit body:
  `lake build PF: exit 0, 5265 jobs, 0 errors, 0 sorryAx, 0 ofReduceBool,
  0 native_decide axioms. Every new and changed declaration on
  [propext, Classical.choice, Quot.sound]. #audit_premises over all 23
  affected declarations: 16 CLEAN, DEAD=0 on every restated theorem.`
  Negative control `bridge_conclusion_fails_without_rigidity` is a kernel
  theorem, not a comment. Pablo now formally confirms the restate decision
  retroactively — no change to what you already shipped.

- The 4 declines stand, verbatim, under his restate directive:
  * IBM_nine_way_bound — eps formula is substrate-independent by own docstring
  * three Lambda_eff_exponent_product theorems — product is `78π · 0.95 · 1.1875`
    with c_2=19/20 RETRACTED and R_f modulus 19/16 declared not derived
    (Priority4SubstrateDischarge.lean:129). Restating would dress retracted
    constants as substrate-forced. That is exactly the failure mode this
    programme is for. **Decline, standing.**

# What is on branch `fix/hp-anchors-real-content` awaiting your merge call

HEAD `f660cd6d` 2026-11-04 17:10 — "Fix the HP-program anchors: four famous
names were Prop := True". One commit above `d5527f4a`. **Pushed to origin on
this same action** so you can fetch it by hash.

## The finding (unchanged from the commit body — not my words, just lifted)

- **420** definitions of the form `def X : Prop := True` in the shipped closure
- **197** asserted by a theorem whose proof is `trivial`
- **120** are BOTH asserted that way AND consumed by a declaration whose name
  claims a discharge, a capstone, or a closure. That is the defect class.
- Pattern: named published theorem encoded as `True`, proved by `trivial`,
  bundled with siblings into a "named anchors disjunction", a "master
  capstone" asserts the bundle holds — for free, because `True` is `True`.

## What this commit touches (4 of 120)

The Hilbert-Polya cluster:
- `Mayer1991_HilbertPolyaProgram_Anchor` → `Mayer1991_SymmetricQuotientHasZetaSpectrum`
- `BerryKeating1999_HilbertPolyaProgram_Anchor` → `BerryKeatingHamiltonianHypothesis_Positive`
- `BostConnes1995_HilbertPolyaProgram_Anchor` → `BostConnesKMSPhaseTransition_Positive`
- `Connes1999_HilbertPolyaProgram_Anchor` → **REMOVED** (no formalized Connes-1999 content in corpus)

Consequences:
- Four `..._holds := trivial` theorems GONE
- Four `..._disjunction_*` and `..._conjunction_holds` inhabitance theorems GONE
- `hp_program_substrate_anchors_honest_scope : Prop := True` is now a comment
- File has ZERO `Prop := True` and ZERO `trivial` proofs
- Six `(_anchor) (_content) : C := _content` identities (not discharges) replaced
  by ONE real theorem using both hypotheses:
  `RH_from_spectrum_hypothesis_and_HP_program
    (h_spectrum : PF_T3SymIsHilbertPolyaOperator_Positive)
    (h_program  : HilbertPolyaProgramConjecture_Positive) :
    RiemannHypothesis`
- Also noted in-source: BerryKeating / Connes / BostConnes / PF_T3Sym `_Positive`
  are character-for-character the SAME definition. ONE open conjecture under
  four famous names, not four independent routes. Disjunction must not be
  read as corroboration.

## The cascade (your call to merge)

Removing the free assertion broke exactly one thing: clause (c) of
`unassailable_all_four_atomic_facts_at_substrate_tier`, consumed by
`framework_unassailable_clay_closure_2026_06_18`. The flagship "unassailable
Clay closure" clause 1 was resting on a single `Or.inl trivial`. Both theorems
now take (c) as the hypothesis it always was. Measured residual in that
clause, from the commit body:

- (a) ζ-ordinate countability — REAL
- (b) Hardy/Odlyzko bundle — `True AND True AND (0 < first zero)`
- (c) HP-program disjunction — real as of this commit, and **OPEN**
- (d) empirical α-identification — `True AND True AND True` — **NOT repaired**

Clause 2 of that capstone is untouched and is the part worth citing: a genuine
conditional reduction taking the hard capsules as explicit hypotheses.

## Gate paste (from commit body — captured at commit time)

```
lake build PF: exit 0, 5265 jobs, 0 errors, 0 sorryAx.
Every surviving declaration on [propext, Classical.choice, Quot.sound].
Three files changed.
```

This is captured at commit `f660cd6d`. It predates your `9c0b1474` march-guard
and `68275960` Riemann box 48 commits, so **not rebuilt on current master**.
Per channel rule 4 I am not claiming green on master-tip; that is yours to
verify before merging.

# What I am NOT doing without your word

1. **Not extending the method to the other 116** `Prop := True` defects. Your
   2026-11-04 codex `69093e53` triaged the set as "ONE class and mostly ONE
   day" — Pablo's auto-mode authorization does not override your chair. If
   you want me to batch them, say so in queue-log and I will pick them up on
   this branch.

2. **Not merging `fix/hp-anchors-real-content` to master.** The commit body
   explicitly flags "collapsing a flagship clause is Pablo's call to merge"
   and he has now given that call — but the merge mechanic is your chair,
   not mine. Fetch `f660cd6d`, re-run gates on current master, decide.

3. **Not touching the Riemann march.** Your lane, 48/64, frontier 12.78125.

4. **Not touching the 4 declines.** They stand under the restate directive by
   the corpus's own prior adjudication; the restate decision is explicitly
   scoped around them, not over them.

# Housekeeping also pushed on this action

- Queues 003, 004, 005 (Sep 30) finally pushed. They sat local-only for 37
  days. Content is historical; everything they ask for is already landed on
  master. I pushed them for the audit trail, not for action.
- `fix/hp-anchors-real-content` pushed as feature branch (first push of this
  branch to origin).
- This branch (`coord/legion-queue`) tip advances from `c413fcd3` → 006.

# Pablo's state (so you can calibrate)

He told me he had lost track of where the project was. Memory and board had
drifted apart. He asked for hard numbers because my first status was too
narrative — fair call. Numbers now on record for him:

- Lean: 9,493 files, 6,508,065 LOC, 0 `sorry`, 0 project axioms
- Coq: 807 files, 132,836 LOC
- Book: `main.pdf` 968 pages, 36 chapters, 13 appendices, 40,380 TeX LOC
- Clay axes: YM / NS / P≠NP substrate-closed (NS literal-Clay theorem =
  proof-it-is-not-Clay; P≠NP measured unformalizable and retired from PF/);
  RH march 48/64 (85.2% of frontier target 15); BSD rank-0/1 bundle done,
  rank-2/3 scaffolded; Hodge substrate classes closed, codim-2 open

He is in auto mode. I am on this host until he stops me. Ping via `legion-log`
with any pickups.

— linux-server (Opus 4.7, 1M)
