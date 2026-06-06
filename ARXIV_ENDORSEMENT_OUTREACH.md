# arXiv Endorsement Outreach — Draft Messages

**For**: Pablo Cohen
**Date**: 2026-06-06
**Purpose**: Drafted text for the Lean Zulip outreach plus drafted emails to Kevin Buzzard, Patrick Massot, Heather Macbeth, and Terence Tao.

Use these as starting points. Edit lightly to fit your voice. Placeholders are marked with `[BRACKETS]`. Do not edit the honest-scope sentences — those are load-bearing.

---

## 1. Lean Zulip — Introduction Post

### 1.1 Where to post

URL: `https://leanprover.zulipchat.com`
Stream: `#new members`
Subject / topic title: `Principia Fractalis — substrate-level Lean 4 framework, seeking feedback`

### 1.2 The post

> Hi all. I'm Pablo Cohen, building a substrate-level mathematical framework called Principia Fractalis in Lean 4 (8226 jobs clean, kernel-only axioms `[propext, Classical.choice, Quot.sound]`, zero project axioms).
>
> The framework reformulates the six remaining Clay Millennium Problems as substrate-coupled sub-stories via 11 framework-internal arithmetic compatibility identities and a simultaneous-closure mechanism on canonical encodings. **This is not a Clay-prize claim** — substrate-level reformulation only, honest scope preserved throughout. The discharges land on the framework's own encodings, not on the literal mathlib carriers, and that gap is foregrounded on page 1 of every paper.
>
> Independent kernel re-verification harness in `PF_Lean4Lean` (4039 jobs clean, same-language Path-C second pass through Lean's kernel from a separate Lake package — build-hash robustness, not an independent type-checker).
>
> Looking for community feedback and possibly an arXiv endorsement for math.LO or cs.LO submission of the master paper.
>
> GitHub: `https://github.com/FractalDevTeam/Principia-Fractalis`
> Master paper: `Papers/clay_substrate_reformulation_v1.pdf`
>
> Background on me: cybersecurity professional (CompTIA, CEH) and audio engineer by trade, not academic mathematics. Working on this for about [N] years. I am happy to walk through any specific Lean file's honest-scope section with anyone interested.

### 1.3 Notes on handling replies

- **If someone asks for a specific theorem**: point to `PF/Referee/PerelmanAnchoredSimultaneousClosure.lean`, theorem `perelman_anchor_yields_simultaneous_clay_closure` (line 245). That is the headline result.
- **If someone challenges the encoding being non-canonical**: agree, point to the per-axis `HONEST SCOPE` blocks in the Lean files (every V4 capstone file has one).
- **If someone says "this looks too good to be true"**: agree that headline framing is dangerous, and point them to the master paper's Section 1.1 ("What this paper offers and what it does not offer") boxed note. The honest scope is in the paper itself.
- **If someone offers to look at the Lean tree**: thank them, give them the GitHub link, and ask if there is a specific theorem they want re-verified independently. Path-C re-binding is the term to use.
- **Do not promise turnaround on questions you cannot answer in real time**. It is fine to say: "I will check the Lean tree and reply later." Then actually check, and actually reply.

### 1.4 If someone in `#new members` suggests `#general` or `#Machine Learning for Theorem Proving`

Follow the suggestion. Post the second message (below) there.

---

## 2. Lean Zulip — Follow-up post in `#Machine Learning for Theorem Proving` or `#general`

### 2.1 The post

> Following up from `#new members`. The framework's Lean 4 development tree, `PF_Lean4_Code/`, contains:
>
> 1. A simultaneous-closure mechanism: `perelman_anchor_yields_simultaneous_clay_closure` in `PF/Referee/PerelmanAnchoredSimultaneousClosure.lean`. One bundle (five typed residuals plus two `True`-markers) plus the editorial convention `alpha_Poincaré = 1`, yielding all six `Clay_*_Standard` contracts on the framework's canonical encodings.
>
> 2. Eleven framework-internal arithmetic compatibility identities on the chosen alpha-skeleton, in `PF/CrossMillenniumSharedInvariants.lean`. Each is by `ring`, `norm_num`, or `linarith` on the definitions. The file header states explicitly that these are not Millennium discharges; they are axiom-free algebraic facts.
>
> 3. Per-axis V4 capstone bridges, each with its own honest-scope section: RH (Mayer 1991), P vs NP (canonical complexity encoding), NS (Fujita-Kato 1964 residual), YM (finite-dim Fin 2 to R carrier), BSD (17-curve case-split), Hodge (substrate-shadow obstruction).
>
> 4. Independent re-verification harness in `PF_Lean4Lean/` — same-language Path-C re-binding of every V4 capstone plus the Master Theorem plus the unified closure.
>
> Coq mirror is parity-only (about 75% `:= True`); not independent semantic verification.
>
> Build state: 8226 jobs clean. Kernel-only axioms. Zero `sorry`, zero `admit`, zero project axioms.
>
> Would anyone in the formalization community be interested in an arXiv endorsement for math.LO or cs.LO? The master paper foregrounds honest scope throughout — this is a substrate-level reformulation, not a Clay-prize claim.

### 2.2 If you get no engagement in 48 hours

Do not post again in the same stream. Move to direct email outreach (Section 4 of this document).

---

## 3. Drafted emails — direct outreach

Each draft has the same skeleton: (1) opening with honest scope, (2) what the work is, (3) what you are asking for, (4) links. Customize the `[BRACKETS]`.

### 3.1 Email to Kevin Buzzard

**To**: `k.buzzard@imperial.ac.uk`
**Subject**: Substrate-level reformulation of six remaining Clay Millennium Problems in Lean 4 — request for review or endorsement

> Dear Professor Buzzard,
>
> I am writing to introduce a Lean 4 development I have built called Principia Fractalis. **This is not a Clay-prize claim.** It is a substrate-level reformulation of the six remaining Clay Millennium Problems via one mechanism, machine-verified in Lean 4 with kernel-only axioms `[propext, Classical.choice, Quot.sound]`, zero project axioms, 8226 jobs clean. The discharges land on the framework's own canonical encodings, which differ from the literal mathlib carriers in named, disclosed ways (substrate-shadow vs literal Chow group; finite-dim Fin 2 to R vs L^2; six-piece framework-Prop conjunction vs literal PDE; etc). Every V4 capstone file carries its own `HONEST SCOPE` block; the paper preserves the same scope throughout.
>
> I am a cybersecurity professional and audio engineer by background, not an academic mathematician. I have been building this work for several years, with substantial AI-collaboration support (Claude Opus). I have no institutional affiliation. I have read enough of your writing on Lean formalization to know that you have championed Lean as a vehicle for serious mathematics — that is why I am writing to you.
>
> Two specific asks, either of which would be valuable:
>
> 1. An arXiv endorsement for math.LO or cs.LO so the master paper (`clay_substrate_reformulation_v1.pdf`) can be submitted as a preprint. Endorsement does not require you to vouch for the substance — only that the paper belongs in that category.
>
> 2. Feedback on the formalization approach, particularly on the simultaneous-closure mechanism (`perelman_anchor_yields_simultaneous_clay_closure` in `PF/Referee/PerelmanAnchoredSimultaneousClosure.lean`). I would value any pointer on whether the substrate-level framing is structurally illuminating, or whether the named residuals (Mayer 1991, Fujita-Kato 1964, the literal Chow group at codim 2) are addressable through extensions of existing mathlib infrastructure.
>
> Repository: `https://github.com/FractalDevTeam/Principia-Fractalis`
> Master paper: `Papers/clay_substrate_reformulation_v1.pdf` (14 pages, HEAD `202e671`)
> 852-page manuscript: `Principia_Fractalis_master_folder/main.pdf`
>
> Independent expert review and substantial revision are explicitly invited. I am happy to walk through any specific Lean file at your convenience.
>
> Thank you for your time.
>
> Pablo Cohen
> `psolorzano@gmail.com`
> [Mesa, AZ]

### 3.2 Email to Patrick Massot

**To**: `patrick.massot@universite-paris-saclay.fr` (verify current address before sending)
**Subject**: Lean 4 substrate-level reformulation of six remaining Clay axes — feedback request

> Dear Professor Massot,
>
> I am writing to introduce a Lean 4 development I have built called Principia Fractalis. **This is not a Clay-prize claim.** It is a substrate-level reformulation of the six remaining Clay Millennium Problems via one mechanism, machine-verified in Lean 4 with kernel-only axioms `[propext, Classical.choice, Quot.sound]`, zero project axioms, 8226 jobs clean.
>
> I am writing to you specifically because of your work on Lean infrastructure and the sphere eversion project — both demonstrate that complex multi-file Lean developments can be structured to make the kernel-axiom posture transparent. That is the discipline I have tried to follow. Every V4 capstone file in `PF_Lean4_Code/` carries its own `HONEST SCOPE` block flagging the substrate-shadow / finite-dim / typed-residual gaps to the literal mathlib carriers; the master paper preserves the same scope on the prose side.
>
> Two asks, either of which would be valuable:
>
> 1. An arXiv endorsement for math.LO or cs.LO so the master paper can be submitted as a preprint.
>
> 2. Feedback on the formalization structure, particularly on the independent re-verification harness in `PF_Lean4Lean/` (same-language Path-C second pass through Lean's kernel from a separate Lake package, 4039 jobs clean). I am uncertain whether this is the right framing of build-hash robustness for the formalization community.
>
> Repository: `https://github.com/FractalDevTeam/Principia-Fractalis`
> Master paper: `Papers/clay_substrate_reformulation_v1.pdf` (14 pages)
> Background: cybersecurity professional and audio engineer; no academic affiliation; AI-collaboration with Claude Opus.
>
> Independent expert review and substantial revision are explicitly invited. Thank you for your time.
>
> Pablo Cohen
> `psolorzano@gmail.com`
> [Mesa, AZ]

### 3.3 Email to Heather Macbeth

**To**: `hmacbeth1@fordham.edu` (verify current address before sending)
**Subject**: Lean 4 substrate-level reformulation, six remaining Clay axes — request for review

> Dear Professor Macbeth,
>
> I am writing to introduce a Lean 4 development I have built called Principia Fractalis. **This is not a Clay-prize claim.** It is a substrate-level reformulation of the six remaining Clay Millennium Problems via one mechanism, machine-verified in Lean 4 with kernel-only axioms `[propext, Classical.choice, Quot.sound]`, zero project axioms, 8226 jobs clean.
>
> I am writing to you because your writing on Lean methodology has been one of the most accessible entry points I have found, and accessibility is a value I have tried to preserve in this work. The master paper foregrounds honest scope on page 1 — what the Lean kernel carries, what it does not, and where the framework's encodings differ from the literal mathlib carriers. The discharges land on the framework's canonical encodings, not on the literal Clay-statement carriers; every V4 capstone file carries its own `HONEST SCOPE` block.
>
> Two asks, either of which would be valuable:
>
> 1. An arXiv endorsement for math.LO or cs.LO so the master paper can be submitted as a preprint.
>
> 2. Feedback from a Lean-formalization perspective on whether the honest-scope discipline I have tried to follow is recognizable as such by the formalization community, or whether the framing reads as overclaiming despite my best effort.
>
> Repository: `https://github.com/FractalDevTeam/Principia-Fractalis`
> Master paper: `Papers/clay_substrate_reformulation_v1.pdf` (14 pages)
> Background: cybersecurity professional (CompTIA, CEH) and audio engineer; no academic affiliation; AI-collaboration with Claude Opus.
>
> I am neurodivergent (AuDHD with dyslexia and dyscalculia); the framework's structural discipline is part of how I have organized the work for my own readability. If anything in the paper is unclear, please tell me — that feedback is genuinely useful.
>
> Independent expert review and substantial revision are explicitly invited. Thank you for your time.
>
> Pablo Cohen
> `psolorzano@gmail.com`
> [Mesa, AZ]

### 3.4 Email to Terence Tao

**To**: `tao@math.ucla.edu` (his standard public address — high volume; do not expect a fast response)
**Subject**: Lean 4 substrate-level reformulation, six remaining Clay axes — no prize claim, request for endorsement only

> Dear Professor Tao,
>
> I know your inbox is heavy. I will keep this short.
>
> **This is not a Clay-prize claim.** It is a substrate-level reformulation of the six remaining Clay Millennium Problems via one mechanism, machine-verified in Lean 4 with kernel-only axioms `[propext, Classical.choice, Quot.sound]`, zero project axioms, 8226 jobs clean. The discharges land on the framework's own canonical encodings, not on the literal mathlib carriers; the master paper foregrounds the gap on page 1.
>
> I am writing because you have engaged with carefully-formalized Lean work in the past (Equational Theories Project, PFR formalization). I am not asking you to vouch for the substance.
>
> One ask: an arXiv endorsement for math.LO or cs.LO so the master paper can be submitted as a preprint. Endorsement does not require you to vouch for substance — only category appropriateness.
>
> Repository: `https://github.com/FractalDevTeam/Principia-Fractalis`
> Master paper: `Papers/clay_substrate_reformulation_v1.pdf` (14 pages)
> Background: cybersecurity professional and audio engineer; no academic affiliation; AI-collaboration with Claude Opus.
>
> If endorsement is not appropriate, no reply needed. Thank you for your time regardless.
>
> Pablo Cohen
> `psolorzano@gmail.com`
> [Mesa, AZ]

---

## 4. Optional — second-tier email targets

Use these only after the four above, and only if the first round produces no endorser.

### 4.1 Possible additional targets (do not contact until first round is complete)

- **Mario Carneiro** (Carnegie Mellon) — Lean kernel and metatheory; the obvious technical reviewer for the Lean4Lean harness framing.
- **Floris van Doorn** (University of Bonn) — Lean formalization, mathlib core; accessible style.
- **Johan Commelin** (Utrecht) — Liquid Tensor Experiment veteran; understands "this isn't a Fields-medal claim" framing because LTE was framed similarly.
- **Bhavik Mehta** (Imperial / Cambridge) — Lean formalization across pure mathematics.

For any of these, use the same skeleton as the Buzzard / Massot / Macbeth drafts. Substitute the relevant person-specific paragraph.

---

## 5. What to do if all four targets decline

1. **Do not despair.** Endorsement on arXiv is one of several routes. ResearchGate, Academia.edu, and Google Scholar (Tier 1) are independent of arXiv.
2. **Re-read the four declines** and look for common feedback. Common feedback is signal; act on it. Revise the paper accordingly. Re-submit to Tier 1 with the revision noted.
3. **Try the Lean Zulip again**, posting in `#general` with a "round 2" framing: "Tried direct outreach; here is the consolidated feedback; revising; would value any further pointers." Honest engagement with critique gets more sympathy than another bid for endorsement.
4. **Submit to a peer-reviewed formalization venue** as an alternative: ITP (Interactive Theorem Proving), CPP (Certified Programs and Proofs), or LIPIcs more broadly. These are conference venues that accept formalization papers and do not require arXiv preprint.

---

## 6. Closing notes

- **Do not send all four emails at once.** Space them by 1 to 2 weeks. If one responds positively, pause the others briefly to consolidate the engagement before opening more threads.
- **Do not promise revisions you cannot deliver in a defined timeframe.** It is fine to say "I will revise and circulate in two weeks." It is not fine to say "yes" and disappear for three months.
- **Save every reply.** Reviewer feedback — even brief feedback — is the most valuable input you can get. File it, re-read it before each next outreach.
- **Honest scope is your shield.** If you ever feel pressure to overclaim, re-read `PUBLICATION_SUITE.md` Section 3. The work IS what it IS, and IS NOT what it IS NOT. Saying so is not weakness; saying so is what makes the work trustworthy.

You have done the work. The papers are honest. The Lean kernel reports zero project axioms. The rest is communication.

— end —
