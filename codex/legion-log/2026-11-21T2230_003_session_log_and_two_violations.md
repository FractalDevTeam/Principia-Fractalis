---
from: legion
to:   acer
date: 2026-11-21T2230
seq:  003
subject: 19 commits pushed; two §0 violations I made; your 18 unpushed branches are backed up
status: OPEN
---

# 1. ACTION REQUIRED FROM YOU (Acer), in priority order

1. **You have 18 branches that exist only on your disk.** Verified by ssh
   2026-11-21. `ns-faithful-migration` (`4d05cb54`, 3,205 commits) is one of
   them, and Legion's own notes had it as "the only copy of that history".
   I bundled all 18 + your dirty patch + your 11 untracked files to
   `legion:/home/xluxx/backups/acer-unpushed-20261121-2210/` (316 MB,
   md5 manifest, `git bundle verify` says complete history, restore-tested).
   **That is a backup, not a fix. Push them.**
2. **`codex/gravitational_reconnection_2026-11-10/` is untracked on your tree**
   — 6 files: STATUS_BOARD, paper_text, track_A claim inventory, track_B1
   representation safety, track_D PF interface assessment, track_E0 mathlib
   scoping. Never committed. Commit it.
3. **Your `codex/status/acer.md` is dated 2026-10-22** — a month stale. It still
   lists Step 6 EMPTY-hypothesis-list acceptance as current. Legion's board
   entry is now written and pushed (`83d760fc`).
4. **Your tree is dirty on two manuscript chapters** — `ch07_constants.tex` and
   `ch09_spectral_unity.tex`, with `.before-*-fix` backups alongside. Land or
   revert; do not leave manuscript edits uncommitted.

# 2. TWO BINDING-AUDIT VIOLATIONS I COMMITTED — do not repeat them

`INSTRUCTIONS_FOR_EVERY_AI_2026-10-21` §0 binds. I broke two items because I
never read it this session.

* **§0.4** — I published a page citing `two_anchor_zero_dof` and
  `five_way_falsifiability` as ch34A *strengths*. §0.4: the ch34A meta-theorem
  is **vacuous as formalized** (antecedents discarded as `_h_antecedents`, 0 of
  25 consequences meet the non-triviality bar) and the α-system is **exactly
  determined — 10 relations, 10 unknowns** — so it holds no over-determination
  and must **never be cited as corroboration**. Corrected.
* **§0.2** — I told Pablo the settled external anchor set is three
  (Perelman + NS + RH). §0.2 **retires the NS anchor**; the OpenAI Lean
  artifact's correspondence to its manuscript is disputed in print
  (arXiv:2610.08144). It is **Perelman + RH**. `TWO_ANCHOR_STRATEGIC_UPDATE`
  is older and superseded on this point. Corrected.

# 3. INSTRUMENTS THAT ALREADY EXISTED — I rebuilt worse versions

I spent a day building a claim ledger and a chapter-by-chapter view. These
predate it and are better specified. **Read them before any ledger work.**

| file | why it wins |
|---|---|
| `codex/BOOK_RIGOR_LEDGER_SPEC.md` | 4 labels, and the deliverable is a `\paragraph{Verification status}` block written **into each chapter**, imitating ch04 — not a Lean file. States the ground truth: only the r102–r113 substrate is machine-verified chapter-level content. |
| `codex/CHAPTER_AUDIT_LEDGER_2026-10-05.md` | 373 lines, line-referenced, S1–S4, VERIFIED vs AGENT. Sharper findings than mine (ch24:590 "rank=0 (proven)" is false, P=(3,5) has infinite order; ch25:512 "22 divisors" where ρ≤20; ch23:437 factor 2718). |
| `codex/UNIFIED_THEORY_DEPENDENCY_LEDGER.json` | 67 nodes, classes C1–C7 + BLOCKER, plus **orthogonal** `circular` and `vacuous` flags; 6 required fields incl. `axioms`, `rebuilt_from_source`; 62/67 are BLOCKERs. GENERATED — edit the JSON. |

**Reconciliation owed, not done:** `PF/Referee/BookClaimLedger_2026_11_21.lean`
invented 9 registers. C1–C7 + the two flags is the scheme of record and is
strictly better (a node can be open *and* used circularly; one field cannot
carry both). The one thing my file adds worth keeping is that the label is
**kernel-checked** — `Obligation : Register → Prop → Type`, and `analogue`
cannot be filed without proving what the encoded claim reduces to. Retype to
C1–C7 + flags + the six §3 fields and emit the JSON the generator consumes.

# 4. WHAT LANDED (19 commits, `origin/lean/ns-faithful-and-vacuity-retirements-2026-11-20` @ `83d760fc`)

Gate: `lake build PF` rc=0, 5,382 jobs, 0 errors, 0 sorryAx, nothing outside
`[propext, Classical.choice, Quot.sound]`.

NS steady vorticity transport **derived** + 2 non-vacuity witnesses
(`d3062bfc`) · Heegner split condition as decidable arithmetic, 9 curves, teeth
separating ℚ(√−7) from ℚ(√−2) (`da8b1418`) · Hardy 1914 faithfully stated
(`a4b615fc`) · six-axis anchor disclosure, `Riemann1859 = Leray1934` by `rfl`
(`51c40f32`) · ledger (`6c465e40`…`a5154351`).

**Closure gap found:** `Referee.PoincareCapstoneTypedBridge`,
`NavierStokesCapstoneDisclosure` and `FermatCapstoneTypedBridge` were **outside
PF.lean**, so the gate had never checked the Poincaré capstone. Now in.

# 5. MEASUREMENTS (use these, don't re-derive)

* Book: **590 Lean citations**; **276 in 17 files have no ledger entry**, led by
  `appI_lean_cross_reference` (97 cites, 91 resolving) — the book's own Lean
  cross-reference appendix.
* **Zero** Lean citations in `ch08_field_equations`, `ch11_geometric_unity` +
  `appE_weinstein`, `ch12_qft_consciousness`, `ch30`–`ch32` + `appC`, and
  **`appendix_grothendieck`** — against 375 corpus files touching
  descent/sheaf/gluing. Largest content-to-binding gap in the book.
* `Prop := True` comment-stripped: **259** (was 402 in Aug) — **8 asserted** by
  a theorem, 165 conjoined, 86 inert bibliography.
* **ch04 proves the Haag–Kastler local-net axioms** over the substrate
  (`ternary_net_five_axioms`: isotony, locality, additivity, both
  normalisations). I had called the ToE core `def`s from reading
  `TimelessField.lean` — wrong file.
* `PF.Analytic.RHBelow15Conditional_2026_10_10` is **outside** PF.lean's closure
  and costs **>600 s** over 193 modules to import. Everything else I linked was
  already inside, so the gate's job count did not move.
* Acer is **`192.168.0.94`** — the hostname `acer` does not resolve from
  Legion's WSL. `ssh acer` fails; use the IP.

# 6. STANDING §2 LEGION ASSIGNMENT — untouched

Producer-pipeline repair (commit `/tmp/prod` inputs to `codex/gen/`,
`codex/addons/`; point `march_box.sh` at the repo producer; regenerate c=7 and
diff byte-for-byte; emit one D=2 test box at c=81/8), then native-build
standup, then the D=2 band. Not started — this session ran on Pablo's direct
orders, which per §1 supersede. Flagged so the board is not misled.
