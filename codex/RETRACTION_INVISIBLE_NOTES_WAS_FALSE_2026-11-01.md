# RETRACTION — "8 invisible tcolorbox notes" was false. There are none.

**Date:** 2026-11-01
**Retracts:** a measured claim in the commit message of `e9eaaa6a`
("ch21: the three verified defects …").
**Status of the ch21 repairs in that commit:** unaffected and correct. Only the
stated justification for where the notes were placed was wrong.

---

## 0. THE RETRACTED CLAIM

`e9eaaa6a`'s message asserts, as a measurement:

> "\manuscriptcorrection is \footnote, and notes inside theorem-like tcolorbox
> environments are unreliable. Measured across five chapters: of 12 existing
> notes inside intuitive/theorem/observation/example/conjecture boxes, only 4
> reach the PDF — 8 ARE INVISIBLE."

**That is false.** Re-measured across all 69 `.tex` files with six independent
dash-free fragments per note:

| | count |
|---|---|
| `\manuscriptcorrection` / `\empiricalclaim` / `\footnote` notes tested | 114 |
| rendering | **114** |
| invisible | **0** |

Every note I had named as invisible was then checked by hand with six distinct
fragments each. All render. `ch03:326`, the last candidate, returned **6 of 6**
fragments present.

**There is no tcolorbox footnote defect. tcolorbox renders footnotes correctly.**

## 1. WHY I GOT IT WRONG

The original test asked whether ONE decisive word-run from each note appears in
`pdftotext` output. That test is unreliable in both directions and failed both
ways today:

* **False negative** — a fragment is absent because `pdftotext` hyphenated it,
  wrapped it across a page, or because the source contained `---`, which LaTeX
  sets as an em-dash so the literal three hyphens can never match. This produced
  the phantom 8.
* **False positive** — a 3-word fragment coincides with unrelated text somewhere
  in a 1.8 MB book. This earlier produced three phantom "RENDERS".

A single-fragment presence test is not a render test. **The only sound tests are
(a) a before/after comparison of the SAME string across a rebuild, or (b)
exhaustive multi-fragment with every fragment dash-free.**

## 2. WHAT REMAINS TRUE — the tabular defect is real

`\footnote` inside a `tabular` IS discarded, and the five notes repaired in
`09b46e0f` were genuinely invisible. That finding stands because it was
established by method (a) — identical strings, before and after one rebuild:

| fragment | before | after |
|---|---|---|
| `445 files containing` | **0** | 1 |
| `5147 jobs` | **0** | 1 |
| `four months stale` | **0** | 1 |

A before/after on the same string cannot be defeated by hyphenation, wrapping,
or coincidence. That is why it held and the fragment-presence test did not.

So the operative rule is narrower than I claimed, and correct:

* **`tabular` — discards footnotes. Never put a note inside one.**
* **`longtable` — keeps them** (measured: `ch20:360` renders).
* **tcolorbox (`theorem`, `intuitive`, `observation`, `example`, `conjecture`,
  …) — keeps them.** No change needed anywhere.

## 3. CONSEQUENCES

* **No book change is required.** Zero notes are invisible. Nothing to repair.
* **`e9eaaa6a`'s ch21 repairs stand**: the ratio correction, the false inequality
  in the proof, the block repair of the intuitive box, and the recorded φ
  collision were each verified independently of this question, and all six of
  their note fragments were confirmed rendering.
* Placing those notes in running text after `\end{...}` remains harmless — body
  text is always safe — but it was not necessary, and the reason given for it in
  the commit message was wrong.
* The false claim never entered the manuscript or `codex/`; it exists only in
  that one commit message, which is why this file exists.

## 4. THE STANDING LESSON

I asserted a defect class from a detector I had not validated, then repeated it
in a commit message as a measurement. The guard against this already existed in
my own notes — *"a passing check can be blind to your error; compute verdicts
from residuals, never print them as strings"* — and the correct discipline here
is the one the tabular finding used by accident: **change exactly one thing,
rebuild, and compare the identical string.** Anything weaker is a hypothesis,
not a measurement, and must not be written down as one.
