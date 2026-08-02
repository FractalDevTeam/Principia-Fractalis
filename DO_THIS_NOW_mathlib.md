# Two admin tasks — exact steps

Nothing here needs judgment. Copy, paste, done. ~10 minutes total.

---

## TASK 1 — Add the AI-disclosure line to three PRs

Three pull requests need one sentence added to their **description** (the big
text box at the top of the PR, not a comment).

### The text to paste — identical for all three

```
Parts of this contribution were developed with AI assistance (Claude). All statements are machine-checked by the Lean kernel; `#print axioms` on the new declarations reports only `[propext, Classical.choice, Quot.sound]`.
```

### Where to put it

Paste it as the **last paragraph** of the existing description. Do not delete
anything that is already there.

### The three PRs, in order

| # | Link | Done? |
|---|---|---|
| 1 | https://github.com/leanprover-community/mathlib4/pull/42095 | ☐ |
| 2 | https://github.com/leanprover-community/mathlib4/pull/42100 | ☐ |
| 3 | https://github.com/leanprover-community/mathlib4/pull/42101 | ☐ |

### The clicks, for one PR

1. Open the link.
2. Just under the PR title, find the first box — that is the description.
3. Top-right of that box: the `···` button → **Edit**.
4. Scroll to the bottom of the text, press Enter twice, paste the line.
5. Green **Update comment** button.
6. Tick the box above. Repeat for the next link.

**#42093 is already done** — grunweg added it for you. Don't touch it.

### If someone asks a follow-up

You are on solid ground; the disclosure trail predates the question:

- both papers state the AI collaboration in their Acknowledgements
- every Lean file header says `Author: Pablo Cohen + Claude`
- every git commit carries a `Co-Authored-By: Claude Opus 5` trailer

And the `Authors:` line inside mathlib files stays **humans only** — that is the
convention grunweg confirmed on #42093. Disclosure goes in the PR description.
The two are separate things.

---

## TASK 2 — One Zulip message about where PR-6 should live

**Why:** `TateLimit.lean` is ready but it fits neither "linear algebra" nor
"number theory" cleanly. Guessing wrong wastes a reviewer's time. One question
first is the polite and faster route.

### Where to post

1. Go to https://leanprover.zulipchat.com
2. Left sidebar → stream **`#mathlib4`**
3. Click **New topic** (or the pencil / "Start new conversation")
4. **Topic name:** `Tate's telescoping limit — placement?`
5. Paste the message below into the body, press Enter to send.

### The message

```
I have a small self-contained file I'd like to upstream, and I'd rather ask about placement before opening a PR.

The statement: for a self-map `T : α → α`, a function `f : α → ℝ`, and `d > 1` satisfying `|f (T x) - d * f x| ≤ C` for all `x`, the rescaled iterates `f (T^[n] x) / d ^ n` converge — and the limit is the unique function that is exactly homogeneous (`g (T x) = d * g x`) while staying a bounded distance from `f`.

`α` carries no structure at all. This is Tate's telescoping argument (Silverman, *Arithmetic of Elliptic Curves* VIII.9.3 and the lemma preceding it) in the generality it actually has. The Néron–Tate canonical height is the special case `T = (· + ·)`, `f = log ∘ (naive height)`, `d = 4`.

Declarations: `tateSeq`, `tateLimit`, `tendsto_tateLimit`, `tateLimit_comp_self`, `tateLimit_iterate`, `abs_tateLimit_sub_le`, `abs_tateLimit_sub_iterate_le`, and `eq_of_comp_self_of_abs_sub_le` (uniqueness).

It imports only `Mathlib.Analysis.SpecificLimits.Basic` and `Mathlib.Order.Filter.AtTopBot.Basic`, and its two workhorses are `cauchySeq_of_le_geometric` and `dist_le_of_le_geometric_of_tendsto₀`. That makes `Mathlib/Analysis/SpecificLimits/` feel natural, but it is arguably a dynamics statement (`Mathlib/Dynamics/`). Which would reviewers prefer?

Naming suggestions also welcome — `tateLimit` may be too number-theory-flavoured for a file containing no number theory.

For context on why I want this: mathlib currently has no canonical/Néron–Tate height at all (grep for "canonical height", "Néron-Tate", "NeronTate" returns nothing), and this is the analytic core such a development would sit on.

(Per the AI policy: parts of this were developed with AI assistance (Claude). Everything is kernel-checked; `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`.)
```

### What happens next

Someone will reply with a preferred directory, usually within a day. Tell me
what they say and I'll write the PR to match. **Do not open the PR before the
reply** — that's the whole point of asking.

---

## What you are NOT being asked to do

- Nothing about r174–r177. Those are committed and pushed.
- No decision about PR-5 (`GramLinearIndependent.lean`) — it has an obvious home
  and can be opened whenever; it is not blocked on anything.
