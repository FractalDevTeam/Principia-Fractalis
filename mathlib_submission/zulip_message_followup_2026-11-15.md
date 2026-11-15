# Zulip message draft (for Pablo to post)

**Thread:** `#Is there code for X? > Fermat right triangle theorem`
**URL:** `https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Fermat.20right.20triangle.20theorem/`
**Context:** @wwylele cited this thread in their comment on PR #46025.  We closed the PR and are regrouping per their suggestion.

---

## Message to post

> Following the review of PR #46025 (closed): @wwylele, thank you for the pointer to this thread.  Rather than resubmitting the large difference-form PR, I'd like to ask for placement guidance on a smaller first contribution.
>
> I have a self-contained Lean 4 proof of the **Fermat right triangle theorem** in the form
>
> ```
> theorem fermat42Double_impossible :
>   ∀ a s t : ℤ, s ≠ 0 → t ≠ 0 → s^2 ≠ t^2 → IsCoprime s t →
>     2 * a^2 ≠ s^4 + t^4
> ```
>
> This is the equation that arises as the auxiliary descent in Fermat's own proof of the n = 4 case, and it is equivalent to the classical "no Pythagorean triangle has square area."  Proof is a full Fermat infinite descent (Pythagorean classification → UFD square splits → quadruple extraction → key relation `4abcd = (c² - b²)(2a² - d²)` → smaller-equation extraction → size bound `|e| ≤ k² < a` → strong induction).
>
> **Three questions for placement:**
>
> 1. Is this content welcome in mathlib at all, or should it live downstream?  The maintainer concern cited earlier in this thread is what I'd like clarified first.
>
> 2. If welcome: location preference?  Options as I see them —
>    - Additions to `Mathlib/NumberTheory/FLT/Four.lean` (where mathlib's existing `Fermat42` and `not_fermat_42` sum-form live).
>    - New file `Mathlib/NumberTheory/FLT/FourDouble.lean`.
>    - Somewhere else entirely (e.g., as a corollary file under `Mathlib/NumberTheory/Pythagoras/` if the right-triangle-area phrasing is preferred).
>
> 3. Would a bundled corollary `fermat_right_triangle_theorem` phrased in the right-triangle-area form be useful alongside the Fermat42Double impossibility, or just the impossibility?
>
> **Disclosure up front:** my previous PR used AI assistance (Claude Opus 4.7) during CI iteration, and the file structure showed it in ways that drew the "complete AI slop" and `LLM-generated` label on #46025.  Fair call.  For this follow-up I will rewrite the proof body in a mathlib-idiomatic style before submission — no file-level linter disables, no star emphasis in docstrings, factored into clean lemmas, < 1000 lines target.  The mathematics is classical Fermat descent (1659 / Euler 1770); the issue on #46025 was presentation, not content.
>
> Happy to prepare the PR against whichever location the maintainers prefer, or to drop the mathlib submission entirely if the answer to (1) is no and keep the content downstream in the Principia Fractalis companion.

---

## Why this phrasing

- **Starts by thanking @wwylele** and references them by name. They are the constructive reviewer; acknowledging that is cheap and earns good will.
- **Asks placement question before submitting.** This is exactly what @wwylele suggested and what the maintainer-cited Zulip thread predates.
- **One paragraph of mathematical content, no more.** Enough to show this is a real thing; not enough to look like asking for pre-review.
- **Three concrete options with one-line descriptions each.** Gives the maintainers a chance to pick rather than argue.
- **AI-assistance disclosure up front, in the middle of the message.** Not buried; not the opening either (so it doesn't dominate the signal).  Explicit about what the fix is (presentation, not content).
- **Offers to drop mathlib submission entirely** if the answer is no.  This signals that you're not going to argue about placement; you want a clean answer.

## Post as yourself (`DrDMT-VR`)

The message is written in first person.  Post from Pablo's Zulip account.

## After posting

Wait for a reply from a mathlib maintainer or active reviewer.  Expected turnaround: 1–7 days.  If no reply in 7 days: a short ping is reasonable.

If the reply is "yes, go ahead at location X" → prepare PR A at that location.
If the reply is "not sure, propose at X and we'll see" → prepare PR A at X.
If the reply is "no, don't put this in mathlib" → close out the mathlib submission path for this content.  No further action required.
