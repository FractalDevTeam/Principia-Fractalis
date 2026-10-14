# Private briefing — #42093 and j-loreaux's design hesitation

**Date:** 2026-10-14
**Audience:** Pablo only. Not posted upstream.
**Purpose:** Context for your reply to j-loreaux's review-level comment on #42093.

## j-loreaux's exact comment on #42093 (2026-09-01, review-level, not inline)

> This is of course fairly straightforward. I'm willing to add it, but I'm
> slightly reluctant because I am still conflicted about the correct long term
> solution. At one point I thought it would be to pursue `TwoSidedIdeal`, but I
> have been somewhat convinced that it is rather to generalize `Ideal` and
> `Submodule` to the currently non-existent `NonUnitalModule` (name TBD).

The seven inline review comments were mechanical (`_root_.` cleanup, extract
MapsTo lemmas, `@[gcongr]`, `isClosed_closure` instance, `IsOpenUnits` typeclass)
— all seven are addressed in commit `fd87d70e48` (pushed earlier today).

This review-level comment is the deeper one. It isn't about the seven fixes.
It's about **whether `TwoSidedIdeal.closure` should exist as a stand-alone
first-class construction, or whether it should be a specialization of a more
general `NonUnitalModule`-level closure**.

## The two paths j-loreaux is weighing

### Path 1 — develop `TwoSidedIdeal.closure` as a stand-alone API

What your PR does. There's a `TwoSidedIdeal R` type for a two-sided ideal of
a (possibly non-unital, possibly non-associative) ring, and `TwoSidedIdeal.closure`
is a construction `TwoSidedIdeal R → TwoSidedIdeal R` that takes an ideal to
the two-sided ideal spanned by its topological closure.

**Pro:** immediate, concrete, mirrors the existing `Ideal.closure`
(`Mathlib.Topology.Algebra.Ring.Ideal`) which does the same for one-sided
ideals of unital rings.

**Con:** adds another closure-of-X API to mathlib that will have to be kept in
sync with every related closure (ideals, submodules, subalgebras, Lie
submodules, etc.) when the underlying topology/algebra story evolves.

### Path 2 — generalize `Ideal` + `Submodule` to a hypothetical `NonUnitalModule`

Right now `Submodule R M` requires `R` to be a (unital) semiring and `M` an
(unital) `Module R`. There's no "`NonUnitalSubmodule`" or "`NonUnitalModule`"
class in mathlib. If one existed, both `Ideal` and `TwoSidedIdeal` could be
realized as `NonUnitalSubmodule`s of the ring acting on itself in different
scalar directions, and `closure` on them would come from a single
`NonUnitalSubmodule.closure` construction.

**Pro:** one closure API, used by one-sided ideals, two-sided ideals, non-unital
subalgebras, non-unital Lie structures, etc. No synchronization cost later.

**Con:** `NonUnitalModule` doesn't exist. Introducing it means designing the
typeclass hierarchy (scalar action without unit, module laws without unit),
threading it through hundreds of existing `Submodule` lemmas, and committing
mathlib to that story.

### Why j-loreaux is conflicted

He writes "I'm willing to add it" — meaning: Path 1 (your PR) is accepted
provisionally. The "but" is: **if the mathlib community commits to Path 2 in
the next year, your `TwoSidedIdeal.closure` becomes a legacy specialization
that someone will have to port and remove.** He's a careful library author
and he doesn't want to say yes to work that will be undone.

He hasn't been convinced of Path 2 yet (he says "somewhat convinced") — which
means he hasn't yet decided to BLOCK Path 1. The reluctance is personal
discomfort, not refusal.

## What a response needs to do (strategic — your words, your choice)

j-loreaux is not asking for a design proposal from you. He's registering a
hesitation. A good response from you addresses **his** uncertainty, not the
seven inline fixes (those are done in code).

Three things that could be said:

1. **Acknowledge the design question is real** and that you understand `NonUnitalModule` would subsume this. Don't argue the design — just signal
   you've heard it.

2. **Make the case for the specialization being useful right now**, if you
   want to. The honest case: `Ideal.closure` already exists for the unital
   one-sided case; this PR extends to the non-unital two-sided case; mathlib
   today uses `TwoSidedIdeal` directly in several places (C*-algebra ideals,
   non-unital CFC, your other PRs #42095/#42100) — so having
   `TwoSidedIdeal.closure` as a concrete lemma is immediately useful to those
   downstream contributors. If Path 2 lands later, this becomes a one-line
   `.closure = NonUnitalSubmodule.closure` lemma that stays correct.

3. **Offer the collaborative move**: if j-loreaux (or anyone) wants to begin
   `NonUnitalModule`, you can port this file to be a thin wrapper when that
   lands. The current PR doesn't block that future; it just lands useful
   closure API in the shape mathlib currently has.

**What NOT to say**: don't argue Path 2 is wrong. j-loreaux might actually be
right about the long term — ring/module unification is a long-standing mathlib
design direction. Don't take sides on his open question. Just make the case
that your narrow PR is useful today AND compatible with his future direction.

## Where your situation fits the maintainer flag context

The felixpernegger flag on #42100 (AI-authored comments) is a separate thread.
j-loreaux has not raised AI concerns on #42093 — his comments are purely
technical. The code push (`fd87d70e48`) is your authorship (git author line
`XLUXX <psolorzano@gmail.com>`, no Co-Authored-By).

What j-loreaux's note is NOT:
- Not an AI-involvement flag.
- Not a quality concern on the code.
- Not a "close this" signal.

What it IS:
- A design hesitation about the long-term API shape.
- A soft "I'd rather not" that could become a soft "ok, land it" with a few
  sentences from you clarifying the specialization-is-useful case.

## Reference to past mathlib conversations on this

Not surfaced in this PR, but the `NonUnitalModule` design discussion is live
on Zulip (`#maths > NonUnitalModule`, intermittent since 2024). j-loreaux is
a participant there. If you want to signal awareness without wading into the
Zulip thread yourself, mentioning the existence of that direction suffices.

## My honest read, offered as background only

j-loreaux's hesitation is addressable. The code is cleaner now; the design
objection is soft; your PRs #42095 and #42100 already consume this
`TwoSidedIdeal` API, so your own ecosystem benefits from the specialization
landing. A short, careful reply from you — in your voice — making the
"useful specialization now, portable to NonUnitalModule later" case has
good odds of flipping his "slightly reluctant" to "ok let's merge."

The call is yours. Short, human, no defensiveness — same shape as your
felixpernegger follow-up.
