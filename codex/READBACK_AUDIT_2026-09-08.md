# STATEMENT READ-BACK AUDIT — FIRST RUN

**Date:** 2026-09-08. Gate: `codex/RELEASE_GATE_r331b.md` §H (added today).
**Method:** `codex/FLT_LESSONS_FOR_PF_2026-09-08.md` §6 — an independent reader
renders the Lean into prose **without having seen the intended meaning**, then
the two are diffed.

Five statements audited. Each auditor received the declaration text and the
definitions needed to unfold it — **no docstrings, no comments, no surrounding
prose, no statement of intent**.

---

## VERDICT SUMMARY

| # | statement | read-back vs intent | outcome |
|---|---|---|---|
| S1 | `xi_T15_zero_count_identity_unconditional` | **matches** | naming flags only |
| S2 | `top15_re_lt_neg_1e4` | **matches** | one real naming defect |
| S3 | `re_xi_lower_bound_from_edge` (r331c) | matches — **but a vacuity hole found** | **DEFECT FIXED** |
| S4 | r332 obstruction theorems | **matches the type, challenges the framing** | **substantive; see §4** |
| S5 | `alpha_skeleton_unique` (r128) | **matches, independently reproduced** | confirmation + 2 new facts |

**No statement was found to mean something other than we believed.** The base
rate quoted in the FLT lessons (~43% faithful) did not manifest here. That is a
real result and worth stating: our statements are, so far, faithful.

**But the audit paid for itself anyway**, on S3 and S4.

---

## §1 — S1, the endpoint

Read-back rendered it correctly as the argument principle for ξ on the rectangle:
`(1/2πi)∮ ξ'/ξ = Σ ord_ρ(ξ)`. Matches intent.

**Checked and resolved:**

- *"`boundary_zero_free_of_top_right_half` is applied pointwise at `z15`, so it
  may be nonvanishing at one corner rather than on the border."* — **Resolved.**
  The lemma's real signature is
  `(hTop : ∀ σ, 1/2 ≤ σ → σ ≤ 1 → riemannXiEntire ⟨σ,15⟩ ≠ 0) : ∀ s ∈ RectangleBorder z15 w15, riemannXiEntire s ≠ 0`
  — border-wide. The call site instantiates it; the lemma is not weakened.
- *Degenerate-rectangle vacuity.* — **Closed.** `z15 = ⟨0,0⟩`, `w15 = ⟨1,15⟩`;
  the rectangle is `[0,1] × [0,15]`, non-degenerate.
- *"`unconditional` is not asserted by the type."* — Correct as a statement about
  the *text*. It is established by evidence we hold outside the text:
  `#check @` returns a type with **no binders at all** (recorded 2026-09-05), and
  `#print axioms` gives exactly the mathlib three. The auditor's demand — "run
  `#check @` before the name is accepted" — is precisely our §B0 rule. Satisfied.

**Naming flags, recorded, not yet acted on:**

- `zero_count` — no numeral appears; it is a symbolic identity, not a count.
- `T15` — no numeric content in the type; `z15`/`w15` are opaque constants there.
- The source lemma is `..._exact_zero_count_identity_top_only`; the derived name
  drops both `exact` and `top_only`. **Renaming is not widening**, and dropping a
  scope qualifier is the exact erosion pattern §H exists to catch.

## §2 — S2, the union

Rendered correctly: for all σ ∈ [1/2, 1], `Re ξ(σ+15i) < −1/10000`.

**The one flag that mattered, checked immediately:** the auditor could not tell
which normalization `riemannXiEntire` uses, and warned that under bare
`Λ(s) = π^(−s/2)Γ(s/2)ζ(s)` the sign flips and **the statement would be false at
σ = 1/2**.

**Resolved.** `riemannXiEntire s := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2`
— the classical ξ. The failure mode does not apply. This was the single
highest-value check the audit produced, and it came from an auditor who was not
told what the function was.

**Real naming defect, unfixed:** `top15_re_lt_neg_1e4` — `1e4` reads as 10⁴; the
bound is 10⁻⁴. Off by eight orders in the name. Also `top15` is ambiguous with
Lean's `⊤`. Correct forms: `..._lt_neg_1em4`, or `t15`.

**Scope, correctly identified:** one horizontal segment at exactly `t = 15`, of
zero measure in `t`; implies non-vanishing on that segment only; says nothing
about RH, other heights, or σ ∉ [1/2,1]. This matches gate item F8 exactly.

## §3 — S3, r331c — **A REAL DEFECT, CAUGHT BEFORE PROOF WORK**

The statement is algebraically correct. The auditor independently derived, from
Mathlib's `completedRiemannZeta = completedRiemannZeta₀ - 1/s - 1/(1-s)` and
`ξ = ½s(s−1)Λ`, that the consumer is provable **iff**
`riemannXiEntire = (1 + s(s−1)Λ₀ s)/2` — and predicted that a missing `½` would
make it off by a factor of two and unsound wherever the bracket is negative.
**The definition matches to the symbol.** Independent confirmation that r331c's
staged shape is right.

**But:** `re_xi_lower_bound_from_edge` and `im_xi_lower_bound_from_edge` had
**no `t_lo ≤ t_hi` hypothesis**.

With `t_lo := 1, t_hi := 0`:

- every enclosure hypothesis is vacuously provable, for arbitrary bounds —
  including inconsistent ones;
- `h_arith` is vacuously provable for **arbitrary `m`**;
- the conclusion is vacuously true.

So the theorem was provable with `m = 10^100` while asserting nothing about ξ. In
the auditor's words: *"a downstream campaign could assemble a pile of green
certificates covering a total t-measure of zero. Nothing in this lemma detects
it."*

Not unsoundness — the theorem is true as stated. It is an **audit exposure**, and
it is exactly the kind that survives every gate we have: `#print axioms` would be
clean, the build green, the ledger full of CLOSED rows.

**FIXED.** `h_ne : t_lo ≤ t_hi` added to both consumers, with a docstring
recording why it is deliberately unused in the proofs. Conditions at time of fix:
module **not yet elaborated**, **zero consumers** — the cheapest possible moment.

**Also recorded:** `h_arith` is trivially satisfiable by taking `m` very
negative, so the lemma certifies nothing on its own; all real content is deferred
to the call site, which must produce a specific `m` **and show it positive**.
`Re ξ ≥ m` implies `ξ ≠ 0` only when `m > 0`, and `m > 0` is nowhere asserted.
That obligation must be tracked at the aggregation layer.

## §4 — S4, r332 — **the framing is challenged, and the challenge lands**

The type read back exactly as intended. The challenge is to what we said *about*
it, and it is substantive enough to act on.

The auditor's findings:

1. **ℤ ⊆ ℤ[1/3]** (take `k = 0`), so the set of ratios `{b/a}` is **exactly ℚ** —
   all of it. The theorem's content is therefore precisely **"π ∉ ℚ"**.
2. **The "3-ness" does no work.** Replace 3 with 2, 7, or drop the localization
   entirely and the proof is unchanged. Any argument leaning on the *triadic*
   character of the substrate is not supported by this theorem.
3. **It consumes irrationality rather than producing it.** `hx : Irrational x` is
   a hypothesis, so the theorem can never be the load-bearing step in showing a
   quantity is special.
4. **"Not equal to any element" ≠ "not constructible from".** ℤ[1/3] is dense in
   ℝ; π is a limit of such ratios. The theorem addresses a **single division** —
   not sums, series, roots, limits, or solutions of equations over ℤ[1/3].
5. **`ktheoretic` is unsupported by the text** — no ring, module, functor or `K₀`
   appears. If ℤ[1/3] arises as some `K₀(R)` elsewhere, that identification is
   not in these declarations and is not inherited by naming.
6. `h0 : a ≠ 0` is redundant — which we had already recorded as r332.F.

**What survives.** The canonical verdict sentence — *"L5 is impossible through
its formalized substrate-ratio channel"* — is precise and stands: it is scoped to
the ratio channel by construction. `no_ktheoretic_ratio_is_irrational` is
likewise exactly true.

**What must be corrected.** My surrounding commentary called this obstruction
"exhaustive" and treated it as closing derivability broadly. Per this audit the
honest statement is narrower:

> r332 establishes that π is not the quotient of two elements of ℤ[1/3] — i.e.
> that π is irrational, specialised to that subring. It closes **one operation,
> not a closure**. It does not address sums, series, limits, or any other route
> from substrate data to π, and its force does not depend on the substrate being
> base-3.

The **conclusion** is unchanged: the α-values are not derived, and L5 has no
intrinsic derivation in the corpus. The **reason** is thinner than I stated, and
the ledger and canonical language should say so.

## §5 — S5, r128 — independent confirmation

The auditor, seeing only the Lean, reproduced the r334/r335 findings unprompted:
triangular system, nine equations for nine unknowns, **zero redundancy**
("nothing here could have failed"), positivity as tie-breaker for exactly the
three quadratics (Hodge, P, QG), and — verbatim — that **"no free parameters" is
false as stated**, the parameters having been *relocated into the equations*,
count conserved.

That is a blind reproduction of the audit we spent a day on. It is the strongest
evidence available that the α-verdict is right.

**One false alarm, and it was mine.** The auditor flagged that no existence lemma
appears, so the theorem could be vacuous if the equations were inconsistent. The
corpus **does** have them — `canonical_isPositive`, `canonical_satisfiesStructural`,
`canonical_satisfiesLaws`, `alpha_skeleton_exists_unique`. They were absent from
the extract I supplied. **Extraction error on my part, not a corpus gap** —
recorded because it is a lesson about running this gate: the extract must include
the existence side, or the auditor will correctly flag a hole that is not there.

**Two new facts we did not have:**

- **Six of the nine positivity hypotheses are redundant** — only `pos_Hodge`,
  `pos_P`, `pos_QG` do work (the three quadratics). The other six follow with
  determined sign.
- **Four fields are terminal leaves** — `aNP`, `aBSD`, `aQG`, `aP` each appear in
  exactly one equation. They are pure definitions, constrained by nothing;
  changing that one equation moves the value with no effect elsewhere.

---

## WHAT THIS RUN COST AND RETURNED

Five auditors, ~5 minutes wall-clock, no build resources.

Returned: one real pre-proof defect fixed at zero cost (S3), one framing
correction that would otherwise have reached publication (S4), two new structural
facts (S5), one normalization risk closed (S2), and independent confirmation that
four of five statements say what we believed.

**The FLT lessons' claim that statement review is the best-ROI activity available
is supported by this run.** Recommend it become routine at statement-freeze, per
§H, not an occasional exercise.

---

*First run of gate §H. Public HEAD `96c71da7`. NO PUSH.*
