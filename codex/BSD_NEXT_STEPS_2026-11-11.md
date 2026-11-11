# BSD lane — next steps after step 2 completion and Ch24 discovery

**Date:** 2026-11-11.
**Author:** Pablo Cohen.
**Head at write time:** `c6bb035d` on `master`.

## Status

All four Rio-audit items from `BSD_SCOPING_UPPER_BOUND_IS_THE_GAP_2026-10-17.md` are either done or pending as pure cleanup:

| Rio step | state |
|---|---|
| 1 — Retire/repoint 8 redundant Heegner mirrors | pending (near-zero cost cleanup) |
| 2 — Instantiate `rank ≥ 1` on E_91a1 / E_102a1 / E_131a1 / E_141a1 | **DONE** 2026-11-11 |
| 3 — First rank UPPER bound via 2-descent | **DONE** 2026-10-17 (`Ch24Descent2TorsionRatBridge_2026_10_17`) |
| 4 — Combine 2 + 3 → first exact rank in the repo | **DONE** 2026-10-17 (same file — rank = 0 for E : y² = x³ + x) |

The scoping doc has been corrected in-place to reflect this.

## Why we're writing a new doc

Asked today ("now step 3") to work on the first rank upper bound, I nearly re-attempted something that already existed. This doc exists so the next session has a concrete list of tasks that are actually still open.

## Next targets, in order of tractability

### A. Second rank-0 curve via Fermat descent — real work, bounded

**Target:** `Module.rank ℤ E'(ℚ) = 0` for some second curve `E'`, same technique.

**Natural candidate:** E' : y² = x³ − x (= x(x − 1)(x + 1), the n = 1 congruent number curve, LMFDB 32.a2, full rational 2-torsion). Classical Fermat descent.

**Obstruction (why it's not a one-session job).** Ch24's descent reduces to mathlib's `not_fermat_42` (sum form `a⁴ + b⁴ ≠ c²`). For y² = x³ − x, the descent reduces to the DIFFERENCE Fermat `a⁴ − b⁴ ≠ c²`, which is NOT in mathlib as a named lemma. Need to prove it.

**Rough plan for `not_fermat_42_sub`:**

1. Define `Fermat42Sub a b c : Prop := a ≠ 0 ∧ b ≠ 0 ∧ a⁴ − b⁴ = c²` (mirroring mathlib's `Fermat42`).
2. Define `MinimalSub` — a minimal counterexample by `a²`.
3. Classical descent via mathlib's `PythagoreanTriples.coprime_classification'`:
   - From `a⁴ − b⁴ = c²` derive `(b²)² + c² = (a²)²`.
   - Primitive Pythagorean triple (b², c, a²) classified by (m, n).
   - Case split on which leg is even.
   - Case where c even, b odd: `b² = m² − n²` forces `m − n = s²`, `m + n = t²`; `a² = m² + n²` → Pythagorean triple → classified by (j, k) → derive equation `t² + s² = 2a²` or similar — needs further descent.
   - Case where b even, c odd: `b² = 2mn` with m, n coprime, one even ⇒ `mn` a square after halving ⇒ m, n squares → `a² = m² + n² = p⁴ + 4q⁴` → `(a − p²)(a + p²) = (2q²)²` → gcd-2 splitting → `p² = v − u = f⁴ − e⁴`. **New instance of `Fermat42Sub` with f < a.** Descent.
4. Combine cases → the minimal counterexample doesn't exist → `not_fermat_42_sub`.

**Estimated size:** 150–300 lines Lean. Day-long focused session.

**Deliverable:** one new file `FermatDescentSub_2026_MM_DD.lean` + one capstone `Ch32Descent2TorsionRatBridge_2026_MM_DD.lean` (name parallels Ch24). Capstone delivers `Module.rank ℤ E'(ℚ) = 0` for E' : y² = x³ − x, on three-axiom bar.

### B. Rank EXACTLY 1 — the real multi-week project

**Target:** `Module.rank ℤ E''(ℚ) = 1` for some curve `E''` with rational 2-torsion. **"First exact rank 1 in the repo."**

**Candidate curve.** E'' : y² = x³ − 25x (congruent number n = 5). Full rational 2-torsion {O, (0, 0), (5, 0), (−5, 0)}. LMFDB label 80.b2 or 80.a2 (needs confirmation). Classical rank 1.

**Rank ≥ 1 direction (mechanical, follows the gap-curve pattern).**

Non-torsion generator: P = (−4, 6). Verified on curve: (−4)³ − 25·(−4) = −64 + 100 = 36 = 6². ✓

Orbit under duplication (computed offline, verified before formalizing):
* `xs 0 = −4`
* `xs 1 = 1681/144`
* `xs 2 = 11183412793921 / 2234116132416`  (14-digit / 13-digit)
* `xs 3 ≈ 6.24 × 10⁵²` (53-digit num / 52-digit den)
* `xs 4 ≈ 1.52 × 10²¹³`

CL (universal curve constant at b-invariants (0, −50, 0, −625)) = **144,750,000,000,000** (~1.45 × 10¹⁴).

**Threshold:** `h(xs n) > κ` first at n = 3 (because h(xs 2) ≈ 1.1 × 10¹³ < CL < 6.2 × 10⁵² ≈ h(xs 3)). So shift = 3.

**Concern:** xs 3 has a 53-digit numerator and denominator. `norm_num` in Lean has to verify
`xs 3 = (53-digit number) / (52-digit number)` and that fraction is reduced. This may be slow but should succeed — Ch24 and the gap curves verified 15-digit numerators without issue; 53 digits is 3× larger and may compile but take tens of seconds per rewrite rather than milliseconds.

**Pattern.** Full rational 2-torsion means the curve-wide h2tor fails (same situation as E_102a1). The E_102a1 per-point route applies, specialised to the three rational 2-torsion points {O, (0, 0), (5, 0), (−5, 0)}. Lemma needed: `x(R) ∉ {0, 5, -5} ⟹ 2R ≠ 0`.

**Rank ≤ 1 direction — the real gap.** Needs a 2-descent via isogeny for a curve with full rational 2-torsion. Specifically:

* Descent map `E(ℚ)/2E(ℚ) → (ℚ*/(ℚ*)²)³ with product = 1`.
* Local conditions at primes 2, 5, ∞.
* Computation that the image has size 4 (giving dim F₂ = 2, so `2·rank + dim(E[2]) = dim(image) = 2 + 2 = 4`, giving rank = 1).

**This is the honest "weeks of work."** It requires building the entire descent-map and local-at-prime infrastructure that's not in mathlib. Partial progress towards this could happen incrementally — each lemma individually bounded — but there's no shortcut.

### C. Mordell-Weil statement in Lean (for Ecurve)

Ch24 delivers `Module.rank ℤ Ecurve.toAffine.Point = 0`. From this alone we can't conclude `E(ℚ)` is FINITE as a group, because Mordell-Weil (finitely-generated-ness) isn't assumed anywhere.

In the SPECIFIC case of Ch24, `solutions_are_origin` shows E(ℚ) = {O, (0, 0)} as a 2-element group, so `Fintype E(ℚ)` would follow by hand. But a general `Module.rank = 0 → Finite` for E(ℚ) needs the Mordell-Weil theorem for mathlib's `WeierstrassCurve` — not currently present.

Minor project: write a `Fintype` instance for Ecurve.toAffine.Point explicitly, or at least state the equality `(Set.univ : Set Ecurve.toAffine.Point) = {0, Point.some P0_nonsingular}` and derive finiteness.

### D. Retire/repoint the 8 redundant Heegner mirrors (Rio step 1)

Per the scoping doc, 8 of 12 Heegner-mirror files (for 43a1, 53a1, 61a1, 79a1, 83a1, 89a1, 101a1, 106a1) assert `∃ cert, cert.r = 1` for curves that have a stronger, genuine `1 ≤ Module.rank` theorem elsewhere. Repoint or retire them. Near-zero cost, benefit is that the lane stops looking Prop-level when it isn't.

## Priority ranking

1. **D (Heegner mirror cleanup)** — fastest, lowest risk, pure bookkeeping.
2. **A (second rank-0 curve)** — day-long, bounded, delivers a new theorem of the same kind as Ch24.
3. **C (Fintype instance for Ecurve)** — few hours, delivers finiteness of E(ℚ) for the specific Ch24 curve.
4. **B.rank≥1 (rank ≥ 1 for y² = x³ − 25x)** — multi-day because of 53-digit norm_num and per-point 2-torsion handling, but mechanically parallel to the gap curves.
5. **B.rank≤1 (rank ≤ 1 for same curve)** — multi-week, the honest "real project."

## Open questions for future sessions

* Should B.rank≥1 be attempted even without B.rank≤1? Produces an additional lower-bound capstone but no exact rank. Possibly worth it to move the Lean build order along.
* Is the Fermat-sub descent (A) worth the day it takes? Delivers a second instance of the Ch24 technique, broadening the "rank upper bound" story from 1 curve to 2. Arguably yes.
* Is there a congruent number curve with smaller orbit numbers for B.rank≥1? Larger n gives larger CL. Smaller n: n = 1 is y² = x³ − x, rank 0 (not useful). n = 2, 3, 4 not congruent (rank 0). n = 5 is the smallest congruent rank-1 example, which is what we scoped.
