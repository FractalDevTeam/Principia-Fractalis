# `Prop := True` audit — 2026-08-01

**Found by:** re-reading the corpus top-down after Pablo pointed out that the
chapters form one architecture and that I had been auditing atoms.
**Author of the defect:** me. These files are mine.

---

## 0. The headline

`PF/Wave56CrossMillenniumMasterCascade.lean` is the framework's top-level
cross-Millennium theorem. Its conclusion,
`FrameworkInternalCrossMillenniumCascadeConclusionConditional`, is a six-fold
conjunction. **Five of the six conjuncts are `True`:**

```
RHWave56ShortestChain        : Prop := True
NSWave56UniformBilinearBound : Prop := True
HodgeCYCodim2Chain           : Prop := True
BSDTypedRankZeroChain        : Prop := True
YMContinuumLiftChain         : Prop := True
```

So `Wave56_cross_millennium_master_cascade_conditional` proves

```
LHS  →  (R1 ∧ True ∧ True ∧ True ∧ True ∧ True)
```

Only R1 carries content, and R1 is itself behind two unproved hypotheses
(`IBMHardwarePeaksMatchAlphaCanonicalPair`, `WaveCorrespondenceGaloisOrbitMembership`).

The docstrings are honest — each says "placeholder for a Wave 56 sibling-agent
…". The **theorem name and the capstone framing are not**. A reader who greps
for the capstone and not for the definitions will conclude something false.

## 1. Scale

| | count |
|---|---|
| `def … : Prop := True` corpus-wide | **402** |
| …of those, inside the verified `lake build PF` | **338** |
| `: True := trivial` marker theorems, corpus-wide | 675 |

Among the 402 are definitions whose names assert results:
`BSDThreeRankProven`, `BSDFourRankConcordanceProven`,
`BSDRankSixUniversalConcordanceProven`, `BSDRankBlindUniversalProven`,
`CrossMillenniumImplicationChainsProven`, `ConsciousnessRHWave35FivepointProven`.
**A name ending in `Proven` on a `Prop := True` is the worst case**, because it
survives casual inspection.

## 2. Why the axiom discipline did not catch it

The governing rule has always been `#print axioms` = `[propext,
Classical.choice, Quot.sound]`, no `sorry`, no `native_decide`. **A `Prop :=
True` passes all of it.** `trivial` is a perfectly good proof of `True`. The
discipline was built to catch unsound proofs; this is a *vacuous statement*,
which is a different failure and invisible to the same check.

This is the same defect already logged for the F1–F8 falsifiability registry
(task #40, "do not cite F1–F8 as kernel-verified falsifiability anywhere").
It is not confined to F1–F8. It is 338 declarations inside the build.

## 3. What is NOT affected

Verified by inspection of the import graph — these owe nothing to any `True`
Prop:

* the Glimm/UHF arc (r102–r113): faithful trace, simplicity of `T∞`, uniqueness
  of the tracial state;
* the Mordell–Weil arc (r143–r181): rank ≥ 2 for 389a1, rank ≥ 3 for 5077a1,
  the general Gram criterion, the universal canonical height;
* the Hardy/RH atom r120;
* both mathlib candidates.

These are real theorems with real content. The `True` problem is concentrated in
the *cross-Millennium cascade and capstone layer*, i.e. exactly the layer that
makes the largest-sounding claims.

## 4. First repair — done

`PF/BSDRankChainReal_r182.lean`. `BSDRankChainReal` is a four-clause conjunction
with no `True` in it:

1. `2 ≤ Module.rank ℤ E389a1(ℚ)` (r154)
2. `3 ≤ Module.rank ℤ E5077a1(ℚ)` (r169)
3. the general Gram criterion, for any abelian group and any `n` (r170)
4. the canonical-height doubling law for 389a1, from the coefficients alone
   (universal chain r174–r180)

plus `clause_three_is_inhabited`, so clause 3 is demonstrably not vacuous.
Kernel-clean. `BSDTypedRankZeroChain` is left in place; this stands beside it.

## 5. What remains

Four more Wave-56 conjuncts (RH, NS, Hodge, YM) and 334 further `True` Props in
the build. They fall into three classes and need different treatment:

* **literature anchors** (`Cook1971_NPCompletenessSAT_Anchor`, …) — these are
  citations, not claims. Honest fix: rename to `…_Citation` and stop conjoining
  them into capstones as if they were content.
* **placeholders for unfinished work** (the five cascade conjuncts) — either
  give them content, as r182 does for BSD, or remove them from the capstone
  conjunction so the capstone states what it actually proves.
* **markers** (`…_axiom_free : True := trivial`) — replace with a real statement
  or delete; a marker that proves nothing is worse than no marker.

**Until that sweep is done, no capstone or cascade theorem should be cited as
evidence for anything.** The per-arc results in §3 can be cited freely.
