# Edge-sign neighborhoods — generic infrastructure for R1/R2/R3, 2026-10-13

Author: Pablo Cohen + Claude Opus 4.7 (1M context). Session restarted on
linux-server after a two-day Legion-on-Acer gap; mathlib-PR back-and-forth
deferred by Pabs to clear context for research.

## What landed

`PF/Analytic/EdgeSignNeighborhoods_2026_10_13.lean` (284 L). Generic
continuity-based neighborhood infrastructure plus specialisations to all three
right-edge sign segments. **16 kernel-clean theorems**, every one axiom-set
`[propext, Classical.choice, Quot.sound]`. Zero project axioms. No `sorry`,
`native_decide`, `axiom`, or `Prop := True`. `autoImplicit` off. Additive.

## The pieces

**§0 Generic (6 lemmas, pure real analysis, zero numerics).** For
`f : ℝ → ℝ` continuous and a point sign at `t₀`, a positive-length closed
interval of that sign exists around `t₀`:

```
pos_neighborhood_both / right / left  :  0 < f t₀ → ∃ δ > 0, ∀ t ∈ Icc _ _, 0 < f t
neg_neighborhood_both / right / left  :  f t₀ < 0 → ∃ δ > 0, ∀ t ∈ Icc _ _, f t < 0
```

**§1 Specialisation.** `edgeIm t := Im ξ(1 + it)`, continuous (dual of Legion's
`continuous_edgeRe` with `Complex.continuous_im`).

**§2 Right-edge specialisations.** Seven one-line consequences:
`R1_right_of`, `R1_both_of`, `R2_both_of`, `R2_right_of`, `R2_left_of`,
`R3_left_of`, `R3_both_of`.
Each is CONDITIONAL on a point sign value — no numerics introduced.

**§3 Endpoint one-liner.** `R1_right_neighborhood_of_zero` restates Legion's
`R1Neighborhood20261009.R1_on_neighborhood` as a specialisation of the generic
lemma, confirming the infrastructure reproduces existing endpoint coverage.

## What this does NOT do (unchanged scope)

* **Does not close R1, R2, or R3.** Each still needs the whole closed segment:
  `[0, 13]`, `[13, 29/2]`, `[29/2, 15]`. The infrastructure only converts a point
  sign into a positive-length neighborhood of that point.
* **Does not supply any new point sign.** R1's point sign at `t = 0` and R3's
  point sign at `t = 15` already exist (`R1_at_zero_local`,
  `top15_re_lt_neg_1e4`). R2's two endpoint signs — at `t = 13` and `t = 29/2` —
  do not. The latter still require a numerical quadrature producer, which this
  file does not provide.
* **Does not touch the open Riemann Hypothesis.** `riemannHypothesis_below_15`
  is RH on one finite rectangle, classically known since Riemann and Gram.

## What it unblocks

* R3 left-neighborhood of `t = 15`: fires immediately in any file that imports
  both this one and `RiemannXiTopUnion` (deliberately kept out of this file to
  avoid pulling in TopUnion's stale olean; see §3 of the Lean file).
* R2 right-neighborhood of `t = 13` and left-neighborhood of `t = 29/2`: fires
  the moment a point certificate `0 < Im ξ(1 + 13i)` or `0 < Im ξ(1 + 14.5i)`
  lands. These were previously the only R2 covering of any kind.
* Chaining via `RightEdgeSignsProof_2026_10_09.forall_Icc_cover`: once an
  interior point value lands anywhere in `[0, 13]`, `[13, 29/2]`, or
  `[29/2, 15]`, this file produces a positive-length cover piece around it,
  reducing the length of the remaining open segment that the certified
  producer must still handle.

## Build method

Legion's taskset-isolated single-file compile method (see
`RH_BELOW15_FULLY_WIRED_2026-10-10.md` §Infrastructure):

```
taskset -c 0,1 lake env lean \
  -o .lake/build/lib/lean/PF/Analytic/R1Neighborhood_2026_10_09.olean \
  PF/Analytic/R1Neighborhood_2026_10_09.lean       # 13.4 s

taskset -c 0,1 lake env lean \
  -o .lake/build/lib/lean/PF/Analytic/EdgeSignNeighborhoods_2026_10_13.olean \
  PF/Analytic/EdgeSignNeighborhoods_2026_10_13.lean # 18.6 s
```

Zero dependency cascade. Load never exceeded ~1.0. The 4,241-panel OOM trap
(`RiemannXiTopUnion` stale, risks rebuild) is avoided by not importing TopUnion
in this file — see Lean §3.

## Where this sits in the dependency graph

Chain to `rh_below_15_conditional` (Rank 1 of
`GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-09-29.md`):

```
    R1_at_zero_local                  (R1Neighborhood_2026_10_09, Legion 10-09)
          │
          ▼
  R1_on_neighborhood                  (R1Neighborhood_2026_10_09, Legion 10-09)
          │   ≡
    R1_right_neighborhood_of_zero     (this file, 10-13)   ◄── one-line via generic lemma
          │
          ▼
    forall_Icc_cover                  (RightEdgeSignsProof_2026_10_09, Legion 10-09)
          │ + R1_box / R2_box / R3_box
          ▼
    R1 ∧ R2 ∧ R3                       (open — needs t-boxed interval producer)
          │
          ▼
  rh_below_15_conditional             (CAPSTONE, Legion 10-10)
```

The remaining open distance is the certified `t`-boxed `Λ₀` producer with the
centered-form lever (`TBOX_CENTERED_FORM_LEVER_2026-10-10.md`,
`ARB_CERTIFIED_MARCH_2026-10-10.md`). This file does not shorten that distance;
it adds generic machinery that converts any future point-sign landing into
positive-length coverage, and sets up R2 for its first endpoint-neighborhood
coverage (currently it has none).
