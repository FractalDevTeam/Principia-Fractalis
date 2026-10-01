# Partition optimality — NEGATIVE RESULT, 2026-09-30

**Question asked:** can a smarter Box-0 partition cut the ~6.5-day panel build?

**Answer: no. The hand-tuned OPT-40-TIGHT partition is essentially optimal.
Maximum available saving is 4.5%, and claiming it costs more work than it saves.
Do not spend time here.**

## The design problem

`scripts/opt40tight.py` fixes 40 macrosegments over `[1, 5]`. Its own docstring
states the constraint:

```
total midpoint error = Σ MHI_j · (U_j − L_j)³ / (24 · n_j²)
                     = 1.9621020147e-06   (after MHI_OVERRIDE)
```

Build cost is (panel count) × (per-panel elaboration cost). Per-panel cost is
fixed by the generator, so the only lever is panel count:

```
minimise    Σ n_j
subject to  Σ MHI_j h_j³ / (24 n_j²) ≤ E_budget
```

With `c_j = MHI_j h_j³ / 24`, the Lagrangian gives `n_j ∝ c_j^(1/3)` — the
classical equidistribution rule.

## Result 1 — allocation only, boundaries fixed

`scripts/partition_search.py` (new, read-only).

| | panels | E |
|---|---|---|
| current OPT-40-TIGHT | **530** | 1.9621020147e-06 |
| equidistributed, same budget | **519** | 1.9566677101e-06 |

**Saving: 11 panels, 2.1%.**

The hand-tuned table is within 2.1% of the theoretical optimum for its
boundaries. Whoever tuned it did the job properly. Allocation is not where the
cost is.

Direction of the correction is interesting: the current table *over*-allocates
to the high-MHI segments near `σ = 1` (Seg 1 wants 16 not 18, Seg 17 wants 19
not 23, Seg 25 wants 23 not 30) and *under*-allocates to the low-MHI tail
(Seg 37–40 want 6/5/4/3 rather than 4/3/2/2). Net 11.

## Result 2 — joint boundary + allocation search

`scripts/boundary_search.py` (new, read-only). Boundaries re-placed by
equidistributing `∫ M(x)^(1/3) dx`, scanning segment count K from 8 to 80.

| K | panels | vs current |
|---|---|---|
| 36 | 530 | +0 |
| 40 | 525 | −5 |
| 46 | 519 | −11 |
| 60 | 512 | −18 |
| 72 | 507 | −23 |
| **80** | **506** | **−24** |

**Best: 506 panels at K = 80. Saving 24 panels, 4.5%.**

And it requires **doubling the segment count**, so twice as many
`emit_M_certificate` runs and twice as many MHI bounds to certify. The 4.5%
panel saving is consumed by the certification work, and every one of the 506
panels would have to be regenerated and re-gated from scratch.

The dyadic boundary scheme (1/32, 1/16, 1/8, 1/4) was the thing I expected to
find slack in, since MHI spans five orders of magnitude (13.3 → 1.01e-4) and
dyadic blocks cannot track that. It turns out the blocks were chosen to roughly
follow the decay, and the residual inefficiency is small.

## What this means for build time

The ~6.5-day cost is **intrinsic to per-panel elaboration**, not to the
partition. The levers that remain, in order of expected value:

1. **Per-panel elaboration cost** — a Lean-level question about the emitted
   panel proofs, not a geometry question. Untouched so far and the only place
   a large factor could still be hiding.
2. **Parallelism** — the build is memory-bound, not core-bound. Each
   `RiemannXiBox*Panels` module peaks near 9 GB, so throughput scales with RAM,
   not cores. Raising WSL's cap from 15 GB to 22 GB on the Legion takes it from
   `-j 1` to `-j 2`; that is a real 2× and it is already applied.
3. **Fewer panels** — closed off by this document. ≤ 4.5%, net negative.

## Honest limitation

`boundary_search.py` log-interpolates `M(x)` from the 40 certifier samples at
the segment left endpoints. The true `M` comes from `emit_M_certificate`. So the
4.5% figure is an **estimate**, not a certified design.

That limitation does not weaken the conclusion. The estimate would have to be
wrong by a large factor to make re-partitioning worthwhile, and the scan is
monotone and well-behaved across K — there is no sign of a hidden regime where
the payoff jumps. If anything, left-endpoint evaluation of a decreasing MHI is
conservative, so the real optimum is likely *closer* to current than the scan
suggests.

## Provenance

- `scripts/partition_search.py`, `scripts/boundary_search.py` — new, read-only
  with respect to the corpus, import `opt40tight` without modifying it.
- Raw output: `/tmp/partition_search_result.json`,
  `/tmp/boundary_search_result.json`.
- Nothing in the existing corpus was modified or deleted to produce this.
