# R1 uniform-bound pilot program — COMPLETE

**Date:** 2026-10-15
**Decision (Pablo, after PILOT14 gate analysis):** option D — stop + document.
**Verdict:** the uniform-bound R1 campaign is closed as a precise analytic fact.
No further uniform-bound pilots will be built; the sharp ceiling is reached.
**HEAD at closure:** `fe768c5a` on `master`, in sync with origin.

## 1. What landed

**13 kernel-clean R1 pilot boxes** on the right edge `Re s = 1`, covering the
connected interval `[0, 81/20] = [0, 4.05]` (31.2% of the `[0, 13]` target).
Each pilot delivers an unconditional theorem of the form

```
pilot_r1_box_c*_closed :
    ∀ t ∈ Icc (c - r) (c + r), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re
```

with zero hypotheses, zero project axioms, and `#print axioms` reporting the
mathlib allowlist `[propext, Classical.choice, Quot.sound]` (nothing beyond
the three — unavoidable for anything using `tsum` / `exp` / `HasDerivAt`).

Together with the uniform modulus bound `‖completedRiemannZeta₀(1+it)‖ ≤ 50/1727`
(valid on all `t ∈ ℝ`, kernel-clean), the program certifies `Re ξ(1+it) > 0`
on the connected segment `[0, 4.05]` of the right edge.

## 2. Scientific status (per master directive classifier)

- **PROVEN** (unconditional, kernel-clean):
  - 13 right-edge boxes certifying `Re ξ(1+it) > 0` on `[0, 4.05]`.
  - Uniform bound `‖Λ₀(1+it)‖ ≤ 50/1727 ≈ 0.02895` on all `ℝ`.
  - Strip-uniform bound `‖Λ₀(z)‖ ≤ 2/3` on `Re z ∈ [0, 2]`.
  - Cauchy derivative bound `‖Λ₀'(1+it)‖ ≤ 2/3`.
- **CLASSICALLY KNOWN territory:** the finite-rectangle statement that
  `ζ(s) ≠ 0` on this segment of the critical strip is a Riemann–Gram-era
  fact. The pilot program is a Lean kernel-clean verification of a known
  fact via a producer-side uniform-bound recipe — not a claim about open RH.
- **NOT CLOSED:** the open Riemann Hypothesis on `[0, 13]` or anywhere else.

## 3. Why the program stops at 4.05 (the sharp ceiling)

Gate 1 for a centered-form box at `c` with uniform modulus bound `B`:
```
|s(s-1)| · B ≤ 1/2 ,  where s = 1 + ic , so |s(s-1)| = c·√(c²+1) .
```
Under the strongest cheap rational bound `B = 50/1727` the sharp ceiling is
```
c · √(c² + 1) ≤ 1727/100 = 17.27  ⇒  c ≤ ≈ 4.09 .
```
Pilot 13 at `c = 73/20 = 3.65` with `r = 2/5` covers up to `c+r = 81/20 = 4.05`,
leaving Gate 1 margin ≈ 0.004 (closed by `nlinarith`). One more pilot at
`c ≈ 4.085` could gain `~0.04` of coverage; two more cannot be built under
any uniform modulus bound compatible with the current rational-numerics chain
(`exp(π) ≥ 23`, `π > 157/50`, `exp(-π) ≤ 1/23`). The `50/1727` bound is
essentially saturated; sharpening it further is a rational-numerics campaign
without clear return.

## 4. The three Λ₀ ceilings used

| Bound        | Pilots       | Numerics                                           | Max `c` (triangle `|s(s-1)| ≤ c²+c`) |
|--------------|--------------|----------------------------------------------------|---------------------------------------|
| `2/21`       | 1–7, 5'      | `exp(π) ≥ 8`, `exp(-π) ≤ 1/8` → tighten to `1/20` | `(−1 + √22)/2 ≈ 1.85`                 |
| `1/33`       | 8–11         | `exp(-π) ≤ 1/23`                                   | `(−1 + √67)/2 ≈ 3.59`                 |
| `50/1727`    | 12, 13       | `exp(π) ≥ 23` combined with `π > 157/50`          | sharp (`c√(c²+1) ≤ 17.27`) ⇒ `≈ 4.09` |

Pilots 12 and 13 additionally switched the gate from the triangle estimate
`|s(s-1)| ≤ c² + c` to the sharp `|s(s-1)| = c√(c²+1)` to reach the ceiling.

## 5. The 13 pilots (left to right)

| # | File (`PF/Analytic/PilotBoxes/`)             | Center `c` | `r`   | `L`  | Box `[c-r, c+r]`      | Bound used |
|---|-----------------------------------------------|------------|-------|------|-----------------------|------------|
| 7 | `R1_c1_20_r0_05_2026_10_14`                   | 1/20       | 1/20  | 2    | `[0, 1/10]`           | 2/21       |
| 5'| `R1_c1_5_r0_1_2026_10_14`                     | 1/5        | 1/10  | 2    | `[1/10, 3/10]`        | 2/21       |
| 2 | `R1_c0_5_r0_2_2026_10_14`                     | 1/2        | 1/5   | 2    | `[3/10, 7/10]`        | 2/21       |
| 1 | `R1_c0_5_r0_05_L2_2026_10_14`                 | 1/2        | 1/20  | 2    | `[9/20, 11/20]`       | 2/21       |
| 4 | `R1_c3_4_r0_05_2026_10_14`                    | 3/4        | 1/20  | 2    | `[7/10, 4/5]`         | 2/21       |
| 3 | `R1_c1_r0_2_2026_10_14`                       | 1          | 1/5   | 2    | `[4/5, 6/5]`          | 2/21       |
| 5 | `R1_c7_5_r0_2_2026_10_14`                     | 7/5        | 1/5   | 2    | `[6/5, 8/5]`          | 2/21       |
| 6 | `R1_c9_5_r0_2_2026_10_14`                     | 9/5        | 1/5   | 2    | `[8/5, 2]`            | 2/21       |
| 8 | `R1_c11_5_r0_2_2026_10_14`                    | 11/5       | 1/5   | 1    | `[2, 12/5]`           | 1/33       |
| 9 | `R1_c13_5_r0_2_2026_10_14`                    | 13/5       | 1/5   | 1    | `[12/5, 14/5]`        | 1/33       |
|10 | `R1_c3_r0_2_2026_10_14`                       | 3          | 1/5   | 1    | `[14/5, 16/5]`        | 1/33       |
|11 | `R1_c17_5_r0_2_2026_10_14`                    | 17/5       | 1/5   | 1    | `[16/5, 18/5]`        | 1/33       |
|12 | `R1_c18_5_r0_4_L0_5_2026_10_14`               | 18/5       | 2/5   | 1/2  | `[16/5, 4]`           | 50/1727    |
|13 | `R1_c73_20_r0_4_L0_5_2026_10_15`              | 73/20      | 2/5   | 1/2  | `[13/4, 81/20]`       | 50/1727    |

Pilot ordering above is spatial (left to right on the right edge). Pilot 1 was
the first full centered-form box landed (commit `0c14eb38`), chronologically
followed by pilots 2, 3, 4, 5, 6, 5', 7, 8, 9, 10, 11, 12, 13.

Connected coverage checks (adjacency chain): every consecutive pair meets or
overlaps at a shared endpoint, so the union is the single connected interval
`[0, 81/20]`.

## 6. Why no pilot 14 (the IBP-decay route fails Gate 1)

See `codex/PILOT14_GATE_ANALYSIS_2026-10-14.md` (uncommitted, preserved on
disk per handoff). Key quantitative points:

- The single-IBP bound `‖Λ₀(1+it)‖ ≤ 4/(11|t|)` passes Gate 1 only for
  `c ≤ 0.943` — far below the 4.05 frontier. At `c ≈ 4`, the IBP bound is
  3× worse than the uniform `50/1727`, and the sharp Gate 1 constraint is
  negative (`(1 − 4·√17·0.091)/2 < 0`). Hard fail.
- The zeroth-order boundary terms cancel (`F₊(0) = F₋(0) = ω(1)`, opposite
  frequencies `±t/2` in `I₊`, `I₋`), so the true decay rate after one more
  IBP is `C₂/t²` not `C₁/|t|`. Even the right power with rough constant
  `C₂ ≈ 2.0` is `~2× short` of Gate 1 near the first zero at `t ≈ 14.13`.
- Conclusion recorded in that note: IBP is at best a mid-`t` tool; reaching
  the first-zero neighbourhood requires per-point certified panels
  (r120-style, Route B), estimated ~600 files. That is NOT in R1 scope.

The L4 identity itself (`Λ₀(1+it) = (2/(it))[∫F₋' e^{-itu/2} − ∫F₊' e^{+itu/2}]`,
the boundary-cancellation identity giving the true `1/t²` rate) is being
built by Legion in parallel. R1 does not depend on it.

## 7. Files and commits

**Lean files (producer stack):**
- `PF/Analytic/R1Neighborhood_2026_10_09.lean` — R1 statement scaffolding
- `PF/Analytic/CenteredFormBridge_2026_10_13.lean` — `R1_box_centered_of_lb`
- `PF/Analytic/Lambda0UniformBound_2026_10_14.lean` — `‖Λ₀(1+it)‖ ≤ 2/3`
- `PF/Analytic/Lambda0PrimeUniformBound_2026_10_14.lean` — Cauchy derivative
- `PF/Analytic/Lambda0TightBounds_2026_10_14.lean` — `‖Λ₀‖ ≤ 2/21`
- `PF/Analytic/Lambda0UltraTightBoundsMellin_2026_10_14.lean` — `‖Λ₀‖ ≤ 1/33`
- `PF/Analytic/Lambda0TightestBoundsMellin_2026_10_14.lean` — `‖Λ₀‖ ≤ 50/1727`
- `PF/Analytic/EdgeReDerivBound_2026_10_14.lean` — `|deriv edgeRe x| ≤ L` family
- `PF/Analytic/PilotBoxes/R1_*.lean` — the 13 pilot files above

**Reflog slice (pilot commits):**
```
78957b69 pilot 13 — R1 extends to [0, 81/20] (31.2% of target)
15017572 pilot 12 — L=1/2 + 50/1727, R1 reaches [0, 4] (30.8%)
a27dc4ee pilot 11 — R1 extends to [0, 18/5] (27.7%)
4aff57f0 pilot 10 — R1 extends to [0, 16/5] (24.6%)
a6eb1724 pilot  9 — R1 extends to [0, 14/5] (21.5%)
da160c59 pilot  8 — first box on 1/33 bound, extends to [0, 12/5]
a0db80bd pilot  7 — R1 closes to [0, 2] (15.4%)
e8a2cd41 pilot  5' — fills left gap, connected [1/10, 2] (15%)
c5582d25 pilot  6 — extends to [3/10, 2] (13%)
40d4907e pilot  5 — extends to [3/10, 8/5]
f6e9f6f9 pilot  4 — closes gap to [3/10, 6/5]
23256f5b pilot  3 — [4/5, 6/5], disjoint from pilots 1–2
9583d8e9 pilot  2 — tighter 2/21 bound, 4× wider box
0c14eb38 pilot  1 — FIRST FULL CENTERED-FORM BOX, end-to-end closed
```

## 8. Companion codex notes

- `codex/PILOT14_GATE_ANALYSIS_2026-10-14.md` — the gate verdict (uncommitted)
- `codex/R1_COVERAGE_STATUS_2026-10-14_evening.md` — mid-campaign snapshot (pilots 1–11)
- `codex/LAMBDA0_UNIFORM_BOUND_STRATEGY_2026-10-14.md` — strategy for `‖Λ₀‖ ≤ 2/3`
- `codex/LAMBDA0_UNIFORM_BOUND_LANDED_2026-10-14.md` — landing note for `‖Λ₀‖ ≤ 2/3`
- `codex/LAMBDA0_PRIME_UNIFORM_BOUND_LANDED_2026-10-14.md` — landing for the derivative
- `codex/LAMBDA0_IBP_DECAY_STRATEGY_2026-10-14.md` — the IBP-decay path (now Legion's)
- `codex/FIRST_FULL_PILOT_LANDED_2026-10-14.md` — pilot 1 landing note

## 9. Governing-order context (not a claim, a locator)

Per the governing order recorded in the PILOT14 analysis
(mathlib PRs > substrate preprint > conclusion-gate > finite-rectangle RH):
this R1 program sits at the lowest-priority tier of the four. It is a clean
verified contribution that saturates its own analytic route; it does not bear
on open RH and does not reach the first zero.

The next priority items (not R1 scope):
- mathlib PRs #42093 (j-loreaux), #42101 (tb65536) — Pablo's words only.
- The L4 identity — Legion, in parallel.
- Substrate preprint and conclusion-gate work — separate campaigns.

## 10. Audit note

Standing rules observed in building this record:
- Content is factual-only; no narrative inflation; no referee-tier tail.
- No `#print axioms` output is reported as literal `[]`; every pilot and
  bound used mathlib's `[propext, Classical.choice, Quot.sound]`. The
  distinction between the mathlib allowlist and a literal empty list has
  been separately surfaced to Rio in the PILOT14 note.
- No public reply drafted. No mathlib push. No externally visible action.
- The uncommitted PILOT14 gate analysis is preserved as-is per handoff.
