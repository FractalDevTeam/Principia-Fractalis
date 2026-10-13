# RH below 15 — Gap B (zero-count exhaustion) VERIFIED kernel-clean, 2026-10-10

Author: Pablo Cohen. New additive module:
`PF_Lean4_Code/PF/Analytic/RHBelow15CountExhaustion_2026_10_10.lean` (untracked).

## What is now machine-checked

Single-file `lake env lean` (taskset -c 0,1, no build, load 0.10, EXIT 0). All three
declarations: axioms `[propext, Classical.choice, Quot.sound]` — no sorryAx, no project
axioms.

- `one_le_order_of_zero {z} (hz : riemannXiEntire z = 0) : 1 ≤ analyticOrderNatAt riemannXiEntire z`
  — a genuine ξ-zero has multiplicity ≥ 1 (ξ entire ⇒ AnalyticAt; ξ 1 = 1/2 ≠ 0 on the
  connected plane ⇒ not eventually zero ⇒ `analyticOrderAt ∉ {0, ⊤}`).
- `xiRectangleCountAtMostTwo_of_zeroSum (S) (hmem) (hsum) : XiRectangleCountAtMostTwo`
  — THE EXHAUSTION. `hmem` characterises `S` as exactly the ξ-zeros in `[0,1]×[-15,15]`;
  `hsum : ∑_{ρ∈S} (analyticOrderNatAt ξ ρ : ℂ) = 2`. Since each order ≥ 1 and the two
  distinct critical-line zeros (`two_distinct_critical_zeros_exists`) are in `S`, a
  `Finset.card` argument forces `S = {those two}`, so every zero is on `σ = 1/2`.
- `rh_below_15_of_zeroSum (S) (hmem) (hsum) : ∀ σ t ∈ box, ξ⟨σ,t⟩ = 0 → σ = 1/2`
  — RH below 15, via r331f's `rh_below_15_of_count_le_two`.

## Why this is the whole non-numerical half

`riemannHypothesis_below_15` splits into: contour = 2 (⇐ R1∧R2∧R3, the numerical campaign)
and contour = 2 ⇒ RH-on-box (this file). The corpus previously stated
`XiRectangleCountAtMostTwo` as an OPEN Prop and asserted its equivalence to "contour = 2"
only in prose; this file proves the `⇐` direction (the exhaustion) kernel-clean.

## The two interface hypotheses, and why they are mechanical to discharge

`hmem` is exactly `Set.Finite.mem_toFinset` of r331e's `finite_zeros_rectangle` composed
with `Complex.mem_reProdIm` on `Rectangle ⟨0,-15⟩ ⟨1,15⟩` — i.e. the re/im-bound form used
here is literally the membership of r331e's zero set. `hsum` is r331e's
`xi_full_rectangle_zero_count_identity` (contour = ∑ orders) with the contour value `2`
from `RightEdgeSigns.rectangleIntegral'_logDeriv_eq_two_of_right_edge` (verified kernel-clean
2026-10-09, conditional on R1∧R2∧R3).

**Why the wiring is deferred, not faked:** r331e and RightEdgeSigns have no oleans at this
pin. r331e is currently unbuildable because it imports the autoImplicit-broken r331c; the
clean top/bottom edges already exist in `RightEdgeSigns_2026_10_08` (the repair), so the
next step is to re-point r331e off r331c, build r331e + RightEdgeSigns oleans, then state
the fully-wired `rh_below_15_conditional (R1) (R2) (R3)` with hmem/hsum discharged. No new
mathematics — pure plumbing + an olean build.

## Honest scope

`riemannHypothesis_below_15` is RH on one finite rectangle, classically known since
Riemann/Gram. Nothing here bears on the open Riemann Hypothesis. R1/R2/R3 themselves
remain open (numerically confirmed only; see RH_RIGHTEDGE_SIGNFACTS_COLAB_2026-10-09.md and
TBOX_CAMPAIGN_COST_2026-10-01.md — the 402× interval-dependency lever).
