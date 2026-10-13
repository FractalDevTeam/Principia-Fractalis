# RH below 15 — the full conditional theorem, WIRED and kernel-clean, 2026-10-10

Author: Pablo Cohen. The non-numerical half of `riemannHypothesis_below_15` is now
a single machine-checked theorem conditional on exactly the three right-edge sign
facts R1 ∧ R2 ∧ R3, with no other open antecedent and no project axioms.

## The capstone

`PF/Analytic/RHBelow15Conditional_2026_10_10.lean` (new, additive, isolated from PF.lean):

```
theorem rh_below_15_conditional
    (hR1 : RightEdgeR1) (hR2 : RightEdgeR2) (hR3 : RightEdgeR3) :
    ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → -15 ≤ t → t ≤ 15 →
      riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1 / 2
```
(plus `rh_below_15_conditional'` with the three sign facts spelled out inline.)

Axioms (live `#print axioms`, single-file `lake env lean`): `[propext,
Classical.choice, Quot.sound]` — no sorryAx, no project axioms.

## The three layers it composes (all re-verified kernel-clean this pass)

1. **contour = 2 ⇐ R1∧R2∧R3** —
   `RightEdgeSigns20261008.rectangleIntegral'_logDeriv_eq_of_three_right_edge_facts`
   (rotated log-branch bridge r331g + symmetry reduction).
2. **contour = ∑ zero-orders** — `FullRectangleBoundaryR331e.xi_full_rectangle_zero_count_identity`
   (argument principle on `[0,1]×[-15,15]`).
3. **∑ orders = 2 ⇒ RH-on-box** — `RHBelow15CountExhaustion.rh_below_15_of_zeroSum`
   (multiplicity exhaustion, 2026-10-10, + r331f's `rh_below_15_of_count_le_two`).

r331g's `zF`/`wF` are defined identically to r331e's (`⟨0,-15⟩`,`⟨1,15⟩`), so the two
contour terms are defeq and compose by `.trans`.

## Two REPAIRS made to get here (root-cause, not routed-around)

Both were pre-existing latent defects; both modules had NO olean (never built).

* **r331c autoImplicit capture** (`RiemannXiTopEdge_r331c.lean`): the file used
  `riemannXiEntire` without `open PrincipiaTractalis.RiemannXiEntire`, so
  autoImplicit silently bound it as an arbitrary `Sort`, making every theorem
  (incl. `top_edge_ne_zero`) `sorryAx`-tainted. FIX: added
  `set_option autoImplicit false` + `open PrincipiaTractalis.RiemannXiEntire`.
  Now all four theorems `[propext, Classical.choice, Quot.sound]`. r331d
  (bottom edge, imports r331c) follows clean.
* **r331e border navigation** (`RiemannXiFullRectangleBoundary_r331e.lean`):
  `interior_re_strict` constructed `RectangleBorder` membership with the wrong
  union disjuncts (type mismatch at the left/right edges). FIX: matched the
  correct `((bottom ∨ left) ∨ top) ∨ right` structure (same the working
  `full_rectangle_boundary_zero_free` uses) and built membership via
  `Complex.mem_reProdIm`/`Set.mem_singleton_iff`. `xi_full_rectangle_zero_count_identity`
  and `interior_xi_zero_iff_zeta_zero` now clean, no sorryAx.

Backups: `*.bak_autoimplicit_2026-10-10`, `*.bak_borderfix_2026-10-10`.
Both files are tracked (`git M`) but ISOLATED from PF.lean's build closure (neither
r331c nor r331e is imported by PF.lean), so the main panel build is unaffected.

## Infrastructure method (important, avoids the OOM trap)

`RiemannXiTopUnion.olean` shows STALE by mtime (checkout artifact; source git-clean).
Running `lake build` on anything importing it risks rebuilding the 4,241-panel union
(the 76-day / OOM category). AVOIDED entirely: built every olean with
`taskset -c 0,1 lake env lean -o <olean> <src>` — the raw compiler with `-o`
compiles ONE file against EXISTING import oleans, writes one olean, ZERO dependency
cascade. Load never exceeded ~1.0. Five oleans built this way: r331c, r331d, r331e,
RightEdgeSigns, RHBelow15CountExhaustion, + the capstone.

## Scope — unchanged and honest

`riemannHypothesis_below_15` is RH on ONE finite rectangle, classically known since
Riemann/Gram. This bears NOTHING on the open Riemann Hypothesis. R1/R2/R3 are still
OPEN (numerically confirmed only; certified t-boxed interval campaign remains — see
TBOX_CAMPAIGN_COST_2026-10-01.md, the 402× interval-dependency lever). What changed:
the finite statement is now one theorem, conditional on exactly those three sign
facts, machine-checked with zero project axioms.
