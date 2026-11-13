# YM reflection positivity — L² extension state (2026-11-12)

**Status update to `YM_L2_EXTENSION_SCOPING_2026-11-11.md`** after the
2026-11-12 session's push into step 3c.4c assembly.

**Head at write time:** `7cb17fc3` on master (pushed to origin as of
`b44173f6`; final linearity commit pending push).

## What this session delivered

Seven new files, all three-axiom bar, no sorry, no native_decide. All
steps of the step-3c.4c composition are now live, conditional on a
single named Fubini-reassembly gap (`WilsonAvgMinusL2ContractionBase`).

### Files landed (chronological)

| # | File | Purpose |
|---|------|---------|
| 1 | `WilsonActionTotalBounds_2026_11_12.lean` | `∃ M, m > 0, ∀ U, m ≤ exp(-β·S_W(U)) ≤ M` via compactness |
| 2 | `WilsonMuGibbsMuBaseBounds_2026_11_12.lean` | `lintegral` comparison `μ_Gibbs ↔ μ_base` with those `M, m` |
| 3 | `WilsonMuGibbsMuBaseELpNorm_2026_11_12.lean` | Lift to `eLpNorm 2` comparison (`√M`, `√(1/m)`) |
| 4 | `WilsonAvgMinusL2Composition_2026_11_12.lean` | Composition theorem — reduces `WilsonAvgMinusL2Bound L β` to a single base-measure Jensen hypothesis |
| 5 | `JensenNormSqIntegral_2026_11_12.lean` | Atomic `‖∫ f dμ‖² ≤ ∫ ‖f‖² dμ` for probability measures |
| 6 | `WilsonAvgMinusPointwiseJensen_2026_11_12.lean` | Specialised Jensen to `avgMinus` — per-U bound |
| 7 | `WilsonAvgMinusLinearity_2026_11_12.lean` | `avgMinus_sub` + `avgMinus_gluePlusMinus` factorisation |

### Composition chain closed

```
WilsonAvgMinusL2Bound L β              — L² contraction on μ_Gibbs
  ← wilsonAvgMinusL2Bound_of_base_contraction           [LANDED]
      • exp(-βS) sandwich M, m         ← WilsonActionTotalBounds       [LANDED]
      • μ_Gibbs ≤ √M · μ_base          ← WilsonMuGibbsMuBaseELpNorm   [LANDED]
      • μ_base ≤ √(1/m) · μ_Gibbs      ← WilsonMuGibbsMuBaseELpNorm   [LANDED]
      • WilsonAvgMinusL2ContractionBase L                  [REMAINING GAP]

WilsonAvgMinusL2ContractionBase L      — Jensen contraction on μ_base
  ← (Fubini + pointwise Jensen)
      • avgMinus_sub                   ← WilsonAvgMinusLinearity      [LANDED]
      • avgMinus_gluePlusMinus         ← WilsonAvgMinusLinearity      [LANDED]
      • pointwise-U Jensen             ← WilsonAvgMinusPointwiseJensen[LANDED]
      • atomic Jensen for ‖·‖²         ← JensenNormSqIntegral         [LANDED]
      • Fubini reassemble              ← wilsonBaseMeasure_integral_split
                                         (2026-10-20 EXISTS, needs lintegral analog)
```

## Remaining gap — `WilsonAvgMinusL2ContractionBase`

**Statement:**
```
∀ G H : BoundedContinuousFunction (GaugeField L) ℂ,
  eLpNorm (fun U => avgMinus G U - avgMinus H U) 2 (wilsonBaseMeasure L)
    ≤ eLpNorm (fun U => G U - H U) 2 (wilsonBaseMeasure L)
```

**Proof sketch (fully mapped; mechanical to implement):**

1. Set `K := G - H`, continuous.
2. By `avgMinus_sub` [LANDED]: the LHS integrand becomes `avgMinus K U`.
3. The target becomes `eLpNorm (avgMinus K) 2 μ_base ≤ eLpNorm K 2 μ_base`.
4. Via `eLpNorm_eq_lintegral_rpow_enorm`, this reduces to the
   `lintegral` form:
   `∫⁻ U, ‖avgMinus K U‖ₑ² ∂μ_base ≤ ∫⁻ U, ‖K U‖ₑ² ∂μ_base`.
5. Apply `wilsonBaseMeasure_split_minus` [EXISTS 2026-10-20] via
   `MeasurePreserving.lintegral_map_equiv` to rewrite both sides as
   integrals on the product space `Pi{isMinus} × Pi{¬isMinus}`.
6. On LHS: `avgMinus K (e.symm (V, W))` depends on `V` only through
   `(V, W) ↦ W` (via `avgMinus_gluePlusMinus` [LANDED] + the structural
   fact `projectNonMinus ∘ e.symm = snd` modulo subtype identification).
   So the inner `V`-integral collapses (constant integrand against
   probability measure).
7. By `norm_sq_avgMinus_le_integral_norm_sq` [LANDED] applied pointwise
   in `W`, the LHS is bounded by the iterated integral of `‖K(e.symm
   (V', W))‖ₑ²`.
8. By `lintegral_prod` (Tonelli), this equals the RHS.

**Estimated size:** 150–250 Lean lines, one dedicated session. The
intricate piece is step 6 — identifying `projectNonMinus ∘ e.symm` with
the product projection, which needs careful subtype-vs-complement
bookkeeping between `MinusLinks L` (used in `avgMinus`) and
`Subtype isMinusLink` (used in the Fubini split).

**Simplification path:** introduce
`gaugeFieldSectorEquiv : GaugeField L ≃ᵐ NonMinusGauge L × MinusGauge L`
directly (bypassing the `isMinusLink` Subtype form), prove its
measure-preserving property for `μ_base ↔ μ_{nonminus} × μ_minus`, and
use that for Fubini. This is a one-line `MeasurableEquiv.piEquivPiSubtypeProd`
spelling + inheritance of `MeasurePreserving`.

## Downstream on the L² extension plan

Once `WilsonAvgMinusL2ContractionBase` discharges, the step-3c.4c
hypothesis `WilsonAvgMinusL2Bound L β` becomes a live theorem, which:

* Closes the density composition for step 3c.4d (~30-50 lines).
* Together with step 4 (PSD ← entrywise limit, already LANDED as
  `MatrixPosSemidefLimit_2026_11_11.lean`) and step 5a (bilinear Gram
  convergence, pending ~100 lines), delivers full L² reflection
  positivity — the `wilson_reflection_positivity_of_L2` target.

## Session commit roll-up

```
7cb17fc3 YM L² step 3c.4c atomic: avgMinus linearity under subtraction
b44173f6 YM L² step 3c.4c atomic: pointwise Jensen for avgMinus
0645b1e1 YM L² step 3c.4c atomic: Jensen for squared norm on probability measures
28c94b2f YM L² step 3c.4c composition: WilsonAvgMinusL2Bound from base contraction
dcacc302 YM L² step 3c.4c ingredient: eLpNorm two comparison μ_Gibbs ↔ μ_base
39ef1b82 YM L² step 3c.4c ingredient: μ_Gibbs ↔ μ_base lintegral comparison
4fee7918 YM L² step 3c.4c ingredient: wilsonActionTotal bounds on compact
```

Seven commits. All three-axiom bar [propext, Classical.choice,
Quot.sound]. No project axioms, no sorry, no native_decide.
