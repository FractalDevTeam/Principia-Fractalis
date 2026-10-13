# Arb-certified RH-below-15 box march — rigorous campaign simulation, 2026-10-10

Author: Pablo Cohen. Run on Google Colab (python-flint / Arb ball arithmetic,
prec 160-180 bits). RIGOROUS: an Arb comparison `(ball > 0)` is True only if the
WHOLE ball is > 0, so every certified box is a genuine rigorous sign enclosure.
This is a campaign SIMULATION in Arb, NOT a Lean proof (see limitation below).

## Two methods, measured

For each right-edge segment, grow each t-box as wide as the method can still
rigorously certify the required sign; count certified boxes.

| segment (requirement)        | naive theta-gen | DIRECT Arb ball | CENTERED (mean-value) Arb |
|------------------------------|-----------------|-----------------|---------------------------|
| R1  Re xi>0 on [0,13]        | 53              | stuck at t=0*   | 289  (r 1.1e-2..4.0e-2)   |
| R2  Im xi>0 on [13,29/2]     | 43              | **867**         | **41**  (r 1.3e-2..2.3e-2)|
| R3  Re xi<0 on [29/2,15]     | 136             | 78              | **13**  (r 1.7e-2..2.0e-2)|
| total                        | 232             | (n/a)           | 343 / best-of ~107        |

*R1 direct: box containing t=0 hits s=1, the removable `1/(1-s)` pole in Lambda0
that interval arithmetic can't cancel. Handled by starting the march at t=0.05
([0,0.05] is already the PROVEN `R1_on_neighborhood` Lean theorem).

## The finding

- The **centered / mean-value form** `f(t) in f(c) + f'(box)*[-r,r]` (f(c) a tight
  point eval, f'(box) the x^1 coefficient of an Arb power series at the ball t_box)
  **kills the cancellation-dependency loss** that dominates R2/R3: R2 867->41,
  R3 136->13 (~10x). These are the hard, margin-limited segments where
  `Im xi = (-t^2 B + t A)/2` nearly cancels.
- R1 is smooth with a large margin (xi(1)=1/2); it wants WIDE boxes. The 1st-order
  centered form caps box width (the derivative enclosure inflates over wide boxes),
  giving 289 — worse than the naive theta decomposition's 53. R1 should use either
  the existing theta generator or a higher-order Taylor model (cap>=3, bounding f''
  etc.), which would widen R1 boxes greatly.
- **Best-of-both (naive R1 + centered R2/R3) ~ 107 boxes**, vs naive 232. Feasible
  either way — day-scale, not the 76-day naive campaign. A higher-order Taylor
  model plausibly brings the total to order-30-50.

## Honest limitation (the gap to a Lean proof)

Arb rigor certifies the sign facts R1/R2/R3 as a NUMERICAL campaign — stronger than
the earlier mpmath SAMPLING (which only checked grid points), because Arb balls
cover whole boxes. But this is Arb/Python, NOT Lean. To close the LEAN R1/R2/R3
(`RightEdgeR1/R2/R3`, consumed by `rh_below_15_conditional`), the certificates must
be reproduced in Lean's own interval arithmetic (the `girving/interval` + t-boxed
quadrature generator), OR a verified Arb-certificate checker would be needed. The
centered-form lever tells the Lean generator HOW to be cheap (mean-value in t, not
naive intervals); it does not itself discharge the Lean goals.

And unchanged: `riemannHypothesis_below_15` is RH on ONE finite rectangle,
classically known since Riemann/Gram. None of this touches the open Riemann
Hypothesis.

## Next step

Higher-order Taylor model (cap=3-4) for R1 to widen its boxes, then a hybrid
all-segment count; then transpose the Lean generator (`scripts/emit_box_segment.py`)
to emit centered-form (mean-value in t) panels for R2/R3. Colab notebook:
`Untitled` at https://colab.research.google.com/drive/1r0X1XTFek0H8Q2wqZPHzOTSJoXrdzRGc
Scripts: scratchpad/colab_arb_rh_march.py (direct), colab_arb_centered.py (centered).
