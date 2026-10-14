# Pilot R1 producer — feasibility measurements, 2026-10-13

Author: Pablo Cohen + Claude Opus 4.7 (1M context). Numerical probe for the
centered-form Lean bridge (`CenteredFormBridge_2026_10_13.R1_box_centered`).
mpmath dps = 100, 201 derivative samples per box. **This is sampling, NOT a
certificate** — a certified producer must emit interval-arithmetic bounds. The
point here: measure the `(c, r, Mc, L)` parameters a certified producer must
supply, and verify the strict margin `L · r < Mc` holds comfortably across R1.

## Measurement table (R1 on `[0, 13]`, right edge, `Re ξ(1 + it) > 0`)

| box | c | r | Mc = Re ξ(1+ic) | L (sampled) | L_inflated_2x · r | margin |
|---|---|---|---|---|---|---|
| 0 | 0.1 | 0.05 | 0.499883 | 3.500e-03 | 3.500e-04 | **+0.4995** |
| 1 | 0.5 | 0.05 | 0.497090 | 1.276e-02 | 1.276e-03 | **+0.4958** |
| 2 | 1.0 | 0.10 | 0.488454 | 2.501e-02 | 5.003e-03 | **+0.4835** |
| 3 | 2.0 | 0.50 | 0.455284 | 5.093e-02 | 5.093e-02 | **+0.4044** |
| 4 | 5.0 | 0.50 | 0.275361 | 6.746e-02 | 6.746e-02 | **+0.2079** |
| 5 | 10.0 | 0.10 | 0.036811 | 2.316e-02 | 4.631e-03 | **+0.0322** |
| 6 | 12.5 | 0.50 | 0.004849 | 7.856e-03 | 7.856e-03 | **−0.0030** (fails) |

Margin = `Mc − L_inflated_2x · r`. The `2×` inflation accounts for the gap
between a true pointwise derivative bound and a rigorous interval enclosure of
`|f'(box)|` over the whole `t`-box (Legion's `TBOX_CENTERED_FORM_LEVER` and
`ARB_CERTIFIED_MARCH` saw ~2–3× realistic inflation for cap-1 Taylor on R1).

## Findings

1. **R1 is comfortable almost everywhere on `[0, 13]`.** Six of seven probe
   boxes pass the strict margin check `L · r < Mc` after 2× derivative
   inflation. The reserves are generous for `t ∈ [0, 5]` (margin ~0.5–0.4) and
   still ample at `t = 10` (margin ~0.03 against a drop of three orders of
   magnitude in `Re ξ`).

2. **Only the segment tail `t ∈ [12, 13]` is margin-tight.** `Re ξ(1 + 12.5i) ≈
   4.85e-3` is already down to 1 % of `ξ(1) = 0.5`; a 0.5-wide box fails but a
   narrower one — `r ≈ 0.1` — would pass. Legion's ARB march on R1 using the
   cap-1 centered form landed 289 boxes for the full segment; this probe
   suggests a well-sized `r(t)` schedule would do it with far fewer boxes if the
   margin thresholds are respected per sub-segment.

3. **Approximate box-count feasibility:** with a mixed `r`-schedule
   (`r = 0.5` on `[0, 10]`, `r = 0.1` on `[10, 13]`), R1 could be covered in
   roughly 20 + 30 = 50 boxes. This is **sampled, not rigorous** — the real
   count depends on the actual interval widths of the certified
   `f'(box)` enclosure, which only the full Lean/Arb producer gives. Legion's
   289 is the rigorous Arb/python-flint cap-1 count; it's the correct upper
   target for Lean-side planning until the producer runs.

4. **Derivative magnitude profile (sampled):**
   - `t = 0.1`: `|edgeRe'| ≈ 3.5e-3`
   - `t = 1`:   `|edgeRe'| ≈ 2.5e-2`
   - `t = 5`:   `|edgeRe'| ≈ 6.7e-2` (sampled peak over probed range)
   - `t = 10`:  `|edgeRe'| ≈ 2.3e-2`
   - `t = 12.5`:`|edgeRe'| ≈ 7.9e-3`
   The sampled peak on `[0, 13]` is ~0.07 near `t = 5`. A single global
   derivative-bound `L_global = 0.1` works on `[0, 13]` and gives
   `L · r < Mc` across most boxes.

## What this does NOT establish

* **No certified bound.** The sampling is 201 points per box; a certified
  producer must use interval arithmetic. The numbers here are feasibility
  signal, not Lean-admissible certificates.
* **No closed Lean segment.** R1 remains open on `[0, 13]`. The infrastructure
  (`centered_form_pos`, `R1_box_centered`, `forall_Icc_cover`) is ready; the
  per-box certificates (`(Mc, L, margin)` with rigorous interval widths) are
  the missing engineering piece.
* **No bearing on the open Riemann Hypothesis.** This is a sub-sub-step of
  formalising `rh_below_15_conditional`, a classically-known finite fact.

## The next engineering piece (producer side)

Per Legion's `TBOX_CENTERED_FORM_LEVER_2026-10-10.md`, the Lean producer needs:
1. **Per-box `I` panels** (certified theta quadrature of
   `completedRiemannZeta₀(1 + ic)` at the box CENTER `c`, rational-node interval
   arithmetic with phase kept).
2. **Parallel `I'` panels** (integrand × `(i log u)/2`, same panels, one extra
   factor per node) over the full box `[c − r, c + r]`.
3. **Assembly:** `f'(box) = (g' · I + g · I') / 2` as interval arithmetic on
   the sum, not on moduli — keeps the phase-cancellation that collapses the
   interval width 30–184×.
4. **Center value:** `f(c) = Re ξ(1 + ic)` from a point evaluation at `c`.
5. **Lean emission:** rewrite `scripts/emit_box_segment.py` to parameterise `t`
   as `[t_lo, t_hi]` and emit the two panel sets + the margin check.

The CURRENT panels are hard-pinned at `t = 15` (4,241 of them, representing the
σ-dimension of the top-edge campaign). Transposing to per-box center-with-radius
is the ~day-scale engineering estimate Legion recorded. This probe confirms the
mathematical margins are there; the barrier is purely implementation.

## Script

`codex/pilot_r1_box_measurement_2026-10-13.py` — stand-alone, mpmath dps = 100,
6.5 s runtime on this laptop. Reproducible.
