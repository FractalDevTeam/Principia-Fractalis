# Pilot R2 + R3 producer — feasibility measurements, 2026-10-13

Author: Pablo Cohen + Claude Opus 4.7 (1M context). Companion to
`PILOT_R1_FEASIBILITY_2026-10-13.md`. Measures the `(c, r, Mc, L)` parameters
the centered-form Lean bridge needs for the two margin-tight segments:

* **R2:** `Im ξ(1 + it) > 0` on `t ∈ [13, 29/2 = 14.5]`
* **R3:** `Re ξ(1 + it) < 0` on `t ∈ [29/2, 15]`

Not a certificate — mpmath sampling at dps=100, 201 derivative samples per box.
Point: confirm the centered-form margins `L · r < |Mc|` hold across R2 and R3
with 2× derivative inflation for interval-slack. **All 14 probed boxes pass.**

## R2 table — `0 < Im ξ(1 + it)`

| c | r | Mc = Im ξ(1+ic) | L (sampled) | L_inflated_2x · r | margin | status |
|---|---|---|---|---|---|---|
| 13.00 | 0.050 | +1.983e-03 | 1.621e-03 | 1.621e-04 | **+1.821e-03** | PASS |
| 13.25 | 0.100 | +1.614e-03 | 1.457e-03 | 2.913e-04 | **+1.323e-03** | PASS |
| 13.50 | 0.100 | +1.293e-03 | 1.265e-03 | 2.531e-04 | **+1.040e-03** | PASS |
| 13.75 | 0.100 | +1.016e-03 | 1.089e-03 | 2.179e-04 | **+7.983e-04** | PASS |
| 14.00 | 0.100 | +7.800e-04 | 9.286e-04 | 1.857e-04 | **+5.943e-04** | PASS |
| 14.25 | 0.100 | +5.806e-04 | 7.831e-04 | 1.566e-04 | **+4.239e-04** | PASS |
| 14.40 | 0.050 | +4.770e-04 | 6.775e-04 | 6.775e-05 | **+4.093e-04** | PASS |
| 14.45 | 0.030 | +4.450e-04 | 6.427e-04 | 3.856e-05 | **+4.064e-04** | PASS |

8 boxes, 8 PASS. The margin stays comfortable even at the right endpoint
`t = 29/2` where `Im ξ` has dropped to ~4.4e-4.

## R3 table — `Re ξ(1 + it) < 0`

| c | r | Mc = Re ξ(1+ic) | L (sampled) | L_inflated_2x · r | margin | status |
|---|---|---|---|---|---|---|
| 14.50 | 0.050 | −5.591e-04 | 8.096e-04 | 8.096e-05 | **+4.781e-04** | PASS |
| 14.60 | 0.050 | −6.284e-04 | 6.925e-04 | 6.925e-05 | **+5.591e-04** | PASS |
| 14.70 | 0.050 | −6.869e-04 | 5.845e-04 | 5.845e-05 | **+6.284e-04** | PASS |
| 14.80 | 0.050 | −7.354e-04 | 4.851e-04 | 4.851e-05 | **+6.869e-04** | PASS |
| 14.90 | 0.050 | −7.749e-04 | 3.940e-04 | 3.940e-05 | **+7.355e-04** | PASS |
| 14.95 | 0.030 | −7.914e-04 | 3.348e-04 | 2.009e-05 | **+7.713e-04** | PASS |

6 boxes, 6 PASS. `Re ξ` becomes more negative as `t → 15`; the derivative
magnitude decreases monotonically; margin widens along the segment.

## Findings

1. **Centered-form margin holds across R2 and R3.** All 14 probed boxes pass
   with 2× derivative inflation, confirming Legion's ARB_CERTIFIED_MARCH
   findings on both segments quantitatively (ARB count 41 for R2, 13 for R3;
   my probe suggests ~15 R2 boxes at `r = 0.1`, ~10 R3 boxes at `r = 0.05`,
   consistent with ARB's rigorous interval widths being ~2–4× looser than
   sampled derivatives).

2. **R2 is the globally tightest segment** (Mc down to 4.5e-4 at `t = 14.45`,
   vs R3's floor ~5.6e-4 at `t = 14.5`). But both are still an order of
   magnitude above the margin threshold with modest `r`.

3. **The derivative magnitude profile on R2 ∪ R3** stays bounded between
   roughly `3e-4` and `1.7e-3` across `[13, 15]`. A global uniform
   derivative bound `L_global = 2e-3` would work for the entire R2 ∪ R3
   campaign; using segment-local bounds (`L ≈ 7e-4` on tightest sub-boxes)
   gives more boxes-per-r headroom.

4. **Combined pilot-box budget for all three sign facts, mixed `r` schedule**:
   - R1 on `[0, 13]`:  ~20 boxes at `r = 0.5` on `[0, 10]` + ~30 boxes at
     `r = 0.1` on `[10, 13]`  →  ~50 boxes (sampled estimate)
   - R2 on `[13, 14.5]`: ~15 boxes at `r = 0.05 – 0.10` (above)
   - R3 on `[14.5, 15]`: ~10 boxes at `r = 0.05` (above)
   - **Total pilot campaign: ~75 boxes.**
   Legion's rigorous ARB-cap-1 count was 343 (289 R1 + 41 R2 + 13 R3), with
   `best-of-both ~ 107`. The gap between the sampled ~75 and Legion's rigorous
   ~107 is the interval-width tax on the derivative enclosure — a 1.4×
   inflation on average. Both counts stay well under the retracted
   uniform-modulus 232-box figure, and far under the pre-lever 76-day campaign.

## Script

`codex/pilot_r23_box_measurement_2026-10-13.py` — stand-alone, mpmath dps=100,
13.8 s runtime on this laptop.

## Honest unchanged scope

* Sampling, not interval arithmetic — not Lean-admissible certificates.
* R1 ∧ R2 ∧ R3 remain open; the producer-side engineering is unchanged in
  size (the Lean generator transpose of `scripts/emit_box_segment.py`).
* No bearing on the open Riemann Hypothesis.

What the probe adds: numerical confirmation that the centered-form lever
margins hold across all three segments, with concrete `(c, r)` schedules a
certified producer must match. The whole R1 ∧ R2 ∧ R3 feasibility picture is
now self-consistent at this `dps = 100` sampling level.
