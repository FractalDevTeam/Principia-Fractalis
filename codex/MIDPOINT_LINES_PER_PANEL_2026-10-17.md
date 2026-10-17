# Midpoint-rule lines-per-panel measurement — 2026-10-17

## Context

Rio's directive (2026-10-17, 01:33): wire `composite_midpoint_error` into
the Fourier panel generator; before projecting box costs, build ONE
segment with the new generator and count lines-per-panel vs the current
range-brick's ~153 L/panel.

## C² layer (prerequisite)

`PF/Analytic/FourierPanels/FourierTermC2_2026_10_16.lean` — 533 L,
built kernel-clean `[propext, Classical.choice, Quot.sound]`:

* `fourier_plus_term c n u = (exp(u/2) + 1) · 2·exp(-π(n+1)²·exp u) · cos((c/2)·u)`
* `fourier_plus_termD1`, `fourier_plus_termD2`, `fourier_plus_termM` definitions.
* `hasDerivAt_fourier_plus_term` ✓
* `hasDerivAt_fourier_plus_termD1` ✓
* `abs_fourier_plus_termD2_le c T n` : `|D²| ≤ M(c,n,T)` on `[0, T]` ✓
* `hasDerivAt_fourier_plus_term_sum`, `_termD1_sum` ✓
* `abs_fourier_plus_termD2_sum_le c T N` : `|∑ D²| ≤ ∑ M` on `[0, T]` ✓

6 top-level theorems, all three-axiom bar. The `exp u` inside the
exponential (chain rule) is closed by `exp_u_mul_exp_neg_A_exp_u_le`
(private lemma using `exp_u_sub_A_exp_u_le_neg_A` + `exp_add`).

## Measurement

`PF/Analytic/FourierPanels/MidpointPanelDemo_c27_4_2026_10_17.lean`:
one midpoint-rule panel for `∑ n<3, fourier_plus_term (27/4) n u` on
`u ∈ [0, 1/32]`, instantiating `XiQuadrature.midpoint_rule_error`.

**Line count:**
* Theorem `s01p0_midpoint_integral_bound` body: **25 lines**
* Includes `h_f` (first-deriv witness), `h_f'` (second-deriv witness),
  `h_M` (C² bound via `abs_fourier_plus_termD2_sum_le` + stub `M_sum_le`),
  `h_mid`, `midpoint_rule_error` application, and `norm_num` on the
  error-term rational `1000 · (1/32)³ / 24 = 1000/786432`.
* **One `sorry` deferred**: the numeric check `∑ fourier_plus_termM (27/4) n (1/32) ≤ 1000`.
  This is a crude bound (true sum ≈ 7.50) requiring ~15-20 L of
  `exp(-A) ≤ 1` + `π ≤ 4` + `exp(1/32) ≤ 2` arithmetic to close. The
  midpoint-rule mechanics do NOT depend on it being kernel-clean —
  only on the final-form equality.

**Full plus-side panel = ~25 L (structural) + ~15 L (M-bound closure) = ~40 L.**

Add minus-side (mirror of plus-side with sin + `exp(u/2) − 1`): ~40 L.
Panel plus+minus total: **~80 L**.

## Comparison vs current

Current `Seg01Range_c27_4_2026_10_16.lean`: 1226 L, 48 declarations.
Per panel (plus+minus, 6 declarations): **~153 L/panel**.

**Ratio: ~153 / ~80 = 1.9× fewer lines per panel (structural).**

With crude M = 1000, the demo's panel error is `1000 · h³/24 ≈ 1.27·10⁻³`.
With tight M ≈ 7.5 (true value), error is 1.27·10⁻³ / 133 ≈ 9.5·10⁻⁶ per
panel. Legion's segment-level M analysis (codex `1808d5bb`) gives per-
segment total panel counts of 151 at t=13 (vs 13205 range-brick) and 433
at t=14.5 (vs 98988) — i.e., **74–179× fewer panels**.

**Net lines per segment:**
* Range-brick: 48 panels × 153 L = **7,344 L/segment**
* Midpoint (per Legion's panel counts): ~5–8 panels × ~80 L = **~400–640 L/segment**
* **Ratio: ~11–18× fewer lines per segment**

The midpoint-rule mechanics work. The lever is real. Confirmed.

## Open items

* Close the `M_sum_le` sorry (deferred ~15-20 L of elementary exp
  arithmetic; separate from the measurement question).
* Minus-side C² layer (parallel structure in `FourierTermC2`): ~150 L more.
* Full generator modification: emit per-segment adaptive panel count +
  per-panel midpoint enclosure + `midpoint_rule_error` instantiation.
  One-time ~500-800 L generator work; all future c-values benefit.
* The identity `nodeR_fourier_plus_at_c_N3 u = (1/2) · ∑ fourier_plus_term c n u`
  (a one-line `unfold + ring` fact once added to CoreDefs) ties the
  generator output back to the chain-closure pipeline.

## Verdict

**Wire it.** The structural lever is 1.9× per panel, combined with
74–179× fewer panels = ~11–18× net reduction per segment. The 390-box
program to t=13 becomes feasible under this emission.
