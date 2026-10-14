# 🎉 FIRST FULL CENTERED-FORM PILOT BOX — CLOSED END-TO-END, 2026-10-14

Author: Pablo Cohen + Claude Opus 4.7 (1M context).

## The result

`PilotBoxes/R1_c0_5_r0_05_L2_2026_10_14.pilot_r1_box_c0_5_r0_05_L2_closed`:

```
theorem pilot_r1_box_c0_5_r0_05_L2_closed :
    ∀ t ∈ Icc ((9 : ℝ) / 20) (11 / 20),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re
```

**Zero hypotheses. Zero project axioms. `[propext, Classical.choice, Quot.sound]`.**

R1 holds unconditionally on the positive-length segment `t ∈ [9/20, 11/20]` of
the right edge, via the centered-form Lean bridge discharged by uniform
analytic bounds — **no panels, no quadrature infrastructure for new t-values.**

## This cycle landed 10 new kernel-clean theorems

`PF/Analytic/EdgeReDerivBound_2026_10_14.lean` (203 L), build 13.0 s:

- `norm_le_abs_re_add_abs_im` — triangle `‖z‖ ≤ |z.re| + |z.im|`
- `norm_two_s_minus_one_le t : ‖2·(⟨1,t⟩) - 1‖ ≤ 1 + 2·|t|`
- `norm_s_mul_s_minus_one_le t : ‖(⟨1,t⟩)·((⟨1,t⟩) - 1)‖ ≤ t² + |t|`
- `hasDerivAt_edgeLine_at t : HasDerivAt (fun s => ⟨1, s⟩) I t`
- `deriv_riemannXiEntire_at t` — the ξ product rule:
    `deriv ξ (⟨1,t⟩) = ((2s-1)·Λ₀(s) + s(s-1)·Λ₀'(s)) / 2`
- `norm_deriv_riemannXiEntire_le_at (|t| ≤ 11/20) : ‖deriv ξ (⟨1,t⟩)‖ ≤ 2`
- `deriv_edgeRe_eq t : deriv edgeRe t = (deriv ξ (⟨1,t⟩) · I).re`  — chain rule
- `abs_deriv_edgeRe_le_at (|t| ≤ 11/20) : |deriv edgeRe t| ≤ 2`
- `pilot_r1_hbound : ∀ x ∈ Icc (9/20) (11/20), |deriv edgeRe x| ≤ 2`

`PF/Analytic/PilotBoxes/R1_c0_5_r0_05_L2_2026_10_14.lean` (56 L), build 3.6 s:

- `pilot_r1_box_c0_5_r0_05_L2_closed` — THE PILOT, zero hypotheses.

## Chain

```
Lambda0UniformBound_2026_10_14.pilot_r1_hvalue_lb (Mc_lb = 1/4)
       │
       ├──── CenteredFormBridge_2026_10_13.R1_box_centered_of_lb
       │        with c=1/2, r=1/20, L=2, Mc_lb=1/4; margin L·r=1/10 < 1/4 ✓
       │
       └──── EdgeReDerivBound_2026_10_14.pilot_r1_hbound (L = 2)
       │
       ▼
pilot_r1_box_c0_5_r0_05_L2_closed  ◄── zero hypotheses, kernel-clean
       │
       ▼
∀ t ∈ Icc (9/20) (11/20), 0 < Re ξ(1 + it)
```

The entire chain is 7 modules (R1Neighborhood_2026_10_09, EdgeSignNeighborhoods,
CenteredFormBridge, Lambda0UniformBound, Lambda0PrimeUniformBound,
EdgeReDerivBound, PilotBoxes/R1_c0_5_r0_05_L2), all kernel-clean, all built
via Legion's taskset single-file method.

## Scope — unchanged honesty

- **One box, not R1.** This closes R1 on `[9/20, 11/20]`, a 1/10-wide slice.
  R1 remains open on the rest of `[0, 13]`. Scaling the same recipe
  (point-value + derivative bound per box) is a batched campaign.
- **Loose L bound.** `L = 2` is 150× looser than the sampled true value
  `|deriv edgeRe x| ≈ 0.013` on `[9/20, 11/20]`. Tighter `L` enables wider
  boxes; same analytic machinery with sharpened `‖Λ₀‖ ≤ 2/21` + differentiated
  Mellin for `‖Λ₀'‖` closes `L ≈ 1/15` or so, enabling r → 1/5 boxes.
- **No bearing on the open Riemann Hypothesis.** `rh_below_15_conditional` is
  RH on one finite rectangle, classically known since Riemann and Gram.
- **Not R2 or R3.** R2's `Mc_lb ~1e-3` requires tighter `‖Λ₀‖` bound; R3 near
  t=15 requires phase cancellation (centered form at those t), which Legion's
  panel infrastructure handles.

## Rank-1.5 progress record

| step | status | session |
|------|--------|---------|
| Lean consumer (`R{1,2,3}_box_centered_of_*`) | DONE | 2026-10-13 |
| Pilot box emitter (Python) | DONE | 2026-10-13 |
| `‖Λ₀(1+it)‖ ≤ 2/3` uniform | DONE | 2026-10-14 |
| `pilot_r1_hvalue_lb : 1/4 ≤ Re ξ(1+i/2)` | DONE | 2026-10-14 |
| `‖Λ₀(z)‖ ≤ 2/3` on strip σ ∈ [0, 2] | DONE | 2026-10-14 |
| `‖deriv Λ₀ (1+it)‖ ≤ 2/3` (Cauchy) | DONE | 2026-10-14 |
| ξ product rule `deriv ξ (⟨1,t⟩) = …` | DONE | 2026-10-14 (now) |
| Chain rule `deriv edgeRe = Re(deriv ξ · I)` | DONE | 2026-10-14 (now) |
| `|deriv edgeRe x| ≤ 2` on `[9/20, 11/20]` | DONE | 2026-10-14 (now) |
| **FIRST FULL PILOT BOX, R1 on `[9/20, 11/20]`** | **DONE** | **this cycle** |
| Scale to full R1 segment | open | subsequent sessions |
| Tighter `L` for wider boxes | open | optional |
| R2 pilot | open | needs tighter `‖Λ₀‖` |
| R3 pilot | open | needs centered-form panels |

**The Rank-1.5 pilot producer has delivered its first unconditional pilot box
on R1.** The recipe generalises to all R1 (fewer boxes if `L` tightened); R2
needs tighter uniform bounds (one more session), R3 needs the phase-cancelling
panels (separate campaign).
