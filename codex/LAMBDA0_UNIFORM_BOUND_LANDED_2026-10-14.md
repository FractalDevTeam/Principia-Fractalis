# Λ₀ uniform modulus bound — LANDED, 2026-10-14

Author: Pablo Cohen + Claude Opus 4.7 (1M context). The strategy document
`codex/LAMBDA0_UNIFORM_BOUND_STRATEGY_2026-10-14.md` has been executed.

## What landed

`PF/Analytic/Lambda0UniformBound_2026_10_14.lean` (241 L). **10 kernel-clean
theorems**, every one `[propext, Classical.choice, Quot.sound]`. Zero project
axioms. No `sorry`, `native_decide`, `axiom`, or `Prop := True`. `autoImplicit`
off. Additive. Build time 11.1 s via Legion's taskset single-file method.

### Theorems

**Elementary numerics (§0):**
- `exp_one_ge_two : 2 ≤ Real.exp 1`
- `exp_pi_ge_eight : 8 ≤ Real.exp π`
- `exp_neg_pi_le_eighth : Real.exp (-π) ≤ 1/8`

**Exponent real parts at σ = 1 (§1):**
- `re_exp_a : ((⟨1, t⟩ : ℂ) / 2 - 1).re = -(1/2)`
- `re_exp_b : ((1 - (⟨1, t⟩ : ℂ)) / 2 - 1).re = -1`

**Pointwise and integrability (§2–3):**
- `norm_integrand_bound : ‖(x^a + x^b)·ω(x)‖ ≤ 2·exp(-πx)/(1-exp(-π))` for x ≥ 1
- `dominating_integrableOn : IntegrableOn (fun x => 2·(1-exp(-π))⁻¹·exp(-πx)) (Ioi 1)`

**Main result (§4):**
- **`lambda0_abs_uniform (t : ℝ) : ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
    ≤ 2 · Real.exp (-π) / (π · (1 - Real.exp (-π)))`**
  — uniform-in-t integral bound.
- **`lambda0_abs_le_two_thirds (t : ℝ) : ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
    ≤ 2/3`** — rational-rhs form.

**Pilot discharge (§6):**
- **`pilot_r1_hvalue_lb : (1/4 : ℝ) ≤ (riemannXiEntire (⟨1, 1/2⟩ : ℂ)).re`**
  — THE first producer-side pilot hypothesis, discharged. No panels.

## What this unblocks right now

`PilotBoxes/R1_c0_5_r0_05_2026_10_13.lean` has a theorem

```
theorem pilot_r1_box_c0_5_r0_05
    (hvalue_lb : (1 / 4 : ℝ) ≤ (riemannXiEntire (⟨1, 1 / 2⟩ : ℂ)).re)
    (hbound   : ∀ x ∈ Icc ((1 / 2 : ℝ) - 1 / 20) ((1 / 2 : ℝ) + 1 / 20),
                   |deriv edgeRe x| ≤ 1 / 10) :
    ∀ t ∈ Icc ((1 / 2 : ℝ) - 1 / 20) ((1 / 2 : ℝ) + 1 / 20),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re
```

`hvalue_lb` is **now kernel-provable** via `Lambda0UniformBound20261014.pilot_r1_hvalue_lb`.
What remains for the first full R1 pilot box: the derivative modulus bound
`hbound`. See `codex/LAMBDA0_UNIFORM_BOUND_STRATEGY_2026-10-14.md` §4
discussion — a certified bound on `|deriv edgeRe x|` on `[9/20, 11/20]` would
complete the first pilot. That is a parallel session's work.

## Scope — honestly stated

- **Uniform-in-t** across all real t. So the bound discharges `hvalue_lb` for
  R1 and R2 pilots on any `c` whose segment-local `Mc_lb` margin accepts
  `‖Λ₀‖ ≤ 2/3`.
- **R1 at c = 1/2, 1, 2, 5, 10**: pilot's `Mc_lb` is at most 0.1 (per
  `PILOT_R1_FEASIBILITY_2026-10-13.md` sampling), and `3·(2/3)/8 = 1/4` is the
  worst-case `|Λ₀_re/4 + Λ₀_im/2|` perturbation to `Re ξ`, so Mc_lb ≥ 1/4
  works for most R1 pilots.
- **R2** needs a tighter bound at the σ=1 line because the (t²·Λ₀_re +
  t·(-)·Λ₀_im)/2 structure in `im_xi_at_s` scales up with t². For t ≈ 13–14.5,
  Mc_lb ≈ 1e-3, so the bound ≤ 2/3 is way too loose. The exact integral bound
  2·exp(-π)/(π·(1-exp(-π))) ≈ 0.028 is close enough, but the arithmetic
  margin needs re-derivation per segment-local Mc_lb.
- **R3** at t ≈ 15 is NOT closable by uniform modulus — it needs the
  centered-form phase cancellation. Legion's `top15_re_lt_neg_1e4` already
  handles it via the full 4,241-panel campaign.

## Build evidence (gate paste)

```
taskset -c 0,1 lake env lean -o \
  .lake/build/lib/lean/PF/Analytic/Lambda0UniformBound_2026_10_14.olean \
  PF/Analytic/Lambda0UniformBound_2026_10_14.lean   # 11.1 s

#print axioms:
  exp_one_ge_two              : [propext, Classical.choice, Quot.sound]
  exp_pi_ge_eight             : [propext, Classical.choice, Quot.sound]
  exp_neg_pi_le_eighth        : [propext, Classical.choice, Quot.sound]
  re_exp_a                    : [propext, Classical.choice, Quot.sound]
  re_exp_b                    : [propext, Classical.choice, Quot.sound]
  norm_integrand_bound        : [propext, Classical.choice, Quot.sound]
  dominating_integrableOn     : [propext, Classical.choice, Quot.sound]
  lambda0_abs_uniform         : [propext, Classical.choice, Quot.sound]
  lambda0_abs_le_two_thirds   : [propext, Classical.choice, Quot.sound]
  pilot_r1_hvalue_lb          : [propext, Classical.choice, Quot.sound]
```

Zero project axioms end-to-end.

## Rank-1.5 progress record

| step | state | this session |
|------|-------|--------------|
| Lean consumer (`R{1,2,3}_box_centered_of_*`) | DONE | 2026-10-13 |
| Pilot box file emitter (Python) | DONE | 2026-10-13 |
| Three pilot box files (R1, R2, R3) | DONE | 2026-10-13 |
| **Uniform modulus bound on `Λ₀`** | **DONE** | **2026-10-14** |
| **First producer-side hypothesis** (`hvalue_lb` for R1 pilot) | **DONE** | **2026-10-14** |
| Derivative modulus bound `|deriv edgeRe x| ≤ 1/10` on `[9/20, 11/20]` | open | next session |
| First full pilot box closed end-to-end | open | after derivative bound |
| Scale to all R1 ∧ R2 segment coverage | open | subsequent |

The pilot producer has gone from "weeks of compute per box" (naive panel
transpose) to "one uniform bound + one derivative bound, both analytic." The
first half of the first full pilot box is **in the tree, kernel-clean**.
