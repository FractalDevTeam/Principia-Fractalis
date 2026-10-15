# Pointwise panel pack for `Re ξ(1+ic) > 0` past the uniform-modulus ceiling

**Date:** 2026-10-15
**Status:** DESIGN LOCKED, implementation starting (next wave)
**Scope:** First kernel-clean R1 pilot at `c > 5.835` (where the uniform `‖Λ₀‖ ≤ 50/1727` route is impossible). Target `c = 6`, box width TBD by Gate 2 margin.

## 0. The hard ceiling we're breaking

The POC + 4-pilot fan-out at commits `d47577f1`, `92f933d4` work up to `c ≈ 5.835`, the point where `c·√(c² + 1)·B = 1` under uniform `B = 50/1727`. Past that, Lambda0DecayCeiling's `gate1_fails_at_of_xi_small` guarantees ANY modulus-only argument gives `|s(s−1)|·B > 1/2`, hence cannot force `|ξ| ≥ 1/4` (or any positive margin via modulus alone). We MUST use real-part estimates — i.e. certified rational-interval enclosures of `Re Λ₀(1+ic)` and `Im Λ₀(1+ic)` at specific c.

## 1. Mathematical path (verified numerically at c=6, N=200 panels)

From the Riemann split of `completedRiemannZeta₀` (Legion's `lambda0_edge_eq_F_integrals`, kernel-clean at `33e18ec9`):

```
   Λ₀(1+ic)  =  ∫₀^∞ F_plus(u)·e^(+icu/2) du  +  ∫₀^∞ F_minus(u)·e^(−icu/2) du
```

where `F_plus(u) = Real.exp (u/2) · omega (Real.exp u)` and `F_minus(u) = omega (Real.exp u)`. Taking real and imaginary parts:

```
   Re Λ₀(1+ic)  =  ∫₀^∞ (F_plus(u) + F_minus(u)) · cos(cu/2) du
   Im Λ₀(1+ic)  =  ∫₀^∞ (F_plus(u) − F_minus(u)) · sin(cu/2) du
```

Combined with Lambda0DecayCeiling's `lambda0_mul_eq_two_xi_sub_one`:

```
   Re ξ(1+ic)  =  (1 − c²·Re Λ₀(1+ic) − c·Im Λ₀(1+ic)) / 2
```

Gate 1 at c=6 with `Mc_lb = 1/8` ⟺ `36·Re Λ₀(1+6i) + 6·Im Λ₀(1+6i) ≤ 3/4`.

## 2. Numerical confirmation (Agent B, 2026-10-15)

200 adaptive panels (quadratic density, `u_k = 5·(k/N)²`) in pure-`Fraction` interval arithmetic deliver:

```
   Re Λ₀(1+6i)  ∈  [0.015 322 848 935 968,  0.016 604 032 410 144]    width ≈ 1.28·10⁻³
   Im Λ₀(1+6i)  ∈  [0.000 561 108 935 596,  0.001 302 220 023 779]    width ≈ 7.41·10⁻⁴

   36·R_ub + 6·I_ub  =  0.605 558 5
   Gate 1 margin at Mc_lb = 1/8 :  0.144 441 5 > 0.125  →  CLOSES WITH SLACK 0.019
```

Ground-truth (mpmath, non-certifying): `R ≈ 0.015 964`, `I ≈ 0.000 923`. Both inside the certified intervals, confirming the Python generator's enclosure is faithful.

Deliverable: `/tmp/panel_c6_v1.py` (643 lines, pure Fraction, 13 s runtime).

## 3. Lean implementation decomposition (Agents A + C synthesis)

### 3.1 Reusable from r120 (`PF/Analytic/XiPanelsT15/` + `XiOnLineZeroCoreT15`)

* **Interval type + arithmetic** — vendored `Interval` with `Interval.approx_le` trimming to real inequalities.
* **Panel folding abstraction** — `nodeFold15 n U H` as a recursive panel-sum enclosure; parameterise over integrand.
* **Aggregation plumbing** — `nodeSum15_split` (manual partition lemma) + `linarith` to compose chunks.
* **Integral assembly** — mathlib's `intervalIntegral.sum_integral_adjacent_intervals` composes per-panel integral bounds into a total enclosure (`PF/Analytic/XiOnLineZeroT15.lean` uses this pattern via `integral_add_adjacent_intervals`).
* **Decide-kernel closure** — each panel brick closed by `decide +kernel` (NOT `native_decide`; the three-axiom bar is preserved). r120's 165 bricks of this form are the template.
* **Generator script skeleton** — `scripts/gen_r120_panels_t15.py` emits SegXXPY.lean + SegXX.lean + ChunkTable; mpmath dps = 100 with `floor(x · 10^10) / 10^10 − 1 ULP` safety backoff. Panel geometry hard-coded as a `SEGMENTS` table.

### 3.2 Must be built new

(a) **Node functions for the two Fourier integrands.** In Lean:
```
   nodeR_fourier_plus_at_c  (u c : ℝ) : ℝ  :=  (F_plus u + F_minus u) · Real.cos (c · u / 2)
   nodeR_fourier_minus_at_c (u c : ℝ) : ℝ  :=  (F_plus u − F_minus u) · Real.sin (c · u / 2)
```
Note: `F_plus`, `F_minus` already in `OmegaDerivative_2026_10_14.lean` (Legion). The node-level functions above are new.

(b) **Interval mirrors** `nodeI_fourier_plus_at_c`, `nodeI_fourier_minus_at_c` using the vendored `Interval` arithmetic.

(c) **Conservativity lemmas** `nodeR_fourier_plus_at_c_mem_approx` (real values lie in the interval mirror) — follows r120's `nodeR15_mem_approx` pattern, modified for the new node definitions.

(d) **C² (K) bounds.** r120 computed `K0(15), K1(15), K2(15)` via `nlinarith`. We need analogous bounds `K_plus(c)` and `K_minus(c)` for the Fourier integrands' second derivatives, valid at the specific rational c in use. These let us bound per-panel errors.

(e) **Dual enclosures (lower AND upper per panel)** — r120 only proved lower bounds (one-sided for Xi(15) > 0). We need both: Gate 1 needs upper bounds on `Re Λ₀` and `Im Λ₀` (bounding `c²R + cI` above), and the method is cleaner with both lower and upper. Each per-panel brick becomes TWO `decide +kernel` theorems (`s_lo` and `s_hi`).

(f) **Python generator** — fork `scripts/gen_r120_panels_t15.py` → `scripts/gen_fourier_panels_c.py`, parameterised by rational `c`. Reuse `SEGMENTS` table verbatim (adaptive density matches). Emit both lower and upper per-panel brick statements. Use the already-prototyped Fraction-interval primitives from `/tmp/panel_c6_v1.py`.

(g) **Tail bounds** — explicit rational tail bound for `|∫_U^∞|`, both integrands. Super-exp decay from Legion's `F_plus_le_exp_bound` and `F_minus_le_exp_neg_pi_mul` makes this ~2 Lean lemmas.

(h) **The pilot module itself** — composes (a)–(g) into Gate 1 at `c = 6`, pairs with pilot-era Gate 2 (uniform-bound L=1 for `|t| ≤ 6 + r`), passes `R1_box_centered_of_lb` to produce `∀ t ∈ [6 − r, 6 + r], 0 < Re ξ(1+it)`.

## 4. Session-realistic scope

The agents concur: 3–4 weeks to build the full Fourier pack. For THIS session, scope back to the first "demonstration brick" — not a full pilot, just:

* **Milestone M1.** Lean definitions of `nodeR_fourier_plus_at_c`, `nodeR_fourier_minus_at_c` + interval mirrors + the conservativity lemmas. Compiles kernel-clean. ONE module, no panels yet.
* **Milestone M2.** A SINGLE panel brick for ONE segment (e.g. `s01c01_plus_lo`, `s01c01_plus_hi`, `s01c01_minus_lo`, `s01c01_minus_hi`) at c=6, closed by `decide +kernel`. Four theorems, demonstrating the method lands.
* **Milestone M3 (defer):** 165 panels × 4 bricks each = 660 bricks, aggregated into the two integral enclosures. The pilot itself.

M1 + M2 is the realistic session goal — foundation + proof-of-concept-brick that the generator can then multiply.

## 5. Dispatch plan for the next wave

Legion fan-out, running concurrently (no overlapping files):

* **Agent D — Node definitions + mirrors.** Build `PF/Analytic/FourierPanels/CoreDefs_c6_2026_10_15.lean` with the two node functions, their interval mirrors, and `_mem_approx` conservativity lemmas. Target: compiles kernel-clean, 4–8 kernel-clean theorems. Blocked by: nothing (purely new file).

* **Agent E — Generator script.** Fork `scripts/gen_r120_panels_t15.py` → `scripts/gen_fourier_panels_c6.py`. Reuse the Fraction-interval primitives from `/tmp/panel_c6_v1.py`. Output: ONE segment file (`FourierPanels/Seg01P1_c6.lean`) with 4 `decide +kernel` bricks matching M2. Blocked by: Agent D's node definitions, imported.

* **Agent F — Aggregation skeleton.** Write `PF/Analytic/FourierPanels/Assemble_c6_2026_10_15.lean` that will IMPORT the segment files and aggregate panel sums into `R_lb ≤ Re Λ₀(1+6i) ≤ R_ub`, `I_lb ≤ Im Λ₀(1+6i) ≤ I_ub`. For M1+M2, this can be a skeleton with placeholder theorems; filled in M3. Blocked by: Agent D's definitions.

Pilot module itself: deferred to a later session once M3 is complete.

## 6. Standing rules observed

* No `native_decide`. All kernel-decide bricks (r120 standard).
* No fudging numerics — `/tmp/panel_c6_v1.py` is end-to-end `Fraction`.
* No AI public replies.
* No mathlib pushes.
* No files committed in this plan (design doc only).
* The three-axiom bar `[propext, Classical.choice, Quot.sound]` audited on every new declaration before any commit.

## 7. References

* `PF/Analytic/XiPanelsT15/Seg05P2.lean` — representative panel brick (Agent C audit).
* `PF/Analytic/XiOnLineZeroCoreT15.lean` — `nodeSum15_split`, interval mirrors, aggregation pattern.
* `PF/Analytic/XiOnLineZeroT15.lean` — final integral assembly (`int_lower_15`, `Xi_15_pos`).
* `scripts/gen_r120_panels_t15.py` — generator provenance.
* `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1016-1035` — `sum_integral_adjacent_intervals` (Agent A).
* `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:919` — `norm_integral_le_integral_norm` (Agent A).
* `/tmp/panel_c6_v1.py` — Agent B's Fraction-arithmetic panel prototype (not committed).
* This document.
