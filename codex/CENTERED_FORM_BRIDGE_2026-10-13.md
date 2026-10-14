# Centered-form sign bridge — the Lean half of the lever, 2026-10-13

Author: Pablo Cohen + Claude Opus 4.7 (1M context).

## What landed

`PF/Analytic/CenteredFormBridge_2026_10_13.lean` (268 L). The Lean mean-value
sign bridge. **10 kernel-clean theorems**, every one
`[propext, Classical.choice, Quot.sound]`. Zero project axioms. No `sorry`,
`native_decide`, `axiom`, or `Prop := True`. `autoImplicit` off. Additive.

## What it proves

Converts a certified `(point value, derivative modulus bound)` pair into a
per-box R1/R2/R3 sign over a positive-length closed `t`-box.

**Generic (pure real analysis via mathlib mean-value inequality):**

```
centered_form_pos : 0 ≤ r → (∀ x ∈ [c-r, c+r], HasDerivAt f (f' x) x) →
                   (∀ x ∈ [c-r, c+r], |f' x| ≤ L) → L * r < f c →
                   ∀ t ∈ [c-r, c+r], 0 < f t

centered_form_neg : (dual with f c < -(L*r) → ∀ t ∈ [c-r, c+r], f t < 0)
```

**Edge-function differentiability** (`edgeRe t := Re ξ(1+it)`, `edgeIm t := Im ξ(1+it)`):
- `differentiable_edgeLine`, `differentiable_edgeRe`, `differentiable_edgeIm`
- `hasDerivAt_edgeRe t`, `hasDerivAt_edgeIm t` — derivative values `deriv edgeRe t`,
  `deriv edgeIm t` (opaque; the certified producer supplies bounds, not formulas).

**Per-box R1/R2/R3 specialisations:**

```
R1_box_centered : (Re ξ(1+ic) = Mc) → (|deriv edgeRe x| ≤ L on [c-r, c+r])
                   → L * r < Mc  →  ∀ t ∈ [c-r, c+r], 0 < Re ξ(1+it)

R2_box_centered : analogous for Im ξ, positive sign
R3_box_centered : analogous for Re ξ, negative sign (Mc < -(L*r))
```

## This is the Lean half of the lever

`TBOX_CENTERED_FORM_LEVER_2026-10-10.md` measured the interval-dependency collapse
30–184× on R1/R2/R3 by evaluating `f(t) ∈ f(c) + f'(box)·[-r, r]` instead of the
naive dependency-blown interval formula. `ARB_CERTIFIED_MARCH_2026-10-10.md` ran
the campaign in Arb ball arithmetic — R2 at 41 boxes, R3 at 13 (both centered),
R1 at 289 (needs higher-order Taylor model for full win).

This file is the exact mathematical statement that converts the Arb-demonstrated
`(point value, derivative bound)` pair into a per-box Lean sign claim. No new
math — just mathlib's mean-value inequality `|f(y) - f(x)| ≤ L·|y - x|` applied
on the convex box.

## What this does NOT do (unchanged scope)

* **No producer.** The certified `(Mc, L)` pair for `ξ(1+ic)` and `|deriv edgeRe|`
  is still missing from Lean. Supplying it is the next engineering step — the
  centered-form transpose of `scripts/emit_box_segment.py`, which must emit
  per-box `I` panels AND parallel `I'` panels and assemble `f'(box) = (g'I + gI')/2`
  with phase kept.
* **No new sign claim** on any segment of R1, R2, or R3. The three sign facts
  remain conditional on the absent producer.
* **No bearing on the open Riemann Hypothesis.** `rh_below_15_conditional` is RH
  on one finite rectangle, classically known since Riemann and Gram.

## What it unblocks

The entire Lean side of the centered-form campaign now has a clean, named,
reusable interface. For every box the producer certifies, `R1/R2/R3_box_centered`
fires with four inputs:
1. `hr : 0 ≤ r` (box radius nonnegative)
2. `hvalue : (ξ(1+ic)).re = Mc` or `.im = Mc` (certified center value)
3. `hbound : ∀ x ∈ [c-r, c+r], |deriv edgeRe x| ≤ L` or `edgeIm` (certified derivative bound)
4. `hmargin : L * r < Mc` or `Mc < -(L*r)` (producer-side numeric check)

Each is a cheap `norm_num` or interval-arithmetic consequence once the producer
emits certificates. Chaining per `RightEdgeSignsProof_2026_10_09.forall_Icc_cover`
closes a full segment.

## Dependency / build

```
taskset -c 0,1 lake env lean \
  -o .lake/build/lib/lean/PF/Analytic/CenteredFormBridge_2026_10_13.olean \
  PF/Analytic/CenteredFormBridge_2026_10_13.lean   # 13.9 s, 10 kernel-clean theorems
```

Imports: `PF/Analytic/EdgeSignNeighborhoods_2026_10_13.lean` (new today, 10-13),
`Mathlib.Analysis.Calculus.MeanValue`. No TopUnion import — build closure safe.

## Where this sits in the Rank-1 chain

```
    (future certified producer)
            │
            ▼
    (ξ(1+ic) point value Mc)  +  (|deriv edgeRe| ≤ L on [c-r, c+r])
            │
            ▼
    R{1,2,3}_box_centered    ◄── THIS FILE
            │
            ▼
    per-box R1/R2/R3 sign on [c-r, c+r]
            │   (chain finite cover)
            ▼
    RightEdgeSignsProof_2026_10_09.forall_Icc_cover
            │
            ▼
    R1 ∧ R2 ∧ R3 on their full segments
            │
            ▼
    rh_below_15_conditional   (CAPSTONE, kernel-clean since 10-10)
```

The remaining open distance = the producer. This file closes the Lean-side
arithmetic. The producer is the next piece of real engineering.
