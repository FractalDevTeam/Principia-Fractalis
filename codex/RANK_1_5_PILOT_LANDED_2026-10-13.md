# Rank-1.5 pilot — first three centered-form pilot boxes landed, 2026-10-13

Author: Pablo Cohen + Claude Opus 4.7 (1M context).

## What landed

**Four new kernel-clean theorems**, every one
`[propext, Classical.choice, Quot.sound]`, zero project axioms:

1. `CenteredFormBridge20261013.R1_box_centered_of_lb` — producer-friendly
   lower-bound form (new; the equality form was 10-13 earlier).
2. `CenteredFormBridge20261013.R2_box_centered_of_lb` — ditto for Im ξ.
3. `CenteredFormBridge20261013.R3_box_centered_of_ub` — upper-bound form for
   R3 negativity.
4. Three one-pilot-each specialisations in `PF/Analytic/PilotBoxes/`:
   - `R1_c0_5_r0_05_2026_10_13.lean` — R1 on `[9/20, 11/20]`,
     conservative `(Mc_lb = 1/4, L = 1/10)`.
   - `R2_c27_2_r1_20_2026_10_13.lean` — R2 on `[13.5 ± 0.05]`,
     conservative `(Mc_lb = 1/1000, L = 1/100)`.
   - `R3_c74_5_r1_20_2026_10_13.lean` — R3 on `[14.8 ± 0.05]`,
     conservative `(Mc_ub = -1/2000, L = 1/1000)`.

Plus the generator: **`scripts/emit_centered_pilot_box.py`** (195 L) —
parameterised Lean emitter. Takes `(kind ∈ {R1,R2,R3}, c, r, Mc, L)`,
produces a kernel-clean conditional Lean theorem specialising the matching
`R{1,2,3}_box_centered_of_{lb,ub}` lemma. Builds in 3–5 s per box.

## Scope — unchanged honesty

* **Conditional theorems.** Each pilot takes the two certified-producer
  hypotheses as explicit arguments; the certified panel generator is still the
  remaining piece. The pilots demonstrate the chain is ready to close the
  moment the producer delivers.
* **Three boxes, not three segments.** `R1`, `R2`, `R3` still open on their
  full segments. These three pilots cover a 1/10-wide slice of R1, a 1/10-wide
  slice at the midpoint of R2, and a 1/10-wide slice of R3.
* **Conservative rationals.** The pilot uses `Mc_lb = 1/4, L = 1/10` for R1
  (actual: `Mc ≈ 0.497, L ≈ 0.013`), giving 50× margin headroom. Points: the
  pilot's margin check closes trivially; the producer only needs to beat these
  loose rationals, not match them exactly.
* **No bearing on the open Riemann Hypothesis.** `rh_below_15_conditional` is
  RH on one finite rectangle, classically known since Riemann and Gram.

## Build evidence (gate paste)

```
taskset -c 0,1 lake env lean -o <olean> PF/Analytic/CenteredFormBridge_2026_10_13.lean
  13 declarations, all [propext, Classical.choice, Quot.sound]    18.6 s

python3 scripts/emit_centered_pilot_box.py --kind R1 --c 1/2 --r 1/20 --mc 1/4 --l 1/10
python3 scripts/emit_centered_pilot_box.py --kind R2 --c 27/2 --r 1/20 --mc 1/1000 --l 1/100
python3 scripts/emit_centered_pilot_box.py --kind R3 --c 74/5 --r 1/20 --mc=-1/2000 --l 1/1000

taskset -c 0,1 lake env lean -o <olean> PF/Analytic/PilotBoxes/R1_c0_5_r0_05_2026_10_13.lean
  2 declarations, all [propext, Classical.choice, Quot.sound]    4.7 s
taskset -c 0,1 lake env lean -o <olean> PF/Analytic/PilotBoxes/R2_c27_2_r1_20_2026_10_13.lean
  1 declaration,  all [propext, Classical.choice, Quot.sound]    3.1 s
taskset -c 0,1 lake env lean -o <olean> PF/Analytic/PilotBoxes/R3_c74_5_r1_20_2026_10_13.lean
  1 declaration,  all [propext, Classical.choice, Quot.sound]    3.2 s
```

## Rank-1.5 remaining distance

The emitter templates every per-box Lean file identically. All that varies
across boxes is the four rationals `(c, r, Mc, L)` and the kind. **The
remaining Rank-1.5 engineering = the certified numerical producer** that
discharges `hvalue_lb`/`hvalue_ub` and `hbound` for concrete rationals.

Per Legion's `TBOX_CENTERED_FORM_LEVER_2026-10-10.md` and
`ARB_CERTIFIED_MARCH_2026-10-10.md`, that producer requires:

1. **Certified `(ξ(1 + ic)).re` or `.im` at concrete c** — a theta-quadrature
   point evaluation per box, rational-node interval arithmetic. The 4,241
   t=15 panels are the existing proof-of-feasibility; a per-box center-value
   needs its own fresh panel set, scope ~1,000–1,500 panels per decimal of
   precision at a point.
2. **Certified `|deriv edgeRe x| ≤ L` on `[c - r, c + r]`** — the parallel
   I'-panels (integrand × `(i log u)/2`), assembled on the sum
   `f'(box) = (g'I + gI')/2` to keep phase-cancellation (30–184× tighter than
   naive `|g'||I| + |g||I'|`).

The sampled derivative-magnitude profile in
`PILOT_R1_FEASIBILITY_2026-10-13.md` + `PILOT_R23_FEASIBILITY_2026-10-13.md`
confirms a global uniform `L = 1e-3` works for R2 ∪ R3 and `L = 1e-1` for R1,
so the producer need not refine `L` per box — a single segment-wide bound
suffices for all three sign facts.

## Where this fits in the chain

```
                    (certified panel generator — the next piece)
                            │
                            ▼
                 (hvalue_lb, hbound) producer certificates
                            │
                            ▼
                emit_centered_pilot_box.py  ◄── NEW this session
                            │
                            ▼
         PF/Analytic/PilotBoxes/{R1,R2,R3}_c{...}_r{...}.lean  ◄── NEW this session
                            │
                            ▼
    R{1,2,3}_box_centered_of_{lb,ub}  ◄── NEW this session (CenteredFormBridge extension)
                            │
                            ▼
   R{1,2,3}_box_centered  →  per-box sign  →  forall_Icc_cover
                            │
                            ▼
                    R1 ∧ R2 ∧ R3
                            │
                            ▼
          rh_below_15_conditional   (CAPSTONE, Legion 10-10)
```

The pipeline is now **plumbed end-to-end** modulo the certified panel
generator. Every link but the first is kernel-clean and in-tree. The Rank 1.5
engineering has gone from "a single bottleneck engineering block" to "one
single-point numerical campaign + one derivative-bound numerical campaign,"
both of which the Arb march has shown feasible at day-scale.
