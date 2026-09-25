# DISPATCH RESULTS LEDGER — 2026-08-30

One line per landed theorem. Margins are EXACT rationals; decimals are diagnostic.
Axiom status "clean" = exactly [propext, Classical.choice, Quot.sound].

## BOX 0 — sigma in [1/2, 9/16] — CLOSED

| theorem | margin / value | axioms | landed |
|---|---|---|---|
| `top15_box0_re_lt_neg_1e4` | unconditional, no numeric hypotheses | clean | 2026-08-30 15:35 |
| `RE_MARGIN_pos` | 19564553848401467842464431639/4403368995751841955840000000000 - 2221/500000 = +1.087524e-06 | clean | 15:35 |
| `IM_LO_MARGIN_pos` | +6.264311e-05 | clean | 15:35 |
| `IM_HI_MARGIN_pos` | +2.589050e-05 | clean | 15:35 |
| `box0_re_enclosure` / `box0_im_enclosure` | r331a structures, sigma-generic | clean | 15:35 |
| `finite_re_lower/upper`, `finite_im_lower/upper` | 40-segment cumulative, [1,5] | clean | 15:35 |
| `re/im_join_1..39` (78) | sigma-universal, reusable by all boxes | clean | 15:35 |
| `box0_envelope_le` | section-8 envelope <= 1/5000000 (no hypotheses) | clean | 15:34 |
| Full audit | 31/31 endpoints | clean | 15:40 |

Upstream: 188/188 panels, 40/40 segments, 0 nonzero RC, 8h43m.

## INFRASTRUCTURE — landed

| artifact | status | landed |
|---|---|---|
| `PF/Analytic/RiemannXiBoxParametric.lean` | RC=0 first try; 264 lines; sections P.0-P.5 | 2026-08-30 16:20 |
| `pow_sum_mono`, `pow_diff_mono` | amplitude monotonicity at free exponents | clean |
| `box_pow_sum_lb/ub`, `box_pow_diff_lb/ub` | sigma-uniform enclosures at arbitrary endpoints | clean |
| `box_a1/a2_range`, `box_a_pow_bounds` | p1=(1+shi)/2, p2=p1(p1+1) | clean |
| `abs_realThetaRe/ImIntegrandND2_le_box` | box-parametric C2 bound | clean |
| `box_re/im_midpoint_error_on_segment` | box-parametric quadrature wrappers | clean |
| `scripts/emit_box_segment.py` | box-parametric generator; regression vs box 0: 96 nodes, 0 mismatches | 16:37 |

## BOX 2 — sigma in [5/8, 11/16] — BUILDING

Launched 2026-08-30T16:40:59-04:00. Predictions under test:
RE_LO 4.440739e-03 | IM_LO 3.651406e-05 | IM_HI 1.474846e-04 | RE margin +2.861917e-05

| event | detail |
|---|---|
| `Box2Seg40M` | RC=0 (smoke) |
| `Seg40P1` | RC=0, 145.64 s, 9.98 GB, 0 errors (architecture stress test) |

## PENDING

17-strip manifest over [9/16, 1], all RE-positive, weakest strip 6 [13/16,27/32] +2.267028e-05.
Union theorem, boundary chain, count identity.

NO PUSH until r331b release threshold.

## BOX 2 — sigma in [5/8, 11/16] (manifest strip 1) — PANELS GREEN

Relaunched 2026-08-30T19:38:50-04:00 after two aborted attempts (16:40 run died at
Seg01 on a generator defect; 19:04 run superseded). Completed 2026-08-31T06:01:19-04:00.

| metric | value |
|---|---|
| targets | 268/268 RC=0 |
| segments | 40/40 COMPLETE |
| panels | 228/228 olean |
| wall clock | 10 h 22 min |
| peak RSS | 12.63 GB (single lake job, serialized) |
| failures | 0 |
| driver log | /tmp/r331b_logs/box2_mass3.log |

**Discriminating experiment SETTLED.** The rival sweep (scripts/gen_r331b_box_panels.py)
predicted boxes 1-7 FAIL at width 1/16. The kernel built box 2 at width 1/16 with zero
errors. The regression-verified emitter sweep is CORRECT; the rival recon is refuted for
this box.

**Verdict status: PARTIAL.** The 40 segment enclosures
(`box2_seg{01..40}_re/im_integral_lower/upper`) are kernel-green. The three exact margins
(RE, IM_LO, IM_HI) are NOT yet kernel-extracted — they require a
`PF/Analytic/RiemannXiBox2Bridge.lean` capstone chaining the 40 segments through the
sigma-universal `re/im_join_1..39` (already green, reusable from box 0) plus a box-2
envelope bound. That capstone does not exist yet. No axiom audit has been run for box 2.

Predicted (manifest v2, emitter-driven, Gate-B clean): RE margin +2.839068e-05.
Not to be quoted as a result until the bridge lands.

## BOX INDEX -> MANIFEST STRIP MAP (resolved 2026-08-31)

Panel files encode `thetaPowTermM 15 p1 p2 L` with **p1 = (1 + sigma_hi)/2**, p2 = p1(p1+1).
Decode sigma_hi = 2*p1 - 1. Verified against strip_manifest_v2.json for all 18 boxes.

| box dir | p1 | sigma_hi | manifest strip |
|---|---|---|---|
| Box0 | 25/32 | 9/16 | (below manifest; [1/2,9/16]) CLOSED |
| Box100 | 13/16 | 5/8 | strip 0 |
| Box2 | 27/32 | 11/16 | strip 1 |
| Box102..Box116 | (100+k pattern) | | strip 2..16 |

Rule: **Box(100+k) = strip k**, EXCEPT strip 1, which was built under the name `Box2`.
There is no Box101 directory. Do not assume Box106 = strip 6 by name alone — it is
strip 6 by decode (p1=59/64 -> sigma_hi=27/32 -> [13/16,27/32]), which is the weakest strip.

## LEGION RESTART — 2026-08-31

Legion (Windows host) restarted; the driving session and its WSL build died. Recovery:

| item | state |
|---|---|
| public HEAD | 96c71da7 unchanged — NO PUSH holds |
| box 0 | CLOSED, untouched |
| box 2 | completed before the restart (06:01), panels intact |
| Legion WSL tree | survived the VHD move to D:\wsl\Ubuntu; mathlib 6866 oleans intact |
| competing agents | none — no lake/lean processes on Acer at recovery time |

Relaunched 2026-08-31T18:2x:
- **Legion WSL**: strip 6 / Box106 (weakest, +2.211197e-05), systemd transient unit
  `pf-box106`, log /home/xluxx/pf-worker/logs/box106_mass.log
- **Acer**: `scripts/strip_queue.sh` over the remaining 15 strips weakest-first
  (105 104 103 102 116 115 114 100 113 112 111 110 109 108 107), systemd user unit
  `pf-strip-queue`, log /tmp/r331b_logs/strip_queue.log, linger enabled

Both units are PID-1 owned so they survive SSH logout and session teardown.

## BOX 2 — sigma in [5/8, 11/16] (manifest strip 1) — **CLOSED** 2026-08-31

Bridge generated by `scripts/emit_box_bridge.py` (new, box-parametric) and elaborated
2026-08-31 18:5x. Panels were already green from the 19:38 -> 06:01 mass build.

| stage | result |
|---|---|
| panels | 268/268 RC=0, 40/40 segments, 10 h 22 min, peak 12.63 GB |
| `RiemannXiBox2Bridge` | RC=0, **66.83 s**, peak 4.22 GB |
| `RiemannXiBox2BridgeAudit` | RC=0, 38.88 s, peak 3.78 GB |
| axiom audit | **19/19 clean** — `[propext, Classical.choice, Quot.sound]` |
| `sorryAx` / `ofReduceBool` | none |

### Headline figure

**xi-space margin: +2.839063e-05** (against the -1/10000 top-edge target).

This is the figure to quote for this box.

### The three exact margins (internal enclosure check -- NOT the headline)

These are Lambda-space margins of the certified endpoints against the DECLARED box
bounds. They sit near 1e-13 **by construction**, because the declared bounds are
outward-rounded at 1e-12 -- that is the rounding step, not a measure of tightness.
Quoted without that context they misread as knife-edge, when the consumer-facing
margin above is healthy.

Certified Lambda-0 endpoints are the 40-segment cumulative chains with the section-8
envelope applied exactly once (`box0_envelope_le`, reused verbatim — it has no
hypotheses and no sigma). Declared box bounds are outward-rounded at 1e-12.

| theorem | exact value | margin |
|---|---|---|
| `RE_MARGIN_pos` | `27934588365869776741120603796125841251144731925793/6290527136788345651200000000000000000000000000000000` - `4440738869/1000000000000` | **+4.823905e-13** |
| `IM_LO_MARGIN_pos` | `228926098507768092155771924125841251144731925793/6290527136788345651200000000000000000000000000000000` - `9098049/250000000000` | **+3.183275e-13** |
| `IM_HI_MARGIN_pos` | `108841967/500000000000` - `1369346689321392824635617003874158748855268074207/6290527136788345651200000000000000000000000000000000` | **+7.548573e-13** |

Certified `RE_LO` ~ 4.440738869482e-03, `IM_LO` ~ 3.639219631833e-05,
`IM_HI` ~ 2.176839332451e-04.

### Capstone

`top15_box2_re_lt_neg_1e4` — unconditional, no numeric hypotheses:

    Re xi(sigma + 15i) < -1/10000   for all sigma in [5/8, 11/16]

via `box2_re_xi_le : ... <= -13147200071/102400000000000` (~ -1.283906257e-04),
built from `box2_re_enclosure` / `box2_im_enclosure` through the r331a generic
consumer `re_xi_upper_bound_from_enclosures`.

xi-space margin against the -1/10000 target: **+2.839063e-05**.

### Reconciliation with manifest v2

The kernel-certified `RE_LO` is **bit-for-bit identical** to the rational that
manifest v2 predicted for strip 1. The xi margin differs from the prediction by
-5.492e-11, which is exactly the cost of outward-rounding the declared box bounds at
1e-12 (|Ahi|+Bsel)/2 / 1e12 ~ 1.2e-10. The emitter and the kernel agree.

This is the second independent confirmation that the regression-verified emitter sweep
is correct and the rival `gen_r331b_box_panels.py` sweep (which predicted boxes 1-7 fail
at width 1/16) is wrong.

## INFRASTRUCTURE — `scripts/emit_box_bridge.py` landed 2026-08-31

Box-parametric bridge generator. Converts a BUILT box into a CLOSED box with no
hand-written Lean. Emits, in the literal r331a structures:

- Section B.3 — four cumulative chains over [1,5] (`finite_re/im_lower/upper`),
  40 segments each, joined in geometric order.
- Section B.5 — four Lambda-0 bounds, section-8 envelope applied EXACTLY ONCE.
- Section B.6 — three exact rational margin theorems.
- Section B.7 — coefficient enclosures, `BoxReEnclosure` / `BoxImEnclosure` witnesses,
  and the unconditional capstone via `re_xi_upper_bound_from_enclosures`.

It does NOT re-emit the 39+39 adjacency joins, the two integrability lemmas, or the two
Ioc rewrites — those are sigma-universal and are imported from box 0's bridge with a
selective `open` (so box 0's own `finite_*` names cannot shadow the new ones).

Safety properties, all enforced before a single line is written:

- sigma is DECODED from `p1 = (1 + sigma_hi)/2` in the M certificate and cross-checked
  against every one of the 40 segment files' hypotheses. The box directory number is
  never trusted. `p2 = p1(p1+1)` is verified as a second check.
- Segment endpoints must tile [1,5] with no gap, starting 1/1 and ending 5/1.
- Every segment must satisfy lower <= upper (this gate caught a real sign bug in the
  numeral parser during development, before it could reach the kernel).
- The **B-endpoint soundness trap** is resolved at generation time from the sign of the
  declared `IM_LO`: `Bsel = Bhi` when `IM_LO < 0`, `Blo` when `IM_LO >= 0`. Never assumed.
- Refuses to emit unless `Ahi < 0`, `Blo >= 0`, `RE_LO > 0`, `RE_HI <= 1`, all three
  margins positive, and the xi margin positive. A box that does not close produces a
  GATE FAILED diagnosis, not a Lean file.
- Refuses box 0 outright: box 0's hand-written bridge is the reference, not a target.

`scripts/strip_queue.sh` now runs the generator plus `lake build` of the Bridge and
BridgeAudit after each strip's panels go green, so **closure follows build automatically**
for every remaining strip.

## LEDGER CONVENTION — margins (set 2026-08-31)

**Quote the xi-space margin as the headline figure for every box.** It is the
consumer-facing quantity: the slack in `Re xi(sigma+15i) < -1/10000` over the box.

The Lambda-space `RE_MARGIN_pos` / `IM_LO_MARGIN_pos` / `IM_HI_MARGIN_pos` values are an
INTERNAL enclosure check — the certified endpoint against the declared box bound. They
sit at ~1e-13 for every box by construction, because `emit_box_bridge.py` outward-rounds
the declared bounds at 1e-12. That number is the rounding step; it is not tightness, and
quoting it as "the margin" would misread a healthy box as knife-edge.

`scripts/emit_box_bridge.py` now prints the xi margin FIRST and tags it `[HEADLINE]`,
and tags the Lambda-space line as the internal check, so the per-strip ledger lines that
`strip_queue.sh` appends carry this framing automatically.

Reference values, box 2 (strip 1): headline xi margin **+2.839063e-05**; internal
Lambda-space RE +4.823905e-13, IM_LO +3.183275e-13, IM_HI +7.548573e-13.
| box 105 | 40/40 segments green | 630 min | xluxx-Nitro-AN515-58 | 2026-09-01T05:29:08-04:00 |
| box 105 | **CLOSED**   xi bound M = -1.521543088e-04   xi margin +5.215431e-05  [HEADLINE]  (Bsel=135/16, IM_LO >= 0)   MARGINS [internal Lambda-space enclosure check, NOT the headline; ~1e-13 is the 1e-12 rounding of the declared bounds, not tightness]  RE +2.924044e-13   IM_LO +3.911139e-13   IM_HI +3.235175e-13  | audit 19 clean | xluxx-Nitro-AN515-58 | 2026-09-01T05:30:54-04:00 |
| box 104 | 40/40 segments green | 648 min | xluxx-Nitro-AN515-58 | 2026-09-01T16:19:09-04:00 |
| box 104 | **CLOSED**   xi bound M = -1.827551276e-04   xi margin +8.275513e-05  [HEADLINE]  (Bsel=15/2, IM_LO >= 0) |   MARGINS [internal Lambda-space enclosure check, NOT the headline; ~1e-13 is the 1e-12 rounding of the declared bounds, not tightness]  RE +5.849782e-13   IM_LO +5.985268e-13   IM_HI +6.922009e-13 | audit 19 | xluxx-Nitro-AN515-58 | 2026-09-01T16:20:55-04:00 |
| box 103 | FAILED at PF.Numerics.Box103Seg01M | 0 min | xluxx-Nitro-AN515-58 | 2026-09-01T16:21:20-04:00 |
| box 102 | FAILED at PF.Analytic.RiemannXiBox102Panels.Seg01P2 | 4 min | xluxx-Nitro-AN515-58 | 2026-09-01T20:20:49-04:00 |
| box 102 | FAILED at PF.Numerics.Box102Seg01M | 0 min | xluxx-Nitro-AN515-58 | 2026-09-01T20:22:49-04:00 |
| box 106 | **CLOSED** panels+bridge built on Legion, artifacts synced, **re-audited on the production tree** — xi margin +2.211191e-05 | audit 19 clean | xluxx-Nitro-AN515-58 | 2026-09-01T20:29:09-04:00 |
| box 102 | 40/40 segments green | 643 min | xluxx-Nitro-AN515-58 | 2026-09-02T07:11:12-04:00 |
| box 102 | **CLOSED**   xi bound M = -2.465593886e-04   xi margin +1.465594e-04  [HEADLINE]  (Bsel=45/8, IM_LO >= 0) |   MARGINS [internal Lambda-space enclosure check, NOT the headline; ~1e-13 is the 1e-12 rounding of the declared bounds, not tightness]  RE +9.009970e-13   IM_LO +8.438714e-13   IM_HI +9.219057e-15 | audit 19 | xluxx-Nitro-AN515-58 | 2026-09-02T07:12:59-04:00 |
| generator fix | Box103Seg01M STILL FAILING after integer-literal fix — 103,116 remain parked | | xluxx-Nitro-AN515-58 | 2026-09-02T07:15:48-04:00 |
| box 100 | **CLOSED** built on Legion, synced, **re-audited on production tree** — xi margin +1.694871e-04 (first box with IM_LO < 0: Bhi branch of the B-endpoint trap exercised) | audit 19 clean | xluxx-Nitro-AN515-58 | 2026-09-02T13:24:57-04:00 |

## BOXES 100 and 102 — CLOSED 2026-09-02

| box | strip | sigma | headline xi margin | audit | where built |
|---|---|---|---|---|---|
| 102 | 2 | [11/16, 23/32] | **+1.465594e-04** | 19/19 clean | Acer |
| 100 | 0 | [9/16, 5/8] | **+1.694871e-04** | 19/19 clean | Legion, synced, re-audited on production tree |

Both match manifest v2 prediction to ~1e-11 (the 1e-12 declared-bound rounding).

**Box 100 exercised the other branch of the B-endpoint soundness trap.** It is the first
box with `IM_LO < 0`, so `emit_box_bridge.py` selected `Bsel = Bhi = 15/4` rather than
`Blo`. Every previously closed box had `IM_LO >= 0` and used `Blo`. **Both branches of
the trap are now kernel-tested**, and the generator picked correctly in both regimes
without being told which.

## TOP-EDGE UNION — multi-box case split kernel-validated 2026-09-02

With boxes 0, 100, 2, 102 closed, the contiguous prefix from 1/2 reached four boxes:

    RiemannXiTopUnion.top15_re_lt_neg_1e4_partial : sigma in [1/2, 23/32]

`RiemannXiTopUnion` RC=0 (3.99 s), `RiemannXiTopUnionAudit` RC=0 (31.64 s), axioms clean.
This is the first exercise of the `by_cases` case-split scaffold over more than one box;
the earlier 1-box version proved nothing about the branching. The union emitter's cover
gate (contiguity, no gap/overlap, measure exactly 1/2) passes at every regeneration.

## GENERATOR DEFECT — integer-valued coefficients vs the `approx` tactic (RESOLVED)

Boxes 103 and 116 aborted the queue at their first M certificate:

    Box103Seg01M.lean:95:2: unsolved goals
    |- 67 / 1 in approx (Interval.ofRat (67 / 1))

**First diagnosis was wrong.** Removing the `/1` (emitting a bare `67`) changed the goal
to `67 in approx (Interval.ofRat 67)` and it still failed. The `pf-validate` gate caught
this — 103/116 were never requeued on the strength of the unverified fix.

**Actual root cause.** The `@[approx]` lemma set in
`vendor/interval/Interval/Interval/Conversion.lean` provides:

- `approx_ofRat (x : Q) : ^x in approx (Interval.ofRat x)` — needs a coercion, not a literal
- `ofNat_div_mem_approx_ofRat {a b} [a.AtLeastTwo] [b.AtLeastTwo]` — matches `a / b`
- `one_div_ofNat_mem_approx_ofRat {b} [b.AtLeastTwo]` — matches `1 / b`

There is **no lemma for a bare integer literal**, and `n/1` fails too because `1` is not
`AtLeastTwo`. Which boxes are hit is arithmetic, not luck: the pi-coefficient of the n-th
theta term is `(n+1)^2 * (2*p1 + 15)`, integral for p1 = 7/8 at n = 1 (box 103) and for
p1 = 1 at every n (box 116). The other 16 boxes have a p1 that keeps all coefficients
non-integral — which is why they built.

**Fix (route (a), exact).** `emit_box_segment.py::_qs` now renders an integer `n >= 2` as
`2n/2`, matching `ofNat_div_mem_approx_ofRat` with a = 2n, b = 2. This is EXACT — no
outward nudge, no margin spent. 0 and 1 are left alone (not `AtLeastTwo`, and already
present in the 16 working boxes). The vendored Interval library was NOT modified, so
provenance is unaffected.

Kernel-validated on the previously failing target before any requeue:

    lake build PF.Numerics.Box103Seg01M  ->  RC = 0, 11.80 s, 4.22 GB

Boxes 103 and 116 fully regenerated, zero residual bare-integer literals. `pf-validate`
re-armed; it re-tests the same target at the next Acer closure and requeues both boxes
only on RC=0.

## WORKER CHAINING — mandatory after the second idle incident

Box 100 closed on the Legion at 01:18 PDT and the machine sat idle until 10:23 because
`legion_box.sh` builds one box and exits with no follow-on. Second idle incident of the
campaign.

`legion_queue.sh <boxk...>` now runs the Legion over a list back-to-back, skipping any
box that already carries a capstone in that tree. `pf-legion-chain` waits for the current
single-shot `pf-box107` and then launches the queue over 108-113. **Every worker gets a
follow-on watcher; an idle machine is an anomaly and is reported as one.**
| box 115 | 40/40 segments green | 647 min | xluxx-Nitro-AN515-58 | 2026-09-02T18:03:42-04:00 |
| box 115 | **CLOSED**   xi bound M = -2.627946777e-04   xi margin +1.627947e-04  [HEADLINE]  (Bsel=225/16, IM_LO >= 0) |   MARGINS [internal Lambda-space enclosure check, NOT the headline; ~1e-13 is the 1e-12 rounding of the declared bounds, not tightness]  RE +7.706602e-13   IM_LO +5.906292e-13   IM_HI +5.090180e-13 | audit 19 | xluxx-Nitro-AN515-58 | 2026-09-02T18:05:29-04:00 |
| generator fix | `N/1` integer literals defeated `approx`; emit_box_segment.py now prints bare integers. Box103Seg01M green. Boxes 103,116 requeued | | xluxx-Nitro-AN515-58 | 2026-09-02T18:08:22-04:00 |
| box 114 | 40/40 segments green | 649 min | xluxx-Nitro-AN515-58 | 2026-09-03T04:57:44-04:00 |
| box 114 | **CLOSED**   xi bound M = -2.668576824e-04   xi margin +1.668577e-04  [HEADLINE]  (Bsel=435/32, IM_LO >= 0) |   MARGINS [internal Lambda-space enclosure check, NOT the headline; ~1e-13 is the 1e-12 rounding of the declared bounds, not tightness]  RE +2.865249e-13   IM_LO +9.829077e-13   IM_HI +7.994730e-13 | audit 19 | xluxx-Nitro-AN515-58 | 2026-09-03T04:59:31-04:00 |
| box 113 | 40/40 segments green | 649 min | xluxx-Nitro-AN515-58 | 2026-09-03T15:51:45-04:00 |
| box 113 | **CLOSED**   xi bound M = -2.710598127e-04   xi margin +1.710598e-04  [HEADLINE]  (Bsel=105/8, IM_LO >= 0) |   MARGINS [internal Lambda-space enclosure check, NOT the headline; ~1e-13 is the 1e-12 rounding of the declared bounds, not tightness]  RE +4.065083e-13   IM_LO +8.048100e-13   IM_HI +4.698012e-13 | audit 19 | xluxx-Nitro-AN515-58 | 2026-09-03T15:53:31-04:00 |
| box 107 | **CLOSED** built on Legion, synced, **re-audited on production tree** | audit 19 clean | xluxx-Nitro-AN515-58 | 2026-09-03T17:41:13-04:00 |
| box 108 | **CLOSED** built on Legion, synced, **re-audited on production tree** | audit 19 clean | xluxx-Nitro-AN515-58 | 2026-09-03T17:41:14-04:00 |
| box 112 | 40/40 segments green | 649 min | xluxx-Nitro-AN515-58 | 2026-09-04T02:42:58-04:00 |
| box 112 | **CLOSED**   xi bound M = -2.755555578e-04   xi margin +1.755556e-04  [HEADLINE]  (Bsel=405/32, IM_LO >= 0) |   MARGINS [internal Lambda-space enclosure check, NOT the headline; ~1e-13 is the 1e-12 rounding of the declared bounds, not tightness]  RE +6.278455e-13   IM_LO +8.481815e-13   IM_HI +6.390175e-13 | audit 19 | xluxx-Nitro-AN515-58 | 2026-09-04T02:44:45-04:00 |
| box 103 | 40/40 segments green | 649 min | xluxx-Nitro-AN515-58 | 2026-09-04T13:34:09-04:00 |
| box 103 | **CLOSED**   xi bound M = -2.143580777e-04   xi margin +1.143581e-04  [HEADLINE]  (Bsel=105/16, IM_LO >= 0) |   MARGINS [internal Lambda-space enclosure check, NOT the headline; ~1e-13 is the 1e-12 rounding of the declared bounds, not tightness]  RE +7.101818e-13   IM_LO +4.434500e-14   IM_HI +6.877114e-13 | audit 19 | xluxx-Nitro-AN515-58 | 2026-09-04T13:35:57-04:00 |
| box 116 | FAILED at PF.Analytic.RiemannXiBox116Panels.Seg01P1 | 4 min | xluxx-Nitro-AN515-58 | 2026-09-04T13:41:50-04:00 |
| box 109 | **CLOSED** built on Legion, synced, re-audited on production tree | audit 19 clean | xluxx-Nitro-AN515-58 | 2026-09-04T14:29:35-04:00 |
| box 110 | **CLOSED** built on Legion, synced, re-audited on production tree | audit 19 clean | xluxx-Nitro-AN515-58 | 2026-09-04T14:29:36-04:00 |
| generator fix 2 | box 116 (sigma_hi = 1) exponent -1 rendered `1/1` on the R side but `ofRat 1` on the Interval side — _pow_real was not routed through _qs. Both now render `2/2` (exact). Box116Seg01P1 green. | | xluxx-Nitro-AN515-58 | 2026-09-04T14:35:31-04:00 |
| box 116 | 40/40 segments green | 645 min | xluxx-Nitro-AN515-58 | 2026-09-05T01:20:43-04:00 |
| box 116 | panels green, BRIDGE FAILED | 66s | xluxx-Nitro-AN515-58 | 2026-09-05T01:21:49-04:00 |
| box 116 | **CLOSED** xi margin +1.588177e-04 — required a second generator fix (sigma_hi = 1: exponent literal, and bridge/panel sigma-literal mismatch) | audit 19 clean | xluxx-Nitro-AN515-58 | 2026-09-05T01:45:03-04:00 |
| box 111 | **CLOSED** built on Legion, synced, re-audited on production tree | audit 19 clean | xluxx-Nitro-AN515-58 | 2026-09-05T02:50:47-04:00 |
| **UNION FULL** | `top15_re_lt_neg_1e4` over [1/2,1] kernel-green; all 18 boxes CLOSED | union audit 21 clean | xluxx-Nitro-AN515-58 | 2026-09-05T02:55:07-04:00 |

## ★★★ r331b ENDPOINT — T=15 ZERO-COUNT IDENTITY, UNCONDITIONAL — 2026-09-05 ★★★

`lake build PF.Analytic.RiemannXiT15Endgame` — **RC=0, 95.48 s, peak 8.95 GB**,
single-target serialized build (CPUAffinity 0-3, MemoryMax 11G).

### Axiom audit — all three, exactly the mathlib three

    PrincipiaTractalis.RiemannXiT15Endgame.H_TOP
      depends on axioms: [propext, Classical.choice, Quot.sound]
    PrincipiaTractalis.RiemannXiT15Endgame.boundary_zero_free_T15
      depends on axioms: [propext, Classical.choice, Quot.sound]
    PrincipiaTractalis.RiemannXiT15Endgame.xi_T15_zero_count_identity_unconditional
      depends on axioms: [propext, Classical.choice, Quot.sound]

sorryAx / ofReduceBool occurrences in this module's audit output: **0**.

### No residual hypotheses — verified by Lean, not by reading

`#check @xi_T15_zero_count_identity_unconditional` (the `@` form shows every binder,
implicit ones included) returns a type with **no binders at all**:

    xi_T15_zero_count_identity_unconditional : RectangleIntegral'
        (fun s => logDeriv riemannXiEntire s) z15 w15 =
      sum over rho in (...).toFinset, (analyticOrderNatAt riemannXiEntire rho : C)

- no `hTop` / H_TOP residual
- no boundary-nonvanishing hypothesis
- no numerical premise
- no named conjecture

### A build that failed first, and why that mattered

The first attempt returned RC=1 AND an audit line reading
`xi_T15_zero_count_identity_unconditional depends on axioms: [propext, sorryAx, ...]`.
Cause: `finite_zeros_rectangle`, `RectangleIntegral'` and
`rectangleBorder_subset_rectangle` live in namespace `Zeta23.Analytic`
(RectangleArgumentPrinciple_r327.lean:51-52); r328 (line 73) and r329b (line 83) both
open it, the staged endgame module did not. The name elaborated to a metavariable and
Lean admitted the goal.

Fix was one `open Zeta23.Analytic` line. No theorem text changed — the patch asserted
byte-identity of every `theorem` block before writing. The consumed statements
(`boundary_zero_free_of_top_right_half`, `xi_T15_exact_zero_count_identity_top_only`)
were re-read verbatim before the build and matched the module's consumption exactly.

**The `#print axioms` checks inside the module are what exposed the sorry.** An RC-only
gate would have shown a build failure with no sign that Lean had silently admitted the
theorem.

### Scope — read this before writing any release text

This is the **exact zero-count identity for the classical entire Riemann xi on the
T = 15 rectangle** `z15 = 0` to `w15 = 1 + 15i`, i.e. `[0,1] x [0,15]`. It states that
the rectangle contour integral of `logDeriv riemannXiEntire` equals the sum of
`analyticOrderNatAt` over the finitely many interior zeros.

It is **not** the Riemann Hypothesis. It is one rectangle, one identity. See
`codex/RELEASE_GATE_r331b.md` item F8.

NO PUSH. Public HEAD remains 96c71da7. Release gate to be walked item by item.
