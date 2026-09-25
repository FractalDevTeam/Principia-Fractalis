# Provenance: reconciliation of two box-parametric generators (2026-08-30)

Two Claude Code agents independently built box-parametric generators for the
r331b top-edge boxes and reached OPPOSITE verdicts on boxes 1-7.

  A. `scripts/emit_box_segment.py`      (SSH session from the Legion)
  B. `scripts/gen_r331b_box_panels.py`  (TUI session on the Acer)

A said boxes 1,2 PASS at width 1/16.  B said all of 1-7 FAIL.

## Finding: the underlying arithmetic AGREES

|            | box1 A        | box1 B        | box2 A        | box2 B        |
|------------|---------------|---------------|---------------|---------------|
| RE_LO      | 4.442219e-03  | 4.442322e-03  | 4.440739e-03  | 4.440842e-03  |
| IM_LO      | -2.507e-07    | -1.480e-07    | 3.6514e-05    | 3.6617e-05    |
| IM_HI      | 1.10661e-04   | 1.10558e-04   | 1.47485e-04   | 1.47382e-04   |
| E_QUAD     | 1.801e-06     | 1.788e-06     | 1.801e-06     | 1.798e-06     |

Agreement to ~1e-7 on every certified quantity.  The residual gap is fully
explained by node rounding (A: 10 digits, B: 12) and the analytic envelope
(A: 1/5000000 majorant; B: raw 1.0027e-7).  Both differences make A the more
conservative.  There is NO arithmetic dispute.

## Root cause of the divergence: the ACCEPTANCE TEST

B scores every box against Box 0's frozen declared triple:

    RE_MARGIN    = RE_FINAL_LO  - TARGET_RLO      # 2221/500000
    IM_MARGIN_LO = IM_TRUE_LO   - TARGET_IM_LO    # -1/10000
    IM_MARGIN_HI = TARGET_IM_HI - IM_TRUE_HI      # +1/10000

Those constants were chosen FOR BOX 0.  They are not the requirement for any
other box.  The r331a consumer re_xi_upper_bound_from_enclosures is generic in
sigma_lo/sigma_hi, in both enclosure bounds, and in the target M; each box
declares its enclosure at ITS OWN certified values and supplies its own
h_arith.  The real per-box bar is

    RE_LO  >=  (1 + 2/10000 - B_adverse * IM_LO) / (-Ahi)

with that box's own Ahi = sigma_hi*(sigma_hi-1)-225 and B_adverse.

Worked, box 2 (Ahi = -57655/256, B = Blo = 15/4, IM_LO = 3.65e-5):

    required RE_LO = (1 + 2e-4 - 1.369e-4)/225.2148 = 4.440485e-03
    B's own RE_FINAL_LO                              = 4.440842e-03  -> PASSES
    Box-0's fixed bar                                = 4.442000e-03  -> B reports FAIL

Reason: for Box 0, IM_LO < 0, so the term -B*IM_LO is a PENALTY.  For boxes
>= 2, IM_LO > 0 and the same term is a CREDIT that LOWERS the required Rlo.
A fixed Rlo bar discards that credit entirely.

## IM_HI is not margin-critical

The consumer obligation is

    forall q2 in [A_im, B_im], (1 + p1*p2 - q1*q2)/2 <= M

and q1 >= 0, so the maximum over q2 sits at q2 = A_im = IM_LO.  B_im = IM_HI
only widens a hypothesis range; it never tightens the conclusion.  IM_HI is
needed for the enclosure to EXIST, not for the margin.  B's IM_MARGIN_HI gate
therefore manufactures failures against a constant no theorem requires -- it is
what turns box 1 (whose RE passes even on B's strict bar, +3.2e-7) into a FAIL.

## Verdict

A models the Lean consumer it would instantiate; B applies a Box-0-inherited
bar.  A is consumer-faithful.

Methodology rule recorded: **a dry-run's acceptance test must be the arithmetic
of the theorem it will instantiate, not a constant inherited from a previously
closed instance.**

## Two further notes (these cut both ways)

1. B's header prose inverts the amplitude monotonicity ("decreasing in sigma,
   MIN at sigma_hi") and states a1+a2 = -1.  The true value is **-3/2**,
   kernel-proven here as RiemannXiBoxParametric.conj_exp (closed by ring).
   B's CODE is correct on both points -- its lines 168-179 catch the error in a
   comment, and its amplitude pairing matches A's exactly.  Prose only.

2. B computes E_QUAD from the TRUE M_segment, not from a certifiable ceiling of
   the loose per-term bounds the Lean M-certificate actually proves.  That is
   precisely the optimism A caught in ITSELF earlier this sprint (tight ceiling
   on 2*sum T_n vs certifiable 2*sum B_n, worth ~2.0e-05 in xi-space, fixed by
   tightening the per-term slack 1.10 -> 1.0005).  It cuts against B's own
   pessimistic conclusions and should be corrected before B's numbers are
   reused for anything.

## Adjudication

Box 2's kernel build (launched 2026-08-30T16:40:59-04:00) is the discriminating
experiment.  Whatever it returns is authoritative over both dry-runs.
