# DISPATCH OWNERSHIP — BUILD LOCK

**Owner:** Claude Code session driving over SSH from the Legion (psolo@windows-claude-sync).
**Established:** 2026-08-30T16:52:52-04:00
**Re-established after Legion restart:** 2026-08-31T18:32-04:00
**Scope:** ALL Lean builds and ALL writes under PF_Lean4_Code/ until further notice.

## If you are another Claude Code agent (e.g. the MobaXterm TUI)

**STAND DOWN on builds.** Do not run `lake build`. This machine has 15.7 GB RAM;
a single r331b panel peaks near 12.6 GB (measured, box 2). Two concurrent `lake`
invocations WILL trigger the OOM killer — this already destroyed one run
(Lean exit 137) earlier in this sprint.

## IN PROGRESS

**Acer (this machine):** systemd user unit `pf-strip-queue`, launched
2026-08-31T18:32:43-04:00. Runs scripts/strip_queue.sh over the remaining 15
manifest strips weakest-first:

    105 104 103 102 116 115 114 100 113 112 111 110 109 108 107

~10.4 h per strip, serialized -> ~6.5 days. Log: /tmp/r331b_logs/strip_queue.log
Per-strip result lines are appended to codex/DISPATCH_RESULTS_2026-08-30.md.

    systemctl --user status pf-strip-queue     # check
    systemctl --user stop   pf-strip-queue     # stop (only if you own the lock)

Linger is enabled for xluxx, so the unit survives logout. Do not `pkill lean`.

**Legion WSL:** strip 6 / Box106 (weakest strip, margin +2.211197e-05), systemd
transient unit `pf-box106`. Separate machine, no contention with this one.

## COMPLETE

- Box 0 ([1/2, 9/16]) — CLOSED, kernel-green, 31/31 endpoint audit clean.
- Box 2 (strip 1, [5/8, 11/16]) — 268/268 targets RC=0, 40/40 segments,
  10 h 22 min, 0 failures. Panels green; **bridge capstone not yet written**, so the
  three exact margins are not yet kernel-extracted.

## Files owned by this session — do not edit

- scripts/emit_box_segment.py            (box-parametric generator; regression-verified
                                          against box 0: 96 nodes, 0 mismatches)
- scripts/emit_stage2_segment.py         (box-0 generator; import is fine, do not edit)
- scripts/strip_queue.sh
- scripts/opt40tight.py
- PF/Analytic/RiemannXiBoxParametric.lean
- PF/Analytic/RiemannXiBox0Envelope.lean
- PF/Analytic/RiemannXiBox0Bridge.lean   (+ Audit)
- PF/Analytic/RiemannXiBox0Panels/**     (Box 0 CLOSED — kernel-green, do not regenerate)
- PF/Analytic/RiemannXiBox2Panels/**     (GREEN — do not regenerate)
- PF/Analytic/RiemannXiBox1??Panels/**   (queue targets)
- PF/Numerics/Box0Seg*M.lean, Box2Seg*M.lean, Box1??Seg*M.lean

## Resolved: the rival recon

A second agent sweep (scripts/gen_r331b_box_panels.py, 16:38) reported boxes 1-7
failing at width 1/16. The box-2 build was the discriminating experiment and it came
back **green at width 1/16 with 0 errors**. The regression-verified emitter sweep stands;
the rival sweep is refuted for box 2. Do not act on gen_r331b_box_panels.py output.

## Box naming — read before touching anything

`Box(100+k)` = manifest strip k, EXCEPT strip 1, which is named `Box2`. No Box101 exists.
Decode a box sigma from its M file: `thetaPowTermM 15 p1 p2 L` has p1 = (1+sigma_hi)/2.

NO PUSH by any agent until the r331b release threshold. Public HEAD stays 96c71da7.
