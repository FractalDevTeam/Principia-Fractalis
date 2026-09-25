#!/usr/bin/env python3
"""
emit_top_union.py — assemble the per-box top-edge capstones into the single
literal statement

    top15_re_lt_neg_1e4 :
      forall sigma, 1/2 <= sigma -> sigma <= 1 ->
        (riemannXiEntire (sigma + 15i)).re < -(1/10000)

by an exhaustive case split over the EXACT final partition of [1/2, 1].

The partition is not assumed from directory names.  Every box's sigma interval is
decoded from its own M certificate (p1 = (1 + sigma_hi)/2) AND cross-checked against
its segment files' hypotheses; the cover is then gated for contiguity, no gap, no
overlap, and total measure exactly 1/2.  Box(100+k) = strip k EXCEPT strip 1, which
is named Box2; there is no Box101; [9/16, 5/8] belongs to Box100 (strip 0), NOT Box2.

Modes:
  (default)   emit the full union; refuses unless all 18 capstones are present
  --partial   emit a clearly-named PARTIAL union over the maximal contiguous
              prefix starting at 1/2, for incremental elaboration while strips
              are still closing.  Never emits `sorry` and never claims the full
              range.
  --check-only  report the cover and which capstones are present; write nothing

SPDX-License-Identifier: Apache-2.0
"""
import argparse
import json
import os
import re
import sys
from fractions import Fraction as F

HALF = F(1, 2)
ONE = F(1)


def lr(x):
    if x.denominator == 1:
        return str(x.numerator) if x.numerator >= 0 else "-(%d)" % (-x.numerator)
    if x.numerator < 0:
        return "-(%d/%d)" % (-x.numerator, x.denominator)
    return "%d/%d" % (x.numerator, x.denominator)


def lean_num(t):
    """Parse a Lean numeral, tolerating `(1 : R)/2` and `(5/8 : R)` shapes."""
    t = t.replace(" : ℝ", "").replace("(", "").replace(")", "").replace(" ", "")
    return F(t)


def discover(root):
    adir = os.path.join(root, "PF", "Analytic")
    keys = []
    for d in sorted(os.listdir(adir)):
        m = re.fullmatch(r"RiemannXiBox(\d+)Panels", d)
        if m:
            keys.append(m.group(1))

    units = []
    for K in keys:
        mp = os.path.join(root, "PF", "Numerics", "Box%sSeg01M.lean" % K)
        src = open(mp, encoding="utf-8").read()
        mm = re.search(r"thetaPowTermM\s+15\s+\(([^)]+)\)\s+\(([^)]+)\)", src)
        if not mm:
            sys.exit("FATAL: no thetaPowTermM in %s" % mp)
        p1 = F(mm.group(1).replace(" ", ""))
        p2 = F(mm.group(2).replace(" ", ""))
        if p2 != p1 * (p1 + 1):
            sys.exit("FATAL: Box%s p2 != p1(p1+1) -- refusing to guess sigma" % K)

        sp = os.path.join(root, "PF", "Analytic",
                          "RiemannXiBox%sPanels" % K, "Seg01.lean")
        ssrc = open(sp, encoding="utf-8").read()
        hm = re.search(r"\(hσ0 : (.+?) ≤ σ\) \(hσ1 : σ ≤ (.+?)\)\s*:",
                       ssrc, re.S)
        if not hm:
            sys.exit("FATAL: cannot read sigma hypotheses in %s" % sp)
        slo, shi = lean_num(hm.group(1)), lean_num(hm.group(2))
        if shi != 2 * p1 - 1:
            sys.exit("FATAL: Box%s p1 decode (%s) disagrees with segment hypotheses (%s)"
                     % (K, 2 * p1 - 1, shi))

        bpath = os.path.join(root, "PF", "Analytic", "RiemannXiBox%sBridge.lean" % K)
        cap = False
        if os.path.exists(bpath):
            cap = ("theorem top15_box%s_re_lt_neg_1e4" % K) in open(bpath, encoding="utf-8").read()

        units.append(dict(K=K, slo=slo, shi=shi, p1=p1, capstone=cap))

    units.sort(key=lambda u: u["slo"])
    return units


def gate_cover(units):
    fail = []
    if not units:
        fail.append("no box panel directories found")
        return fail
    if units[0]["slo"] != HALF:
        fail.append("cover starts at %s, not 1/2" % units[0]["slo"])
    if units[-1]["shi"] != ONE:
        fail.append("cover ends at %s, not 1" % units[-1]["shi"])
    for a, b in zip(units, units[1:]):
        if a["shi"] != b["slo"]:
            fail.append("GAP/OVERLAP: Box%s ends %s, Box%s starts %s"
                        % (a["K"], a["shi"], b["K"], b["slo"]))
    for u in units:
        if u["slo"] >= u["shi"]:
            fail.append("Box%s: empty interval" % u["K"])
    tot = sum(u["shi"] - u["slo"] for u in units)
    if tot != HALF:
        fail.append("total measure %s != 1/2" % tot)
    return fail


def ns(K):
    return "PrincipiaTractalis.RiemannXiBox%sBridge" % K


def emit(units, full, root):
    """Emit the union module.  `units` is the contiguous run being covered."""
    lo, hi = units[0]["slo"], units[-1]["shi"]
    name = "top15_re_lt_neg_1e4" if full else "top15_re_lt_neg_1e4_partial"
    mod = "PF.Analytic.RiemannXiTopUnion"
    NS = "PrincipiaTractalis.RiemannXiTopUnion"

    O = []
    A = O.append
    A("/-")
    A("# %s" % mod)
    A("")
    if full:
        A("**The T = 15 top-edge sign theorem over the full range.**")
    else:
        A("**PARTIAL top-edge union -- sigma in [%s, %s] ONLY.**" % (lo, hi))
        A("")
        A("This is NOT the full theorem.  It covers the maximal contiguous run of")
        A("CLOSED boxes starting at 1/2.  It is emitted for incremental elaboration")
        A("while the remaining strips are still building.  It contains no `sorry`;")
        A("it simply proves less.  The full `top15_re_lt_neg_1e4` is emitted only")
        A("when every box in the partition has a kernel-green capstone.")
    A("")
    A("AUTO-GENERATED by scripts/emit_top_union.py.  Do not edit by hand.")
    A("")
    A("Exhaustive case split over the exact final partition of [%s, %s]:" % (lo, hi))
    A("")
    A("| box | sigma interval | source |")
    A("|---|---|---|")
    for u in units:
        A("| Box%s | [%s, %s] | `%s.top15_box%s_re_lt_neg_1e4` |"
          % (u["K"], u["slo"], u["shi"], ns(u["K"]), u["K"]))
    A("")
    A("Cover gate (checked at generation time, not assumed): contiguous, no gap, no")
    A("overlap, endpoints owned by both neighbours (each capstone is closed on its")
    A("own interval), total measure exactly %s." % (hi - lo))
    A("")
    A("Box numbering is NOT the strip id: Box(100+k) = manifest strip k EXCEPT strip 1,")
    A("which is named Box2, and there is no Box101.  In particular [9/16, 5/8] is")
    A("covered by **Box100** (strip 0), not by Box2.  Every interval above was decoded")
    A("from that box's own M certificate via p1 = (1 + sigma_hi)/2 and cross-checked")
    A("against its segment hypotheses.")
    A("")
    A("SPDX-License-Identifier: Apache-2.0")
    A("-/")
    A("")
    for u in units:
        A("import PF.Analytic.RiemannXiBox%sBridge" % u["K"])
    A("")
    A("namespace %s" % NS)
    A("")
    A("open scoped Real")
    A("open PrincipiaTractalis.RiemannXiEntire")
    A("")
    if full:
        A("/-- **THE T = 15 TOP-EDGE SIGN THEOREM** -- unconditional, no numeric")
        A("hypotheses, no residual conjecture:")
        A("")
        A("    Re xi(sigma + 15i) < -1/10000   for every sigma in [1/2, 1].")
        A("")
        A("Proved by exhaustive case split over %d certified boxes." % len(units))
        A("Each branch is that box's own kernel-green capstone. -/")
    else:
        A("/-- PARTIAL union over [%s, %s] -- the closed prefix only. -/" % (lo, hi))
    A("theorem %s {σ : ℝ}" % name)
    A("    (h0 : (%s : ℝ) ≤ σ) (h1 : σ ≤ %s) :" % (lr(lo), lr(hi)))
    A("    (riemannXiEntire (⟨σ, 15⟩ : ℂ)).re < -(1/10000 : ℝ) := by")
    for i, u in enumerate(units):
        last = (i == len(units) - 1)
        lower = "h0" if i == 0 else "(le_of_lt hc%d)" % (i - 1)
        if last:
            A("  exact %s.top15_box%s_re_lt_neg_1e4 (by linarith) (by linarith)"
              % (ns(u["K"]), u["K"]))
        else:
            A("  by_cases hc%d : σ ≤ (%s : ℝ)" % (i, lr(u["shi"])))
            A("  · exact %s.top15_box%s_re_lt_neg_1e4 (by linarith) (by linarith)"
              % (ns(u["K"]), u["K"]))
            A("  push_neg at hc%d" % i)
    A("")
    A("/-- The `≠ 0` shape consumed by r328/r329b (`hTop`).  `Re z < 0` forces `z ≠ 0`. -/")
    A("theorem %s_ne_zero {σ : ℝ}" % name)
    A("    (h0 : (%s : ℝ) ≤ σ) (h1 : σ ≤ %s) :" % (lr(lo), lr(hi)))
    A("    riemannXiEntire (⟨σ, 15⟩ : ℂ) ≠ 0 := by")
    A("  intro hzero")
    A("  have hneg := %s h0 h1" % name)
    A("  have hre : (riemannXiEntire (⟨σ, 15⟩ : ℂ)).re = 0 := by rw [hzero]; simp")
    A("  linarith")
    if full:
        A("")
        A("/-- **H_TOP, DISCHARGED** -- exactly the hypothesis shape required by")
        A("`RiemannXiBottomEdgeUnconditional.boundary_zero_free_of_top_right_half`")
        A("and `.xi_T15_exact_zero_count_identity_top_only`. -/")
        A("theorem H_TOP_discharged :")
        A("    ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → riemannXiEntire (⟨σ, 15⟩ : ℂ) ≠ 0 :=")
        A("  fun _ h0 h1 => %s_ne_zero h0 h1" % name)
    A("")
    A("end %s" % NS)
    return "\n".join(O) + "\n", name


def emit_audit(units, full, name):
    NS = "PrincipiaTractalis.RiemannXiTopUnion"
    O = []
    A = O.append
    A("/-")
    A("# PF.Analytic.RiemannXiTopUnionAudit")
    A("")
    A("Axiom audit for the top-edge union%s." % ("" if full else " (PARTIAL)"))
    A("Expected only: [propext, Classical.choice, Quot.sound].")
    A("No project axioms.  No sorry.  No native_decide.")
    A("")
    A("AUTO-GENERATED by scripts/emit_top_union.py.")
    A("")
    A("SPDX-License-Identifier: Apache-2.0")
    A("-/")
    A("")
    A("import PF.Analytic.RiemannXiTopUnion")
    A("")
    A("open %s" % NS)
    A("")
    A("-- per-box capstones consumed by the union")
    for u in units:
        A("#print axioms %s.top15_box%s_re_lt_neg_1e4" % (ns(u["K"]), u["K"]))
    A("")
    A("-- the union itself")
    A("#print axioms %s" % name)
    A("#print axioms %s_ne_zero" % name)
    if full:
        A("#print axioms H_TOP_discharged")
    return "\n".join(O) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--partial", action="store_true")
    ap.add_argument("--check-only", action="store_true")
    args = ap.parse_args()

    units = discover(args.root)
    fail = gate_cover(units)
    print("partition of [1/2, 1] — %d units" % len(units))
    for u in units:
        print("  Box%-4s [%-7s, %-7s]  p1=%-8s  %s"
              % (u["K"], u["slo"], u["shi"], u["p1"],
                 "CLOSED" if u["capstone"] else "pending"))
    owner = [u["K"] for u in units if u["slo"] <= F(9, 16) and u["shi"] >= F(5, 8)]
    print("[9/16, 5/8] owned by: %s" % (", ".join("Box" + k for k in owner) or "NOBODY"))
    if fail:
        print("COVER GATE: FAILED")
        for f in fail:
            print("  - " + f)
        sys.exit(1)
    print("COVER GATE: PASS — contiguous, no gap, no overlap, measure exactly 1/2")

    closed = [u for u in units if u["capstone"]]
    print("capstones: %d/%d closed" % (len(closed), len(units)))

    full = len(closed) == len(units)
    if full:
        run = units
    else:
        run = []
        for u in units:
            if not u["capstone"]:
                break
            run.append(u)
        if not args.partial:
            print("")
            print("REFUSING to emit the full union: %d box(es) still pending (%s)."
                  % (len(units) - len(closed),
                     " ".join("Box" + u["K"] for u in units if not u["capstone"])))
            print("Re-run with --partial to emit the closed prefix"
                  " [1/2, %s]." % (run[-1]["shi"] if run else "nothing"))
            sys.exit(2)
        if not run:
            sys.exit("Nothing to emit: no closed box starts at 1/2.")
        print("PARTIAL mode: emitting the closed prefix [1/2, %s] (%d boxes)"
              % (run[-1]["shi"], len(run)))

    if args.check_only:
        print("[check-only] nothing written")
        return

    body, name = emit(run, full, args.root)
    audit = emit_audit(run, full, name)
    bp = os.path.join(args.root, "PF", "Analytic", "RiemannXiTopUnion.lean")
    apth = os.path.join(args.root, "PF", "Analytic", "RiemannXiTopUnionAudit.lean")
    with open(bp, "w", encoding="utf-8") as f:
        f.write(body)
    with open(apth, "w", encoding="utf-8") as f:
        f.write(audit)
    print("wrote %s (%s, %d boxes)" % (bp, "FULL" if full else "PARTIAL", len(run)))
    print("wrote %s" % apth)


if __name__ == "__main__":
    main()
