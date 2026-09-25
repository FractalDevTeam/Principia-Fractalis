#!/usr/bin/env python3
"""
emit_box_bridge.py — box-parametric §8 consumption layer (bridge) generator.

Emits  PF/Analytic/RiemannXiBox{K}Bridge.lean  (+ ...BridgeAudit.lean) for any
box whose 40 OPT-40-TIGHT panel segments are already kernel-green, converting a
BUILT box into a CLOSED box.

What it emits, in the literal r331a structures:

  §B.3  four cumulative chains over [1,5]  (finite_re/im_lower/upper)
  §B.4  intervalIntegral -> Ioc rewrites   (REUSED from box 0, sigma-generic)
  §B.5  four Lambda-0 bounds, §8 envelope applied EXACTLY ONCE via
        RiemannXiBox0Envelope.box0_envelope_le  (no hypotheses, no sigma --
        reusable verbatim by every box)
  §B.6  three exact rational margin theorems (RE, IM_LO, IM_HI)
  §B.7  BoxReEnclosure / BoxImEnclosure witnesses + the unconditional
        `top15_box{K}_re_lt_neg_1e4` via the r331a generic consumer
        `re_xi_upper_bound_from_enclosures`

What it does NOT re-emit (box-universal, imported from box 0's bridge):
  re_integrable / im_integrable, the 39+39 adjacent-interval joins, and the
  two Ioc rewrites.  These take `(sigma : R)` with no sigma constraints.

Error ledger (locked, inherited from box 0): node rounding and composite-
midpoint error are already inside each `box{K}_seg{j}_*_integral_*` endpoint
and are NEVER re-subtracted here.  The ONLY error applied at this layer is the
§8 analytic envelope, once.

Usage:
  emit_box_bridge.py --root <repo>/PF_Lean4_Code --box 2 \
      [--manifest /tmp/strip_manifest_v2.json] [--denom 12] [--check-only]

SPDX-License-Identifier: Apache-2.0
"""
import argparse
import json
import os
import re
import sys
from fractions import Fraction as F

T = 15                      # fixed top-edge height
NPAR = 3                    # theta truncation N
ENV = F(1, 5000000)         # §8 envelope majorant (box0_envelope_le RHS)
TARGET = F(-1, 10000)       # xi top-edge target
NSEG = 40
SIGMA_LITERAL = ["", ""]   # raw slo/shi text from the panels
SIG = "σ"           # the sigma binder name used throughout the emitted Lean


# ----------------------------------------------------------------------------
# rational -> Lean surface syntax
# ----------------------------------------------------------------------------

def lr(x: F) -> str:
    """Lean numeral for an exact rational, WITHOUT a type ascription."""
    if x.denominator == 1:
        return str(x.numerator) if x.numerator >= 0 else "-(%d)" % (-x.numerator)
    if x.numerator < 0:
        return "-(%d/%d)" % (-x.numerator, x.denominator)
    return "%d/%d" % (x.numerator, x.denominator)


def lrR(x: F) -> str:
    """Lean numeral ascribed to R."""
    return "(%s : ℝ)" % lr(x)


def parse_frac(s: str) -> F:
    """Parse a Lean rational numeral.  Handles any nesting of unary minus and
    parentheses: `3/4`, `-3/4`, `-(3/4)`, `(-(3/4))`.  Getting the sign wrong
    here silently inverts a certificate, so the shape is peeled explicitly
    rather than matched by one regex."""
    s = s.strip().replace(" ", "")
    sign = 1
    while True:
        if s.startswith("-"):
            sign = -sign
            s = s[1:]
            continue
        if s.startswith("(") and s.endswith(")"):
            s = s[1:-1]
            continue
        break
    if "/" in s:
        n, d = s.split("/", 1)
        if not (re.fullmatch(r"\d+", n) and re.fullmatch(r"\d+", d)):
            sys.exit("FATAL: unparseable rational numeral %r" % s)
        return sign * F(int(n), int(d))
    if not re.fullmatch(r"\d+", s):
        sys.exit("FATAL: unparseable rational numeral %r" % s)
    return sign * F(int(s))


# ----------------------------------------------------------------------------
# box discovery: decode sigma from p1, cross-check against the segment files
# ----------------------------------------------------------------------------

def decode_sigma_from_M(root: str, K: str):
    """sigma_hi = 2*p1 - 1 where the M certificate carries `thetaPowTermM 15 p1 p2 L`.

    Box directory numbers are NOT strip ids (Box(100+k) = strip k, except strip 1
    which is named Box2, and there is no Box101), so the sigma MUST be decoded,
    never inferred from the name."""
    path = os.path.join(root, "PF", "Numerics", "Box%sSeg01M.lean" % K)
    src = open(path, encoding="utf-8").read()
    m = re.search(r"thetaPowTermM\s+15\s+\(([^)]+)\)\s+\(([^)]+)\)\s+\(([^)]+)\)", src)
    if not m:
        sys.exit("FATAL: no thetaPowTermM application found in %s" % path)
    p1, p2 = parse_frac(m.group(1)), parse_frac(m.group(2))
    if p2 != p1 * (p1 + 1):
        sys.exit("FATAL: p2 != p1*(p1+1) in %s (p1=%s p2=%s) -- refusing to guess sigma"
                 % (path, p1, p2))
    return 2 * p1 - 1, p1, p2


# ----------------------------------------------------------------------------
# segment certificate extraction
# ----------------------------------------------------------------------------

HYP_PAT = r"\(hσ0 : \(([^)]+) : ℝ\) ≤ σ\) \(hσ1 : σ ≤ ([0-9/]+)\)"

LOWER_PAT = re.compile(
    r"\(\((.+?) : ℝ\)\)\s*≤\s*∫ u in \((.+?) : ℝ\)\.\.([0-9/]+)\s*,", re.S)
UPPER_PAT = re.compile(
    r"\(∫ u in \((.+?) : ℝ\)\.\.([0-9/]+)\s*,.*?\)\s*≤\s*\(\((.+?) : ℝ\)\)", re.S)


def theorem_blocks(src: str):
    """Split a segment file into {theorem name -> body up to ':= by'}."""
    out = {}
    nl = chr(10)
    parts = re.split(nl + r"theorem\s+", nl + src)
    for part in parts[1:]:
        m = re.match(r"([A-Za-z0-9_']+)", part)
        if not m:
            continue
        end = part.find(":= by")
        out[m.group(1)] = part[:end if end != -1 else len(part)]
    return out


def read_segments(root: str, K: str):
    """Return (segs, slo, shi).  segs[j] carries the four exact certified
    endpoints plus the segment's (a, b) integration limits, read from the
    Lean sources the kernel actually accepted -- never recomputed."""
    pdir = os.path.join(root, "PF", "Analytic", "RiemannXiBox%sPanels" % K)
    segs, slo, shi = {}, None, None
    for j in range(1, NSEG + 1):
        path = os.path.join(pdir, "Seg%02d.lean" % j)
        if not os.path.exists(path):
            sys.exit("FATAL: missing segment source %s" % path)
        src = open(path, encoding="utf-8").read()
        blocks = theorem_blocks(src)

        rec = {}
        for kind, suffix, is_lower in (
                ("re_lo", "re_integral_lower", True),
                ("re_hi", "re_integral_upper", False),
                ("im_lo", "im_integral_lower", True),
                ("im_hi", "im_integral_upper", False)):
            name = "box%s_seg%d_%s" % (K, j, suffix)
            if name not in blocks:
                sys.exit("FATAL: %s not found in %s" % (name, path))
            blk = blocks[name]

            h = re.search(HYP_PAT, blk)
            if not h:
                sys.exit("FATAL: cannot read sigma hypotheses of %s" % name)
            s0, s1 = parse_frac(h.group(1)), parse_frac(h.group(2))
            # Keep the literal source text: the bridge must hand these exact
            # terms back to the segment lemmas (see box 116, sigma_hi = 1/1).
            raw0, raw1 = h.group(1).strip(), h.group(2).strip()
            if raw0.endswith(" : ℝ") or raw0.startswith("("):
                raw0 = raw0.replace(" : ℝ", "").strip("()")
            SIGMA_LITERAL[0], SIGMA_LITERAL[1] = raw0, raw1
            if slo is None:
                slo, shi = s0, s1
            elif (s0, s1) != (slo, shi):
                sys.exit("FATAL: %s declares sigma [%s,%s], expected [%s,%s]"
                         % (name, s0, s1, slo, shi))

            m = (LOWER_PAT if is_lower else UPPER_PAT).search(blk)
            if not m:
                sys.exit("FATAL: cannot parse the statement of %s" % name)
            if is_lower:
                const, a, b = m.group(1), m.group(2), m.group(3)
            else:
                a, b, const = m.group(1), m.group(2), m.group(3)
            rec[kind] = parse_frac(const)
            if "a" in rec and (rec["a"], rec["b"]) != (a.strip(), b.strip()):
                sys.exit("FATAL: seg %d endpoint disagreement across the four kinds" % j)
            rec["a"], rec["b"] = a.strip(), b.strip()
        segs[j] = rec

    if segs[1]["a"] != "1/1":
        sys.exit("FATAL: segment 1 does not start at 1/1 (got %s)" % segs[1]["a"])
    for j in range(1, NSEG):
        if segs[j]["b"] != segs[j + 1]["a"]:
            sys.exit("FATAL: endpoint gap between seg %d (b=%s) and seg %d (a=%s)"
                     % (j, segs[j]["b"], j + 1, segs[j + 1]["a"]))
    if segs[NSEG]["b"] != "5/1":
        sys.exit("FATAL: segment 40 does not end at 5/1 (got %s)" % segs[NSEG]["b"])

    # Every certified segment must actually be an enclosure.  A sign or capture
    # bug in the parser shows up here first, before it can poison a cumulative
    # chain and produce a plausible-looking but wrong margin.
    inverted = [j for j in range(1, NSEG + 1)
                if segs[j]["re_lo"] > segs[j]["re_hi"] or segs[j]["im_lo"] > segs[j]["im_hi"]]
    if inverted:
        sys.exit("FATAL: segments %s have lower bound > upper bound -- the parse is wrong, "
                 "refusing to emit" % inverted)
    return segs, slo, shi


# ----------------------------------------------------------------------------
# certification arithmetic
# ----------------------------------------------------------------------------

def certify(segs, slo, shi, dexp):
    """Cumulative sums -> Lambda-0 endpoints -> declared box bounds -> xi bound.

    The ONLY error applied here is the section-8 envelope, once per endpoint."""
    cum = {k: [] for k in ("re_lo", "re_hi", "im_lo", "im_hi")}
    for k in cum:
        acc = F(0)
        for j in range(1, NSEG + 1):
            acc += segs[j][k]
            cum[k].append(acc)

    c = {k: cum[k][NSEG - 1] for k in cum}
    cert = {
        "RE_LO": c["re_lo"] - ENV,
        "RE_HI": c["re_hi"] + ENV,
        "IM_LO": c["im_lo"] - ENV,
        "IM_HI": c["im_hi"] + ENV,
    }

    D = 10 ** dexp

    def ffloor(x):
        return F(x.numerator // x.denominator, 1)

    decl = {
        "RE_LO": ffloor(cert["RE_LO"] * D) / D,
        "IM_LO": ffloor(cert["IM_LO"] * D) / D,
        "IM_HI": -(ffloor(-cert["IM_HI"] * D)) / D,
        "RE_HI": F(1),
    }

    Alo = slo * (slo - 1) - F(T) ** 2
    Ahi = shi * (shi - 1) - F(T) ** 2
    Blo = F(T) * (2 * slo - 1)
    Bhi = F(T) * (2 * shi - 1)
    Bsel = Bhi if decl["IM_LO"] < 0 else Blo

    M = (1 + Ahi * decl["RE_LO"] - Bsel * decl["IM_LO"]) / 2
    xi_margin = TARGET - M

    return dict(cum=cum, cert=cert, decl=decl, Alo=Alo, Ahi=Ahi, Blo=Blo,
                Bhi=Bhi, Bsel=Bsel, M=M, xi_margin=xi_margin,
                AR=Ahi * decl["RE_LO"], BI=Bsel * decl["IM_LO"],
                margins={
                    "RE": cert["RE_LO"] - decl["RE_LO"],
                    "IM_LO": cert["IM_LO"] - decl["IM_LO"],
                    "IM_HI": decl["IM_HI"] - cert["IM_HI"],
                })


def gate(K, slo, shi, R):
    """Refuse to emit anything that is not sound or does not close."""
    fail = []
    if not (slo < shi):
        fail.append("empty sigma box")
    if R["Ahi"] >= 0:
        fail.append("Ahi = %s is not negative -- the A*r monotone step is invalid" % R["Ahi"])
    if R["Blo"] < 0:
        fail.append("Blo = %s < 0 -- q1 nonnegativity fails, the B*i step is invalid" % R["Blo"])
    if R["decl"]["RE_LO"] <= 0:
        fail.append("declared RE_LO = %s is not positive" % R["decl"]["RE_LO"])
    if R["cert"]["RE_HI"] > 1:
        fail.append("certified RE_HI = %s exceeds the declared upper bound 1" % R["cert"]["RE_HI"])
    for name, v in R["margins"].items():
        if v <= 0:
            fail.append("%s margin = %s is not positive (rounding denominator too small)"
                        % (name, v))
    if R["xi_margin"] <= 0:
        fail.append("xi margin = %.6e is not positive -- this box does NOT close"
                    % float(R["xi_margin"]))
    if fail:
        sys.exit("GATE FAILED for box %s:\n  - %s" % (K, "\n  - ".join(fail)))


# ----------------------------------------------------------------------------
# Lean emission
# ----------------------------------------------------------------------------

def emit_chain(K, slo, shi, segs, cum, kind, is_lower, is_re):
    part = "Re" if is_re else "Im"
    join = ("re" if is_re else "im") + "_join"
    seg_suffix = ("re" if is_re else "im") + "_integral_" + ("lower" if is_lower else "upper")
    name = "finite_%s_%s" % ("re" if is_re else "im", "lower" if is_lower else "upper")
    integrand = "realTheta%sIntegrandN 3 " % part + SIG + " 15 u"
    total = cum[kind][NSEG - 1]

    def stmt(bound, b):
        itg = "\u222b u in (1/1 : \u211d)..%s, %s" % (b, integrand)
        if is_lower:
            return "(%s : \u211d) \u2264 %s" % (lr(bound), itg)
        return "(%s) \u2264 (%s : \u211d)" % (itg, lr(bound))

    L = []
    L.append("set_option maxHeartbeats 4000000 in")
    L.append("theorem %s (%s : \u211d)" % (name, SIG))
    L.append("    (h\u03c30 : (%s : \u211d) \u2264 %s) (h\u03c31 : %s \u2264 %s) :"
             % (SIGMA_LITERAL[0], SIG, SIG, SIGMA_LITERAL[1]))
    L.append("    %s := by" % stmt(total, "5/1"))
    for j in range(1, NSEG + 1):
        L.append("  have s%d := box%s_seg%d_%s %s h\u03c30 h\u03c31"
                 % (j, K, j, seg_suffix, SIG))
        line = "  have c%d : %s" % (j, stmt(cum[kind][j - 1], segs[j]["b"]))
        if j == 1:
            L.append(line + " := s1")
        else:
            L.append(line + " := by")
            L.append("    rw [\u2190 %s_%d %s]" % (join, j - 1, SIG))
            L.append("    linarith [c%d, s%d]" % (j - 1, j))
    L.append("  exact c%d" % NSEG)
    return "\n".join(L)


def emit_bridge(K, slo, shi, segs, R, strip_id, pred):
    c, d, m = R["cert"], R["decl"], R["margins"]
    mod = "PF.Analytic.RiemannXiBox%sBridge" % K
    ns = "PrincipiaTractalis.RiemannXiBox%sBridge" % K
    B0 = "PrincipiaTractalis.RiemannXiBox0Bridge"
    ENC = "PrincipiaTractalis.RiemannXiThetaBoxEnclosure"

    O = []
    A = O.append
    A("/-")
    A("# %s" % mod)
    A("")
    A("**Section-8 consumption layer for r331b box %s** -- sigma in [%s, %s]%s."
      % (K, slo, shi, "  (manifest strip %d)" % strip_id if strip_id is not None else ""))
    A("")
    A("AUTO-GENERATED by scripts/emit_box_bridge.py.  Do not edit by hand.")
    A("")
    A("Chains the 40 certified OPT-40-TIGHT segment integrals in GEOMETRIC order")
    A("(segment index order = geometric order) into a single intervalIntegral over")
    A("[1, 5], rewrites it as the set integral over Ioc 1 5, instantiates T := 5, and")
    A("applies the section-8 analytic envelope EXACTLY ONCE via")
    A("RiemannXiBox0Envelope.box0_envelope_le, which has no hypotheses and no sigma")
    A("and is therefore reusable verbatim by every box.")
    A("")
    A("The 39+39 adjacent-interval joins, the two integrability lemmas and the two")
    A("Ioc rewrites are sigma-universal and are IMPORTED from box 0's bridge rather")
    A("than re-emitted.")
    A("")
    A("Error ledger (locked): node rounding and composite-midpoint error are already")
    A("inside each box%s_seg{j}_*_integral_* endpoint and are NEVER re-subtracted" % K)
    A("here.  The only error applied at this layer is the section-8 envelope.")
    A("")
    A("Certified Lambda-0 endpoints (exact rationals, after one envelope application):")
    A("  RE_LO = %s" % c["RE_LO"])
    A("        ~ %.12e" % float(c["RE_LO"]))
    A("  IM_LO ~ %.12e" % float(c["IM_LO"]))
    A("  IM_HI ~ %.12e" % float(c["IM_HI"]))
    A("")
    A("HEADLINE FIGURE for this box -- xi-space margin against the -1/10000 target:")
    A("")
    A("    xi margin ~ %+.6e" % float(R["xi_margin"]))
    A("")
    A("xi top-edge bound: Re xi(sigma+15i) <= %s" % R["M"])
    A("                                     ~ %.9e   <   -1e-4" % float(R["M"]))
    A("")
    A("Internal enclosure check (NOT the headline).  These are Lambda-space margins of")
    A("the certified endpoints against the DECLARED box bounds.  They sit near 1e-13 by")
    A("construction, because the declared bounds are outward-rounded at 1e-12 -- that is")
    A("the rounding step, not a measure of tightness.  Quoting them as the box's margin")
    A("would misread as knife-edge when the consumer margin above is healthy.")
    A("  RE     margin = %s" % m["RE"])
    A("         ~ %+.6e" % float(m["RE"]))
    A("  IM_LO  margin ~ %+.6e" % float(m["IM_LO"]))
    A("  IM_HI  margin ~ %+.6e" % float(m["IM_HI"]))
    if pred is not None:
        A("Manifest v2 predicted xi margin ~ %+.6e (reconciliation only, not load-bearing)"
          % float(pred))
    A("")
    A("SPDX-License-Identifier: Apache-2.0")
    A("-/")
    A("")
    A("import PF.Analytic.RiemannXiBox0Bridge")
    for j in range(1, NSEG + 1):
        A("import PF.Analytic.RiemannXiBox%sPanels.Seg%02d" % (K, j))
    A("")
    A("namespace %s" % ns)
    A("")
    A("open scoped Real")
    A("open MeasureTheory")
    A("open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes")
    A("open PrincipiaTractalis.RiemannXiEntire")
    joins = " ".join(["re_join_%d" % j for j in range(1, NSEG)]
                     + ["im_join_%d" % j for j in range(1, NSEG)]
                     + ["re_interval_eq_Ioc", "im_interval_eq_Ioc"])
    A("-- sigma-universal infrastructure, reused verbatim from box 0.  Selective open")
    A("-- so that box 0's own finite_* / *_Lambda0_* names cannot shadow ours.")
    A("open %s (%s)" % (B0, joins))
    for j in range(1, NSEG + 1):
        A("open PrincipiaTractalis.RiemannXiBox%sPanels.Seg%02d" % (K, j))
    A("")
    A("/-! ## Section B.3 -- cumulative bounds over [1, 5] (exact rationals) -/")
    A("")
    for kind, is_lower, is_re in (("re_lo", True, True), ("re_hi", False, True),
                                  ("im_lo", True, False), ("im_hi", False, False)):
        A(emit_chain(K, slo, shi, segs, R["cum"], kind, is_lower, is_re))
        A("")
    A("/-! ## Section B.5 -- section-8 envelope applied EXACTLY ONCE, T := 5")
    A("")
    A("Section B.4 (intervalIntegral 1..5 = set integral over Ioc 1 5) is")
    A("sigma-universal and is imported from box 0 rather than re-proved. -/")
    A("")

    def lam(part, is_lower, bound, fin, habs):
        nm = "%s_Lambda0_%s" % (part, "lower" if is_lower else "upper")
        proj = "(completedRiemannZeta\u2080 (\u27e8%s, 15\u27e9 : \u2102)).%s" % (SIG, part)
        rel = ("(%s : \u211d) \u2264 %s" % (lr(bound), proj)) if is_lower \
            else ("%s \u2264 (%s : \u211d)" % (proj, lr(bound)))
        return "\n".join([
            "theorem %s (%s : \u211d)" % (nm, SIG),
            "    (h\u03c30 : (%s : \u211d) \u2264 %s) (h\u03c31 : %s \u2264 %s) :"
            % (SIGMA_LITERAL[0], SIG, SIG, SIGMA_LITERAL[1]),
            "    %s := by" % rel,
            "  have h\u03c3a : (0 : \u211d) \u2264 %s := by linarith" % SIG,
            "  have h\u03c3b : %s \u2264 1 := by linarith" % SIG,
            "  have h8 := %s_Lambda0_close_to_truncated_integral (N := 3) (\u03c3 := %s) (t := 15)"
            % (part, SIG),
            "    (T := 5) h\u03c3a h\u03c3b (by norm_num)",
            "  push_cast at h8",
            "  have henv := PrincipiaTractalis.RiemannXiBox0Envelope.box0_envelope_le",
            "  have habs := abs_le.mp (le_trans h8 henv)",
            "  have hfin := %s %s h\u03c30 h\u03c31" % (fin, SIG),
            "  rw [%s_interval_eq_Ioc %s] at hfin" % (part, SIG),
            "  linarith [habs.%d, hfin]" % habs,
        ])

    A(lam("re", True, c["RE_LO"], "finite_re_lower", 1))
    A("")
    A(lam("im", True, c["IM_LO"], "finite_im_lower", 1))
    A("")
    A(lam("im", False, c["IM_HI"], "finite_im_upper", 2))
    A("")
    A(lam("re", False, F(1), "finite_re_upper", 2))
    A("")
    A("/-! ## Section B.6 -- exact rational margins -/")
    A("")
    A("theorem RE_MARGIN_pos : (0 : \u211d) < (%s : \u211d) - (%s : \u211d) := by norm_num"
      % (lr(c["RE_LO"]), lr(d["RE_LO"])))
    A("")
    A("theorem IM_LO_MARGIN_pos : (0 : \u211d) < (%s : \u211d) - (%s : \u211d) := by norm_num"
      % (lr(c["IM_LO"]), lr(d["IM_LO"])))
    A("")
    A("theorem IM_HI_MARGIN_pos : (0 : \u211d) < (%s : \u211d) - (%s : \u211d) := by norm_num"
      % (lr(d["IM_HI"]), lr(c["IM_HI"])))
    A("")
    A("/-! ## Section B.7 -- coefficient enclosures, r331a box enclosures, and the")
    A("unconditional box-%s top-edge bound -/" % K)
    A("")
    A("theorem box%s_A_lo_bound :" % K)
    A("    \u2200 %s : \u211d, (%s : \u211d) \u2264 %s \u2192 %s \u2264 %s \u2192 (%s : \u211d) \u2264 %s * (%s - 1) - (15 : \u211d) ^ 2 := by"
      % (SIG, SIGMA_LITERAL[0], SIG, SIG, SIGMA_LITERAL[1], lr(R["Alo"]), SIG, SIG))
    A("  intro %s h0 h1" % SIG)
    A("  nlinarith [mul_nonneg (by linarith : (0 : \u211d) \u2264 %s - (%s : \u211d))"
      % (SIG, lr(slo)))
    A("    (by linarith : (0 : \u211d) \u2264 %s + (%s : \u211d) - 1)]" % (SIG, lr(slo)))
    A("")
    A("theorem box%s_A_hi_bound :" % K)
    A("    \u2200 %s : \u211d, (%s : \u211d) \u2264 %s \u2192 %s \u2264 %s \u2192 %s * (%s - 1) - (15 : \u211d) ^ 2 \u2264 (%s : \u211d) := by"
      % (SIG, SIGMA_LITERAL[0], SIG, SIG, SIGMA_LITERAL[1], SIG, SIG, lr(R["Ahi"])))
    A("  intro %s h0 h1" % SIG)
    A("  nlinarith [mul_nonneg (by linarith : (0 : \u211d) \u2264 (%s : \u211d) - %s)"
      % (lr(shi), SIG))
    A("    (by linarith : (0 : \u211d) \u2264 %s + (%s : \u211d) - 1)]" % (SIG, lr(shi)))
    A("")
    A("theorem box%s_B_lo_bound :" % K)
    A("    \u2200 %s : \u211d, (%s : \u211d) \u2264 %s \u2192 %s \u2264 %s \u2192 (%s : \u211d) \u2264 (15 : \u211d) * (2 * %s - 1) := by"
      % (SIG, SIGMA_LITERAL[0], SIG, SIG, SIGMA_LITERAL[1], lr(R["Blo"]), SIG))
    A("  intro %s h0 h1; linarith" % SIG)
    A("")
    A("theorem box%s_B_hi_bound :" % K)
    A("    \u2200 %s : \u211d, (%s : \u211d) \u2264 %s \u2192 %s \u2264 %s \u2192 (15 : \u211d) * (2 * %s - 1) \u2264 (%s : \u211d) := by"
      % (SIG, SIGMA_LITERAL[0], SIG, SIG, SIGMA_LITERAL[1], SIG, lr(R["Bhi"])))
    A("  intro %s h0 h1; linarith" % SIG)
    A("")
    A("theorem box%s_re_enclosure :" % K)
    A("    %s.BoxReEnclosure" % ENC)
    A("      (%s : \u211d) (%s) 15 (%s) (%s) := by"
      % (SIGMA_LITERAL[0], SIGMA_LITERAL[1], lr(d["RE_LO"]), lr(d["RE_HI"])))
    A("  constructor")
    A("  intro %s h0 h1" % SIG)
    A("  refine \u27e8?_, ?_\u27e9")
    A("  \u00b7 have := re_Lambda0_lower %s h0 h1" % SIG)
    A("    linarith")
    A("  \u00b7 have := re_Lambda0_upper %s h0 h1" % SIG)
    A("    linarith")
    A("")
    A("theorem box%s_im_enclosure :" % K)
    A("    %s.BoxImEnclosure" % ENC)
    A("      (%s : \u211d) (%s) 15 (%s) (%s) := by"
      % (SIGMA_LITERAL[0], SIGMA_LITERAL[1], lr(d["IM_LO"]), lr(d["IM_HI"])))
    A("  constructor")
    A("  intro %s h0 h1" % SIG)
    A("  refine \u27e8?_, ?_\u27e9")
    A("  \u00b7 have := im_Lambda0_lower %s h0 h1" % SIG)
    A("    linarith")
    A("  \u00b7 have := im_Lambda0_upper %s h0 h1" % SIG)
    A("    linarith")
    A("")
    # The two factors are introduced as NAMED hypotheses rather than inline
    # `(by tac : T)` terms inside the nlinarith bracket list.  A multi-line term
    # inside `nlinarith [...]` must stay strictly right of the tactic's own
    # column, which silently breaks whenever the surrounding indentation moves.
    IM = lr(d["IM_LO"])
    if d["IM_LO"] < 0:
        q2hint = "\n".join([
            "      have hq1bnd : (0 : \u211d) \u2264 (%s : \u211d) - q1 := by linarith" % lr(R["Bhi"]),
            "      have himsgn : (0 : \u211d) \u2264 -(%s : \u211d) := by norm_num" % IM,
            "      have hQ2 : (%s : \u211d) * (%s : \u211d) \u2264 q1 * (%s : \u211d) := by"
            % (lr(R["Bsel"]), IM, IM),
            "        nlinarith [mul_nonneg hq1bnd himsgn]",
        ])
        why = ("Bhi", "<")
    else:
        q2hint = "\n".join([
            "      have hq1bnd : (0 : \u211d) \u2264 q1 - (%s : \u211d) := by linarith" % lr(R["Blo"]),
            "      have himsgn : (0 : \u211d) \u2264 (%s : \u211d) := by norm_num" % IM,
            "      have hQ2 : (%s : \u211d) * (%s : \u211d) \u2264 q1 * (%s : \u211d) := by"
            % (lr(R["Bsel"]), IM, IM),
            "        nlinarith [mul_nonneg hq1bnd himsgn]",
        ])
        why = ("Blo", ">=")
    A("/-- Worst-case arithmetic over the box rectangle.  p1*p2 is maximised at")
    A("(Ahi, RE_LO) because Ahi < 0 <= RE_LO; q1*q2 is minimised at (%s, IM_LO)" % why[0])
    A("because IM_LO %s 0.  Selecting the wrong B endpoint here is the known" % why[1])
    A("soundness trap; it is resolved at generation time from the sign of the")
    A("DECLARED IM_LO, never assumed. -/")
    A("theorem box%s_re_xi_le :" % K)
    A("    \u2200 %s : \u211d, (%s : \u211d) \u2264 %s \u2192 %s \u2264 %s \u2192"
      % (SIG, SIGMA_LITERAL[0], SIG, SIG, SIGMA_LITERAL[1]))
    A("      (riemannXiEntire (\u27e8%s, 15\u27e9 : \u2102)).re \u2264 (%s : \u211d) :="
      % (SIG, lr(R["M"])))
    A("  %s.re_xi_upper_bound_from_enclosures" % ENC)
    A("    box%s_re_enclosure box%s_im_enclosure" % (K, K))
    A("    box%s_A_lo_bound box%s_A_hi_bound" % (K, K))
    A("    box%s_B_lo_bound box%s_B_hi_bound" % (K, K))
    A("    (%s : \u211d)" % lr(R["M"]))
    A("    (by")
    A("      intro p1 p2 q1 q2 hp1lo hp1hi hp2lo hp2hi hq1lo hq1hi hq2lo hq2hi")
    A("      have hp2nn : (0 : \u211d) \u2264 p2 := le_trans (by norm_num) hp2lo")
    A("      have hq1nn : (0 : \u211d) \u2264 q1 := le_trans (by norm_num) hq1lo")
    A("      have hA1 : p1 * p2 \u2264 (%s : \u211d) * p2 :=" % lr(R["Ahi"]))
    A("        mul_le_mul_of_nonneg_right hp1hi hp2nn")
    A("      have hA2 : (%s : \u211d) * p2 \u2264 (%s : \u211d) * (%s : \u211d) :="
      % (lr(R["Ahi"]), lr(R["Ahi"]), lr(d["RE_LO"])))
    A("        mul_le_mul_of_nonpos_left hp2lo (by norm_num)")
    A("      have hQ1 : q1 * (%s : \u211d) \u2264 q1 * q2 :=" % lr(d["IM_LO"]))
    A("        mul_le_mul_of_nonneg_left hq2lo hq1nn")
    A(q2hint)
    A("      have hAval : (%s : \u211d) * (%s : \u211d) = (%s : \u211d) := by norm_num"
      % (lr(R["Ahi"]), lr(d["RE_LO"]), lr(R["AR"])))
    A("      have hBval : (%s : \u211d) * (%s : \u211d) = (%s : \u211d) := by norm_num"
      % (lr(R["Bsel"]), lr(d["IM_LO"]), lr(R["BI"])))
    A("      linarith [hA1, hA2, hQ1, hQ2, hAval, hBval])")
    A("")
    A("/-- **BOX %s CLOSED** -- unconditional top-edge negativity at t = 15" % K)
    A("for sigma in [%s, %s]. -/" % (slo, shi))
    A("theorem top15_box%s_re_lt_neg_1e4 {%s : \u211d}" % (K, SIG))
    A("    (h0 : (%s : \u211d) \u2264 %s) (h1 : %s \u2264 %s) :"
      % (SIGMA_LITERAL[0], SIG, SIG, SIGMA_LITERAL[1]))
    A("    (riemannXiEntire (\u27e8%s, 15\u27e9 : \u2102)).re < -(1/10000 : \u211d) :=" % SIG)
    A("  lt_of_le_of_lt (box%s_re_xi_le %s h0 h1) (by norm_num)" % (K, SIG))
    A("")
    A("end %s" % ns)
    return "\n".join(O) + "\n"


def emit_audit(K, slo, shi):
    ns = "PrincipiaTractalis.RiemannXiBox%sBridge" % K
    O = []
    A = O.append
    A("/-")
    A("# PF.Analytic.RiemannXiBox%sBridgeAudit" % K)
    A("")
    A("Axiom audit for the complete r331b box-%s closure chain: the four cumulative" % K)
    A("finite bounds, the Lambda-0 bounds after one application of the section-8")
    A("envelope, the exact rational margins, the coefficient enclosures, both r331a")
    A("box enclosures, and the unconditional top-edge theorem.")
    A("")
    A("Expected only: [propext, Classical.choice, Quot.sound] for every check.")
    A("No project axioms.  No sorry.  No native_decide.")
    A("")
    A("AUTO-GENERATED by scripts/emit_box_bridge.py.")
    A("")
    A("SPDX-License-Identifier: Apache-2.0")
    A("-/")
    A("")
    A("import PF.Analytic.RiemannXiBox%sBridge" % K)
    A("")
    A("open %s" % ns)
    A("")
    A("-- cumulative finite bounds over [1,5]")
    for n in ("finite_re_lower", "finite_re_upper", "finite_im_lower", "finite_im_upper"):
        A("#print axioms %s" % n)
    A("")
    A("-- Lambda-0 bounds (section-8 envelope applied exactly once)")
    for n in ("re_Lambda0_lower", "re_Lambda0_upper", "im_Lambda0_lower", "im_Lambda0_upper"):
        A("#print axioms %s" % n)
    A("")
    A("-- exact rational margins")
    for n in ("RE_MARGIN_pos", "IM_LO_MARGIN_pos", "IM_HI_MARGIN_pos"):
        A("#print axioms %s" % n)
    A("")
    A("-- coefficient enclosures")
    for n in ("A_lo_bound", "A_hi_bound", "B_lo_bound", "B_hi_bound"):
        A("#print axioms box%s_%s" % (K, n))
    A("")
    A("-- r331a box enclosures")
    A("#print axioms box%s_re_enclosure" % K)
    A("#print axioms box%s_im_enclosure" % K)
    A("")
    A("-- BOX %s CLOSED" % K)
    A("#print axioms box%s_re_xi_le" % K)
    A("#print axioms top15_box%s_re_lt_neg_1e4" % K)
    return "\n".join(O) + "\n"


# ----------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True, help="path to PF_Lean4_Code")
    ap.add_argument("--box", required=True, help="box directory index, e.g. 2 or 106")
    ap.add_argument("--manifest",
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         "manifests", "strip_manifest_v2.json"),
                    help="Gate-B partition manifest (in-repo copy by default)")
    ap.add_argument("--denom", type=int, default=12,
                    help="declared-bound rounding at 10^-DENOM (default 12)")
    ap.add_argument("--check-only", action="store_true")
    args = ap.parse_args()

    K = args.box
    if K == "0":
        sys.exit("REFUSED: box 0 has a hand-written, kernel-green bridge. "
                 "It is the reference for this generator, not a target.")

    shi_dec, p1, p2 = decode_sigma_from_M(args.root, K)
    segs, slo, shi = read_segments(args.root, K)
    if shi != shi_dec:
        sys.exit("FATAL: sigma_hi from p1 decode (%s) != segment hypotheses (%s) for box %s"
                 % (shi_dec, shi, K))

    strip_id, pred = None, None
    if os.path.exists(args.manifest):
        man = json.load(open(args.manifest))
        for s in man["strips"]:
            if F(s["slo"]) == slo and F(s["shi"]) == shi:
                strip_id, pred = s["id"], F(s["margin"])
                break

    R = certify(segs, slo, shi, args.denom)
    gate(K, slo, shi, R)

    print("box %-4s sigma [%s, %s]  p1=%s  %s"
          % (K, slo, shi, p1,
             "manifest strip %d" % strip_id if strip_id is not None else "NOT IN MANIFEST"))
    print("  certified RE_LO = %s" % R["cert"]["RE_LO"])
    print("                  ~ %.12e" % float(R["cert"]["RE_LO"]))
    print("  certified IM_LO ~ %.12e   IM_HI ~ %.12e"
          % (float(R["cert"]["IM_LO"]), float(R["cert"]["IM_HI"])))
    # HEADLINE FIRST.  The xi-space margin is the consumer-facing figure for a box;
    # the Lambda-space margins below sit at ~1e-13 by construction (the declared
    # bounds are outward-rounded at 1e-12) and would misread as knife-edge if quoted
    # without that context.  Printed in this order so a downstream `grep` that keeps
    # log order reports the headline first.
    print("  xi bound M = %.9e   xi margin %+.6e  [HEADLINE]  (Bsel=%s, IM_LO %s 0)"
          % (float(R["M"]), float(R["xi_margin"]), R["Bsel"],
             "<" if R["decl"]["IM_LO"] < 0 else ">="))
    print("  MARGINS [internal Lambda-space enclosure check, NOT the headline; ~1e-13 "
          "is the 1e-12 rounding of the declared bounds, not tightness]  "
          "RE %+.6e   IM_LO %+.6e   IM_HI %+.6e"
          % (float(R["margins"]["RE"]), float(R["margins"]["IM_LO"]),
             float(R["margins"]["IM_HI"])))
    if pred is not None:
        print("  manifest predicted xi margin %+.6e   delta %+.3e"
              % (float(pred), float(R["xi_margin"] - pred)))

    if args.check_only:
        print("  [check-only] nothing written")
        return

    bpath = os.path.join(args.root, "PF", "Analytic", "RiemannXiBox%sBridge.lean" % K)
    apath = os.path.join(args.root, "PF", "Analytic", "RiemannXiBox%sBridgeAudit.lean" % K)
    with open(bpath, "w", encoding="utf-8") as f:
        f.write(emit_bridge(K, slo, shi, segs, R, strip_id, pred))
    with open(apath, "w", encoding="utf-8") as f:
        f.write(emit_audit(K, slo, shi))
    print("  wrote %s (%d lines)"
          % (bpath, sum(1 for _ in open(bpath, encoding="utf-8"))))
    print("  wrote %s" % apath)


if __name__ == "__main__":
    main()
