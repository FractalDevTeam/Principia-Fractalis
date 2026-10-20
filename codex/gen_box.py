#!/usr/bin/env python3
"""
gen_box.py -- ONE c-parametric producer for a complete R1 pilot box.

    python3 gen_box.py --c 55/8 --out <dir>

emits the whole pack for an unconditional `R1` box centred at `c`:

    CoreDefs_<tag>_2026_10_16.lean                     (1)
    Seg0{1,2}Midpoint_<tag>_2026_10_20.lean            (2)   midpoint tier
    Seg0{1..6}Range_<tag>_2026_10_16.lean              (6)   range-brick tier
    Assemble_<tag>_threehalves_HYBRID_2026_10_20.lean  (1)
    ResidueBound_<tag>_three_halves_to_5_2026_10_20.lean
    ResidueBoundTight_<tag>_2026_10_20.lean
    AnalyticTailBound_<tag>_2026_10_20.lean
    OmegaTailBound_<tag>_2026_10_20.lean                (4)  add-ons
    R1_<tag>_r<r>_HYBRID_2026_10_20.lean                (1)  gate composition
    R1_<tag>_r<r>_pointwise_UNCONDITIONAL_2026_10_20.lean (1)

HOW EACH PIECE IS PARAMETRIC IN c
---------------------------------
* CoreDefs, the 4 add-ons and the pilot: pure textual substitution. `c` enters
  only through the phase `cos((c/2)u)` / `sin((c/2)u)`, and every add-on
  majorant discards it via |cos|,|sin| <= 1 -- verified exhaustively (no
  cos_pos / cos_nonneg / cos_le_* anywhere). So the three add-on constants are
  c-independent: residue 7/10^7, analytic tail 12/10^8, omega-gap 1/10^21.
* Range panels: the existing generator is ALREADY parametric -- its six
  instances differ only in `C_VALUE`/`C_HALF` and the `c13_2` token. We retag
  the source and exec it.
* Midpoint panels: NOT previously parametric. See below.
* Hybrid assemble: parses the emitted panels and sums them, halving the
  midpoint bounds (`fourier_plus_term` carries an explicit factor 2, so
  `f_plus = 2 * nodeR_..._N3`).

THE MIDPOINT M BOUND -- the one piece that needed real work
-----------------------------------------------------------
`gen_fourier_panels_c27_4_midpoint.py` hardcodes `M := 24` and the M-bound
proof at `T = 1/4`, while computing panel errors with `M_for_seg` = 24/30/72.
It therefore reproduces only Seg01 of its own six output files; the other five
carry (M,T) = (24,1/2),(30,3/4),(30,1),(72,5/4),(72,3/2) and must have been
hand-edited. This producer closes that gap: it computes M from c and T using
*the same coarse bounds the emitted Lean proof uses*

    pi <= 4,  exp(T/2) <= 2,  exp(T) <= 2,  exp(-pi(n+1)^2) <= (1/23)^((n+1)^2)

so the emitted constants are guaranteed to be provable with the emitted proof.
Sanity: at (c,T) = (27/4,1/4) the formula gives 18.65 -> target 19, which is
exactly the landed constant, and the total 8.4315 matches the generator's own
comment "symbolic upper bound ~ 8.44".

Midpoint is emitted only for segments 1-2 (T <= 1/2). That is not a limitation
-- it is the measured optimum. The midpoint error is M*h^3/24 with M growing
along u while the range-brick spread shrinks as the integrand decays; midpoint
wins segments 1-2 and loses segment 6 by 863x. T <= 1/2 < log 2 is also
exactly the range where `exp(T) <= 2` holds, which is what the emitted proof
needs.

BOX GEOMETRY -- read this before running it in a loop
-----------------------------------------------------
`r` and `L` are parameters, not constants, because the fixed `r = 1/16`,
`L = 1` shape does NOT survive the march:

  * `R1_box_centered_of_lb` needs `L*r < Mc_lb <= Re xi(1+ic)`, and
    `Re xi(1+ic)` decays to 0 at its first zero 13.98838.
  * With `L = 1`: `Mc_lb = 1/8` fails past c = 7.502, and `r = 1/16` fails
    past c = 9.046. Covering [6.75, 13] needs ~193 boxes.
  * With a box-local `L = 1.25*|d/dt Re xi|` it needs **3**.

`L = 1` is 17.6x too loose at c = 6.75 and 261x at c = 13. The gap is NOT in
the Lambda0 constants: xi' = ((2s-1)L0 + s(s-1)L0')/2 and the two pieces
cancel (2.5x at c=6.75, 36x at c=13), so the best possible triangle bound is
~0.157-0.173 and flat in t. Closing it needs an enclosure of `deriv edgeRe`
itself, panel-style -- not a better constant.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-20.
"""
import argparse
import io
import os
import re
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_box_part2 as P2

# Templates: the c = 27/4 generators (range + midpoint) and the c = 13/2
# hand-written modules that port textually.
RANGE_TPL = os.path.join(HERE, "gen", "gen_fourier_panels_c27_4.py")
MID_TPL = os.path.join(HERE, "gen", "gen_fourier_panels_c27_4_midpoint.py")
PORT_DIR = os.path.join(HERE, "addons")      # c=13/2 CoreDefs + 4 add-ons + pilot

LF = chr(10)
PANEL_WIDTH = F(1, 32)
N_PANELS = 8
MID_SEGS = (1, 2)                   # midpoint tier: T <= 1/2
RANGE_SEGS = (1, 2, 3, 4, 5, 6)     # range emitted for all six; 3-6 used by the hybrid
ADDON = F(7, 10**7) + F(12, 10**8) + F(1, 10**21)

# omega(1) to 30 digits; L0 c = 2*omega(1)*(1 + 1/c) + 1/(2 c^2)
OMEGA1 = F(4321741, 10**8)   # > omega(1) = 0.04321740560665..., rounded UP


def L0_val(c):
    """The Lean `L0` of R1BoxLocalL_2026_10_20, as an exact rational in c
    (omega(1) rounded UP so the computed value is an upper bound)."""
    return 2 * OMEGA1 * (1 + 1 / F(c)) + 1 / (2 * F(c) ** 2)


# --------------------------------------------------------------------------
# c formatting
# --------------------------------------------------------------------------
def tag(c):
    """Fraction(27,4) -> 'c27_4'."""
    return f"c{c.numerator}_{c.denominator}" if c.denominator != 1 else f"c{c.numerator}"


def lean_frac(q):
    q = F(q)
    return f"{q.numerator}/{q.denominator}" if q.denominator != 1 else str(q.numerator)


def dec(q):
    """Exact decimal string; raises if q does not terminate."""
    q = F(q)
    d, e2, e5 = q.denominator, 0, 0
    while d % 2 == 0:
        d //= 2
        e2 += 1
    while d % 5 == 0:
        d //= 5
        e5 += 1
    if d != 1:
        raise ValueError(f"{q} is not a terminating decimal")
    k = max(e2, e5)
    scaled = q.numerator * 10**k // q.denominator
    s = str(abs(scaled)).rjust(k + 1, "0")
    out = (s[:-k] + "." + s[-k:]) if k else s
    return ("-" if q < 0 else "") + out


# --------------------------------------------------------------------------
# The midpoint M bound, computed with the SAME coarse bounds the Lean uses
# --------------------------------------------------------------------------
PI_UB = F(4)          # pi <= 4                        (Real.pi_lt_four)
E_UB = F(2)           # exp(T/2) <= 2  for T <= 2 log 2
T_UB = F(2)           # exp(T)   <= 2  for T <= log 2
B_UB = {n: F(1, 23) ** ((n + 1) ** 2) for n in range(3)}   # exp(-pi(n+1)^2)


def termM_coarse(c, n, T):
    """Rational upper bound on `fourier_plus_termM c n T`, using exactly the
    coarse factor bounds the emitted proof supplies. Every term is positive and
    monotone increasing in each factor, so this is sound."""
    A = PI_UB * (n + 1) ** 2
    E, Th, B, G = E_UB, T_UB, B_UB[n], abs(c) / 2
    return (E / 4 * (2 * B)
            + (E + 1) * (2 * A * (A * Th - 1) * B)
            + (E + 1) * (2 * B) * G ** 2
            + 2 * (E / 2) * (2 * A * B)
            + 2 * (E / 2) * (2 * B) * G
            + 2 * (E + 1) * (2 * A * B) * G)


def m_data(c, T):
    """(per-n integer targets, M) with M the least multiple of 3 >= sum.
    M must be a multiple of 3 so that M*(1/32)^3/24 = M/786432 terminates
    (786432 = 2^18 * 3)."""
    tg = [int(termM_coarse(c, n, T)) + 1 for n in range(3)]
    s = sum(tg)
    M = s + (-s) % 3
    assert F(M, 786432) == F(M) * PANEL_WIDTH ** 3 / 24
    dec(F(M, 786432))        # must terminate
    return tg, M


# --------------------------------------------------------------------------
# Retagging: rewrite a c=27/4 (or c=13/2) source for a new c
# --------------------------------------------------------------------------
NB, NA = r"(?<![0-9.])", r"(?![0-9.])"


def _sub(s, pat, rep, desc, require=True):
    s2, k = re.subn(NB + re.escape(pat) + NA, rep, s)
    if require:
        assert k > 0, f"retag: pattern {pat!r} ({desc}) not found"
    return s2, k


def retag(src, c_from, c_to, *, is_python, set_params=False):
    """Rewrite every c-dependent token. Numeric rewrites are anchored with
    negative lookaround on digits and dots (the 231/10^6 hazard) and each is
    asserted. Collision-prone exp literals are routed through placeholders."""
    if c_from == c_to:
        # identity: nothing to rewrite, and the stale-literal assertions below
        # would fire on the (correct) surviving c_from literals. Used to
        # regenerate a known-good centre as a self-test.
        return src

    s = src
    # 1. identifier token
    t_from, t_to = tag(c_from), tag(c_to)
    n_tok = s.count(t_from)
    assert n_tok > 0, f"retag: token {t_from} absent"
    s = s.replace(t_from, t_to)
    assert t_from not in s

    # 2. phase decimal c/2 (CoreDefs / Interval mirrors use a decimal literal)
    ph_from, ph_to = dec(c_from / 2), dec(c_to / 2)
    s, _ = _sub(s, ph_from, ph_to, "phase decimal", require=False)

    # 2b. the type-ascribed form |((27:' + chr(8477) + ')/4)| -- the digits there are followed by
    #     ':' not '/', so the bare-fraction rule below does NOT see them. Missing
    #     this leaves a half-rewritten  |((27:' + chr(8477) + ')/4)| = 55/8  which is false.
    #     An INTEGER target must NOT be written "(7:R)/1": Lean normalises that
    #     occurrence to |7|, so the later `rw [habs_c]` cannot find the pattern,
    #     and the main goal `7/1 = 7` is not closed by rw's rfl, so `norm_num`
    #     consumes it and the positivity side goal `0 < 7/1` survives. (For a
    #     genuine fraction the main goal IS closed by rfl, which is why 27/4 and
    #     55/8 worked and c = 7 was the first centre to fail.)
    assert c_from.denominator != 1, (
        f"retag: integer source centre {c_from} would make asc_from a prefix "
        "of the fractional form")
    asc_from = f"({c_from.numerator}:{chr(8477)})/{c_from.denominator}"
    asc_to = (f"({c_to.numerator}:{chr(8477)})/{c_to.denominator}"
              if c_to.denominator != 1
              else f"({c_to.numerator}:{chr(8477)})")
    n_asc = s.count(asc_from)
    s = s.replace(asc_from, asc_to)

    # 3. c/2 and c as fractions
    s, _ = _sub(s, lean_frac(c_from / 2), lean_frac(c_to / 2), "c/2 fraction",
                require=False)
    s, _ = _sub(s, lean_frac(c_from), lean_frac(c_to), "c fraction", require=False)
    sp_from = lean_frac(c_from).replace("/", " / ")
    if "/" in lean_frac(c_from):
        s, _ = _sub(s, sp_from, lean_frac(c_to).replace("/", " / "),
                    "c spaced fraction", require=False)
    # c^2
    s, _ = _sub(s, lean_frac(c_from ** 2), lean_frac(c_to ** 2), "c^2", require=False)

    if set_params:
        # the two generator parameters (only the RANGE generator defines them;
        # the midpoint generator imports them from it)
        s2, k = re.subn(r"C_VALUE = Fraction\(\d+,\s*\d+\)",
                        f"C_VALUE = Fraction({c_to.numerator}, {c_to.denominator})", s)
        assert k == 1, "retag: C_VALUE not found"
        h = c_to / 2
        s2, k = re.subn(r"C_HALF\s*= Fraction\(\d+,\s*\d+\)",
                        f"C_HALF  = Fraction({h.numerator}, {h.denominator})", s2)
        assert k == 1, "retag: C_HALF not found"
        s = s2

    # 4. post-assertions: no stale c literals
    assert asc_from not in s, f"retag: stale ascribed {asc_from}"
    # Catches the whole integer-centre class, for every future centre: Lean
    # normalises a /1 denominator away, so any rewrite naming it cannot match.
    assert f":{chr(8477)})/1" not in s, (
        "retag: emitted a '/1' denominator -- Lean normalises it away and "
        "later rewrites will not match (integer-centre hazard)")
    for bad in (lean_frac(c_from), dec(c_from / 2)):
        assert re.search(NB + re.escape(bad) + NA, s) is None, \
            f"retag: stale {bad!r} survived"
    return s


# --------------------------------------------------------------------------
# Loading the retagged generators
# --------------------------------------------------------------------------
def load_gen(path, c, extra_globals=None):
    src = io.open(path, encoding="utf-8").read()
    src = retag(src, F(27, 4), c, is_python=True)
    # the midpoint generator execs the range generator by path; point it at a
    # retagged copy written next to it
    g = dict(extra_globals or {})
    g["__name__"] = "_gen"
    g["__file__"] = path
    exec(compile(src, f"<{os.path.basename(path)}:{tag(c)}>", "exec"), g)
    return g


def load_both(c, workdir):
    """Retag the range generator to disk (the midpoint one execs it by path),
    then load both."""
    rsrc = retag(io.open(RANGE_TPL, encoding="utf-8").read(),
                 F(27, 4), c, is_python=True, set_params=True)
    # the retagged midpoint generator execs the range generator by the RETAGGED
    # name (its `_v1_path` literal was rewritten too), so write it under that name
    rpath = os.path.join(workdir, f"gen_fourier_panels_{tag(c)}.py")
    io.open(rpath, "w", encoding="utf-8", newline="\n").write(rsrc)
    msrc = retag(io.open(MID_TPL, encoding="utf-8").read(),
                 F(27, 4), c, is_python=True)
    mpath = os.path.join(workdir, "gen_mid.py")
    io.open(mpath, "w", encoding="utf-8", newline="\n").write(msrc)
    rg = {"__name__": "_rg", "__file__": rpath}
    exec(compile(rsrc, rpath, "exec"), rg)
    mg = {"__name__": "_mg", "__file__": mpath}
    exec(compile(msrc, mpath, "exec"), mg)
    return rg, mg


# --------------------------------------------------------------------------
# Midpoint preamble: (c, T, M, targets)-parameterised
# --------------------------------------------------------------------------
def midpoint_preamble(mg_src, c, T, M, targets, seg_idx, ns):
    """Take the midpoint generator's preamble template (already retagged in c)
    and specialise T, M and the three per-n targets."""
    i = mg_src.index("def seg_preamble_mp(seg_idx):")
    j = mg_src.index("def emit_midpoint_panel_block")
    body = mg_src[i:j]
    # the template is `return f"""..."""`
    k = body.index('return f"""') + len('return f"""')
    e = body.rindex('"""')
    tpl = body[k:e]

    s = tpl
    # Route every colliding literal through a placeholder FIRST. For T = 1/2 the
    # new E (= exp(1/4)) collides with the template's old T-hat (= exp(1/4)), so
    # an ordered in-place substitution would clobber one with the other.
    marks = [("Real.exp ((1:ℝ)/8)", "@@E@@"),
             ("Real.exp ((1:ℝ)/4)", "@@TH@@"),
             ("(1:ℝ)/8 ≤ Real.log 2", "@@ELOG@@"),
             ("(1:ℝ)/4 ≤ Real.log 2", "@@TLOG@@")]
    for a, b in marks:
        assert a in s, f"preamble: template literal {a!r} absent"
        s = s.replace(a, b)
    s = s.replace("@@E@@", f"Real.exp (({lean_frac(T/2)} : ℝ))")
    s = s.replace("@@TH@@", f"Real.exp (({lean_frac(T)} : ℝ))")
    s = s.replace("@@ELOG@@", f"({lean_frac(T/2)} : ℝ) ≤ Real.log 2")
    s = s.replace("@@TLOG@@", f"({lean_frac(T)} : ℝ) ≤ Real.log 2")
    assert "@@" not in s, "preamble: unexpanded placeholder"
    # exp(T) <= 2 needs T <= log 2; the emitted proof relies on it
    assert T <= F(693, 1000), f"T = {T} exceeds log 2; needs a different tier"
    # the `show (T/2) = ...` rewrite
    s, k1 = re.subn(re.escape("((1:ℝ)/4/2 : ℝ) = 1/8"),
                    f"(({lean_frac(T)}/2 : ℝ)) = {lean_frac(T/2)}", s)
    assert k1 == 3, f"preamble: T/2 rewrite count {k1}"
    # per-n targets and the T literal in each lemma statement
    cL = lean_frac(c)
    for n, t in enumerate(targets):
        pat = f"fourier_plus_termM ({cL}) {n} (1/4) ≤ "
        m = re.search(re.escape(pat) + r"\d+", s)
        assert m, f"preamble: target line for n={n} not found"
        s = s.replace(m.group(0), f"fourier_plus_termM ({cL}) {n} ({lean_frac(T)}) ≤ {t}")
    # the sum lemma's T
    s, k2 = re.subn(re.escape(f"fourier_plus_termM ({cL}) n (1/4) ≤ M"),
                    f"fourier_plus_termM ({cL}) n ({lean_frac(T)}) ≤ M", s)
    assert k2 == 1, f"preamble: sum lemma T count {k2}"
    # M
    s, k3 = re.subn(re.escape("abbrev M : ℝ := 24"), f"abbrev M : ℝ := {M}", s)
    assert k3 == 1, "preamble: M not found"
    # docstrings that quote T
    s = s.replace("u ∈ [0, 1/4]", f"u ∈ [0, {lean_frac(T)}]")
    s = s.replace("at T=1/4", f"at T={lean_frac(T)}")
    s = s.replace("(`exp(1/8) ≤ 2`, `exp(1/4) ≤ 2`)",
                  f"(`exp({lean_frac(T/2)}) ≤ 2`, `exp({lean_frac(T)}) ≤ 2`)")
    s = s.replace("we prove ≤ 24", f"we prove ≤ {M}")
    # no stale T literal left in a termM position (vacuous when T really is 1/4)
    if T != F(1, 4):
        assert f"fourier_plus_termM ({cL}) 0 (1/4)" not in s, "stale T=1/4 target"
        assert "(1:ℝ)/8" not in s, "stale E = exp(1/8)"
    assert "(1:ℝ)/4/2" not in s, "stale T/2 rewrite"
    return s.replace("{ns}", ns)


# --------------------------------------------------------------------------
# Textual-port components: CoreDefs, the four add-ons, the pilot
# --------------------------------------------------------------------------
C13 = F(13, 2)

PORTS = [
    # (source basename at c=13/2, destination template)
    ("CoreDefs_c13_2_2026_10_16.lean", "CoreDefs_{tag}_2026_10_16.lean"),
    ("ResidueBound_c13_2_three_halves_to_5_2026_10_16.lean",
     "ResidueBound_{tag}_three_halves_to_5_2026_10_20.lean"),
    ("ResidueBoundTight_c13_2_2026_10_18.lean",
     "ResidueBoundTight_{tag}_2026_10_20.lean"),
    ("AnalyticTailBound_c13_2_2026_10_16.lean",
     "AnalyticTailBound_{tag}_2026_10_20.lean"),
    ("OmegaTailBound_c13_2_2026_10_16.lean",
     "OmegaTailBound_{tag}_2026_10_20.lean"),
]

# module-path renames applied to every ported file (longest first)
def port_module_renames(c):
    t = tag(c)
    return [
        ("PF.Analytic.FourierPanels.ResidueBound_c13_2_three_halves_to_5_2026_10_16",
         f"PF.Analytic.FourierPanels.ResidueBound_{t}_three_halves_to_5_2026_10_20"),
        ("PF.Analytic.FourierPanels.ResidueBoundTight_c13_2_2026_10_18",
         f"PF.Analytic.FourierPanels.ResidueBoundTight_{t}_2026_10_20"),
        ("PF.Analytic.FourierPanels.AnalyticTailBound_c13_2_2026_10_16",
         f"PF.Analytic.FourierPanels.AnalyticTailBound_{t}_2026_10_20"),
        ("PF.Analytic.FourierPanels.OmegaTailBound_c13_2_2026_10_16",
         f"PF.Analytic.FourierPanels.OmegaTailBound_{t}_2026_10_20"),
        ("PF.Analytic.FourierPanels.CoreDefs_c13_2_2026_10_16",
         f"PF.Analytic.FourierPanels.CoreDefs_{t}_2026_10_16"),
        ("PF.Analytic.FourierPanels.Seg01Range_c13_2_2026_10_16",
         f"PF.Analytic.FourierPanels.Seg01Range_{t}_2026_10_16"),
    ]


PROVENANCE = """Emitted by codex/gen_box.py for c = {cl} (2026-10-20). `c` enters the node
functions only through the phase cos((c/2)u) / sin((c/2)u), and every add-on
majorant discards it via |cos|,|sin| <= 1, so the three add-on constants are
c-independent: residue 7/10^7, analytic tail 12/10^8, omega-gap 1/10^21.

SPDX-License-Identifier: Apache-2.0"""


def emit_ports(c, outdir):
    """CoreDefs + the four add-ons, by anchored textual port from c = 13/2."""
    t = tag(c)
    written = []
    for srcname, dsttpl in PORTS:
        src = io.open(os.path.join(PORT_DIR, srcname), encoding="utf-8").read()
        s = src
        for a, b in port_module_renames(c):
            s = s.replace(a, b)
        # header title line
        s = s.replace(srcname[:-5], dsttpl.format(tag=t)[:-5], 1)
        s = retag(s, C13, c, is_python=False)
        s = s.replace("SPDX-License-Identifier: Apache-2.0",
                      PROVENANCE.format(cl=lean_frac(c)), 1)
        dst = os.path.join(outdir, dsttpl.format(tag=t))
        io.open(dst, "w", encoding="utf-8", newline=LF).write(s)
        written.append(os.path.basename(dst))
    return written


# --------------------------------------------------------------------------
# Emission
# --------------------------------------------------------------------------
def emit_range(rg, c, seg, outdir):
    bricks, _audit, lo, hi, _w = rg["run_segment"](seg)
    path = os.path.join(outdir, rg["seg_file_name"](seg))
    rg["emit_lean_file"](seg, lo, hi, bricks, path)
    tot, per, ivl = {}, {}, {}
    for side, iL, iU in (("plus", 3, 4), ("minus", 5, 6)):
        tot[side] = (sum(PANEL_WIDTH * F(b[iL]) for b in bricks),
                     sum(PANEL_WIDTH * F(b[iU]) for b in bricks))
        for b in bricks:
            k, a, bb = b[0], b[1], b[2]
            per[(side, "rng", seg, k)] = (PANEL_WIDTH * F(b[iL]),
                                          PANEL_WIDTH * F(b[iU]))
            ivl[(seg, k)] = (a, bb)
    return path, tot, per, ivl


def emit_midpoint(mg, mg_src, c, seg, T, outdir):
    targets, M = m_data(c, T)
    mg["M_for_seg"] = lambda _s, _M=M: F(M)        # override the tier table
    lo, hi = mg["SEGMENTS"][seg]
    ns = mg["seg_namespace_mp"](seg)
    bricks = []
    per, ivl = {}, {}
    sums = {"plus": [F(0), F(0)], "minus": [F(0), F(0)]}
    err = F(M) * PANEL_WIDTH ** 3 / 24
    for k in range(1, N_PANELS + 1):
        a, b = mg["panel_endpoints"](lo, hi, k - 1)
        m = (a + b) / 2
        Lp, Up, Lm, Um = mg["point_bounds"](m)
        brick = mg["emit_midpoint_panel_block"](seg, k, a, b, Lp, Up, Lm, Um)
        # The panel emitter hardcodes T = 1/4 in TWO places per side -- the
        # `h_bu : u <= T` step and the `abs_fourier_*_termD2_sum_le c T 3` call.
        # This is the same T-hardcoding that limits the upstream generator to
        # Seg01: for seg 2 the panels live on [1/4, 1/2], so `u <= 1/4` is false
        # and linarith fails. Specialise both, and assert the counts.
        brick, n1 = re.subn(re.escape("have h_bu : u ≤ (1/4 : ℝ)"),
                            f"have h_bu : u ≤ ({lean_frac(T)} : ℝ)", brick)
        brick, n2 = re.subn(
            re.escape(f"termD2_sum_le ({lean_frac(c)}) (1/4) 3"),
            f"termD2_sum_le ({lean_frac(c)}) ({lean_frac(T)}) 3", brick)
        if T != F(1, 4):
            assert n1 == 2, f"panel {seg}.{k}: h_bu count {n1}, expected 2"
            assert n2 == 2, f"panel {seg}.{k}: termD2_sum_le count {n2}, expected 2"
            assert "(1/4 : ℝ)" not in brick, f"panel {seg}.{k}: stale T=1/4"
        bricks.append(brick)
        # bound on int nodeR over the panel = width*node_mid +/- err/2
        plo, phi = PANEL_WIDTH * F(Lp) - err / 2, PANEL_WIDTH * F(Up) + err / 2
        mlo, mhi = PANEL_WIDTH * F(Lm) - err / 2, PANEL_WIDTH * F(Um) + err / 2
        sums["plus"][0] += plo
        sums["plus"][1] += phi
        sums["minus"][0] += mlo
        sums["minus"][1] += mhi
        per[("plus", "mid", seg, k)] = (plo, phi)
        per[("minus", "mid", seg, k)] = (mlo, mhi)
        ivl[(seg, k)] = (a, b)
    body = mg["seg_file_header_mp"](seg, lo, hi)
    body += midpoint_preamble(mg_src, c, T, M, targets, seg, ns)
    for br in bricks:
        body += br
    body += f"end {ns}\nend FourierPanels_{tag(c)}\nend PrincipiaTractalis\n\n"
    pre = mg["seg_prefix_mp"](seg)
    nsf = f"PrincipiaTractalis.FourierPanels_{tag(c)}.{ns}"
    body += "/-! ## §Axiom check — spot-check first and last panels -/\n"
    for w in (1, N_PANELS):
        body += f"#print axioms {nsf}.{pre}{w}_plus_integral_bound\n"
        body += f"#print axioms {nsf}.{pre}{w}_minus_integral_bound\n"
    path = os.path.join(outdir, f"Seg0{seg}Midpoint_{tag(c)}_2026_10_20.lean")
    io.open(path, "w", encoding="utf-8", newline="\n").write(body)
    return path, {k: (v[0], v[1]) for k, v in sums.items()}, M, targets, per, ivl


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--c", required=True, help="box centre, e.g. 55/8")
    ap.add_argument("--r", default="1/16", help="box radius")
    ap.add_argument("--pick-r", action="store_true",
                    help="ignore --r; take the largest dyadic radius in "
                         "1/16..1/4096 whose box criterion passes with the "
                         "safety ratio, and report the ladder")
    ap.add_argument("--safety", default="1.25",
                    help="required Mc_lb / (L0*r) ratio when picking r")
    ap.add_argument("--out", required=True)
    ap.add_argument("--work", default=None)
    args = ap.parse_args()

    c, r = F(args.c), F(args.r)
    assert c > 0 and r > 0
    dec(c / 2)                       # phase must be a terminating decimal
    os.makedirs(args.out, exist_ok=True)
    work = args.work or os.path.join(args.out, "_work")
    os.makedirs(work, exist_ok=True)

    print(f"=== gen_box: c = {c} ({float(c):.6f}), r = {r}, tag = {tag(c)} ===")
    rg, mg = load_both(c, work)
    mg_src = io.open(os.path.join(work, "gen_mid.py"), encoding="utf-8").read()

    # --- CoreDefs + the four add-ons (textual ports) ---
    for nm in emit_ports(c, args.out):
        print(f"  port      : {nm}")

    # --- range panels, all six ---
    PER, IVL, MBY = {}, {}, {}
    rtot = {}
    for seg in RANGE_SEGS:
        p, tot, per, ivl = emit_range(rg, c, seg, args.out)
        rtot[seg] = tot
        PER.update(per)
        IVL.update({(seg, "rng", k): v for (sg, k), v in ivl.items()})
        print(f"  range   seg{seg}: {os.path.basename(p)}")

    # --- midpoint panels, segments 1-2 ---
    mtot = {}
    for seg in MID_SEGS:
        T = mg["SEGMENTS"][seg][1]
        p, tot, M, tg, per, ivl = emit_midpoint(mg, mg_src, c, seg, T, args.out)
        mtot[seg] = tot
        MBY[seg] = M
        PER.update(per)
        IVL.update({(seg, "mid", k): v for (sg, k), v in ivl.items()})
        print(f"  midpnt  seg{seg}: {os.path.basename(p)}  T={T} M={M} targets={tg}")

    # --- hybrid totals + Gate-1 ---
    R = [F(0), F(0)]
    I_ = [F(0), F(0)]
    for seg in RANGE_SEGS:
        src = mtot[seg] if seg in MID_SEGS else rtot[seg]
        R[0] += src["plus"][0]
        R[1] += src["plus"][1]
        I_[0] += src["minus"][0]
        I_[1] += src["minus"][1]
    gate = c * c * (R[1] + ADDON) + c * (I_[1] + ADDON)
    margin = F(3, 4) - gate
    # --- the box criterion, parameterised (R1BoxLocalL_2026_10_20) ---
    # box_of_enclosure needs  L0(c-r)*r < (1 - c^2 R_ub - c I_ub)/2 = (1-gate)/2.
    # The old shape hardcoded Mc_lb = 1/8, i.e. gate <= 3/4, which is strictly
    # stronger and fails from c = 29/4 on.
    Mlb = (F(1) - gate) / 2

    # --- radius selection ---------------------------------------------------
    # Mc_lb depends only on c, never on r, so a centre with Mc_lb <= 0 is
    # unreachable at EVERY radius -- shrinking r cannot rescue it. Where
    # Mc_lb > 0 the largest dyadic r that clears the safety ratio is taken.
    if args.pick_r:
        safety = F(args.safety)
        ladder = [F(1, 2 ** k) for k in range(4, 13)]
        chosen = None
        print()
        print(f"  Mc_lb = {float(Mlb):.8f}   radius ladder (safety {float(safety)}x):")
        for rr in ladder:
            if rr >= c:
                continue
            lr = L0_val(c - rr) * rr
            ok = Mlb > 0 and lr * safety < Mlb
            ratio = float(Mlb / lr) if lr > 0 else float("nan")
            print(f"    r = {lean_frac(rr):>9}  L0*r = {float(lr):.8f}  "
                  f"ratio = {ratio:7.2f}x  {'OK' if ok else '--'}")
            if ok and chosen is None:
                chosen = rr
        if chosen is None:
            print("  NO radius in the ladder works at this centre.")
            if Mlb <= 0:
                print("  Mc_lb <= 0: unreachable at ANY radius -- the panel "
                      "enclosure, not the box geometry, is the wall here.")
            return 1
        r = chosen
        print(f"  chosen r = {lean_frac(r)}  (box [{float(c-r):.6f}, {float(c+r):.6f}])")

    Lr = L0_val(c - r) * r
    print()
    print(f"  hybrid plus  [0,3/2] : [{float(R[0]):.10f}, {float(R[1]):.10f}]")
    print(f"  hybrid minus [0,3/2] : [{float(I_[0]):.10f}, {float(I_[1]):.10f}]")
    print(f"  gate lhs = {float(gate):.8f}")
    print(f"  provable Mc_lb = (1-gate)/2 = {float(Mlb):.8f}")
    print(f"  L0({float(c-r):.4f})*r      = {float(Lr):.8f}")
    print(f"  BOX CRITERION  L0*r < Mc_lb : "
          f"{'PASS' if Lr < Mlb else 'FAIL'}  (ratio {float(Mlb/Lr):.1f}x)"
          if Lr > 0 else "")
    print(f"  [old shape, Mc_lb=1/8] margin vs 3/4 = {float(margin):+.8f} "
          f"{'PASS' if margin > 0 else 'FAIL'}")
    if Lr >= Mlb:
        print("  BOX CRITERION FAILS at this centre -- refusing to emit the pilot.")
        return 1
    print("  BOX CRITERION PASSES")

    # --- hybrid assemble ---
    panels = []
    for seg in MID_SEGS:
        for k in range(1, N_PANELS + 1):
            a, b = IVL[(seg, "mid", k)]
            panels.append(("mid", seg, k, a, b))
    for seg in (3, 4, 5, 6):
        for k in range(N_PANELS):
            a, b = IVL[(seg, "rng", k)]
            panels.append(("rng", seg, k, a, b))
    panels.sort(key=lambda e: e[3])
    assert panels[0][3] == 0 and panels[-1][4] == F(3, 2), "panels do not tile [0,3/2]"
    for i in range(len(panels) - 1):
        assert panels[i][4] == panels[i + 1][3], f"panel gap at {i}"
    ap, tots, marg2 = P2.emit_assemble(c, tag, lean_frac, dec, args.out,
                                       panels, PER, MBY)
    print(f"  assemble  : {os.path.basename(ap)}  (margin {float(marg2):+.8f})")
    assert abs(marg2 - margin) < F(1, 10**9), "assemble margin disagrees with the sweep"

    # --- gate-composition pilot ---
    gp = P2.emit_gate_pilot(c, r, tag, lean_frac, args.out, R[1], I_[1], margin)
    print(f"  pilot     : {os.path.basename(gp)}")

    # --- the UNCONDITIONAL pilot (the edge-identity chain) ---
    up = P2.emit_uncond_pilot(c, r, tag, lean_frac, retag, HERE, args.out,
                              (R[0], R[1], I_[0], I_[1]))
    print(f"  pilot     : {os.path.basename(up)}")
    # --- build order: only the files the chain actually imports ---
    # Emitting is free; compiling is 3.4-7.4 GB and ~8 min per panel file, so
    # the march must not compile dead weight. Seg02Range is emitted for
    # completeness (an all-range-brick comparison) but the HYBRID chain uses
    # midpoint on segment 2, so nothing imports it.
    imported = set()
    for fn in sorted(os.listdir(args.out)):
        if not fn.endswith(".lean"):
            continue
        for line in io.open(os.path.join(args.out, fn), encoding="utf-8"):
            if line.startswith("import PF.Analytic.FourierPanels."):
                imported.add(line.strip().split(".")[-1])
    t = tag(c)
    order = ([f"CoreDefs_{t}_2026_10_16"]
             + [f"Seg0{k}Range_{t}_2026_10_16" for k in RANGE_SEGS]
             + [f"Seg0{k}Midpoint_{t}_2026_10_20" for k in MID_SEGS]
             + [f"ResidueBound_{t}_three_halves_to_5_2026_10_20",
                f"ResidueBoundTight_{t}_2026_10_20",
                f"AnalyticTailBound_{t}_2026_10_20",
                f"OmegaTailBound_{t}_2026_10_20",
                f"Assemble_{t}_threehalves_HYBRID_2026_10_20"])
    needed = [m for m in order if m in imported or m.startswith("Assemble_")]
    dead = [m for m in order if m not in needed]
    io.open(os.path.join(args.out, "_buildorder.txt"), "w", encoding="utf-8").write(
        LF.join(needed) + LF)
    print()
    print(f"  build order ({len(needed)} modules) -> _buildorder.txt")
    if dead:
        print(f"  emitted but NOT imported (do not compile): {', '.join(dead)}")

    io.open(os.path.join(args.out, "_totals.txt"), "w", encoding="utf-8").write(
        LF.join([lean_frac(R[0]), lean_frac(R[1]), lean_frac(I_[0]),
                 lean_frac(I_[1]), lean_frac(margin)]) + LF)
    return 0


if __name__ == "__main__":
    sys.exit(main())
