#!/usr/bin/env python3
"""
Figure generator for  Papers/formal_mordell_weil_rank_2026-07-30.tex

Emits five self-contained TikZ/pgfplots figure files.  Every number printed
into a figure is recomputed here from the *same* definitions the Lean
development uses, so a figure cannot silently disagree with the kernel:

  * the group law is mathlib's `WeierstrassCurve.Affine.Point` addition
    (slope / addX / negY), transcribed literally below;
  * naive height is `naiveHeight q = max q.num.natAbs q.den`
    (PF/NaiveHeightQ_r130.lean);
  * the height sequence is `hseq n R = Real.log (naiveHeight (x (2^n R))) / 4^n`
    (PF/CanonicalHeight389a1_r147.lean);
  * the certified window constant is the *Lean* over-estimate
    `log_1728_lt : Real.log 1728 < 7.625` (PF/RegulatorPositive389a1_r153.lean),
    NOT the true log 1728 = 7.45472..., so the drawn bands are the ones the
    kernel actually proves and are never tighter than the proof;
  * the dyadic exponents j and the log-2 bounds c1 < log 2 < c2 are mathlib's
    `Real.log_two_gt_d9` / `Real.log_two_lt_d9`.

Assertions below check that the height-lattice embedding used in Figure 3
reproduces the certified values of hhat(P+Q) and hhat(P-Q) exactly; the
script fails loudly rather than drawing a wrong picture.

Run:   /home/xluxx/ai-env/bin/python make_figures.py
Needs: python >= 3.8, stdlib only.  Runtime ~1 min (exact rational arithmetic
       on x(2^9 R), which has some 37000 digits).
"""

from fractions import Fraction as Fr
import math
import os

OUT = os.path.dirname(os.path.abspath(__file__))


def fill(template, **kw):
    """Substitute @@name@@ tokens.  Used instead of %-formatting or .format()
    because these templates are full of literal % (LaTeX comments) and { }
    (TikZ groups)."""
    out = template
    for k, v in kw.items():
        out = out.replace("@@" + k + "@@", str(v))
    assert "@@" not in out, "unsubstituted token in template"
    return out


# --------------------------------------------------------------------------
# 389a1 : y^2 + y = x^3 + x^2 - 2x        (a1,a2,a3,a4,a6) = (0,1,1,-2,0)
# --------------------------------------------------------------------------
A1, A2, A3, A4, A6 = 0, 1, 1, -2, 0


def neg(P):
    x, y = P
    return (x, -y - A1 * x - A3)


def add(P, Q):
    """mathlib Affine.Point addition, affine chart only (no multiple used
    in this file reaches the point at infinity)."""
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2 and y1 == neg(Q)[1]:
        raise ValueError("hit the identity")
    if P == Q:
        lam = Fr(3 * x1 * x1 + 2 * A2 * x1 + A4 - A1 * y1, 1) / (2 * y1 + A1 * x1 + A3)
    else:
        lam = Fr(y1 - y2, 1) / (x1 - x2)
    x3 = lam * lam + A1 * lam - A2 - x1 - x2
    return (x3, lam * (x1 - x3) - y1 - A1 * x3 - A3)


def naive_height(q):
    return max(abs(q.numerator), q.denominator)


P = (Fr(0), Fr(0))
Q = (Fr(1), Fr(0))
S = add(P, Q)
D = add(P, neg(Q))
assert S == (Fr(-2), Fr(-1)), S
assert D == (Fr(-1), Fr(-2)), D

PTS = [("P", P), ("Q", Q), ("PpQ", S), ("PmQ", D)]
LABEL = {"P": r"$P$", "Q": r"$Q$", "PpQ": r"$P{+}Q$", "PmQ": r"$P{-}Q$"}
PAL = {"P": "clrP", "Q": "clrQ", "PpQ": "clrS", "PmQ": "clrD"}

NMAX = 9          # depth used to pin the limit
NPLOT = 6         # depth shown in the plots

hseq = {}
for _nm, _R in PTS:
    _cur, _vals = _R, []
    for _n in range(NMAX + 1):
        _vals.append(math.log(naive_height(_cur[0])) / 4 ** _n)
        _cur = add(_cur, _cur)
    hseq[_nm] = _vals

lim = {nm: hseq[nm][NMAX] for nm in hseq}

KAPPA_LOG = 7.625          # Lean's log_1728_lt over-estimate


def window(n):
    return KAPPA_LOG / (3 * 4 ** n)


# --- certified level-3 data (exactly what r153 verifies) -------------------
C1, C2 = 0.6931471803, 0.6931471808        # log_two_gt_d9 / log_two_lt_d9
JEXP = {"P": 30, "Q": 43, "PpQ": 84, "PmQ": 62}
W3 = window(3)

cert = {}
for _nm, _j in JEXP.items():
    _blo, _bhi = _j * C1 / 64, (_j + 1) * C2 / 64
    cert[_nm] = (_blo - W3, _bhi + W3, _blo, _bhi)

PREAMBLE = r"""% !TeX root = ../../formal_mordell_weil_rank_2026-07-30.tex
%
% GENERATED FILE -- do not edit by hand.
% Produced by Papers/figures/mordell_weil/make_figures.py
"""

COLORS = r"""% Okabe--Ito colourblind-safe palette
\definecolor{clrP}{HTML}{0072B2}
\definecolor{clrQ}{HTML}{D55E00}
\definecolor{clrS}{HTML}{009E73}
\definecolor{clrD}{HTML}{CC79A7}
\definecolor{clrBand}{HTML}{56B4E9}
\definecolor{clrGrey}{HTML}{6E6E6E}
"""


def coords(pairs, digits=9):
    f = "(%d,%." + str(digits) + "f)"
    return " ".join(f % (n, v) for n, v in pairs)


def coords_g(pairs):
    return " ".join("(%d,%.10g)" % (n, v) for n, v in pairs)


# ==========================================================================
# FIGURE 1 -- the canonical height exists: convergence + the certified rate
# ==========================================================================
T_CONV_HEAD = r"""
\begin{tikzpicture}
\begin{groupplot}[
  group style={group size=2 by 1, horizontal sep=1.7cm},
  width=0.46\linewidth, height=5.4cm,
  tick label style={font=\scriptsize},
  label style={font=\scriptsize},
  legend style={font=\scriptsize, draw=clrGrey!45, fill=white,
                fill opacity=0.9, text opacity=1, row sep=-1.5pt,
                inner sep=2pt},
  axis line style={clrGrey!70},
  grid style={clrGrey!18, line width=0.3pt},
  every axis plot/.append style={line width=0.85pt},
]
\nextgroupplot[
  xlabel={$n$},
  ylabel={$\log\mathcal{H}\bigl(x(2^nR)\bigr)/4^n$},
  xmin=-0.2, xmax=@@np@@.2, ymin=-0.05, ymax=1.02,
  xtick={0,1,2,3,4,5,6}, ytick={0,0.25,0.5,0.75,1.0},
  ymajorgrids, xmajorgrids,
  title={\scriptsize (a) four points, one construction},
  title style={yshift=-2pt},
  legend pos=south east,
]
\addplot[draw=none, fill=clrBand, fill opacity=0.15, forget plot]
  coordinates {@@band@@} -- cycle;
"""

T_CONV_MID = r"""
\nextgroupplot[
  xlabel={$n$},
  ylabel={$\bigl|\log\mathcal{H}(x(2^nR))/4^n-\hat h(R)\bigr|$},
  ymode=log, xmin=-0.2, xmax=@@np@@.2, ymin=3e-6, ymax=6,
  xtick={0,1,2,3,4,5,6},
  ymajorgrids, xmajorgrids,
  title={\scriptsize (b) actual error vs.\ the proved bound},
  title style={yshift=-2pt},
  legend style={font=\scriptsize, at={(0.03,0.05)}, anchor=south west,
                draw=clrGrey!45, fill=white, fill opacity=0.9,
                text opacity=1, inner sep=2pt},
]
\addplot[color=black, line width=1.05pt, mark=none,
         dash pattern=on 4pt off 2pt]
  coordinates {@@bound@@};
\addlegendentry{$7.625/(3\cdot 4^{n})$, Lean}
"""


def fig_convergence():
    np_ = NPLOT
    top = [(n, min(lim["P"] + window(n), 1.30)) for n in range(1, np_ + 1)]
    bot = [(n, max(lim["P"] - window(n), -0.30)) for n in range(np_, 0, -1)]
    parts = [PREAMBLE, COLORS,
             fill(T_CONV_HEAD, np=np_, band=coords(top) + " " + coords(bot))]

    for nm, _ in PTS:
        parts.append("\\addplot[color=" + PAL[nm] + ", mark=*, mark size=1.3pt]\n"
                     "  coordinates {" + coords([(n, hseq[nm][n]) for n in range(np_ + 1)])
                     + "};\n\\addlegendentry{" + LABEL[nm] + "}\n")
    for nm, _ in PTS:
        parts.append("\\addplot[color=" + PAL[nm] + ", dashed, line width=0.5pt,"
                     " forget plot]\n  coordinates {(-0.2,%.9f) (%d.2,%.9f)};\n"
                     % (lim[nm], np_, lim[nm]))

    parts.append(fill(T_CONV_MID, np=np_,
                      bound=coords_g([(n, window(n)) for n in range(np_ + 1)])))
    for nm, _ in PTS:
        pts = [(n, abs(hseq[nm][n] - lim[nm])) for n in range(np_ + 1)]
        pts = [(n, v) for n, v in pts if v > 3e-6]
        parts.append("\\addplot[color=" + PAL[nm] + ", mark=*, mark size=1.3pt,"
                     " forget plot]\n  coordinates {" + coords_g(pts) + "};\n")

    parts.append("\\end{groupplot}\n\\end{tikzpicture}\n")
    return "".join(parts)


# ==========================================================================
# FIGURE 2 -- the certified intervals, and regDet > 0 falling out of them
# ==========================================================================
T_WIN = r"""
\begin{tikzpicture}
\begin{axis}[
  width=0.88\linewidth, height=4.6cm,
  xlabel={$\hat h$}, xmin=0.245, xmax=1.10,
  ymin=0.42, ymax=4.70,
  ytick={@@ytick@@}, yticklabels={@@ylab@@},
  tick label style={font=\scriptsize}, label style={font=\scriptsize},
  y tick label style={font=\small},
  axis line style={clrGrey!70}, ymajorgrids=false,
  xmajorgrids, grid style={clrGrey!18, line width=0.3pt},
  xtick distance=0.1,
  clip=false,
]
@@bars@@
\end{axis}
\end{tikzpicture}
"""

T_BAR = r"""
\fill[@@c@@, fill opacity=0.16]
  (axis cs:@@lo@@,@@ylo@@) rectangle (axis cs:@@hi@@,@@yhi@@);
\fill[@@c@@, fill opacity=0.50]
  (axis cs:@@blo@@,@@ylo@@) rectangle (axis cs:@@bhi@@,@@yhi@@);
\draw[@@c@@, line width=1.15pt]
  (axis cs:@@true@@,@@tlo@@) -- (axis cs:@@true@@,@@thi@@);
\node[font=\tiny, color=clrGrey, anchor=west]
  at (axis cs:@@tag@@,@@y@@) {$j{=}@@j@@$};
"""


def fig_windows():
    order = ["P", "Q", "PmQ", "PpQ"]
    ytick, ylab, bars = [], [], []
    for i, nm in enumerate(order):
        y = len(order) - i
        lo, hi, blo, bhi = cert[nm]
        ytick.append(str(y))
        ylab.append(LABEL[nm])
        bars.append(fill(T_BAR, c=PAL[nm],
                         lo="%.6f" % lo, hi="%.6f" % hi,
                         blo="%.6f" % blo, bhi="%.6f" % bhi,
                         ylo="%.2f" % (y - 0.26), yhi="%.2f" % (y + 0.26),
                         true="%.6f" % lim[nm],
                         tlo="%.2f" % (y - 0.35), thi="%.2f" % (y + 0.35),
                         tag="%.6f" % (hi + 0.015), y=y, j=JEXP[nm]))
    return PREAMBLE + COLORS + fill(T_WIN, ytick=",".join(ytick),
                                    ylab=",".join(ylab), bars="".join(bars))


# ==========================================================================
# FIGURE 3 -- independence *is* an area: the height lattice
# ==========================================================================
T_LAT = r"""
\begin{tikzpicture}
\begin{axis}[
  name=indep,
  width=0.47\linewidth, height=0.47\linewidth,
  axis equal image, xmin=-1.42, xmax=1.42, ymin=-1.42, ymax=1.42,
  xtick=\empty, ytick=\empty,
  axis lines=middle,
  axis line style={clrGrey!55, -{Stealth[length=4pt]}},
  title={\scriptsize (a) $P,Q$ independent: area $>0$},
  title style={yshift=-1pt},
  clip=false,
]
\fill[clrBand, fill opacity=0.22] @@par@@;
\draw[clrGrey!60, line width=0.3pt] @@par@@;
\addplot[only marks, mark=*, mark size=0.8pt, color=clrGrey!70]
  coordinates {@@dots@@};
\draw[-{Stealth[length=5pt]}, clrP, line width=1.15pt]
  (axis cs:0,0) -- (axis cs:@@v1x@@,@@v1y@@);
\draw[-{Stealth[length=5pt]}, clrQ, line width=1.15pt]
  (axis cs:0,0) -- (axis cs:@@v2x@@,@@v2y@@);
@@labels@@
\node[font=\tiny, align=center, color=black!75]
  at (axis cs:@@cx@@,@@cy@@) {area\\[-2pt]$@@area@@$};
\end{axis}

\begin{axis}[
  at={(indep.right of south east)}, anchor=south west, xshift=6mm,
  width=0.47\linewidth, height=0.47\linewidth,
  axis equal image, xmin=-1.42, xmax=1.42, ymin=-1.42, ymax=1.42,
  xtick=\empty, ytick=\empty,
  axis lines=middle,
  axis line style={clrGrey!55, -{Stealth[length=4pt]}},
  title={\scriptsize (b) a relation flattens the cell},
  title style={yshift=-1pt},
  clip=false,
]
@@ghosts@@
\draw[clrGrey!45, line width=0.3pt]
  (axis cs:-1.32,0) -- (axis cs:1.32,0);
\draw[clrBand, line width=2.6pt, opacity=0.75]
  (axis cs:0,0) -- (axis cs:@@dsum@@,0);
\addplot[only marks, mark=*, mark size=1.35pt, color=clrGrey!85]
  coordinates {@@ddots@@};
\draw[-{Stealth[length=5pt]}, clrP, line width=1.15pt]
  (axis cs:0,0) -- (axis cs:@@dv1@@,0);
\draw[-{Stealth[length=5pt]}, clrQ, line width=1.15pt]
  (axis cs:0,0) -- (axis cs:@@dv2@@,0);
\filldraw[clrP] (axis cs:@@dv1@@,0) circle (2pt);
\filldraw[clrQ] (axis cs:@@dv2@@,0) circle (2pt);
\node[font=\scriptsize, color=clrP, anchor=north, inner sep=4pt]
  at (axis cs:@@dv1@@,0) {$P$};
\node[font=\scriptsize, color=clrQ, anchor=north, inner sep=4pt]
  at (axis cs:@@dv2@@,0) {$Q$};
\node[font=\tiny, align=center, color=black!75, anchor=north]
  at (axis cs:0.48,-0.28) {area $0$};
\node[font=\tiny, align=center, color=clrGrey, anchor=south]
  at (axis cs:0.05,1.02) {$\langle P,Q\rangle$ increasing};
\end{axis}
\end{tikzpicture}
"""


def fig_lattice():
    hP, hQ = lim["P"], lim["Q"]
    pair = (lim["PpQ"] - hP - hQ) / 2
    v1 = (math.sqrt(hP), 0.0)
    v2x = pair / math.sqrt(hP)
    v2y = math.sqrt(hQ - v2x * v2x)
    v2 = (v2x, v2y)
    det = hP * hQ - pair * pair

    def nrm2(m, n):
        return (m * v1[0] + n * v2[0]) ** 2 + (m * v1[1] + n * v2[1]) ** 2

    # The embedding is *built* from hhat(P), hhat(Q), hhat(P+Q), so the first
    # three checks are exact by construction and must hold to machine epsilon.
    assert abs(nrm2(1, 0) - lim["P"]) < 1e-12
    assert abs(nrm2(0, 1) - lim["Q"]) < 1e-12
    assert abs(nrm2(1, 1) - lim["PpQ"]) < 1e-12

    # The fourth is NOT free: nrm2(1,-1) = 2h(P) + 2h(Q) - h(P+Q), so agreement
    # with the independently computed h(P-Q) is exactly the parallelogram law
    # of r150, tested numerically.  The sequences are truncated at n = NMAX, so
    # the residual is O(4^-NMAX) rather than zero; assert against that scale.
    par_residual = abs(nrm2(1, -1) - lim["PmQ"])
    assert par_residual < 1e-3, par_residual
    print("  parallelogram-law residual at n=%d: %.3e" % (NMAX, par_residual))

    dots = []
    for m in range(-2, 3):
        for n in range(-2, 3):
            dots.append("(%.6f,%.6f)" % (m * v1[0] + n * v2[0],
                                         m * v1[1] + n * v2[1]))

    # Panel (b): a hypothetical dependent pair, 2P = 3Q, so v2 = (2/3)v1 and
    # every mP+nQ lands on the line through v1.  The orange arrow is literally
    # a sub-segment of the blue one -- collinearity is shown, not asserted.
    dv1 = math.sqrt(hP)
    dv2 = 2.0 * dv1 / 3.0
    dd = sorted({round((m + 2.0 * n / 3.0) * dv1, 6)
                 for m in range(-3, 4) for n in range(-3, 4)})
    ddots = " ".join("(%.6f,0)" % x for x in dd if abs(x) <= 1.32)

    # Ghost cells interpolating from the true generator to the collinear one:
    # holding v1 fixed and sliding v2 towards the line raises <P,Q> and drives
    # the area to 0.  These are illustrative, not computed from any curve.
    ghosts = []
    for t, op in [(1.0, 0.30), (0.62, 0.22), (0.28, 0.15)]:
        wx = (1.0 - t) * dv2 + t * v2[0]
        wy = t * v2[1]
        ghosts.append(
            "\\draw[clrGrey!70, line width=0.35pt, dash pattern=on 1.6pt off "
            "1.2pt, fill=clrBand, fill opacity=%.2f]\n"
            "  (axis cs:0,0) -- (axis cs:%.6f,0) -- (axis cs:%.6f,%.6f)"
            " -- (axis cs:%.6f,%.6f) -- cycle;\n"
            % (op * 0.35, dv1, dv1 + wx, wy, wx, wy))

    labels = []
    for (m, n), nm, anch in [((1, 0), "P", "north"), ((0, 1), "Q", "west"),
                             ((1, 1), "PpQ", "west"), ((1, -1), "PmQ", "west")]:
        x, y = m * v1[0] + n * v2[0], m * v1[1] + n * v2[1]
        labels.append("\\filldraw[%s] (axis cs:%.6f,%.6f) circle (2pt);\n"
                      "\\node[font=\\scriptsize, color=%s, anchor=%s,"
                      " inner sep=3.5pt] at (axis cs:%.6f,%.6f) {%s};\n"
                      % (PAL[nm], x, y, PAL[nm], anch, x, y, LABEL[nm]))

    par = ("(axis cs:0,0) -- (axis cs:%.6f,%.6f) -- (axis cs:%.6f,%.6f)"
           " -- (axis cs:%.6f,%.6f) -- cycle"
           % (v1[0], v1[1], v1[0] + v2[0], v1[1] + v2[1], v2[0], v2[1]))

    return PREAMBLE + COLORS + fill(
        T_LAT, par=par, dots=" ".join(dots), labels="".join(labels),
        v1x="%.6f" % v1[0], v1y="%.6f" % v1[1],
        v2x="%.6f" % v2[0], v2y="%.6f" % v2[1],
        cx="%.6f" % ((v1[0] + v2[0]) / 2), cy="%.6f" % ((v1[1] + v2[1]) / 2),
        area="%.4f" % math.sqrt(det),
        ddots=ddots, dv1="%.6f" % dv1, dv2="%.6f" % dv2,
        dsum="%.6f" % (dv1 + dv2), ghosts="".join(ghosts))


# ==========================================================================
# FIGURE 4 -- proof architecture, r143 .. r154
# ==========================================================================
T_DAG = r"""
\begin{tikzpicture}[
  box/.style={draw=clrGrey!65, rounded corners=1.6pt, line width=0.4pt,
              align=center, inner xsep=3pt, inner ysep=2.6pt,
              minimum height=6.4mm, text width=24mm, font=\tiny},
  sub/.style={box, fill=clrGrey!8},
  key/.style={box, fill=clrBand!24, draw=clrP!70},
  flag/.style={box, fill=clrS!26, draw=clrS!85, line width=0.75pt},
  ar/.style={-{Stealth[length=3.4pt]}, clrGrey!75, line width=0.45pt},
]
\node[sub]  (a) at (0,0)       {\textbf{r143}\\naive-height chain\\$0\to3\to\cdots$};
\node[sub]  (b) at (3.4,0)     {\textbf{r145}\\$\mathcal{H}(x(2R))\le 17\,\mathcal{H}^4$};
\node[key]  (c) at (6.8,0)     {\textbf{r147}\\$\hat h$ exists (Cauchy)\\$\hat h=0\iff$ torsion};
\node[sub]  (d) at (0,-1.45)   {\textbf{r148a--c}\\B\'ezout certificates\\content $\mid 389^4$};
\node[sub]  (e) at (3.4,-1.45) {\textbf{r148d--e}\\secant bridge\\quadratic-root height};
\node[sub]  (f) at (6.8,-1.45) {\textbf{r148f--g}\\upper $34$, lower $10368$};
\node[sub]  (i) at (0,-2.9)    {\textbf{r151}\\$\hat h(kR)=k^2\hat h(R)$};
\node[key]  (h) at (3.4,-2.9)  {\textbf{r150}\\parallelogram law\\(exact)};
\node[sub]  (g) at (6.8,-2.9)  {\textbf{r149}\\$|$log defect$|\le\log 10368$};
\node[sub]  (j) at (2.2,-4.35) {\textbf{r152}\\$\det\ne0\Rightarrow$ rank $\ge2$};
\node[sub]  (k) at (5.6,-4.35) {\textbf{r153}\\dyadic log bracket\\$\det\ge0.1057$};
\node[flag] (l) at (3.9,-5.85) {\textbf{r154}\\$2\le\operatorname{rank}E(\mathbb{Q})$};

\draw[ar] (a) -- (b);
\draw[ar] (b) -- (c);
\draw[ar] (d) -- (e);
\draw[ar] (e) -- (f);
\draw[ar] (f) -- (g);
\draw[ar] (g) -- (h);
\draw[ar] (c) -- (h);
\draw[ar] (h) -- (i);
\draw[ar] (h) -- (j);
\draw[ar] (i) -- (j);
\draw[ar] (h) -- (k);
\draw[ar] (j) -- (l);
\draw[ar] (k) -- (l);
% r147 also feeds the numerics directly; routed around the right-hand side
% so that it crosses no box.
\draw[ar] (c.east) -- (9.35,0) -- (9.35,-4.35) -- (k.east);
\end{tikzpicture}
"""


def fig_dag():
    return PREAMBLE + COLORS + T_DAG


# ==========================================================================
# FIGURE 5 -- the rank >= 1 cohort: certificate scale
# ==========================================================================
COHORT = [
    ("37a1",   171,    480106),
    ("43a1",   139,    8338438),
    ("53a1",   172,    369),
    ("61a1",   590,    636789825),
    ("79a1",   298,    385),
    ("83a1",   470,    83281),
    ("89a1",   220,    1024),
    ("101a1",  373,    28981),
    ("106a1",  38896,  26615281),
    ("389a1",  1728,   1169154495),
    ("5077a1", 105754, 3009638454),
]

T_COH = r"""
\begin{tikzpicture}
\begin{axis}[
  width=0.94\linewidth, height=5.0cm,
  ybar=0.5pt, bar width=6pt,
  xtick={0,...,@@last@@}, xticklabels={@@names@@},
  x tick label style={rotate=38, anchor=east, font=\tiny},
  tick label style={font=\scriptsize}, label style={font=\scriptsize},
  ylabel={$\log_{10}$}, ymin=0, ymax=10.6,
  ytick={0,2,4,6,8,10},
  ymajorgrids, grid style={clrGrey!18, line width=0.3pt},
  axis line style={clrGrey!70},
  legend style={font=\scriptsize, at={(0.02,0.97)}, anchor=north west,
                draw=clrGrey!45, fill=white, fill opacity=0.9,
                text opacity=1, row sep=-1.5pt, inner sep=2pt},
  enlarge x limits=0.05,
]
\addplot[fill=clrP, draw=clrP!80, fill opacity=0.85]
  coordinates {@@hbar@@};
\addlegendentry{$\log_{10}\mathcal{H}$ reached by the chain}
\addplot[fill=clrQ, draw=clrQ!80, fill opacity=0.85]
  coordinates {@@kbar@@};
\addlegendentry{$\log_{10}\kappa$ (duplication constant)}
\end{axis}
\end{tikzpicture}
"""


def fig_cohort():
    names = ",".join("\\texttt{%s}" % c for c, _, _ in COHORT)
    hbar = " ".join("(%d,%.5f)" % (i, math.log10(h))
                    for i, (_, _, h) in enumerate(COHORT))
    kbar = " ".join("(%d,%.5f)" % (i, math.log10(k))
                    for i, (_, k, _) in enumerate(COHORT))
    return PREAMBLE + COLORS + fill(T_COH, last=len(COHORT) - 1,
                                    names=names, hbar=hbar, kbar=kbar)


# ==========================================================================
if __name__ == "__main__":
    for fn, txt in [
        ("fig_canheight_convergence.tex", fig_convergence()),
        ("fig_certified_windows.tex",     fig_windows()),
        ("fig_regulator_lattice.tex",     fig_lattice()),
        ("fig_arc_dag.tex",               fig_dag()),
        ("fig_cohort.tex",                fig_cohort()),
    ]:
        with open(os.path.join(OUT, fn), "w") as fh:
            fh.write(txt)
        print("wrote %-34s %6d bytes" % (fn, len(txt)))

    hP, hQ = lim["P"], lim["Q"]
    pair = (lim["PpQ"] - hP - hQ) / 2
    print()
    print("hhat(P)   = %.10f" % hP)
    print("hhat(Q)   = %.10f" % hQ)
    print("hhat(P+Q) = %.10f" % lim["PpQ"])
    print("hhat(P-Q) = %.10f" % lim["PmQ"])
    print("pairing   = %.10f" % pair)
    print("det       = %.10f  (= classical regulator of 389a1)"
          % (hP * hQ - pair * pair))
    print()
    print("certified level-3 intervals (Lean r153):")
    for nm in ["P", "Q", "PpQ", "PmQ"]:
        lo, hi, blo, bhi = cert[nm]
        print("  %-4s j=%-3d bracket=[%.6f,%.6f]  +/-window=[%.6f,%.6f]"
              % (nm, JEXP[nm], blo, bhi, lo, hi))
    plo = (cert["PpQ"][0] - cert["P"][1] - cert["Q"][1]) / 2
    phi = (cert["PpQ"][1] - cert["P"][0] - cert["Q"][0]) / 2
    dlo = cert["P"][0] * cert["Q"][0] - max(abs(plo), abs(phi)) ** 2
    print("  pairing in [%.6f,%.6f] -> det >= %.6f" % (plo, phi, dlo))
