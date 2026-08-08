#!/usr/bin/env python3
"""
RH front, T1: the two-line split, at the level of NULL VECTORS.

Both families of Z_Selberg zeros live in the SAME factor det(1 - L_s):
    even Maass cusp form   s = 1/2 + i*13.77975135189074   (L2 eigenvalue)
    first Riemann zero     s = 1/4 + i* 7.06736276055...   (rho_1/2, scattering)
M1 (2026-08-02) located both to ~2e-7 through |det|.  T1 asks the next
question: what do the corresponding NULL VECTORS look like, and does their
structure distinguish the self-adjointly-pinned family from the unpinned one?

Method
------
Matrix elements: the exact Hurwitz-zeta continuation of rh_mayer_full.py,
disc-normalized basis e_n(x) = ((x-1)/R)^n, R = 3/2, on D(1, 3/2).
    A[m,n](s) = sum_i C(n,i)(-1)^(i+m) Poch(2s+n-i,m)/m! zeta_H(2s+n-i+m,2) R^(m-n)
Null vector: inverse iteration on (A - I).  Returns the eigenvalue of A
nearest 1 together with its eigenvector; |lambda - 1| is the quality gate.

Period function: psi(x) = sum_n c_n ((x-1)/R)^n.

Three-term equation.  L_s psi = psi means, term by term,
    psi(x) = psi(x+1) + (x+1)^(-2s) psi(1/(x+1)),
verified on a grid in (0,1) where all three arguments sit inside D(1,3/2).
(This is the operator's own form; the Lewis x/(x+1) form is the other
normalization.)

Asymptotics.  Telescoping that same identity to the right,
    psi(x0 + n) = psi(x0) - sum_{j=1..n} (x0+j)^(-2s) psi(1/(x0+j)),
and every 1/(x0+j) lies in (0,1) c D(1,3/2), so the continuation to large
argument needs nothing beyond the disc.  Expanding psi(1/(x0+j)) about 0,
the leading term is psi(0) * sum_j (x0+j)^(-2s), whose partial sums grow
like X^(1-2s)/(1-2s).  So:
    Re s = 1/2  ->  |X^(1-2s)| = X^0     bounded/oscillating
    Re s = 1/4  ->  |X^(1-2s)| = X^(1/2) growing
UNLESS psi(0) = 0.  Lewis-Zagier: Maass cusp forms have psi(x) = O(1/x).
Predicted split of the fitted exponent a in |psi(X)| ~ X^a:
    a ~ -1   at the Maass point   (decaying: the L2 condition)
    a ~ +1/2 at the Riemann point (growing: no L2 condition to impose)
This script measures a; it does not assume it.

Controls: a non-zero point on Re s = 1/4 (t = 6.60), where |lambda - 1|
must be O(1), i.e. no null vector exists to compare.
"""
import mpmath as mp
from math import comb
import sys

mp.mp.dps = 50
R = mp.mpf(3) / 2
N = 72

OUT = open(sys.argv[1] if len(sys.argv) > 1 else "rh_t1_results.txt", "w")
def log(s):
    print(s, flush=True); OUT.write(s + "\n"); OUT.flush()


# --- matrix: exact Hurwitz-zeta continuation (rh_mayer_full.py v6) ----------
def matrix(s, N):
    z = [mp.zeta(2 * s + q, 2) for q in range(2 * N + 1)]
    A = mp.zeros(N, N)
    for n in range(N):
        Rf = [R ** (m - n) for m in range(N)]
        for i in range(n + 1):
            c0 = comb(n, i) * (-1) ** i
            sig = 2 * s + n - i
            poch = mp.mpc(1)
            for m in range(N):
                if m > 0:
                    poch *= (sig + m - 1) / m
                A[m, n] += c0 * (-1) ** m * poch * z[n - i + m] * Rf[m]
    return A


def null_vector(A, N, iters=40):
    """Inverse iteration on (A - I): eigenpair of A with eigenvalue nearest 1."""
    M = A - mp.eye(N)
    v = mp.matrix([mp.mpf(1) / (k + 1) for k in range(N)])
    lam = None
    for _ in range(iters):
        w = mp.lu_solve(M, v)
        nrm = mp.sqrt(sum(abs(w[k]) ** 2 for k in range(N)))
        v = w / nrm
        Av = A * v
        # Rayleigh quotient  <v, Av> / <v, v>   (v is unit)
        lam = sum(mp.conj(v[k]) * Av[k] for k in range(N))
    resid = A * v - lam * v
    rnorm = mp.sqrt(sum(abs(resid[k]) ** 2 for k in range(N)))
    return lam, v, rnorm


def psi_eval(c, x, N):
    """psi(x) = sum_n c_n ((x-1)/R)^n by Horner."""
    u = (x - 1) / R
    acc = mp.mpc(0)
    for n in range(N - 1, -1, -1):
        acc = acc * u + c[n]
    return acc


def report(label, s, N, nmax=2000):
    log("")
    log("=" * 72)
    log(f"{label}:  s = {mp.nstr(s, 18)}   [N = {N}]")
    log("=" * 72)

    A = matrix(s, N)
    lam, c, rnorm = null_vector(A, N)
    log(f"  eigenvalue of L_s nearest 1 : {mp.nstr(lam, 16)}")
    log(f"  |lambda - 1|                : {mp.nstr(abs(lam - 1), 8)}")
    log(f"  ||A v - lambda v||          : {mp.nstr(rnorm, 8)}")

    # (a) coefficient decay -------------------------------------------------
    log("")
    log("  (a) coefficient decay  |c_n|")
    for n in (0, 1, 2, 4, 8, 16, 24, 32, 48, 64, 71):
        log(f"        n={n:3d}   |c_n| = {mp.nstr(abs(c[n]), 8)}")
    tail = [abs(c[n]) for n in range(N - 12, N)]
    ratios = [tail[k + 1] / tail[k] for k in range(len(tail) - 1) if tail[k] != 0]
    if ratios:
        gm = mp.exp(sum(mp.log(r) for r in ratios) / len(ratios))
        log(f"        geometric ratio over last 12 coefficients: {mp.nstr(gm, 8)}")

    # (b) psi(0) ------------------------------------------------------------
    p0 = psi_eval(c, mp.mpf(0), N)
    p1 = psi_eval(c, mp.mpf(1), N)
    log("")
    log(f"  (b) psi(0) = {mp.nstr(p0, 12)}   |psi(0)| = {mp.nstr(abs(p0), 8)}")
    log(f"      psi(1) = {mp.nstr(p1, 12)}   |psi(1)| = {mp.nstr(abs(p1), 8)}")
    log(f"      |psi(0)|/|psi(1)| = {mp.nstr(abs(p0) / abs(p1), 8)}")

    # (c) three-term equation ----------------------------------------------
    log("")
    log("  (c) three-term equation  psi(x) = psi(x+1) + (x+1)^(-2s) psi(1/(x+1))")
    worst = mp.mpf(0)
    for k in range(1, 10):
        x = mp.mpf(k) / 10
        lhs = psi_eval(c, x, N)
        rhs = psi_eval(c, x + 1, N) + (x + 1) ** (-2 * s) * psi_eval(c, 1 / (x + 1), N)
        rel = abs(lhs - rhs) / abs(lhs)
        worst = max(worst, rel)
        if k in (1, 3, 5, 7, 9):
            log(f"        x={mp.nstr(x,3)}  rel residual = {mp.nstr(rel, 6)}")
    log(f"        WORST relative residual on the grid: {mp.nstr(worst, 6)}")

    # (d) growth of |psi(X)| by telescoping ---------------------------------
    log("")
    log("  (d) |psi(X)| for large X, by telescoping the three-term equation")
    x0 = mp.mpf(1) / 2
    acc = psi_eval(c, x0, N)
    marks = [10, 30, 100, 300, 1000, 2000]
    vals = {}
    for j in range(1, nmax + 1):
        acc -= (x0 + j) ** (-2 * s) * psi_eval(c, 1 / (x0 + j), N)
        if j in marks:
            vals[j] = acc
            log(f"        X = {mp.nstr(x0 + j, 8):>10}   "
                f"|psi(X)| = {mp.nstr(abs(acc), 10)}")

    # (e) fitted exponent ---------------------------------------------------
    log("")
    log("  (e) fitted exponent a in |psi(X)| ~ X^a")
    fits = {}
    for lo, hi in ((10, 100), (100, 1000), (300, 2000), (1000, 2000)):
        if lo in vals and hi in vals:
            a = (mp.log(abs(vals[hi])) - mp.log(abs(vals[lo]))) / \
                (mp.log(x0 + hi) - mp.log(x0 + lo))
            fits[(lo, hi)] = a
            log(f"        over X in [{lo},{hi}] :  a = {mp.nstr(a, 8)}")
    return {"lam": lam, "psi0": psi_eval(c, mp.mpf(0), N),
            "psi1": psi_eval(c, mp.mpf(1), N), "vals": vals, "fits": fits}


# ---------------------------------------------------------------------------
log("RH T1 -- null vectors of (1 - L_s) at the Maass point and the Riemann point")
log(f"dps = {mp.mp.dps}   R = 3/2   disc D(1, 3/2)")

s_maass = mp.mpc(mp.mpf(1) / 2, mp.mpf("13.77975135189074"))
s_riem = mp.mpc(mp.mpf(1) / 4, mp.mpf("7.0673627605540221"))
s_ctrl = mp.mpc(mp.mpf(1) / 4, mp.mpf("6.60"))

res = {}
for NN in (72, 88):
    res[("M", NN)] = report("MAASS point (even cusp form, Re s = 1/2)", s_maass, NN)
    res[("R", NN)] = report("RIEMANN point (rho_1 / 2, Re s = 1/4)", s_riem, NN)

# --- N-STABILITY GATE ------------------------------------------------------
# psi(0) came out ~1e-18 against coefficients of order 0.3 at the Maass point:
# 18 digits of cancellation.  A number that small is only meaningful if it is
# stable when the truncation size changes.  If it moves, it is truncation
# noise and every conclusion drawn from "psi(0) = 0" is void.
log("")
log("=" * 72)
log("N-STABILITY GATE: N = 72 vs N = 88")
log("=" * 72)
for tag, name in (("M", "Maass  "), ("R", "Riemann")):
    a, b = res[(tag, 72)], res[(tag, 88)]
    log(f"  {name}  |psi(0)|   N72 = {mp.nstr(abs(a['psi0']), 8)}   "
        f"N88 = {mp.nstr(abs(b['psi0']), 8)}")
    log(f"  {name}  |psi(1)|   N72 = {mp.nstr(abs(a['psi1']), 8)}   "
        f"N88 = {mp.nstr(abs(b['psi1']), 8)}")
    for k in a["fits"]:
        log(f"  {name}  exponent a on X in {str(k):>12} : "
            f"N72 = {mp.nstr(a['fits'][k], 8)}   N88 = {mp.nstr(b['fits'][k], 8)}")
    log("")

log("=" * 72)
log("CONTROL: Re s = 1/4, t = 6.60 -- no zero here, so no null vector")
log("=" * 72)
Ac = matrix(s_ctrl, 72)
lamc, vc, rc = null_vector(Ac, 72)
log(f"  eigenvalue of L_s nearest 1 : {mp.nstr(lamc, 16)}")
log(f"  |lambda - 1|                : {mp.nstr(abs(lamc - 1), 8)}")
log("  (must be O(1) -- if it is small, the comparison above is meaningless)")

OUT.close()
