#!/usr/bin/env python3
"""
RH front, M4: the Gamma_0(9) transfer operator TWISTED BY AN ORDER-3 CHARACTER
mod 9, and the question of whether L(s, chi_9) zeros appear in its determinant.

WHY LEVEL 9.  M2 (2026-08-03) closed the Gamma_0(3) route with a negative
result: chi_3 mod 3 is the quadratic character and is ODD, hence inadmissible
as a weight-0 nebentypus, so L(s,chi_3) cannot appear in Gamma_0(3) scattering.
That obstruction is level-3 only.  The order-3 characters mod 9 are EVEN
(-1 = 8 = 2^3 in (Z/9)*, chi(2)^3 = 1 => chi(-1) = 1), so they ARE weight-0
admissible, and chi is primitive mod 9 (an order-3 character cannot be induced
from mod 3, whose unit group has order 2).

CONSTRUCTION.
  Cosets Gamma_0(9)\\PSL(2,Z) <-> P^1(Z/9), 12 of them (index 12).
  Induced rep of the nebentypus chi:  rho(g)_{ij} = chi(R_i g R_j^{-1}) if that
  lies in Gamma_0(9), else 0.  Monomial, 12-dimensional; chi(gamma) := chi(d).
  It descends to PSL(2,Z) exactly because chi is even -- rho(S)^2 = rho(-I) =
  chi(-1) I.  Trivial chi gives back the 12-dim permutation representation.

  Transfer operator (Mayer / Chang-Mayer, Fraczek-Mayer):
      (L_s f)(x) = sum_{k>=1} (x+k)^{-2s} rho(S T^k) f(1/(x+k)).
  rho(T) has order 9 in ALL THREE characters (measured, Phase 0), so the k-sum
  splits by k mod 9 into nine scalar blocks A_r tensored with rho(S T^r):
      A_r[m,n](s) = sum_i C(n,i)(-1)^(i+m) Poch(sig,m)/m! 9^{-(sig+m)}
                      * zeta_H(sig+m, (r+1)/9) * R^(m-n),   sig = 2s+n-i,
  in the disc-normalized basis e_n(x) = ((x-1)/R)^n, R = 3/2 (M1's basis).

  M2 LESSON, CARRIED: the UNTWISTED det(1-L)det(1+L) is NOT the Selberg zeta
  for Gamma_0(N).  Fraczek-Mayer Thm 2.1.1's symmetry operator P (from
  j = diag(1,-1), which normalizes Gamma_0(9) and fixes the nebentypus since
  it leaves d alone) must be inserted:
      Z_Selberg(s, chi) = det(1 - P L_s) det(1 + P L_s),
      even <-> det(1 - P L),   odd <-> det(1 + P L).
  P is built as P_{i,pi(i)} = chi(h_i) with j R_i j^{-1} = h_i R_{pi(i)}, and
  the intertwining relations P rho(S) = rho(S) P, P rho(T) = rho(T^{-1}) P,
  P^2 = 1 are ASSERTED, not assumed.

WHAT IS BEING TESTED (Phase 2).  For chi primitive mod q the Eisenstein
scattering determinant for (Gamma_0(q), chi) carries L(2s, chi) in its
DENOMINATOR, exactly as zeta(2s) does at level 1.  Level 1 + M1: det(1 - L_s)
vanishes at s = rho/2 on Re s = 1/4 where zeta(2s) = 0 (Lewis-Zagier).  The
level-9 analogue would put zeros of det(1 -+ P L_s^chi) at s = rho/2 on
Re s = 1/4 for rho a zero of L(s, chi_9).  This is an instrument question
about the SCATTERING (Eisenstein) side.  It says nothing about RH and nothing
about Hilbert-Polya, where the failure is on the Eisenstein side to begin with.

GATES (run before any conclusion; every figure printed, not just PASS/FAIL):
  V1  12 distinct cosets; S/T act as permutations of them; rho a homomorphism;
      rho(S)^2 = 1, rho(ST)^3 = 1 (the second needs chi(-1) = +1);
      rho|_{Gamma_0(9)} = chi; trivial chi reproduces the permutation rep.
  V2  P^2 = 1, P rho(S) = rho(S) P, P rho(T) = rho(T^{-1}) P.
  V3  sum_{r=1..9} A_r = the M1 level-1 matrix, entrywise.
  V4  numpy float64 determinant vs mpmath determinant at production N -- the
      fast path is only used after it is measured against the slow one.
  V5  truncation: relative and scale-normalized determinant drift, N vs N+8,
      at the worst point of each scan, plus a dps re-measurement to separate
      roundoff from truncation.
  P1  THE GATE: the trivial-character Gamma_0(9) determinant must contain the
      M2-certified Gamma_0(3) spectrum as OLDFORMS, in the right parity factor.
      Needs no external data (LMFDB has NO level-9 Maass forms at all -- it was
      queried).  If it fails, nothing downstream means anything.
  V6  det(1 - P L_s^{chi^2}) = conj(det(1 - P L_{sbar}^{chi})), so chi^2 needs
      no separate scan.

RESULT (see codex/rh_gamma09_results.txt for every measured figure):
  Phase 1 PASSES -- all ten certified parameters are zeros of the
  parity-correct factor, to ~4e-12 in t, with exactly the predicted oldform
  multiplicities (2 for a level-3 newform, 3 for the level-1 form).
  ONE DOCUMENTED ANOMALY: the 8-dim level-9-new block additionally produces an
  exact -lambda partner for each correct +lambda, so there is one spurious
  opposite-parity zero at every parameter.  Absent at level 3.  Not explained;
  leading untested hypothesis is that j = diag(1,-1) is not the full symmetry
  operator for Gamma_0(p^2), whose normalizer is strictly larger than
  Gamma_0(p)'s.
  Phase 2 POSITIVE -- 29/29 verified zeros of L(s,chi_9) appear in
  det(1 - P L_s^{chi}) at s = rho/2 on Re s = 1/4 (ratio 3.0e-14 .. 1.6e-10
  against local controls); 0/29 in the odd factor; 0/29 anywhere in the
  trivial-character operator at the same points.

Usage:  rh_gamma09.py [--gates] [--detgate] [--trunc]
                      [--phase1] [--phase1b] [--phase1c] [--phase2]
        --phase1b is THE gate (direct evaluation); --phase1 is the scan, whose
        minimum-refiner is fragile and is kept only for the record.
Output: codex/rh_gamma09_results.txt   (APPENDED -- concurrent runs interleave;
        the committed copy of that file was recomposed in logical order).
"""
import os
import sys
import time
from math import comb, gcd

import mpmath as mp
import numpy as np

DPS = 40
mp.mp.dps = DPS
R = mp.mpf(3)/2
NLEV = 9
MOD = 9                      # order of rho(T); asserted in V1
NPROD = 56                   # production section size; gated in V5
HERE = os.path.dirname(os.path.abspath(__file__))
OUTPATH = os.path.join(HERE, "rh_gamma09_results.txt")
TARGETS = os.path.join(HERE, "rh_gamma09_targets.txt")

_OUT = None
def log(msg=""):
    global _OUT
    if _OUT is None:
        _OUT = open(OUTPATH, "a")
    print(msg, flush=True)
    _OUT.write(msg + "\n")
    _OUT.flush()

# ============================ Phase 0: the representation ====================
UNITS = [u for u in range(1, NLEV) if gcd(u, NLEV) == 1]

def canon(c, d):
    c %= NLEV; d %= NLEV
    assert gcd(gcd(c, d), NLEV) == 1, (c, d)
    return min(((u*c) % NLEV, (u*d) % NLEV) for u in UNITS)

PTS = sorted({canon(c, d) for c in range(NLEV) for d in range(NLEV)
              if gcd(gcd(c, d), NLEV) == 1})
IDX = {p: i for i, p in enumerate(PTS)}
DIM = len(PTS)

def mul(g, h):
    a, b, c, d = g; e, f, gg, hh = h
    return (a*e + b*gg, a*f + b*hh, c*e + d*gg, c*f + d*hh)

def inv(g):
    a, b, c, d = g
    return (d, -b, -c, a)

S = (0, -1, 1, 0)
T = (1, 1, 0, 1)

def egcd(a, b):
    if b == 0: return (a, 1, 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a//b)*y)

def lift_rep(c0, d0):
    """SL(2,Z) matrix whose bottom row reduces to (c0,d0) mod 9."""
    c, d, k = c0, d0, 0
    while gcd(c, d) != 1:
        k += 1
        d = d0 + NLEV*k
        if k > 400: raise RuntimeError("no coprime lift")
    _, x, y = egcd(d, c)              # d*x + c*y = 1
    a, b = x, -y
    assert a*d - b*c == 1
    return (a, b, c, d)

REPS = [lift_rep(c, d) for (c, d) in PTS]

def coset(g):
    return IDX[canon(g[2], g[3])]

def make_chi(power):
    """Order-3 character mod 9 with chi(2) = exp(2 pi i power/3).
    power = 0 is the trivial character; 1 and 2 are the two order-3 ones."""
    w = mp.exp(2j*mp.pi*power/3)
    tab, v = {}, 1
    for k in range(6):
        tab[v] = w**k
        v = (v*2) % NLEV
    return lambda x: tab[x % NLEV]

def induced(g, chi):
    """rho(g)_{ij} = chi(R_i g R_j^{-1}) when R_i g R_j^{-1} is in Gamma_0(9)."""
    M = mp.zeros(DIM, DIM)
    for i in range(DIM):
        h = mul(REPS[i], g)
        j = coset(h)
        hh = mul(h, inv(REPS[j]))
        assert hh[2] % NLEV == 0, "coset bookkeeping broken"
        M[i, j] = chi(hh[3])
    return M

def sigma(g):
    """j g j^{-1} with j = diag(1,-1); an automorphism preserving Gamma_0(9)
    and the nebentypus (it leaves the lower-right entry alone)."""
    a, b, c, d = g
    return (a, -b, -c, d)

def twist_P(chi):
    P = mp.zeros(DIM, DIM)
    for i in range(DIM):
        si = sigma(REPS[i])
        j = coset(si)
        hh = mul(si, inv(REPS[j]))
        assert hh[2] % NLEV == 0
        P[i, j] = chi(hh[3])
    return P

def mat_order(Mx, cap=200):
    A = mp.eye(DIM)
    for k in range(1, cap + 1):
        A = A*Mx
        if mp.mnorm(A - mp.eye(DIM)) < mp.mpf('1e-30'):
            return k
    return None

def to_np(Mx):
    return np.array([[complex(Mx[a, b]) for b in range(Mx.cols)]
                     for a in range(Mx.rows)], dtype=complex)

# ============================ matrix elements ================================
_ACACHE = {}
def block_A(s, N, r, M=MOD):
    """k-sum restricted to k = M*j + r, j >= 0 (r = 1..M).  Returns numpy.

    The blocks depend only on (s, N, r) -- NOT on the character -- so they are
    cached and shared between the chi-twisted and trivial-character operators,
    which halves the cost of running both over the same target list."""
    ckey = (mp.nstr(s, 30), N, r, M)      # NB: 'key' is taken by the inner loop
    if ckey in _ACACHE:
        return _ACACHE[ckey]
    z = {}
    A = [[mp.mpc(0)]*N for _ in range(N)]
    a_arg = mp.mpf(r + 1)/M
    for n in range(N):
        Rf = [R**(m - n) for m in range(N)]
        for i in range(n + 1):
            c0 = comb(n, i)*(-1)**i
            sig = 2*s + n - i
            poch = mp.mpc(1)
            for m in range(N):
                if m > 0: poch *= (sig + m - 1)/m
                key = n - i + m
                if key not in z:
                    z[key] = M**(-(2*s + key))*mp.zeta(2*s + key, a_arg)
                A[m][n] += c0*(-1)**m*poch*z[key]*Rf[m]
    out = np.array([[complex(x) for x in row] for row in A], dtype=complex)
    if len(_ACACHE) < 4000:
        _ACACHE[ckey] = out
    return out

def block_A_mp(s, N, r, M=MOD):
    z = {}
    A = mp.zeros(N, N)
    a_arg = mp.mpf(r + 1)/M
    for n in range(N):
        Rf = [R**(m - n) for m in range(N)]
        for i in range(n + 1):
            c0 = comb(n, i)*(-1)**i
            sig = 2*s + n - i
            poch = mp.mpc(1)
            for m in range(N):
                if m > 0: poch *= (sig + m - 1)/m
                key = n - i + m
                if key not in z:
                    z[key] = M**(-(2*s + key))*mp.zeta(2*s + key, a_arg)
                A[m, n] += c0*(-1)**m*poch*z[key]*Rf[m]
    return A

def level1_A_mp(s, N):
    """M1's level-1 Mayer matrix, for the V3 consistency check."""
    z = [mp.zeta(2*s + q, 2) for q in range(2*N + 1)]
    A = mp.zeros(N, N)
    for n in range(N):
        Rf = [R**(m - n) for m in range(N)]
        for i in range(n + 1):
            c0 = comb(n, i)*(-1)**i
            sig = 2*s + n - i
            poch = mp.mpc(1)
            for m in range(N):
                if m > 0: poch *= (sig + m - 1)/m
                A[m, n] += c0*(-1)**m*poch*z[n - i + m]*Rf[m]
    return A

# ============================ the operator ===================================
class Rep:
    def __init__(self, power):
        self.power = power
        self.chi = make_chi(power)
        self.rS = induced(S, self.chi)
        self.rT = induced(T, self.chi)
        self.P = twist_P(self.chi)
        self.reps = [induced(mul(S, (1, r, 0, 1)), self.chi)
                     for r in range(1, MOD + 1)]
        self.reps_np = [to_np(m) for m in self.reps]
        self.P_np = to_np(self.P)

def PL_matrix(s, N, rep):
    """(P (x) I_N) . L_s  as a numpy complex array of size 12N."""
    D = DIM*N
    L = np.zeros((D, D), dtype=complex)
    for r in range(MOD):
        A = block_A(s, N, r + 1)
        rr = rep.reps_np[r]
        for a in range(DIM):
            for b in range(DIM):
                c = rr[a, b]
                if c == 0: continue
                L[a*N:(a+1)*N, b*N:(b+1)*N] += c*A
    PL = np.zeros((D, D), dtype=complex)
    for a in range(DIM):
        for b in range(DIM):
            c = rep.P_np[a, b]
            if c == 0: continue
            PL[a*N:(a+1)*N, :] += c*L[b*N:(b+1)*N, :]
    return PL

def dets(s, N, rep):
    """(det(1 - P L_s), det(1 + P L_s)) via the gated float64 path."""
    M = PL_matrix(s, N, rep)
    I = np.eye(M.shape[0])
    return np.linalg.det(I - M), np.linalg.det(I + M)

def PL_matrix_mp(s, N, rep):
    D = DIM*N
    L = [[mp.mpc(0)]*D for _ in range(D)]
    for r in range(MOD):
        A = block_A_mp(s, N, r + 1)
        rr = rep.reps[r]
        for a in range(DIM):
            for b in range(DIM):
                c = rr[a, b]
                if c == 0: continue
                for m in range(N):
                    row = L[a*N + m]
                    for n in range(N):
                        row[b*N + n] += c*A[m, n]
    PL = mp.zeros(D, D)
    for a in range(DIM):
        for b in range(DIM):
            c = rep.P[a, b]
            if c == 0: continue
            for m in range(N):
                src = L[b*N + m]
                for n in range(D):
                    PL[a*N + m, n] += c*src[n]
    return PL

def dets_mp(s, N, rep):
    M = PL_matrix_mp(s, N, rep)
    I = mp.eye(M.rows)
    return mp.det(I - M), mp.det(I + M)

# ============================ V1 / V2 gates ==================================
def gates_representation():
    log("=" * 74)
    log("PHASE 0 -- representation and its self-checks")
    log("=" * 74)
    log(f"P^1(Z/9) coset labels ({len(PTS)}): {PTS}")
    assert len(PTS) == 12 and len(set(PTS)) == 12
    log(f"V1a  exactly 12 cosets, no duplicates: PASS   index [PSL(2,Z):Gamma_0(9)] = 12")
    # S, T act as permutations of the coset set
    for nm, g in (("S", S), ("T", T)):
        img = [coset(mul(REPS[i], g)) for i in range(DIM)]
        assert sorted(img) == list(range(DIM)), f"{nm} is not a permutation"
    log("V1b  S and T act as permutations of the 12 cosets: PASS")

    for nm, pw in (("trivial", 0), ("chi", 1), ("chi^2", 2)):
        chi = make_chi(pw)
        rS, rT = induced(S, chi), induced(T, chi)
        rST = induced(mul(S, T), chi)
        e_hom = mp.mnorm(rS*rT - rST)
        e_S2 = mp.mnorm(rS*rS - mp.eye(DIM))
        e_ST3 = mp.mnorm(rST**3 - mp.eye(DIM))
        ordT = mat_order(rT)
        chim1 = chi(NLEV - 1)
        P = twist_P(chi)
        rTi = induced(inv(T), chi)
        e_P2 = mp.mnorm(P*P - mp.eye(DIM))
        e_PS = mp.mnorm(P*rS - rS*P)
        e_PT = mp.mnorm(P*rT - rTi*P)
        log(f"  [{nm}]  chi(-1) = {mp.nstr(chim1, 10)}   (must be +1: weight-0 admissible)")
        log(f"         rho(S)rho(T) - rho(ST) : {mp.nstr(e_hom, 3)}")
        log(f"         rho(S)^2 - 1           : {mp.nstr(e_S2, 3)}")
        log(f"         rho(ST)^3 - 1          : {mp.nstr(e_ST3, 3)}")
        log(f"         order of rho(T)        : {ordT}")
        log(f"         P^2 - 1                : {mp.nstr(e_P2, 3)}")
        log(f"         P rho(S) - rho(S) P    : {mp.nstr(e_PS, 3)}")
        log(f"         P rho(T) - rho(T^-1) P : {mp.nstr(e_PT, 3)}")
        tol = mp.mpf('1e-30')
        assert abs(chim1 - 1) < tol, f"{nm}: chi is ODD -- inadmissible at weight 0"
        for e in (e_hom, e_S2, e_ST3, e_P2, e_PS, e_PT):
            assert e < tol, f"{nm}: representation/twist relation FAILED"
        assert ordT == MOD, f"{nm}: order of rho(T) is {ordT}, not {MOD}"
        # rho restricted to Gamma_0(9) is chi (row of the identity coset)
        for gam in ((1, 0, 9, 1), (1, 1, 9, 10), (4, 1, 27, 7), (5, 3, 18, 11)):
            assert gam[0]*gam[3] - gam[1]*gam[2] == 1
            rg = induced(gam, chi)
            assert abs(rg[0, 0] - chi(gam[3])) < tol
            assert max(abs(rg[0, j]) for j in range(1, DIM)) < tol
        log(f"         rho|_Gamma_0(9) = chi(d) on 4 test elements: PASS")
        if pw == 0:
            ok = all(rS[a, b] in (0, 1) and rT[a, b] in (0, 1)
                     for a in range(DIM) for b in range(DIM))
            assert ok, "trivial character does not give a 0/1 permutation rep"
            log("         trivial chi reproduces the 12-dim PERMUTATION rep: PASS")
    log("V1/V2  ALL REPRESENTATION AND TWIST CHECKS PASS")
    log("")

def gate_blocks():
    log("V3  sum_{r=1..9} A_r  vs  the M1 level-1 Mayer matrix")
    for st, Nt in ((mp.mpc('0.5', '5.3'), 24), (mp.mpc('0.25', '7.07'), 24)):
        Asum = block_A_mp(st, Nt, 1)
        for r in range(2, MOD + 1):
            Asum += block_A_mp(st, Nt, r)
        A1 = level1_A_mp(st, Nt)
        err = max(abs(Asum[i, j] - A1[i, j]) for i in range(Nt) for j in range(Nt))
        sc = max(abs(A1[i, j]) for i in range(Nt) for j in range(Nt))
        log(f"     s={st}  N={Nt}  max abs err {mp.nstr(err,3)}   matrix scale {mp.nstr(sc,3)}"
            f"   relative {mp.nstr(err/sc,3)}")
        assert err/sc < mp.mpf('1e-30'), "V3 FAILED"
    log("V3  PASS")
    log("")

def gate_det_path(rep, spts):
    """V4: float64 determinant vs mpmath determinant.

    M1's ledger records a gate that tested the wrong quantity; this is the same
    trap.  A RELATIVE comparison is meaningless at a point where the determinant
    is nearly zero -- that is exactly where we want to work.  The figure that
    decides whether the float64 path is usable is the ABSOLUTE discrepancy
    measured against (a) the local determinant scale and (b) the truncation
    error, which is the dominant systematic everywhere in this study.
    """
    log(f"V4  float64 det vs mpmath det (dps={DPS})")
    worst = mp.mpf(0)
    for st, N in spts:
        t0 = time.time(); dn = dets(st, N, rep); tn = time.time() - t0
        t0 = time.time(); dm = dets_mp(st, N, rep); tm = time.time() - t0
        d8 = dets(st, N + 8, rep)          # truncation reference, float64
        scale = max(abs(dm[0]), abs(dm[1]))
        log(f"     s={st}, N={N}, D={DIM*N}   float64 {tn:.1f}s   mpmath {tm:.0f}s")
        for k, nm in ((0, "det(1-PL)"), (1, "det(1+PL)")):
            adiff = abs(mp.mpc(dn[k]) - dm[k])
            rel = adiff/abs(dm[k])
            nrm = adiff/scale
            trunc = abs(mp.mpc(dn[k]) - mp.mpc(d8[k]))
            worst = max(worst, nrm)
            log(f"       {nm}: |det| = {float(abs(dm[k])):.6e}")
            log(f"          float64-vs-mpmath  abs {mp.nstr(adiff,3)}"
                f"   rel {mp.nstr(rel,3)}   /localscale {mp.nstr(nrm,3)}")
            log(f"          truncation N{N}-vs-N{N+8}  abs {mp.nstr(trunc,3)}"
                f"   -> float64 error is {mp.nstr(adiff/trunc,3)} of it")
    log(f"V4  worst float64 discrepancy / local determinant scale: {mp.nstr(worst,3)}")
    assert worst < mp.mpf('1e-9'), "V4 FAILED -- float64 path not usable"
    log("V4  PASS -- float64 determinant error is far below the truncation error;")
    log("    the float64 path is used from here on (100x faster than mp.det).")
    log("")

def gate_truncation(rep, label, spts, Nprod=NPROD):
    log(f"V5  truncation gate, {label}: N={Nprod} vs N={Nprod+8}")
    worst = 0.0
    for st in spts:
        d1 = dets(st, Nprod, rep)
        d2 = dets(st, Nprod + 8, rep)
        scale = max(abs(d2[0]), abs(d2[1]))
        for k, nm in ((0, "det(1-PL)"), (1, "det(1+PL)")):
            rel = abs(d1[k] - d2[k])/abs(d2[k])
            nrm = abs(d1[k] - d2[k])/scale
            worst = max(worst, nrm)
            log(f"     s={st}  {nm}: |det|={abs(d2[k]):.6e}"
                f"   rel drift {rel:.2e}   drift/scale {nrm:.2e}")
    log(f"V5  worst scale-normalized drift {worst:.2e}")
    assert worst < 1e-7, "V5 FAILED"
    log("")

def gate_dps(rep, st, N):
    """Separate roundoff from truncation by rebuilding the entries at higher dps."""
    global DPS
    log(f"V5b roundoff separation at s={st}, N={N}")
    d = {}
    for dps in (30, 40, 55):
        mp.mp.dps = dps
        globals()['R'] = mp.mpf(3)/2
        r2 = Rep(rep.power)
        d[dps] = dets(st, N, r2)
    mp.mp.dps = DPS
    globals()['R'] = mp.mpf(3)/2
    sc = max(abs(d[55][0]), abs(d[55][1]))
    for k, nm in ((0, "det(1-PL)"), (1, "det(1+PL)")):
        log(f"     {nm}: dps30 vs 55 {abs(d[30][k]-d[55][k])/sc:.2e}"
            f"   dps40 vs 55 {abs(d[40][k]-d[55][k])/sc:.2e}   (scale-normalized)")
    log("")

# ============================ Phase 1: THE GATE ==============================
# M2-certified Gamma_0(3) spectral parameters (from codex/RH_M2_COMPLETE_2026-08-03.md,
# themselves matched to LMFDB's rigorous collection).  Level-1 forms must appear
# in Gamma_0(9) with multiplicity 3 (divisors of 9); level-3 newforms with
# multiplicity 2 (divisors of 9/3).  Parity is preserved by the oldform maps.
GAMMA03 = [
    ("4.38805356322", "odd",  "level-3 new"),
    ("5.09874190873", "even", "level-3 new"),
    ("6.12057553309", "odd",  "level-3 new"),
    ("6.75741527775", "odd",  "level-3 new"),
    ("7.75813319502", "odd",  "level-3 new"),
    ("8.03886120386", "even", "level-3 new"),
    ("8.19303593168", "odd",  "level-3 new"),
    ("8.77828239355", "even", "level-3 new"),
    ("9.29237932822", "odd",  "level-3 new"),
    ("9.53369526135", "odd",  "level-1 old"),
]

def phase1(rep, N=NPROD, t0=4.0, t1=9.70, step=0.05):
    log("=" * 74)
    log("PHASE 1 -- THE GATE: trivial-character Gamma_0(9) on Re s = 1/2")
    log("=" * 74)
    log("Prediction, no external data needed: the M2-certified Gamma_0(3)")
    log("spectrum must appear inside Z_{Gamma_0(9)} = det(1-PL) det(1+PL),")
    log("in the SAME parity factor (even <-> det(1-PL), odd <-> det(1+PL)).")
    log(f"Scan N={N}, dps={DPS}, t in [{t0}, {t1}], step {step}.")
    ts, vm, vp = [], [], []
    tt = mp.mpf(repr(t0))
    while tt <= mp.mpf(repr(t1)) + mp.mpf('1e-9'):
        a, b = dets(mp.mpc(mp.mpf('0.5'), tt), N, rep)
        ts.append(tt); vm.append(abs(a)); vp.append(abs(b))
        tt += mp.mpf(repr(step))
    log(f"  {len(ts)} scan points computed.")

    def refine(idx, j):
        """Local 5-point refinement at step/10 then a parabolic fit."""
        h = mp.mpf(repr(step))/10
        c = ts[j]
        xs = [c + (k - 2)*h for k in range(5)]
        ys = [abs(dets(mp.mpc(mp.mpf('0.5'), x), N, rep)[idx]) for x in xs]
        k = min(range(5), key=lambda q: ys[q])
        if k in (0, 4):
            return xs[k], ys[k]
        fm, f0, fp = ys[k-1], ys[k], ys[k+1]
        den = fm - 2*f0 + fp
        xstar = xs[k] + (h*(fm - fp)/(2*den) if den > 0 else 0)
        return xstar, abs(dets(mp.mpc(mp.mpf('0.5'), xstar), N, rep)[idx])

    found = {"even": [], "odd": []}
    for idx, par, nm in ((0, "even", "det(1-PL)"), (1, "odd", "det(1+PL)")):
        arr = vm if idx == 0 else vp
        log(f"\n  local minima of |{nm}|  (parity {par}):")
        for j in range(1, len(ts) - 1):
            if arr[j] < arr[j-1] and arr[j] < arr[j+1]:
                xs, v = refine(idx, j)
                depth = v/((arr[j-1] + arr[j+1])/2)
                found[par].append((xs, v, depth))
                log(f"    t* = {mp.nstr(xs, 11):>16}   |det| = {v:.3e}   depth = {depth:.3e}")

    log("\n  MATCH TABLE against the M2-certified Gamma_0(3) spectrum:")
    log("  | certified r | parity | expected mult | found t* | offset | verdict |")
    log("  |---|---|---|---|---|---|")
    nhit = 0
    for rstr, par, kind in GAMMA03:
        rv = mp.mpf(rstr)
        mult = 3 if kind == "level-1 old" else 2
        cands = [f for f in found[par] if abs(f[0] - rv) < mp.mpf('0.02')]
        if cands:
            best = min(cands, key=lambda f: abs(f[0] - rv))
            off = best[0] - rv
            nhit += 1
            log(f"  | {rstr} | {par} | {mult} | {mp.nstr(best[0], 11)} | {mp.nstr(off, 3)} | HIT |")
        else:
            log(f"  | {rstr} | {par} | {mult} | -- | -- | MISSED |")
    log(f"\n  P1 GATE: {nhit}/{len(GAMMA03)} certified Gamma_0(3) parameters recovered.")
    # cross-contamination: a certified value must NOT appear in the other factor
    log("  cross-parity contamination check (a value must be absent from the other factor):")
    bad = 0
    for rstr, par, kind in GAMMA03:
        rv = mp.mpf(rstr)
        other = "odd" if par == "even" else "even"
        cands = [f for f in found[other] if abs(f[0] - rv) < mp.mpf('0.01')]
        if cands:
            bad += 1
            log(f"    CONTAMINATION: {rstr} ({par}) also minimises the {other} factor at "
                f"{mp.nstr(cands[0][0],9)}")
    log(f"    contaminated: {bad}/{len(GAMMA03)}")
    extra = [f for par in ("even", "odd") for f in found[par]
             if not any(abs(f[0] - mp.mpf(r)) < mp.mpf('0.02') for r, _, _ in GAMMA03)]
    log(f"  minima not matching any Gamma_0(3) parameter (candidate level-9 newforms "
        f"or shallow non-zeros): {len(extra)}")
    for f in extra:
        log(f"    t* = {mp.nstr(f[0], 11)}   |det| = {f[1]:.3e}   depth = {f[2]:.3e}")
    log("")
    return nhit, bad

def phase1b(rep, N=NPROD, delta=0.15):
    """THE GATE, direct form.  No scan, no refinement, no fitting: evaluate
    |det(1 -+ P L_s)| AT each M2-certified Gamma_0(3) spectral parameter and at
    controls +- delta.  If the parameter is a zero of that factor, |det| sits on
    the truncation floor there and is O(1) at the controls.  This avoids the
    minimum-finding heuristics entirely, which is where the scan version of the
    gate was fragile."""
    log("=" * 74)
    log("PHASE 1b -- THE GATE, direct evaluation at the certified parameters")
    log("=" * 74)
    log(f"Trivial-character Gamma_0(9), Re s = 1/2, N={N}, dps={DPS},"
        f" controls at r +- {delta}.")
    log("Expected: a certified value is a zero of the factor matching its")
    log("PARITY, with multiplicity 3 if it is a level-1 form and 2 if it is a")
    log("level-3 newform.  It must be a zero of NEITHER factor's partner.")
    log("")
    log("  | certified r | parity | mult | factor | |det| at r | ctrl(r-.15) | "
        "ctrl(r+.15) | ratio |")
    log("  |---|---|---|---|---|---|---|---|")
    verdict = []
    for rstr, par, kind in GAMMA03:
        rv = mp.mpf(rstr)
        mult = 3 if kind == "level-1 old" else 2
        at = dets(mp.mpc(mp.mpf('0.5'), rv), N, rep)
        cm = dets(mp.mpc(mp.mpf('0.5'), rv - delta), N, rep)
        cp = dets(mp.mpc(mp.mpf('0.5'), rv + delta), N, rep)
        row = {}
        for k, nm in ((0, "det(1-PL)"), (1, "det(1+PL)")):
            v = abs(at[k]); a = abs(cm[k]); b = abs(cp[k])
            ratio = v/((a*b)**0.5)
            row[k] = ratio
            tag = "<= expected zero" if (k == 0) == (par == "even") else ""
            log(f"  | {rstr} | {par} | {mult} | {nm} | {v:.4e} | {a:.3e} | "
                f"{b:.3e} | {ratio:.3e} | {tag}")
        kexp = 0 if par == "even" else 1
        verdict.append((rstr, par, row[kexp], row[1 - kexp]))
    log("")
    log("  SUMMARY")
    log("  | certified r | parity | ratio in EXPECTED factor | ratio in OTHER factor |")
    log("  |---|---|---|---|")
    nhit = ncontam = 0
    for rstr, par, rexp, roth in verdict:
        if rexp < 1e-4: nhit += 1
        if roth < 1e-4: ncontam += 1
        log(f"  | {rstr} | {par} | {rexp:.3e} | {roth:.3e} |")
    log("")
    log(f"  P1 GATE: {nhit}/{len(GAMMA03)} certified parameters are zeros of the")
    log(f"           parity-correct factor (ratio < 1e-4).")
    log(f"           cross-parity contamination: {ncontam}/{len(GAMMA03)}.")
    log("")
    return nhit, ncontam

def fibre_basis():
    """P^1(Z/9) -> P^1(Z/3) has 4 fibres of size 3.  Functions pulled back along
    it span a 4-dim INVARIANT subspace carrying Ind_{Gamma_0(3)}^{PSL(2,Z)} 1
    (M2's operator); its orthogonal complement is the 8-dim level-9-new part."""
    def red(p):
        c, d = p[0] % 3, p[1] % 3
        if c == 0: return (0, 1)
        if c == 2: c, d = (2*c) % 3, (2*d) % 3
        return (c, d)
    fib = {}
    for i, p in enumerate(PTS):
        fib.setdefault(red(p), []).append(i)
    cols = []
    for _, idx in sorted(fib.items()):
        v = np.zeros(DIM); v[idx] = 1.0; cols.append(v/np.linalg.norm(v))
    for _, idx in sorted(fib.items()):
        for k in range(1, len(idx)):
            v = np.zeros(DIM); v[idx[0]] = 1.0; v[idx[k]] = -1.0
            cols.append(v/np.linalg.norm(v))
    B, _ = np.linalg.qr(np.array(cols).T)
    return B, fib

def phase1c(rep, N=40, tol=1e-6):
    """Multiplicity structure: eigenvalues of P.L on the unit circle at each
    certified parameter, split over the 4-dim Gamma_0(3) pull-back block and
    the 8-dim level-9-new block.  det(1-PL) = 0 <-> an eigenvalue at +1;
    det(1+PL) = 0 <-> an eigenvalue at -1; the ORDER of the zero is the number
    of such eigenvalues."""
    log("=" * 74)
    log("PHASE 1c -- multiplicity structure, read off the spectrum of P.L")
    log("=" * 74)
    B, fib = fibre_basis()
    log(f"fibres of P^1(Z/9) -> P^1(Z/3): {fib}")
    log(f"Trivial character, Re s = 1/2, N={N}; eigenvalues within {tol} of the")
    log("unit circle are listed.  Expected oldform multiplicity in Gamma_0(9):")
    log("3 for a level-1 form (divisors of 9), 2 for a level-3 newform.")
    log("")
    log("  | certified r | parity | expected mult | eigenvalues near +-1 (full 12-dim) "
        "| 4-dim block | 8-dim block |")
    log("  |---|---|---|---|---|---|")
    Bk = np.kron(B, np.eye(N))
    for rstr, par, kind in GAMMA03:
        mult = 3 if kind == "level-1 old" else 2
        M = PL_matrix(mp.mpc(mp.mpf('0.5'), mp.mpf(rstr)), N, rep)
        Mb = Bk.T.conj() @ M @ Bk
        def near(A):
            ev = np.linalg.eigvals(A)
            return sorted((z for z in ev if abs(abs(z) - 1) < tol),
                          key=lambda z: -z.real)
        f = lambda zs: ", ".join(f"{z.real:+.11f}" for z in zs) or "none"
        log(f"  | {rstr} | {par} | {mult} | {f(near(M))} | "
            f"{f(near(Mb[:4*N, :4*N]))} | {f(near(Mb[4*N:, 4*N:]))} |")
    log("")

# ============================ Phase 2: the L-function test ===================
def read_targets():
    out = []
    with open(TARGETS) as fh:
        which = None
        for line in fh:
            ls = line.strip()
            if ls.startswith("# --- chi^1"): which = "chi^1"; continue
            if ls.startswith("# --- chi^2"): which = "chi^2"; continue
            if not ls or ls.startswith("#"): continue
            gam = mp.mpf(ls.split()[0])
            out.append((which, gam, gam/2))
    return out

def refine_min(idx, t0, rep, N, h0=mp.mpf('0.02'), iters=9):
    """Parabolic descent on |det| along Re s = 1/4, starting at t0."""
    t0 = mp.mpf(t0); h = h0
    for _ in range(iters):
        f = lambda x: abs(dets(mp.mpc(mp.mpf('0.25'), x), N, rep)[idx])
        fm, f0, fp = f(t0 - h), f(t0), f(t0 + h)
        den = fm - 2*f0 + fp
        if den <= 0:
            t0 = t0 - h if fm < fp else t0 + h
        else:
            t0 += h*(fm - fp)/(2*den)
        h /= 2
    return t0, abs(dets(mp.mpc(mp.mpf('0.25'), t0), N, rep)[idx])

def phase2(reps, N=NPROD, delta=0.30):
    log("=" * 74)
    log("PHASE 2 -- L(s, chi_9) zeros on Re s = 1/4")
    log("=" * 74)
    tg = read_targets()
    log(f"{len(tg)} targets read from {os.path.basename(TARGETS)} (not regenerated).")
    tset = [float(t) for _, _, t in tg]
    log(f"Controls: t +- {delta}; a control is dropped if it lands within 0.15")
    log("of any target.  'ratio' = |det| at the target / geometric mean of the")
    log("surviving controls.  A hit means ratio << 1; a null result means ratio ~ 1.")
    def fmt(x):
        return "     --    " if x is None else f"{x:.3e}"
    hits = []
    for name, rep in reps:
        log(f"\n--- operator: Gamma_0(9) twisted by {name},  N={N} ---")
        log("  rows are logged as they are computed.")
        log("  | src | gamma | t = gamma/2 | factor | |det| at target |"
            " ctrl(t-0.3) | ctrl(t+0.3) | ratio |")
        log("  |---|---|---|---|---|---|---|---|")
        rows = {0: [], 1: []}
        for src, gam, t in tg:
            vals = {}
            for tag, tv in (("c-", t - delta), ("t", t), ("c+", t + delta)):
                if tag != "t" and min(abs(float(tv) - x) for x in tset) < 0.15:
                    vals[tag] = None
                    continue
                a, b = dets(mp.mpc(mp.mpf('0.25'), tv), N, rep)
                vals[tag] = (abs(a), abs(b))
            for k, fac in ((0, "det(1-PL)"), (1, "det(1+PL)")):
                vt = vals["t"][k]
                cm = vals["c-"][k] if vals["c-"] else None
                cp = vals["c+"][k] if vals["c+"] else None
                cs = [c for c in (cm, cp) if c is not None]
                ratio = (float(vt)/float(np.prod(cs))**(1.0/len(cs))) if cs \
                    else float('nan')
                rows[k].append((src, gam, t, vt, cm, cp, ratio))
                log(f"  | {src} | {mp.nstr(gam, 10)} | {mp.nstr(t, 10)} | {fac} |"
                    f" {vt:.4e} | {fmt(cm)} | {fmt(cp)} | {ratio:.3e} |")
                if ratio < 1e-2:
                    hits.append((name, k, src, gam, t, ratio))
        for k, nm in ((0, "det(1 - P L)  [even factor]"),
                      (1, "det(1 + P L)  [odd factor]")):
            fin = [r for r in rows[k] if r[6] == r[6]]
            best = min(fin, key=lambda r: r[6]); worst = max(fin, key=lambda r: r[6])
            log(f"  {nm}: smallest ratio {best[6]:.3e} at gamma ="
                f" {mp.nstr(best[1],10)};  largest ratio {worst[6]:.3e}"
                f" at gamma = {mp.nstr(worst[1],10)}")
    log("\n  Targets with ratio < 1e-2 (candidate hits): "
        f"{len(hits)} of {2*len(tg)*len(reps)} (target, factor) pairs tested.")
    for name, k, src, gam, t, ratio in hits:
        log(f"    {name}  {'det(1-PL)' if k == 0 else 'det(1+PL)'}  "
            f"{src} gamma={mp.nstr(gam,12)}  ratio {ratio:.3e}")
    return hits

def phase2_refine(hits, reps, N=NPROD, cap=4, iters=5):
    """For the strongest candidate hits, locate the actual minimum and report
    the offset from the predicted t = gamma/2.  Capped: each refinement costs
    3*iters+1 determinant evaluations."""
    if not hits:
        log("  no candidate hits to refine.")
        return
    sel = sorted(hits, key=lambda h: h[5])[:cap]
    log(f"\n  REFINEMENT of the {len(sel)} strongest hits of {len(hits)} "
        f"(minimum located, then compared to gamma/2):")
    log("  | operator | factor | predicted t = gamma/2 | located t* | offset | |det| at t* |")
    log("  |---|---|---|---|---|---|")
    byname = dict(reps)
    for name, k, src, gam, t, ratio in sel:
        ts, v = refine_min(k, t, byname[name], N, iters=iters)
        log(f"  | {name} | {'det(1-PL)' if k == 0 else 'det(1+PL)'} | "
            f"{mp.nstr(t, 12)} | {mp.nstr(ts, 12)} | {mp.nstr(ts - t, 3)} | {v:.3e} |")

def phase2_conjugation(reps, N=32):
    """det(1 - P L_s^{chi2}) must equal conj(det(1 - P L_{sbar}^{chi}))."""
    log("V6  conjugation relation between the chi and chi^2 operators")
    r1 = dict(reps)["chi"]; r2 = dict(reps)["chi^2"]
    for t in (mp.mpf('3.9'), mp.mpf('7.3')):
        a = dets(mp.mpc(mp.mpf('0.25'), t), N, r2)
        b = dets(mp.mpc(mp.mpf('0.25'), -t), N, r1)
        e0 = abs(a[0] - np.conj(b[0]))/abs(a[0])
        e1 = abs(a[1] - np.conj(b[1]))/abs(a[1])
        log(f"     t={mp.nstr(t,4)}: rel {e0:.2e} (minus factor), {e1:.2e} (plus factor)")
    log("")

# ============================ main ===========================================
if __name__ == "__main__":
    log("\n" + "#" * 74)
    log(f"# RUN {time.strftime('%Y-%m-%d %H:%M:%S')}   args={' '.join(sys.argv[1:])}")
    log("#" * 74)
    args = sys.argv[1:]
    reps = None

    if "--gates" in args or not args:
        gates_representation()
        gate_blocks()

    if "--detgate" in args:
        rep1 = Rep(1)
        # the near-zero point is the demanding case; a generic point at smaller
        # N gives a second, cheaper data point.
        gate_det_path(rep1, [(mp.mpc('0.25', '9.884965957990'), 40),
                             (mp.mpc('0.5', '7.3'), 24)])

    if "--trunc" in args:
        rep0, rep1 = Rep(0), Rep(1)
        gate_truncation(rep0, "trivial character, Re s = 1/2",
                        [mp.mpc('0.5', '9.7')])
        gate_truncation(rep1, "chi, Re s = 1/4",
                        [mp.mpc('0.25', '9.884965957990'),
                         mp.mpc('0.25', '-9.884965957990')])
        gate_dps(rep1, mp.mpc('0.25', '9.884965957990'), 40)

    if "--phase1" in args:
        phase1(Rep(0))

    if "--phase1b" in args:
        phase1b(Rep(0))

    if "--phase1c" in args:
        phase1c(Rep(0))

    if "--phase2" in args:
        NP2 = 64            # V5: scale-normalized truncation drift 1.2e-9 at N=56
        r1, r2, r0 = Rep(1), Rep(2), Rep(0)
        # chi^2 is covered by the conjugation relation V6, so the full table is
        # run for chi and for the TRIVIAL character (the structural control:
        # it answers whether the chi-twist is what brings the L-function in).
        allreps = [("chi", r1), ("trivial", r0)]
        phase2_conjugation([("chi", r1), ("chi^2", r2)], N=40)
        hits = phase2(allreps, N=NP2)
        phase2_refine(hits, allreps, N=NP2)

    if _OUT: _OUT.close()
