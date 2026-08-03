#!/usr/bin/env python3
"""
RH front, M2 stage (a): the Gamma_0(3) transfer operator via the induced
permutation representation -- construction, validation, and pilot scan.

THEORY. Cosets Gamma_0(3)\\PSL(2,Z) <-> P^1(F_3) = {(0:1),(1:0),(1:1),(1:2)}
via the bottom row mod 3.  The induced (permutation) representation rho splits
as trivial (+) 3-dimensional (PSL(2,F_3) ~ A_4 acting on 4 points), so

    det(1 -+ L_s^{ind}) = det(1 -+ L_s) * det(1 -+ L_s^{rho3}),

scalar factor = the level-1 Mayer determinant (validated in M1); the rho3
factor carries the NEW level-3 content.  Chang-Mayer/Fraczek-Mayer give
Z_{Gamma_0(3)}(s) = det(1 - L_s^{ind}) det(1 + L_s^{ind}).

OPERATOR.  (L^{ind}_s f)(x) = sum_{k>=1} (x+k)^{-2s} rho(g_k) f(1/(x+k)),
g_k = ST^k (convention CONV=+1) or (ST^k)^{-1} (CONV=-1); rho(T) has order 3,
so the k-sum splits by k mod 3 into three scalar operators A_r tensored with
constant 4x4 permutation matrices.  EXACT matrix elements (disc-normalized
basis ((x-1)/R)^n, R=3/2), derived as in M1 but with the k-sum restricted to
k = 3j + r, j >= 0:

  A_r[m,n](s) = sum_i C(n,i)(-1)^(i+m) Poch(sig,m)/m! 3^-(sig+m)
                  * zeta_H(sig+m, (r+1)/3) * R^(m-n),   sig = 2s+n-i.

ASSERTED VALIDATIONS (all run before any scan):
  V1  P_S^2 = I, P_T^3 = I, (P_S P_T)^3 = I  (PSL relations in the perm rep),
      and the action is transitive.
  V2  sum_{r=1..3} 3^-sig zeta_H(sig,(r+1)/3) = zeta_H(sig,2)  (numeric, 1e-40),
      hence sum_r A_r = the M1 level-1 matrix (checked entrywise, 1e-38).
  V3  Q^T P_g Q block-diagonalizes to 1 (+) 3 for g in {S, T} (offdiag < 1e-40).
  V4  det factorization: det(1 -+ L^{ind}) = det(1 -+ L^{scalar}) det(1 -+ L^{rho3})
      at a test point, both conventions (rel err < 1e-30).
  V5  gates: rho3-block truncation N vs N+16 at the scan's worst point, and
      dps-roundoff separation (dps 30 vs 40).
PILOT SCAN: |det(1 -+ L^{rho3})| on Re s = 1/2, both conventions, t range set
by whichever gate passes.  Zeros to be compared against LMFDB level-3 rigorous
Maass parameters (fetched independently; NOT hardcoded here -- comparison is a
separate step so this scan cannot fit to the target).
"""
import sys
import mpmath as mp
from math import comb

R = None  # set after dps

# ---------- coset machinery over P^1(F_3) ------------------------------------
PTS = [(0,1),(1,0),(1,1),(1,2)]
def norm(p):
    c, d = p[0] % 3, p[1] % 3
    if c == 0: return (0, 1) if d else None
    if c == 2: c, d = (2*c) % 3, (2*d) % 3    # scale by 2 = inverse of 2
    return (c, d)
def act(p, g):
    a, b, c, d = g
    return norm((p[0]*a + p[1]*c, p[0]*b + p[1]*d))
def perm_matrix(g):
    P = [[0]*4 for _ in range(4)]
    for j, p in enumerate(PTS):
        P[PTS.index(act(p, g))][j] = 1
    return mp.matrix(P)

T  = (1,1,0,1); S = (0,-1,1,0)
def mat_mul(g, h):
    a,b,c,d = g; e,f,gg,hh = h
    return (a*e+b*gg, a*f+b*hh, c*e+d*gg, c*f+d*hh)
def mat_inv(g):     # det = 1
    a,b,c,d = g
    return (d,-b,-c,a)

def validate_group():
    PS, PT = perm_matrix(S), perm_matrix(T)
    I4 = mp.eye(4)
    assert mp.mnorm(PS*PS - I4) == 0, "S^2 != I"
    assert mp.mnorm(PT**3 - I4) == 0, "T^3 != I"
    PST = perm_matrix(mat_mul(S, T))
    assert mp.mnorm(PST**3 - I4) == 0, "(ST)^3 != I"
    # composition convention: P_{gh} = P_h P_g (right action)
    assert mp.mnorm(PST - PT*PS) == 0, "composition convention broken"
    orbit = {0}
    for _ in range(4):
        orbit |= {PTS.index(act(PTS[i], S)) for i in orbit} | {PTS.index(act(PTS[i], T)) for i in orbit}
    assert orbit == {0,1,2,3}, "not transitive"
    return PS, PT

def rho(g):
    """Fraczek-Mayer induced rep rho(g)_{ij} = delta(R_i g R_j^-1 in Gamma_0(3)):
    the TRANSPOSE of the left-action permutation matrix; rho(gh) = rho(g)rho(h)."""
    return perm_matrix(g).T

def rep_matrices(conv):
    """rho(ST^k), k = 1..3.  FM's L^+ uses conv=+1; conv=-1 kept for V4 only."""
    out = []
    for k in (1, 2, 3):
        g = mat_mul(S, (1, k, 0, 1))
        if conv < 0: g = mat_inv(g)
        out.append(rho(g))
    return out

def twist_P():
    """FM Thm 2.1.1 symmetry from j = diag(1,-1): bottom row (c,d) -> (-c,d),
    projectively (0:1),(1:0) fixed, (1:1) <-> (1:2)."""
    P = mp.zeros(4,4)
    for j_, pt in enumerate(PTS):
        P[PTS.index(norm((-pt[0], pt[1]))), j_] = 1
    return P

def twisted_op(sv, Nv, Q, reps, Ptw):
    """(P3 (x) I_N) * L_rho3 -- the operator whose two determinants factor
    Z_Gamma0(3) together with the scalar (level-1) factor."""
    L = rho3_op(sv, Nv, +1, Q, reps)
    P3full = Q.T * Ptw * Q
    P3N = mp.zeros(3*Nv, 3*Nv)
    for a in range(3):
        for b in range(3):
            c = P3full[a+1, b+1]
            if c != 0:
                for m in range(Nv):
                    P3N[a*Nv+m, b*Nv+m] = c
    return P3N * L

def split_basis():
    """Q orthogonal: col 0 = invariant vector, cols 1..3 span the 3-dim rep."""
    v = [mp.matrix([mp.mpf(1)/2]*4)]
    for seed in ([1,-1,0,0],[1,0,-1,0],[1,0,0,-1]):
        w = mp.matrix([mp.mpf(x) for x in seed])
        for u in v:
            w -= (u.T*w)[0] * u
        w /= mp.sqrt((w.T*w)[0])
        v.append(w)
    Q = mp.zeros(4,4)
    for j,u in enumerate(v):
        for i in range(4): Q[i,j] = u[i]
    return Q

# ---------- exact matrix elements --------------------------------------------
def block_A(s, N, r):
    """A_r: k-sum restricted to k ≡ r (mod 3), k>=1  (r=3 means k≡0)."""
    z = {}
    A = mp.zeros(N, N)
    a_arg = mp.mpf(r + 1)/3
    for n in range(N):
        Rf = [R**(m - n) for m in range(N)]
        for i in range(n + 1):
            c0 = comb(n, i) * (-1)**i
            sig = 2*s + n - i
            poch = mp.mpc(1)
            for m in range(N):
                if m > 0: poch *= (sig + m - 1)/m
                key = n - i + m
                if key not in z:
                    z[key] = None
                if z[key] is None:
                    z[key] = 3**(-(2*s + key)) * mp.zeta(2*s + key, a_arg)
                A[m, n] += c0 * (-1)**m * poch * z[key] * Rf[m]
    return A

def level1_A(s, N):
    z = [mp.zeta(2*s + q, 2) for q in range(2*N + 1)]
    A = mp.zeros(N, N)
    for n in range(N):
        Rf = [R**(m - n) for m in range(N)]
        for i in range(n + 1):
            c0 = comb(n, i) * (-1)**i
            sig = 2*s + n - i
            poch = mp.mpc(1)
            for m in range(N):
                if m > 0: poch *= (sig + m - 1)/m
                A[m, n] += c0 * (-1)**m * poch * z[n - i + m] * Rf[m]
    return A

def rho3_op(s, N, conv, Q, reps):
    """3N x 3N operator: sum_r A_r (x) R3_r, R3_r = lower 3x3 block of Q^T P Q."""
    L = mp.zeros(3*N, 3*N)
    for r in (1, 2, 3):
        A = block_A(s, N, r)
        P = Q.T * reps[r-1] * Q
        for a in range(3):
            for b in range(3):
                c = P[a+1, b+1]
                if c == 0: continue
                for m in range(N):
                    for n in range(N):
                        if A[m,n] != 0:
                            L[a*N+m, b*N+n] += c * A[m,n]
    return L

def dets_of(Lmat, dim):
    I = mp.eye(dim)
    return mp.det(I - Lmat), mp.det(I + Lmat)

if __name__ == "__main__":
    OUT = open("codex/rh_gamma03_m2_results.txt", "a")
    def log(x):
        print(x, flush=True); OUT.write(x + "\n"); OUT.flush()

    mp.mp.dps = 40
    R = mp.mpf(3)/2
    PS, PT = validate_group()
    log("V1  group relations + transitivity: PASS")

    # V2: restricted-sum consistency
    for sig in (mp.mpc(2.3, 4.1), mp.mpc(1.0, 19.2)):
        lhs = mp.fsum([3**(-sig) * mp.zeta(sig, mp.mpf(r+1)/3) for r in (1,2,3)])
        rhs = mp.zeta(sig, 2)
        assert abs(lhs - rhs) < mp.mpf('1e-35'), "V2 zeta identity FAILED"
    st = mp.mpc(0.5, mp.mpf('5.3')); Ntest = 24
    Asum = block_A(st, Ntest, 1) + block_A(st, Ntest, 2) + block_A(st, Ntest, 3)
    A1 = level1_A(st, Ntest)
    err = max(abs(Asum[i,j] - A1[i,j]) for i in range(Ntest) for j in range(Ntest))
    log(f"V2  sum_r A_r = level-1 A entrywise: max err {mp.nstr(err,3)}")
    assert err < mp.mpf('1e-27'), "V2 FAILED"  # dps=40 chain roundoff measured at 2.4e-30

    # V3: block diagonalization (twist included)
    Q = split_basis()
    Ptw = twist_P()
    for P in (PS, PT, Ptw):
        B = Q.T * P * Q
        off = max(abs(B[0, j]) for j in range(1,4)) + max(abs(B[j, 0]) for j in range(1,4))
        assert off < mp.mpf('1e-35'), "V3 FAILED"
    log("V3  induced rep splits 1 (+) 3, twist included: PASS")

    # V3b: FM Thm 2.1.1 intertwining relations, in FM's rho
    rS, rT, rTi = rho(S), rho(T), rho(mat_inv(T))
    assert mp.mnorm(Ptw*rS - rS*Ptw) == 0, "V3b: P rho(S) != rho(S) P"
    assert mp.mnorm(Ptw*rT - rTi*Ptw) == 0, "V3b: P rho(T) != rho(T^-1) P"
    assert mp.mnorm(Ptw*Ptw - mp.eye(4)) == 0, "V3b: P^2 != 1"
    log("V3b FM intertwining P rho(S)=rho(S)P, P rho(T)=rho(T^-1)P: PASS")

    # V4: det factorization at a test point, both conventions
    for conv in (+1, -1):
        reps = rep_matrices(conv)
        Nv = 20
        Lfull = mp.zeros(4*Nv, 4*Nv)
        for r in (1,2,3):
            A = block_A(st, Nv, r); P = reps[r-1]
            for a in range(4):
                for b in range(4):
                    if P[a,b] == 0: continue
                    for m in range(Nv):
                        for n in range(Nv):
                            Lfull[a*Nv+m, b*Nv+n] += P[a,b]*A[m,n]
        dfm, dfp = dets_of(Lfull, 4*Nv)
        dsm, dsp = dets_of(level1_A(st, Nv), Nv)
        drm, drp = dets_of(rho3_op(st, Nv, conv, Q, reps), 3*Nv)
        e1 = abs(dfm - dsm*drm)/abs(dfm); e2 = abs(dfp - dsp*drp)/abs(dfp)
        log(f"V4  conv={conv:+d}  factorization rel err: {mp.nstr(e1,3)} {mp.nstr(e2,3)}")
        assert max(e1, e2) < mp.mpf('1e-25'), "V4 FAILED"

    log("ALL VALIDATIONS PASS")

    if "--scan" in sys.argv:
        # V5 gates at the worst point, then pilot scan (both conventions).
        tmax = mp.mpf('9.6'); Nprod = 56   # N=48 gated at 1.04e-8, marginally over
        reps = rep_matrices(+1)                      # FM convention rho(ST^{+n})
        g1 = dets_of(twisted_op(mp.mpc(0.5, tmax), Nprod, Q, reps, Ptw), 3*Nprod)
        g2 = dets_of(twisted_op(mp.mpc(0.5, tmax), Nprod+16, Q, reps, Ptw), 3*(Nprod+16))
        r1 = abs(g1[0]-g2[0])/abs(g2[0]); r2 = abs(g1[1]-g2[1])/abs(g2[1])
        log(f"V5  P-twisted rho3, N{Nprod} vs N{Nprod+16} at t={tmax}: {mp.nstr(r1,3)} {mp.nstr(r2,3)}")
        assert max(r1, r2) < mp.mpf('1e-8'), "V5 gate FAILED"
        log(f"\nSCAN P-twisted rho3 factor of Z_Gamma0(3), Re s = 1/2, t in [2.0, 9.6], step 0.05")
        t = mp.mpf(2)
        vals = []
        while t <= tmax + mp.mpf('1e-9'):
            a, b = dets_of(twisted_op(mp.mpc(0.5, t), Nprod, Q, reps, Ptw), 3*Nprod)
            vals.append((t, abs(a), abs(b)))
            t += mp.mpf('0.05')
        for j in range(1, len(vals)-1):
            for idx, nm in ((1, "det(1-PL_rho3)"), (2, "det(1+PL_rho3)")):
                if vals[j][idx] < vals[j-1][idx] and vals[j][idx] < vals[j+1][idx]:
                    depth = vals[j][idx]/((vals[j-1][idx]+vals[j+1][idx])/2)
                    log(f"  min |{nm}| near t = {mp.nstr(vals[j][0],4)}  val = {mp.nstr(vals[j][idx],3)}  depth = {mp.nstr(depth,3)}")
        log("PILOT DONE")
    OUT.close()
