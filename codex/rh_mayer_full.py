#!/usr/bin/env python3
"""
RH front, M1 (v3): FULL-alphabet Mayer operator for PSL(2,Z).
    (L_s f)(x) = sum_{k>=1} (x+k)^(-2s) f(1/(x+k)),   Mayer 1991:
    Z_Selberg(s) = det(1 - L_s) det(1 + L_s), L_s nuclear on H(D(1,3/2)).

EXACT matrix elements in the disc-normalized basis e_n(x) = ((x-1)/R)^n, R=3/2:
    A[m,n](s) = sum_{i<=n} C(n,i)(-1)^(i+m) Poch(2s+n-i,m)/m! zeta_H(2s+n-i+m,2) R^(m-n)
-- a finite Hurwitz-zeta combination, i.e. THE analytic continuation to the
critical line (poles only at 2s+q = 1, off our scan lines).

v1 lesson: raw monomial basis fails truncation check (columns ~1.5^n).
v2 lesson: double precision fails on the line -- entries grow ~e^(pi t/2)
   (the 1/Gamma growth of the continuation), 9+ digits cancel at t=10.
v3: ALL arithmetic in mpmath at dps=30; truncation gates are RELATIVE;
   worst-point (t=20) N=64 vs N=80 gate asserted before scanning.

Checks (asserted): C1 Gauss lambda_max(L_1)=1; C2 relative det drift < 1e-8
at s=1/2+10i and 1/4+7i (N 48/64); C3 relative drift N64 vs 80 at s=1/2+20i.
Scans: S1 Re s=1/2, t in [8,20] step 0.1, minima of |det(I-L)|, |det(I+L)|
refined; S2 Re s=1/4, t' in [6.60,7.55] step 0.01, |det(I-L)det(I+L)|
(marker rho_1/2 = 7.0673626...). Results -> codex/rh_mayer_full_results.txt
"""
import mpmath as mp
from math import comb

mp.mp.dps = 50   # v5: dps=30 was roundoff-limited (cancellation in Poch*zeta assembly grows with N); at dps=50 measured truncation N72 vs 88 = 5.3e-14, N88 vs 104 = 1.5e-18 at the worst point s = 1/2 + 15.2i
R = mp.mpf(3)/2
OUT = open("codex/rh_mayer_full_results.txt", "w")
def log(s):
    print(s, flush=True); OUT.write(s + "\n"); OUT.flush()

def matrix(s, N):
    z = [mp.zeta(2*s + q, 2) for q in range(2*N + 1)]
    A = mp.zeros(N, N)
    for n in range(N):
        Rf = [R**(m - n) for m in range(N)]
        for i in range(n + 1):
            c0 = comb(n, i) * (-1)**i
            sig = 2*s + n - i
            poch = mp.mpc(1)
            for m in range(N):
                if m > 0:
                    poch *= (sig + m - 1)/m
                A[m, n] += c0 * (-1)**m * poch * z[n - i + m] * Rf[m]
    return A

def dets(s, N=72):
    A = matrix(s, N)
    I = mp.eye(N)
    return mp.det(I - A), mp.det(I + A)

# C1 -------------------------------------------------------------------------
A1 = matrix(mp.mpf(1), 48)
lam = max(abs(w) for w in mp.eig(A1, left=False, right=False))
log(f"C1  lambda_max(L_1) = {mp.nstr(lam, 15)}   (must be 1)")
assert abs(lam - 1) < mp.mpf('1e-12'), "Gauss check FAILED"

# C2 -------------------------------------------------------------------------
for st in (mp.mpc(0.5, 10), mp.mpc(0.25, 7)):
    a72, b72 = dets(st, 72); a88, b88 = dets(st, 88)
    r1 = abs(a72 - a88)/abs(a88); r2 = abs(b72 - b88)/abs(b88)
    log(f"C2  s={st}  rel det drift N72 vs 88 (production vs larger): {mp.nstr(r1,3)} {mp.nstr(r2,3)}")
    assert max(r1, r2) < mp.mpf('1e-10'), "truncation instability"

# C3 (worst point of the restricted scan) -------------------------------------
# v3 lesson: at t=20 even N=80 drifts 1.4e-2 -- the continuation grows like
# e^(pi t/2), so the section size must grow with t.  This pass restricts to
# t <= 15.2, where N=72 is gated below; higher t needs a follow-up run with
# N ~ 100+ and dps ~ 40 (Fraczek's regime).  No silent extrapolation.
st = mp.mpc(0.5, mp.mpf('15.2'))
a72, b72 = dets(st, 72); a88, b88 = dets(st, 88)
r1 = abs(a72 - a88)/abs(a88); r2 = abs(b72 - b88)/abs(b88)
log(f"C3  s={st}  rel det drift N72 vs 88: {mp.nstr(r1,3)} {mp.nstr(r2,3)}")
assert max(r1, r2) < mp.mpf('1e-10'), "worst-point instability"

# S1 -------------------------------------------------------------------------
log("\nS1  Re s = 1/2, t in [8,15.2], step 0.1")
ts = [8 + mp.mpf(j)/10 for j in range(73)]
vm, vp = [], []
for t in ts:
    a, b = dets(mp.mpc(0.5, t))
    vm.append(abs(a)); vp.append(abs(b))
    if float(t*10) % 20 == 0: log(f"    t={mp.nstr(t,4)}  |1-L|={mp.nstr(abs(a),4)}  |1+L|={mp.nstr(abs(b),4)}")

def refine(fun, t0, h):
    t0 = mp.mpf(t0); h = mp.mpf(h)
    for _ in range(14):
        fm, f0, fp = fun(t0-h), fun(t0), fun(t0+h)
        den = fm - 2*f0 + fp
        if den <= 0: break
        t0 += h*(fm - fp)/(2*den); h /= 2
    return t0, fun(t0)

for name, arr, idx in (("det(1-L)", vm, 0), ("det(1+L)", vp, 1)):
    log(f"  local minima of |{name}| (t*, |det|, depth ratio vs neighbors):")
    for j in range(1, 72):
        if arr[j] < arr[j-1] and arr[j] < arr[j+1]:
            f = lambda t: abs(dets(mp.mpc(0.5, t))[idx])
            t_s, v = refine(f, ts[j], mp.mpf('0.1'))
            depth = v/((arr[j-1] + arr[j+1])/2)
            log(f"    t* = {mp.nstr(t_s, 11)}   |det| = {mp.nstr(v,3)}   depth = {mp.nstr(depth,3)}")

# S2 -------------------------------------------------------------------------
log("\nS2  Re s = 1/4, t' in [6.60,7.55], step 0.01 (marker rho_1/2 = 7.06736279...)")
tps = [mp.mpf('6.60') + mp.mpf(j)/100 for j in range(96)]
pv = []
for tp in tps:
    a, b = dets(mp.mpc(0.25, tp))
    pv.append(abs(a*b))
jm = min(range(96), key=lambda j: pv[j])
# Lewis-Zagier: at s = rho/2 the +1-eigenfunction exists (EVEN factor
# det(1-L) vanishes); det(1+L) must NOT vanish there. Test both separately.
fA = lambda t: abs(dets(mp.mpc(0.25, t))[0])
t_s, v = refine(fA, tps[jm], mp.mpf('0.01'))
log(f"  |det(1-L)| minimum: t' = {mp.nstr(t_s, 11)}   value = {mp.nstr(v,3)}")
log(f"  offset from rho_1/2 = 7.0673627606: {mp.nstr(t_s - mp.mpf('7.0673627606'), 3)}")
aA, bB = dets(mp.mpc(0.25, t_s))
log(f"  ODD factor at the same point (must be far from 0): |det(1+L)| = {mp.nstr(abs(bB),3)}")
log(f"  contrast |det(1-L)|: at 6.60 = {mp.nstr(abs(dets(mp.mpc(0.25, mp.mpf('6.60')))[0]),3)}, at 7.55 = {mp.nstr(abs(dets(mp.mpc(0.25, mp.mpf('7.55')))[0]),3)}")
OUT.close()
