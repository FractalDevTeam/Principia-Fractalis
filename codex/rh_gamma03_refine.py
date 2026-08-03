#!/usr/bin/env python3
"""M2 refinement: polish the 10 pilot minima of the P-twisted rho3 determinants
to high precision.  Reuses the validated machinery of rh_gamma03_m2.py by
module import; configuration identical to the gated production scan
(dps=40, N=56, FM convention, P-twist)."""
import importlib.util, sys
import mpmath as mp

spec = importlib.util.spec_from_file_location("m2", "codex/rh_gamma03_m2.py")
m2 = importlib.util.module_from_spec(spec); sys.modules["m2"] = m2
spec.loader.exec_module(m2)          # __main__ guard keeps this side-effect free

mp.mp.dps = 40
m2.R = mp.mpf(3)/2
m2.validate_group()
Q = m2.split_basis(); Ptw = m2.twist_P(); reps = m2.rep_matrices(+1)
N = 56

def f(idx):
    def g(t):
        L = m2.twisted_op(mp.mpc(0.5, t), N, Q, reps, Ptw)
        a, b = m2.dets_of(L, 3*N)
        return abs(a) if idx == 0 else abs(b)
    return g

def refine(fun, t0, h):
    t0 = mp.mpf(t0); h = mp.mpf(h)
    for _ in range(16):
        fm, f0, fp = fun(t0-h), fun(t0), fun(t0+h)
        den = fm - 2*f0 + fp
        if den <= 0: break
        t0 += h*(fm - fp)/(2*den); h /= 2
    return t0, fun(t0)

# (pilot grid t, factor index: 0 = det(1-PL) even, 1 = det(1+PL) odd)
CANDS = [(4.40,1),(5.10,0),(6.10,1),(6.75,1),(7.75,1),(8.05,0),(8.20,1),(8.80,0),(9.30,1),(9.55,1)]
OUT = open("codex/rh_gamma03_refined.txt","w")
for t0, idx in CANDS:
    t_s, v = refine(f(idx), t0, 0.05)
    line = f"factor={'1-PL(even)' if idx==0 else '1+PL(odd)'}  t* = {mp.nstr(t_s, 12)}   |det| = {mp.nstr(v,3)}"
    print(line, flush=True); OUT.write(line+"\n"); OUT.flush()
OUT.close()
