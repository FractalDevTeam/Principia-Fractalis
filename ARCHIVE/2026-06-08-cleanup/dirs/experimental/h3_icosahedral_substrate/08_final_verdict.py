"""
Final verdict tests.

T1: High precision on the alpha=3 "near hit" (0.66% gap).
    If real, it should converge to EXACT pi/30 = 0.1047197551... as quadrature improves.
T2: Same calculation REMOVING H_3 symmetry (random potential same energy scale).
    If the close hits are due to symmetry, randomizing should destroy them.
T3: Bayes-style probability check.  Given 11 random eigenvalues spread over [-1, 2],
    what's the chance that one lies within 1% of the target by accident?
T4: Reverse engineer: for which alpha is there an EXACT eigenvalue at pi/(10 alpha)?
    Solve V_alpha eigenvalue = pi/(10 alpha) for alpha by bisection.
"""

import numpy as np
import mpmath as mp
from scipy.special import eval_legendre
from numpy.polynomial.legendre import leggauss
import itertools

PI = np.pi
mp.mp.dps = 30

def ico_vertices():
    phi = (1+np.sqrt(5))/2
    V = []
    for s1 in (-1,1):
        for s2 in (-1,1):
            V += [(0,s1,s2*phi),(s1,s2*phi,0),(s1*phi,0,s2)]
    V = np.array(V, float); V /= np.linalg.norm(V[0]); return V

def ico_edges():
    V = ico_vertices()
    dists = [(np.linalg.norm(V[i]-V[j]), i, j) for i in range(12) for j in range(i+1,12)]
    edge = sorted(set(round(d[0],8) for d in dists))[1]
    M = []
    for d, i, j in dists:
        if abs(d-edge)<1e-6:
            m = (V[i]+V[j])/2; M.append(m/np.linalg.norm(m))
    return np.array(M)

V12 = ico_vertices()
E30 = ico_edges()

def quad(Nth, Nph):
    x, wx = leggauss(Nth)
    theta = np.arccos(x)
    phi = 2*PI*(np.arange(Nph)+0.5)/Nph
    dphi = 2*PI/Nph
    th, ph = np.meshgrid(theta, phi, indexing='ij')
    w = wx[:,None] * dphi * np.ones((1,Nph))
    return th.ravel(), ph.ravel(), w.ravel()

SPECTRUM = [0, 6, 10, 12, 16, 18, 20, 22, 24, 26, 28]

def best_eig(alpha, N_terms, Nth=80, Nph=160, anchors=E30):
    th, ph, w = quad(Nth, Nph)
    xq = np.stack([np.sin(th)*np.cos(ph), np.sin(th)*np.sin(ph), np.cos(th)], -1)
    basis = np.stack([eval_legendre(l, xq @ V12.T).sum(axis=1) for l in SPECTRUM], axis=0)
    norms = np.sqrt(np.einsum('ip,p->i', basis**2, w))
    U = basis / norms[:,None]
    d = np.min(np.arccos(np.clip(xq @ anchors.T, -1, 1)), axis=1)
    V = np.zeros_like(d)
    for n in range(N_terms):
        V += 2.0**(-n) * np.cos(PI * alpha**n * d)
    M = np.einsum('ip,jp,p->ij', U, U*V, w)
    e = np.linalg.eigvalsh(M)
    t = PI/(10*alpha)
    i = np.argmin(np.abs(e-t))
    return e[i], abs(e[i]-t), e

# T1: high precision alpha=3
print("=== T1: alpha=3.0, edge-midpoints, vary quadrature density + N_terms ===")
print(f"Target pi/30 = {PI/30:.12f}")
for Nth, Nph, N_terms in [(60,120,12), (100,200,16), (160,320,24), (240,480,40)]:
    e, gap, _ = best_eig(3.0, N_terms, Nth, Nph)
    print(f"  Nth={Nth:3d} Nph={Nph:3d} N_terms={N_terms:2d}: e = {e:.10f}  gap = {gap:.10f}")
print("  -> If real, gap should -> 0.  If coincidence, gap will stabilize at finite value.")

# T2: control with rotated/randomized anchors (12 random points instead of vertices)
print("\n=== T2: replace 30 edge-midpoints with 30 RANDOM points on S^2 (control) ===")
print("If the matches are due to icosahedral symmetry, random anchors should destroy them.")
np.random.seed(42)
for trial in range(3):
    rand_pts = np.random.randn(30, 3)
    rand_pts /= np.linalg.norm(rand_pts, axis=1, keepdims=True)
    print(f"\n  Trial {trial+1}:")
    for a in [np.sqrt(2), 2.0, 3.0]:
        e, gap, _ = best_eig(a, 12, 80, 160, anchors=rand_pts)
        print(f"    alpha={a:.4f}: e = {e:.6f}  gap = {gap:.6f}  rel = {gap/(PI/(10*a))*100:.2f}%")

# T3: Probability estimate.
print("\n=== T3: probability of accidental 1% hit ===")
print("With 11 eigenvalues spread over the range of V_alpha (~[-1,2]):")
print(f"  density = 11/3 ~= 3.67 eigenvalues per unit interval")
print(f"  prob of any one within 1% of target (window ~ 2*0.01*target ~ 0.003 at alpha=3.0):")
print(f"  ~ 3.67 * 0.003 = {3.67*0.003*100:.2f}%   --> close hits are EXPECTED by chance")
print(f"  prob within 5%: ~ 3.67 * 2 * 0.05 * 0.105 = {3.67*0.01:.2f} ~= 4%/alpha-scan-point")

# T4: For alpha=3.0 specifically, run bisection
# Actually: for fixed N_terms=40, scan alpha very finely near 3.0 and see if 0.66% gap stays
print("\n=== T4: fine alpha scan around 3.0, see if pi/(10 alpha) is followed ===")
for a in np.linspace(2.9, 3.1, 21):
    e, gap, _ = best_eig(a, 16, 80, 160)
    t = PI/(10*a)
    print(f"  alpha={a:.4f}  target={t:.6f}  best_eig={e:.6f}  gap={gap:.6f}  ratio e/target={e/t:.4f}")
