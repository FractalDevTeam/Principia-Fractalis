"""
Deep dive on C9 (edge-midpoint distance), which got within ~2-8% across alpha.

Questions:
  Q1: Is the proximity to pi/(10 alpha) robust to N_terms and decay weight?
  Q2: Does the *exact* match exist as N_terms -> infinity?
  Q3: What's the asymptotic form of the operator's lowest-magnitude eigenvalue?
  Q4: Is the same proximity reproduced if we use H_3-NON-invariant subspace
      (i.e., is it a quirk of the 30 edge midpoints, not the H_3-symmetry)?

Also: test with HIGH precision (mpmath) on the most promising case.
"""
import numpy as np
from scipy.special import eval_legendre
from numpy.polynomial.legendre import leggauss
import itertools

PI = np.pi

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
            m = (V[i]+V[j])/2
            M.append(m/np.linalg.norm(m))
    return np.array(M)

V12 = ico_vertices()
E30 = ico_edges()
print(f"E30: {len(E30)} edge midpoints; should be 30")
# Octahedral angle between adjacent edge midpoints
dots = sorted(set(round(E30[0] @ E30[i], 6) for i in range(30) if i!=0))
print(f"Distinct dot products from one edge midpoint to others: {dots[:6]}...")

def quad_sphere(Nth=100, Nph=200):
    x, wx = leggauss(Nth)
    theta = np.arccos(x)
    phi = 2*PI*(np.arange(Nph)+0.5)/Nph
    dphi = 2*PI/Nph
    th, ph = np.meshgrid(theta, phi, indexing='ij')
    w = wx[:,None] * dphi * np.ones((1,Nph))
    return th.ravel(), ph.ravel(), w.ravel()

th, ph, w = quad_sphere(100, 200)
xq = np.stack([np.sin(th)*np.cos(ph), np.sin(th)*np.sin(ph), np.cos(th)], -1)

SPECTRUM = [0, 6, 10, 12, 16, 18, 20, 22, 24, 26, 28]
basis_raw = np.stack([eval_legendre(l, xq @ V12.T).sum(axis=1) for l in SPECTRUM], axis=0)
norms_sq = np.einsum('ip,p->i', basis_raw**2, w)
U = basis_raw / np.sqrt(norms_sq)[:,None]

def op_mat(V_vals):
    UV = U * V_vals
    return np.einsum('ip,jp,p->ij', U, UV, w)

def d_to_nearest(x, pts):
    return np.min(np.arccos(np.clip(x @ pts.T, -1, 1)), axis=1)

dE = d_to_nearest(xq, E30)
dV = d_to_nearest(xq, V12)
print(f"dE range: [{dE.min():.4f}, {dE.max():.4f}]")

def V_alpha(d, alpha, N, decay=2.0):
    s = np.zeros_like(d)
    for n in range(N):
        s += (decay**(-n)) * np.cos(PI*(alpha**n)*d)
    return s

# Q1: vary N_terms for alpha=2 (best case)
print("\n--- Q1: vary N_terms, alpha=2, edge-midpoint distance ---")
print(f"Target pi/(10*2) = {PI/20:.8f}")
target = PI/20
for N in [2,4,6,8,12,16,24,40]:
    M = op_mat(V_alpha(dE, 2.0, N))
    e = np.linalg.eigvalsh(M)
    i = np.argmin(np.abs(e - target))
    print(f"  N={N:>3}: best eig = {e[i]:.8f}  gap = {abs(e[i]-target):.6f}  rel = {abs(e[i]-target)/target*100:5.2f}%")

print("\n--- Q1b: vary decay weight, alpha=2 ---")
for decay in [1.5, 2.0, 3.0, 4.0, np.e, np.pi]:
    M = op_mat(V_alpha(dE, 2.0, 12, decay=decay))
    e = np.linalg.eigvalsh(M)
    i = np.argmin(np.abs(e - target))
    print(f"  decay={decay:.3f}: best eig = {e[i]:.6f}  gap = {abs(e[i]-target):.6f}")

# Q3: ALL eigenvalues across many alpha
print("\n--- Q3: full eigenvalue scan for alpha in [1.3, 3.0] ---")
print("Looking for eigenvalues that track pi/(10 alpha):")
alphas = np.linspace(1.3, 3.0, 18)
print(f"{'alpha':>8} {'pi/(10a)':>10} {'best_eig':>12} {'gap':>10} {'rel%':>8}")
for a in alphas:
    t = PI/(10*a)
    M = op_mat(V_alpha(dE, a, 12))
    e = np.linalg.eigvalsh(M)
    i = np.argmin(np.abs(e - t))
    print(f"{a:8.4f} {t:10.6f} {e[i]:12.6f} {abs(e[i]-t):10.6f} {abs(e[i]-t)/t*100:7.2f}%")

# Q4: control -- the SAME calculation but on a NON-H_3 substrate
# Use the FULL L^2(S^2) low-l space (not just invariant subspace).
print("\n--- Q4: control -- spectrum on FULL l<=20 subspace (NOT H_3-invariant) ---")
print("If C9's match is from H_3 symmetry, removing it should worsen the gap.")
from scipy.special import sph_harm
def build_full_basis_l_max(lmax):
    # All Y_l^m for 0 <= l <= lmax: total (lmax+1)^2 functions.
    U_full = []
    for l in range(lmax+1):
        for m in range(-l, l+1):
            # Real spherical harmonic
            Y = sph_harm(abs(m), l, ph, th)
            if m > 0:   Y = np.sqrt(2)*Y.real
            elif m < 0: Y = np.sqrt(2)*Y.imag
            else:       Y = Y.real
            U_full.append(Y)
    return np.array(U_full)
U_full = build_full_basis_l_max(8)
# Orthonormalize (should already be ON to quadrature precision; just verify)
G_full = np.einsum('ip,jp,p->ij', U_full, U_full, w)
print(f"  Full basis size: {U_full.shape[0]}, |G-I|_inf = {np.max(np.abs(G_full-np.eye(U_full.shape[0]))):.2e}")
# Diagonalize
def op_mat_full(V_vals, U_):
    UV = U_ * V_vals
    return np.einsum('ip,jp,p->ij', U_, UV, w)
for a in [np.sqrt(2), 2.0]:
    t = PI/(10*a)
    M = op_mat_full(V_alpha(dE, a, 12), U_full)
    e = np.linalg.eigvalsh(M)
    i = np.argmin(np.abs(e - t))
    print(f"  alpha={a:.4f}: full-space best eig = {e[i]:.6f}  gap = {abs(e[i]-t):.6f}  rel = {abs(e[i]-t)/t*100:.2f}%")

# Q5: is the small gap just because |min eigenvalue| of V is small and varies smoothly?
# Show the FULL spectrum of V_alpha for several alpha so we can see if there's a NATURAL match.
print("\n--- Q5: full H_3-invariant spectrum of V_alpha(d_E) ---")
for a in [np.sqrt(2), 1.5, 2.0]:
    t = PI/(10*a)
    M = op_mat(V_alpha(dE, a, 12))
    e = np.sort(np.linalg.eigvalsh(M))
    print(f" alpha={a:.4f}: target {t:.4f}; eigs = {np.round(e,5)}")
