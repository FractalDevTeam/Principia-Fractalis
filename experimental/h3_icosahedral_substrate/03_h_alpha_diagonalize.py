"""
Task 3 & 5: Build H_alpha on H_3-invariant L^2(S^2) and diagonalize.

Constructions tested:
  (A)  H_alpha = -Delta_{S^2} + V_alpha(d_min)  (Schrodinger)
       where V_alpha(d) = sum_{n=0}^{N-1} 2^(-n) cos(pi * alpha^n * d),
       d = arccos(x . v_*) is the geodesic distance to the nearest icosahedral vertex.
  (B)  M_alpha = V_alpha(d_min) as a pure multiplication operator on H_3-invariant L^2(S^2).
  (C)  K_alpha = convolution operator with kernel V_alpha(arccos(x.y))  (zonal kernel).
  (D)  Just -Delta: control -- eigenvalues are l(l+1) for l in the spectrum.

For each, diagonalize in the H_3-invariant subspace spanned by the orthonormalized
zonal basis {psi_l : l in spectrum, l <= L_max}.  Look for any eigenvalue near
pi/(10*alpha) for alpha = sqrt(2), 3/2, 2.
"""

import numpy as np
from scipy.special import eval_legendre
from numpy.polynomial.legendre import leggauss

# ---------- icosahedron + quadrature (reuse from 02) ----------------------
def icosahedron_vertices():
    phi = (1 + np.sqrt(5))/2
    raw = []
    for s1 in (-1,1):
        for s2 in (-1,1):
            raw += [(0,s1,s2*phi),(s1,s2*phi,0),(s1*phi,0,s2)]
    V = np.array(raw, float); V /= np.linalg.norm(V[0]); return V

def quad_sphere(Nth=80, Nph=160):
    x, wx = leggauss(Nth)
    theta = np.arccos(x); sint = np.sqrt(1-x*x)
    phi = 2*np.pi*(np.arange(Nph)+0.5)/Nph
    dphi = 2*np.pi/Nph
    th, ph = np.meshgrid(theta, phi, indexing='ij')
    w = wx[:,None] * dphi * np.ones((1,Nph))
    return th.ravel(), ph.ravel(), w.ravel()

V12 = icosahedron_vertices()
th, ph, w = quad_sphere(80, 160)
xq = np.stack([np.sin(th)*np.cos(ph), np.sin(th)*np.sin(ph), np.cos(th)], -1)
print(f"Quadrature: {len(th)} pts, sum w = {w.sum():.8f} (4pi = {4*np.pi:.8f})")

# ---------- H_3-invariant basis -------------------------------------------
SPECTRUM = [0, 6, 10, 12, 16, 18, 20, 22, 24, 26, 28]  # 11 functions (l<=28)

def zonal_sum(x, l):
    return eval_legendre(l, x @ V12.T).sum(axis=1)

# Build orthonormal basis via Gram-Schmidt on quadrature values
basis_raw = np.stack([zonal_sum(xq, l) for l in SPECTRUM], axis=0)  # (Nb, Np)
# Inner product: integrate against w
def L2inner(f, g):  return (w * f * g).sum()
Nb = len(SPECTRUM)
G = np.zeros((Nb, Nb))
for i in range(Nb):
    for j in range(Nb):
        G[i,j] = L2inner(basis_raw[i], basis_raw[j])
# Eigendecomp G = Q D Q^T, build whitening
evals, evecs = np.linalg.eigh(G)
print(f"\nGram matrix eigenvalues (should all > 0): {evals}")
Whiten = evecs / np.sqrt(np.maximum(evals, 1e-30))
# Orthonormal basis: U[i] = sum_j Whiten[j,i] * basis_raw[j]
U = Whiten.T @ basis_raw      # (Nb, Np), L^2-orthonormal
# Sanity
GG = np.einsum('ip,jp,p->ij', U, U, w)
print(f"|U U^T - I|_inf = {np.max(np.abs(GG - np.eye(Nb))):.3e}")

# Diagonal Laplacian on this basis (it's NOT diagonal in U-basis,
# but it's block-diagonal in psi_l basis since each l is an eigenvalue l(l+1)).
# We need Laplacian as matrix in U-basis: M_L_psi = diag(l(l+1)) in psi-basis,
# then transform.
L_psi = np.diag([l*(l+1) for l in SPECTRUM]).astype(float)
# psi_l = sum_j Whiten[j,i] * basis_raw[j]?  Actually U[i] = sum_j (Whiten.T)[i,j] basis_raw[j]
#       = sum_j Whiten[j,i] basis_raw[j].   So basis_raw[j] = sum_i Whiten^{-T}[j,i] U[i].
# In ORIGINAL psi_l basis, Laplacian is diagonal diag(l(l+1)).
# In U-basis, Laplacian is M_L_U = Whiten.T * G * L_psi_normalized * G * Whiten ...
# Simpler: build Laplacian by direct quadrature using its spectral form.
# Trick: each psi_l is itself an eigenfn of -Delta with eigenvalue l(l+1).
# So in raw basis the Laplacian matrix is L_raw[i,j] = l_i(l_i+1) * G[i,j]
# and in U-basis: L_U = Whiten.T @ L_raw @ Whiten.
L_raw = np.array([[l*(l+1) for l in SPECTRUM]]).T * G  # row i scaled by l_i(l_i+1)?
# Actually <psi_i, -Delta psi_j> = l_j(l_j+1) <psi_i, psi_j> = l_j(l_j+1) G[i,j].
# But the operator is symmetric, so this only works if l_i=l_j, which it does since psi_l are
# orthogonal across different l (different SO(3) irreps).  Confirm:
print("\nOff-diagonal G (cross-l overlap, should be 0):")
G_off = G - np.diag(np.diag(G))
print(f"  |G_off|_inf = {np.max(np.abs(G_off)):.3e}")

# Confirmed orthogonal -- Laplacian in raw basis is just diagonal:
# L_raw[i,j] = delta_ij * l_i(l_i+1) * G[i,i]
L_raw = np.diag([l*(l+1)*G[i,i] for i,l in enumerate(SPECTRUM)])
L_U = Whiten.T @ L_raw @ Whiten
# Should be diagonal with entries l(l+1) since psi_l/sqrt(G_ii) is the orthonormal basis
print("Laplacian in U-basis (should be diag l(l+1)):")
print(np.round(np.diag(L_U), 4))
print("Expected:", [l*(l+1) for l in SPECTRUM])

# ---------- V_alpha(d) potential ------------------------------------------
def V_alpha(d, alpha, N_terms=8):
    """V_alpha(d) = sum_{n=0}^{N-1} 2^(-n) cos(pi * alpha^n * d)."""
    s = np.zeros_like(d)
    for n in range(N_terms):
        s += (2.0**(-n)) * np.cos(np.pi * (alpha**n) * d)
    return s

def d_to_nearest_vertex(x):
    """x shape (Np, 3); returns geodesic distance to nearest of V12."""
    cs = x @ V12.T                  # (Np, 12)
    cs = np.clip(cs, -1.0, 1.0)
    return np.min(np.arccos(cs), axis=1)

dmin = d_to_nearest_vertex(xq)
print(f"\nGeodesic dist range: [{dmin.min():.4f}, {dmin.max():.4f}]")
print(f"  Max possible distance to NEAREST vertex on icosahedron ~ {np.arccos(1/np.sqrt(5))/2:.4f} (half edge)? "
      f"Actually = arccos(circumradius cosine) at face center.")

# ---------- Build operator matrices in U-basis ----------------------------
def operator_matrix(V_vals):
    """For multiplication-by-V operator: M[i,j] = <U_i, V U_j> = sum_p w_p U_i[p] V[p] U_j[p]."""
    UV = U * V_vals                            # (Nb, Np)
    return np.einsum('ip,jp,p->ij', U, UV, w)

# ---------- Diagonalize for several alphas --------------------------------
def report(alpha, name):
    print(f"\n========== alpha = {alpha} ({name}) ==========")
    target = np.pi / (10*alpha)
    print(f"Target lambda_0 = pi/(10*alpha) = {target:.10f}")

    V_vals = V_alpha(dmin, alpha, N_terms=8)
    M_V = operator_matrix(V_vals)
    # Construction (A): H = -Delta + V
    H_A = L_U + M_V
    eA = np.linalg.eigvalsh(H_A)
    # Construction (B): H = V multiplication only
    eB = np.linalg.eigvalsh(M_V)
    # Construction (D): -Delta only (control)
    eD = np.linalg.eigvalsh(L_U)

    def best_match(evals):
        gaps = np.abs(evals - target)
        i = np.argmin(gaps)
        return evals[i], gaps[i]

    print(f"\n(A) -Delta + V_alpha:  eigenvalues = {np.round(eA, 6)}")
    e_best, g_best = best_match(eA)
    print(f"    Best match to target: {e_best:.6f}   gap = {g_best:.6f}   ratio gap/target = {g_best/target:.3f}")

    print(f"(B) V_alpha (mult only): eigenvalues = {np.round(eB, 6)}")
    e_best, g_best = best_match(eB)
    print(f"    Best match to target: {e_best:.6f}   gap = {g_best:.6f}   ratio gap/target = {g_best/target:.3f}")

    print(f"(D) -Delta (control): {np.round(eD,4)}")

report(np.sqrt(2),  "sqrt(2)")
report(1.5,         "3/2")
report(2.0,         "2")
report((1+np.sqrt(5))/2, "phi")
