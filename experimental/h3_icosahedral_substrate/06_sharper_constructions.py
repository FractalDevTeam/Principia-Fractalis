"""
Final attack: try MULTIPLE natural operator constructions on H_3-invariant L^2(S^2),
hunting for any that reproduces pi/(10 alpha).

Constructions:
  C1: M_V on H_3-invariant subspace (mult by V_alpha(d_min))
  C2: -Delta + V (Schrodinger)
  C3: |D_alpha| = sqrt(-Delta) + V_alpha (Dirac-like)
  C4: V_alpha applied to NORMALIZED geodesic d in [0,1] instead of [0, pi]
      (since the framework's V_alpha uses d in [0,1] in the manuscript)
  C5: Convolution kernel V_alpha(d) acting via Funk-Hecke (already done)
  C6: Random unitary conjugation of C1 -- just to confirm it isn't spectral artifact
  C7: SUMMED-over-12-vertex potential, NOT min: V(x) = (1/12) sum_v V_alpha(d(x,v))
  C8: Geodesic to NEAREST face center (20 face centers)
  C9: Geodesic to NEAREST edge midpoint (30 edge midpoints)
  C10: Operator H_alpha = -Delta + V_alpha rescaled so that eigenvalue grows as l(l+1)/(some scale)
"""
import numpy as np
from scipy.special import eval_legendre
from numpy.polynomial.legendre import leggauss
import itertools

PI = np.pi

# ---------- Icosahedron geometry ------------------------------------------
def icosahedron_vertices():
    phi = (1+np.sqrt(5))/2
    V = []
    for s1 in (-1,1):
        for s2 in (-1,1):
            V += [(0,s1,s2*phi),(s1,s2*phi,0),(s1*phi,0,s2)]
    V = np.array(V, float); V /= np.linalg.norm(V[0]); return V

def icosahedron_faces():
    V = icosahedron_vertices()
    # face = triple of vertices forming a small triangle.  Edge length on unit ico:
    edge = np.linalg.norm(V[0]-V[1])
    # Actually we need to find triples whose pairwise distance is the icosahedron edge.
    dists = []
    for i in range(12):
        for j in range(i+1,12):
            dists.append((np.linalg.norm(V[i]-V[j]), i, j))
    edge = sorted(set(round(d[0],8) for d in dists))[1]  # smallest nonzero
    edges = [(i,j) for d,i,j in dists if abs(d-edge)<1e-6]
    faces = []
    for i,j,k in itertools.combinations(range(12),3):
        if (i,j) in [tuple(sorted(e)) for e in edges] or (i,j) in edges or (j,i) in edges:
            pass
        ok = all((tuple(sorted([a,b])) in [tuple(sorted(e)) for e in edges]) for a,b in [(i,j),(i,k),(j,k)])
        if ok:
            faces.append((i,j,k))
    centers = np.array([(V[i]+V[j]+V[k])/3 for i,j,k in faces])
    centers /= np.linalg.norm(centers, axis=1, keepdims=True)
    return centers

def icosahedron_edges():
    V = icosahedron_vertices()
    dists = []
    for i in range(12):
        for j in range(i+1,12):
            dists.append((np.linalg.norm(V[i]-V[j]), i, j))
    edge = sorted(set(round(d[0],8) for d in dists))[1]
    mids = []
    for d,i,j in dists:
        if abs(d-edge)<1e-6:
            m = (V[i]+V[j])/2; mids.append(m/np.linalg.norm(m))
    return np.array(mids)

V12 = icosahedron_vertices()
F20 = icosahedron_faces()
E30 = icosahedron_edges()
print(f"|V12|={len(V12)} |F20|={len(F20)} |E30|={len(E30)}")

def quad_sphere(Nth=80, Nph=160):
    x, wx = leggauss(Nth)
    theta = np.arccos(x)
    phi = 2*PI*(np.arange(Nph)+0.5)/Nph
    dphi = 2*PI/Nph
    th, ph = np.meshgrid(theta, phi, indexing='ij')
    w = wx[:,None] * dphi * np.ones((1,Nph))
    return th.ravel(), ph.ravel(), w.ravel()

th, ph, w = quad_sphere(80,160)
xq = np.stack([np.sin(th)*np.cos(ph), np.sin(th)*np.sin(ph), np.cos(th)], -1)
print(f"Quad: {len(th)} pts, sum w = {w.sum():.6f}")

# ---------- H_3-invariant orthonormal basis -------------------------------
SPECTRUM = [0, 6, 10, 12, 16, 18, 20, 22, 24, 26, 28]
def zonal_sum(x, l, P):
    return eval_legendre(l, x @ P.T).sum(axis=1)

basis_raw = np.stack([zonal_sum(xq, l, V12) for l in SPECTRUM], axis=0)
# orthonormalize (already orthogonal across l)
norms_sq = np.einsum('ip,p->i', basis_raw**2, w)
U = basis_raw / np.sqrt(norms_sq)[:,None]
# sanity
print(f"|U U^T - I|_inf = {np.max(np.abs(np.einsum('ip,jp,p->ij',U,U,w)-np.eye(len(SPECTRUM)))):.2e}")

L_U = np.diag([float(l*(l+1)) for l in SPECTRUM])

def d_to_nearest(x, pts):
    cs = np.clip(x @ pts.T, -1, 1)
    return np.min(np.arccos(cs), axis=1)

def d_sum_to(x, pts, alpha, N=8):
    """sum_v V_alpha(d(x,v))/|pts|"""
    s = np.zeros(x.shape[0])
    for v in pts:
        d = np.arccos(np.clip(x @ v, -1, 1))
        for n in range(N):
            s += (2.0**(-n))*np.cos(PI*(alpha**n)*d)
    return s/len(pts)

def V_alpha(d, alpha, N=8):
    s = np.zeros_like(d)
    for n in range(N):
        s += (2.0**(-n))*np.cos(PI*(alpha**n)*d)
    return s

def op_mat(V_vals):
    UV = U * V_vals
    return np.einsum('ip,jp,p->ij', U, UV, w)

dV = d_to_nearest(xq, V12)
dF = d_to_nearest(xq, F20)
dE = d_to_nearest(xq, E30)

def evaluate(alpha, name):
    target = PI/(10*alpha)
    print(f"\n========== alpha = {alpha:.6f} ({name})  target = {target:.6f} ==========")

    cases = [
        ("C1 V_alpha(d_min^vertex)",          op_mat(V_alpha(dV, alpha))),
        ("C2 -Delta + V_alpha(d_vertex)",     L_U + op_mat(V_alpha(dV, alpha))),
        ("C4 V_alpha(d_vertex / pi)",         op_mat(V_alpha(dV/PI, alpha))),  # normalized d in [0,1]
        ("C7 sum_v V_alpha(d(x,v))/12",       op_mat(d_sum_to(xq, V12, alpha))),
        ("C8 V_alpha(d_min^face)",            op_mat(V_alpha(dF, alpha))),
        ("C9 V_alpha(d_min^edge)",            op_mat(V_alpha(dE, alpha))),
        ("C10 V_alpha(2*d_vertex)",           op_mat(V_alpha(2*dV, alpha))),
    ]
    print(f"{'Construction':<35} {'best eig':>12} {'gap':>10} {'rel gap':>10}")
    for name_c, M in cases:
        e = np.linalg.eigvalsh(M)
        i = np.argmin(np.abs(e - target))
        gap = abs(e[i] - target)
        print(f"{name_c:<35} {e[i]:>12.6f} {gap:>10.6f} {gap/target*100:>9.2f}%")
    # Show all eigenvalues for the best one (C1)
    e = np.linalg.eigvalsh(cases[0][1])
    print(f"\nFull spectrum C1 (V_alpha on H_3-inv 11D subspace): {np.round(e, 6)}")

for alpha, name in [(np.sqrt(2),'sqrt(2)'), (1.5,'3/2'), (2.0,'2'), ((1+np.sqrt(5))/2,'phi'), (3.0,'3')]:
    evaluate(alpha, name)
