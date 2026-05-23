"""
Task 7: Cross-validate the "10" by testing Coxeter groups I_2(8), I_2(10), I_2(12).

I_2(N) = dihedral group of order 2N, acting on S^1 (circle).
   Invariant L^2(S^1)^{I_2(N)} basis: {cos(N k theta) : k >= 0}.
   Laplacian eigenvalues: (N k)^2.

H_alpha on this substrate: same recipe.
   V_alpha(theta) = sum_n 2^(-n) cos(pi alpha^n |theta - theta_0|)
   on the fundamental domain [0, 2pi/N], with theta_0 = 0 (vertex).

Or, more naturally, the icosahedral substrate's "Coxeter number" h=10 should
produce pi/(10 alpha) ONLY if the dihedral I_2(h) substrate also produces
pi/(h alpha).  Let's test.

NOTE: I_2(10) is the symmetry group of the decagon -- this is the DIHEDRAL
version of the "10" in pi/10.  H_3 contains I_2(10) as a parabolic subgroup
(stabilizer of an edge).
"""

import numpy as np
from numpy.polynomial.legendre import leggauss

def test_dihedral(N, alpha_list, K_terms=8, N_basis=30):
    """Test I_2(N) (dihedral order 2N) on S^1.
       Invariant basis under cyclic part: {cos(N k theta)}_{k=0..N_basis-1}.
       (Reflection invariance is automatic for cos basis.)
    """
    print(f"\n========== I_2({N}) (dihedral order {2*N}, Coxeter number h={N}) ==========")
    # Quadrature on [0, 2pi]
    Nq = 2000
    theta = np.linspace(0, 2*np.pi, Nq, endpoint=False)
    dth   = 2*np.pi / Nq

    # I_2(N)-invariant basis: cos(N k theta), k = 0,1,...,N_basis-1
    # Orthogonal with norms pi (k=0: 2pi)
    basis = np.stack([np.cos(N*k*theta) for k in range(N_basis)], axis=0)  # (Nb, Nq)
    norms_sq = (basis**2).sum(axis=1) * dth
    U = basis / np.sqrt(norms_sq[:,None])
    # Sanity
    GG = U @ U.T * dth
    assert np.max(np.abs(GG - np.eye(N_basis))) < 1e-8, np.max(np.abs(GG-np.eye(N_basis)))

    # Laplacian eigenvalues: -d^2/dtheta^2 cos(Nk theta) = (Nk)^2 cos(Nk theta)
    L_U = np.diag([(N*k)**2 for k in range(N_basis)]).astype(float)

    # Distance to nearest "vertex" (k * 2pi/N for k=0..N-1)
    # = min_k |theta - 2 pi k / N| (mod 2pi)
    vertices = 2*np.pi*np.arange(N)/N
    d = np.min(np.abs((theta[:,None] - vertices[None,:] + np.pi) % (2*np.pi) - np.pi), axis=1)

    for alpha in alpha_list:
        target = np.pi / (N * alpha)
        V = np.zeros_like(d)
        for n in range(K_terms):
            V += (2.0**(-n)) * np.cos(np.pi * (alpha**n) * d)
        # Operators in U-basis
        M_V = U * V[None,:]
        M_V = M_V @ U.T * dth     # (Nb, Nb)
        H = L_U + M_V

        e_H = np.linalg.eigvalsh(H)
        e_V = np.linalg.eigvalsh(M_V)
        # Best match
        gH = np.min(np.abs(e_H - target));  iH = np.argmin(np.abs(e_H - target))
        gV = np.min(np.abs(e_V - target));  iV = np.argmin(np.abs(e_V - target))
        print(f" alpha={alpha:.4f}: target pi/({N} alpha)={target:.6f} | "
              f"-Delta+V best eig={e_H[iH]:.6f} gap={gH:.4f} | "
              f"V only best={e_V[iV]:.6f} gap={gV:.4f}")

for N in [8, 10, 12]:
    test_dihedral(N, [np.sqrt(2), 1.5, 2.0, (1+np.sqrt(5))/2, 3.0])

print("\n--- Interpretation ---")
print("If pi/(10 alpha) comes from H_3's h=10, then ONLY I_2(10) should produce pi/(10 alpha),")
print("while I_2(8), I_2(12) should NOT produce pi/(N alpha) for their respective N.")
print("If NONE of them produce pi/(N alpha), the '10' is not coming from Coxeter number h.")
