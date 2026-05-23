"""
Test 1: SO(5) Laplacian on S^4 perturbed by V_alpha(geodesic distance).

S^4 = SO(5)/SO(4), Laplace-Beltrami eigenvalues l(l+3).
First non-zero eigenvalue at l=1: lambda_1 = 4.

We test: does perturbation by V_alpha produce a ground state involving pi/10?

Strategy:
- Spherical harmonics Y_l^m on S^4 (dimension d_l = (l+1)(l+2)(2l+3)/6 — Gegenbauer C^(3/2))
- Compute matrix elements <Y_l|V_alpha|Y_l'> where V_alpha(theta) = some fractal-resonance kernel
   with theta = geodesic distance on S^4 (theta in [0, pi])
- Diagonalize H_alpha = Laplacian + V_alpha truncated to l <= L_max
- Compare lowest eigenvalue (above 0) to pi/(10*alpha)
"""

import numpy as np
from mpmath import mp, mpf, pi, sqrt, cos, sin, quad
from scipy.special import gegenbauer
from scipy.linalg import eigh

mp.dps = 50

def V_alpha(theta, alpha):
    """Fractal-resonance kernel on geodesic distance theta in [0, pi].
    Model: V(theta) = cos(pi * theta / alpha) / alpha  (analogue of polylog series)
    """
    return float(np.cos(float(pi) * theta / alpha) / alpha)

def spherical_harmonic_norm_S4(l):
    """Dimension of degree-l harmonics on S^4."""
    return (l + 1) * (l + 2) * (2 * l + 3) // 6

def matrix_element_S4(l1, l2, alpha, n_quad=200):
    """
    Matrix element of V_alpha between zonal spherical harmonics of degree l1, l2 on S^4.
    Zonal harmonic of degree l on S^4 is proportional to Gegenbauer C_l^(3/2)(cos theta).
    Measure on S^4 (radial): sin^3(theta) d theta (omitting S^3 angular factor — constant).

    <l1|V|l2> = integral_0^pi C_{l1}^(3/2)(cos theta) C_{l2}^(3/2)(cos theta) V(theta) sin^3(theta) d theta
                / sqrt(N_l1 * N_l2)
    where N_l = integral C_l^(3/2)(cos theta)^2 sin^3(theta) d theta.
    """
    # Numerical quadrature
    thetas = np.linspace(1e-8, np.pi - 1e-8, n_quad)
    dtheta = thetas[1] - thetas[0]
    x = np.cos(thetas)
    w = np.sin(thetas) ** 3
    Cl1 = gegenbauer(l1, 1.5)(x)
    Cl2 = gegenbauer(l2, 1.5)(x)
    V = np.array([V_alpha(t, alpha) for t in thetas])
    integrand = Cl1 * Cl2 * V * w
    val = np.trapz(integrand, dx=dtheta)
    # Norms
    N1 = np.trapz(Cl1 ** 2 * w, dx=dtheta)
    N2 = np.trapz(Cl2 ** 2 * w, dx=dtheta)
    return val / np.sqrt(N1 * N2)

def lowest_perturbed_eigenvalue(alpha, L_max=10):
    """Build truncated H_alpha = diag(l(l+3)) + V_matrix and return lowest eigenvalue above tiny threshold."""
    L = L_max + 1
    H = np.zeros((L, L))
    for l1 in range(L):
        for l2 in range(L):
            if l1 == l2:
                H[l1, l2] = l1 * (l1 + 3)  # Laplacian eigenvalue
            H[l1, l2] += matrix_element_S4(l1, l2, alpha, n_quad=400)
    eigs = np.sort(eigh(H, eigvals_only=True))
    return eigs

def main():
    print("=" * 70)
    print("TEST 1: SO(5) Laplacian on S^4 perturbed by V_alpha")
    print("=" * 70)
    print(f"{'alpha':>10} {'lambda_0':>15} {'lambda_1':>15} {'pi/(10*alpha)':>18} {'ratio':>10}")
    print("-" * 70)
    for alpha in [np.sqrt(2), 1.5, 2.0, np.sqrt(3), 3.0]:
        eigs = lowest_perturbed_eigenvalue(alpha, L_max=12)
        # The Laplacian zero-mode (l=0) gets shifted but stays lowest; we report it and the next.
        target = float(pi) / (10 * alpha)
        ratio = eigs[0] / target if abs(target) > 1e-12 else float("nan")
        print(f"{alpha:>10.5f} {eigs[0]:>15.6f} {eigs[1]:>15.6f} {target:>18.6f} {ratio:>10.4f}")
    print()
    print("VERDICT: If pi/(10 alpha) corresponds to lambda_0 or lambda_1 across all alpha,")
    print("the ratio column should be ~ 1.000.")

if __name__ == "__main__":
    main()
