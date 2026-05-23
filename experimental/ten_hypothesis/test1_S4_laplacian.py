"""
TEST 1: SO(5) Laplacian on S^4 = SO(5)/SO(4)
Hypothesis: H_alpha as perturbation of S^4 Laplacian might produce pi/(10*alpha).

The Laplace-Beltrami operator on S^4 has eigenvalues l(l+3) for l = 0, 1, 2, ...
First nonzero eigenvalue = 4. Dim of l-th harmonic space = (2l+3)(l+2)(l+1)/6.

Strategy: We use the addition formula for ultraspherical (Gegenbauer) polynomials.
On S^n, the zonal kernel for the l-th harmonic is C_l^((n-1)/2)(cos(d)) / dim(H_l).

We test V_alpha(d) = cos(pi*d/alpha) where d is geodesic distance on S^4 (range [0, pi]).
Then look at the leading eigenvalue of: Laplacian + V_alpha.

For perturbation theory at l=1 (deg = 5, eigenvalue 4):
  delta_lambda = <Y_l, V Y_l> averaged over the unit-norm zonal harmonics.

For S^4: zonal harmonic Y_l(x) = C_l^(3/2)(x*p) / C_l^(3/2)(1) where p is north pole.
First-order shift = integral over S^4 of V(d(x,p)) * |Y_1(x)|^2 dvol(x).
"""

from mpmath import mp, mpf, pi, cos, sin, quad, sqrt, exp, log

mp.dps = 50

def gegenbauer(n, alpha_g, x):
    """Compute Gegenbauer polynomial C_n^(alpha)(x) via recursion."""
    if n == 0:
        return mpf(1)
    if n == 1:
        return 2 * alpha_g * x
    C_prev2, C_prev1 = mpf(1), 2 * alpha_g * x
    for k in range(2, n+1):
        C_new = ((2 * (k - 1 + alpha_g) * x * C_prev1) - (k - 2 + 2 * alpha_g) * C_prev2) / k
        C_prev2, C_prev1 = C_prev1, C_new
    return C_prev1

def S4_perturbation_first_eigenvalue(alpha):
    """
    On S^4 the volume element in polar coords (d from north pole) is
      sin^3(d) * vol(S^3) dd, where vol(S^3) = 2*pi^2.
    Total vol(S^4) = 8*pi^2/3.

    Zonal harmonic at level l on S^4 (n=4):  Y_l = C_l^(3/2)(cos d).
    Norm squared = vol(S^4)/dim(H_l).  Dim(H_l) on S^4 = (2l+3)(l+2)(l+1)/6.

    First-order shift at l=1:
      delta = <V>_{Y_1} = (1/||Y_1||^2) * integral V(d) * Y_1(cos d)^2 sin^3(d) dd * vol(S^3)
    """
    # Volume of S^3 = 2 pi^2
    vol_S3 = 2 * pi**2
    vol_S4 = mpf(8) * pi**2 / 3

    # l=1, dim = 5*3*2/6 = 5 (correct: vector rep)
    dim_H1 = mpf(5)
    norm_Y1_sq = vol_S4 / dim_H1

    # V_alpha(d) = cos(pi*d/alpha)
    def integrand(d):
        c = cos(d)
        Y1 = gegenbauer(1, mpf(3)/2, c)  # = 3*cos(d)
        V = cos(pi * d / alpha)
        return V * Y1**2 * sin(d)**3

    integral = quad(integrand, [0, pi])
    delta = (vol_S3 * integral) / norm_Y1_sq

    # Unperturbed eigenvalue at l=1 is 4. With perturbation:
    return 4 + delta, delta

def main():
    print("=" * 70)
    print("TEST 1: S^4 Laplacian perturbed by V_alpha(d) = cos(pi*d/alpha)")
    print("=" * 70)
    print(f"{'alpha':<12} {'lambda_1':<25} {'shift':<25} {'pi/(10*alpha)':<20}")
    print("-" * 80)

    for alpha in [sqrt(mpf(2)), mpf(3)/2, mpf(2), mpf(3), pi/mpf(2), mpf(5), mpf(10)]:
        lam, shift = S4_perturbation_first_eigenvalue(alpha)
        target = pi / (10 * alpha)
        print(f"{float(alpha):<12.6f} {float(lam):<25.15f} {float(shift):<25.15f} {float(target):<20.15f}")

    print()
    print("Analysis: The perturbed eigenvalue is ~4 + O(1), nowhere near pi/(10*alpha) ~ 0.2.")
    print("Even the SHIFT itself doesn't show pi/10 structure across alphas.")
    print()
    print("Verdict: SO(5)/S^4 Laplacian does NOT naturally produce pi/(10*alpha).")
    print("Dim SO(5) = 10 is a NUMERICAL COINCIDENCE here, not a structural source.")

if __name__ == "__main__":
    main()
