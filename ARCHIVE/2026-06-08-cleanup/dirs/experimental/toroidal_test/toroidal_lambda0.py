"""
Toroidal substrate test for the polylog conjecture.

Tests whether
    lambda_0(alpha) = integral over T^2 x T^2 of V_alpha(d(0,y)) dHaar(y)
equals pi/(10*alpha) on the (double) flat torus, with geodesic kernel.

V_alpha(d) = sum_{n=0}^{N-1} a^(-n) cos(pi * alpha^n * d), with a=2, N=20.

Geodesic on T^2 = R/2piZ x R/2piZ:
  d_T^2(0, (theta1,theta2)) = sqrt(g(theta1)^2 + g(theta2)^2)
where g(theta) = min(|theta|, 2pi - |theta|) for theta in [0, 2pi).

For (x,y) in T^2 x T^2, by translation invariance:
  lambda_0 = (2pi)^(-4) * int_{[0,2pi]^4} V_alpha(d(0, (theta1..theta4))) dtheta
where d on the product is sqrt(d_T^2(x)^2 + d_T^2(y)^2)
       = sqrt(g(theta1)^2 + g(theta2)^2 + g(theta3)^2 + g(theta4)^2).

So d ranges over [0, 2*pi] (since each g <= pi and we have 4 of them =>
sqrt(4*pi^2) = 2pi).

Single T^2 version: lambda_0^single = (2pi)^(-2) int_{[0,2pi]^2} V_alpha(sqrt(g(t1)^2 + g(t2)^2)) dt
"""

import numpy as np
from scipy import integrate
import math

PI = math.pi


def g(theta):
    """Folded distance on R/2piZ from 0: returns min(theta mod 2pi, 2pi - theta mod 2pi)."""
    t = theta % (2 * PI)
    return np.minimum(t, 2 * PI - t)


def V_alpha(d, alpha, a=2.0, N=20):
    """Kernel V_alpha(d) = sum_{n=0}^{N-1} a^(-n) cos(pi * alpha^n * d)."""
    total = 0.0
    for n in range(N):
        total += (a ** (-n)) * math.cos(PI * (alpha ** n) * d)
    return total


def V_alpha_vec(d, alpha, a=2.0, N=20):
    """Vectorized over numpy array d."""
    d_arr = np.asarray(d, dtype=float)
    total = np.zeros_like(d_arr)
    for n in range(N):
        total += (a ** (-n)) * np.cos(PI * (alpha ** n) * d_arr)
    return total


# ----- Approach 1: reduce single-T^2 integral to 1D via the radial CDF -----
# By symmetry, on T^2:
#   (1/(2pi)^2) int_{[0,2pi]^2} f(sqrt(g(t1)^2+g(t2)^2)) dt
# = (1/pi^2) int_{[0,pi]^2} f(sqrt(s^2+t^2)) ds dt   (folding g)
# Substitute polar: s = r cos phi, t = r sin phi, with the constraint
# s,t in [0,pi]. So we can do it as a 2D integral on [0,pi]^2.


def lambda0_single_T2(alpha, a=2.0, N=20):
    """Single T^2: (1/(2pi)^2) int_{[0,2pi]^2} V_alpha(sqrt(g(t1)^2+g(t2)^2)) dt1 dt2.
    Equivalent to (1/pi^2) int_{[0,pi]^2} V_alpha(sqrt(s^2+t^2)) ds dt by symmetry."""
    def integrand(s, t):
        d = math.sqrt(s * s + t * t)
        return V_alpha(d, alpha, a, N)
    val, err = integrate.dblquad(
        integrand, 0, PI, 0, PI,
        epsabs=1e-10, epsrel=1e-10
    )
    return val / (PI ** 2), err / (PI ** 2)


def lambda0_double_T2(alpha, a=2.0, N=20):
    """Double T^2 x T^2: integrate over 4 angular variables.

    By symmetry (folding): (1/pi^4) int_{[0,pi]^4} V_alpha(sqrt(s1^2+s2^2+s3^2+s4^2)) ds.

    We use a radial reformulation via the joint density of R = sqrt(sum si^2)
    where each si is uniform on [0,pi].

    Equivalently, compute as iterated 4D quadrature using scipy.integrate.nquad,
    but that's slow. Instead use Monte Carlo cross-check + a smarter approach:

    Method: write V as sum of cos terms, then for each n:
      I_n = (1/pi^4) int cos(pi*alpha^n*sqrt(s1^2+s2^2+s3^2+s4^2)) ds
    Use radial density of R when each s_i ~ Uniform[0,pi].
    """
    # Compute the radial density p(r) numerically by Monte Carlo / convolution.
    # Then I_n = int_0^{2pi} cos(pi*alpha^n*r) p(r) dr.
    # We'll do it more directly: 4D adaptive quadrature is feasible with care.
    #
    # We'll use nquad with moderate precision per term.
    pass  # implemented below differently


def lambda0_double_T2_MC(alpha, a=2.0, N=20, n_samples=10_000_000, seed=42):
    """Monte Carlo estimate of lambda_0 on T^2 x T^2.

    Sample 4 angles uniformly in [0, 2pi)^4. Evaluate V_alpha at the
    product-geodesic distance from origin. Average.
    """
    rng = np.random.default_rng(seed)
    # Sample uniformly on [0, 2pi]
    samples = rng.uniform(0.0, 2 * PI, size=(n_samples, 4))
    g_vals = g(samples)
    d = np.sqrt(np.sum(g_vals ** 2, axis=1))
    V = V_alpha_vec(d, alpha, a, N)
    mean = V.mean()
    sem = V.std(ddof=1) / math.sqrt(n_samples)
    return mean, sem


def lambda0_single_T2_MC(alpha, a=2.0, N=20, n_samples=10_000_000, seed=42):
    """MC for single T^2."""
    rng = np.random.default_rng(seed)
    samples = rng.uniform(0.0, 2 * PI, size=(n_samples, 2))
    g_vals = g(samples)
    d = np.sqrt(np.sum(g_vals ** 2, axis=1))
    V = V_alpha_vec(d, alpha, a, N)
    mean = V.mean()
    sem = V.std(ddof=1) / math.sqrt(n_samples)
    return mean, sem


def lambda0_double_T2_quad(alpha, a=2.0, N=20):
    """Higher-accuracy: split V into terms, reduce each to a 4D integral via
    radial CDF of sum of 4 uniforms-squared.

    Direct 4D nquad is expensive; do it term-by-term with adaptive precision.

    For each term cos(pi*alpha^n*r): integrate over [0,pi]^4 (by symmetry):
       I_n = (1/pi^4) * int_{[0,pi]^4} cos(pi*alpha^n*sqrt(sum s_i^2)) ds
    """
    total = 0.0
    err_total = 0.0
    for n in range(N):
        k = PI * (alpha ** n)
        def integrand(s1, s2, s3, s4, k=k):
            return math.cos(k * math.sqrt(s1*s1 + s2*s2 + s3*s3 + s4*s4))
        # nquad with moderate tolerance
        val, err = integrate.nquad(
            integrand,
            [[0, PI], [0, PI], [0, PI], [0, PI]],
            opts={'epsabs': 1e-6, 'epsrel': 1e-6, 'limit': 50},
        )
        I_n = val / (PI ** 4)
        coef = a ** (-n)
        total += coef * I_n
        err_total += coef * (err / (PI ** 4))
        # Skip remaining if coefficient is tiny
        if coef < 1e-7:
            break
    return total, err_total


def main():
    print("=" * 70)
    print("TOROIDAL SUBSTRATE TEST: lambda_0 on T^2 and T^2 x T^2")
    print("=" * 70)

    cases = [
        ("alpha = sqrt(2)", math.sqrt(2), PI / (10 * math.sqrt(2))),
        ("alpha = 3/2",     1.5,            PI / 15),
        ("alpha = 2",       2.0,            PI / 20),
    ]

    for name, alpha, target in cases:
        print()
        print(f"--- {name}  (target pi/(10*alpha) = {target:.10f}) ---")

        # Single T^2 via deterministic 2D quadrature
        v1, e1 = lambda0_single_T2(alpha, a=2.0, N=20)
        print(f"  Single T^2  (2D quad, N=20):  lambda_0 = {v1:.10f}  (err ~ {e1:.2e})")
        print(f"     distance to target          : {v1 - target:+.10f}  "
              f"(relative {abs(v1-target)/abs(target)*100:.3f}%)")

        # Single T^2 MC for cross-check
        v1_mc, e1_mc = lambda0_single_T2_MC(alpha, a=2.0, N=20, n_samples=5_000_000)
        print(f"  Single T^2  (MC 5e6):         lambda_0 = {v1_mc:.10f}  "
              f"(sem ~ {e1_mc:.2e})")

        # Double T^2 x T^2 via MC (4D nquad is slow for many terms)
        v2_mc, e2_mc = lambda0_double_T2_MC(alpha, a=2.0, N=20, n_samples=20_000_000)
        print(f"  Double T^2xT^2 (MC 2e7):      lambda_0 = {v2_mc:.10f}  "
              f"(sem ~ {e2_mc:.2e})")
        print(f"     distance to target          : {v2_mc - target:+.10f}  "
              f"(relative {abs(v2_mc-target)/abs(target)*100:.3f}%)")


if __name__ == "__main__":
    main()
