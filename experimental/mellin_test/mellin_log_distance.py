"""
Mellin Log-Distance Spectrum
============================

Confirmed by diagnose script: when V_alpha acts via |u-v| in log-coords
(i.e., as a translation-invariant convolution), the spectrum is geometric
with ratio alpha (between every second eigenvalue) -- eigenvalues come in
parity-paired doublets.

This script:
  1. Resolves the doublet structure (is it exactly degenerate or split?).
  2. Identifies the leading constant C in lambda_k = C * alpha^(-k).
  3. Tests if C depends on the cutoff U (the log-domain half-width).
  4. Compares C to candidate analytic forms:
        - 2U      (= 20 for U=10) -- the integral of the kernel times something
        - U       (= 10)
        - a/(a-1) * 2U = 2*2U = 40 for a=2
        - pi/(10 alpha) and other framework constants
  5. Computes the Fourier symbol m(xi) of K(u) = sum_n a^(-n) cos(pi alpha^n |u|)
     on the discrete grid and matches its top values to the measured eigenvalues.

This will tell us whether the framework's conjectured lambda_0 = pi/(10 alpha)
matches any natural Mellin-route quantity.
"""
import numpy as np

np.set_printoptions(precision=12, suppress=False, linewidth=160)


def V_kernel_of_d(d, alpha, a=2.0, n_max=60):
    d = np.asarray(d, dtype=np.float64)
    n = np.arange(n_max + 1, dtype=np.float64)
    decay = a ** (-n)
    phase = np.pi * (alpha ** n)
    arg = np.multiply.outer(d, phase)
    return np.sum(decay * np.cos(arg), axis=-1)


def build_T_logdist(alpha, U=10.0, N=2000, a=2.0, n_max=60):
    u = np.linspace(-U, U, N, dtype=np.float64)
    h = u[1] - u[0]
    D = np.abs(u[:, None] - u[None, :])
    K = V_kernel_of_d(D, alpha, a=a, n_max=n_max)
    H_sym = h * K
    return u, H_sym, K


def fourier_symbol(alpha, xi_grid, a=2.0, n_max=60):
    """
    Continuous Fourier transform of K(u) = sum_{n>=0} a^(-n) cos(pi alpha^n |u|).
    On R, the cos(pi alpha^n |u|) is not in L^1; we use its 'symbol' as a
    distribution: F[cos(omega|u|)](xi) = 2 omega / (omega^2 - xi^2) in
    principal-value sense (this is the Hilbert-transform / Fourier integral
    of |u| cos).
    Actually for cos(omega u) on R (without |u|), F = pi[delta(xi-omega)+delta(xi+omega)].
    But cos(omega|u|) is the same as cos(omega u) since cos is even -- so
    F[cos(omega|u|)] = pi*[delta(xi-omega) + delta(xi+omega)] in the
    distribution sense.

    On a finite interval [-U, U] this distribution is replaced by a finite
    Fourier integral:
        m_U(xi) = int_{-U}^{U} cos(omega u) e^{-i xi u} du
                = 2 * sin((omega-xi)U) / (omega-xi) + 2*sin((omega+xi)U)/(omega+xi).
    Combining over n:
        m_U(xi) = sum_{n>=0} a^(-n) * [
              sin((pi alpha^n - xi) U) / (pi alpha^n - xi)
            + sin((pi alpha^n + xi) U) / (pi alpha^n + xi)
          ]
    Returns this for each xi in xi_grid.
    """
    n = np.arange(n_max + 1, dtype=np.float64)
    decay = a ** (-n)
    omegas = np.pi * (alpha ** n)
    # xi_grid: shape (M,)
    out = np.zeros_like(xi_grid, dtype=np.float64)
    for j in range(len(xi_grid)):
        xi = xi_grid[j]
        terms = np.zeros_like(omegas)
        for k in range(len(omegas)):
            om = omegas[k]
            # safe sin(x)/x
            def sinc_pi(z, U):
                if abs(z) < 1e-12:
                    return U
                return np.sin(z * U) / z
            t1 = sinc_pi(om - xi, 10.0)  # U=10; pass below if needed
            t2 = sinc_pi(om + xi, 10.0)
            terms[k] = t1 + t2
        out[j] = np.sum(decay * terms)
    return out


def main():
    print("MELLIN LOG-DISTANCE: doublet structure and constant C analysis")
    print()
    U = 10.0
    N = 3000     # higher res
    a = 2.0
    n_max = 60

    for alpha, label in [(np.sqrt(2.0), "sqrt(2)"), (1.5, "3/2"), (2.0, "2")]:
        print("=" * 80)
        print(f"alpha = {label} ({alpha:.15f}),  a = {a},  U = {U}, N = {N}")
        print("=" * 80)
        u, H, K = build_T_logdist(alpha, U=U, N=N, a=a, n_max=n_max)
        evals = np.linalg.eigvalsh(H)
        order = np.argsort(-np.abs(evals))
        top = evals[order[:30]]
        # Doublet means evals come as pairs of nearly equal magnitudes
        print(f"\nTop 30 eigenvalues (signed, sorted by |lambda|):")
        for i, ev in enumerate(top):
            print(f"  k={i:2d}  lambda = {ev:+.14e}")
        # Pair-collapse: average consecutive pairs to extract single-mode ladder
        # The pairs come from cos / sin parity. Take the larger of each pair.
        # Equivalently, take eigenvalues with k even after sorting.
        ladder = top[::2]  # k=0, 2, 4, ...
        print(f"\nLadder (every other eigenvalue, picking larger of each pair):")
        for i in range(min(12, len(ladder))):
            print(f"  m={i:2d}  L_m = {ladder[i]:+.14e}")
        # Ratios of consecutive ladder rungs -- expect alpha
        print(f"\nLadder ratios L_m / L_{{m+1}}  (expected alpha = {alpha:.10f}):")
        ratios = []
        for i in range(min(10, len(ladder) - 1)):
            r = ladder[i] / ladder[i + 1]
            ratios.append(r)
            print(f"  m={i}: {r:.12f}   diff from alpha = {r - alpha:+.4e}")
        # Leading constant C: ladder[m] = C * alpha^(-m)
        # Use the "median" fit on m=2..8 (avoid boundary)
        L = np.array(ladder[:10])
        ms = np.arange(len(L))
        # log L_m = log C - m log alpha
        valid = L > 0
        ms_v = ms[valid]
        L_v = L[valid]
        A = np.vstack([np.ones_like(ms_v, dtype=float), -ms_v.astype(float)]).T
        sol, *_ = np.linalg.lstsq(A, np.log(L_v), rcond=None)
        logC, log_alpha_fit = sol
        C_fit = np.exp(logC)
        alpha_fit = np.exp(log_alpha_fit)
        print(f"\nBest-fit ladder: L_m = C * alpha_fit^(-m)")
        print(f"  C_fit      = {C_fit:.10f}")
        print(f"  alpha_fit  = {alpha_fit:.10f}  (input alpha = {alpha:.10f})")
        print(f"  C_fit / U  = {C_fit / U:.10f}    (U = {U})")
        print(f"  C_fit / (2U) = {C_fit / (2*U):.10f}")
        print(f"  C_fit * alpha = {C_fit * alpha:.10f}")
        print(f"  Framework target: pi/(10 alpha) = {np.pi/(10*alpha):.10f}")
        print(f"  C_fit * (pi/(10 alpha)) = {C_fit * np.pi/(10*alpha):.10f}")
        # Test: maybe C depends on U
        # Re-run at U/2 to check scaling
        print()

    # Test C as a function of U
    print("=" * 80)
    print("Testing whether C scales linearly with U at alpha=2:")
    print("=" * 80)
    alpha = 2.0
    for Utest in [5.0, 10.0, 15.0, 20.0]:
        u, H, K = build_T_logdist(alpha, U=Utest, N=2000, a=a, n_max=n_max)
        evals = np.linalg.eigvalsh(H)
        order = np.argsort(-np.abs(evals))
        top = evals[order[:6]]
        print(f"  U = {Utest:5.1f}:  top 4 = {top[:4]}")
        # Ladder
        ladder = top[::2]
        if len(ladder) >= 2:
            print(f"    L_0 = {ladder[0]:.10f},  L_0/U = {ladder[0]/Utest:.10f},  ratio L_0/L_1 = {ladder[0]/ladder[1]:.10f}")


if __name__ == "__main__":
    main()
