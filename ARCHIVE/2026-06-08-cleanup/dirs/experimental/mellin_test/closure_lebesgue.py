"""
Closure Check: L^2(R_+, dx) -- regular Lebesgue measure on R_+
==============================================================

For completeness: does the framework's conjecture lambda_0 = pi/(10 alpha)
hold for the Euclidean kernel on the standard half-line with Lebesgue
measure? This is the most "natural" half-line Hilbert space (not the
Mellin one).

We discretize on a log-uniform grid x_i = exp(u_i) but with Lebesgue
quadrature weight x_i * h (since dx = x * du).

The integral operator is
    (H_alpha f)(x) = int_0^inf V_alpha(x, y) f(y) dy
and the L^2(R_+, dx) inner product is int_0^inf f g dx.
Discretized: H_sym[i,j] = sqrt(w_i) V(x_i,x_j) sqrt(w_j) where w_i = x_i * h.

Report top 20 eigenvalues at alpha = sqrt(2), 3/2, 2.
"""
import numpy as np

np.set_printoptions(precision=12, suppress=False, linewidth=160)


def V_kernel(d, alpha, a=2.0, n_max=60):
    d = np.asarray(d, dtype=np.float64)
    n = np.arange(n_max + 1, dtype=np.float64)
    decay = a ** (-n)
    phase = np.pi * (alpha ** n)
    arg = np.multiply.outer(d, phase)
    return np.sum(decay * np.cos(arg), axis=-1)


def build_lebesgue(alpha, U=10.0, N=2000, a=2.0, n_max=60):
    u = np.linspace(-U, U, N, dtype=np.float64)
    h = u[1] - u[0]
    x = np.exp(u)
    D = np.abs(x[:, None] - x[None, :])
    K = V_kernel(D, alpha, a=a, n_max=n_max)
    w = x * h
    sw = np.sqrt(w)
    H_sym = (sw[:, None] * K) * sw[None, :]
    return u, H_sym


def main():
    print("CLOSURE: L^2(R_+, dx) with Euclidean kernel V_alpha(|x-y|)")
    print()
    for alpha, label in [(np.sqrt(2.0), "sqrt(2)"), (1.5, "3/2"), (2.0, "2")]:
        u, H = build_lebesgue(alpha, U=10.0, N=2000, a=2.0, n_max=60)
        evals = np.linalg.eigvalsh(H)
        order = np.argsort(-np.abs(evals))
        top = evals[order[:20]]
        print(f"alpha = {label}  ({alpha:.6f})")
        target = np.pi / (10 * alpha)
        print(f"  target pi/(10 alpha) = {target:.10f}")
        print(f"  top 20 by |lambda|:")
        for i, ev in enumerate(top):
            print(f"    k={i:2d}  lambda = {ev:+.10e}")
        # Is target anywhere in the spectrum?
        diffs = np.abs(evals - target)
        idx = np.argmin(diffs)
        print(f"  closest spectral value to target: lambda = {evals[idx]:.10f}  (diff = {evals[idx]-target:+.4e})")
        print()


if __name__ == "__main__":
    main()
