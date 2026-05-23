"""
Mellin Diagnosis
================

The raw spectrum from mellin_spectrum.py looks identical across alpha
(eigenvalues ~ 20, 6.4, 3.7, 3.0, 1.8, 1.6, ...) AND the geometric ratio
settles at ~1.44 regardless of input alpha. This strongly suggests the
operator T is NOT dilation-covariant on R_+ -- because V_alpha(x,y) depends
on |x-y|, not on x/y.

Check 1: Is the kernel translation-invariant in u = log x?
   K(u,v) = V_alpha(e^u, e^v) = sum_n a^(-n) cos(pi * alpha^n * |e^u - e^v|).
   |e^u - e^v| is NOT a function of (u - v) alone -- it depends on e^max(u,v).
   So K is NOT a convolution kernel in log coords; T is NOT dilation-invariant.

Check 2: What IS the correct Mellin-natural operator?
   Two candidates:
   (A) Replace |x - y| with |log(x/y)| -- pure translation-invariant in log
       coords. Then K(u,v) = sum_n a^(-n) cos(pi alpha^n |u-v|), a convolution
       kernel whose spectrum is its Fourier transform.
   (B) Replace |x - y| with |x/y - 1| or |1 - y/x| -- multiplicatively
       homogeneous of degree 0.

The framework's manuscript kernel uses Euclidean |x - y|, so it's NOT
dilation-natural. The Mellin route, as stated, doesn't apply directly to
this kernel.

But: maybe the framework's claim is that AFTER restricting to a fractal
substrate (Cantor set, self-similar), the operator DOES inherit a discrete
dilation symmetry that produces a geometric spectrum.

This script:
  1. Confirms K(u,v) is not a function of (u-v) for the original kernel.
  2. Builds the modified kernel K_log(u,v) = V_alpha at distance |u-v|
     (the "log-distance" variant) and tests its spectrum.
  3. Builds the "log-ratio" kernel K_ratio(x,y) = V_alpha at |log x - log y|.
  4. Reports spectra for both, at alpha = sqrt(2), 3/2, 2.

If variant (A) gives a geometric spectrum with ratio alpha, then the
manuscript's V_alpha has the wrong functional form -- it should use log
distance, not Euclidean distance, for the Mellin interpretation to work.
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


def build_T_with_metric(alpha, metric, U=10.0, N=2000, a=2.0, n_max=60):
    """
    metric in {'euclidean', 'log-distance'}
    'euclidean':   d = |e^u - e^v|     (the manuscript kernel in log coords)
    'log-distance': d = |u - v|         (the convolution / Mellin-natural variant)
    """
    u = np.linspace(-U, U, N, dtype=np.float64)
    h = u[1] - u[0]
    if metric == "euclidean":
        x = np.exp(u)
        D = np.abs(x[:, None] - x[None, :])
    elif metric == "log-distance":
        D = np.abs(u[:, None] - u[None, :])
    else:
        raise ValueError(metric)
    K = V_kernel_of_d(D, alpha, a=a, n_max=n_max)
    H_sym = h * K
    return u, H_sym


def show_top(evals, k=20, label=""):
    print(f"  Top |lambda|, {label}:")
    order = np.argsort(-np.abs(evals))
    for i, idx in enumerate(order[:k]):
        print(f"    k={i:2d}  lambda = {evals[idx]:+.12e}")
    # ratios on positives
    pos = sorted([e for e in evals if e > 0], reverse=True)
    if len(pos) >= 6:
        print(f"  Ratios of positive eigenvalues:")
        for i in range(min(8, len(pos) - 1)):
            r = pos[i] / pos[i + 1]
            print(f"    k={i}: {r:.10f}")


def main():
    U = 10.0
    N = 1500     # slightly smaller for speed; we run more cases
    a = 2.0
    n_max = 60

    for metric in ["euclidean", "log-distance"]:
        print()
        print("#" * 80)
        print(f"# METRIC = {metric}")
        print("#" * 80)
        for alpha, label in [(np.sqrt(2.0), "sqrt(2)"), (1.5, "3/2"), (2.0, "2")]:
            print(f"\n--- alpha = {label} ({alpha:.10f}),  metric = {metric} ---")
            u, H = build_T_with_metric(alpha, metric, U=U, N=N, a=a, n_max=n_max)
            evals = np.linalg.eigvalsh(H)
            show_top(evals, k=15, label=f"alpha={label}, {metric}")
            # If log-distance: T is a true convolution. Eigenfunctions are
            # plane waves e^{i xi u}; eigenvalues are F[K](xi) for various xi.
            # Largest |lambda| corresponds to xi where Fourier transform is
            # maximal in absolute value. Sum_n a^(-n) cos(pi alpha^n |u|)
            # has Fourier transform = sum_n a^(-n) * [delta(xi - pi alpha^n)
            # + delta(xi + pi alpha^n)] -- but in continuous sense, it's
            # NOT in L^1; in finite-grid discretization the eigenvalues are
            # the discrete Fourier transform values on the periodized grid.
            if metric == "log-distance":
                # Compute the symbol m(xi) = integral K(u) e^{-i xi u} du, but K
                # is a sum of cosines so it's a "comb" -- not quite an L^1
                # function. On a finite grid we have a tractable approximation:
                # the kernel matrix is circulant (translation-invariant), so
                # eigenvalues are FFT(first row) values.
                first_row = H[N // 2, :]  # T's matrix is translation-invariant
                fft_vals = np.fft.fft(first_row).real  # symmetric kernel => real
                top_fft = np.sort(np.abs(fft_vals))[::-1][:15]
                print(f"  FFT magnitudes of kernel symbol (top 15): {top_fft}")


if __name__ == "__main__":
    main()
