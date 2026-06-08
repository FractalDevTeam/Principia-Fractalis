"""
Mellin-Natural Spectrum Test for H_alpha
=========================================

CRITICAL TEST: does H_alpha on L^2(R_+, dx/x) have spectrum {C * alpha^(-k)}_k
for some natural constant C (ideally C = pi/10)?

Operator:
    (H_alpha f)(x) = integral_0^inf V_alpha(x,y) f(y) dy/y
where
    V_alpha(x,y) = sum_{n>=0} a^(-n) cos(pi * alpha^n * |x-y|)

In log coordinates u = log x, dx/x = du:
    f-tilde(u) = f(e^u)
    K(u,v) = V_alpha(e^u, e^v)
    (T f-tilde)(u) = integral_R K(u,v) f-tilde(v) dv
T is the Mellin-natural transcription. Discretize on a uniform log-grid
u in [-U, U] with N points; spacing h = 2U/(N-1).

Symmetric discretization with quadrature weights w_i = h:
    H_sym[i,j] = sqrt(w_i) * K(u_i,u_j) * sqrt(w_j) = h * K(u_i,u_j)

Eigenvalues of H_sym approximate eigenvalues of T.

Reports:
  - top 20 eigenvalues by absolute value
  - check geometric ratios lambda_k / lambda_{k+1} =? alpha
  - check C * alpha^(-k) fit
  - lambda_0 at alpha in {sqrt(2), 3/2, 2} vs predictions pi/(10*alpha)
"""
import numpy as np
import sys

np.set_printoptions(precision=12, suppress=False, linewidth=160)


def V_kernel(d, alpha, a=2.0, n_max=60):
    """
    V_alpha as a function of d = |x - y|.
    Vectorized: d is a numpy array of arbitrary shape.
    """
    d = np.asarray(d, dtype=np.float64)
    n = np.arange(n_max + 1, dtype=np.float64)
    decay = a ** (-n)           # (n_max+1,)
    phase = np.pi * (alpha ** n)  # (n_max+1,)
    # arg shape: d.shape + (n_max+1,)
    arg = np.multiply.outer(d, phase)
    return np.sum(decay * np.cos(arg), axis=-1)


def build_T_log_grid(alpha, U=10.0, N=2000, a=2.0, n_max=120):
    """
    Build the symmetric discretization H_sym of T on the log-grid.
    Returns (u_grid, H_sym).
    """
    u = np.linspace(-U, U, N, dtype=np.float64)
    h = u[1] - u[0]
    x = np.exp(u)
    # Pairwise |x_i - x_j|. For large U this can be huge; that's fine,
    # the cos oscillates and the geometric decay in a^(-n) keeps it bounded.
    Xi = x[:, None]
    Xj = x[None, :]
    D = np.abs(Xi - Xj)
    # Need n_max large enough that a^(-n_max) << 1; n_max=120 -> 2^(-120) ~ 7.5e-37
    # but the cos argument pi * alpha^n * D can hit huge values.
    # For alpha=sqrt(2) and D up to 2*e^10 ~ 4.4e4, alpha^120 ~ 1.3e18, so arg ~ 1.8e23.
    # cos of that is meaningless in float64. We need to be careful: the kernel
    # is only well-defined as a tempered series, so truncate at modest n_max.
    # The series is geometric; for our spectral test, n_max=60 is the canonical choice.
    K = V_kernel(D, alpha, a=a, n_max=n_max)
    # Symmetric quadrature weight w_i = h (trapezoidal interior; endpoints get h/2,
    # but at U=10 the integrand effectively vanishes so this is negligible).
    H_sym = h * K
    return u, H_sym


def top_eigs(H, k=30):
    """
    Symmetric eigendecomposition; return top-k eigenvalues by abs value.
    """
    # H may be huge -- use eigvalsh for speed if we only need values
    evals = np.linalg.eigvalsh(H)
    # Sort by absolute value, descending
    order = np.argsort(-np.abs(evals))
    return evals[order[:k]]


def analyze_geometric(evals, alpha, label=""):
    """
    Check if eigenvalues follow lambda_k = C * alpha^(-k).
    Reports ratios and best-fit C.
    """
    print(f"\n--- Geometric structure check ({label}) ---")
    print(f"alpha = {alpha:.15f}")
    print(f"Top eigenvalues (signed, sorted by |lambda|):")
    for i, ev in enumerate(evals[:20]):
        print(f"  k={i:2d}  lambda = {ev:+.15e}")
    # Ratios
    print(f"\nRatios lambda_k / lambda_{{k+1}} (should be alpha={alpha:.6f} if geometric):")
    pos = np.array([e for e in evals if e > 0])[:15]
    for i in range(min(10, len(pos) - 1)):
        r = pos[i] / pos[i + 1]
        print(f"  k={i}: ratio = {r:.10f}   (alpha = {alpha:.10f},  diff = {r-alpha:+.3e})")
    # Best-fit C assuming lambda_k = C * alpha^(-k)
    if len(pos) >= 3:
        ks = np.arange(len(pos))
        # log lambda_k = log C - k log alpha; least-squares
        logL = np.log(pos)
        # Solve [1 -k] [logC; log alpha_fit]
        A = np.vstack([np.ones_like(ks), -ks.astype(float)]).T
        sol, *_ = np.linalg.lstsq(A, logL, rcond=None)
        logC_fit, log_alpha_fit = sol
        C_fit = np.exp(logC_fit)
        alpha_fit = np.exp(log_alpha_fit)
        print(f"\nLeast-squares fit  lambda_k = C * (alpha_fit)^(-k):")
        print(f"  C_fit       = {C_fit:.10f}")
        print(f"  alpha_fit   = {alpha_fit:.10f}   (input alpha = {alpha:.10f})")
        print(f"  pi/10       = {np.pi/10:.10f}")
        print(f"  C_fit / (pi/10) = {C_fit / (np.pi/10):.10f}")
        print(f"  C_fit * 10 / pi = {C_fit * 10 / np.pi:.10f}")


def predicted_lambda0(alpha):
    return np.pi / (10.0 * alpha)


def run_single_alpha(alpha, alpha_label, U=10.0, N=2000, a=2.0, n_max=60):
    print("=" * 80)
    print(f"ALPHA = {alpha_label}  ({alpha:.15f})")
    print(f"Grid: u in [-{U}, {U}], N = {N},  a = {a},  n_max = {n_max}")
    print(f"Predicted lambda_0 = pi/(10*alpha) = {predicted_lambda0(alpha):.15f}")
    print("=" * 80)
    u, H = build_T_log_grid(alpha, U=U, N=N, a=a, n_max=n_max)
    evals = top_eigs(H, k=30)
    analyze_geometric(evals, alpha, label=alpha_label)
    # Check the largest positive eigenvalue against pi/(10*alpha)
    pos = sorted([e for e in evals if e > 0], reverse=True)
    if pos:
        lam0 = pos[0]
        target = predicted_lambda0(alpha)
        print(f"\nLAMBDA_0 check at alpha = {alpha_label}:")
        print(f"  largest positive eigenvalue:  {lam0:.15f}")
        print(f"  target pi/(10*alpha):         {target:.15f}")
        print(f"  ratio (lambda_0 / target):    {lam0/target:.10f}")
        print(f"  absolute diff:                {lam0 - target:+.6e}")
    return evals


def main():
    print("MELLIN-NATURAL SPECTRUM TEST FOR H_alpha")
    print("Hilbert space: L^2(R_+, dx/x)")
    print()
    # Resolution: 2000 points is at the edge of dense diag tractability
    # (matrix is 2000x2000, ~32 MB; eigvalsh ~ a few seconds).
    U = 10.0
    N = 2000
    a = 2.0
    n_max = 60

    results = {}
    for alpha, label in [
        (np.sqrt(2.0), "sqrt(2)"),
        (1.5, "3/2"),
        (2.0, "2"),
    ]:
        evals = run_single_alpha(alpha, label, U=U, N=N, a=a, n_max=n_max)
        results[label] = evals
        print()

    # Joint summary
    print("=" * 80)
    print("JOINT SUMMARY: Mellin-conjecture lambda_0 vs measured")
    print("=" * 80)
    print(f"{'alpha':>10s}  {'predicted pi/(10a)':>22s}  {'measured lambda_0':>22s}  {'ratio':>12s}")
    for alpha, label in [(np.sqrt(2.0), "sqrt(2)"), (1.5, "3/2"), (2.0, "2")]:
        evals = results[label]
        pos = sorted([e for e in evals if e > 0], reverse=True)
        lam0 = pos[0] if pos else float("nan")
        target = predicted_lambda0(alpha)
        ratio = lam0 / target if target else float("nan")
        print(f"  {label:>8s}  {target:22.15f}  {lam0:22.15f}  {ratio:12.6f}")


if __name__ == "__main__":
    main()
