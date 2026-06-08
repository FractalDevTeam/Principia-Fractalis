"""
TEST 4: Truncated adele scaling operator.

The adele class space A_Q / Q* is the natural Hilbert-space habitat of Connes's
RH spectral interpretation. A FULL simulation is research-grade NCG.

We use a TRACTABLE SIMPLIFICATION: a scaling operator on a fundamental domain
of the real adele factor (R^*), discretized via Mellin modes, with INSERTED
p-adic Euler factors at p = 2, 3 (mimicking the restricted product).

Concrete construction:
  - Mellin orthonormal modes on (0, inf) with measure dx/x:
        e_n(x) = (1/sqrt(2*pi)) * x^{i*n*tau}  for tau = pi/L (lattice scale)
  - Scaling-by-lambda operator: (U_lambda f)(x) = lambda^{1/2} * f(lambda*x)
  - Action on modes:  U_lambda e_n = lambda^{1/2 + i*n*tau} * e_n
    -> eigenvalues are diagonal: lambda^{1/2 + i*n*tau}
  - At p-adic places, the standard local zeta factor is 1/(1 - p^{-s}) for the
    Schwartz-Bruhat characteristic function. Inserting this Euler product gives
    the "completed" Mellin-zeta intertwiner.

The CONNES RH operator construction (via Riemann-Weil explicit formula) gives,
truncated to the p=2,3 places, the "dual basis" operator with matrix elements

    H_jk = delta_{jk} * E_j  +  off-diagonal arithmetic corrections from p=2,3

We compute the spectrum and search for pi/(10*alpha).

This is a HEURISTIC truncation — Connes's full operator is on the noncommutative
adele class space, NOT just truncated Mellin modes. But the truncation is the
honest "first-pass" numerical test the framework should pass.
"""

import mpmath as mp
import numpy as np
mp.mp.dps = 50

PI = mp.pi
TARGET = lambda a: PI / (10 * a)

ALPHAS = {
    "alpha_P=sqrt(2)":     mp.sqrt(2),
    "alpha_NP=phi+1/4":    (1 + mp.sqrt(5))/2 + mp.mpf(1)/4,
    "alpha_Hodge=phi":     (1 + mp.sqrt(5))/2,
    "alpha_NS=3pi/2":      3*PI/2,
    "alpha_YM=2":          mp.mpf(2),
    "alpha_BSD=3pi/4":     3*PI/4,
    "alpha_QG=sqrt(2pi)":  mp.sqrt(2*PI),
}


def truncated_adele_operator(N, L, primes=(2, 3), scaling_log=None):
    """
    Build truncated 'Connes-style' scaling operator.

    N      : number of Mellin modes (2N+1 modes from -N..+N)
    L      : log-cutoff (compact-domain size)
    primes : finite set of p-adic places included
    scaling_log : log(lambda) for the scaling action; if None, generator T = -i*d/dt

    Returns a (2N+1)x(2N+1) Hermitian operator (numpy complex128).
    """
    dim = 2*N + 1
    H = np.zeros((dim, dim), dtype=complex)
    tau = float(mp.pi) / L

    # Diagonal: log-scaling generator eigenvalues are E_n = n*tau (real)
    # Connes's generator is the scaling generator on R^*_+, basically -i*d/d(log x)
    # which has eigenvalues n*tau in the Mellin basis on a compact fundamental domain.
    for j in range(dim):
        n = j - N
        H[j, j] = n * tau

    # Arithmetic correction at each finite prime p: the trace-formula term is
    #     sum_p sum_{m>=1} log(p) * p^{-m/2} * (e_{m log p} + e_{-m log p})
    # which contributes off-diagonal matrix elements coupling modes whose
    # Mellin-energy differs by an arithmetic shift.
    # Concretely we add an off-diagonal kernel
    #     K(t,t') = sum_p sum_m log(p) p^{-m/2} delta(t - t' - m log p)
    # whose Mellin-mode matrix entry (j,k) is
    #     log(p) * p^{-m/2} * exp(i*(n_k - n_j)*tau * m*log(p) * 0)
    # using the discrete delta on the lattice t = j*L/N.
    # We implement a SIMPLIFIED Riemann-Weil arithmetic perturbation:
    #     H_jk += sum_p sum_{m=1..M} log(p)/sqrt(p^m) * cos((n_j - n_k)*tau * m*log(p))
    M = 5
    for p in primes:
        logp = float(mp.log(p))
        for m in range(1, M+1):
            amp = logp / float(mp.sqrt(p**m))
            for j in range(dim):
                for k in range(dim):
                    nj = j - N
                    nk = k - N
                    H[j, k] += amp * np.cos((nj - nk) * tau * m * logp)
    # Hermitian symmetrization (already real-symmetric)
    H = 0.5 * (H + H.conj().T)
    return H


def find_eigenvalues(H):
    eigs = np.linalg.eigvalsh(H)
    return np.sort(eigs)


print("="*78)
print("TEST 4: TRUNCATED 'CONNES-STYLE' ADELE SCALING OPERATOR")
print("(Mellin modes on R^*_+ with Euler-factor perturbations at p=2,3)")
print("="*78)

results = []
for L in [3.0, 5.0, 8.0, 12.0]:
    for N in [10, 20, 30]:
        print(f"\nL = {L}, N = {N} (dim = {2*N+1})")
        H = truncated_adele_operator(N, L, primes=(2, 3))
        eigs = find_eigenvalues(H)
        print(f"  Eigenvalues range: [{eigs[0]:+.6f}, {eigs[-1]:+.6f}]")
        print(f"  First 20 (sorted by |.|): {[f'{e:+.5f}' for e in sorted(eigs, key=lambda x: abs(x))[:20]]}")
        # For each framework alpha test closest eigenvalue to pi/(10*alpha)
        for aname, aval in ALPHAS.items():
            tgt = float(TARGET(aval))
            best = min(eigs, key=lambda e: abs(e - tgt))
            d = abs(best - tgt)
            results.append((aname, L, N, tgt, best, d))
            if d < 1e-3:
                print(f"  *** {aname:24s}  target={tgt:+.6f}  closest={best:+.6f}  d={d:.3e}")

# Best matches over the entire grid
print("\n" + "="*78)
print("TRUNCATED ADELE SUMMARY — best matches over (L, N) grid:")
print("="*78)
# Group by alpha, take best per alpha
by_alpha = {}
for r in results:
    a = r[0]
    if a not in by_alpha or r[5] < by_alpha[a][5]:
        by_alpha[a] = r

print(f"\n{'alpha':30s} {'target':>12s} {'best eig':>14s} {'L':>5s} {'N':>4s} {'dist':>12s}")
print("-"*78)
for a, r in sorted(by_alpha.items(), key=lambda x: x[1][5]):
    print(f"{a:30s} {r[3]:>12.6f} {r[4]:>14.6f} {r[1]:>5.1f} {r[2]:>4d} {r[5]:>12.4e}")

best_overall = min(results, key=lambda r: r[5])
print(f"\nBest overall: {best_overall[0]}, L={best_overall[1]}, N={best_overall[2]}, dist={best_overall[5]:.4e}")
if best_overall[5] < 1e-4:
    print("VERDICT: Sharp coincidence — plausibly resolving.")
elif best_overall[5] < 1e-2:
    print("VERDICT: Mild coincidence. Note: with dense Mellin spectrum on a")
    print("        compact interval, *any* target will have some eigenvalue close")
    print("        to it; need to compare to a NULL distribution.")
else:
    print("VERDICT: No tight match.")

# Null comparison: random targets in the same range
print("\n" + "-"*78)
print("NULL CONTROL: closest eigenvalue distances for RANDOM real targets")
print("(in the operator's spectral range)")
print("-"*78)
H = truncated_adele_operator(20, 8.0, primes=(2, 3))
eigs = find_eigenvalues(H)
spec_range = (eigs[0], eigs[-1])
print(f"  Spectral range: [{spec_range[0]:+.4f}, {spec_range[1]:+.4f}]")
rng = np.random.default_rng(seed=12345)
null_dists = []
for _ in range(1000):
    rt = rng.uniform(spec_range[0], spec_range[1])
    d = min(abs(e - rt) for e in eigs)
    null_dists.append(d)
null_dists = np.array(null_dists)
print(f"  Null distance median: {np.median(null_dists):.4e}")
print(f"  Null distance 5th percentile: {np.percentile(null_dists, 5):.4e}")
print(f"  Null distance 1st percentile: {np.percentile(null_dists, 1):.4e}")

# Compare: best match distance for framework target vs null
for a, r in sorted(by_alpha.items(), key=lambda x: x[1][5]):
    pct = (null_dists < r[5]).mean() * 100
    print(f"  {a:30s} best dist = {r[5]:.4e}  -> {pct:.1f}% of null below it")
print("\n(A 'real' coincidence would be in the bottom 1-5% of the null.)")
