"""
R_f-modulated scaling operator at alpha = 2, using framework Mechanism 3.

At alpha = 2: R_f(2, s) = zeta(s) (PROVEN axiom-free in Lean).
So the framework's R_f anchor at alpha=2 IS the Riemann zeta function.

Mechanism 3 modulation: add an off-diagonal / multiplicative perturbation
of strength (ch_2 - 0.95) involving an R_f-derived potential.

We test FOUR potentials:
  V0: bare scaling (control)
  V1: V(x) = eps * (ch_2 - 0.95) * Re[R_f(2, 1 + i*log(x)/L)]
       — uses zeta on the critical line via R_f(2,.) identity
  V2: V(x) = eps * (ch_2 - 0.95) * sum_p (log p / p^{1/2}) * cos(log(p) * log(x))
       — von Mangoldt-prime modulation (injects Euler product structure)
  V3: V(x) = eps * (ch_2 - 0.95) * |zeta(1/2 + i*log(x))|^{-2}
       — Berry-Keating-style 1/|zeta| potential

H = D + diag(V(x_j))

This tests whether the framework's R_f(2,.) = zeta anchor, COMBINED WITH
Mechanism 3 modulation at ch_2 = 0.95, yields a spectrum matching
zeta zeros.

Author: Pablo Cohen + Claude (Wave 11)
Date: 2026-05-23
"""

import numpy as np
import mpmath as mp
import json
import os

mp.mp.dps = 25

OUT_DIR = os.path.dirname(os.path.abspath(__file__))


def first_zeta_zeros(k):
    return np.array([float(mp.im(mp.zetazero(n))) for n in range(1, k + 1)])


def build_D(L, N):
    """Hermitian discretization of -i d/du on (0, L), Dirichlet BCs."""
    du = L / (N + 1)
    upper = np.full(N - 1, -1j / (2 * du), dtype=complex)
    lower = np.full(N - 1, 1j / (2 * du), dtype=complex)
    M = np.diag(upper, 1) + np.diag(lower, -1)
    return 0.5 * (M + M.conj().T)


def u_grid(L, N):
    """Interior grid points in (0, L)."""
    du = L / (N + 1)
    return np.array([(j + 1) * du for j in range(N)])


# ----- POTENTIALS -----

def V_bare(u_arr, eps, ch2):
    return np.zeros_like(u_arr, dtype=float)


def V_Rf_at_2(u_arr, eps, ch2):
    """V = eps*(ch2-0.95)*Re[zeta(1 + i*u)]  (using R_f(2,s) = zeta(s))."""
    coupling = eps * (ch2 - 0.95)
    if abs(coupling) < 1e-15:
        return np.zeros_like(u_arr, dtype=float)
    V = np.zeros_like(u_arr, dtype=float)
    for j, u in enumerate(u_arr):
        # zeta(1 + i*u) — careful near u=0 because of pole at s=1.
        # Use mpmath, take real part. Cap near pole.
        s = mp.mpc(1.0, u)
        if abs(u) < 0.5:
            # near the pole; regularize by subtracting 1/(s-1)
            val = mp.zeta(s) - 1.0 / (s - 1.0)
        else:
            val = mp.zeta(s)
        V[j] = coupling * float(mp.re(val))
    return V


# Precompute primes up to P
def sieve_primes(P):
    sieve = np.ones(P + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(P**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False
    return np.flatnonzero(sieve)


PRIMES = sieve_primes(5000)


def V_prime_mod(u_arr, eps, ch2):
    """V = eps*(ch2-0.95) * sum_p (log p / sqrt(p)) * cos(log p * u)."""
    coupling = eps * (ch2 - 0.95)
    if abs(coupling) < 1e-15:
        return np.zeros_like(u_arr, dtype=float)
    log_p = np.log(PRIMES.astype(float))
    weights = log_p / np.sqrt(PRIMES.astype(float))
    # V[j] = sum_p weights[p] * cos(log_p * u[j])
    # Vectorize: (Np, Nu)
    cos_mat = np.cos(np.outer(log_p, u_arr))
    V = coupling * (weights @ cos_mat)
    return V


def V_one_over_zeta_sq(u_arr, eps, ch2):
    """V = eps*(ch2-0.95) / |zeta(1/2 + i*u)|^2."""
    coupling = eps * (ch2 - 0.95)
    if abs(coupling) < 1e-15:
        return np.zeros_like(u_arr, dtype=float)
    V = np.zeros_like(u_arr, dtype=float)
    for j, u in enumerate(u_arr):
        z = mp.zeta(mp.mpc(0.5, u))
        m = float(mp.fabs(z))
        if m < 1e-8:
            V[j] = 0.0  # at a zero, regularize
        else:
            V[j] = coupling / (m * m)
    return V


POTENTIALS = {
    "bare": V_bare,
    "Rf_at_2": V_Rf_at_2,
    "prime_mod": V_prime_mod,
    "one_over_zeta_sq": V_one_over_zeta_sq,
}


def diagonalize(L, N, pot_name, eps, ch2):
    D = build_D(L, N)
    u = u_grid(L, N)
    V = POTENTIALS[pot_name](u, eps, ch2)
    H = D + np.diag(V.astype(complex))
    H = 0.5 * (H + H.conj().T)
    w = np.linalg.eigvalsh(H)
    pos = w[w > 1e-8]
    return np.sort(pos)[:20]


def wigner_dyson_stats(eigs):
    """Compute level-spacing variance & KS distance to GUE Wigner surmise."""
    if len(eigs) < 3:
        return {"var": 0.0, "ks_to_GUE": 0.0, "n_spacings": 0}
    spacings = np.diff(eigs)
    s = spacings / np.mean(spacings)
    var = float(np.var(s))
    # GUE Wigner surmise CDF
    # P_GUE(s) = (32/pi^2) s^2 exp(-4 s^2 / pi)
    s_sorted = np.sort(s)
    n = len(s_sorted)
    # empirical CDF
    ecdf = np.arange(1, n + 1) / n
    # GUE CDF via numerical integration
    from scipy.integrate import cumulative_trapezoid

    s_dense = np.linspace(0, max(s_sorted.max(), 4.0), 5000)
    pdf_dense = (32.0 / np.pi**2) * s_dense**2 * np.exp(-4.0 * s_dense**2 / np.pi)
    cdf_dense = np.concatenate([[0.0], cumulative_trapezoid(pdf_dense, s_dense)])
    # interpolate GUE cdf at empirical s values
    gue_at_s = np.interp(s_sorted, s_dense, cdf_dense)
    ks = float(np.max(np.abs(ecdf - gue_at_s)))
    return {"var": var, "ks_to_GUE": ks, "n_spacings": n}


def run_experiment(L, N, pot_name, eps, ch2):
    eigs = diagonalize(L, N, pot_name, eps, ch2)
    zeros = first_zeta_zeros(20)
    rms = float(np.sqrt(np.mean((eigs - zeros) ** 2)))
    stats = wigner_dyson_stats(eigs)
    return {
        "L": L,
        "N": N,
        "pot": pot_name,
        "eps": eps,
        "ch2": ch2,
        "eigs": eigs.tolist(),
        "zeros": zeros.tolist(),
        "rms_vs_zeros": rms,
        "wd_stats": stats,
    }


if __name__ == "__main__":
    results = []

    # --- ch_2 sweep at fixed L=50, N=1000, with R_f modulation ---
    L, N = 50.0, 1000
    eps = 1.0
    for pot in ["bare", "Rf_at_2", "prime_mod", "one_over_zeta_sq"]:
        for ch2 in [0.5, 0.7, 0.9, 0.95, 1.0]:
            r = run_experiment(L, N, pot, eps, ch2)
            results.append(r)
            print(
                f"pot={pot:<18} ch2={ch2:<5} RMS_zeros={r['rms_vs_zeros']:8.3f}  "
                f"KS_GUE={r['wd_stats']['ks_to_GUE']:.3f}  var={r['wd_stats']['var']:.3f}"
            )

    with open(os.path.join(OUT_DIR, "results_02_modulated.json"), "w") as f:
        json.dump(results, f, indent=2)

    print("\nDone. Results in results_02_modulated.json")
