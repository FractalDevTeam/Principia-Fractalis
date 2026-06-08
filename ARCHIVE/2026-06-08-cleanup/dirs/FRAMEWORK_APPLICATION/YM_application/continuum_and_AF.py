"""
continuum_and_AF.py — Continuum limit via T_∞ and asymptotic-freedom sketch.

Companion to discharge_YM.py.  Two pieces:

(A) Continuum-limit numerical witness.  T_∞ = lim_k N(H_k) ⊗_min F_{α=2}.
    At α=2 with the anchor R_f(2,s)=ζ(s), the level-k truncation
    realises ζ via its partial sums  ζ_N(s) = Σ_{n=1}^{N} n^{-s}, N=3^k.
    We track Δ_k = Λ_QCD · ω_c^(k), with ω_c^(k) defined as the
    argmin of the truncated ρ_k(ω) := Re[ζ_N(1/ω)] subject to a
    BANDPASS WINDOW (the framework's IR cutoff is Λ_QCD-scale).

(B) Asymptotic freedom from the framework's universal coupling.
    Identifies the framework anchor λ_0(H_2)=π/20 with the leading-log
    IR boundary value of α_s(μ) at μ = Δ_fYM, then exhibits
    perturbative running to μ ≫ Λ_QCD.

Author: Claude, dispatched by Pabs (Principia Fractalis, 2026-05-23).
"""

from __future__ import annotations
import numpy as np
from mpmath import mp, mpc, mpf, zeta, re, im, pi, log
from scipy.optimize import brentq, minimize_scalar

mp.dps = 50


# ----------------------------------------------------------------------
# (A) Continuum limit:  level-k truncation behaviour
# ----------------------------------------------------------------------
def rho_full(omega: float) -> float:
    """ρ(ω) = ζ(1/ω) on the real axis (full, untruncated)."""
    return float(re(zeta(mpf(1) / mpf(omega))))


def rho_truncated(omega: float, N: int) -> float:
    """ρ_N(ω) = Re Σ_{n=1}^{N} n^{-1/ω}."""
    s = mpf(1) / mpf(omega)
    val = sum(mpc(1) / mpc(n) ** s for n in range(1, N + 1))
    return float(re(val))


def find_local_extremum(f, a, b, n_grid=400):
    """Find the abscissa where |f| is minimal in [a,b].
    Uses bounded scalar minimisation to avoid bracketing failures
    when the minimum lies at an endpoint or |f| is monotone."""
    # First: pure grid search for a robust initial estimate.
    grid = np.linspace(a, b, n_grid)
    vals = np.array([abs(f(float(x))) for x in grid])
    i = int(np.argmin(vals))
    x_grid = float(grid[i])
    f_grid = float(vals[i])
    # Refine with a bounded optimiser around the grid minimum.
    lo = max(a, x_grid - (b - a) / n_grid)
    hi = min(b, x_grid + (b - a) / n_grid)
    if hi - lo < 1e-12:
        return x_grid, f_grid
    res = minimize_scalar(lambda x: abs(f(float(x))), bounds=(lo, hi),
                          method='bounded', options={'xatol': 1e-10})
    if res.fun < f_grid:
        return float(res.x), float(res.fun)
    return x_grid, f_grid


def continuum_witness(K=(1, 2, 3, 4, 5, 6, 7), window=(1.5, 5.0)):
    """For each level k, locate the first 'resonance' = local min of |ρ_N|
    in the IR window, and report convergence to the manuscript ω_c."""
    print(f"  level k    N=3^k      ω*_k       |ρ_N(ω*_k)|     Δ_k (MeV)")
    print(f"  ------------------------------------------------------------")
    Lambda = 197.2
    omega_manuscript = 2.13198462
    for k in K:
        N = 3 ** k
        try:
            wstar, val = find_local_extremum(
                lambda w: rho_truncated(w, N), window[0], window[1], n_grid=200
            )
            Dk = Lambda * wstar
            print(f"  k={k}   N={N:>7}   ω*={wstar:.6f}   |ρ_N|={val:.4e}   "
                  f"Δ_k={Dk:.2f}")
        except Exception as e:
            print(f"  k={k}   N={N:>7}   FAILED ({e})")
    # Full ζ comparison
    try:
        wstar_full, val_full = find_local_extremum(rho_full, window[0], window[1],
                                                    n_grid=400)
        print(f"  k=∞ (full ζ)            ω*={wstar_full:.6f}   "
              f"|ρ|={val_full:.4e}   Δ_∞={Lambda * wstar_full:.2f}")
    except Exception as e:
        print(f"  k=∞ failed: {e}")
    print(f"  Manuscript pinned ω_c   = {omega_manuscript}")
    print(f"  Manuscript pinned Δ_fYM = {Lambda * omega_manuscript:.2f} MeV")


# ----------------------------------------------------------------------
# (B) Asymptotic freedom from λ_0(H_2)=π/20
# ----------------------------------------------------------------------
def alpha_s_running(mu_MeV: float,
                     Lambda_QCD_MeV: float = 197.2,
                     N_c: int = 3, N_f: int = 3) -> float:
    """1-loop QCD running.

        α_s(μ) = 1 / (b_0 · log(μ²/Λ²))
        b_0    = (11 N_c − 2 N_f) / (12π)
    """
    b0 = (11 * N_c - 2 * N_f) / (12 * float(pi))
    if mu_MeV <= Lambda_QCD_MeV:
        return float('inf')
    return 1.0 / (b0 * np.log((mu_MeV / Lambda_QCD_MeV) ** 2))


def asymptotic_freedom_demo():
    Lambda = 197.2
    omega_c = 2.13198462
    Delta = Lambda * omega_c
    coupling = float(pi) / 20.0  # framework λ_0(H_2)
    print(f"  Framework universal coupling at α=2:  λ_0(H_2) = π/20 = {coupling:.6f}")
    print(f"  Δ_fYM (IR mass-gap scale) = {Delta:.2f} MeV")
    print(f"  α_s(Δ_fYM)  one-loop      = {alpha_s_running(Delta):.4f}")
    print(f"  α_s(1 GeV)  one-loop      = {alpha_s_running(1000):.4f}")
    print(f"  α_s(M_Z = 91200 MeV)      = {alpha_s_running(91200):.4f}")
    print(f"  α_s(M_Z) experimental     ≈ 0.118")
    print()
    print(f"  Framework match condition: λ_0(H_2) = α_s(μ*) for some μ* with")
    print(f"  α_s(μ*) = π/20.  Solve 1/(b0·log(μ*²/Λ²)) = π/20:")
    b0 = (11 * 3 - 2 * 3) / (12 * float(pi))
    log_term = 1.0 / (b0 * coupling)
    mu_star = Lambda * float(np.exp(log_term / 2))
    print(f"    b_0       = {b0:.6f}")
    print(f"    log(μ*²/Λ²) = 1/(b0·π/20) = {log_term:.6f}")
    print(f"    μ*        = Λ_QCD · exp({log_term/2:.4f}) = {mu_star:.2f} MeV")
    print(f"    μ* / Δ_fYM = {mu_star/Delta:.4f}")


# ----------------------------------------------------------------------
# MAIN
# ----------------------------------------------------------------------
if __name__ == "__main__":
    print("=" * 70)
    print("(A) CONTINUUM LIMIT via T_∞ projective limit, α = 2")
    print("=" * 70)
    continuum_witness()

    print()
    print("=" * 70)
    print("(B) ASYMPTOTIC FREEDOM from λ_0(H_2) = π/20")
    print("=" * 70)
    asymptotic_freedom_demo()
