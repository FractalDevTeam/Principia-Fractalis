"""
BBM (Bender-Brody-Muller 2017) non-local Hamiltonian + Principia Fractalis framework.

Implements:
  H_BBM = (1/(1 - exp(-i*hbar*dx))) * (X P + P X)   on L^2(0, L]
  H_BBM^framework = H_BBM + epsilon * (ch_2 - 0.95) * V_alpha(x)
  where V_alpha uses R_f(3/2, .) values to modulate the BBM kernel.

We test:
  - PT-symmetry of H_BBM
  - Eigenvalues vs. first 20 nontrivial zeta zeros
  - Effect of framework Mechanism 3 ch_2 modulation
  - Wigner-Dyson (GUE) spacing statistics

Author: Claude Opus 4.7 (1M ctx) for Pablo Cohen, 2026-05-23.
"""
from __future__ import annotations

import numpy as np
import scipy.linalg as sla
from scipy.fft import fft, ifft, fftfreq
from dataclasses import dataclass


# ---------------------------------------------------------------------------
# Reference zeta zero imaginary parts (first 20, Odlyzko table)
# ---------------------------------------------------------------------------
ZETA_ZEROS = np.array([
    14.134725142, 21.022039639, 25.010857580, 30.424876126,
    32.935061588, 37.586178159, 40.918719012, 43.327073281,
    48.005150881, 49.773832478, 52.970321478, 56.446247697,
    59.347044003, 60.831778525, 65.112544048, 67.079810529,
    69.546401711, 72.067157674, 75.704690699, 77.144840069,
])


# ---------------------------------------------------------------------------
# R_f base-3 digit-sum resonance function (framework primitive)
# ---------------------------------------------------------------------------
def base3_digit_sum(n: int) -> int:
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s


def R_f(alpha: float, s: complex, N: int = 4000) -> complex:
    """R_f(alpha, s) = sum_{n=1..N} exp(i*pi*alpha*D_3(n)) / n^s."""
    n = np.arange(1, N + 1)
    D3 = np.array([base3_digit_sum(int(k)) for k in n], dtype=np.float64)
    phases = np.exp(1j * np.pi * alpha * D3)
    return np.sum(phases / (n ** s))


# ---------------------------------------------------------------------------
# Discrete operators on (0, L] with N grid points
# ---------------------------------------------------------------------------
@dataclass
class Grid:
    N: int
    L: float

    @property
    def dx(self) -> float:
        return self.L / self.N

    @property
    def x(self) -> np.ndarray:
        # uniform grid x_j = (j + 1/2) * dx, j = 0..N-1 (midpoint, avoid x=0)
        return (np.arange(self.N) + 0.5) * self.dx

    @property
    def k(self) -> np.ndarray:
        # FFT momentum frequencies (angular)
        return 2.0 * np.pi * fftfreq(self.N, d=self.dx)


def momentum_matrix(grid: Grid) -> np.ndarray:
    """P = -i d/dx via spectral FFT differentiation matrix."""
    N = grid.N
    k = grid.k
    # P acts in momentum space as multiplication by k
    F = np.fft.fft(np.eye(N), axis=0)
    Finv = np.fft.ifft(np.eye(N), axis=0)
    # P = F^{-1} diag(k) F
    P = Finv @ np.diag(k) @ F
    return P


def position_matrix(grid: Grid) -> np.ndarray:
    return np.diag(grid.x)


def xp_plus_px(grid: Grid) -> np.ndarray:
    """Symmetric Berry-Keating operator (XP + PX)/2 -> Berry-Keating is (XP+PX)."""
    X = position_matrix(grid)
    P = momentum_matrix(grid)
    return X @ P + P @ X


def shift_inverse_operator(grid: Grid, hbar: float = 1.0) -> np.ndarray:
    """
    (1 - exp(-i*hbar*d/dx))^{-1} via spectral calculus on FFT basis.
    In momentum space exp(-i*hbar*d/dx) acts as exp(-i*hbar*(i*k)) = exp(hbar*k)?
    Careful: d/dx in momentum space is multiplication by i*k (since P = -i d/dx,
    so d/dx = i*P, and P -> k means d/dx -> i*k).
    Therefore exp(-i*hbar*d/dx) -> exp(-i*hbar*(i*k)) = exp(hbar*k).

    But BBM paper uses (1 - Delta_hbar)^{-1} where Delta_hbar = exp(-i*hbar*d/dx);
    the resulting symbol diverges for large |k|. We regularize by clipping
    |hbar*k| <= cutoff (the integrable manifold). This is the standard BBM
    discretization caveat.
    """
    N = grid.N
    k = grid.k
    # exp(-i*hbar * d/dx) = exp(hbar*k) in momentum space? That blows up.
    # The original BBM paper writes it as (1 - exp(-i*hbar*p))^{-1} where p = -i d/dx,
    # so exp(-i*hbar*p) = exp(-i*hbar*(-i d/dx)) = exp(-hbar*d/dx).
    # In momentum (Fourier) basis, p -> k (eigenvalue), so exp(-i*hbar*p) -> exp(-i*hbar*k).
    # Then 1 - exp(-i*hbar*k), and inverse is 1/(1 - exp(-i*hbar*k)).
    # This has poles at k = 2*pi*n/hbar. We regularize by adding small imaginary part.
    eps = 1e-10
    denom = 1.0 - np.exp(-1j * hbar * k) + eps
    inv_symbol = 1.0 / denom
    F = np.fft.fft(np.eye(N), axis=0)
    Finv = np.fft.ifft(np.eye(N), axis=0)
    return Finv @ np.diag(inv_symbol) @ F


def H_BBM(grid: Grid, hbar: float = 1.0) -> np.ndarray:
    """H_BBM = (1 - exp(-i*hbar*p))^{-1} * (XP + PX)."""
    S = shift_inverse_operator(grid, hbar)
    BK = xp_plus_px(grid)
    return S @ BK


# ---------------------------------------------------------------------------
# Framework modulation V_alpha using R_f(3/2, .) values
# ---------------------------------------------------------------------------
def V_alpha_potential(grid: Grid, alpha: float = 1.5, N_terms: int = 200) -> np.ndarray:
    """
    V_alpha(x) = sum_{n=1..N_terms} Re(exp(i*pi*alpha*D_3(n))) * cos(n*x) / n^2
    A smooth bounded modulation on (0, L]; uses R_f phase data at alpha=3/2.
    """
    x = grid.x
    n = np.arange(1, N_terms + 1)
    D3 = np.array([base3_digit_sum(int(k)) for k in n], dtype=np.float64)
    coeffs = np.cos(np.pi * alpha * D3) / (n ** 2)  # bounded by zeta(2)
    # outer: shape (len(x), N_terms)
    cos_table = np.cos(np.outer(x, n))
    V = cos_table @ coeffs
    return np.diag(V)


def H_BBM_framework(
    grid: Grid,
    hbar: float = 1.0,
    ch_2: float = 0.95,
    alpha: float = 1.5,
    epsilon: float = 1.0,
) -> np.ndarray:
    H0 = H_BBM(grid, hbar)
    V = V_alpha_potential(grid, alpha=alpha)
    return H0 + epsilon * (ch_2 - 0.95) * V


# ---------------------------------------------------------------------------
# PT-symmetry test:  P : x -> L - x ;  T : complex conjugation
# Test  P T H (PT)^{-1} = H
# ---------------------------------------------------------------------------
def parity_matrix(grid: Grid) -> np.ndarray:
    """P : f(x) -> f(L - x). On midpoint grid this is the flip permutation."""
    return np.fliplr(np.eye(grid.N))


def pt_symmetry_residual(H: np.ndarray, grid: Grid) -> float:
    """Returns ||PT H (PT)^{-1} - H|| / ||H|| where T = complex conjugation."""
    P = parity_matrix(grid)
    # (PT) H (PT)^{-1} f = P conj( H conj(P f) )
    H_pt = P @ np.conj(H) @ P  # since P is real symmetric involution, P^{-1} = P
    num = np.linalg.norm(H_pt - H)
    den = np.linalg.norm(H) + 1e-30
    return num / den


# ---------------------------------------------------------------------------
# Eigenvalues, sorting, spacing statistics
# ---------------------------------------------------------------------------
def eigen_sorted(H: np.ndarray, n_keep: int = 50) -> np.ndarray:
    w = sla.eigvals(H)
    # Sort by |Im(w)| (BBM conjecture: eigenvalues purely imaginary, related to gamma_n)
    idx = np.argsort(np.abs(w.imag))
    w = w[idx]
    # Keep first n_keep with positive imaginary part
    pos = w[w.imag > 0]
    pos = pos[np.argsort(pos.imag)]
    return pos[:n_keep]


def unfolded_spacings(levels: np.ndarray) -> np.ndarray:
    """Unfold by mean spacing, return normalized nearest-neighbor spacings."""
    g = np.sort(levels.real if np.allclose(levels.imag, 0) else levels.imag)
    s = np.diff(g)
    if s.size == 0:
        return s
    return s / np.mean(s)


def variance_of_spacings(s: np.ndarray) -> float:
    return float(np.var(s)) if s.size > 1 else float("nan")


# ---------------------------------------------------------------------------
# Reporter
# ---------------------------------------------------------------------------
def report(H, grid, name: str) -> dict:
    pt = pt_symmetry_residual(H, grid)
    ev = eigen_sorted(H, n_keep=20)
    # if eigenvalues are essentially real but should be imaginary, also try real sort
    s_im = unfolded_spacings(ev.imag) if np.any(ev.imag > 1e-8) else np.array([])
    var_s = variance_of_spacings(s_im) if s_im.size > 0 else float("nan")

    # Compare to zeta zeros: try matching by imaginary parts
    zeta = ZETA_ZEROS
    # rough scaling: BBM eigenvalues need rescaling to match gamma_n
    if ev.size and np.any(ev.imag > 1e-8):
        scale = zeta[0] / max(ev.imag[0], 1e-12)
        scaled_im = ev.imag * scale
        rel_err = np.abs(scaled_im[: min(len(zeta), len(scaled_im))]
                         - zeta[: min(len(zeta), len(scaled_im))]) / \
                  zeta[: min(len(zeta), len(scaled_im))]
        mean_rel = float(np.mean(rel_err))
    else:
        scale = float("nan")
        scaled_im = np.array([])
        mean_rel = float("nan")

    return dict(
        name=name,
        pt_residual=pt,
        ev_first10_real=ev.real[:10].tolist(),
        ev_first10_imag=ev.imag[:10].tolist(),
        scale_to_zeta=scale,
        scaled_imag=scaled_im[:10].tolist(),
        zeta_first10=zeta[:10].tolist(),
        mean_relative_error=mean_rel,
        var_unfolded_spacing=var_s,
        gue_target_variance=0.18,
        gse_target_variance=0.10,
        goe_target_variance=0.27,
        poisson_target_variance=1.00,
    )


if __name__ == "__main__":
    import json

    # Conservative size for direct dense diagonalization (N^3 cost)
    grid = Grid(N=512, L=50.0)

    print("Building H_BBM ...")
    H0 = H_BBM(grid, hbar=1.0)

    print("Building H_BBM^framework  ch_2 = 0.95 (modulation off)...")
    H_at = H_BBM_framework(grid, hbar=1.0, ch_2=0.95, alpha=1.5, epsilon=1.0)

    print("Building H_BBM^framework  ch_2 = 0.70 (subthreshold modulation)...")
    H_sub = H_BBM_framework(grid, hbar=1.0, ch_2=0.70, alpha=1.5, epsilon=1.0)

    print("Building H_BBM^framework  ch_2 = 0.99 (superthreshold modulation)...")
    H_sup = H_BBM_framework(grid, hbar=1.0, ch_2=0.99, alpha=1.5, epsilon=1.0)

    results = []
    for H, nm in [
        (H0, "H_BBM bare"),
        (H_at, "H_BBM_framework ch_2=0.95"),
        (H_sub, "H_BBM_framework ch_2=0.70"),
        (H_sup, "H_BBM_framework ch_2=0.99"),
    ]:
        print(f"  reporting {nm} ...")
        results.append(report(H, grid, nm))

    out = json.dumps(results, indent=2, default=lambda o: float(o))
    print(out)
    with open(
        "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/"
        "RH_BBM_nonlocal/bbm_results.json",
        "w",
    ) as f:
        f.write(out)
    print("\nSaved bbm_results.json")
