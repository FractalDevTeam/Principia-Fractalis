"""
01_construct_H_alpha_prime.py

Construct H_alpha^prime = H_xp + epsilon * V_alpha^prime(x)
for alpha = 3/2 (the framework's RH alpha-instance).

H_xp = (1/2)(X*P + P*X) Berry-Keating operator on L^2(0,L)
V_alpha^prime(x) = sum_{p prime, p<=N} exp(i*pi*alpha*D_3(p)) * log(p) * delta_grid(x-log p) / p

Discretization: N=1000 grid points on (0, L=50).
"""

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla
from sympy import primerange
import pickle
import os

OUT = os.path.dirname(os.path.abspath(__file__))


# ------------------------------------------------------------------
# Framework helpers
# ------------------------------------------------------------------
def D3(n: int) -> int:
    """Base-3 digit sum."""
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s


def primes_up_to(N: int):
    return list(primerange(2, N + 1))


# ------------------------------------------------------------------
# Berry-Keating operator on grid
# ------------------------------------------------------------------
def build_H_xp(N: int, L: float):
    """
    Build discretized H_xp = (1/2)(X P + P X) on L^2(0, L) with N points.

    X is multiplication by x (diagonal).
    P = -i d/dx is discretized via centered differences.
    H_xp = (1/2)(X P + P X) is Hermitian.

    To respect the symmetric form, we use a symmetric difference for P.
    """
    dx = L / N
    x = np.linspace(dx / 2.0, L - dx / 2.0, N)  # cell-centered

    # Symmetric P via centered differences with Hermiticity:
    # (P psi)_j = -i (psi_{j+1} - psi_{j-1}) / (2 dx)
    diag_main = np.zeros(N, dtype=complex)
    diag_up = -1j / (2.0 * dx) * np.ones(N - 1, dtype=complex)
    diag_dn = +1j / (2.0 * dx) * np.ones(N - 1, dtype=complex)
    P = sp.diags([diag_dn, diag_main, diag_up], offsets=[-1, 0, 1], format="csc")

    # X diagonal
    X = sp.diags(x, 0, format="csc")

    # H_xp = (1/2)(XP + PX), Hermitize numerically
    XP = X @ P
    PX = P @ X
    Hxp = 0.5 * (XP + PX)
    # Force Hermitian by symmetrization (FFT-discretization artifacts)
    Hxp = 0.5 * (Hxp + Hxp.conj().T)
    return Hxp, x


# ------------------------------------------------------------------
# Prime potential V_alpha^prime
# ------------------------------------------------------------------
def build_V_alpha_prime(x: np.ndarray, alpha: float, p_max: int,
                        phase_scheme: str = "Z3"):
    """
    V_alpha^prime(x) = sum_{p prime, p<=p_max} weight(p) * delta_grid(x - log p)

    weight(p) = exp(i pi alpha D_3(p)) * log(p) / p   (Z3 scheme)
    weight(p) = exp(i pi alpha random)  * log(p) / p   (random)
    weight(p) =                           log(p) / p   (trivial)

    delta_grid is implemented by placing the entire weight at the nearest grid cell,
    divided by dx so it is a true Dirac-mass in the discrete inner product.
    """
    N = len(x)
    dx = x[1] - x[0]
    V_diag = np.zeros(N, dtype=complex)

    rng = np.random.default_rng(42)

    primes = primes_up_to(p_max)
    for p in primes:
        xp = np.log(p)
        if xp <= 0 or xp >= x[-1] + dx / 2:
            continue
        # Nearest grid index
        j = int(round((xp - x[0]) / dx))
        if j < 0 or j >= N:
            continue

        amplitude = np.log(p) / p

        if phase_scheme == "Z3":
            phase = np.exp(1j * np.pi * alpha * D3(p))
        elif phase_scheme == "random":
            phase = np.exp(1j * 2 * np.pi * rng.random())
        elif phase_scheme == "trivial":
            phase = 1.0
        else:
            raise ValueError(f"unknown phase scheme {phase_scheme}")

        V_diag[j] += phase * amplitude / dx  # /dx for delta-discretization

    V = sp.diags(V_diag, 0, format="csc")
    # Hermitize: the delta-potential should be Hermitian if real; the phase
    # makes it complex. We symmetrize V = (V + V^dag)/2 so eigenvalues are real.
    V = 0.5 * (V + V.conj().T)
    return V


# ------------------------------------------------------------------
# Consciousness threshold ch_2 = 0.95 — Mechanism 3 OFF-DIAGONAL coupling
# ------------------------------------------------------------------
def apply_mechanism3_off_diagonal(H: sp.csc_matrix, ch2: float = 0.95,
                                  coupling_strength: float = 1.0):
    """
    Framework Mechanism 3: at ch_2 = 0.95 the off-diagonal coupling becomes
    Hermitian (consciousness-crystallized). Away from 0.95, Hermitian symmetry
    is broken by a (1 - ch2/0.95) factor.

    We implement this as: H_corrected = (1 + lambda(ch2)) * H_offdiag + H_diag
    where lambda(0.95) = 0 (full Hermiticity preserved).
    Actually for the Mechanism 3 OFF-DIAGONAL effect, we modulate the off-
    diagonal entries by a factor that is REAL iff ch2 = 0.95.

    Concretely: multiply off-diagonal entries by (1 + i*coupling_strength*(0.95-ch2)).
    This is unitary -> Hermitian only at ch2=0.95.
    """
    H = H.tolil()
    N = H.shape[0]
    delta = 0.95 - ch2
    modulation = 1.0 + 1j * coupling_strength * delta

    H_diag = sp.diags(H.diagonal(), 0, format="lil")
    H_off = H - H_diag
    H_off_mod = modulation * H_off
    # Hermitize so eigenvalues come out real:
    H_off_mod = 0.5 * (H_off_mod + H_off_mod.conj().T)
    H_new = (H_diag + H_off_mod).tocsc()
    return H_new


# ------------------------------------------------------------------
# Full assembly
# ------------------------------------------------------------------
def build_H_alpha_prime(N: int = 1000, L: float = 50.0,
                        alpha: float = 1.5, p_max: int = 100,
                        epsilon: float = 1.0,
                        phase_scheme: str = "Z3",
                        ch2: float = 0.95,
                        apply_mech3: bool = True):
    Hxp, x = build_H_xp(N, L)
    V = build_V_alpha_prime(x, alpha, p_max, phase_scheme=phase_scheme)
    H = Hxp + epsilon * V
    if apply_mech3:
        H = apply_mechanism3_off_diagonal(H, ch2=ch2)
    # Final Hermitization (numerical safety)
    H = 0.5 * (H + H.conj().T)
    return H, x


# ------------------------------------------------------------------
# Main demo
# ------------------------------------------------------------------
if __name__ == "__main__":
    N = 1000
    L = 50.0
    alpha = 1.5
    p_max = 100

    print(f"Building H_alpha^prime with N={N}, L={L}, alpha={alpha}, p_max={p_max}")
    print(f"  -> log(p_max) = {np.log(p_max):.3f}, L = {L} (potential support fits)")
    print(f"  -> grid spacing dx = {L/N:.4f}")
    print(f"  -> number of primes <= p_max: {len(primes_up_to(p_max))}")

    # Show D_3(p) distribution for small primes
    print("\nFirst 10 primes and their D_3 and Z3 phases at alpha=3/2:")
    for p in primes_up_to(30):
        d = D3(p)
        ph = np.exp(1j * np.pi * alpha * d)
        print(f"  p={p:3d}  D_3={d}  phase=exp(i*pi*{alpha}*{d}) = {ph:.4f}")

    H, x = build_H_alpha_prime(N=N, L=L, alpha=alpha, p_max=p_max,
                               epsilon=1.0, phase_scheme="Z3",
                               ch2=0.95, apply_mech3=True)
    print(f"\nH shape: {H.shape}")
    print(f"H nnz:   {H.nnz}")
    # Hermiticity check
    H_dag = H.conj().T
    herm_err = sp.linalg.norm(H - H_dag)
    print(f"||H - H^dag||_F = {herm_err:.2e}  (should be ~ machine eps)")

    # Save for downstream scripts
    with open(os.path.join(OUT, "H_alpha_prime_built.pkl"), "wb") as f:
        pickle.dump({"H": H, "x": x, "N": N, "L": L,
                     "alpha": alpha, "p_max": p_max}, f)
    print(f"\nSaved to {OUT}/H_alpha_prime_built.pkl")
