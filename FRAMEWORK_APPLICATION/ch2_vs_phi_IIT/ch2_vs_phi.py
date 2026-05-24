"""
ch_2 (Principia Fractalis) vs Phi (Tononi IIT) Comparison
===========================================================

APPLICATION MODE: Test whether the framework's ch_2 measure (second
Chern character) recovers, refines, or genuinely differs from Tononi's
Integrated Information Phi.

Framework definitions:
    ch_2(rho)   = 1 - Tr(rho_A^2)             (quantum, partial trace)
    ch_2(W)     = (Tr(W^2) - (Tr W)^2) / (2 ||W||_F^2)   (neural)

Tononi IIT approximations used here (PyPhi not available in this env;
implementations follow the standard literature):
    Phi_M : minimum information bipartition (MIB) mutual information
            across bipartitions of system state distribution.
    Phi_G : effective-information / Gaussian Phi (Barrett-Seth 2011)
            for linear AR systems with i.i.d. noise.
    Phi_W : whole-minus-parts mutual information lower bound.

We pick Phi_G (Barrett-Seth Gaussian Phi) as the principal Phi proxy
because:
  (i) it is well-defined, closed-form, and reproducible without PyPhi,
  (ii) it operates on the SAME object as ch_2(W) (a connectivity matrix W),
 (iii) it has been used in the IIT literature as the canonical
       continuous-state Phi.

Phi_G(W, Sigma_eps) over partition P=(M1, M2):
    Phi_G(P) = (1/2) log(|Sigma_X(M1)| |Sigma_X(M2)| / |Sigma_X|)
               - similar conditional terms;
equivalently the time-delayed mutual information lost when the system
is cut into M1 and M2. We use the standard formulation:
    EI(X) = (1/2) log( |Sigma_full_pred| / |Sigma_cond_pred| )
and Phi = min over bipartitions of integrated information lost by
removing across-cut connections (Barrett-Seth 2011, Oizumi 2016 IIT 3.0
PyPhi default for continuous Gaussian systems).

Author: Claude (Opus 4.7) with Pablo Cohen, 2026-05-23
"""

from __future__ import annotations

import itertools
import math
import time
from dataclasses import dataclass
from typing import Callable

import numpy as np
from scipy.linalg import solve_discrete_lyapunov


# ---------------------------------------------------------------------------
# Section 1.  ch_2  (Principia Fractalis second Chern character)
# ---------------------------------------------------------------------------

def ch2_neural(W: np.ndarray) -> float:
    """ch_2 for a neural connectivity matrix W (Ch 6).

        ch_2(W) = (Tr(W^2) - (Tr W)^2) / (2 ||W||_F^2)

    Returns 0 when W is the zero matrix.
    """
    W = np.asarray(W, dtype=float)
    fro_sq = float(np.sum(W * W))
    if fro_sq == 0.0:
        return 0.0
    tr_W2 = float(np.trace(W @ W))
    trW = float(np.trace(W))
    return (tr_W2 - trW * trW) / (2.0 * fro_sq)


def ch2_quantum(rho: np.ndarray, dimA: int, dimB: int) -> float:
    """ch_2 for a bipartite quantum state rho on H_A (x) H_B.

        ch_2(rho) = 1 - Tr(rho_A^2)

    where rho_A = Tr_B rho.  Returns the purity-based linear entropy
    (a.k.a. 1 minus the purity of the reduced state), normalized so that
    a maximally mixed reduced state of dimension d gives 1 - 1/d.
    """
    rho = np.asarray(rho, dtype=complex)
    assert rho.shape == (dimA * dimB, dimA * dimB)
    # Partial trace over B
    rho_tensor = rho.reshape(dimA, dimB, dimA, dimB)
    rho_A = np.einsum("ijkj->ik", rho_tensor)
    purity = float(np.real(np.trace(rho_A @ rho_A)))
    return 1.0 - purity


# ---------------------------------------------------------------------------
# Section 2.  Phi_G  (Barrett-Seth Gaussian Phi - IIT proxy)
# ---------------------------------------------------------------------------

def _stationary_cov(W: np.ndarray, Sigma_eps: np.ndarray,
                    spectral_safety: float = 0.95) -> np.ndarray:
    """Stationary covariance Sigma of the linear AR(1) process
        X_{t+1} = W X_t + eps_t,   eps_t ~ N(0, Sigma_eps).

    The system must be stable (spectral radius < 1); if not, W is
    rescaled to bring it below `spectral_safety`.  Solves the discrete
    Lyapunov equation Sigma = W Sigma W^T + Sigma_eps.
    """
    n = W.shape[0]
    sr = max(abs(np.linalg.eigvals(W)))
    if sr >= spectral_safety:
        W = W * (spectral_safety / max(sr, 1e-12))
    Sigma = solve_discrete_lyapunov(W, Sigma_eps)
    return Sigma, W


def _safe_logdet(M: np.ndarray, eps: float = 1e-12) -> float:
    """Numerically stable log|det M| via slogdet, with regularization
    for near-singular matrices.
    """
    M = np.asarray(M)
    if M.size == 0:
        return 0.0
    sign, logdet = np.linalg.slogdet(M + eps * np.eye(M.shape[0]))
    if sign <= 0:
        # Mild regularization fallback
        sign, logdet = np.linalg.slogdet(M + (eps * 1e3) * np.eye(M.shape[0]))
    return float(logdet)


def effective_information_gaussian(W: np.ndarray,
                                   Sigma_eps: np.ndarray | None = None) -> float:
    """Whole-system effective information (Barrett-Seth):
        EI(X) = (1/2) log |Sigma| / |Sigma_eps|
    interpreted as the information that the past state provides about
    the next state.  Equivalently the time-delayed mutual information.
    """
    n = W.shape[0]
    if Sigma_eps is None:
        Sigma_eps = np.eye(n)
    Sigma, W_used = _stationary_cov(W, Sigma_eps)
    return 0.5 * (_safe_logdet(Sigma) - _safe_logdet(Sigma_eps))


def phi_gaussian(W: np.ndarray,
                 Sigma_eps: np.ndarray | None = None,
                 max_partitions: int = 256) -> float:
    """Gaussian Phi (Barrett-Seth 2011), the principal continuous-state
    IIT proxy used here.

    Phi(X) = min over bipartitions P of  EI(X) - sum_k EI(X^P_k)
    where EI is the whole-system effective information and EI(X^P_k)
    is the effective information of the k-th part with across-cut
    incoming connections removed.

    We enumerate all 2^(n-1) - 1 bipartitions (n <= ~12).
    For larger systems we sample `max_partitions` random bipartitions.
    """
    n = W.shape[0]
    if Sigma_eps is None:
        Sigma_eps = np.eye(n)

    EI_whole = effective_information_gaussian(W, Sigma_eps)
    if EI_whole <= 0:
        return 0.0

    indices = list(range(n))
    bipartitions = []
    if n <= 12:
        # Enumerate non-trivial bipartitions (exclude empty / full duplicates).
        for r in range(1, n // 2 + 1):
            for M1 in itertools.combinations(indices, r):
                M2 = tuple(i for i in indices if i not in M1)
                if r == n - r and M1 > M2:
                    continue  # avoid duplicate symmetric partition
                bipartitions.append((M1, M2))
    else:
        rng = np.random.default_rng(0)
        seen = set()
        while len(bipartitions) < max_partitions:
            mask = rng.integers(0, 2, size=n)
            if mask.sum() in (0, n):
                continue
            key = tuple(mask.tolist())
            inv = tuple(1 - m for m in key)
            if key in seen or inv in seen:
                continue
            seen.add(key)
            M1 = tuple(i for i, b in enumerate(mask) if b == 1)
            M2 = tuple(i for i, b in enumerate(mask) if b == 0)
            bipartitions.append((M1, M2))

    best_phi = math.inf
    for M1, M2 in bipartitions:
        W_cut = W.copy()
        # Sever across-cut directed edges (both directions)
        for i in M1:
            for j in M2:
                W_cut[i, j] = 0.0
                W_cut[j, i] = 0.0
        Sigma_cut, _ = _stationary_cov(W_cut, Sigma_eps)
        # EI of each part is computed on its sub-process
        EI_parts = 0.0
        for part in (M1, M2):
            if not part:
                continue
            W_sub = W[np.ix_(part, part)]
            Sigma_eps_sub = Sigma_eps[np.ix_(part, part)]
            EI_parts += effective_information_gaussian(W_sub, Sigma_eps_sub)
        phi_P = max(EI_whole - EI_parts, 0.0)
        if phi_P < best_phi:
            best_phi = phi_P
        if best_phi == 0.0:
            break
    return float(best_phi if best_phi != math.inf else 0.0)


# ---------------------------------------------------------------------------
# Section 3.  Quantum Phi (purity-mutual-information proxy)
# ---------------------------------------------------------------------------

def quantum_phi_mib(rho: np.ndarray, dimA: int, dimB: int) -> float:
    """Quantum mutual information across the (A | B) bipartition,
        I(A:B) = S(rho_A) + S(rho_B) - S(rho_AB),
    used as the quantum IIT proxy.  For pure rho_AB this reduces to
    2 S(rho_A) and is monotone with ch_2_quantum.
    """
    rho = np.asarray(rho, dtype=complex)
    rho_tensor = rho.reshape(dimA, dimB, dimA, dimB)
    rho_A = np.einsum("ijkj->ik", rho_tensor)
    rho_B = np.einsum("ijil->jl", rho_tensor)

    def von_neumann(rho_):
        evals = np.linalg.eigvalsh(rho_)
        evals = evals[evals > 1e-12]
        return float(-np.sum(evals * np.log(evals)))

    return von_neumann(rho_A) + von_neumann(rho_B) - von_neumann(rho)


# ---------------------------------------------------------------------------
# Section 4.  Test systems
# ---------------------------------------------------------------------------

def cycle_graph_W(n: int, weight: float = 0.5) -> np.ndarray:
    """Directed cycle 1 -> 2 -> ... -> n -> 1, edge weight = `weight`."""
    W = np.zeros((n, n))
    for i in range(n):
        W[(i + 1) % n, i] = weight
    return W


def complete_graph_W(n: int, weight: float = 0.5) -> np.ndarray:
    """Symmetric all-to-all connectivity (zero diagonal)."""
    W = np.full((n, n), weight)
    np.fill_diagonal(W, 0.0)
    return W


def disconnected_W(n: int, weight: float = 0.5) -> np.ndarray:
    """Block-diagonal: two halves with no cross-edges."""
    W = np.zeros((n, n))
    half = n // 2
    W[:half, :half] = weight / max(half, 1)
    W[half:, half:] = weight / max(n - half, 1)
    np.fill_diagonal(W, 0.0)
    return W


def erdos_renyi_W(n: int, p: float, seed: int = 0,
                  weight_scale: float = 0.4) -> np.ndarray:
    """Random directed ER(n,p) with edge weights ~ N(0, weight_scale^2)."""
    rng = np.random.default_rng(seed)
    mask = rng.random((n, n)) < p
    np.fill_diagonal(mask, False)
    W = mask * rng.normal(0.0, weight_scale, size=(n, n))
    return W


def identity_W(n: int, weight: float = 0.5) -> np.ndarray:
    return weight * np.eye(n)


# ---------------------------------------------------------------------------
# Quantum test states
# ---------------------------------------------------------------------------

def bell_state_rho() -> np.ndarray:
    psi = np.array([1, 0, 0, 1]) / math.sqrt(2)
    return np.outer(psi, psi.conj())


def product_state_rho() -> np.ndarray:
    psi = np.array([1, 0, 0, 0])  # |00>
    return np.outer(psi, psi.conj())


def werner_state_rho(p: float) -> np.ndarray:
    bell = bell_state_rho()
    I4 = np.eye(4) / 4.0
    return p * bell + (1 - p) * I4


# ---------------------------------------------------------------------------
# Section 5.  Sweep + correlation
# ---------------------------------------------------------------------------

@dataclass
class Result:
    name: str
    n: int
    ch2: float
    phi: float


def run_neural_sweep() -> list[Result]:
    results = []
    # Cycles
    for n in [3, 4, 5, 6, 8]:
        W = cycle_graph_W(n, weight=0.5)
        results.append(Result(f"cycle_C{n}", n, ch2_neural(W), phi_gaussian(W)))

    # Complete graphs
    for n in [3, 4, 5, 6, 8]:
        W = complete_graph_W(n, weight=0.3)
        results.append(Result(f"complete_K{n}", n, ch2_neural(W), phi_gaussian(W)))

    # Disconnected
    for n in [4, 6, 8]:
        W = disconnected_W(n, weight=0.4)
        results.append(Result(f"disconnected_{n}", n, ch2_neural(W), phi_gaussian(W)))

    # Identity (purely autonomous)
    for n in [3, 5, 8]:
        W = identity_W(n, weight=0.6)
        results.append(Result(f"identity_{n}", n, ch2_neural(W), phi_gaussian(W)))

    # Erdos-Renyi sweep
    for n in [4, 6, 8]:
        for p in [0.2, 0.5, 0.8]:
            for seed in range(3):
                W = erdos_renyi_W(n, p, seed=seed)
                results.append(Result(
                    f"ER_n{n}_p{p:.1f}_s{seed}", n,
                    ch2_neural(W), phi_gaussian(W)
                ))
    return results


def run_quantum_sweep() -> list[tuple[str, float, float]]:
    rows = []
    rho = bell_state_rho()
    rows.append(("bell_max_entangled", ch2_quantum(rho, 2, 2),
                 quantum_phi_mib(rho, 2, 2)))
    rho = product_state_rho()
    rows.append(("product_00", ch2_quantum(rho, 2, 2),
                 quantum_phi_mib(rho, 2, 2)))
    for p in np.linspace(0.0, 1.0, 11):
        rho = werner_state_rho(float(p))
        rows.append((f"werner_p{p:.1f}", ch2_quantum(rho, 2, 2),
                     quantum_phi_mib(rho, 2, 2)))
    return rows


# ---------------------------------------------------------------------------
# Section 6.  Timing study
# ---------------------------------------------------------------------------

def timing_study(ns=(4, 6, 8, 10, 12)):
    rows = []
    for n in ns:
        W = erdos_renyi_W(n, 0.4, seed=42)

        t0 = time.perf_counter()
        for _ in range(5):
            _ = ch2_neural(W)
        ch2_t = (time.perf_counter() - t0) / 5.0

        t0 = time.perf_counter()
        _ = phi_gaussian(W)
        phi_t = time.perf_counter() - t0

        rows.append((n, ch2_t, phi_t, phi_t / max(ch2_t, 1e-12)))
    return rows


# ---------------------------------------------------------------------------
# Section 7.  Main
# ---------------------------------------------------------------------------

def correlate(xs, ys):
    xs = np.asarray(xs); ys = np.asarray(ys)
    if xs.std() == 0 or ys.std() == 0:
        return float("nan"), float("nan")
    r = float(np.corrcoef(xs, ys)[0, 1])
    # Spearman (rank)
    rx = xs.argsort().argsort()
    ry = ys.argsort().argsort()
    rho = float(np.corrcoef(rx, ry)[0, 1])
    return r, rho


def main():
    print("=" * 72)
    print(" ch_2 (Principia Fractalis)  vs  Phi (Tononi IIT, Gaussian proxy)")
    print("=" * 72)

    print("\n--- NEURAL SWEEP ---")
    neural = run_neural_sweep()
    print(f"{'system':<22} {'n':>3} {'ch_2':>10} {'Phi_G':>10}")
    for r in neural:
        print(f"{r.name:<22} {r.n:>3} {r.ch2:>10.4f} {r.phi:>10.4f}")

    ch2_vals = [r.ch2 for r in neural]
    phi_vals = [r.phi for r in neural]
    pear, spr = correlate(ch2_vals, phi_vals)
    print(f"\nPearson  corr(ch_2, Phi_G) = {pear:.4f}")
    print(f"Spearman corr(ch_2, Phi_G) = {spr:.4f}")

    # Threshold analysis
    print("\n--- THRESHOLD ANALYSIS ---")
    above = [(r.ch2, r.phi, r.name) for r in neural if r.ch2 >= 0.95]
    below = [(r.ch2, r.phi, r.name) for r in neural if r.ch2 < 0.95]
    print(f"systems with ch_2 >= 0.95 : {len(above)}")
    for c, p, n in above:
        print(f"  {n:<22} ch_2={c:.4f}  Phi_G={p:.4f}")
    if above:
        phi_at_thresh = np.mean([p for _, p, _ in above])
        print(f"  -> mean Phi_G at ch_2 >= 0.95 :  {phi_at_thresh:.4f}")
    if below:
        print(f"systems with ch_2  < 0.95 : {len(below)} "
              f"(max Phi_G = {max(p for _, p, _ in below):.4f})")

    print("\n--- QUANTUM SWEEP (2x2 bipartite) ---")
    quantum = run_quantum_sweep()
    print(f"{'state':<22} {'ch_2':>10} {'I(A:B)':>10}")
    for name, c2, ph in quantum:
        print(f"{name:<22} {c2:>10.4f} {ph:>10.4f}")
    ch2_q = [c for _, c, _ in quantum]
    phi_q = [p for _, _, p in quantum]
    pear_q, spr_q = correlate(ch2_q, phi_q)
    print(f"\nPearson  corr(ch_2, I(A:B)) = {pear_q:.4f}")
    print(f"Spearman corr(ch_2, I(A:B)) = {spr_q:.4f}")

    print("\n--- TIMING (computational complexity) ---")
    tt = timing_study()
    print(f"{'n':>4} {'ch_2 (s)':>14} {'Phi_G (s)':>14} {'ratio':>10}")
    for n, c, p, ratio in tt:
        print(f"{n:>4} {c:>14.6g} {p:>14.6g} {ratio:>10.2f}x")

    # Persist results
    import json
    out = {
        "neural": [r.__dict__ for r in neural],
        "neural_corr": {"pearson": pear, "spearman": spr},
        "quantum": [{"state": n, "ch2": c, "phi_QMI": p}
                    for n, c, p in quantum],
        "quantum_corr": {"pearson": pear_q, "spearman": spr_q},
        "timing": [{"n": n, "ch2_sec": c, "phi_sec": p, "ratio": r}
                   for n, c, p, r in tt],
    }
    path = "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/ch2_vs_phi_IIT/results.json"
    with open(path, "w") as f:
        json.dump(out, f, indent=2)
    print(f"\nResults saved to {path}")


if __name__ == "__main__":
    main()
