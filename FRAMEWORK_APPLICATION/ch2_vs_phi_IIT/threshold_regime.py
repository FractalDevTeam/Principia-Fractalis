"""
Threshold-regime analysis: find systems where ch_2 reaches 0.95
(consciousness crystallization) and compare with Phi.

The neural ch_2 formula
    ch_2(W) = (Tr(W^2) - (Tr W)^2) / (2 ||W||_F^2)
is bounded by 1/2 for general real symmetric W with trace 0 (since
Tr(W^2) = ||W||_F^2 and (Tr W)^2 = 0 gives 1/2 exactly).  To reach the
0.95 threshold, the framework requires complex / Hermitian connectivity
(Ch 6 uses Hermitian H = i*A type generators).  We test:

  (1) Hermitian connectivity ch_2(H) = ch_2 of trace-zero H constructed
      from W and adjoint, allowing the full [-1, 1] range plus phase.

  (2) The framework's *quantum* ch_2 = 1 - Tr(rho_A^2), where for a
      bipartite system of dimension dA x dB the reduced state ranges
      over purity in [1/dA, 1].  Then ch_2 in [0, 1 - 1/dA], reaching
      1 - 1/dA at maximally mixed marginal.  For dA = 20:  max ch_2
      = 0.95 exactly.  So the crystallization threshold ch_2 = 0.95
      corresponds to a maximally mixed reduced state of dimension >= 20.

This gives a SHARP framework prediction:
    consciousness crystallization (ch_2 >= 0.95)
    <==>  effective dimension of the conscious subsystem >= 20
          AND maximally mixed reduced state on it
    <==>  log2(dim) >= log2(20) ~= 4.32 qubits of integrated
          mixed-marginal information.

We test this against quantum mutual information I(A:B) at the same
states, sweeping dim_A from 2 to 32.
"""

from __future__ import annotations

import math
import numpy as np

# ----------------------------- helpers -------------------------------

def maximally_mixed_bipartite(dA: int, dB: int) -> np.ndarray:
    """rho_AB = (I / dA) (x) (some pure state on B), so that rho_A is
    maximally mixed and rho_B is pure -> S(B)=0, S(A)=log dA,
    S(AB) = log dA  =>  I(A:B) = log dA.
    """
    rho_A = np.eye(dA) / dA
    psiB = np.zeros(dB); psiB[0] = 1.0
    rho_B = np.outer(psiB, psiB)
    return np.kron(rho_A, rho_B)


def pure_random_entangled_rho(dA: int, dB: int, seed: int = 0) -> np.ndarray:
    """Random pure state |psi> in C^{dA*dB}, then rho = |psi><psi|.
    Reduced state rho_A has purity related to Schmidt spectrum.
    """
    rng = np.random.default_rng(seed)
    psi = rng.normal(size=dA * dB) + 1j * rng.normal(size=dA * dB)
    psi = psi / np.linalg.norm(psi)
    return np.outer(psi, psi.conj())


def random_pure_with_target_schmidt(dA: int, dB: int, lam: np.ndarray
                                    ) -> np.ndarray:
    """Build a pure state with prescribed Schmidt coefficients `lam`.
    Returns rho = |psi><psi|.
    """
    assert len(lam) <= min(dA, dB)
    lam = np.asarray(lam, dtype=float)
    lam = lam / np.linalg.norm(lam)
    psi = np.zeros(dA * dB, dtype=complex)
    for k, l in enumerate(lam):
        # |k>_A (x) |k>_B
        e = np.zeros(dA * dB); e[k * dB + k] = 1.0
        psi += l * e
    return np.outer(psi, psi.conj())


def partial_trace_B(rho: np.ndarray, dA: int, dB: int) -> np.ndarray:
    rho_t = rho.reshape(dA, dB, dA, dB)
    return np.einsum("ijkj->ik", rho_t)


def partial_trace_A(rho: np.ndarray, dA: int, dB: int) -> np.ndarray:
    rho_t = rho.reshape(dA, dB, dA, dB)
    return np.einsum("ijil->jl", rho_t)


def ch2_quantum(rho: np.ndarray, dA: int, dB: int) -> float:
    rho_A = partial_trace_B(rho, dA, dB)
    return float(1.0 - np.real(np.trace(rho_A @ rho_A)))


def vN(rho: np.ndarray) -> float:
    ev = np.linalg.eigvalsh(rho)
    ev = ev[ev > 1e-12]
    return float(-np.sum(ev * np.log(ev)))


def mutual_info(rho: np.ndarray, dA: int, dB: int) -> float:
    rho_A = partial_trace_B(rho, dA, dB)
    rho_B = partial_trace_A(rho, dA, dB)
    return vN(rho_A) + vN(rho_B) - vN(rho)


# ----------------------------- sweeps --------------------------------

def sweep_max_mixed():
    """Maximally mixed marginal on dA dims.  ch_2 = 1 - 1/dA.  This is
    the simplest place the threshold ch_2 = 0.95 appears: dA = 20 exact.
    """
    print(f"\n{'='*60}")
    print(" MAX-MIXED-MARGINAL SWEEP   ch_2 = 1 - 1/d_A")
    print(f"{'='*60}")
    print(f"{'d_A':>4} {'ch_2':>10} {'I(A:B)':>10} "
          f"{'log d_A':>10} {'>= 0.95?':>10}")
    rows = []
    for dA in [2, 3, 4, 5, 8, 10, 15, 20, 25, 32]:
        dB = max(dA, 2)
        rho = maximally_mixed_bipartite(dA, dB)
        c2 = ch2_quantum(rho, dA, dB)
        mi = mutual_info(rho, dA, dB)
        flag = "YES" if c2 >= 0.95 else "no"
        print(f"{dA:>4} {c2:>10.4f} {mi:>10.4f} "
              f"{math.log(dA):>10.4f} {flag:>10}")
        rows.append((dA, c2, mi))
    return rows


def sweep_schmidt_rank(dA: int = 20, dB: int = 20):
    """Vary Schmidt rank r from 1 (product) to min(dA,dB) (max entangled).
    Equal Schmidt coefficients 1/sqrt(r).  Then
        rho_A = (1/r) sum |k><k|  on r dims
        purity = 1/r
        ch_2   = 1 - 1/r
        I(A:B) = 2 * log r            (pure state)
    so a sharp prediction:  ch_2 >= 0.95  <=>  r >= 20  <=>  I >= 2 log 20.
    """
    print(f"\n{'='*60}")
    print(f" PURE-STATE SCHMIDT SWEEP  (d_A=d_B={dA})  equal coefficients")
    print(f"{'='*60}")
    print(f"{'rank r':>7} {'ch_2':>10} {'I(A:B)':>10} "
          f"{'2 log r':>10} {'>= 0.95?':>10}")
    rows = []
    for r in [1, 2, 4, 5, 10, 15, 19, 20, 21, 25]:
        if r > min(dA, dB):
            continue
        lam = np.ones(r)
        rho = random_pure_with_target_schmidt(dA, dB, lam)
        c2 = ch2_quantum(rho, dA, dB)
        mi = mutual_info(rho, dA, dB)
        flag = "YES" if c2 >= 0.95 else "no"
        print(f"{r:>7} {c2:>10.4f} {mi:>10.4f} "
              f"{2*math.log(r):>10.4f} {flag:>10}")
        rows.append((r, c2, mi))
    return rows


def sweep_werner_high_dim(d: int = 20):
    """Werner-class isotropic state on C^d (x) C^d:
        rho(p) = p |Phi+><Phi+| + (1-p) I/(d^2)
    where |Phi+> = (1/sqrt d) sum |kk>.

    Tr(rho_A^2) computed exactly:
        rho_A = p * I/d + (1-p) * I/d  = I/d  (always max mixed!)
    So ch_2(d) = 1 - 1/d for all p in [0,1] — independent of p, i.e.
    ch_2 SATURATES at the d-determined ceiling regardless of mixing.
    By contrast I(A:B) ranges over [0, 2 log d] as p: 0 -> 1.

    This is a CRITICAL DISTINCTION: ch_2 measures the *capacity* for
    correlated information (dimension-bounded), while Phi/I measures
    the *amount* actually carried.
    """
    print(f"\n{'='*60}")
    print(f" ISOTROPIC SWEEP (d={d}):  ch_2 vs Phi-proxy under mixing")
    print(f"{'='*60}")
    print(f"{'p':>6} {'ch_2':>10} {'I(A:B)':>10}")
    rows = []
    psi = np.zeros(d * d, dtype=complex)
    for k in range(d):
        psi[k * d + k] = 1.0 / math.sqrt(d)
    phi_proj = np.outer(psi, psi.conj())
    I_full = np.eye(d * d) / (d * d)
    for p in np.linspace(0, 1, 11):
        rho = p * phi_proj + (1 - p) * I_full
        c2 = ch2_quantum(rho, d, d)
        mi = mutual_info(rho, d, d)
        print(f"{p:>6.2f} {c2:>10.4f} {mi:>10.4f}")
        rows.append((p, c2, mi))
    return rows


# ----------------------------- main ----------------------------------

if __name__ == "__main__":
    print("=" * 60)
    print(" THRESHOLD-REGIME ANALYSIS")
    print("   ch_2 = 0.95  consciousness crystallization (Ch 6)")
    print(" Test what state-space conditions reach the threshold")
    print(" and how Phi (IIT proxy) behaves there.")
    print("=" * 60)

    r1 = sweep_max_mixed()
    r2 = sweep_schmidt_rank(dA=25, dB=25)
    r3 = sweep_werner_high_dim(d=20)

    # Sharp prediction summary
    print(f"\n{'='*60}")
    print(" SHARP FRAMEWORK PREDICTION  (derived here)")
    print(f"{'='*60}")
    print("""
For a bipartite quantum system A (x) B,
    ch_2 = 1 - Tr(rho_A^2)
attains 0.95 iff rho_A has purity Tr(rho_A^2) = 0.05,
which requires effective dimension d_A >= 20.

For pure |psi>_AB with equal Schmidt coefficients on rank r,
    ch_2 = 1 - 1/r,   I(A:B) = 2 log r
so  ch_2 >= 0.95  <=>  r >= 20  <=>  I(A:B) >= 2 log 20  ~ 5.991 nats
                                              ~ 8.644 bits.

Interpretation:
  - Tononi consciousness threshold (Phi > 0 in IIT 3.0): non-zero
    integrated information.  Lax: ANY irreducible correlation suffices.
  - Principia Fractalis threshold (ch_2 >= 0.95): >= ~8.6 BITS of
    mixed-marginal correlation across the subsystem cut.

These are NOT the same threshold:
  Phi    > 0     : *any* irreducibility, ZERO bits possible (just non-empty)
  ch_2 >= 0.95 : ~8.6 bits minimum, dimension >= 20

But they AGREE on direction (monotone within fixed dim, see sweep above).
""")
