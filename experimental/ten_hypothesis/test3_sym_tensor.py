"""
Test 3: Operator on T^2_{sym}(R^4) — 10-dimensional space of 4x4 symmetric tensors.

We construct natural rank-2 symmetric-tensor operators on R^4 and look for any
spectrum involving pi/10.

Setup:
- Space V = Sym^2(R^4) ~ R^10 (basis: e_i e_j with i <= j)
- Natural operators:
  (1) Casimir of SO(4) acting on Sym^2 -> eigenvalues are quadratic in highest weights
  (2) Trace operator + traceless splitting (V = R . delta + symmetric traceless)
  (3) "Resonance" operator: K_ij,kl = cos(pi * (i+j+k+l)/10) / 10 -- ad hoc but tests if 10 emerges

The test: do any natural eigenvalues involve pi/10?
"""

import numpy as np
from mpmath import mp, pi
from scipy.linalg import eigh

mp.dps = 50

def sym2_basis():
    """Return list of (i, j) pairs with i <= j for Sym^2(R^4), R^4 indexed 0..3."""
    return [(i, j) for i in range(4) for j in range(i, 4)]

def casimir_sym2():
    """Casimir operator on Sym^2(R^4) acts as a multiple of identity within each irrep.
    Sym^2(R^4) decomposes as (5,5) (traceless symmetric, 9-dim) + scalar (trace, 1-dim).

    For SO(4), Casimir on a rep with weights (a, b) is a(a+1) + b(b+1)... rough.
    Let's just diagonalize trace-and-traceless splitting.
    """
    basis = sym2_basis()
    d = len(basis)  # 10
    # Trace projector: P_trace contributes to (i, i) entries
    P = np.zeros((d, d))
    trace_vec = np.array([1.0 if i == j else 0.0 for (i, j) in basis])
    trace_vec /= np.linalg.norm(trace_vec)
    P = np.outer(trace_vec, trace_vec)
    return P  # rank-1 projector onto trace direction

def resonance_op(use_pi_10=True):
    """Build K_{(ij),(kl)} = cos(pi * (i+j+k+l + 1) / 10) / 10."""
    basis = sym2_basis()
    d = len(basis)
    K = np.zeros((d, d))
    for a, (i, j) in enumerate(basis):
        for b, (k, l) in enumerate(basis):
            if use_pi_10:
                K[a, b] = np.cos(np.pi * (i + j + k + l + 1) / 10) / 10
            else:
                K[a, b] = np.cos(np.pi * (i + j + k + l + 1) / 12) / 12
    return K

def main():
    print("=" * 70)
    print("TEST 3: Operators on Sym^2(R^4) — 10-dimensional space")
    print("=" * 70)
    print()
    print(f"dim Sym^2(R^4) = {len(sym2_basis())}")

    # Diagonalize a natural kernel
    K10 = resonance_op(use_pi_10=True)
    eigs10 = np.sort(eigh(K10, eigvals_only=True))
    print()
    print("Eigenvalues of K (pi/10 kernel):")
    for e in eigs10:
        print(f"  {e:+.8f}    ratio to pi/10: {e / (np.pi/10):+.6f}")

    K12 = resonance_op(use_pi_10=False)
    eigs12 = np.sort(eigh(K12, eigvals_only=True))
    print()
    print("Eigenvalues of K (pi/12 kernel) — control:")
    for e in eigs12:
        print(f"  {e:+.8f}    ratio to pi/12: {e / (np.pi/12):+.6f}")

    # Does the ground state of K10 give pi/10? Test:
    pi10 = np.pi / 10
    print()
    print(f"pi/10 = {pi10:.8f}")
    print(f"Largest |eig| of K10 = {np.max(np.abs(eigs10)):.8f}")
    print()
    print("VERDICT: This is a hand-crafted test. The presence of pi/10")
    print("in the eigenvalues is an artifact of the kernel definition,")
    print("NOT a natural emergent constant from the symmetric-tensor structure.")
    print("A true emergence would require pi/10 from the SO(4) representation theory,")
    print("which does not contain pi as an eigenvalue (Casimir eigenvalues are rationals).")

if __name__ == "__main__":
    main()
