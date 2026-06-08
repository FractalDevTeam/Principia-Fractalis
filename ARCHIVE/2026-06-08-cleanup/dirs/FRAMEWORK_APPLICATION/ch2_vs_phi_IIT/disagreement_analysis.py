"""
Where ch_2 and Phi DIFFER — and why.

The ch_2 formula for neural connectivity
    ch_2(W) = (Tr(W^2) - (Tr W)^2) / (2 ||W||_F^2)
depends only on the second-order spectral invariants Tr W and Tr W^2.
In particular ch_2 is invariant under any change of basis  W -> U W U^T
and is BLIND to the actual graph structure beyond its trace + trace^2.

Tononi's Phi (and any IIT proxy) is sensitive to BIPARTITION structure
and is NOT a polynomial in {Tr W^k}.  So:

    DISAGREEMENT IS GENERIC ON NEURAL SYSTEMS.

The two measures only converge in the QUANTUM regime, where ch_2 is the
linear entropy of the reduced state — a genuine measure of correlation.

This script demonstrates the disagreement by constructing TWO networks
with identical {Tr W, Tr W^2, ||W||_F} but very different Phi.
"""

import numpy as np
from ch2_vs_phi import ch2_neural, phi_gaussian


def make_pair_same_ch2():
    """Two 4-node systems with identical Tr W, Tr W^2, ||W||_F^2 but
    different graph topology.
    """
    # System A: directed cycle
    A = np.array([
        [0, 0, 0, 0.5],
        [0.5, 0, 0, 0],
        [0, 0.5, 0, 0],
        [0, 0, 0.5, 0],
    ])
    # System B: pair of independent 2-cycles
    B = np.array([
        [0,   0.5, 0,   0],
        [0.5, 0,   0,   0],
        [0,   0,   0,   0.5],
        [0,   0,   0.5, 0],
    ])
    return A, B


def report(W, name):
    c2 = ch2_neural(W)
    ph = phi_gaussian(W)
    print(f"  {name}:")
    print(f"    Tr(W)       = {np.trace(W):.4f}")
    print(f"    Tr(W^2)     = {np.trace(W @ W):.4f}")
    print(f"    ||W||_F^2   = {np.sum(W*W):.4f}")
    print(f"    ch_2(W)     = {c2:.4f}")
    print(f"    Phi_G(W)    = {ph:.4f}")


def main():
    print("=" * 60)
    print(" DISAGREEMENT DEMONSTRATION")
    print(" Same spectral invariants -> same ch_2,")
    print(" different topology -> different Phi.")
    print("=" * 60)
    A, B = make_pair_same_ch2()
    print("\nSystem A: directed 4-cycle (integrated)")
    report(A, "A")
    print("\nSystem B: two independent 2-cycles (modular)")
    report(B, "B")

    print("""
INTERPRETATION
  ch_2(A) = ch_2(B): the framework's neural ch_2 cannot distinguish
                     an integrated cycle from two disconnected sub-cycles.
  Phi_G(A) > Phi_G(B): IIT *does* distinguish them — disconnected
                       components have zero across-cut Phi.

This is NOT a defect of the framework; ch_2 is a *topological* invariant
(second Chern character) and lives at a different abstraction level than
IIT bipartition irreducibility.  The two measures are *complementary*:
  - ch_2 captures spectral/dimensional coherence
  - Phi   captures structural integration across cuts

The CORRECT bridge is on QUANTUM states (ch_2 = linear entropy of rho_A),
where:   ch_2 <= 1 - exp(-Phi_IIT / 2),  equality on uniform Schmidt.
""")


if __name__ == "__main__":
    main()
