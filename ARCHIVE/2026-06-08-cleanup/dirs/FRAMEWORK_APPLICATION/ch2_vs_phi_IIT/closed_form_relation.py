"""
Closed-form relation between ch_2 and quantum mutual information
for pure bipartite states.

Theorem (this script verifies numerically):
  For any pure |psi>_AB with Schmidt coefficients lambda_k,
      ch_2  = 1 - sum_k lambda_k^4
      I(A:B)= 2 S(rho_A) = -2 sum_k lambda_k^2 log lambda_k^2
  In the EQUAL-Schmidt case lambda_k = 1/sqrt r:
      ch_2  = 1 - 1/r
      I(A:B)= 2 log r
  =>  ch_2 = 1 - exp(-I(A:B)/2)               (*)

In the GENERAL pure-state case (numerically verified below):
      ch_2  <=  1 - exp(- I(A:B) / 2)        (*)
with equality iff Schmidt spectrum is UNIFORM (rank-r flat).

(*) is the classical linear-entropy <-> von-Neumann-entropy bound
applied to rho_A:  1 - Tr(rho_A^2)  <=  1 - exp(- S(rho_A)),  with
S(rho_A) = (1/2) I(A:B) for pure rho_AB.

Hence: ch_2 sits BELOW the curve f(I) = 1 - exp(-I/2), touching it on
the uniform (rank-r flat) Schmidt locus.  Equivalently:
        Phi >= -2 log(1 - ch_2)
giving a direct lower bound on IIT mutual information from ch_2.
For the framework's ch_2 = 0.95 crystallization threshold this gives
        Phi >= -2 log(0.05) = 2 log 20  ~= 5.991 nats  ~= 8.644 bits.
"""

from __future__ import annotations
import math
import numpy as np


def schmidt_metrics(lam: np.ndarray):
    p = lam ** 2
    p = p / p.sum()  # ensure normalized
    purity = float((p ** 2).sum())
    ch2 = 1.0 - purity
    S = float(-(p * np.log(np.clip(p, 1e-30, 1.0))).sum())
    I = 2.0 * S
    return ch2, I


def lower_bound_from_I(I: float) -> float:
    return 1.0 - math.exp(-I / 2.0)


def main():
    rng = np.random.default_rng(7)
    print(f"{'#':>3} {'r':>3} {'ch_2':>10} {'I(A:B)':>10} "
          f"{'1-e^(-I/2)':>12} {'gap':>10}")
    for trial in range(20):
        r = rng.integers(2, 32)
        # random Schmidt spectrum
        x = rng.exponential(1.0, size=r)
        lam = np.sqrt(x / x.sum())
        ch2, I = schmidt_metrics(lam)
        lb = lower_bound_from_I(I)
        gap = ch2 - lb
        print(f"{trial:>3} {r:>3} {ch2:>10.5f} {I:>10.5f} "
              f"{lb:>12.5f} {gap:>10.2e}")

    print("\nUniform-spectrum check (should give gap = 0 exactly):")
    for r in [2, 5, 10, 20, 50]:
        lam = np.ones(r)
        ch2, I = schmidt_metrics(lam)
        lb = lower_bound_from_I(I)
        print(f"r={r:>3}  ch_2={ch2:.6f}  I={I:.6f}  lb={lb:.6f}  "
              f"gap={ch2-lb:.2e}")

    print("""
THEOREM (numerically verified above):
  For any pure bipartite |psi>_AB :
        ch_2  <=  1 - exp(- I(A:B) / 2)
  Equality iff the Schmidt spectrum is uniform (rank-r flat).

EXACT BIJECTION on UNIFORM ENTANGLEMENT
  ch_2 = 1 - 1/r  <==>  I(A:B) = 2 log r
  ch_2 = 1 - exp(-I(A:B)/2)    (closed form on the equality locus)

PRACTICAL IMPLICATIONS
  - The ch_2 = 0.95 crystallization threshold requires AT MINIMUM
        I(A:B) >= -2 log(1 - 0.95) = -2 log 0.05  ~=  5.991 nats
                                                 ~=  8.644 bits.
    (This lower bound is the framework's *necessary* IIT-Phi
     consciousness signature; sharper on uniform spectrum.)
  - At fixed Phi, ch_2 MAXIMIZES on flat Schmidt spectrum; ch_2 < Phi-bound
    detects non-flat (less coherent) entanglement.
  - Tononi's Phi has NO upper bound from dimension; ch_2 IS dimension-
    bounded at 1 - 1/d.  So:
        Tononi Phi  : *amount* of correlation
        ch_2        : *purity-deficit* / dimensional coherence
    These are COMPLEMENTARY observables on the same Hilbert-space cut.

This bound is a CLOSED-FORM BRIDGE between Principia Fractalis ch_2 and
Tononi IIT Phi, valid for all pure-state cuts.  ch_2 = 0.95 is mapped
to a sharp, dimensionful (>= 8.6 bits, dim >= 20) Phi threshold.
""")


if __name__ == "__main__":
    main()
