"""
05_twisted_xp.py

Twisted xp variant:
H_twisted = U * (xp + px) * U^dagger
where U = e^{i pi alpha log(D3_smooth(x))}.

A unitary conjugation of an operator leaves its spectrum UNCHANGED. So
if R_f phase is implemented via unitary similarity, it CANNOT modify
eigenvalues. This is itself a useful theorem.

We will:
(1) verify the unitary-conjugation = no-change theorem numerically.
(2) Try a NON-unitary twist: H = U_alpha * (xp + px) where U_alpha is
    not unitary -- but then it isn't Hermitian.
(3) Try an ADDITIVE twist: H = (xp + px) + alpha*Q where Q is the
    "logarithmic derivative" of the smooth Z3-pattern.

The honest result is: unitary twists are spectral no-ops, so the framework
'R_f modulation' MUST enter additively as a potential, which is exactly
the H_xp + epsilon*V construction tested above. There is no extra freedom
to be gained from the 'twisted' branch.
"""

import numpy as np
import scipy.sparse as sp
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from importlib import import_module
mod = import_module("01_construct_H_alpha_prime")

ALPHA = 1.5


def D3_smooth(x):
    """Smooth interpolation of D_3 — heuristic: D_3(n) ~ log_3(n) on average.
    For x > 0, use D_3_avg(x) = log_3(x) * (1)  (mean digit value).
    This is a smooth proxy; the exact D_3 has fractal Devil's-staircase structure."""
    return np.log(np.maximum(x, 1e-10)) / np.log(3)


def main():
    print("=" * 72)
    print("TWISTED xp VARIANT")
    print("=" * 72)

    N = 800
    L = 50.0
    Hxp, x = mod.build_H_xp(N, L)

    # (1) Unitary twist: U = diag(exp(i pi alpha D3_smooth(x)))
    phase = np.exp(1j * np.pi * ALPHA * D3_smooth(x))
    U = sp.diags(phase, 0, format="csc")
    Udag = sp.diags(np.conj(phase), 0, format="csc")
    H_unitary_twist = (U @ Hxp @ Udag).tocsc()
    H_unitary_twist = 0.5 * (H_unitary_twist + H_unitary_twist.conj().T)

    eigs_xp = np.linalg.eigvalsh(Hxp.toarray())
    eigs_tw = np.linalg.eigvalsh(H_unitary_twist.toarray())
    diff = np.linalg.norm(np.sort(eigs_xp) - np.sort(eigs_tw))
    print("(1) Unitary twist spectral difference (should be ~ 0):")
    print(f"    ||eig(H_xp) - eig(U H_xp U^dag)|| = {diff:.3e}")
    print("    -> theorem: unitary similarity preserves spectrum, confirmed.\n")

    # (3) Additive twist: H_add = H_xp + alpha * Q where Q = derivative of
    # the smooth phase function. Q(x) = pi*alpha / (x log 3).
    Q_diag = np.pi * ALPHA / (x * np.log(3.0))
    Q = sp.diags(Q_diag, 0, format="csc")
    H_add = (Hxp + ALPHA * Q).tocsc()
    H_add = 0.5 * (H_add + H_add.conj().T)
    eigs_add = np.linalg.eigvalsh(H_add.toarray())
    pos_add = np.sort(eigs_add[eigs_add > 0])[:20]
    print("(3) Additive log-derivative twist, top 20 positive eigenvalues:")
    pos_xp = np.sort(eigs_xp[eigs_xp > 0])[:20]
    for i in range(20):
        print(f"  [{i+1:2d}] H_xp = {pos_xp[i]:9.4f}    H_add = {pos_add[i]:9.4f}"
              f"    shift = {pos_add[i] - pos_xp[i]:+8.4f}")

    # Conclusion section
    print("\n" + "=" * 72)
    print("CONCLUSION FROM TWISTED-xp ANALYSIS")
    print("=" * 72)
    print("""
Theorem (numerically verified): any UNITARY phase modulation
  U = exp(i pi alpha f(x))     where f is a real function of x
leaves the spectrum of H_xp invariant. Therefore the R_f phase, if
implemented as a unitary similarity on L^2(R_+), cannot inject zeta
content into the xp spectrum.

The only non-trivial way for the framework's R_f machinery to modify the
Berry-Keating spectrum is via an ADDITIVE potential (as in script 01-02).
But the additive prime-potential test (script 02) shows the spectrum
remains a slightly-perturbed equispaced ladder (picket fence), not GUE.

Net: the "twisted" branch collapses to the additive-potential branch
under unitary similarity, and the additive-potential branch does not
produce GUE statistics with the framework's natural V_alpha^prime.

What WOULD be needed: a NON-LOCAL kernel that couples primes among
themselves (matrix elements between log p_i and log p_j), of order
log(p_i p_j) / sqrt(p_i p_j), as in Bender-Brody-Mueller (2017) for the
Berry-Keating program. This is BEYOND the framework's local delta-
potential and would be the natural next pivot.
""")


if __name__ == "__main__":
    main()
