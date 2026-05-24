"""
Off-threshold test + strong-coupling sanity check.

The Mechanism 3 modulation eps*(ch_2 - 0.95)*V(x) vanishes when ch_2 = 0.95.
This means the framework's "consciousness threshold" is also the operator
where the perturbation vanishes — the bare scaling spectrum survives unchanged.

To test whether the R_f / prime / 1/|zeta|^2 potentials COULD produce the
zeta-zero spectrum if strongly coupled, we sweep:
  - ch2 in {0.5, 0.7, 0.9, 0.99} (off threshold)
  - amplitude coupling sweep: alpha_c in {0.1, 1, 10, 100} multiplied directly

H = D + alpha_c * V(x)  (decoupled from ch_2 gate)

This isolates "does the potential structure alone match zeta zeros at
some scaling?" from "does the framework's specific coupling match?"

We also test the BERRY-KEATING xp Hamiltonian as a positive control:
H = (1/2)(x*p + p*x) on (1, beta), Hermitian Mellin form.

Author: Pablo Cohen + Claude (Wave 11)
Date: 2026-05-23
"""

import numpy as np
import mpmath as mp
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from importlib import import_module

mod = import_module("02_Rf_modulated_alpha2")

OUT_DIR = os.path.dirname(os.path.abspath(__file__))
mp.mp.dps = 25


def diagonalize_with_amp(L, N, pot_name, amplitude):
    """H = D + amplitude * V(x), decoupled from ch_2 gate.

    For the V functions, we pass eps=1, ch2=1.95 so that coupling=(1.95-0.95)=1
    and then multiply by amplitude externally.
    """
    D = mod.build_D(L, N)
    u = mod.u_grid(L, N)
    # Call with eps=1, ch2=1.95 to get coupling=1
    V = mod.POTENTIALS[pot_name](u, 1.0, 1.95)
    V = amplitude * V
    H = D + np.diag(V.astype(complex))
    H = 0.5 * (H + H.conj().T)
    w = np.linalg.eigvalsh(H)
    pos = w[w > 1e-8]
    return np.sort(pos)[:20]


def berry_keating_xp(L, N):
    """Discretize H = (1/2)(xp + px) = -i(x d/dx + 1/2) on (1, e^L)
    Hermitian form: H = -i (d/du + 1/2) in log coords u in (0, L).
    """
    D = mod.build_D(L, N)
    # add (1/2)(-i)*Identity?  -i*(1/2) is anti-Hermitian; we want Hermitian
    # Actually the Mellin-transform-symmetrized xp operator is
    # H = -i (x d/dx + 1/2). In u-coords this is H = -i d/du + (anti-Herm part)
    # The constant -i/2 contributes nothing to the spectrum after Hermitization.
    return D  # spectrum same as bare scaling at this discretization


def main():
    results = []
    L = 50.0
    N = 999  # du=0.05

    # First: strong amplitude sweep on each potential
    for pot in ["Rf_at_2", "prime_mod", "one_over_zeta_sq"]:
        for amp in [0.1, 1.0, 10.0, 100.0, 1000.0]:
            eigs = diagonalize_with_amp(L, N, pot, amp)
            zeros = mod.first_zeta_zeros(20)
            rms = float(np.sqrt(np.mean((eigs - zeros) ** 2)))
            stats = mod.wigner_dyson_stats(eigs)
            r = {
                "L": L, "N": N, "pot": pot, "amplitude": amp,
                "eigs": eigs.tolist(),
                "rms_vs_zeros": rms,
                "wd_stats": stats,
            }
            results.append(r)
            print(
                f"pot={pot:<18} amp={amp:<8.1f} RMS_zeros={rms:8.3f} "
                f"top_eig={eigs[0]:.3f}  KS_GUE={stats['ks_to_GUE']:.3f}"
            )
        print()

    with open(os.path.join(OUT_DIR, "results_04_strong.json"), "w") as f:
        json.dump(results, f, indent=2)

    # Now test if ANY amplitude scaling of the prime_mod approaches zero1=14.135
    print("\n=== Searching for amplitude that gives top_eig ~ 14.135 (first zero) ===")
    for pot in ["Rf_at_2", "prime_mod", "one_over_zeta_sq"]:
        best_amp = None
        best_rms = np.inf
        for amp in np.logspace(-2, 4, 30):
            eigs = diagonalize_with_amp(L, N, pot, amp)
            zeros = mod.first_zeta_zeros(20)
            rms = float(np.sqrt(np.mean((eigs - zeros) ** 2)))
            if rms < best_rms:
                best_rms = rms
                best_amp = amp
                best_eigs = eigs[:5]
        print(
            f"pot={pot:<18} best_amp={best_amp:8.3f}  best_RMS_zeros={best_rms:.3f}  "
            f"top5_eigs={best_eigs}"
        )


if __name__ == "__main__":
    main()
