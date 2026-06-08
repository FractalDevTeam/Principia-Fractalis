"""
Sanity check: is the apparent C_sandwich "hit" a structural feature
or merely an artifact of choosing eps=0.1 so that the eps^2 = 0.01 scaling
puts SOME eigenvalue near 0.22?

For C(eps) = eps^2 * V P V, eigenvalues scale as eps^2.
So spec(C(eps)) = eps^2 * spec(V P V).

If we vary eps continuously, SOME eigenvalue will pass through any target value.
The question: is the *lowest* eigenvalue at a CANONICAL eps (independent of the target)
equal to pi/(10*alpha)?

We test by:
1. computing all eigenvalues of V P V (eps=1) at alpha=sqrt2, k=3,
2. listing the closest match to pi/(10*alpha) and checking if eps=0.1 was tuned
   to land that specific eigenvalue on the target.
"""
import numpy as np
from mellin_twisted import (V_alpha, momentum_operator, build_grid, diag_V,
                            construction_c_sandwich, diagonalize, find_closest)

for aname, alpha, target in [("sqrt2", np.sqrt(2.0), np.pi/(10*np.sqrt(2.0))),
                              ("3/2",   1.5,           np.pi/15),
                              ("2",     2.0,           np.pi/20)]:
    for k in [1, 2, 3, 4]:
        L = k * np.log(alpha)
        # eps=1 reference spectrum
        M, _ = construction_c_sandwich(alpha, 1.0, L, 800)
        w = diagonalize(M, k=20)
        pos = w[w > 1e-10]
        # The lowest positive eigenvalue at eps=1
        low_pos = float(np.min(pos)) if len(pos) else None
        # If we use eps=0.1, the lowest pos becomes 0.01 * low_pos
        rescaled_low = 0.01 * low_pos if low_pos else None
        # What eps would put the lowest positive eigenvalue exactly at target?
        # eps^2 * low_pos = target  => eps = sqrt(target/low_pos)
        if low_pos and low_pos > 0:
            eps_required = np.sqrt(target / low_pos)
        else:
            eps_required = None
        print(f"alpha={aname:5s} k={k} target={target:.5f}: "
              f"lowest_pos(eps=1)={low_pos:.5f}  "
              f"rescaled_eps=0.1: {rescaled_low:.5f}  "
              f"eps_to_hit_target_with_LOWEST_pos: {eps_required}")
