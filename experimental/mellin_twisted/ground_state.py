"""
GROUND STATE TEST: lambda_0 must be the LOWEST positive eigenvalue,
not "some eigenvalue near the target".

For each construction, sweep eps over a wide range and ask:
  Does the LOWEST positive eigenvalue ever sit at pi/(10*alpha) ?

If yes — for what eps, and is that eps a 'natural' constant?
If no for all eps — the construction does not realize the universal identity
                    as a ground state.
"""
import numpy as np
from mellin_twisted import (construction_a_additive, construction_b_multiplicative,
                             construction_c_sandwich, construction_d_sturm_liouville,
                             diagonalize)


def lowest_positive(M):
    w = diagonalize(M, k=20)
    pos = w[w > 1e-10]
    return float(np.min(pos)) if len(pos) else None


def sweep_eps(constr, alpha, k, eps_grid, N=600):
    L = k * np.log(alpha)
    lows = []
    for eps in eps_grid:
        try:
            M, _ = constr(alpha, eps, L, N)
            lows.append(lowest_positive(M))
        except Exception as e:
            lows.append(None)
    return np.array([np.nan if x is None else x for x in lows])


def best_eps(eps_grid, lows, target):
    valid = np.isfinite(lows)
    if not np.any(valid):
        return None, None, None
    err = np.abs(lows[valid] - target)
    idx = np.argmin(err)
    eps_v = eps_grid[valid][idx]
    val_v = lows[valid][idx]
    return eps_v, val_v, val_v - target


def main():
    eps_grid = np.geomspace(1e-3, 1e2, 60)
    constructions = [
        ("A_additive",        construction_a_additive),
        ("B_multiplicative",  construction_b_multiplicative),
        ("C_sandwich",        construction_c_sandwich),
        ("D_sturm_liouville", construction_d_sturm_liouville),
    ]
    ALPHA = [("sqrt2", np.sqrt(2.0), np.pi/(10*np.sqrt(2.0))),
             ("3/2",   1.5,           np.pi/15),
             ("2",     2.0,           np.pi/20)]

    print("=== Ground-state hit search: does the LOWEST POSITIVE eigenvalue ever hit pi/(10 alpha)? ===")
    for cname, cfunc in constructions:
        for aname, alpha, target in ALPHA:
            for k in [1, 2, 3, 4]:
                lows = sweep_eps(cfunc, alpha, k, eps_grid)
                eps_v, val_v, dv = best_eps(eps_grid, lows, target)
                if eps_v is None:
                    print(f"  {cname:20s} alpha={aname:5s} k={k}: NO POSITIVE EIGENVALUES ANYWHERE")
                    continue
                rel = abs(dv) / target * 100
                marker = " <- ground state hit (<2%)" if rel < 2.0 else ""
                print(f"  {cname:20s} alpha={aname:5s} k={k}: "
                      f"best eps={eps_v:.4g} gives lowest_pos={val_v:.5f} "
                      f"(target {target:.5f}, gap {rel:.2f}%){marker}")


if __name__ == "__main__":
    main()
