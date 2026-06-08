"""
RH_REFORM_V4_SIGNIFICANCE.PY  —  Final honesty test.

Question: Is the Z_3 phase coupling making the eigenvalues MOVE TOWARD
zeta zeros from the BK Weyl-law baseline, or is it just neutral noise
that happens to leave the eigenvalues near BK ladder positions?

Method:
  (1) Compute residual r_k = eig_k(Arch_A) - eig_k(Arch_B_baseline)
      and compare against target residual t_k - eig_k(Arch_B).
      If Z_3 phase is doing work: r_k correlates with target residual.
      If not: r_k is essentially zero or uncorrelated.
  (2) Repeat with random phases (Arch_E) — if the magnitude of r_k is
      similar to Arch_E, the framework Z_3 isn't doing special work.
  (3) Compute Pearson correlation between r_k (Arch_A) and target.

Also test: averaging over 100 random-phase realizations (Arch_E_ensemble)
gives the mean random-coupling shift. Compare Z_3 against that ensemble.
"""

import numpy as np
from mpmath import zetazero
import json
import time

PI_NP = np.pi


def D3(n):
    s = 0
    while n > 0:
        s += n % 3; n //= 3
    return s


def phi_phase_np(n):
    th = 2.0 * PI_NP * D3(n) / 3.0
    return complex(np.cos(th), np.sin(th))


def D_BK(n):
    return 2.0 * PI_NP * n / np.log(n + 2.0)


def build_TN_full(N, off_kind="Z3", seed=0):
    """BK diagonal + chosen off-diagonal coupling at ch_2=0.95 (Hermitian)."""
    rng = np.random.default_rng(seed)
    T = np.zeros((N, N), dtype=np.complex128)
    for n in range(1, N + 1):
        i = n - 1
        T[i, i] = D_BK(n)
        if n + 1 <= N and off_kind != "zero":
            c_n = 1.0 / np.log(n + 2.0)
            sqrt_c = np.sqrt(c_n)
            if off_kind == "Z3":
                phin = phi_phase_np(n)
            elif off_kind == "rand":
                ang = 2 * PI_NP * rng.random()
                phin = complex(np.cos(ang), np.sin(ang))
            else:
                raise ValueError
            T[i, i + 1] = phin * sqrt_c
            T[i + 1, i] = np.conj(phin) * sqrt_c
    return T


def top_eigs(T, K=15):
    eigs = np.linalg.eigvalsh(0.5 * (T + T.conj().T))
    re = np.sort(eigs)
    pos = re[re > 0.5]
    return pos[:K]


def main():
    t0 = time.time()
    print("=" * 86)
    print("RH REFORM V4 — Is Z_3 phase doing real work or just decorating BK?")
    print("=" * 86)

    zz = np.array([float(zetazero(k).imag) for k in range(1, 16)])

    N = 400
    print(f"\nN = {N}")

    T_z3 = build_TN_full(N, off_kind="Z3")
    T_bk = build_TN_full(N, off_kind="zero")
    eigs_z3 = top_eigs(T_z3, K=15)
    eigs_bk = top_eigs(T_bk, K=15)

    # Residuals
    r_z3 = eigs_z3 - eigs_bk
    target_residual = zz[:15] - eigs_bk

    print(f"\n  {'k':>3} {'t_k':>8} {'BK':>8} {'Z3':>8} {'Z3-BK':>10} {'target-BK':>10} {'helpful?':>10}")
    for k in range(15):
        helpful = "yes" if (r_z3[k] * target_residual[k] > 0) else "no"
        print(f"  {k+1:3d} {zz[k]:8.3f} {eigs_bk[k]:8.3f} {eigs_z3[k]:8.3f} "
              f"{r_z3[k]:+10.4f} {target_residual[k]:+10.4f} {helpful:>10}")

    # Pearson correlation
    corr = float(np.corrcoef(r_z3, target_residual)[0, 1])
    print(f"\n  Pearson corr(Z3 residual, target residual) = {corr:+.4f}")
    print(f"  (Positive => Z3 is pushing eigs toward zeta zeros;")
    print(f"   ~0 => Z3 has no zeta-relevant signal; negative => Z3 pushes AWAY)")

    # Random-phase ensemble
    print(f"\n  Random-phase ensemble (100 seeds): magnitude of r_rand vs r_z3")
    rand_corrs = []
    rand_norms = []
    for s in range(100):
        T_r = build_TN_full(N, off_kind="rand", seed=s)
        eigs_r = top_eigs(T_r, K=15)
        r_r = eigs_r - eigs_bk
        rand_norms.append(float(np.linalg.norm(r_r)))
        rand_corrs.append(float(np.corrcoef(r_r, target_residual)[0, 1]))
    rand_norms = np.array(rand_norms)
    rand_corrs = np.array(rand_corrs)
    z3_norm = float(np.linalg.norm(r_z3))

    print(f"  ||r_Z3||  = {z3_norm:.4f}")
    print(f"  ||r_rand|| stats: mean={rand_norms.mean():.4f}  std={rand_norms.std():.4f}  "
          f"min={rand_norms.min():.4f}  max={rand_norms.max():.4f}")
    print(f"  Random-phase corr stats: mean={rand_corrs.mean():+.4f}  std={rand_corrs.std():.4f}  "
          f"min={rand_corrs.min():+.4f}  max={rand_corrs.max():+.4f}")
    pct_better_z3 = float(np.mean(rand_corrs < corr) * 100)
    print(f"  Fraction of random seeds with WORSE corr than Z3: {pct_better_z3:.1f}%")

    # Quality metric: SSE to zeta zeros
    sse_z3 = float(np.sum((eigs_z3 - zz[:15])**2))
    sse_bk = float(np.sum((eigs_bk - zz[:15])**2))
    sse_rand = np.array([
        float(np.sum((top_eigs(build_TN_full(N, off_kind="rand", seed=s), K=15) - zz[:15])**2))
        for s in range(100)
    ])
    print(f"\n  SSE (sum sq err) to zeta zeros:")
    print(f"    BK only: {sse_bk:.4f}")
    print(f"    Z_3:     {sse_z3:.4f}  ({'BETTER' if sse_z3 < sse_bk else 'WORSE'} than BK)")
    print(f"    rand:    mean={sse_rand.mean():.4f}  min={sse_rand.min():.4f}  max={sse_rand.max():.4f}")
    pct_rand_worse_than_z3 = float(np.mean(sse_rand > sse_z3) * 100)
    print(f"  Fraction of random seeds with WORSE SSE than Z_3: {pct_rand_worse_than_z3:.1f}%")

    out = {
        "N": N,
        "z3_eigs": eigs_z3.tolist(),
        "bk_eigs": eigs_bk.tolist(),
        "zeta_zeros": zz.tolist(),
        "z3_residual": r_z3.tolist(),
        "target_residual": target_residual.tolist(),
        "pearson_z3_target": corr,
        "z3_residual_norm": z3_norm,
        "rand_residual_norm_mean": float(rand_norms.mean()),
        "rand_residual_norm_std": float(rand_norms.std()),
        "rand_corr_mean": float(rand_corrs.mean()),
        "rand_corr_std": float(rand_corrs.std()),
        "fraction_random_worse_corr_than_z3": pct_better_z3,
        "sse_bk": sse_bk,
        "sse_z3": sse_z3,
        "sse_rand_mean": float(sse_rand.mean()),
        "sse_rand_min": float(sse_rand.min()),
        "sse_rand_max": float(sse_rand.max()),
        "fraction_random_worse_sse_than_z3": pct_rand_worse_than_z3,
    }

    outpath = "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/RH_reformulation/rh_reform_v4_significance.json"
    with open(outpath, "w") as f:
        json.dump(out, f, indent=2, default=str)
    print(f"\nElapsed: {time.time() - t0:.1f} s")
    print(f"Saved: {outpath}")


if __name__ == "__main__":
    main()
