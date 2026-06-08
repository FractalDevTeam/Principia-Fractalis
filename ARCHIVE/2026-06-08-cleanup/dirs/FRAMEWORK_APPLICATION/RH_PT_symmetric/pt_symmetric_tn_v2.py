"""
PT_SYMMETRIC_TN_V2.PY  —  Revised PT-symmetric T_N construction.

v1 finding: PT-constraint L_i = conj(U_{N-2-i}) makes the operator
non-Hermitian generically (even at ch_2 = 0.95) because U is NOT
palindromic.  Eigenvalues come in complex-conjugate pairs (PT-broken
phase) because Z_3 phases destroy palindromicity.

v2 strategy: SYMMETRIZE the coupling magnitudes and use the framework
phases as a controlled PT-perturbation.  Three constructions:

  (A) "PT-canonical":
      U_i = sqrt(c_i_sym) * exp(i theta_i)
      where c_i_sym = c_i_sym is palindromic and theta_i = i alpha sin(2 pi D_3(i)/3)
      (real angle) with gain/loss strength i gamma (eps * (ch_2 - 0.95)).
      Sub-diag: L_i = conj(U_{N-2-i}).
      Reduces EXACTLY to Hermitian at ch_2 = 0.95 if we use palindromic
      magnitude and pure-imaginary perturbation.

  (B) "Bender-Boettcher gain/loss":
      Standard PT-construction: real-symmetric tridiagonal magnitudes
      plus DIAGONAL gain/loss D_k = D_BK(k) + i gamma * sign(k - N/2)
      with PT-pairing  D_k = conj(D_{N+1-k}).  This is the textbook
      PT-symmetric tight-binding model.  gamma = eps * (ch_2 - 0.95).

  (C) "Framework-driven":
      Off-diagonal real magnitudes; Z_3 phases injected as PURELY
      IMAGINARY off-diagonal asymmetry:
        U_i = sqrt(c_i_sym) + i * gamma * D_3(i)
        L_i = sqrt(c_i_sym) - i * gamma * D_3(N-1-i)
      so PT-constraint forces palindromic D_3 pattern (D_3(i) ?= D_3(N-1-i)?
      No -- so we ENFORCE PT by using  L_i = conj(U_{N-2-i}).

The cleanest physical PT model is (B); the framework injection is (C);
(A) is hybrid.  All three are run.

Author: Claude Opus 4.7 (1M)
Date  : 2026-05-23
"""

import numpy as np
from numpy.linalg import eigvals
import json
import os
import time
from mpmath import zetazero

PI = np.pi
OUTDIR = "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/RH_PT_symmetric"


# -- Framework primitives ---------------------------------------------------
def D3(n):
    s = 0
    while n > 0:
        s += n % 3; n //= 3
    return s


def D_BK(n):
    return 2.0 * PI * n / np.log(n + 2.0)


def c_coupling(n):
    return 1.0 / np.log(n + 2.0)


def apply_PT(M):
    return np.conj(M[::-1, ::-1])


def pt_defect(M):
    return float(np.linalg.norm(M - apply_PT(M), ord="fro"))


def herm_defect(M):
    return float(np.linalg.norm(M - M.conj().T, ord="fro"))


# -- (A) PT-canonical ------------------------------------------------------
def build_TN_PT_A(N, ch2=0.95, eps=0.5):
    """
    Palindromic magnitudes + Z_3-driven imaginary off-diagonal asymmetry.
    At ch_2 = 0.95 reduces to Hermitian (asymmetry vanishes).
    """
    gamma = eps * (ch2 - 0.95)
    T = np.zeros((N, N), dtype=np.complex128)
    # Palindromic diagonal
    for i in range(N):
        T[i, i] = 0.5 * (D_BK(i + 1) + D_BK(N - i))
    # Palindromic off-diagonal magnitude
    c_arr = np.zeros(N - 1)
    for i in range(N - 1):
        n = i + 1
        c_arr[i] = c_coupling(n)
    c_sym = 0.5 * (c_arr + c_arr[::-1])
    sqrt_c = np.sqrt(c_sym)
    # Z_3 phase as imaginary deviation
    for i in range(N - 1):
        n = i + 1
        D = D3(n)
        Dp = D3(N - 1 - i)   # mirror index 1-indexed = N - i
        U = sqrt_c[i] + 1j * gamma * D
        L = sqrt_c[i] - 1j * gamma * Dp
        # Enforce PT-constraint by averaging:  L_i = conj(U_{N-2-i})
        # We instead build U and then OVERRIDE L:
        T[i, i + 1] = U
    for i in range(N - 1):
        T[i + 1, i] = np.conj(T[N - 2 - i, N - 1 - i])
    return T


# -- (B) Bender-Boettcher gain/loss --------------------------------------
def build_TN_PT_B(N, ch2=0.95, eps=0.5):
    """
    Textbook PT-symmetric tight-binding:
        diag: D_k = D_BK_sym(k) + i gamma_k   with  gamma_k = -gamma_{N-1-k}
              so diagonal is PT-anti-symmetric in imaginary part.
        off-diag: real palindromic magnitudes (Hermitian off-diag).
    PT-symmetric, non-Hermitian, real spectrum until gamma > critical.
    Framework hook: gamma = eps * (ch_2 - 0.95) * profile(k).
    """
    gamma = eps * (ch2 - 0.95)
    T = np.zeros((N, N), dtype=np.complex128)
    for i in range(N):
        d_real = 0.5 * (D_BK(i + 1) + D_BK(N - i))
        # Anti-symmetric imaginary profile
        d_im = gamma * (i - 0.5 * (N - 1))   # linear, PT-antisym about middle
        T[i, i] = d_real + 1j * d_im
    c_arr = np.array([c_coupling(i + 1) for i in range(N - 1)])
    c_sym = 0.5 * (c_arr + c_arr[::-1])
    sqrt_c = np.sqrt(c_sym)
    for i in range(N - 1):
        T[i, i + 1] = sqrt_c[i]
        T[i + 1, i] = sqrt_c[i]
    return T


# -- (C) Framework-driven (Z_3 phases as PT perturbation) ----------------
def build_TN_PT_C(N, ch2=0.95, eps=0.5, off_kind="Z3", seed=0):
    """
    Off-diagonal complex but PT-paired (L_i = conj(U_{N-2-i})).
    At ch_2 = 0.95 the eps-perturbation vanishes and U_i becomes
    purely sqrt(c_i_sym) (Hermitian).
    """
    rng = np.random.default_rng(seed)
    gamma = eps * (ch2 - 0.95)
    T = np.zeros((N, N), dtype=np.complex128)
    for i in range(N):
        T[i, i] = 0.5 * (D_BK(i + 1) + D_BK(N - i))
    c_arr = np.array([c_coupling(i + 1) for i in range(N - 1)])
    c_sym = 0.5 * (c_arr + c_arr[::-1])
    sqrt_c = np.sqrt(c_sym)
    # Phase choice
    phase_arr = np.zeros(N - 1, dtype=np.complex128)
    for i in range(N - 1):
        n = i + 1
        if off_kind == "Z3":
            th = 2.0 * PI * D3(n) / 3.0
        elif off_kind == "rand":
            th = 2.0 * PI * rng.random()
        else:
            th = 0.0
        phase_arr[i] = complex(np.cos(th), np.sin(th))
    # U_i = sqrt(c_i_sym) * exp(i gamma * arg(phase_i))
    # so at gamma=0 (ch2=0.95) U_i = sqrt(c_i_sym) REAL POSITIVE  -> Hermitian.
    U = np.zeros(N - 1, dtype=np.complex128)
    for i in range(N - 1):
        arg_phi = np.angle(phase_arr[i])
        U[i] = sqrt_c[i] * np.exp(1j * gamma * arg_phi)
    for i in range(N - 1):
        T[i, i + 1] = U[i]
        T[i + 1, i] = np.conj(U[N - 2 - i])
    return T


# -- Diagnostics -----------------------------------------------------------
def diag_info(T, tol=1e-7):
    eigs = eigvals(T)
    abs_im = np.abs(np.imag(eigs))
    n_real = int(np.sum(abs_im < tol * (1.0 + np.abs(np.real(eigs)))))
    max_im = float(np.max(abs_im))
    return eigs, n_real, max_im


def top_real_positive(eigs, k=20, tol=1e-6):
    re = np.real(eigs[np.abs(np.imag(eigs)) < tol])
    re = np.sort(re[re > 0.5])
    return re[:k]


def rms_to_zz(top_eigs, zz):
    m = min(len(top_eigs), len(zz))
    if m == 0:
        return float("inf")
    return float(np.sqrt(np.mean((np.real(top_eigs[:m]) - zz[:m]) ** 2)))


def level_spacing_var(eigs):
    re = np.sort(np.real(eigs[np.abs(np.imag(eigs)) < 1e-6]))
    s = np.diff(re)
    if len(s) < 6:
        return float("nan"), float("nan")
    s_n = s / np.mean(s)
    return float(np.mean(s_n)), float(np.var(s_n))


# =========================================================================
# MAIN
# =========================================================================
def main():
    t0 = time.time()
    results = {}
    zz = np.array([float(zetazero(k).imag) for k in range(1, 21)])
    results["zeta_zeros_first20"] = zz.tolist()

    print("=" * 92)
    print("PT-SYMMETRIC T_N v2  —  three constructions (A, B, C)")
    print("=" * 92)

    # -------------------------------------------------------------
    # A) Verify PT-symmetry and Hermitian limit for each construction
    # -------------------------------------------------------------
    for label, builder in [("A_canonical", build_TN_PT_A),
                           ("B_gainloss",  build_TN_PT_B),
                           ("C_framework", build_TN_PT_C)]:
        print(f"\n--- Construction {label} ---")
        sub = {}
        for ch2 in [0.95, 0.93, 0.90, 0.85, 1.00, 1.05]:
            T = builder(N=200, ch2=ch2, eps=0.5)
            pd = pt_defect(T)
            hd = herm_defect(T)
            _, n_real, max_im = diag_info(T)
            sub[ch2] = {"pt_defect": pd, "herm_defect": hd,
                        "n_real_200": n_real, "max_im": max_im}
            print(f"  ch2={ch2:.2f}  PT-def={pd:9.2e}  H-def={hd:9.2e}  "
                  f"real-eigs={n_real:3d}/200  max|Im|={max_im:.2e}")
        results[f"step1_{label}"] = sub

    # -------------------------------------------------------------
    # B) ch_2 sweep for each construction
    # -------------------------------------------------------------
    print("\n" + "=" * 92)
    print("ch_2 sweep — RMS top20 eigenvalues vs first 20 zeta zeros")
    print("=" * 92)
    sweep_ch2 = [0.85, 0.88, 0.90, 0.92, 0.93, 0.95, 0.97, 1.00, 1.02, 1.05, 1.10]
    for label, builder in [("A_canonical", build_TN_PT_A),
                           ("B_gainloss",  build_TN_PT_B),
                           ("C_framework", build_TN_PT_C)]:
        print(f"\n--- {label} ---")
        sub = {}
        best = (None, float("inf"))
        for ch2 in sweep_ch2:
            T = builder(N=400, ch2=ch2, eps=0.5)
            eigs, n_real, max_im = diag_info(T)
            top = top_real_positive(eigs, k=20, tol=1e-6)
            if len(top) < 5:
                print(f"  ch2={ch2:.3f}  only {len(top)} real-pos eigs; "
                      f"max|Im|={max_im:.2e}; PT broken")
                sub[ch2] = {"top": top.tolist(), "rms": None,
                            "max_im": max_im, "n_real_pos": int(len(top))}
                continue
            rms = rms_to_zz(top, zz)
            sub[ch2] = {"top1": float(top[0]) if len(top) else None,
                        "n_top": int(len(top)), "rms": rms, "max_im": max_im}
            mark = ""
            if rms < best[1]:
                best = (ch2, rms); mark = "  <-- best"
            print(f"  ch2={ch2:.3f}  n_real_pos={len(top):3d}  "
                  f"top1={top[0]:8.3f}  rms20={rms:8.3f}{mark}")
        sub["best"] = {"ch2": best[0], "rms": best[1]}
        results[f"sweep_{label}"] = sub

    # -------------------------------------------------------------
    # C) Gauge non-invariance for construction C
    # -------------------------------------------------------------
    print("\n" + "=" * 92)
    print("Gauge non-invariance (construction C, ch_2 = 0.90)")
    print("=" * 92)
    Tz3 = build_TN_PT_C(N=200, ch2=0.90, eps=0.5, off_kind="Z3")
    Ttr = build_TN_PT_C(N=200, ch2=0.90, eps=0.5, off_kind="trivial")
    Tra = build_TN_PT_C(N=200, ch2=0.90, eps=0.5, off_kind="rand", seed=11)
    ez3, era, etr = (np.sort(np.real(eigvals(M))) for M in (Tz3, Tra, Ttr))
    print(f"  max|spec(Z3) - spec(trivial)| = {np.max(np.abs(ez3-etr)):.3e}")
    print(f"  max|spec(Z3) - spec(random) | = {np.max(np.abs(ez3-era)):.3e}")
    results["gauge_at_090_C"] = {
        "z3_vs_trivial": float(np.max(np.abs(ez3-etr))),
        "z3_vs_random":  float(np.max(np.abs(ez3-era))),
    }

    # -------------------------------------------------------------
    # D) Construction B: PT-breaking transition (theoretical sharpest)
    # -------------------------------------------------------------
    print("\n" + "=" * 92)
    print("Construction B: PT-breaking transition over (ch_2, eps) [N=120]")
    print("=" * 92)
    ch2_grid = [0.85, 0.90, 0.93, 0.95, 0.97, 1.00, 1.05, 1.10, 1.20]
    eps_grid = [0.0, 0.01, 0.05, 0.1, 0.5, 1.0, 2.0]
    pt_break_grid = {}
    print(f"{'eps \\ ch2':>10s}", *[f"{c:>8.2f}" for c in ch2_grid])
    for eps in eps_grid:
        row, row_d = [], {}
        for ch2 in ch2_grid:
            T = build_TN_PT_B(N=120, ch2=ch2, eps=eps)
            _, _, max_im = diag_info(T)
            row.append(max_im); row_d[ch2] = max_im
        pt_break_grid[eps] = row_d
        print(f"  eps={eps:5.2f} | ", " ".join(f"{x:8.2e}" for x in row))
    print("  Values: max|Im(eig)| — PT-symmetric phase has ~0; broken phase O(1)")
    results["pt_break_grid_B"] = pt_break_grid

    # -------------------------------------------------------------
    # E) Best-of-best ch_2 fine sweep
    # -------------------------------------------------------------
    print("\n" + "=" * 92)
    print("Construction B: FINE ch_2 sweep, top10 eigs vs first 10 zeta zeros")
    print("=" * 92)
    fine = np.linspace(0.85, 1.10, 26)
    best = (None, float("inf"), None)
    fine_sub = {}
    for ch2 in fine:
        T = build_TN_PT_B(N=400, ch2=float(ch2), eps=0.5)
        eigs, _, max_im = diag_info(T)
        top = top_real_positive(eigs, k=10, tol=1e-6)
        if len(top) < 10:
            fine_sub[float(ch2)] = {"n_top": int(len(top)), "rms": None}
            continue
        rms = rms_to_zz(top, zz[:10])
        fine_sub[float(ch2)] = {"top1": float(top[0]), "rms10": rms}
        if rms < best[1]:
            best = (float(ch2), rms, top[:5].tolist())
    print(f"  best ch_2 = {best[0]:.4f}  RMS10 = {best[1]:.3f}")
    print(f"  top5 there: {[round(x,3) for x in best[2]]}")
    print(f"  zz5       : {[round(x,3) for x in zz[:5]]}")
    results["fine_sweep_B"] = {"detail": fine_sub, "best": best}

    # -------------------------------------------------------------
    # F) Level spacing at best ch_2 (construction B)
    # -------------------------------------------------------------
    if best[0] is not None:
        T = build_TN_PT_B(N=600, ch2=best[0], eps=0.5)
        eigs, _, _ = diag_info(T)
        m, v = level_spacing_var(eigs)
        print(f"\nLevel spacing variance at ch_2={best[0]:.4f}: var={v:.4f} "
              f"(GUE=0.180, GOE=0.286, Poisson=1.000)")
        results["spacing_B_best"] = {"ch2": best[0], "mean": m, "var": v}

    # Save
    outpath = os.path.join(OUTDIR, "pt_symmetric_results_v2.json")
    with open(outpath, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nElapsed: {time.time()-t0:.1f}s   Saved: {outpath}")


if __name__ == "__main__":
    main()
