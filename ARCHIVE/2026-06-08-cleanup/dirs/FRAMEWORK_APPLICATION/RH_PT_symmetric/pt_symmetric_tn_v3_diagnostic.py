"""
PT_SYMMETRIC_TN_V3_DIAGNOSTIC.PY  —  Fix sorting + look at LOW eigenvalues.

v2 finding: ch_2=0.95 (Hermitian limit) reproduces the Wave 7 result
exactly (good).  But the "top20" code was incorrectly taking the
20 SMALLEST eigenvalues above 0.5 (sort ascending then [:20]).  The
LOWEST eigenvalues are the ones that match Berry-Keating Weyl
density ~ zeta zeros.

v3 fixes that and explicitly compares LOW eigenvalues to zeta zeros
across the PT-breaking transition, looking for ch_2 values where
the low eigenvalues SHIFT toward zeta zeros (genuine framework signal).

Then we test the central question: does the eigenvalue ground state
move toward 14.1347 as we tune (ch_2, eps) in the PT-unbroken region
near ch_2 = 0.95?
"""

import numpy as np
from numpy.linalg import eigvals
import json
import os
import time
from mpmath import zetazero

PI = np.pi
OUTDIR = "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/RH_PT_symmetric"

# ---------- Framework primitives ----------
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


# --------- Construction B: cleanest PT-symmetric ----------
def build_TN_PT_B(N, ch2=0.95, eps=0.5, profile="linear", D3_profile=False):
    """
    Bender-Boettcher gain/loss with PT-anti-symmetric imag diagonal.
        diag: D_k = D_BK_sym(k) + i gamma * f(k)  where f(k) = -f(N-1-k)
        off-diag: palindromic real magnitudes (Hermitian off-diag).

    profile = "linear"  : f(k) = k - (N-1)/2
    profile = "D3"      : f(k) = D3(k+1) - D3(N-k)
    """
    gamma = eps * (ch2 - 0.95)
    T = np.zeros((N, N), dtype=np.complex128)
    for i in range(N):
        d_real = 0.5 * (D_BK(i + 1) + D_BK(N - i))
        if profile == "linear":
            f = i - 0.5 * (N - 1)
        elif profile == "D3":
            f = D3(i + 1) - D3(N - i)
        else:
            f = 0.0
        T[i, i] = d_real + 1j * gamma * f
    c_arr = np.array([c_coupling(i + 1) for i in range(N - 1)])
    c_sym = 0.5 * (c_arr + c_arr[::-1])
    sqrt_c = np.sqrt(c_sym)
    for i in range(N - 1):
        T[i, i + 1] = sqrt_c[i]
        T[i + 1, i] = sqrt_c[i]
    return T


def lowest_real(eigs, k=20, tol=1e-6):
    re = np.real(eigs[np.abs(np.imag(eigs)) < tol])
    re = np.sort(re[re > 0])
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


def main():
    t0 = time.time()
    results = {}
    zz = np.array([float(zetazero(k).imag) for k in range(1, 21)])
    print("Zeta zeros first 10:", [round(x, 3) for x in zz[:10]])
    results["zeta_zeros_first20"] = zz.tolist()

    # -----------------------------------------------------------
    # 1) Hermitian baseline (ch_2 = 0.95)
    # -----------------------------------------------------------
    print("\n" + "=" * 86)
    print("Hermitian baseline ch_2 = 0.95, construction B (linear profile)")
    print("=" * 86)
    for N in [200, 400, 800]:
        T = build_TN_PT_B(N=N, ch2=0.95, eps=0.5, profile="linear")
        eigs = eigvals(T)
        low = lowest_real(eigs, k=10)
        rms = rms_to_zz(low, zz[:10])
        print(f"  N={N:4d}  lowest 10: {[round(x,3) for x in low]}")
        print(f"           zz10     : {[round(x,3) for x in zz[:10]]}")
        print(f"           RMS_10   : {rms:.4f}")
        results[f"baseline_N{N}"] = {"low10": low.tolist(), "rms10": rms}

    # -----------------------------------------------------------
    # 2) ch_2 sweep with LOW eigenvalues (the right metric)
    # -----------------------------------------------------------
    print("\n" + "=" * 86)
    print("Construction B, FINE ch_2 sweep, LOW eigenvalues vs zeta zeros (N=400)")
    print("=" * 86)
    sweep = np.concatenate([
        np.linspace(0.85, 0.94, 10),
        np.linspace(0.945, 0.955, 11),
        np.linspace(0.96, 1.10, 15),
    ])
    sweep = np.unique(np.round(sweep, 4))
    fine_data = {}
    best = (None, float("inf"), None)
    for ch2 in sweep:
        T = build_TN_PT_B(N=400, ch2=float(ch2), eps=0.5, profile="linear")
        eigs = eigvals(T)
        low = lowest_real(eigs, k=10)
        if len(low) < 10:
            fine_data[float(ch2)] = {"n": int(len(low)), "rms10": None}
            continue
        rms = rms_to_zz(low, zz[:10])
        fine_data[float(ch2)] = {
            "low10": low.tolist(),
            "rms10": rms,
            "top1": float(low[0]),
        }
        if rms < best[1]:
            best = (float(ch2), rms, low[:5].tolist())
    print(f"  Best ch_2 = {best[0]:.4f}   RMS10 = {best[1]:.4f}")
    if best[2]:
        print(f"  low5 there: {[round(x,3) for x in best[2]]}")
        print(f"  zz5        : {[round(x,3) for x in zz[:5]]}")
    results["fine_sweep_low"] = {"detail": fine_data, "best": best}

    # -----------------------------------------------------------
    # 3) eps sweep at fixed ch_2 in PT-unbroken region (ch_2 close to 0.95)
    # -----------------------------------------------------------
    print("\n" + "=" * 86)
    print("eps sweep at ch_2 = 0.96 (near Hermitian, weakly PT)")
    print("=" * 86)
    eps_data = {}
    for eps in [0.0, 0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0]:
        T = build_TN_PT_B(N=400, ch2=0.96, eps=eps, profile="linear")
        eigs = eigvals(T)
        max_im = float(np.max(np.abs(np.imag(eigs))))
        low = lowest_real(eigs, k=10)
        if len(low) >= 10:
            rms = rms_to_zz(low, zz[:10])
        else:
            rms = None
        print(f"  eps={eps:5.2f}  max|Im|={max_im:8.2e}  "
              f"n_real_pos={len(low):3d}  RMS10="
              f"{'%.4f'%rms if rms is not None else 'PT-broken'}")
        eps_data[eps] = {"max_im": max_im,
                         "n_low": int(len(low)),
                         "rms10": rms,
                         "low5": low[:5].tolist()}
    results["eps_sweep_096_B"] = eps_data

    # -----------------------------------------------------------
    # 4) D3 profile vs linear profile — does framework D3 help?
    # -----------------------------------------------------------
    print("\n" + "=" * 86)
    print("Profile comparison at ch_2 = 0.90, eps = 0.5, N = 400")
    print("=" * 86)
    profile_data = {}
    for prof in ["linear", "D3"]:
        T = build_TN_PT_B(N=400, ch2=0.90, eps=0.5, profile=prof)
        eigs = eigvals(T)
        max_im = float(np.max(np.abs(np.imag(eigs))))
        low = lowest_real(eigs, k=10)
        if len(low) >= 10:
            rms = rms_to_zz(low, zz[:10])
        else:
            rms = None
        print(f"  profile={prof:7s}  max|Im|={max_im:.3e}  "
              f"n_real_pos={len(low):3d}  RMS10="
              f"{'%.4f'%rms if rms is not None else 'PT-broken'}")
        profile_data[prof] = {"max_im": max_im, "n_low": int(len(low)),
                              "rms10": rms, "low5": low[:5].tolist()}
    results["profile_compare"] = profile_data

    # -----------------------------------------------------------
    # 5) Joint (ch_2, eps) optimization for D3 profile
    # -----------------------------------------------------------
    print("\n" + "=" * 86)
    print("Joint (ch_2, eps) optimization, D3 profile, N=300")
    print("=" * 86)
    best_joint = (None, None, float("inf"))
    joint_data = {}
    for ch2 in np.linspace(0.88, 1.02, 15):
        for eps in [0.01, 0.05, 0.1, 0.25, 0.5, 1.0]:
            T = build_TN_PT_B(N=300, ch2=float(ch2), eps=float(eps), profile="D3")
            eigs = eigvals(T)
            low = lowest_real(eigs, k=10)
            if len(low) < 10:
                continue
            rms = rms_to_zz(low, zz[:10])
            joint_data[f"ch2={ch2:.3f},eps={eps:.2f}"] = rms
            if rms < best_joint[2]:
                best_joint = (float(ch2), float(eps), rms)
    print(f"  Best (ch_2, eps) = ({best_joint[0]:.4f}, {best_joint[1]:.3f})  "
          f"RMS10 = {best_joint[2]:.4f}")
    results["joint_best_D3"] = {"ch2": best_joint[0], "eps": best_joint[1],
                                 "rms10": best_joint[2]}

    # -----------------------------------------------------------
    # 6) Level spacing variance at best (Wigner-Dyson)
    # -----------------------------------------------------------
    print("\n" + "=" * 86)
    print("Level spacing variance: PT vs Hermitian")
    print("=" * 86)
    T_h = build_TN_PT_B(N=800, ch2=0.95, eps=0.5, profile="linear")
    e_h = eigvals(T_h)
    m_h, v_h = level_spacing_var(e_h)
    print(f"  Hermitian (ch_2=0.95): var = {v_h:.4f}")
    T_p = build_TN_PT_B(N=800, ch2=0.96, eps=0.05, profile="linear")
    e_p = eigvals(T_p)
    m_p, v_p = level_spacing_var(e_p)
    print(f"  PT (ch_2=0.96, eps=0.05): var = {v_p:.4f}")
    print(f"  Reference: Poisson=1.000  GOE=0.286  GUE=0.180")
    results["spacing_var"] = {"hermitian": v_h, "pt_weak": v_p}

    # -----------------------------------------------------------
    # Save
    # -----------------------------------------------------------
    outpath = os.path.join(OUTDIR, "pt_symmetric_results_v3.json")
    with open(outpath, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nElapsed: {time.time()-t0:.1f}s   Saved: {outpath}")


if __name__ == "__main__":
    main()
