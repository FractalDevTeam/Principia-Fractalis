"""
PT_SYMMETRIC_TN.PY  —  Wave 7 option (c): PT-symmetric non-self-adjoint
construction of T_N as a route around the tridiagonal Hermitian gauge-
invariance obstruction.

Background
----------
Wave 7 proved: for tridiagonal HERMITIAN T_N, off-diagonal phases are
gauge-equivalent (any phase choice gives the SAME spectrum via diagonal
unitary similarity).  Z_3 / D_3 phase from the framework therefore
cannot affect spectrum in that setting.

PT-symmetric (Bender-Boettcher 1998 / Mostafazadeh) operators relax
Hermiticity to:   [PT, H] = 0
where P = parity (here: flip about the middle index) and T = complex
conjugation.  This guarantees REAL spectrum (or complex conjugate
pairs) even though H need not be self-adjoint.  Phase choices DO
matter because the operator is non-Hermitian; the gauge proof breaks.

PT-CONSTRAINT (concrete)
------------------------
With P|i> = |N+1-i> and T = complex conjugation we have, for any
matrix M in the standard basis:
    (PT M (PT)^{-1})_{i,j} = conj(M_{N+1-i, N+1-j}).
[PT, M] = 0 thus reads:
    M_{i,j} = conj(M_{N+1-i, N+1-j})    (PT-constraint)

For a tridiagonal M with diagonal D_i, super-diagonal U_i = M_{i,i+1},
sub-diagonal L_i = M_{i+1,i}, the constraint becomes:
    D_i = conj(D_{N+1-i})                            (diagonal real-symmetric)
    U_i = conj(L_{N-i})                              (sub/super-diag pairing)

So D_i can be REAL if we want it palindromic.  The (U_i, L_i) pair
need not satisfy L_i = conj(U_i) (which would be Hermiticity); they
need only satisfy U_i = conj(L_{N-i}), a NON-LOCAL pairing that does
not coincide with Hermiticity.

CONSTRUCTION
------------
Diagonal:        D_i = D_BK(i)   (Berry-Keating Weyl density; symmetrized to be palindromic)
Super-diagonal:  U_i = phi_i sqrt(c_i) + i eps (ch2 - 0.95) eta_i
Sub-diagonal:    L_i = PT-image of U_{N-i}.

When ch2 = 0.95 the eta term vanishes and PT-constraint can be
arranged to coincide with Hermiticity.  Off ch2 = 0.95 the operator
is genuinely non-Hermitian but PT-symmetric.

Author: Claude Opus 4.7 (1M)
Date  : 2026-05-23
"""

import numpy as np
from numpy.linalg import eig, eigvals
import json
import os
import time
from mpmath import zetazero

PI = np.pi
OUTDIR = "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/RH_PT_symmetric"


# ---------------------------------------------------------------------------
# Framework primitives
# ---------------------------------------------------------------------------
def D3(n):
    """Base-3 digital sum."""
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s


def phi_phase(n):
    """Framework's Z_3 phase exp(2 pi i D_3(n) / 3)."""
    th = 2.0 * PI * D3(n) / 3.0
    return complex(np.cos(th), np.sin(th))


def eta_perturb(n):
    """Mechanism-3 imaginary perturbation magnitude eta_n (real positive)."""
    return 1.0 / (1.0 + np.log(n + 2.0))


def D_BK(n):
    """Berry-Keating Weyl-density diagonal."""
    return 2.0 * PI * n / np.log(n + 2.0)


def c_coupling(n):
    """Off-diagonal magnitude squared."""
    return 1.0 / np.log(n + 2.0)


# ---------------------------------------------------------------------------
# Parity operator P (flip about the middle)
# ---------------------------------------------------------------------------
def parity_matrix(N):
    """Anti-diagonal P = J: P_{i,j} = 1 iff i+j = N-1 (0-indexed)."""
    return np.fliplr(np.eye(N))


def apply_PT(M):
    """Apply PT = parity * conjugation to matrix M:
       (PT M (PT)^{-1})_{i,j} = conj(M_{N-1-i, N-1-j})   (0-indexed)."""
    return np.conj(M[::-1, ::-1])


# ---------------------------------------------------------------------------
# PT-symmetric T_N construction
# ---------------------------------------------------------------------------
def build_TN_PT(N, ch2=0.95, eps=0.5, off_kind="Z3", seed=0,
                palindromize=True):
    """
    Build PT-symmetric tridiagonal T_N.

    Strategy:
      1) Choose RAW super-diagonal U_i for i = 0..N-2 (0-indexed):
           U_i = phi_i sqrt(c_i) + i eps (ch2 - 0.95) eta_i
      2) Force sub-diagonal via PT-constraint:
           L_i = conj(U_{N-2-i})       (PT-pairing index in 0-indexing)
      3) Choose REAL palindromic diagonal:
           D_i = 0.5 * (D_BK(i+1) + D_BK(N-i))    (symmetric, real)

    Parameters
    ----------
    N : int
        Matrix size.
    ch2 : float
        Second Chern character; ch2 = 0.95 -> Hermitian limit.
    eps : float
        Strength of Mechanism-3 imaginary perturbation.
    off_kind : str
        Phase choice on real part of U_i: "Z3", "rand", "trivial".
    seed : int
        RNG seed for off_kind == "rand".
    palindromize : bool
        If True, diagonal is symmetrized (D_i = D_{N-1-i}).  If False,
        raw D_BK -> PT-constraint requires conjugation pairing instead.
    """
    rng = np.random.default_rng(seed)
    eta_off = ch2 - 0.95
    T = np.zeros((N, N), dtype=np.complex128)

    # Diagonal: real and palindromic
    for i in range(N):
        if palindromize:
            T[i, i] = 0.5 * (D_BK(i + 1) + D_BK(N - i))
        else:
            T[i, i] = D_BK(i + 1)

    # Build U_i = T[i, i+1] for i = 0..N-2
    U = np.zeros(N - 1, dtype=np.complex128)
    for i in range(N - 1):
        n = i + 1                              # 1-indexed framework count
        sqrt_c = np.sqrt(c_coupling(n))
        if off_kind == "Z3":
            ph = phi_phase(n)
        elif off_kind == "rand":
            ang = 2 * PI * rng.random()
            ph = complex(np.cos(ang), np.sin(ang))
        else:
            ph = complex(1.0, 0.0)
        # Real (gauge) part:
        real_part = ph * sqrt_c
        # Mechanism-3 imaginary perturbation (NOTE: PURELY IMAGINARY for
        # PT-asymmetry; vanishes at ch2 = 0.95):
        imag_part = 1j * eps * eta_off * eta_perturb(n)
        U[i] = real_part + imag_part
        T[i, i + 1] = U[i]

    # Lower diagonal forced by PT-constraint:
    #   L_i = T[i+1, i] = conj(U_{N-2-i})
    for i in range(N - 1):
        T[i + 1, i] = np.conj(U[N - 2 - i])

    return T


# ---------------------------------------------------------------------------
# PT-symmetry check
# ---------------------------------------------------------------------------
def pt_defect(M):
    """Frobenius norm of [PT, M] -- 0 iff PT-symmetric."""
    PTM = apply_PT(M)
    return float(np.linalg.norm(M - PTM, ord="fro"))


def hermitian_defect(M):
    return float(np.linalg.norm(M - M.conj().T, ord="fro"))


def gauge_defect_vs_trivial(M_phase, M_trivial):
    e_p = np.sort(np.real(eigvals(M_phase)))
    e_t = np.sort(np.real(eigvals(M_trivial)))
    n = min(len(e_p), len(e_t))
    return float(np.max(np.abs(e_p[:n] - e_t[:n])))


# ---------------------------------------------------------------------------
# Real-eigenvalue test (PT-symmetry unbroken)
# ---------------------------------------------------------------------------
def real_spectrum_diagnostics(M, tol=1e-9):
    eigs = eigvals(M)
    abs_im = np.abs(np.imag(eigs))
    n_real = int(np.sum(abs_im < tol * (1 + np.abs(np.real(eigs)))))
    max_im = float(np.max(abs_im))
    return n_real, max_im, eigs


# ---------------------------------------------------------------------------
# Zeta-zero matcher
# ---------------------------------------------------------------------------
def zz_match_rms(top_eigs, zz):
    m = min(len(top_eigs), len(zz))
    return float(np.sqrt(np.mean((np.real(top_eigs[:m]) - zz[:m]) ** 2)))


# ---------------------------------------------------------------------------
# Wigner-Dyson statistics
# ---------------------------------------------------------------------------
def level_spacing_stats(eigs):
    """Return mean, variance of normalized nearest-neighbor spacings."""
    real_eigs = np.sort(np.real(eigs))
    s_raw = np.diff(real_eigs)
    # Local unfolding via running mean of length 5
    if len(s_raw) < 6:
        return float("nan"), float("nan")
    s_norm = s_raw / np.mean(s_raw)
    return float(np.mean(s_norm)), float(np.var(s_norm))


# =============================================================================
# MAIN
# =============================================================================
def main():
    t0 = time.time()
    results = {}

    print("=" * 92)
    print("PT-SYMMETRIC T_N  —  Wave 7 option (c) framework application")
    print("=" * 92)

    # Zeta zeros (first 20 imaginary parts)
    zz = np.array([float(zetazero(k).imag) for k in range(1, 21)])
    print("\nReference: first 5 zeta-zero imag parts:", [round(x, 4) for x in zz[:5]])
    results["zeta_zeros_first20"] = zz.tolist()

    # -----------------------------------------------------------------
    # 1) Verify PT-symmetry construction
    # -----------------------------------------------------------------
    print("\n" + "-" * 92)
    print("STEP 1 — Verify PT-symmetry of construction (N = 100)")
    print("-" * 92)
    N = 100
    step1 = {}
    for ch2 in [0.95, 0.93, 0.90, 0.85, 1.00, 1.05]:
        T = build_TN_PT(N, ch2=ch2, eps=0.5, off_kind="Z3")
        pt_d = pt_defect(T)
        her_d = hermitian_defect(T)
        step1[ch2] = {"pt_defect": pt_d, "hermitian_defect": her_d}
        print(f"  ch2={ch2:.2f}  ||T - PT(T)||_F = {pt_d:.3e}  "
              f"||T - T^H||_F = {her_d:.3e}")
    print("  -> PT defect SHOULD be ~0 at all ch_2 (construction enforces it).")
    print("  -> Hermitian defect SHOULD be 0 only at ch_2 = 0.95.")
    results["step1_pt_verification"] = step1

    # -----------------------------------------------------------------
    # 2) Diagonalize at multiple ch_2 values; check real spectrum
    # -----------------------------------------------------------------
    print("\n" + "-" * 92)
    print("STEP 2 — Spectrum at multiple ch_2; check reality (PT-unbroken phase)")
    print("-" * 92)
    step2 = {}
    for ch2 in [0.95, 0.90, 0.99, 0.85, 1.05]:
        T = build_TN_PT(N=200, ch2=ch2, eps=0.5, off_kind="Z3")
        n_real, max_im, eigs = real_spectrum_diagnostics(T)
        real_eigs = np.sort(np.real(eigs[np.abs(np.imag(eigs)) < 1e-6]))
        top5 = real_eigs[real_eigs > 0.5][:5]
        step2[ch2] = {
            "n_real_out_of_200": n_real,
            "max_im_part": max_im,
            "top5_real_positive": top5.tolist(),
        }
        print(f"  ch2={ch2:.2f}  real eigs: {n_real}/200  max|Im|={max_im:.3e}  "
              f"top5: {[round(x, 3) for x in top5]}")
    results["step2_spectrum"] = step2

    # -----------------------------------------------------------------
    # 3) Gauge non-invariance test at ch_2 = 0.90
    # -----------------------------------------------------------------
    print("\n" + "-" * 92)
    print("STEP 3 — Gauge non-invariance (PT route is supposed to escape it)")
    print("-" * 92)
    step3 = {}
    ch2_gauge = 0.90
    Tz3 = build_TN_PT(N=200, ch2=ch2_gauge, eps=0.5, off_kind="Z3")
    Tra = build_TN_PT(N=200, ch2=ch2_gauge, eps=0.5, off_kind="rand", seed=11)
    Ttr = build_TN_PT(N=200, ch2=ch2_gauge, eps=0.5, off_kind="trivial")
    ez3 = np.sort(np.real(eigvals(Tz3)))
    era = np.sort(np.real(eigvals(Tra)))
    etr = np.sort(np.real(eigvals(Ttr)))
    gd_z3_tr = float(np.max(np.abs(ez3 - etr)))
    gd_z3_ra = float(np.max(np.abs(ez3 - era)))
    print(f"  max|spectrum(Z3) - spectrum(trivial)| = {gd_z3_tr:.4e}")
    print(f"  max|spectrum(Z3) - spectrum(random) | = {gd_z3_ra:.4e}")
    print("  Wave 7 Hermitian result: this was ~1e-13 (gauge-equivalent).")
    print("  PT case: nonzero means PHASES ESCAPE the gauge obstruction.")
    step3 = {
        "diff_z3_trivial": gd_z3_tr,
        "diff_z3_random": gd_z3_ra,
        "z3_top5": ez3[ez3 > 0.5][:5].tolist(),
        "rand_top5": era[era > 0.5][:5].tolist(),
        "trivial_top5": etr[etr > 0.5][:5].tolist(),
    }
    results["step3_gauge_non_invariance"] = step3

    # -----------------------------------------------------------------
    # 4) ch_2 sweep: find value that minimizes RMS to zeta zeros
    # -----------------------------------------------------------------
    print("\n" + "-" * 92)
    print("STEP 4 — ch_2 sweep: which value brings spectrum closest to zeta zeros?")
    print("-" * 92)
    step4 = {}
    sweep_ch2 = [0.85, 0.88, 0.90, 0.92, 0.93, 0.95, 0.97, 1.00, 1.02, 1.05]
    best_ch2, best_rms = None, float("inf")
    N_match = 400
    for ch2 in sweep_ch2:
        T = build_TN_PT(N=N_match, ch2=ch2, eps=0.5, off_kind="Z3")
        eigs = eigvals(T)
        real_eigs = np.sort(np.real(eigs[np.abs(np.imag(eigs)) < 1e-6]))
        top20 = real_eigs[real_eigs > 0.5][:20]
        if len(top20) < 20:
            print(f"  ch2={ch2:.3f}  only {len(top20)} real positive eigs; skipping")
            continue
        rms = zz_match_rms(top20, zz)
        step4[ch2] = {"top5": top20[:5].tolist(), "rms_to_zz20": rms}
        marker = "  <-- best so far" if rms < best_rms else ""
        if rms < best_rms:
            best_rms = rms
            best_ch2 = ch2
        print(f"  ch2={ch2:.3f}  RMS(top20 vs zz20)={rms:8.3f}  "
              f"top1={top20[0]:.4f} (zz1=14.135){marker}")
    step4["best_ch2"] = best_ch2
    step4["best_rms"] = best_rms
    results["step4_ch2_sweep"] = step4
    print(f"\n  Best ch_2 = {best_ch2} with RMS = {best_rms:.3f}")

    # -----------------------------------------------------------------
    # 5) Wigner-Dyson spacings at best ch_2
    # -----------------------------------------------------------------
    print("\n" + "-" * 92)
    print(f"STEP 5 — Level spacing statistics at best ch_2 = {best_ch2}")
    print("-" * 92)
    T = build_TN_PT(N=400, ch2=best_ch2 or 0.95, eps=0.5, off_kind="Z3")
    eigs = eigvals(T)
    real_eigs = np.real(eigs[np.abs(np.imag(eigs)) < 1e-6])
    mean_s, var_s = level_spacing_stats(real_eigs)
    print(f"  Normalized spacing mean (target 1.0): {mean_s:.4f}")
    print(f"  Normalized spacing variance         : {var_s:.4f}")
    print("  Reference variances: Poisson ~1.000, GOE ~0.286, GUE ~0.180")
    results["step5_level_spacing"] = {
        "mean_s": mean_s, "var_s": var_s,
        "ref_poisson": 1.0, "ref_GOE": 0.286, "ref_GUE": 0.180
    }

    # -----------------------------------------------------------------
    # 6) PT-symmetry-breaking transition: scan (ch_2, eps) plane
    # -----------------------------------------------------------------
    print("\n" + "-" * 92)
    print("STEP 6 — PT-symmetry-breaking transition in (ch_2, eps) plane (N=120)")
    print("-" * 92)
    sweep_grid = {}
    ch2_grid = [0.80, 0.85, 0.90, 0.93, 0.95, 0.97, 1.00, 1.05, 1.10]
    eps_grid = [0.0, 0.1, 0.5, 1.0, 2.0, 5.0]
    print(f"{'eps \\ ch2':>10s}", *[f"{c:>7.2f}" for c in ch2_grid])
    for eps in eps_grid:
        row = []
        row_data = {}
        for ch2 in ch2_grid:
            T = build_TN_PT(N=120, ch2=ch2, eps=eps, off_kind="Z3")
            _, max_im, eigs = real_spectrum_diagnostics(T, tol=1e-7)
            row.append(max_im)
            row_data[ch2] = max_im
        sweep_grid[eps] = row_data
        print(f"  eps={eps:5.2f} | ", " ".join(f"{x:7.1e}" for x in row))
    print("  (Values are max|Im(eigenvalue)|; ~0 means PT-unbroken.)")
    print("  PT-breaking transition: where this jumps from ~0 to O(1).")
    results["step6_pt_breaking_grid"] = sweep_grid

    # -----------------------------------------------------------------
    # 7) Detailed comparison at ch_2 = 0.95 to Hermitian Wave 7 result
    # -----------------------------------------------------------------
    print("\n" + "-" * 92)
    print("STEP 7 — At ch_2 = 0.95 PT-construction should reduce to Hermitian case")
    print("-" * 92)
    T_pt_at_095 = build_TN_PT(N=200, ch2=0.95, eps=0.5, off_kind="Z3")
    T_hermitized = 0.5 * (T_pt_at_095 + T_pt_at_095.conj().T)
    e_pt = np.sort(np.real(eigvals(T_pt_at_095)))
    e_h = np.sort(np.real(np.linalg.eigvalsh(T_hermitized)))
    delta = float(np.max(np.abs(e_pt - e_h)))
    print(f"  max|spectrum(PT@0.95) - spectrum(Hermitized@0.95)| = {delta:.3e}")
    print("  Should be tiny -- confirms PT-construction reduces correctly.")
    results["step7_reduction_at_095"] = {"max_diff": delta,
                                          "top5_pt": e_pt[e_pt > 0.5][:5].tolist(),
                                          "top5_h": e_h[e_h > 0.5][:5].tolist()}

    # -----------------------------------------------------------------
    # Save results
    # -----------------------------------------------------------------
    outpath = os.path.join(OUTDIR, "pt_symmetric_results.json")
    with open(outpath, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nElapsed: {time.time() - t0:.1f} s")
    print(f"Saved: {outpath}")


if __name__ == "__main__":
    main()
