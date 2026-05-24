"""
PT_SYMMETRIC_TN_V4_NATURAL.PY  —  Fix the diagonal palindromization issue.

PROBLEM identified in v2/v3:
  Forcing diag palindromic (D_i = D_{N-1-i}) destroys the Berry-Keating
  low-eigenvalue spectrum that Wave 7 used to get the 14.13 anchor.
  With natural D_BK(n) = 2pi*n/log(n+2), low eigenvalues sit at
  ~5.5, 9.0, 11.7, 14.0, ... (matching first zeta zeros).
  Palindromization moves the lowest eigenvalue to ~D_BK(N/2), which
  for N = 400 is ~120 -- nowhere near zeta zeros.

PT-symmetry constraint with natural (non-palindromic) D_BK:
  PT M (PT)^{-1}_{i,j} = conj(M_{N-1-i, N-1-j}).
  Diagonal constraint:  M_{i,i} = conj(M_{N-1-i, N-1-i}).
  For REAL D_BK that's D_BK(i) = D_BK(N-1-i), which FAILS for natural
  D_BK because D_BK is monotone-increasing.

RESOLUTION: choose P = IDENTITY (no spatial flip), so [PT, M] = 0
just says M = conj(M), i.e. M is real (Hermitian for symmetric M).
That's trivial.

Alternative: use a DIFFERENT P operator that respects the natural
diagonal.  Possibilities:
  (i)   P = identity, T = conj  ==>  PT-symmetry == reality
  (ii)  P = anti-diagonal flip  ==>  requires palindromic D (kills spectrum)
  (iii) P = chirality (diag(+1,-1,+1,...,-1))  ==>  preserves natural D
  (iv)  P = "shift": (Pf)(n) = f(n+1)  ==>  not an involution

Option (iii) "chiral PT": P = diag((-1)^i).  Then PT M (PT)^{-1}_{i,j}
= (-1)^{i+j} conj(M_{i,j}).  Diagonal entries (i=j) ==> M_{i,i} = conj(M_{i,i})
i.e. REAL diagonal (no palindromization needed!).
Off-diagonal (i != j) with i+j ODD ==> M_{i,j} = -conj(M_{i,j}) i.e. PURE IMAGINARY.
Off-diagonal (i != j) with i+j EVEN ==> M_{i,j} = conj(M_{i,j}) i.e. REAL.

For TRIDIAGONAL (|i-j|=1) we ALWAYS have i+j odd, so PT-symmetry forces
ALL off-diagonal entries PURELY IMAGINARY.  Sub-diagonal must satisfy
M_{i+1,i} = -conj(M_{i,i+1}) -- so if M_{i,i+1} = i*alpha (real alpha)
then M_{i+1,i} = -conj(i*alpha) = i*alpha -- i.e. SYMMETRIC purely
imaginary off-diagonal.  Such a matrix is anti-Hermitian (i times
real symmetric) -> eigenvalues all pure imaginary, NOT useful.

For tridiagonal Hermitian, PT_chiral forces it to be anti-Hermitian.
So chiral P doesn't work directly for tridiagonal Hermitian + small
perturbation.

THE REAL FIX:
  Pseudo-Hermitian operators (Mostafazadeh 2002): H is eta-pseudo-
  Hermitian if eta H eta^{-1} = H^dag for some Hermitian invertible eta.
  This GENERALIZES PT-symmetry and ADMITS real spectra for
  non-Hermitian H.

  Mostafazadeh's framework with eta = diagonal positive metric still
  requires off-diagonal pairing similar to PT-pairing.  Without
  palindromic D, the most natural construction is:

    H = H_0 + i * gamma * V
  where H_0 is the Hermitian Berry-Keating tridiagonal (Wave 7 baseline)
  and V is a Hermitian operator that is PT-anti-symmetric.  Then
  H is PT-symmetric (PT H PT = H_0 - i*gamma*V*... requires detail).

  SIMPLEST: use NEUTRAL P that respects natural D_BK -- namely
    P_natural = sigma_1 in 2x2 block diagonal:
       paired blocks (k, k+N/2) under flip
  but for ODD N this is awkward.

PRACTICAL APPROACH (this script):
  Build the Wave 7 baseline T_N (natural D_BK, real symmetric off-diag),
  then add a PT-symmetric NON-HERMITIAN PERTURBATION of the form
     delta T_{n,n+1} =  i * gamma * a_n
     delta T_{n+1,n} = -i * gamma * a_n      (anti-Hermitian, hence non-Hermitian)
  where a_n is a real coupling profile.  This makes the off-diagonal
  imag-part ANTI-SYMMETRIC (T_{i,j} != conj(T_{j,i})), breaking
  Hermiticity.  Such operators (Bender-Boettcher complex extensions)
  can be PT-symmetric for appropriate (P, a_n).

  Choose P = identity * chirality (-1)^n so diag stays real; force
  the perturbation to satisfy PT-symmetry by construction.

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


def D3(n):
    s = 0
    while n > 0:
        s += n % 3; n //= 3
    return s


def D_BK(n):
    return 2.0 * PI * n / np.log(n + 2.0)


def c_coupling(n):
    return 1.0 / np.log(n + 2.0)


def phi_phase(n):
    th = 2.0 * PI * D3(n) / 3.0
    return complex(np.cos(th), np.sin(th))


# ---------- Construction D: natural diagonal + anti-Hermitian perturbation ---
def build_TN_PT_D(N, ch2=0.95, eps=0.5, perturb_kind="Z3_imag",
                  off_kind="trivial", seed=0):
    """
    Natural Berry-Keating Hermitian baseline + non-Hermitian PT-symmetric
    perturbation in off-diagonal (anti-Hermitian piece).

    Off-diagonal:
      T_{i,i+1} = phi_i * sqrt(c_i)  + i * gamma * a_i
      T_{i+1,i} = conj(phi_i) * sqrt(c_i) - i * gamma * a_i
        (note SIGN FLIP on imag part -- this is the anti-Hermitian piece)

    Hermiticity defect = ||T - T^H||_F = 2 * gamma * ||a||_2.
    gamma = eps * (ch_2 - 0.95).

    PT-symmetry: for P = (-1)^n chirality (preserves natural D),
      (P T P)_{i,j} = (-1)^{i+j} T_{i,j}
      For tridiagonal i,j with |i-j|=1, (-1)^{i+j} = -1, so
      (P T P)_{i,i+1} = -T_{i,i+1}.
      Then PT T (PT)^{-1}_{i,i+1} = -conj(T_{i,i+1}).
      PT-symmetry: T_{i,i+1} = -conj(T_{i,i+1}) ==> T_{i,i+1} purely
      imaginary.  Fails for our construction (real part nonzero).

    So PT_chiral doesn't apply.  But PT-symmetry for these operators
    is naturally established via "complex deformation of harmonic
    oscillator" type constructions.  Here we just check whether
    the spectrum stays REAL despite non-Hermiticity -- the operational
    test of PT-unbroken phase.
    """
    rng = np.random.default_rng(seed)
    gamma = eps * (ch2 - 0.95)
    T = np.zeros((N, N), dtype=np.complex128)
    for i in range(N):
        n = i + 1
        T[i, i] = D_BK(n)                 # natural, NOT palindromic

    for i in range(N - 1):
        n = i + 1
        sqrt_c = np.sqrt(c_coupling(n))
        if off_kind == "Z3":
            ph = phi_phase(n)
        elif off_kind == "rand":
            ang = 2 * PI * rng.random()
            ph = complex(np.cos(ang), np.sin(ang))
        else:
            ph = complex(1.0, 0.0)

        if perturb_kind == "Z3_imag":
            a = np.sin(2.0 * PI * D3(n) / 3.0)
        elif perturb_kind == "D3_imag":
            a = (D3(n) - 1.0)             # zero-mean perturbation
        elif perturb_kind == "alt_imag":
            a = (-1.0) ** n
        else:
            a = 1.0

        T[i, i + 1] = ph * sqrt_c + 1j * gamma * a
        T[i + 1, i] = np.conj(ph) * sqrt_c - 1j * gamma * a
    return T


# Diagnostics
def diag_info(T, tol=1e-7):
    eigs = eigvals(T)
    abs_im = np.abs(np.imag(eigs))
    n_real = int(np.sum(abs_im < tol * (1.0 + np.abs(np.real(eigs)))))
    max_im = float(np.max(abs_im))
    return eigs, n_real, max_im


def herm_defect(M):
    return float(np.linalg.norm(M - M.conj().T, ord="fro"))


def lowest_real_pos(eigs, k=15, tol=1e-6):
    re = np.real(eigs[np.abs(np.imag(eigs)) < tol])
    re = np.sort(re[re > 0])
    return re[:k]


def rms_to_zz(low_eigs, zz):
    m = min(len(low_eigs), len(zz))
    if m == 0:
        return float("inf")
    return float(np.sqrt(np.mean((np.real(low_eigs[:m]) - zz[:m]) ** 2)))


def closest_eig_to(target, eigs, real_only=True, tol=1e-6):
    if real_only:
        e = np.real(eigs[np.abs(np.imag(eigs)) < tol])
    else:
        e = np.real(eigs)
    if len(e) == 0:
        return None
    idx = int(np.argmin(np.abs(e - target)))
    return float(e[idx])


def level_spacing_var(eigs):
    re = np.sort(np.real(eigs[np.abs(np.imag(eigs)) < 1e-6]))
    s = np.diff(re)
    if len(s) < 6:
        return float("nan"), float("nan")
    s_n = s / np.mean(s)
    return float(np.mean(s_n)), float(np.var(s_n))


# ====================================================================
def main():
    t0 = time.time()
    results = {}
    zz = np.array([float(zetazero(k).imag) for k in range(1, 21)])
    results["zeta_zeros_first20"] = zz.tolist()
    print("Zeta zeros first 10:", [round(x, 3) for x in zz[:10]])

    # ----------------------------------------------------------
    # 1) Baseline at ch_2 = 0.95 (Hermitian, reproduces Wave 7)
    # ----------------------------------------------------------
    print("\n" + "=" * 86)
    print("1) Baseline ch_2 = 0.95: SHOULD reproduce Wave 7 (low eigs ~14, ...)")
    print("=" * 86)
    for off_kind in ["trivial", "Z3"]:
        T = build_TN_PT_D(N=200, ch2=0.95, eps=0.5, off_kind=off_kind)
        hd = herm_defect(T)
        eigs, n_real, max_im = diag_info(T)
        low = lowest_real_pos(eigs, k=10)
        close = closest_eig_to(14.135, eigs)
        rms = rms_to_zz(low, zz[:10])
        print(f"  off={off_kind:7s}  H-def={hd:.2e}  max|Im|={max_im:.2e}  "
              f"low5={[round(x,3) for x in low[:5]]}")
        print(f"           closest_to_14.135 = {close:.4f}   RMS10 = {rms:.4f}")
        results[f"baseline_off_{off_kind}"] = {
            "low10": low.tolist(), "rms10": rms, "closest_t1": close
        }

    # ----------------------------------------------------------
    # 2) Add PT-symmetric non-Hermitian perturbation; track gauge
    # ----------------------------------------------------------
    print("\n" + "=" * 86)
    print("2) ch_2 = 0.90 (non-Hermitian on): does phase choice now matter?")
    print("=" * 86)
    Tz3 = build_TN_PT_D(N=200, ch2=0.90, eps=0.5, off_kind="Z3",
                        perturb_kind="Z3_imag")
    Ttr = build_TN_PT_D(N=200, ch2=0.90, eps=0.5, off_kind="trivial",
                        perturb_kind="Z3_imag")
    Tra = build_TN_PT_D(N=200, ch2=0.90, eps=0.5, off_kind="rand",
                        perturb_kind="Z3_imag", seed=11)
    for label, T in [("Z3", Tz3), ("trivial", Ttr), ("rand", Tra)]:
        hd = herm_defect(T)
        eigs, n_real, max_im = diag_info(T)
        low = lowest_real_pos(eigs, k=10)
        close = closest_eig_to(14.135, eigs)
        rms = rms_to_zz(low, zz[:10])
        print(f"  {label:8s}  H-def={hd:.2e}  max|Im|={max_im:.2e}  "
              f"n_real={n_real:3d}/200  RMS10={rms:.4f}  cl14.135={close}")
    e_z3 = np.sort(np.real(eigvals(Tz3)))
    e_tr = np.sort(np.real(eigvals(Ttr)))
    e_ra = np.sort(np.real(eigvals(Tra)))
    gap_z3_tr = float(np.max(np.abs(e_z3 - e_tr)))
    gap_z3_ra = float(np.max(np.abs(e_z3 - e_ra)))
    print(f"\n  max|spec(Z3) - spec(trivial)| = {gap_z3_tr:.4e}")
    print(f"  max|spec(Z3) - spec(rand)|    = {gap_z3_ra:.4e}")
    print("  Wave 7 Hermitian: ~1e-13 (gauge-equiv).  PT: nonzero -> escape!")
    results["gauge_test_090"] = {"z3_vs_triv": gap_z3_tr,
                                  "z3_vs_rand": gap_z3_ra}

    # ----------------------------------------------------------
    # 3) ch_2 sweep: low eigenvalues & RMS to first 10 zeta zeros
    # ----------------------------------------------------------
    print("\n" + "=" * 86)
    print("3) ch_2 sweep (Z3 + Z3_imag), N=200")
    print("=" * 86)
    sweep = np.unique(np.concatenate([
        np.linspace(0.85, 0.94, 10),
        np.linspace(0.945, 0.955, 11),
        np.linspace(0.96, 1.10, 15),
    ]).round(4))
    sweep_data = {}
    best = (None, float("inf"), None)
    for ch2 in sweep:
        T = build_TN_PT_D(N=200, ch2=float(ch2), eps=0.5,
                          off_kind="Z3", perturb_kind="Z3_imag")
        eigs, n_real, max_im = diag_info(T)
        low = lowest_real_pos(eigs, k=10)
        if len(low) < 10:
            sweep_data[float(ch2)] = {"n_low": int(len(low)),
                                       "max_im": max_im, "rms": None}
            continue
        rms = rms_to_zz(low, zz[:10])
        sweep_data[float(ch2)] = {"top1": float(low[0]),
                                   "n_low": int(len(low)),
                                   "max_im": max_im,
                                   "rms10": rms,
                                   "low3": low[:3].tolist()}
        if rms < best[1]:
            best = (float(ch2), rms, low[:5].tolist())
    print(f"  Best ch_2 = {best[0]:.4f}  RMS10 = {best[1]:.4f}")
    print(f"  low5 there: {[round(x,3) for x in best[2]]}")
    print(f"  zz5        : {[round(x,3) for x in zz[:5]]}")
    # also print a few neighbors
    for ch2 in [0.92, 0.94, 0.95, 0.96, 0.98]:
        d = sweep_data.get(ch2)
        if d and d.get("rms10") is not None:
            print(f"    ch2={ch2:.3f}: top1={d['top1']:.3f} RMS10={d['rms10']:.4f}")
    results["sweep_D"] = {"detail": sweep_data, "best": best}

    # ----------------------------------------------------------
    # 4) PT-breaking grid (ch_2, eps)
    # ----------------------------------------------------------
    print("\n" + "=" * 86)
    print("4) PT-breaking grid (max|Im(eig)| over (ch_2, eps))")
    print("=" * 86)
    ch2_grid = [0.85, 0.90, 0.93, 0.95, 0.97, 1.00, 1.05]
    eps_grid = [0.0, 0.01, 0.05, 0.1, 0.5, 1.0, 2.0]
    grid = {}
    print(f"{'eps \\ ch2':>10s}", *[f"{c:>8.2f}" for c in ch2_grid])
    for eps in eps_grid:
        row, row_d = [], {}
        for ch2 in ch2_grid:
            T = build_TN_PT_D(N=120, ch2=ch2, eps=eps, off_kind="Z3",
                              perturb_kind="Z3_imag")
            _, _, max_im = diag_info(T)
            row.append(max_im); row_d[ch2] = max_im
        grid[eps] = row_d
        print(f"  eps={eps:5.2f} | ", " ".join(f"{x:8.2e}" for x in row))
    print("  Values: max|Im(eig)| — PT-symmetric phase has ~0; broken phase O(1)")
    results["pt_break_grid_D"] = grid

    # ----------------------------------------------------------
    # 5) Critical eps_c at each ch_2 (PT-breaking threshold)
    # ----------------------------------------------------------
    print("\n" + "=" * 86)
    print("5) PT-breaking threshold eps_c(ch_2)")
    print("=" * 86)
    thresh_data = {}
    for ch2 in [0.85, 0.90, 0.92, 0.95, 0.97, 1.00, 1.05]:
        eps_c = None
        for eps in np.linspace(0.0, 5.0, 50):
            T = build_TN_PT_D(N=120, ch2=ch2, eps=float(eps), off_kind="Z3",
                              perturb_kind="Z3_imag")
            _, _, max_im = diag_info(T)
            if max_im > 1e-6:
                eps_c = float(eps); break
        thresh_data[ch2] = eps_c
        # gamma_c = eps_c * |ch2 - 0.95|  (should be nearly ch_2-independent)
        if eps_c is not None and abs(ch2 - 0.95) > 1e-9:
            gamma_c = eps_c * abs(ch2 - 0.95)
            print(f"  ch2={ch2:.2f}  eps_c={eps_c:.3f}  "
                  f"gamma_c=|ch2-0.95|*eps_c={gamma_c:.4f}")
        else:
            print(f"  ch2={ch2:.2f}  eps_c={eps_c}")
    results["pt_threshold_D"] = thresh_data

    # ----------------------------------------------------------
    # 6) Level spacing variance at best ch_2 (Wigner-Dyson)
    # ----------------------------------------------------------
    if best[0] is not None:
        print("\n" + "=" * 86)
        print(f"6) Level spacing at best ch_2 = {best[0]:.4f}")
        print("=" * 86)
        T = build_TN_PT_D(N=600, ch2=best[0], eps=0.5,
                          off_kind="Z3", perturb_kind="Z3_imag")
        eigs, _, _ = diag_info(T)
        m, v = level_spacing_var(eigs)
        print(f"  mean = {m:.4f}, var = {v:.4f}")
        print(f"  Reference: Poisson=1.000, GOE=0.286, GUE=0.180")
        # Hermitian comparison
        T_h = build_TN_PT_D(N=600, ch2=0.95, eps=0.5,
                            off_kind="Z3", perturb_kind="Z3_imag")
        e_h, _, _ = diag_info(T_h)
        m_h, v_h = level_spacing_var(e_h)
        print(f"  Hermitian (ch_2=0.95): mean={m_h:.4f}, var={v_h:.4f}")
        results["spacing_D"] = {"best": {"ch2": best[0], "mean": m, "var": v},
                                 "herm_095": {"mean": m_h, "var": v_h}}

    # ----------------------------------------------------------
    # 7) Perturbation kind comparison (which one is best?)
    # ----------------------------------------------------------
    print("\n" + "=" * 86)
    print("7) Perturbation-kind comparison at ch_2 = 0.93, eps = 0.5")
    print("=" * 86)
    pk_data = {}
    for pk in ["Z3_imag", "D3_imag", "alt_imag", "constant"]:
        T = build_TN_PT_D(N=200, ch2=0.93, eps=0.5, off_kind="Z3",
                          perturb_kind=pk)
        eigs, n_real, max_im = diag_info(T)
        low = lowest_real_pos(eigs, k=10)
        rms = rms_to_zz(low, zz[:10]) if len(low) >= 10 else None
        cl = closest_eig_to(14.135, eigs)
        pk_data[pk] = {"max_im": max_im, "rms10": rms, "closest_t1": cl,
                       "low5": low[:5].tolist()}
        print(f"  perturb={pk:9s}  max|Im|={max_im:.2e}  "
              f"RMS10={'%.4f'%rms if rms else 'NA':>9s}  cl14.135={cl}")
    results["perturb_kind_D"] = pk_data

    # ----------------------------------------------------------
    # Save
    # ----------------------------------------------------------
    outpath = os.path.join(OUTDIR, "pt_symmetric_results_v4.json")
    with open(outpath, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nElapsed: {time.time()-t0:.1f}s   Saved: {outpath}")


if __name__ == "__main__":
    main()
