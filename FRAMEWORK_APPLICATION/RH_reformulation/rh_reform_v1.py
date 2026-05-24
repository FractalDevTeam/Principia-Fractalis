"""
RH_REFORM_V1.PY — Reformulated T_N per Wave 4 specs.

Goals (per Wave 4 RH agent):
  (R1) Mechanism 3 (ch_2 dependence) enters OFF-diagonal phases so ch_2 != 0.95
       genuinely breaks Hermiticity.
  (R2) alpha_scale = O(1), not 5e-6.
  (R3) Matrix-entry scaling produces eigenvalues O(10), not -> 0.
  (R4) Cosine product runs k >= 1 (avoid divide-by-zero at k=0).
  (R5) At ch_2 = 0.95: first eigenvalue close to 14.135 (first zeta zero im part)
       within 5% at N=400.

Construction proposal (PROPOSAL_V1):
  T_{n,n}   = D(n) * (1 + alpha_scale * (ch_2 - 0.95) * eps_n_real)
           where D(n) is a Berry-Keating-like "energy ladder":
              D(n) = 2*pi * n / log(n + 2)      [E_n ~ 2 pi n / log(n)]
           and eps_n_real is REAL bounded perturbation on diagonal (does
           not break Hermiticity by itself).

  T_{n,n+1} = phi_n * sqrt(coupling(n)) * exp(i * (ch_2 - 0.95) * theta_n)
           where phi_n = exp(2 pi i D_3(n)/3)  (Z_3 phase, framework-prescribed)
                 theta_n = pi * D_3(n+1)        (chirality phase, ch_2-dependent)
                 coupling(n) tested below.

  T_{n+1,n} = conj(T_{n,n+1})    [Hermitian conjugate, AT ch_2=0.95 only,
              because the (ch_2 - 0.95) phase factor flips sign under conj
              ONLY when ch_2 = 0.95 makes the phase identity]

  IMPORTANT: To make Hermiticity break OFF the threshold we set
       T_{n+1,n}_independent = conj_phi_n * sqrt(coupling(n))
                              * exp(-i * (ch_2 - 0.95) * theta_n)
  At ch_2 = 0.95 the exponential = 1 and the two reduce to T_{n,n+1}
  and its conjugate. Off threshold they do NOT satisfy
  T_{n+1,n} = conj(T_{n,n+1}) because theta_n applies asymmetrically.

  Specifically we use:
       T_{n,n+1}  = phi_n * sqrt(c_n) * exp(+i * eta * theta_n)
       T_{n+1,n} = conj(phi_n) * sqrt(c_n) * exp(+i * eta * theta_n)
  where eta = (ch_2 - 0.95). At eta = 0:  T_{n+1,n} = conj(T_{n,n+1})  ✓
  At eta != 0: T_{n+1,n} != conj(T_{n,n+1}) because the second exp
       is NOT conjugated, but the first IS, generating an anti-Hermitian piece.

Test 3 coupling profiles:
   (A) c_n = 1 / log(n+2)         [LOG decay — Hilbert-Polya-like]
   (B) c_n = 1 / sqrt(n+1)        [Power decay — moderate]
   (C) c_n = (D(n) * D(n+1)) / 100  [Energy-ladder coupling, matches diag scale]
"""

import numpy as np
from mpmath import mp, mpf, mpc, exp, log, pi, cos, sin, zetazero, fabs, sqrt
import json
import os
import time

mp.dps = 30  # 30-digit precision adequate for spectrum O(10)

# ---------------------------------------------------------------------------
# Framework constants
# ---------------------------------------------------------------------------
ALPHA_RH = mpf("1.5")
CH2_THRESHOLD = mpf("0.95")
ALPHA_SCALE = mpf("1.0")             # R2: O(1) not 5e-6

PI_NP = float(pi)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def D3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

def phi_phase_np(n):
    """Z_3 phase exp(2*pi*i*D_3(n)/3)  -- returns complex (np)."""
    theta = 2.0 * PI_NP * D3(n) / 3.0
    return complex(np.cos(theta), np.sin(theta))

def D_BK(n):
    """Berry-Keating-style energy ladder D(n) = 2 pi n / log(n + 2)."""
    return 2.0 * PI_NP * n / np.log(n + 2.0)

# ---------------------------------------------------------------------------
# Build T_N (REFORMULATED)
# ---------------------------------------------------------------------------
def build_TN_reform(N, ch2=0.95, coupling="A", alpha_scale=1.0,
                   diag_perturb_mode="logn"):
    """Reformulated T_N.

    coupling in {'A', 'B', 'C'}:
        A: c_n = 1 / log(n+2)
        B: c_n = 1 / sqrt(n+1)
        C: c_n = sqrt(D(n) * D(n+1)) / 10   (slightly weaker than diag)

    diag_perturb_mode: shape of eps_n_real on diagonal (still real, so
        doesn't itself break Hermiticity; the breaking comes from off-diag).
    """
    eta = ch2 - 0.95  # ch_2 deviation from threshold
    T = np.zeros((N, N), dtype=np.complex128)
    for n in range(1, N + 1):
        i = n - 1

        # Diagonal: D(n) * (1 + alpha_scale * eta * log(n+2)/10)
        diag = D_BK(n)
        if diag_perturb_mode == "logn":
            eps_real = np.log(n + 2.0) / 10.0
        elif diag_perturb_mode == "const":
            eps_real = 1.0
        else:
            eps_real = 0.0
        T[i, i] = diag * (1.0 + alpha_scale * eta * eps_real)

        # Off-diagonal
        if n + 1 <= N:
            if coupling == "A":
                c_n = 1.0 / np.log(n + 2.0)
            elif coupling == "B":
                c_n = 1.0 / np.sqrt(n + 1.0)
            elif coupling == "C":
                c_n = np.sqrt(D_BK(n) * D_BK(n + 1)) / 10.0
            else:
                raise ValueError("coupling must be A, B, or C")
            sqrt_c = np.sqrt(c_n)

            phin = phi_phase_np(n)
            theta_n = PI_NP * D3(n + 1)  # chirality phase

            # Mechanism 3 mediator
            ch2_phase = np.exp(1j * alpha_scale * eta * theta_n)

            # T_{n, n+1} = phi_n * sqrt(c_n) * ch2_phase
            T[i, i + 1] = phin * sqrt_c * ch2_phase
            # T_{n+1, n} = conj(phi_n) * sqrt(c_n) * ch2_phase
            #   (same ch2_phase — NOT conjugated — breaks Hermiticity off-thresh)
            T[i + 1, i] = np.conj(phin) * sqrt_c * ch2_phase
    return T

# ---------------------------------------------------------------------------
# Hermiticity diagnostics
# ---------------------------------------------------------------------------
def hermiticity_defect(T):
    return float(np.linalg.norm(T - T.conj().T, ord="fro"))

def spectral_diagnostics(T, top=10, anchors=None):
    """Diagonalize and return top eigenvalues + closeness to ζ-zeros."""
    eigs = np.linalg.eigvals(T)
    re = np.real(eigs)
    im = np.imag(eigs)
    max_im = float(np.max(np.abs(im)))
    # Sort by REAL part ascending
    idx = np.argsort(re)
    eigs_s = eigs[idx]

    # Get smallest 'top' positive-real-part eigenvalues
    re_s = re[idx]
    pos_mask = re_s > 1e-8
    eigs_pos = eigs_s[pos_mask]
    top_eigs = eigs_pos[:top]
    top_re = np.real(top_eigs).tolist()

    # If anchors provided, compute closest matches
    closest = []
    if anchors is not None:
        for a in anchors:
            diffs = np.abs(re_s - a)
            j = int(np.argmin(diffs))
            closest.append({
                "anchor": float(a),
                "closest_eig_re": float(re_s[j]),
                "closest_eig_im": float(im[idx][j]),
                "abs_diff": float(abs(re_s[j] - a)),
                "pct_diff": float(abs(re_s[j] - a) / a * 100.0),
            })
    return {
        "max_imag_part": max_im,
        "top_real_parts": top_re,
        "closest_to_anchors": closest,
    }

# ---------------------------------------------------------------------------
# Helper: get first M Riemann zeros (imag parts)
# ---------------------------------------------------------------------------
def zeta_zeros(M):
    out = []
    for k in range(1, M + 1):
        out.append(float(zetazero(k).imag))
    return out

# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------
def main():
    t0 = time.time()
    print("=" * 86)
    print("RH REFORMULATION V1  —  Berry-Keating-inspired T_N with framework Z_3 phase")
    print("=" * 86)

    out = {
        "spec": {
            "diag": "D(n) = 2*pi*n/log(n+2)",
            "off_diag": "T_{n,n+1} = phi_n * sqrt(c_n) * exp(i*eta*theta_n);  "
                        "T_{n+1,n} = conj(phi_n)*sqrt(c_n)*exp(i*eta*theta_n)",
            "alpha_scale": float(ALPHA_SCALE),
            "ch2_threshold": float(CH2_THRESHOLD),
            "cos_product_starts_at_k": 1,
        },
        "tests": []
    }

    # First 20 Riemann zeros for comparison
    print("\nLoading first 20 Riemann zero imaginary parts...")
    zz = zeta_zeros(20)
    print(f"  t_1..t_5 = {zz[:5]}")
    out["zeta_zeros_first_20"] = zz

    # Sanity: diagonal scale at modest n
    print("\nDiagonal D(n) scale check:")
    for n in [1, 2, 5, 10, 20, 50, 100, 200, 400]:
        print(f"  D({n:3d}) = {D_BK(n):10.4f}")
    out["D_BK_samples"] = {n: D_BK(n) for n in [1, 2, 5, 10, 20, 50, 100, 200, 400]}

    # TEST 1: at ch_2 = 0.95, sweep coupling profiles and N, check eigenvalue match
    print("\n" + "=" * 86)
    print("TEST 1: At ch_2 = 0.95, do top eigenvalues align with zeta-zero imag parts?")
    print("=" * 86)
    for coupling in ["A", "B", "C"]:
        print(f"\n--- Coupling {coupling} ---")
        for N in [100, 200, 400]:
            T = build_TN_reform(N, ch2=0.95, coupling=coupling)
            herm_def = hermiticity_defect(T)
            diag = spectral_diagnostics(T, top=10, anchors=zz[:10])
            # match metric: avg pct error of closest matches
            avg_pct = np.mean([c["pct_diff"] for c in diag["closest_to_anchors"]])
            print(f"  N={N:4d}  ||T-T^H||_F={herm_def:.3e}  "
                  f"max|Im(eig)|={diag['max_imag_part']:.3e}  "
                  f"avg pct err to ζ-zeros = {avg_pct:.2f}%")
            print(f"      top 5 real eigs: {[round(x,3) for x in diag['top_real_parts'][:5]]}")
            print(f"      closest to t_1=14.135: eig={diag['closest_to_anchors'][0]['closest_eig_re']:.3f}"
                  f"  diff={diag['closest_to_anchors'][0]['abs_diff']:.3f} "
                  f"({diag['closest_to_anchors'][0]['pct_diff']:.2f}%)")
            out["tests"].append({
                "name": f"test1_coupling_{coupling}_N{N}",
                "ch2": 0.95, "coupling": coupling, "N": N,
                "herm_defect_F": herm_def, "max_imag": diag["max_imag_part"],
                "top_real_eigs": diag["top_real_parts"][:10],
                "anchors_match": diag["closest_to_anchors"],
                "avg_pct_err": float(avg_pct),
            })

    # TEST 2: Hermiticity breakage off threshold (use coupling C as representative)
    print("\n" + "=" * 86)
    print("TEST 2: Hermiticity sweep over ch_2 grid at N=200, coupling A")
    print("=" * 86)
    print(f"  {'ch_2':>6}  {'||T-T^H||_F':>14}  {'max|Im(eig)|':>14}  "
          f"{'lambda_1_re':>12}  {'pct diff to 14.135':>18}")
    sweep = []
    for ch2 in [0.80, 0.85, 0.90, 0.93, 0.94, 0.95, 0.96, 0.97, 1.00, 1.05]:
        T = build_TN_reform(200, ch2=ch2, coupling="A")
        herm = hermiticity_defect(T)
        diag = spectral_diagnostics(T, top=3, anchors=[14.13472514])
        lam = diag["closest_to_anchors"][0]["closest_eig_re"]
        pct = diag["closest_to_anchors"][0]["pct_diff"]
        print(f"  {ch2:6.2f}  {herm:14.3e}  {diag['max_imag_part']:14.3e}  "
              f"{lam:12.4f}  {pct:18.3f}")
        sweep.append({"ch2": ch2, "herm_def": herm,
                      "max_imag": diag["max_imag_part"],
                      "lam1_re": lam, "pct_err": pct})
    out["test2_ch2_sweep"] = sweep

    # TEST 3: Cosine product k >= 1 (R4)
    print("\n" + "=" * 86)
    print("TEST 3: Cosine product Prod cos(pi/2 * 3^-k) for k = 1..K (NOT starting at k=0)")
    print("=" * 86)
    for K in [10, 50, 100, 200]:
        p = mpf(1)
        for k in range(1, K + 1):  # k >= 1
            p *= cos(pi / mpf(2) * mpf(3) ** (-k))
        print(f"  K={K:3d}  Prod = {float(p):.10f}")
        out.setdefault("cos_product_k_ge_1", {})[K] = float(p)

    # SAVE
    outpath = "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/RH_reformulation/rh_reform_v1_results.json"
    with open(outpath, "w") as f:
        json.dump(out, f, indent=2, default=str)
    print(f"\nElapsed: {time.time()-t0:.1f} s")
    print(f"Results saved to: {outpath}")
    return out


if __name__ == "__main__":
    main()
