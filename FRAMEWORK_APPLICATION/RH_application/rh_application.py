"""
RH_APPLICATION.PY  —  Principia Fractalis framework applied to RHSpectralSurjectivityConjecture
==================================================================================================

APPLICATION MODE: use framework as given (per REFRESHER.md).
Targets Proposition 2: RH at alpha = 3/2 via the consciousness-modified Riemann
transfer operator T_N (Ch 9 Definition 'consciousness_zeta_op').

Deliverables in this script:
  (1) Build T_N exactly per Ch 9 line 162-175 spec, at consciousness threshold ch_2 = 0.95.
  (2) Verify Mechanism 1 (self-adjointness) numerically: at ch_2 = 0.95 the off-diagonal
      structure T_{n,n-1} = conj(T_{n-1,n}) forces Hermiticity; the diagonal delta C_n
      term vanishes (ch_2 - 0.95 = 0) so T_N is strictly Hermitian.
  (3) Verify Mechanism 2 (Z_3 phase symmetry) by direct computation: theta_n = 2 pi D_3(n)/3.
  (4) Verify Mechanism 3 (consciousness suppression) by sweeping ch_2 and tracking
      anti-Hermitian Frobenius norm growth as |ch_2 - 0.95| increases.
  (5) Diagonalize truncated T_N for N = 50, 100, 200, 400 and report:
       - smallest positive eigenvalue (universal coupling check vs pi/15)
       - top eigenvalues + spacings (RH zero correspondence check)
  (6) Numerical Spectral-Zeta Correspondence: compute R_f(3/2, s) at s = 1/2 + i*t_k
      for first 10 nontrivial Riemann zeros t_k via mpmath at 50-digit precision.
      Verify whether R_f(3/2, 1/2 + i t_k) -> 0 (the framework's empirical claim).

References:
  - Ch 9 Section "The Spectral-Zeta Correspondence"  (line 213-248)
  - Ch 9 Definition "Consciousness-Modified Riemann Operator" (line 160-175)
  - Ch 9 Theorem "Riemann Ground State Energy"  (line 252-259):  lambda_0 = pi/15
  - Ch 9 Theorem "Critical Line Constraint" + 3 mechanisms (line 276-289)
"""

import numpy as np
from mpmath import mp, mpf, mpc, exp, log, pi, cos, sin, zetazero, fabs, sqrt
import json
import os

mp.dps = 50  # 50-digit precision per task spec

# --------------------------------------------------------------------------------------
# Framework constants (from REFRESHER.md and Ch 9)
# --------------------------------------------------------------------------------------
ALPHA_RH = mpf("1.5")                # alpha = 3/2  (the RH resonance)
CH2_THRESHOLD = mpf("0.95")          # consciousness crystallization threshold
PI10 = pi / 10                       # universal coupling
LAMBDA0_TARGET = pi / 15             # ground-state energy at alpha = 3/2
ALPHA_SCALE = mpf("5e-6")            # consciousness scaling factor (Ch 9 line 173)

# --------------------------------------------------------------------------------------
# Base-3 digital sum function D_3(n)
# --------------------------------------------------------------------------------------
def D3(n):
    """Base-3 digital sum, the framework's fundamental fractal index."""
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

# Statistics of D_3 over [1, N]
def D3_statistics(N):
    vals = [D3(n) for n in range(1, N + 1)]
    arr = np.array(vals, dtype=float)
    return float(arr.mean()), float(arr.std())

# --------------------------------------------------------------------------------------
# Z_3 phase factors phi_n = exp(2 pi i D_3(n) / 3)
# --------------------------------------------------------------------------------------
def phi_phase(n):
    theta = mpf(2) * pi * mpf(D3(n)) / mpf(3)
    return mpc(cos(theta), sin(theta))

# --------------------------------------------------------------------------------------
# Resonant Quantum Geometry weight Psi_RQG
# --------------------------------------------------------------------------------------
def Psi_RQG(n, d3_mean, d3_var):
    if d3_var == 0:
        return mpf(1)
    delta = mpf(D3(n)) - mpf(d3_mean)
    return exp(-PI10 * delta * delta / mpf(d3_var))

# --------------------------------------------------------------------------------------
# Consciousness correction delta C_n
# --------------------------------------------------------------------------------------
def delta_C(n, ch2, alpha=ALPHA_SCALE):
    return alpha * (ch2 - CH2_THRESHOLD) * log(mpf(n) + 1)

# --------------------------------------------------------------------------------------
# Build T_N matrix (consciousness-modified Riemann operator, Ch 9 Def line 160-175)
# Returns: complex numpy array (we use complex128 — sufficient for diagonalization
#          comparisons; the mpmath precision is used for the R_f/zeta computations).
# --------------------------------------------------------------------------------------
def build_TN(N, ch2=CH2_THRESHOLD):
    # Pre-compute D_3 statistics over the truncation window
    d3_mean, d3_std = D3_statistics(N + 3)
    d3_var = d3_std * d3_std if d3_std > 0 else 1.0

    T = np.zeros((N, N), dtype=np.complex128)
    for n in range(1, N + 1):  # 1-indexed math, 0-indexed storage
        i = n - 1
        # Diagonal: T_{nn} = 1/(n+1) + 1/(n+2) + delta C_n
        diag = mpf(1) / mpf(n + 1) + mpf(1) / mpf(n + 2) + delta_C(n, ch2)
        T[i, i] = complex(float(diag.real if hasattr(diag, "real") else diag), 0.0)

        # Super-diagonal T_{n, n+1}
        if n + 1 <= N:
            phin = phi_phase(n)
            psi_n = Psi_RQG(n, d3_mean, d3_var)
            denom = mpf((n + 1)) * mpf((n + 2)) * mpf((n + 3))
            off_mag = mpf(1) / sqrt(denom) * psi_n
            off_val = phin * off_mag
            T[i, i + 1] = complex(float(off_val.real), float(off_val.imag))
            # Sub-diagonal T_{n+1, n} = conj(T_{n, n+1})
            T[i + 1, i] = complex(float(off_val.real), -float(off_val.imag))
    return T

# --------------------------------------------------------------------------------------
# Mechanism diagnostics
# --------------------------------------------------------------------------------------
def hermiticity_defect(T):
    """Frobenius norm of (T - T^H) — measures anti-Hermitian part magnitude."""
    return float(np.linalg.norm(T - T.conj().T, ord="fro"))

def z3_symmetry_check(N=30):
    """Mechanism 2: verify phi_n^3 = 1 for all n (Z_3 symmetry of phase factors)."""
    max_err = mpf(0)
    cube_roots = []
    for n in range(1, N + 1):
        p = phi_phase(n)
        cube = p * p * p
        err = fabs(cube - mpc(1, 0))
        if err > max_err:
            max_err = err
        cube_roots.append((n, D3(n), complex(float(p.real), float(p.imag)),
                            complex(float(cube.real), float(cube.imag))))
    return float(max_err), cube_roots

def consciousness_suppression_sweep(N, ch2_grid):
    """Mechanism 3: sweep ch_2 across grid and track anti-Hermitian growth."""
    rows = []
    for ch2 in ch2_grid:
        T = build_TN(N, ch2=mpf(ch2))
        rows.append((float(ch2), hermiticity_defect(T), float(np.linalg.norm(T, ord="fro"))))
    return rows

# --------------------------------------------------------------------------------------
# Diagonalize and extract spectral data
# --------------------------------------------------------------------------------------
def spectral_analysis(T):
    """Return sorted real eigenvalues + complex eigenvalues + smallest-positive."""
    # T is built to be Hermitian when ch_2 = 0.95, so use eigh for stability.
    # But still test against eig to detect non-Hermitian residuals.
    eigs = np.linalg.eigvals(T)
    # Real part sort
    re = np.real(eigs)
    im = np.imag(eigs)
    max_im = float(np.max(np.abs(im)))
    sorted_idx = np.argsort(re)
    sorted_eigs = eigs[sorted_idx]
    pos = re[sorted_idx]
    smallest_pos = None
    for v in pos:
        if v > 1e-10:
            smallest_pos = v
            break
    return {
        "max_imag_part": max_im,
        "all_eigs_sorted_by_real": sorted_eigs,
        "smallest_positive_real": smallest_pos,
    }

# --------------------------------------------------------------------------------------
# Fractal Resonance Function R_f(alpha, s)
# --------------------------------------------------------------------------------------
def Rf(alpha, s, N=50000):
    """R_f(alpha, s) = sum_{n=1}^{N} exp(i*pi*alpha*D_3(n)) / n^s  (truncated)."""
    alpha = mpc(alpha)
    s = mpc(s)
    total = mpc(0)
    for n in range(1, N + 1):
        phase = exp(mpc(0, 1) * pi * alpha * mpf(D3(n)))
        total += phase / mpf(n) ** s
    return total

# Cosine product factor from Ch 9 line 219
def cos_product(K=200):
    """Prod_{k=0}^{K-1} cos(pi/2 * 3^{-k})."""
    p = mpf(1)
    for k in range(K):
        p *= cos(pi / mpf(2) * mpf(3) ** (-k))
    return p

# --------------------------------------------------------------------------------------
# MAIN
# --------------------------------------------------------------------------------------
def main():
    print("=" * 80)
    print("PRINCIPIA FRACTALIS — RH APPLICATION  (alpha = 3/2, ch_2 = 0.95)")
    print("Working precision: mp.dps =", mp.dps)
    print("=" * 80)

    out = {"framework_constants": {
        "alpha_RH": str(ALPHA_RH),
        "ch2_threshold": str(CH2_THRESHOLD),
        "pi_over_10": str(PI10),
        "lambda_0_target_pi_over_15": str(LAMBDA0_TARGET),
        "alpha_scale": str(ALPHA_SCALE),
    }}

    # ------------------- D_3 sanity -------------------
    print("\n[A] D_3 sanity: first 12 values")
    d3_vals = [(n, D3(n)) for n in range(1, 13)]
    print("   ", d3_vals)
    out["D3_first_12"] = d3_vals

    # ------------------- Mechanism 2: Z_3 phase symmetry -------------------
    print("\n[B] Mechanism 2: Z_3 phase symmetry check — verify phi_n^3 = 1 for n = 1..30")
    max_err, phase_table = z3_symmetry_check(N=30)
    print(f"   max |phi_n^3 - 1| over n in [1,30] = {max_err:.2e}")
    print("   first 6 phase factors (n, D_3(n), phi_n, phi_n^3):")
    for row in phase_table[:6]:
        print(f"     n={row[0]:2d}  D3={row[1]}  phi={row[2]:.6f}  phi^3={row[3]:.6e}")
    out["mechanism_2_z3_max_cube_error"] = max_err

    # ------------------- Mechanism 1: build T_N at threshold, check Hermiticity -------------------
    print("\n[C] Mechanism 1: build T_N at ch_2 = 0.95, verify self-adjointness")
    Ns = [50, 100, 200, 400]
    out["mechanism_1_TN_at_threshold"] = []
    for N in Ns:
        T = build_TN(N, ch2=CH2_THRESHOLD)
        defect = hermiticity_defect(T)
        fro = float(np.linalg.norm(T, ord="fro"))
        print(f"   N={N:4d}  ||T - T^H||_F = {defect:.3e}   ||T||_F = {fro:.3f}   ratio = {defect/fro:.2e}")
        out["mechanism_1_TN_at_threshold"].append({"N": N, "defect_F": defect,
                                                   "frobenius_norm": fro, "ratio": defect/fro})

    # ------------------- Mechanism 3: consciousness suppression sweep -------------------
    print("\n[D] Mechanism 3: consciousness suppression sweep at N=100")
    ch2_grid = [0.80, 0.85, 0.90, 0.93, 0.94, 0.95, 0.96, 0.97, 1.00, 1.05]
    sweep = consciousness_suppression_sweep(100, ch2_grid)
    print(f"   {'ch_2':>6}  {'||T-T^H||_F':>14}  {'||T||_F':>10}")
    for row in sweep:
        print(f"   {row[0]:6.2f}  {row[1]:14.3e}  {row[2]:10.3f}")
    out["mechanism_3_ch2_sweep"] = [{"ch2": r[0], "defect_F": r[1], "frob": r[2]} for r in sweep]

    # ------------------- Diagonalization + universal-coupling check -------------------
    print("\n[E] Diagonalize T_N at ch_2 = 0.95; check lambda_0 ?= pi/15 = 0.20944")
    target = float(LAMBDA0_TARGET)
    print(f"   Target lambda_0 = pi/15 = {target:.10f}")
    out["lambda_0_target"] = target
    out["spectral_results"] = []
    for N in Ns:
        T = build_TN(N, ch2=CH2_THRESHOLD)
        # Hermitize (force exact Hermiticity for clean eigenvalues)
        Th = 0.5 * (T + T.conj().T)
        eigs = np.linalg.eigvalsh(Th)
        eigs_sorted = np.sort(eigs)
        # Smallest positive
        positives = eigs_sorted[eigs_sorted > 1e-12]
        sm_pos = float(positives[0]) if len(positives) > 0 else float("nan")
        # Top 10 eigenvalues
        top = [float(e) for e in eigs_sorted[-10:]]
        print(f"   N={N:4d}  lambda_min_pos = {sm_pos:.6f}   diff vs pi/15: {sm_pos - target:+.4f}")
        out["spectral_results"].append({
            "N": N,
            "smallest_positive_eig": sm_pos,
            "diff_vs_pi_over_15": sm_pos - target,
            "top_10_eigs": top,
            "min_eig": float(eigs_sorted[0]),
            "max_eig": float(eigs_sorted[-1]),
            "all_eigs_first_20": [float(e) for e in eigs_sorted[:20]],
        })

    # ------------------- Spectral-Zeta Correspondence numerical check -------------------
    print("\n[F] Spectral-Zeta Correspondence: compute R_f(3/2, s) at first 10 zeta zeros")
    print("    Per Ch 9 thm: when ch_2 = 0.95, R_f zeros bijectively map to zeta zeros.")
    print(f"    Cosine product Prod cos(pi/2 * 3^{{-k}}) = ", end="")
    Cprod = cos_product(K=200)
    print(f"{float(Cprod):.10f}")
    out["cos_product"] = float(Cprod)

    # Use moderate Rf truncation due to series convergence on critical line being slow.
    # Conditional convergence is the issue, but on Re(s)=1/2 partial sums oscillate.
    # We use Cesaro-style: average of two partial sums at N and 2N for stability.
    def Rf_critical(alpha, t, N=20000):
        s = mpc(mpf("0.5"), mpf(t))
        return Rf(alpha, s, N=N)

    print("\n   Computing R_f(3/2, 1/2 + i*t_k) for first 10 Riemann zeros (N=20000)...")
    out["Rf_at_zeta_zeros"] = []
    for k in range(1, 11):
        tk = zetazero(k).imag
        rf_val = Rf_critical(ALPHA_RH, tk, N=20000)
        rf_val_2N = Rf_critical(ALPHA_RH, tk, N=40000)
        avg = (rf_val + rf_val_2N) / 2
        mag = fabs(avg)
        print(f"   k={k:2d}  t_k={float(tk):11.6f}   |R_f(3/2,1/2+i t_k)|_avg = {float(mag):.4e}")
        out["Rf_at_zeta_zeros"].append({
            "k": k,
            "t_k": float(tk),
            "Rf_N20k_real": float(rf_val.real),
            "Rf_N20k_imag": float(rf_val.imag),
            "Rf_N40k_real": float(rf_val_2N.real),
            "Rf_N40k_imag": float(rf_val_2N.imag),
            "avg_magnitude": float(mag),
        })

    # Control: also evaluate R_f off-critical-line as a baseline
    print("\n   CONTROL: R_f(3/2, sigma + i*14.135) for sigma in {0.3, 0.5, 0.7, 1.0}")
    out["Rf_off_critical_control"] = []
    t1 = float(zetazero(1).imag)
    for sigma in [0.3, 0.5, 0.7, 1.0]:
        s = mpc(mpf(sigma), mpf(t1))
        v = Rf(ALPHA_RH, s, N=20000)
        print(f"     sigma={sigma:.2f}  |R_f| = {float(fabs(v)):.4e}")
        out["Rf_off_critical_control"].append({"sigma": sigma, "magnitude": float(fabs(v))})

    # ------------------- Spectral bijection (eigenvalue vs zeta-zero imag parts) -------------------
    print("\n[G] Spectral bijection check: eigenvalues of T_N vs imaginary parts of zeta zeros")
    print("    The framework's claim: spec(T_N) at ch_2=0.95 ↔ {Im(rho_k)} of zeta zeros.")
    T200 = build_TN(200, ch2=CH2_THRESHOLD)
    T200h = 0.5 * (T200 + T200.conj().T)
    eigs200 = np.sort(np.linalg.eigvalsh(T200h))
    # Take ABSOLUTE values of eigenvalues sorted ascending
    abs_eigs = np.sort(np.abs(eigs200))
    abs_eigs_nonzero = abs_eigs[abs_eigs > 1e-10][:20]
    zz = [float(zetazero(k).imag) for k in range(1, 21)]
    print(f"   {'k':>3}  {'Im(rho_k)':>12}  {'|eig_k|*scale?':>16}  ratio? ")
    # Crudely test: scale eigenvalues to match first zero — what's the implied scaling?
    if abs_eigs_nonzero[0] > 0:
        scale = zz[0] / abs_eigs_nonzero[0]
    else:
        scale = float("nan")
    print(f"   (Empirical scale to match k=1: zz[0]/|eig[0]| = {scale:.3f})")
    rows_g = []
    for k in range(20):
        scaled = abs_eigs_nonzero[k] * scale if k < len(abs_eigs_nonzero) else float("nan")
        ratio = scaled / zz[k] if k < len(abs_eigs_nonzero) else float("nan")
        print(f"   {k+1:3d}  {zz[k]:12.4f}  {scaled:16.4f}  {ratio:.4f}")
        rows_g.append({"k": k+1, "zeta_zero_im": zz[k], "scaled_eig": float(scaled),
                        "ratio": float(ratio)})
    out["spectral_bijection"] = rows_g
    out["spectral_bijection_empirical_scale"] = float(scale)

    # Save results
    outpath = "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/RH_application/rh_results.json"
    with open(outpath, "w") as f:
        json.dump(out, f, indent=2, default=str)
    print(f"\nResults saved to: {outpath}")
    return out


if __name__ == "__main__":
    main()
