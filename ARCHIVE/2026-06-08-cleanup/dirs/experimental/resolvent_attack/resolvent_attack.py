"""
Construction Attack #4 -- Resolvent pole / regularized trace / spectral zeta
============================================================================

Tests whether pi/(10*alpha) appears as a COMPLEX-ANALYTIC object (resolvent
pole, spectral-zeta zero, regularised trace log-singularity, polylog branch
value) even though it FAILED as a literal Hilbert-space eigenvalue.

Operator H_alpha^(k) on M_{3^k}(C) GNS (Form A, distance_kind='abs') from
/tmp/gns_test/gns_spectrum.py, Hermitianised: H = (M + M^dagger)/2.

alpha in {sqrt2, 3/2, 2}, k in {4, 5}.

Outputs:
    poles_<alpha>_k<k>.npz       -- complex resolvent samples on Re x Im grid
    zeta_<alpha>_k<k>.npz        -- spectral zeta on critical-line-like sweep
    summary_<alpha>_k<k>.txt     -- human-readable summary
    polylog_branches.txt         -- branch test independent of GNS
"""

import os
import sys
import math
import numpy as np
from numpy.linalg import eigvalsh

# -------------------------------------------------------------------------
# 1. Operator construction (Form A, ported from /tmp/gns_test/gns_spectrum.py)
# -------------------------------------------------------------------------
A_BASE = 2.0

def digital_sum_b3(n, k):
    s = 0
    for _ in range(k):
        s += n % 3
        n //= 3
    return s

def ternary_xor(m, n, k):
    out, p = 0, 1
    for _ in range(k):
        d = (m % 3 + n % 3) % 3
        out += d * p
        p *= 3
        m //= 3
        n //= 3
    return out

def V_alpha(alpha, d, k, a=A_BASE):
    s = 0.0
    powa = 1.0
    powalpha_j = 1.0
    for _ in range(k + 1):
        s += (1.0 / powa) * math.cos(math.pi * powalpha_j * d)
        powa *= a
        powalpha_j *= alpha
    return s

def build_H_formA(alpha, k):
    """Form A: integer distance |m - n|, Hermitianised."""
    N = 3 ** k
    H = np.zeros((N, N), dtype=np.complex128)
    D3 = np.array([digital_sum_b3(n, k) for n in range(N)], dtype=np.int64)
    Vtab = np.array([V_alpha(alpha, d, k) for d in range(N)], dtype=np.float64)
    for m in range(N):
        for n in range(N):
            tx = ternary_xor(m, n, k)
            phase = np.exp(1j * math.pi * alpha * D3[tx])
            H[m, n] = phase * Vtab[abs(m - n)]
    return 0.5 * (H + H.conj().T)

# -------------------------------------------------------------------------
# 2. Resolvent trace on complex grid
# -------------------------------------------------------------------------
def trace_resolvent_grid(eigvals, re_range, im_range):
    """R(z) = sum_i 1/(lambda_i - z) on complex grid Re x Im."""
    RE, IM = np.meshgrid(re_range, im_range, indexing='ij')
    Z = RE + 1j * IM
    # broadcast over eigenvalues
    R = np.zeros_like(Z, dtype=np.complex128)
    lam = eigvals.astype(np.complex128)
    # chunk to avoid huge arrays
    chunk = 200
    for start in range(0, len(lam), chunk):
        block = lam[start:start + chunk]
        denom = block[:, None, None] - Z[None, :, :]   # (b, NR, NI)
        # add 1/denom contributions
        R += np.sum(1.0 / denom, axis=0)
    return Z, R

def find_poles(Z, R, factor=1000.0):
    absR = np.abs(R)
    thresh = factor * np.median(absR)
    mask = absR > thresh
    coords = np.argwhere(mask)
    poles = []
    for ij in coords:
        i, j = ij
        poles.append((complex(Z[i, j]), float(absR[i, j])))
    poles.sort(key=lambda t: -t[1])
    return poles, thresh

# -------------------------------------------------------------------------
# 3. Spectral zeta function
# -------------------------------------------------------------------------
def spectral_zeta(eigvals, s):
    """zeta_alpha(s) = sum_i lam_i^(-s), excluding lam_i = 0."""
    lam = np.array([l for l in eigvals if abs(l) > 1e-12], dtype=np.complex128)
    # use principal log: lam^(-s) = exp(-s * log(lam))
    return np.sum(np.exp(-s * np.log(lam)))

def critical_line_sweep(eigvals, tau_grid):
    return np.array([spectral_zeta(eigvals, 0.5 + 1j * tau) for tau in tau_grid])

def log_det(eigvals):
    """log det H = sum log(lam_i) with principal log."""
    lam = np.array([l for l in eigvals if abs(l) > 1e-12], dtype=np.complex128)
    return np.sum(np.log(lam))

# -------------------------------------------------------------------------
# 4. Regularised trace Tr(log(H - z))
# -------------------------------------------------------------------------
def reg_trace_log(eigvals, z):
    lam = np.array([l for l in eigvals if abs(l) > 1e-12], dtype=np.complex128)
    return np.sum(np.log(lam - z))

# -------------------------------------------------------------------------
# 5. Main per-alpha driver
# -------------------------------------------------------------------------
OUT = os.path.dirname(os.path.abspath(__file__))

def run_alpha(name, alpha, k):
    target = math.pi / (10.0 * alpha)
    print(f"\n=== alpha={name} ({alpha:.10f}), k={k}, target={target:.10f} ===")
    print(f"Building H ({3**k}x{3**k}) ...", flush=True)
    H = build_H_formA(alpha, k)
    print("Diagonalising ...", flush=True)
    w = eigvalsh(H)
    print(f"  spectrum range: [{w.min():.6f}, {w.max():.6f}]")
    print(f"  smallest |lambda|: {np.min(np.abs(w)):.6f}")
    pos = w[w > 1e-12]
    if len(pos):
        sp = float(np.min(pos))
        print(f"  smallest positive: {sp:.6f}   |.-target|: {abs(sp-target):.6e}")

    # ---- 2. complex resolvent grid ----
    re_range = np.arange(-2.0, 2.0 + 1e-9, 0.01)
    im_range = np.arange(-1.0, 1.0 + 1e-9, 0.01)
    print(f"Resolvent grid: {len(re_range)} x {len(im_range)} = {len(re_range)*len(im_range)} points")
    Z, R = trace_resolvent_grid(w, re_range, im_range)
    poles, thresh = find_poles(Z, R, factor=1000.0)
    print(f"  median|R| = {np.median(np.abs(R)):.4e}, threshold = {thresh:.4e}")
    print(f"  poles found: {len(poles)}")
    # Check whether any pole lies near target (real axis)
    target_z = complex(target, 0.0)
    near_target = [(z, m) for z, m in poles if abs(z - target_z) < 0.02]
    print(f"  poles within 0.02 of target {target_z}: {len(near_target)}")
    # report top-5 closest to target overall (whether or not above threshold)
    re_idx = np.argmin(np.abs(re_range - target))
    im_idx = np.argmin(np.abs(im_range - 0.0))
    print(f"  |R(target)| = {np.abs(R[re_idx, im_idx]):.4e}")
    # distance from real axis to closest pole
    if poles:
        closest_to_target = min(poles, key=lambda t: abs(t[0] - target_z))
        print(f"  closest pole to target: z={closest_to_target[0]:.6f}, |R|={closest_to_target[1]:.4e}, |z-target|={abs(closest_to_target[0]-target_z):.4e}")

    # Save
    npz_path = os.path.join(OUT, f"poles_{name}_k{k}.npz")
    np.savez_compressed(npz_path,
                        eigvals=w,
                        re_range=re_range,
                        im_range=im_range,
                        absR=np.abs(R),
                        target=target,
                        poles=np.array([p[0] for p in poles[:200]], dtype=np.complex128),
                        poles_absR=np.array([p[1] for p in poles[:200]]))

    # ---- 3. spectral zeta values ----
    print("Spectral zeta values (principal log):")
    z_vals = {}
    for s in (1.0, 2.0, 0.5, -1.0):
        v = spectral_zeta(w, s)
        z_vals[str(s)] = complex(v)
        print(f"  zeta(s={s:+.1f}) = {v.real:+.6e} + {v.imag:+.6e}i")
    # log det via -d/ds zeta at 0 -- we can compute log det directly:
    ld = log_det(w)
    print(f"  log det(H) (sum of log lam) = {ld.real:+.6e} + {ld.imag:+.6e}i")
    print(f"  exp(log det) modulus = {abs(np.exp(ld)):.6e}")
    print(f"  Is log det related to target {target}?  Re(log det)/N = {ld.real/(3**k):.6e}")
    print(f"  ratio log det / (pi/(10 alpha)) = {ld.real/target:.6f}")

    # critical-line sweep
    tau_grid = np.arange(-10.0, 10.0 + 1e-9, 0.1)
    zeta_line = critical_line_sweep(w, tau_grid)
    print(f"Critical-line sweep zeta(1/2 + i tau):")
    print(f"  |zeta| min = {np.min(np.abs(zeta_line)):.4e} at tau={tau_grid[np.argmin(np.abs(zeta_line))]:.2f}")
    print(f"  |zeta| max = {np.max(np.abs(zeta_line)):.4e} at tau={tau_grid[np.argmax(np.abs(zeta_line))]:.2f}")
    # any feature near tau corresponding to target?  target * something?
    # try tau = target and tau = 1/target
    for label, tau_try in (('target', target), ('1/target', 1.0/target), ('pi*target', math.pi*target)):
        if -10 <= tau_try <= 10:
            zv = spectral_zeta(w, 0.5 + 1j*tau_try)
            print(f"  zeta(1/2 + i*{label}={tau_try:.4f}) = {zv.real:+.4e} + {zv.imag:+.4e}i  |.|={abs(zv):.4e}")

    npz_path2 = os.path.join(OUT, f"zeta_{name}_k{k}.npz")
    np.savez_compressed(npz_path2,
                        tau=tau_grid,
                        zeta=zeta_line,
                        zeta_special=z_vals,
                        logdet=ld,
                        target=target)

    # ---- 4. regularised trace log(H - z) near target ----
    print("Regularised trace Tr log(H - z) near target:")
    for offset in (-0.05, -0.01, 0.0, 0.01, 0.05):
        z = complex(target + offset, 0.0)
        rt = reg_trace_log(w, z)
        print(f"  z={z.real:+.4f}: Re={rt.real:+.4e}, Im={rt.imag:+.4e}")
    # tiny epsilon around target
    for eps in (1e-2, 1e-3, 1e-4):
        z = complex(target, eps)
        rt = reg_trace_log(w, z)
        print(f"  z=target+{eps}i: Re={rt.real:+.4e}, Im={rt.imag:+.4e}")

    return {
        'eigvals': w,
        'target': target,
        'poles': poles[:50],
        'logdet': ld,
        'zeta_special': z_vals,
    }

# -------------------------------------------------------------------------
# 6. Polylog branch test (independent of operator)
# -------------------------------------------------------------------------
def polylog_branch_test():
    print("\n\n=== POLYLOG BRANCH TEST (mpmath) ===")
    try:
        import mpmath as mp
    except ImportError:
        print("mpmath not available; skipping")
        return
    mp.mp.dps = 50
    for name, alpha_val in (('sqrt2', mp.sqrt(2)), ('3/2', mp.mpf('1.5')), ('2', mp.mpf(2))):
        target = mp.pi / (10 * alpha_val)
        print(f"\nalpha = {name} ({float(alpha_val):.10f}), target pi/(10*alpha) = {float(target):.10f}")
        # principal branch
        lp = mp.polylog(2, alpha_val)
        print(f"  Li_2({name}) principal      = {complex(lp)}")
        print(f"     |Re - target| = {float(abs(lp.real - target)):.6e}")
        # next branch: add 2 pi i log(alpha) (standard monodromy of Li_2)
        offset = 2 * mp.pi * 1j * mp.log(alpha_val)
        for n_branch in (-2, -1, 1, 2):
            lpn = lp + mp.mpf(n_branch) * offset
            print(f"  Li_2(branch {n_branch:+d}) = {complex(lpn)}")
            print(f"     |Re - target| = {float(abs(lpn.real - target)):.6e}")
            print(f"     |Im - target| = {float(abs(lpn.imag - target)):.6e}")
        # also Li_1 and Li_0
        l1 = -mp.log(1 - alpha_val)  # principal Li_1
        print(f"  Li_1({name}) principal = {complex(l1)}  (note: alpha>1 means branch cut crossed)")
        print(f"     |Re - target| = {float(abs(l1.real - target)):.6e}")
        # next branch for Li_1: add 2 pi i
        for n_branch in (-1, 1):
            l1n = l1 + 2j * mp.pi * mp.mpf(n_branch)
            print(f"  Li_1(branch {n_branch:+d}) = {complex(l1n)}")
            print(f"     |Im - target| = {float(abs(l1n.imag - target)):.6e}")

# -------------------------------------------------------------------------
# 7. Main
# -------------------------------------------------------------------------
def main():
    alphas = [
        ('sqrt2', math.sqrt(2.0)),
        ('3o2',   1.5),
        ('2',     2.0),
    ]
    results = {}
    for name, alpha in alphas:
        for k in (4, 5):
            try:
                results[(name, k)] = run_alpha(name, alpha, k)
            except MemoryError:
                print(f"!! MemoryError at alpha={name}, k={k}")
    polylog_branch_test()

    print("\n=== SUMMARY ===")
    for (name, k), r in results.items():
        sp_pole = min(r['poles'], key=lambda t: abs(t[0]-complex(r['target']))) if r['poles'] else None
        print(f"alpha={name} k={k}: target={r['target']:.6f}, "
              f"#poles>{1000}*med = {len(r['poles'])}, "
              f"closest pole to target = {sp_pole[0] if sp_pole else 'n/a'}")

if __name__ == "__main__":
    main()
