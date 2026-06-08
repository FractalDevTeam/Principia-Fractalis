"""
05_strong_coupling_limit.py

In the diagonal-dominant regime tested in (04), the off-diagonal Z_3
holonomies are perturbatively irrelevant. To genuinely test whether
the 2D plaquette holonomy can create GUE-like statistics matching
zeta zeros, we need a regime where the off-diagonal couplings dominate
the dynamics — i.e. tight-binding limit.

Configurations tested:
  Config A: no diagonal (pure hopping); diagonal = 0
            This is the classic tight-binding lattice with Z_3 magnetic
            flux through plaquettes (Hofstadter-like).
  Config B: weak diagonal (Berry-Keating scaled DOWN by 1/(N^2)).
  Config C: only framework diagonal scale (universal coupling form),
            diagonal small and proportional to alpha/N.

In each case, framework vs trivial vs random phases.

Then test:
  - gauge non-invariance (rms framework-trivial)
  - GUE statistics (variance of unfolded spacings)
  - Spectrum matches zeta zeros after appropriate rescaling
"""

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np
import scipy.sparse as sp
import scipy.linalg as la
import json

from importlib import util
spec = util.spec_from_file_location("construct", os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "01_construct_H_graph.py"))
construct = util.module_from_spec(spec)
spec.loader.exec_module(construct)

OUT = os.path.dirname(os.path.abspath(__file__))

ZETA_ZEROS = np.array([
    14.134725141734693, 21.022039638771555, 25.010857580145688,
    30.424876125859513, 32.935061587739190, 37.586178158825671,
    40.918719012147495, 43.327073280914999, 48.005150881167160,
    49.773832477672302, 52.970321477714460, 56.446247697063394,
    59.347044002602353, 60.831778524609810, 65.112544048081607,
    67.079810529494173, 69.546401711173980, 72.067157674481907,
    75.704690699083933, 77.144840068874806,
])


def D3(n):
    s = 0
    n = abs(int(n))
    while n > 0:
        s += n % 3
        n //= 3
    return s


def build_graph_general(N, alpha, ch_2, diag_func, phase_mode, c_h=1.0, c_v=1.0, c_d=0.5, rng=None):
    """Generalized build: caller provides diag_func(m,n) -> float."""
    dim = N * N
    def vidx(m, n): return m * N + n
    def enc_h(m, n): return 1 + m * N + n
    def enc_v(m, n): return 1 + N * N + m * N + n
    def enc_d(m, n): return 1 + 2 * N * N + m * N + n

    def get_phase(eid):
        if phase_mode == "framework":
            return np.exp(1j * np.pi * alpha * D3(eid))
        if phase_mode == "trivial":
            return 1.0 + 0.0j
        if phase_mode == "random":
            return np.exp(1j * rng.uniform(0, 2 * np.pi))
        raise ValueError(phase_mode)

    rows, cols, data = [], [], []
    for m in range(N):
        for n in range(N):
            rows.append(vidx(m, n))
            cols.append(vidx(m, n))
            data.append(diag_func(m, n))
    for m in range(N - 1):
        for n in range(N):
            i, j = vidx(m, n), vidx(m + 1, n)
            amp = ch_2 * c_h * get_phase(enc_h(m, n))
            rows.extend([i, j]); cols.extend([j, i]); data.extend([amp, np.conj(amp)])
    for m in range(N):
        for n in range(N - 1):
            i, j = vidx(m, n), vidx(m, n + 1)
            amp = ch_2 * c_v * get_phase(enc_v(m, n))
            rows.extend([i, j]); cols.extend([j, i]); data.extend([amp, np.conj(amp)])
    for m in range(N - 1):
        for n in range(N - 1):
            i, j = vidx(m, n), vidx(m + 1, n + 1)
            amp = ch_2 * c_d * get_phase(enc_d(m, n))
            rows.extend([i, j]); cols.extend([j, i]); data.extend([amp, np.conj(amp)])
    H = sp.coo_matrix((data, (rows, cols)), shape=(dim, dim)).tocsr()
    H = 0.5 * (H + H.conj().T)
    return H


def diag_eigs(H):
    Hd = H.toarray().astype(np.complex128)
    Hd = 0.5 * (Hd + Hd.conj().T)
    return np.sort(la.eigvalsh(Hd))


def spacing_stats(w, deg=8, trim=0.1):
    w = np.sort(w)
    n = len(w)
    lo = int(trim * n); hi = int((1 - trim) * n)
    bulk = w[lo:hi]
    cumN = np.arange(1, len(bulk) + 1, dtype=float)
    coeffs = np.polyfit(bulk, cumN, deg)
    p = np.poly1d(coeffs)
    s = np.diff(p(bulk))
    s = s / np.mean(s)
    return {"var": float(np.var(s)), "n": int(len(s))}


def run_config(name, diag_func, N=20, alpha=1.5, ch_2=0.95):
    print(f"\n=== Config {name}: N={N}, alpha={alpha}, ch_2={ch_2} ===")
    rng = np.random.default_rng(0xABCD)
    H_fw = build_graph_general(N, alpha, ch_2, diag_func, "framework")
    H_tr = build_graph_general(N, alpha, ch_2, diag_func, "trivial")
    H_rnd = build_graph_general(N, alpha, ch_2, diag_func, "random", rng=rng)
    w_fw = diag_eigs(H_fw)
    w_tr = diag_eigs(H_tr)
    w_rnd = diag_eigs(H_rnd)

    K = 20
    rms_fw_tr = float(np.sqrt(np.mean((w_fw[:K] - w_tr[:K]) ** 2)))
    rms_fw_rnd = float(np.sqrt(np.mean((w_fw[:K] - w_rnd[:K]) ** 2)))
    st_fw = spacing_stats(w_fw)
    st_tr = spacing_stats(w_tr)
    print(f"  spectrum range fw : [{w_fw[0]:+.3f}, {w_fw[-1]:+.3f}]")
    print(f"  spectrum range tr : [{w_tr[0]:+.3f}, {w_tr[-1]:+.3f}]")
    print(f"  spectrum range rnd: [{w_rnd[0]:+.3f}, {w_rnd[-1]:+.3f}]")
    print(f"  rms(fw - trivial) [low 20]: {rms_fw_tr:.4f}")
    print(f"  rms(fw - random ) [low 20]: {rms_fw_rnd:.4f}")
    print(f"  var(unfolded spacings) framework: {st_fw['var']:.3f} (GUE=0.180, GOE=0.286, Poisson=1.0)")
    print(f"  var(unfolded spacings) trivial  : {st_tr['var']:.3f}")

    # Compare lowest 20 positive eigenvalues to zeta zeros
    w_fw_pos = w_fw[w_fw > 0]
    if len(w_fw_pos) >= K:
        # Try linear rescaling: find best a,b such that a*x+b matches zeta_zeros
        x = w_fw_pos[:K]
        A = np.vstack([x, np.ones_like(x)]).T
        coef, _, _, _ = np.linalg.lstsq(A, ZETA_ZEROS, rcond=None)
        a, b = coef
        fitted = a * x + b
        rms_after_rescale = float(np.sqrt(np.mean((fitted - ZETA_ZEROS) ** 2)))
        # Also raw rms (no rescaling)
        rms_raw = float(np.sqrt(np.mean((x - ZETA_ZEROS) ** 2)))
        print(f"  rms framework_pos vs zeta_zeros: raw={rms_raw:.3f}  after best linear rescale={rms_after_rescale:.3f}  (a={a:.3f}, b={b:.3f})")
        return {
            "name": name,
            "rms_fw_tr": rms_fw_tr,
            "rms_fw_rnd": rms_fw_rnd,
            "var_fw": st_fw["var"],
            "var_tr": st_tr["var"],
            "rms_zeta_raw": rms_raw,
            "rms_zeta_rescaled": rms_after_rescale,
            "rescale_a": float(a),
            "rescale_b": float(b),
            "framework_first_20_pos": x.tolist(),
        }
    else:
        return {"name": name, "rms_fw_tr": rms_fw_tr, "rms_fw_rnd": rms_fw_rnd,
                "var_fw": st_fw["var"], "var_tr": st_tr["var"]}


def main():
    N = 20
    alpha = 1.5
    ch_2 = 0.95

    results = []

    # A: pure hopping
    diag_A = lambda m, n: 0.0
    results.append(run_config("A_pure_hopping", diag_A, N, alpha, ch_2))

    # B: weak BK (scaled by 1/N^2)
    def diag_B(m, n):
        mn = (m + 1) * (n + 1)
        return (2 * np.pi * mn / np.log(mn + 2.0)) / (N * N)
    results.append(run_config("B_weak_BK", diag_B, N, alpha, ch_2))

    # C: framework "natural" diagonal: D(m,n) = pi/(10*alpha) per site (universal coupling)
    def diag_C(m, n):
        return np.pi / (10.0 * alpha)
    results.append(run_config("C_uniform_lambda_0", diag_C, N, alpha, ch_2))

    # D: Berry-Keating but rescaled so off-diag is competitive
    # original BK has D~140, off-diag ~ ch_2 ~ 1. To balance, divide by 100.
    def diag_D(m, n):
        mn = (m + 1) * (n + 1)
        return (2 * np.pi * mn / np.log(mn + 2.0)) / 100.0
    results.append(run_config("D_balanced_BK_100x", diag_D, N, alpha, ch_2))

    # E: random diagonal (Wigner reference)
    rng_diag = np.random.default_rng(0xBEEF)
    rdiag = rng_diag.uniform(-1, 1, size=(N, N))
    diag_E = lambda m, n: rdiag[m, n]
    results.append(run_config("E_random_diagonal", diag_E, N, alpha, ch_2))

    with open(os.path.join(OUT, "strong_coupling_results.json"), "w") as f:
        json.dump(results, f, indent=2)
    print("\nSaved JSON.")


if __name__ == "__main__":
    main()
