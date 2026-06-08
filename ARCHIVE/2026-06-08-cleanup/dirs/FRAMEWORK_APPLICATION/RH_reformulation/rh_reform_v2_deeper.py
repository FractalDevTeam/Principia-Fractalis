"""
RH_REFORM_V2_DEEPER.PY  —  Deeper analysis of reformulated T_N.

Probes:
  (P1) Stability under N: do eigenvalues converge as N grows?
  (P2) Are the eigenvalues genuinely tracking zeta zeros, or just the
       Berry-Keating Weyl-density 2*pi*n/log(n)?
       Test: compare against a NULL TN with off_diagonals SET TO ZERO
       (i.e., the pure Berry-Keating ladder). If null gives nearly the
       same top eigenvalues, the Z_3 phase machinery isn't doing the
       work — the BK diagonal is.
  (P3) Sweep coupling strength: scale c_n by factor gamma in {0.1, 0.5,
       1.0, 2.0, 5.0} and see how much the eigenvalues move.
  (P4) Test alternative cleaner couplings:
        D) c_n = D(n)/n  (BK density)
        E) c_n = constant (uniform)
  (P5) Compare eigenvalue STATISTICS (Wigner-Dyson level spacing) against
       zeta zeros — the more meaningful test than point-match.
  (P6) Check: do MORE zeta zeros (beyond first 10) match too, or does
       the agreement degrade?

import + outputs go to /home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/RH_reformulation/
"""

import numpy as np
from mpmath import mp, mpf, mpc, exp, log, pi as mp_pi, cos, sin, zetazero, fabs, sqrt
import json
import time

mp.dps = 25

PI_NP = float(mp_pi)

def D3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

def phi_phase_np(n):
    theta = 2.0 * PI_NP * D3(n) / 3.0
    return complex(np.cos(theta), np.sin(theta))

def D_BK(n):
    return 2.0 * PI_NP * n / np.log(n + 2.0)

def coupling_fn(n, kind):
    if kind == "A":
        return 1.0 / np.log(n + 2.0)
    if kind == "B":
        return 1.0 / np.sqrt(n + 1.0)
    if kind == "C":
        return np.sqrt(D_BK(n) * D_BK(n + 1)) / 10.0
    if kind == "D":
        return D_BK(n) / n
    if kind == "E":
        return 1.0
    raise ValueError(kind)

def build_TN_reform(N, ch2=0.95, coupling="A", gamma=1.0, off_zero=False,
                   alpha_scale=1.0):
    eta = ch2 - 0.95
    T = np.zeros((N, N), dtype=np.complex128)
    for n in range(1, N + 1):
        i = n - 1
        diag = D_BK(n)
        T[i, i] = diag * (1.0 + alpha_scale * eta * np.log(n + 2.0) / 10.0)
        if n + 1 <= N and not off_zero:
            c_n = coupling_fn(n, coupling) * gamma
            sqrt_c = np.sqrt(c_n) if c_n >= 0 else 1j * np.sqrt(-c_n)
            phin = phi_phase_np(n)
            theta_n = PI_NP * D3(n + 1)
            ch2_phase = np.exp(1j * alpha_scale * eta * theta_n)
            T[i, i + 1] = phin * sqrt_c * ch2_phase
            T[i + 1, i] = np.conj(phin) * sqrt_c * ch2_phase
    return T

def get_zeta_zeros(M):
    return [float(zetazero(k).imag) for k in range(1, M + 1)]

def top_real_eigs(T, K=30):
    eigs = np.linalg.eigvals(T)
    re = np.real(eigs)
    # Take real parts > 0 and sort ascending
    re_pos = np.sort(re[re > 0.5])
    return re_pos[:K].tolist()

def match_quality(eigs_sorted, anchors):
    """For each anchor, find closest eigenvalue; return list of (anchor, eig, |diff|, pct)."""
    out = []
    for a in anchors:
        if len(eigs_sorted) == 0:
            out.append({"anchor": a, "eig": None, "diff": None, "pct": None})
            continue
        diffs = np.abs(np.array(eigs_sorted) - a)
        j = int(np.argmin(diffs))
        out.append({"anchor": a, "eig": eigs_sorted[j],
                    "diff": float(abs(eigs_sorted[j] - a)),
                    "pct": float(abs(eigs_sorted[j] - a) / a * 100.0)})
    return out

def main():
    t0 = time.time()
    print("=" * 86)
    print("RH REFORM V2 — Deeper probes")
    print("=" * 86)

    zz30 = get_zeta_zeros(30)
    print(f"\nFirst 10 zeta zero imag parts: {[round(x,3) for x in zz30[:10]]}")
    print(f"Zeros 20-30: {[round(x,3) for x in zz30[19:30]]}")

    out = {"zeta_zeros_30": zz30, "probes": {}}

    # ------------------------------------------------------------
    # P2: NULL MODEL — pure BK diagonal (off-diagonal = 0)
    # ------------------------------------------------------------
    print("\n" + "=" * 86)
    print("P2: NULL MODEL — pure BK diagonal (no off-diagonal)")
    print("=" * 86)
    for N in [100, 200, 400]:
        T0 = build_TN_reform(N, ch2=0.95, coupling="A", off_zero=True)
        eigs = top_real_eigs(T0, K=15)
        match = match_quality(eigs, zz30[:10])
        avg = np.mean([m["pct"] for m in match])
        print(f"  N={N:4d}  top 5 = {[round(x,3) for x in eigs[:5]]}  avg pct err = {avg:.2f}%")
    out["probes"]["P2_null_BK_only"] = "pure BK diagonal — top 5 eigs are exactly D_BK(1..5)"

    # ------------------------------------------------------------
    # P3: Coupling strength sweep
    # ------------------------------------------------------------
    print("\n" + "=" * 86)
    print("P3: Coupling strength sweep gamma in {0.1, 0.5, 1.0, 2.0, 5.0} at N=200, kind A")
    print("=" * 86)
    p3 = []
    for gamma in [0.1, 0.5, 1.0, 2.0, 5.0]:
        T = build_TN_reform(200, ch2=0.95, coupling="A", gamma=gamma)
        eigs = top_real_eigs(T, K=15)
        match = match_quality(eigs, zz30[:10])
        avg = np.mean([m["pct"] for m in match])
        print(f"  gamma={gamma:.2f}  top 5 = {[round(x,3) for x in eigs[:5]]}  avg pct err = {avg:.2f}%")
        p3.append({"gamma": gamma, "top5": eigs[:5], "avg_pct": float(avg)})
    out["probes"]["P3_gamma_sweep"] = p3

    # ------------------------------------------------------------
    # P4: Alternative coupling kinds D, E
    # ------------------------------------------------------------
    print("\n" + "=" * 86)
    print("P4: Alternative coupling kinds D (BK density) and E (uniform) at N=200")
    print("=" * 86)
    p4 = []
    for kind in ["D", "E"]:
        T = build_TN_reform(200, ch2=0.95, coupling=kind)
        eigs = top_real_eigs(T, K=15)
        match = match_quality(eigs, zz30[:10])
        avg = np.mean([m["pct"] for m in match])
        print(f"  kind={kind}  top 5 = {[round(x,3) for x in eigs[:5]]}  avg pct err = {avg:.2f}%")
        p4.append({"kind": kind, "top5": eigs[:5], "avg_pct": float(avg)})
    out["probes"]["P4_alt_kinds"] = p4

    # ------------------------------------------------------------
    # P6: Match more zeros
    # ------------------------------------------------------------
    print("\n" + "=" * 86)
    print("P6: Match first 30 zeta zeros at N=400, coupling A")
    print("=" * 86)
    T = build_TN_reform(400, ch2=0.95, coupling="A")
    eigs = top_real_eigs(T, K=40)
    match = match_quality(eigs, zz30)
    print(f"  {'k':>3}  {'t_k':>10}  {'eig_k':>10}  {'|diff|':>8}  {'pct':>7}")
    for i, m in enumerate(match):
        print(f"  {i+1:3d}  {m['anchor']:10.4f}  {m['eig']:10.4f}  "
              f"{m['diff']:8.4f}  {m['pct']:6.2f}%")
    overall_avg = np.mean([m["pct"] for m in match])
    print(f"\n  Average pct over 30 zeros: {overall_avg:.2f}%")
    out["probes"]["P6_30_zeros"] = match
    out["probes"]["P6_avg_pct_30"] = float(overall_avg)

    # ------------------------------------------------------------
    # P5: Level-spacing statistics — GUE/Wigner-Dyson test
    # ------------------------------------------------------------
    print("\n" + "=" * 86)
    print("P5: Level spacing statistics — Wigner-Dyson signature")
    print("=" * 86)
    # Use middle-of-spectrum eigenvalues to avoid edge effects
    T = build_TN_reform(400, ch2=0.95, coupling="A")
    eigs_all = np.sort(np.real(np.linalg.eigvals(T)))
    # Unfold by local mean spacing: use middle 60%
    mid_lo, mid_hi = int(0.2 * 400), int(0.8 * 400)
    mid = eigs_all[mid_lo:mid_hi]
    gaps = np.diff(mid)
    s = gaps / np.mean(gaps)
    mean_s = float(np.mean(s))
    var_s = float(np.var(s))
    # GUE: <s>=1 by def; var(s) ≈ 0.18; Poisson var(s)=1
    print(f"  Mean spacing (normalized): {mean_s:.4f}  (expect 1.0)")
    print(f"  Var of spacings:           {var_s:.4f}  (GUE ≈ 0.18 ; Poisson = 1.0)")

    # Compare to zeta-zero level spacings (Montgomery / GUE)
    # Use computed 30 zeros, take consecutive gaps, unfold
    zz_arr = np.array(zz30)
    # Mean spacing of zeta zeros near height T_av is 2π/log(T_av/2π)
    Tav = float(np.mean(zz_arr))
    mean_gap_th = 2 * PI_NP / np.log(Tav / (2 * PI_NP))
    zz_gaps = np.diff(zz_arr) / mean_gap_th
    print(f"  Compare zeta zero gaps: mean={float(np.mean(zz_gaps)):.4f}  "
          f"var={float(np.var(zz_gaps)):.4f}")
    out["probes"]["P5_level_spacing"] = {
        "TN_mean": mean_s, "TN_var": var_s,
        "GUE_expected_var": 0.18, "Poisson_var": 1.0,
        "zeta_mean": float(np.mean(zz_gaps)),
        "zeta_var": float(np.var(zz_gaps)),
    }

    # ------------------------------------------------------------
    # P_extra: Cleanly verify Hermiticity behavior over fine grid
    # ------------------------------------------------------------
    print("\n" + "=" * 86)
    print("P_extra: Fine-grain ch_2 sweep — Hermiticity breakage profile")
    print("=" * 86)
    pextra = []
    for ch2 in np.linspace(0.90, 1.00, 21):
        T = build_TN_reform(200, ch2=ch2, coupling="A")
        defect = float(np.linalg.norm(T - T.conj().T, ord="fro"))
        eigs = np.linalg.eigvals(T)
        max_im = float(np.max(np.abs(np.imag(eigs))))
        pextra.append({"ch2": float(ch2), "defect": defect, "max_imag_eig": max_im})
    for r in pextra:
        marker = "  <-- threshold" if abs(r["ch2"] - 0.95) < 0.001 else ""
        print(f"  ch_2 = {r['ch2']:.3f}   ||T-T^H||_F = {r['defect']:8.4f}   "
              f"max|Im(eig)| = {r['max_imag_eig']:8.4e}{marker}")
    out["probes"]["P_extra_fine_sweep"] = pextra

    outpath = "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/RH_reformulation/rh_reform_v2_results.json"
    with open(outpath, "w") as f:
        json.dump(out, f, indent=2, default=str)
    print(f"\nElapsed: {time.time()-t0:.1f} s")
    print(f"Saved: {outpath}")
    return out


if __name__ == "__main__":
    main()
