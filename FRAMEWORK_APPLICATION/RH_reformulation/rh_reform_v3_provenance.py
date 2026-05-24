"""
RH_REFORM_V3_PROVENANCE.PY  —  Which part of the construction does the work?

Diagnostic: compare three architectures honestly.
  (Arch_A) BK diagonal + Z_3 off-diagonal (the reform_v1)
  (Arch_B) BK diagonal ALONE (off-diag = 0)
  (Arch_C) Constant diagonal D(n) = const + Z_3 off-diagonal (framework only)
  (Arch_D) 1/n diagonal (original manuscript style) + Z_3 off-diagonal
  (Arch_E) BK diagonal + RANDOM phases on off-diag (instead of Z_3) — null
           for the framework claim

If Arch_A ≈ Arch_B and Arch_E, the BK ladder is doing the work — the Z_3
phase is irrelevant. If Arch_C produces zero approach, the framework's
Z_3 phase machinery alone CAN'T promote constant operator to zeta-zero
spectrum (negative for the framework). If Arch_C produces approach, the
framework Z_3 phase is doing real work (positive for the framework).
"""

import numpy as np
from mpmath import zetazero
import json
import time

PI_NP = np.pi

def D3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

def phi_phase_np(n):
    th = 2.0 * PI_NP * D3(n) / 3.0
    return complex(np.cos(th), np.sin(th))

def D_BK(n):
    return 2.0 * PI_NP * n / np.log(n + 2.0)

def D_const(n, c=15.0):
    return c

def D_invn(n):
    return 1.0 / (n + 1) + 1.0 / (n + 2)

def build_TN(N, diag_kind="BK", off_kind="Z3", off_decay="A",
              ch2=0.95, alpha_scale=1.0, seed=42):
    """
    diag_kind in {'BK', 'const', 'invn'}
    off_kind in {'Z3', 'rand', 'zero'}
    off_decay in {'A' (1/log), 'B' (1/sqrt(n)), 'E' (constant)}
    """
    eta = ch2 - 0.95
    rng = np.random.default_rng(seed)
    T = np.zeros((N, N), dtype=np.complex128)
    for n in range(1, N + 1):
        i = n - 1
        if diag_kind == "BK":
            T[i, i] = D_BK(n) * (1.0 + alpha_scale * eta * np.log(n + 2.0) / 10.0)
        elif diag_kind == "const":
            T[i, i] = D_const(n)
        elif diag_kind == "invn":
            T[i, i] = D_invn(n)
        else:
            raise ValueError(diag_kind)

        if n + 1 <= N and off_kind != "zero":
            if off_decay == "A":
                c_n = 1.0 / np.log(n + 2.0)
            elif off_decay == "B":
                c_n = 1.0 / np.sqrt(n + 1.0)
            elif off_decay == "E":
                c_n = 1.0
            else:
                raise ValueError(off_decay)
            sqrt_c = np.sqrt(c_n)
            if off_kind == "Z3":
                phin = phi_phase_np(n)
            elif off_kind == "rand":
                # Uniform random phase on unit circle
                ang = 2 * PI_NP * rng.random()
                phin = complex(np.cos(ang), np.sin(ang))
            else:
                raise ValueError(off_kind)
            theta_n = PI_NP * D3(n + 1)
            ch2_phase = np.exp(1j * alpha_scale * eta * theta_n)
            T[i, i + 1] = phin * sqrt_c * ch2_phase
            T[i + 1, i] = np.conj(phin) * sqrt_c * ch2_phase
    return T

def top_real_eigs(T, K=15, lo=0.5):
    eigs = np.linalg.eigvals(T)
    re_pos = np.sort(np.real(eigs)[np.real(eigs) > lo])
    return re_pos[:K].tolist()

def zz_match(eigs, anchors):
    out = []
    for a in anchors:
        if len(eigs) == 0:
            out.append({"a": a, "eig": None, "pct": None}); continue
        diffs = np.abs(np.array(eigs) - a)
        j = int(np.argmin(diffs))
        out.append({"a": a, "eig": eigs[j], "pct": abs(eigs[j]-a)/a*100})
    return out

def main():
    t0 = time.time()
    print("=" * 86)
    print("RH REFORM V3 — PROVENANCE: where does the eigenvalue match come from?")
    print("=" * 86)

    zz = [float(zetazero(k).imag) for k in range(1, 16)]
    print(f"\nFirst 10 zeta zero im parts: {[round(x,3) for x in zz[:10]]}")

    archs = [
        ("Arch_A", "BK", "Z3", "A", "BK diag + Z3 phase off-diag (REFORM)"),
        ("Arch_B", "BK", "zero", "A", "BK diag, NO off-diag (Berry-Keating ladder ALONE)"),
        ("Arch_C", "const", "Z3", "A", "CONSTANT diag + Z3 phase off-diag"),
        ("Arch_D", "invn", "Z3", "A", "1/n diag (Ch 9 manuscript style) + Z3 phase off-diag"),
        ("Arch_E", "BK", "rand", "A", "BK diag + RANDOM phase off-diag (null for Z3 claim)"),
        ("Arch_F", "BK", "Z3", "E", "BK diag + Z3 phase, CONSTANT coupling magnitude"),
    ]

    out = {"zeta_zeros_15": zz, "results": {}}

    for tag, dk, ok, od, desc in archs:
        print(f"\n--- {tag}: {desc} ---")
        # Vary N
        for N in [200, 400]:
            T = build_TN(N, diag_kind=dk, off_kind=ok, off_decay=od, ch2=0.95)
            eigs = top_real_eigs(T, K=15, lo=0.5)
            m = zz_match(eigs, zz[:10])
            avg = np.mean([x["pct"] for x in m if x["pct"] is not None])
            print(f"  N={N:4d}  top 5: {[round(x,3) for x in eigs[:5]]}  "
                  f"avg pct over 10 zeros: {avg:.2f}%")
            out["results"].setdefault(tag, []).append({
                "N": N, "top5": eigs[:5], "all15": eigs[:15],
                "avg_pct": float(avg), "desc": desc,
            })

    # Headline comparison
    print("\n" + "=" * 86)
    print("HEADLINE COMPARISON  (N=400):  top-5 eigenvalues per architecture")
    print("=" * 86)
    print(f"  {'arch':<8} {'top1':>8} {'top2':>8} {'top3':>8} {'top4':>8} {'top5':>8}   avg-pct  desc")
    for tag, _, _, _, desc in archs:
        d = [r for r in out["results"][tag] if r["N"] == 400][0]
        top5 = d["top5"] + [None] * (5 - len(d["top5"]))
        row = "  ".join(f"{(x if x is not None else 0):8.3f}" for x in top5)
        print(f"  {tag:<8} {row}   {d['avg_pct']:5.2f}%  {desc}")
    print(f"\nTarget (zeta zeros):   "
          f"{zz[0]:8.3f}  {zz[1]:8.3f}  {zz[2]:8.3f}  {zz[3]:8.3f}  {zz[4]:8.3f}")

    # SAVE
    outpath = "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/RH_reformulation/rh_reform_v3_provenance.json"
    with open(outpath, "w") as f:
        json.dump(out, f, indent=2, default=str)
    print(f"\nElapsed: {time.time()-t0:.1f} s")
    print(f"Saved: {outpath}")
    return out


if __name__ == "__main__":
    main()
