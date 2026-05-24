"""
Adaptive-resolution 2D vortex pair test (refines grid with separation).

Compares isolated vs paired (counter-rotating) Oseen vortices.
KEY METRIC: the *suppression ratio*  KE_pair / KE_iso  as ε → 0
            and ω_max(paired)/ω_max(isolated)

Framework claim: the cancellation makes the paired configuration
asymptotically less singular than the isolated one; ratios -> 0 as ε -> 0.
"""

from __future__ import annotations
import numpy as np
import json
from pathlib import Path

OUTDIR = Path(__file__).parent
LAMBDA_0_NS = 1.0 / 15.0


def oseen(X, Y, x0, y0, gamma, core):
    dx = X - x0; dy = Y - y0
    r2 = dx*dx + dy*dy + 1e-300
    r = np.sqrt(r2)
    profile = (gamma/(2*np.pi*r)) * (1.0 - np.exp(-r2/(core*core)))
    return -profile*(dy/r), profile*(dx/r)


def curl(u, v, dx):
    dvdx = (np.roll(v, -1, axis=1) - np.roll(v, 1, axis=1)) / (2*dx)
    dudy = (np.roll(u, -1, axis=0) - np.roll(u, 1, axis=0)) / (2*dx)
    return dvdx - dudy


def run_one(eps, N=1024, window_factor=8.0):
    """High-res run with window scaled to eps."""
    L = window_factor * eps
    xs = np.linspace(-L, L, N, endpoint=False)
    X, Y = np.meshgrid(xs, xs, indexing="xy")
    dx = xs[1] - xs[0]
    dA = dx*dx
    R = np.sqrt(X*X + Y*Y)
    core = eps

    # isolated +γ
    u_i, v_i = oseen(X, Y, 0.0, 0.0, +1.0, core)
    om_i = curl(u_i, v_i, dx)
    ke_i = 0.5*(u_i*u_i + v_i*v_i)

    # pair: +γ at -eps/2 and -γ at +eps/2
    u_a, v_a = oseen(X, Y, -eps/2, 0.0, +1.0, core)
    u_b, v_b = oseen(X, Y, +eps/2, 0.0, -1.0, core)
    u_p = u_a + u_b
    v_p = v_a + v_b
    om_p = curl(u_p, v_p, dx)
    ke_p = 0.5*(u_p*u_p + v_p*v_p)

    # restrict to B_{2eps}(0)
    mask = R < 2.0*eps

    return {
        "eps":  float(eps),
        "dx":   float(dx),
        "N":    N,
        "KE_iso":   float(np.sum(ke_i[mask]) * dA),
        "KE_pair":  float(np.sum(ke_p[mask]) * dA),
        "Ens_iso":  float(np.sum(om_i[mask]**2) * dA),
        "Ens_pair": float(np.sum(om_p[mask]**2) * dA),
        "wmax_iso":  float(np.max(np.abs(om_i))),
        "wmax_pair": float(np.max(np.abs(om_p))),
        "umax_iso":  float(np.max(np.sqrt(u_i*u_i + v_i*v_i))),
        "umax_pair": float(np.max(np.sqrt(u_p*u_p + v_p*v_p))),
    }


def main():
    eps_list = [0.5, 0.25, 0.125, 0.0625, 0.03125, 0.015625, 0.0078125]
    rows = [run_one(e, N=1024, window_factor=8.0) for e in eps_list]

    print("="*78)
    print("Adaptive 2D vortex test — KE and enstrophy in B_{2eps}(0)")
    print("="*78)
    print(f"{'eps':>10} {'KE_i':>10} {'KE_p':>10} {'KE p/i':>8} "
          f"{'wmax_i':>10} {'wmax_p':>10} {'w p/i':>8}")
    for r in rows:
        print(f"{r['eps']:>10.5f} {r['KE_iso']:>10.4f} {r['KE_pair']:>10.4f} "
              f"{r['KE_pair']/r['KE_iso']:>8.4f} "
              f"{r['wmax_iso']:>10.3e} {r['wmax_pair']:>10.3e} "
              f"{r['wmax_pair']/r['wmax_iso']:>8.4f}")
    print()

    # Scaling fits
    eps_arr = np.array([r['eps'] for r in rows])
    KE_p    = np.array([r['KE_pair'] for r in rows])
    KE_i    = np.array([r['KE_iso']  for r in rows])
    Wp      = np.array([r['wmax_pair'] for r in rows])
    Wi      = np.array([r['wmax_iso']  for r in rows])

    # log-log fits
    p_KE_iso  = np.polyfit(np.log(eps_arr), np.log(KE_i), 1)[0]
    p_KE_pair = np.polyfit(np.log(eps_arr), np.log(KE_p), 1)[0]
    p_W_iso   = np.polyfit(np.log(eps_arr), np.log(Wi),  1)[0]
    p_W_pair  = np.polyfit(np.log(eps_arr), np.log(Wp),  1)[0]

    print(f"Power-law fits (log-log slopes):")
    print(f"  KE_iso  ~ eps^{p_KE_iso:.4f}     KE_pair ~ eps^{p_KE_pair:.4f}")
    print(f"  ω_max_iso  ~ eps^{p_W_iso:.4f}   ω_max_pair ~ eps^{p_W_pair:.4f}")
    print()

    # Interpretation
    print("INTERPRETATION")
    print(f"  Isolated Oseen vortex:  ω_max(ε) ~ ε^(-2) (point-strength → ∞)")
    print(f"  Numerical slope        : {p_W_iso:.4f}   (expected ≈ -2)")
    print(f"  Paired vortex (cancel): ω_max stays bounded as ε → 0 IF cancellation")
    print(f"                          is exact; numerically we see slope {p_W_pair:.4f}")
    print(f"  Suppression factor ω_p/ω_i at finest ε: "
          f"{rows[-1]['wmax_pair']/rows[-1]['wmax_iso']:.4f}")
    print()
    print(f"  Universal coupling λ_0 = 1/15 = {LAMBDA_0_NS:.6f}")
    print(f"    interpretation: minimum effective dissipation rate per scale,")
    print(f"    i.e. enstrophy decay coefficient lower-bounded by λ_0 in the")
    print(f"    framework's fractal-absorption picture.")

    out = {
        "rows": rows,
        "scalings": {
            "KE_iso":   p_KE_iso,
            "KE_pair":  p_KE_pair,
            "wmax_iso": p_W_iso,
            "wmax_pair": p_W_pair,
        },
        "suppression_ratios_at_finest_eps": {
            "KE_pair_over_iso":   rows[-1]['KE_pair']/rows[-1]['KE_iso'],
            "wmax_pair_over_iso": rows[-1]['wmax_pair']/rows[-1]['wmax_iso'],
        },
        "lambda_0_NS": LAMBDA_0_NS,
    }
    (OUTDIR / "vortex_adaptive_2D_results.json").write_text(
        json.dumps(out, indent=2))
    print(f"\nWrote: {OUTDIR}/vortex_adaptive_2D_results.json")


if __name__ == "__main__":
    main()
