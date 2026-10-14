#!/usr/bin/env python3
"""
pilot_r23_box_measurement.py — R2 and R3 companion to the R1 probe
(`pilot_r1_box_measurement_2026-10-13.py`), for the centered-form Lean bridge
`CenteredFormBridge_2026_10_13.R2_box_centered` / `R3_box_centered`.

R2: 0 < Im ξ(1 + it) on t ∈ [13, 29/2 = 14.5]
R3: Re ξ(1 + it) < 0 on t ∈ [29/2, 15]

Both segments are the margin-tight ones per Legion's `ARB_CERTIFIED_MARCH`:
R2 at t = 14.5 the two ~1 pieces of Re ξ cancel to ~1e-3; R3 the sign crossing
of Re ξ happens between t = 14.1 (first zero) and t = 15 so Re ξ runs from
~0 to its full negative tail.

Not a certificate — mpmath sampling at dps=100. Measures (c, r, Mc, L) a
certified producer must supply, with the strict margin L · r < |Mc| that
R2_box_centered / R3_box_centered requires.

Author: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-13.
"""

import mpmath as mp

mp.mp.dps = 100


def xi(s):
    """Completed Riemann xi: xi(s) = s(s-1)/2 · Lambda(s), where
    Lambda(s) = pi^(-s/2) · Gamma(s/2) · zeta(s)."""
    pi_pow = mp.power(mp.pi, -s / 2)
    gamma_val = mp.gamma(s / 2)
    zeta_val = mp.zeta(s)
    Lambda = pi_pow * gamma_val * zeta_val
    return s * (s - 1) / 2 * Lambda


def xi_prime(s, h=mp.mpf('1e-20')):
    return (xi(s + h) - xi(s - h)) / (2 * h)


def edgeRe(t):
    return mp.re(xi(mp.mpc(1, t)))


def edgeIm(t):
    return mp.im(xi(mp.mpc(1, t)))


def edgeRe_deriv_at(t):
    """d/dt Re xi(1+it) = Re(xi'(1+it) * i) = -Im(xi'(1+it))."""
    return -mp.im(xi_prime(mp.mpc(1, t)))


def edgeIm_deriv_at(t):
    """d/dt Im xi(1+it) = Im(xi'(1+it) * i) = Re(xi'(1+it))."""
    return mp.re(xi_prime(mp.mpc(1, t)))


def measure_box(c, r, kind, n_samples=201):
    """kind: 'R1' or 'R2' or 'R3'. R1 and R3 use edgeRe (±Mc); R2 uses edgeIm."""
    if kind == 'R2':
        Mc = edgeIm(c)
        deriv = edgeIm_deriv_at
    else:
        Mc = edgeRe(c)
        deriv = edgeRe_deriv_at
    ts = [mp.mpf(c) + mp.mpf(r) * (2 * mp.mpf(k) / (n_samples - 1) - 1)
          for k in range(n_samples)]
    L_sample = max(abs(deriv(t)) for t in ts)
    L_inflated = L_sample * mp.mpf('2.0')
    if kind == 'R3':
        # Need Mc < -(L · r), i.e. |Mc| > L · r AND Mc < 0.
        margin = -Mc - L_inflated * mp.mpf(r)
        passes = bool(Mc < 0 and margin > 0)
    else:
        margin = Mc - L_inflated * mp.mpf(r)
        passes = bool(margin > 0)
    return {
        'c': c, 'r': r, 'kind': kind,
        'Mc': Mc,
        'L_sampled': L_sample,
        'L_inflated_x2': L_inflated,
        'L_r_product_x2': L_inflated * mp.mpf(r),
        'margin_x2': margin,
        'margin_passes': passes,
    }


def print_result(label, R):
    print(f"=== {label} ===")
    print(f"  kind = {R['kind']}")
    print(f"  c = {R['c']}, r = {R['r']}")
    print(f"  Mc = {mp.nstr(R['Mc'], 20)}")
    print(f"  L (sampled, 201 pts)     = {mp.nstr(R['L_sampled'], 10)}")
    print(f"  L_inflated_2x · r         = {mp.nstr(R['L_r_product_x2'], 10)}")
    print(f"  margin (2x slack)         = {mp.nstr(R['margin_x2'], 10)}")
    print(f"  passes centered-form?     = {R['margin_passes']}")
    print()


def main():
    print("# R2 and R3 pilot-box feasibility probes (centered-form Lean bridge)")
    print(f"# dps = {mp.mp.dps}")
    print()

    print("## R2 — Im ξ(1+it) > 0 on [13, 29/2 = 14.5]  (Legion margin-tight)")
    print()

    r2_boxes = [
        (mp.mpf('13.0'),  mp.mpf('0.05')),
        (mp.mpf('13.25'), mp.mpf('0.10')),
        (mp.mpf('13.5'),  mp.mpf('0.10')),
        (mp.mpf('13.75'), mp.mpf('0.10')),
        (mp.mpf('14.0'),  mp.mpf('0.10')),
        (mp.mpf('14.25'), mp.mpf('0.10')),
        (mp.mpf('14.4'),  mp.mpf('0.05')),
        (mp.mpf('14.45'), mp.mpf('0.03')),
    ]
    r2_results = []
    for c, r in r2_boxes:
        R = measure_box(c, r, 'R2')
        print_result(f"R2 c={c}, r={r}", R)
        r2_results.append((c, r, R))

    print("## R3 — Re ξ(1+it) < 0 on [29/2 = 14.5, 15]  (first zero at t≈14.1347)")
    print()

    r3_boxes = [
        (mp.mpf('14.5'),  mp.mpf('0.05')),
        (mp.mpf('14.6'),  mp.mpf('0.05')),
        (mp.mpf('14.7'),  mp.mpf('0.05')),
        (mp.mpf('14.8'),  mp.mpf('0.05')),
        (mp.mpf('14.9'),  mp.mpf('0.05')),
        (mp.mpf('14.95'), mp.mpf('0.03')),
    ]
    r3_results = []
    for c, r in r3_boxes:
        R = measure_box(c, r, 'R3')
        print_result(f"R3 c={c}, r={r}", R)
        r3_results.append((c, r, R))

    print()
    print("# Summary")
    print()
    print("## R2 (want: 0 < Im ξ)")
    print(f"  {'c':>7}  {'r':>6}  {'Mc':>12}  {'L_sampled':>12}  margin")
    for c, r, R in r2_results:
        mark = "PASS" if R['margin_passes'] else "fail"
        print(f"  {float(c):>7.3f}  {float(r):>6.3f}  "
              f"{float(R['Mc']):+.4e}  {float(R['L_sampled']):.4e}  "
              f"{float(R['margin_x2']):+.4e}  {mark}")
    print()
    print("## R3 (want: Re ξ < 0)")
    print(f"  {'c':>7}  {'r':>6}  {'Mc':>12}  {'L_sampled':>12}  margin")
    for c, r, R in r3_results:
        mark = "PASS" if R['margin_passes'] else "fail"
        print(f"  {float(c):>7.3f}  {float(r):>6.3f}  "
              f"{float(R['Mc']):+.4e}  {float(R['L_sampled']):.4e}  "
              f"{float(R['margin_x2']):+.4e}  {mark}")


if __name__ == '__main__':
    main()
