#!/usr/bin/env python3
"""
pilot_r1_box_measurement.py — single-box feasibility probe for R1 under the
centered-form Lean bridge (`CenteredFormBridge_2026_10_13`).

Measures Mc = (ξ(1+ic)).re and an upper bound L for |d/dt Re ξ(1+it)| on
[c - r, c + r], then verifies the strict margin L * r < Mc that R1_box_centered
requires. Not a certificate — mpmath sampling at dps=100. The point is to
measure the required (c, r, Mc, L) parameters a certified producer would have
to supply for the pilot R1 box.

Author: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-13.
Reference: TBOX_CENTERED_FORM_LEVER_2026-10-10.md, ARB_CERTIFIED_MARCH_2026-10-10.md
"""

import mpmath as mp
from fractions import Fraction

mp.mp.dps = 100


def xi(s):
    """Completed Riemann xi, mathlib convention:
       xi(s) = s(s-1)/2 * Lambda_0(s) + 1/2
    where Lambda_0 = Lambda - 1/s - 1/(s-1) is entire.
    mpmath's `siegelz`/`zeta` give full Lambda; use the un-pole-stripped form
    via explicit factorisation."""
    pi_pow = mp.power(mp.pi, -s / 2)
    gamma_val = mp.gamma(s / 2)
    zeta_val = mp.zeta(s)
    Lambda = pi_pow * gamma_val * zeta_val
    return s * (s - 1) / 2 * Lambda


def xi_prime(s, h=mp.mpf('1e-20')):
    """Numerical derivative of xi at s, by central difference. For local
    checks only; a certified campaign uses analytic derivatives."""
    return (xi(s + h) - xi(s - h)) / (2 * h)


def edgeRe(t):
    """Re xi(1 + i*t), real-valued function of real t."""
    s = mp.mpc(1, t)
    return mp.re(xi(s))


def edgeRe_deriv_at(t):
    """d/dt Re xi(1+it) = Re(xi'(1+it) * i) = -Im(xi'(1+it))."""
    s = mp.mpc(1, t)
    return -mp.im(xi_prime(s))


def measure_r1_pilot_box(c, r, n_samples=201):
    """Measure Mc at c and sampled L on [c-r, c+r]. Returns a dict."""
    Mc = edgeRe(c)
    ts = [mp.mpf(c) + mp.mpf(r) * (2 * mp.mpf(k) / (n_samples - 1) - 1)
          for k in range(n_samples)]
    deriv_vals = [abs(edgeRe_deriv_at(t)) for t in ts]
    L_sample = max(deriv_vals)
    L_inflated = L_sample * mp.mpf('2.0')  # inflate for interval-width budget
    margin = Mc - L_inflated * mp.mpf(r)
    return {
        'c': c, 'r': r,
        'Mc': Mc,
        'L_sampled': L_sample,
        'L_inflated_x2': L_inflated,
        'L_r_product_x2': L_inflated * mp.mpf(r),
        'margin_x2': margin,
        'margin_passes': bool(margin > 0),
    }


def print_result(label, R):
    print(f"=== {label} ===")
    print(f"  c = {R['c']}")
    print(f"  r = {R['r']}")
    print(f"  Mc = Re xi(1 + {R['c']}i)       = {mp.nstr(R['Mc'], 20)}")
    print(f"  L (sampled, 201 pts)           = {mp.nstr(R['L_sampled'], 10)}")
    print(f"  L inflated 2x (interval slack) = {mp.nstr(R['L_inflated_x2'], 10)}")
    print(f"  L_inflated * r                 = {mp.nstr(R['L_r_product_x2'], 10)}")
    print(f"  Mc - L_inflated * r (margin)   = {mp.nstr(R['margin_x2'], 10)}")
    print(f"  R1_box_centered margin > 0 ?   = {R['margin_passes']}")
    print()


def main():
    print("# R1 pilot-box feasibility probe (centered-form Lean bridge)")
    print("# dps =", mp.mp.dps)
    print()

    # Note on c = 0: Legion's R1Neighborhood_2026_10_09 covers t = 0 via a
    # continuity argument (ξ(1) = 1/2); the s = 1 pole of ζ cancels against
    # the s - 1 = 0 factor in ξ, so ξ(1) is finite but the mpmath Λ-level
    # computation hits the pole. The centered-form bridge is for interior
    # boxes; the t = 0 endpoint is handled by R1_right_neighborhood_of_zero.

    # Pilot box 1: c = 0.1 — immediately away from the ζ pole.
    R0 = measure_r1_pilot_box(mp.mpf('0.1'), mp.mpf('0.05'))
    print_result("pilot box 0: c = 0.1, r = 0.05 (near-endpoint)", R0)

    # Pilot box 1: c = 0.5 — well inside [0, 13], ξ(1+0.5i) still close to 0.5.
    R1 = measure_r1_pilot_box(mp.mpf('0.5'), mp.mpf('0.05'))
    print_result("pilot box 1: c = 0.5, r = 0.05", R1)

    # Pilot box 2: c = 1, r = 0.1.
    R2 = measure_r1_pilot_box(mp.mpf('1'), mp.mpf('0.1'))
    print_result("pilot box 2: c = 1, r = 0.1", R2)

    # Pilot box 3: c = 2, r = 0.5 — stress-test with large box.
    R3 = measure_r1_pilot_box(mp.mpf('2'), mp.mpf('0.5'))
    print_result("pilot box 3: c = 2, r = 0.5 (stress-wide)", R3)

    # Pilot box 4: c = 5, r = 0.5 — deeper in the segment where derivative
    # magnitude grows.
    R4 = measure_r1_pilot_box(mp.mpf('5'), mp.mpf('0.5'))
    print_result("pilot box 4: c = 5, r = 0.5", R4)

    # Pilot box 5: c = 10, r = 0.1 — near the far end of R1 at [0, 13].
    R5 = measure_r1_pilot_box(mp.mpf('10'), mp.mpf('0.1'))
    print_result("pilot box 5: c = 10, r = 0.1 (near segment far end)", R5)

    # Pilot box 6: c = 12.5, r = 0.5 — last big chunk of R1.
    R6 = measure_r1_pilot_box(mp.mpf('12.5'), mp.mpf('0.5'))
    print_result("pilot box 6: c = 12.5, r = 0.5 (last R1 chunk)", R6)

    print("# Summary")
    for label, R in [('c=0.1', R0), ('c=0.5', R1), ('c=1', R2),
                     ('c=2', R3), ('c=5', R4), ('c=10', R5), ('c=12.5', R6)]:
        print(f"  {label:>8}  r={float(R['r']):.3f}  Mc={float(R['Mc']):+.6e}  "
              f"L={float(R['L_sampled']):.6e}  margin_passes={R['margin_passes']}")


if __name__ == '__main__':
    main()
