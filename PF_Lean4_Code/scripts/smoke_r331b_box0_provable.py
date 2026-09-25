#!/usr/bin/env python3
"""
smoke_r331b_box0_provable.py — smoke test with the CLOSED-FORM PROVABLE
|f''| bound (not sampled numerical curvature).

Tests whether Msegment(L) as derived from |P|≤1, |P'|≤25/32, |P''|≤1425/1024,
|Q|≤1, |Q'|≤c=15/2, |Q''|≤c+c²=255/4, and R(u) ≤ exp(-A_n·L),
combined with rational macro-segments and per-segment uniform midpoint,
can satisfy the box-0 target after §8 envelope subtraction.

NOT PROOF.  Purely reconnaissance of a provable path.

Usage:  python3 smoke_r331b_box0_provable.py
"""
import mpmath as mp
from fractions import Fraction

mp.mp.dps = 60

# ------------------------------------------------------------------
# Constants
# ------------------------------------------------------------------
T15 = mp.mpf(15)
HALF_T15 = mp.mpf(15) / 2   # c = t/2 = 15/2
c = HALF_T15
c_sq = c * c                 # 225/4
c_plus_c_sq = c + c_sq       # 255/4

N = 3
T = mp.mpf(5)
SIGMA_LO = mp.mpf(1) / 2
SIGMA_HI = mp.mpf(9) / 16

# Exponent range on box 0: both a₁ and a₂ ∈ [-25/32, -23/32].
# For u ≥ 1, u^a for a in this interval satisfies u^a ≤ 1.
# Rational bounds:
p1 = mp.mpf(25) / 32          # bound on |a| = |σ/2-1| ≤ 25/32 (since |σ/2-1| max at (1-9/16)/2-1 = -25/32)
p2 = mp.mpf(1425) / 1024      # bound on |a(a-1)| ≤ (25/32)·(57/32) = 1425/1024

# π·(n+1)² for n=0,1,2
PI = mp.pi
A = [PI * (n + 1)**2 for n in range(N)]

# §8 envelope
DELTA_N = mp.exp(-PI * (N + 1)**2) / (1 - mp.exp(-PI))
TRUNC_ENVELOPE = 2 * (T - 1) * DELTA_N
TAIL_ENVELOPE = 2 / PI * mp.exp(-PI * T) / (1 - mp.exp(-PI))
ENVELOPE_LAMBDA = TRUNC_ENVELOPE + TAIL_ENVELOPE

TARGET_RLO = mp.mpf(2221) / 500000

# ------------------------------------------------------------------
# Provable per-segment M bound
# ------------------------------------------------------------------
def M_term(L, n):
    """Mterm(L, n) = exp(-A_n·L)·(p2 + (c+c²) + A_n² + 2p1c + 2p1A_n + 2cA_n)."""
    An = A[n]
    coef = p2 + c_plus_c_sq + An*An + 2*p1*c + 2*p1*An + 2*c*An
    return mp.exp(-An * L) * coef

def M_segment(L):
    """Msegment(L) = 2·Σ_{n<3} Mterm(L, n)  (factor 2 for the two exponent branches)."""
    return 2 * sum(M_term(L, n) for n in range(N))

# ------------------------------------------------------------------
# Integrands
# ------------------------------------------------------------------
def omega_partial(u):
    return sum(mp.exp(-PI * (n + 1)**2 * u) for n in range(N))

def theta_re_integrand(sigma, u):
    a = sigma / 2 - 1
    b = (1 - sigma) / 2 - 1
    return (mp.power(u, a) + mp.power(u, b)) * mp.cos(HALF_T15 * mp.log(u)) * omega_partial(u)

def theta_im_integrand(sigma, u):
    a = sigma / 2 - 1
    b = (1 - sigma) / 2 - 1
    return (mp.power(u, a) - mp.power(u, b)) * mp.sin(HALF_T15 * mp.log(u)) * omega_partial(u)

# ------------------------------------------------------------------
# Segment-based midpoint quadrature
# ------------------------------------------------------------------
def segment_midpoint_sum_re(sigma, a_j, b_j, n_j):
    h = (b_j - a_j) / n_j
    return sum(theta_re_integrand(sigma, a_j + h * (i + mp.mpf(1)/2)) * h
               for i in range(n_j))

def segment_midpoint_sum_im(sigma, a_j, b_j, n_j):
    h = (b_j - a_j) / n_j
    return sum(theta_im_integrand(sigma, a_j + h * (i + mp.mpf(1)/2)) * h
               for i in range(n_j))

def segment_midpoint_error(a_j, b_j, n_j):
    """Provable midpoint error bound: (b-a)³·M/(24·n²).
    M is the maximum of M_segment on [a_j, b_j] — but since exp(-A_n·L) is
    decreasing in L, max of M_segment over [a_j, b_j] is at L = a_j."""
    M = M_segment(a_j)
    return (b_j - a_j)**3 * M / (24 * n_j**2)

# ------------------------------------------------------------------
# Test configurations
# ------------------------------------------------------------------
# Config A: modest split, medium n
# Rational endpoints: 1, 17/16, 9/8, 5/4, 11/8, 3/2, 2, 5/2, 3, 4, 5
CONFIG_A = [
    (mp.mpf(1),      mp.mpf(17)/16, 64),
    (mp.mpf(17)/16,  mp.mpf(9)/8,   32),
    (mp.mpf(9)/8,    mp.mpf(5)/4,   24),
    (mp.mpf(5)/4,    mp.mpf(11)/8,  16),
    (mp.mpf(11)/8,   mp.mpf(3)/2,   12),
    (mp.mpf(3)/2,    mp.mpf(2),     16),
    (mp.mpf(2),      mp.mpf(5)/2,   12),
    (mp.mpf(5)/2,    mp.mpf(3),     8),
    (mp.mpf(3),      mp.mpf(4),     8),
    (mp.mpf(4),      mp.mpf(5),     4),
]

# Config B: more aggressive near u=1
CONFIG_B = [
    (mp.mpf(1),      mp.mpf(17)/16, 128),
    (mp.mpf(17)/16,  mp.mpf(9)/8,   64),
    (mp.mpf(9)/8,    mp.mpf(5)/4,   32),
    (mp.mpf(5)/4,    mp.mpf(11)/8,  16),
    (mp.mpf(11)/8,   mp.mpf(3)/2,   16),
    (mp.mpf(3)/2,    mp.mpf(2),     16),
    (mp.mpf(2),      mp.mpf(5)/2,   8),
    (mp.mpf(5)/2,    mp.mpf(3),     8),
    (mp.mpf(3),      mp.mpf(4),     4),
    (mp.mpf(4),      mp.mpf(5),     4),
]

# Config C: heavy front
CONFIG_C = [
    (mp.mpf(1),      mp.mpf(17)/16, 256),
    (mp.mpf(17)/16,  mp.mpf(9)/8,   128),
    (mp.mpf(9)/8,    mp.mpf(5)/4,   64),
    (mp.mpf(5)/4,    mp.mpf(3)/2,   32),
    (mp.mpf(3)/2,    mp.mpf(2),     16),
    (mp.mpf(2),      mp.mpf(5)/2,   16),
    (mp.mpf(5)/2,    mp.mpf(3),     8),
    (mp.mpf(3),      mp.mpf(4),     4),
    (mp.mpf(4),      mp.mpf(5),     4),
]

# Config D: max out front, near-linear elsewhere
CONFIG_D = [
    (mp.mpf(1),      mp.mpf(17)/16, 512),
    (mp.mpf(17)/16,  mp.mpf(9)/8,   256),
    (mp.mpf(9)/8,    mp.mpf(5)/4,   128),
    (mp.mpf(5)/4,    mp.mpf(3)/2,   64),
    (mp.mpf(3)/2,    mp.mpf(2),     32),
    (mp.mpf(2),      mp.mpf(3),     16),
    (mp.mpf(3),      mp.mpf(5),     8),
]

def evaluate_config(name, segments):
    total_n = sum(s[2] for s in segments)
    total_re_lo = mp.mpf(0)
    total_re_hi = mp.mpf(0)
    total_im_lo = mp.mpf(0)
    total_im_hi = mp.mpf(0)
    total_err_re = mp.mpf(0)
    total_err_im = mp.mpf(0)
    # We report at σ endpoints. Uniform σ will use interval bounds later.
    print("=" * 70)
    print("Config {}: {} segments, total n = {}".format(name, len(segments), total_n))
    print("=" * 70)
    print("  {:>8} {:>8} {:>4} {:>12} {:>12} {:>12}"
          .format("a", "b", "n", "M(a)", "err_re", "err_im"))
    for a_j, b_j, n_j in segments:
        M = M_segment(a_j)
        err = segment_midpoint_error(a_j, b_j, n_j)
        total_err_re += err
        total_err_im += err
        print("  {:>8.4f} {:>8.4f} {:>4d} {:>12.3e} {:>12.3e} {:>12.3e}"
              .format(float(a_j), float(b_j), n_j, float(M), float(err), float(err)))
    print("  TOTAL midpoint err_re = {:.3e}".format(float(total_err_re)))
    print("  TOTAL midpoint err_im = {:.3e}".format(float(total_err_im)))
    print()
    for sigma in [SIGMA_LO, SIGMA_HI]:
        mid_re = sum(segment_midpoint_sum_re(sigma, a_j, b_j, n_j)
                    for a_j, b_j, n_j in segments)
        mid_im = sum(segment_midpoint_sum_im(sigma, a_j, b_j, n_j)
                    for a_j, b_j, n_j in segments)
        # Λ₀ enclosure: [mid - midpoint_err - §8 env, mid + midpoint_err + §8 env]
        re_lo = mid_re - total_err_re - ENVELOPE_LAMBDA
        re_hi = mid_re + total_err_re + ENVELOPE_LAMBDA
        im_lo = mid_im - total_err_im - ENVELOPE_LAMBDA
        im_hi = mid_im + total_err_im + ENVELOPE_LAMBDA
        print("  σ = {}".format(sigma))
        print("    mid ∫Re = {:.9f}   Λ₀ ∈ [{:.9f}, {:.9f}]"
              .format(float(mid_re), float(re_lo), float(re_hi)))
        print("      Rlo = 2221/500000 = {:.9f}   margin = {:.3e}   {}"
              .format(float(TARGET_RLO), float(re_lo - TARGET_RLO),
                      "PASS" if re_lo >= TARGET_RLO else "✗ FAIL"))
        print("    mid ∫Im = {:.9f}   Λ₀ ∈ [{:.9f}, {:.9f}]"
              .format(float(mid_im), float(im_lo), float(im_hi)))
        pass_im = im_lo >= -mp.mpf(1)/10000 and im_hi <= mp.mpf(1)/10000
        print("      |·| ≤ 1/10000   {}"
              .format("PASS" if pass_im else "✗ FAIL"))
    print()

if __name__ == "__main__":
    print("§8 Λ₀ envelope: {:.3e}".format(float(ENVELOPE_LAMBDA)))
    print("Target Rlo:   {:.9f}".format(float(TARGET_RLO)))
    print("Target |Im|: {:.9f}".format(1/10000))
    print()
    print("Provable |f''| coefficients (uniform on box 0, u ≥ 1):")
    print("  p1 = |a| max = 25/32 = {:.6f}".format(float(p1)))
    print("  p2 = |a(a-1)| max = 1425/1024 = {:.6f}".format(float(p2)))
    print("  c  = t/2 = 15/2 = {:.4f}".format(float(c)))
    print("  c+c² = 255/4 = {:.4f}".format(float(c_plus_c_sq)))
    print()
    print("Per-term coefficient (excluding exp(-A_n·L)):")
    for n in range(N):
        coef = p2 + c_plus_c_sq + A[n]**2 + 2*p1*c + 2*p1*A[n] + 2*c*A[n]
        print("  n={}: A_n = {:.4f}, coef = {:.2f}".format(n, float(A[n]), float(coef)))
    print()
    print("Msegment(L) at various L (with factor 2 for two exponent branches):")
    for L_val in [1, mp.mpf(17)/16, mp.mpf(9)/8, mp.mpf(5)/4, mp.mpf(3)/2, mp.mpf(2), mp.mpf(3), mp.mpf(5)]:
        print("  L = {:>6}: Msegment = {:.3e}".format(float(L_val), float(M_segment(L_val))))
    print()

    for name, config in [("A", CONFIG_A), ("B", CONFIG_B), ("C", CONFIG_C), ("D", CONFIG_D)]:
        evaluate_config(name, config)

    # ------------------------------------------------------------
    # Automatic segment allocator: given rational boundaries, choose n_j
    # to equalize per-segment error contribution against a target.
    # ------------------------------------------------------------
    def optimize_n(boundaries, target_total_err):
        """Given rational segment boundaries, choose n_j per segment so that
        sum of E_j ≤ target_total_err, minimizing total n."""
        S = len(boundaries) - 1
        target_per = target_total_err / S
        segments = []
        for j in range(S):
            a_j = boundaries[j]
            b_j = boundaries[j + 1]
            M = M_segment(a_j)
            # E = (b-a)³·M/(24·n²) ≤ target_per → n ≥ sqrt((b-a)³·M/(24·target_per))
            n_sq = (b_j - a_j)**3 * M / (24 * target_per)
            n_j = max(1, int(mp.ceil(mp.sqrt(n_sq))))
            segments.append((a_j, b_j, n_j))
        return segments

    # Try optimized allocation with progressively tighter targets
    print("=" * 70)
    print("AUTOMATIC ALLOCATION — 20 segments on [1, 5], target err = 3.5e-6")
    print("=" * 70)
    # Boundaries: 20 segments with denser near u=1
    boundaries_20 = [
        mp.mpf(1),
        mp.mpf(33)/32, mp.mpf(17)/16, mp.mpf(35)/32, mp.mpf(9)/8,
        mp.mpf(37)/32, mp.mpf(19)/16, mp.mpf(5)/4,
        mp.mpf(11)/8, mp.mpf(3)/2, mp.mpf(13)/8, mp.mpf(7)/4,
        mp.mpf(15)/8, mp.mpf(2),
        mp.mpf(9)/4, mp.mpf(5)/2,
        mp.mpf(3), mp.mpf(7)/2, mp.mpf(4),
        mp.mpf(9)/2, mp.mpf(5),
    ]
    config_opt = optimize_n(boundaries_20, mp.mpf('3.5e-6'))
    evaluate_config("OPT-20", config_opt)

    print("=" * 70)
    print("AUTOMATIC ALLOCATION — 40 segments on [1, 5], target err = 3.5e-6")
    print("=" * 70)
    boundaries_40 = []
    # Dense near u=1 with 1/32 spacing, then 1/16, then 1/8, then 1/4
    boundaries_40.append(mp.mpf(1))
    for k in range(1, 17):  # 1 → 1+16/32 = 3/2
        boundaries_40.append(mp.mpf(1) + mp.mpf(k)/32)
    for k in range(1, 9):  # 3/2 → 3/2 + 8/16 = 2
        boundaries_40.append(mp.mpf(3)/2 + mp.mpf(k)/16)
    for k in range(1, 9):  # 2 → 2 + 8/8 = 3
        boundaries_40.append(mp.mpf(2) + mp.mpf(k)/8)
    for k in range(1, 9):  # 3 → 3 + 8/4 = 5
        boundaries_40.append(mp.mpf(3) + mp.mpf(k)/4)
    boundaries_40 = sorted(set(boundaries_40))
    config_opt40 = optimize_n(boundaries_40, mp.mpf('3.5e-6'))
    evaluate_config("OPT-40", config_opt40)

    # Try tighter budget
    print("=" * 70)
    print("AUTOMATIC ALLOCATION — 40 seg, target err = 2.0e-6 (safety)")
    print("=" * 70)
    config_opt40_tight = optimize_n(boundaries_40, mp.mpf('2.0e-6'))
    evaluate_config("OPT-40-TIGHT", config_opt40_tight)
