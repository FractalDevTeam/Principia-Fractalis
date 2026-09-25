#!/usr/bin/env python3
"""
gen_r331b_box_panels.py — BOX-PARAMETRIC generator for r331b top-edge boxes.

Extends `gen_r331b_box0_panels.py` to any of the eight σ-boxes covering
[1/2, 1] at t=15. Same governance: mpmath dps=100, 12-digit outward
rounding, deterministic. Generator emits candidates only — Lean kernel
independently certifies.

Box K covers σ ∈ [σ_lo(K), σ_hi(K)] with the standard uniform 8-box
tiling:
    σ_lo(K) = 1/2 + K/16
    σ_hi(K) = 1/2 + (K+1)/16      for K = 0..7

K=0 recovers the frozen Box 0 = [1/2, 9/16].

Per-box derived constants:
    a1(σ)   = σ/2 - 1                             (in [σ_lo/2-1, σ_hi/2-1])
    a2(σ)   = (1-σ)/2 - 1                         (in [(1-σ_hi)/2-1, (1-σ_lo)/2-1])
    p1(K)   = max(|a1|, |a2|) over the box        (used in M_term coefficient)
    p2(K)   = max(|a(a-1)|) over the box          (used in M_term coefficient)

Note on the σ-uniform amplitude enclosure at each node u:
    A_lo_tight(σ) = u^a1 + u^a2 has min over σ at BOTH endpoints; we take
      the min at σ_lo AND σ_hi (both u^a monotone in a for u≥1) — actually
      for u≥1, u^a is decreasing in a for a<0. So a1 ≤ a2 (since σ ≥ 1/2)
      means u^a1 ≥ u^a2. So the MAX of the amplitude sum is at MIN a1 =
      most-negative a1 = a1(σ_hi). The MIN of the sum is at σ where a1+a2
      derivative wrt σ vanishes... but a1+a2 = σ/2-1 + (1-σ)/2-1 = -1, so
      a1+a2 is CONSTANT! Great — the amplitude sum's σ-dependence is
      captured entirely by a1 vs a2 spread, not by the sum of a's.

For box 0 the tight AM-GM bound `2·u^(-3/4)` is exact at σ=1/2 (where
a1=a2=-3/4). For box K>0 there is NO σ ∈ [σ_lo, σ_hi] where a1=a2, so
we use monotonicity: u^a1 + u^a2 is decreasing in σ (u≥1) → MIN at σ_hi,
MAX at σ_lo.

Similarly u^a1 - u^a2 is increasing in σ (u≥1) → MIN at σ_lo, MAX at σ_hi.

USAGE
    python3 gen_r331b_box_panels.py --box K --dry-run
    python3 gen_r331b_box_panels.py --box K --stage1
"""
import argparse
import mpmath as mp
from fractions import Fraction
import sys

mp.mp.dps = 100

# ---------------------------------------------------------------------------
# Fixed inputs (shared across boxes)
# ---------------------------------------------------------------------------
T15 = mp.mpf(15)
HALF_T15 = mp.mpf(15) / 2
N = 3
T_FRAC = Fraction(5)
T_MP = mp.mpf(5)
PI = mp.pi
A_n = [PI * (n + 1) ** 2 for n in range(N)]
c_val = mp.mpf(15) / 2
c_plus_c_sq = c_val + c_val * c_val

# Standard 8-box tiling of [1/2, 1] into equal 1/16-width boxes.
def box_sigma_range(K: int):
    assert 0 <= K < 8, "K must be in 0..7"
    sig_lo = Fraction(1, 2) + Fraction(K, 16)
    sig_hi = Fraction(1, 2) + Fraction(K + 1, 16)
    return sig_lo, sig_hi

# ---------------------------------------------------------------------------
# Per-box derived quantities
# ---------------------------------------------------------------------------
def box_a_extremes(sig_lo: Fraction, sig_hi: Fraction):
    """Return (a1_lo, a1_hi, a2_lo, a2_hi) with a1(σ) = σ/2-1, a2(σ) = (1-σ)/2-1."""
    a1_lo = sig_lo / 2 - 1     # most negative a1 (min σ)
    a1_hi = sig_hi / 2 - 1
    a2_lo = (1 - sig_hi) / 2 - 1  # most negative a2 (max σ)
    a2_hi = (1 - sig_lo) / 2 - 1
    return a1_lo, a1_hi, a2_lo, a2_hi

def box_pow_bounds(sig_lo: Fraction, sig_hi: Fraction):
    """max(|a|) and max(|a(a-1)|) over σ ∈ [sig_lo, sig_hi] for both a1, a2.
    Used in M_term coefficient. Returns (p1_max, p2_max) as mpf."""
    a1_lo, a1_hi, a2_lo, a2_hi = box_a_extremes(sig_lo, sig_hi)
    all_a = [a1_lo, a1_hi, a2_lo, a2_hi]
    max_abs_a = max(abs(mp.mpf(a.numerator) / a.denominator) for a in all_a)
    # |a(a-1)| — since a ≤ 0 for both a1, a2 in our range, a-1 ≤ -1 < 0 → a(a-1) ≥ 0.
    # a(a-1) = a² - a. For a ≤ 0: a² grows as |a| grows, -a is positive, so a(a-1) is
    # increasing in |a|. Max at max |a|.
    max_a_amp = max_abs_a
    max_a_a_minus_one = max_a_amp * (max_a_amp + 1)  # since a ≤ 0, a-1 ≤ -1, |a(a-1)| = |a|·|a-1| = |a|·(|a|+1)
    # Actually simpler: a(a-1) evaluated at extremes.
    # For each corner |a(a-1)| = |a| · |a - 1|. Since a ≤ 0, a - 1 ≤ -1, |a-1| = 1 - a = 1 + |a|.
    # So max |a(a-1)| = max |a| · (1 + max |a|) — take the extreme.
    return max_abs_a, max_a_amp * (1 + max_a_amp)

def M_term(L, n, p1_mp, p2_mp):
    An = A_n[n]
    coef = p2_mp + c_plus_c_sq + An * An + 2 * p1_mp * c_val + 2 * p1_mp * An + 2 * c_val * An
    return mp.exp(-An * L) * coef

def M_segment(L, p1_mp, p2_mp):
    return 2 * sum(M_term(L, n, p1_mp, p2_mp) for n in range(N))

# §8 envelope — box-independent (only depends on N, T=5)
DELTA_N = mp.exp(-PI * (N + 1) ** 2) / (1 - mp.exp(-PI))
TRUNC_ENVELOPE = 2 * (T_MP - 1) * DELTA_N
TAIL_ENVELOPE = 2 / PI * mp.exp(-PI * T_MP) / (1 - mp.exp(-PI))
E_ANALYTIC = TRUNC_ENVELOPE + TAIL_ENVELOPE

# Targets (frozen — Box 0's target ≈ 2221/500000 works for all boxes per the
# consumer arithmetic; per-box tightening can be added later if needed).
TARGET_RLO = Fraction(2221, 500000)
TARGET_IM_HI = Fraction(1, 10000)
TARGET_IM_LO = -Fraction(1, 10000)

# ---------------------------------------------------------------------------
# OPT-40-TIGHT geometry (fractions) — box-independent u-partition of [1, 5]
# ---------------------------------------------------------------------------
def build_segments(p1_mp, p2_mp):
    """Return list of (a_j, b_j, n_j) with exact rational endpoints.
    n_j is adjusted per-box via M_segment(p1, p2)."""
    boundaries = [Fraction(1)]
    for k in range(1, 17):
        boundaries.append(Fraction(1) + Fraction(k, 32))
    for k in range(1, 9):
        boundaries.append(Fraction(3, 2) + Fraction(k, 16))
    for k in range(1, 9):
        boundaries.append(Fraction(2) + Fraction(k, 8))
    for k in range(1, 9):
        boundaries.append(Fraction(3) + Fraction(k, 4))
    boundaries = sorted(set(boundaries))
    target_per = mp.mpf('2.0e-6') / (len(boundaries) - 1)
    segments = []
    for j in range(len(boundaries) - 1):
        a_j = boundaries[j]
        b_j = boundaries[j + 1]
        width_mp = mp.mpf(b_j.numerator) / b_j.denominator - mp.mpf(a_j.numerator) / a_j.denominator
        M_j = M_segment(mp.mpf(a_j.numerator) / a_j.denominator, p1_mp, p2_mp)
        n_sq = width_mp ** 3 * M_j / (24 * target_per)
        n_j = max(1, int(mp.ceil(mp.sqrt(n_sq))))
        segments.append((a_j, b_j, n_j))
    return segments

def frac_to_mp(x: Fraction) -> mp.mpf:
    return mp.mpf(x.numerator) / x.denominator

def omega_partial_3(u_mp):
    return sum(mp.exp(-A_n[n] * u_mp) for n in range(N))

def realThetaReN(sig_mp, u_mp):
    a1 = sig_mp / 2 - 1
    a2 = (1 - sig_mp) / 2 - 1
    return (mp.power(u_mp, a1) + mp.power(u_mp, a2)) \
           * mp.cos(HALF_T15 * mp.log(u_mp)) \
           * omega_partial_3(u_mp)

def realThetaImN(sig_mp, u_mp):
    a1 = sig_mp / 2 - 1
    a2 = (1 - sig_mp) / 2 - 1
    return (mp.power(u_mp, a1) - mp.power(u_mp, a2)) \
           * mp.sin(HALF_T15 * mp.log(u_mp)) \
           * omega_partial_3(u_mp)

# ---------------------------------------------------------------------------
# Box-K σ-uniform node bounds. For u ≥ 1 and σ ∈ [sig_lo, sig_hi]:
#   u^a1 is decreasing in σ (a1 increasing in σ, u≥1 → u^a1 decreasing)
#   Wait — a1 = σ/2 - 1 is INCREASING in σ. For u > 1, u^a is INCREASING in a
#   (for u>1). Actually let's think: u=e^L, u^a = e^{a·L}. For u>1, L>0, so
#   u^a is INCREASING in a. So a1 increasing in σ → u^a1 increasing in σ.
#   Similarly a2 = (1-σ)/2-1 is DECREASING in σ → u^a2 decreasing in σ.
#
# So u^a1 + u^a2: derivative w.r.t. σ = (1/2)·u^a1·log(u) - (1/2)·u^a2·log(u)
#                                     = (log u / 2)·(u^a1 - u^a2)
# For σ ≥ 1/2: a1 ≥ a2, so u^a1 ≥ u^a2, so derivative ≥ 0 for u≥1.
# → u^a1 + u^a2 is INCREASING in σ on [1/2, 1]. Min at σ_lo, MAX at σ_hi.
# → u^a1 - u^a2: derivative = (log u / 2)·(u^a1 + u^a2) ≥ 0.
# → u^a1 - u^a2 is INCREASING in σ. Min at σ_lo, MAX at σ_hi.
# ---------------------------------------------------------------------------
def node_re_ideal_bounds_box(u_mp, sig_lo_mp, sig_hi_mp):
    """Uniform enclosure of realThetaReN(σ, 15, u) for σ ∈ [sig_lo, sig_hi].
    Sign-aware combination of the amplitude sum bounds and cos·ωP."""
    a1_lo_mp = sig_lo_mp / 2 - 1
    a2_lo_mp = (1 - sig_lo_mp) / 2 - 1
    a1_hi_mp = sig_hi_mp / 2 - 1
    a2_hi_mp = (1 - sig_hi_mp) / 2 - 1
    A_lo = mp.power(u_mp, a1_lo_mp) + mp.power(u_mp, a2_lo_mp)  # min amplitude (at σ_lo)
    A_hi = mp.power(u_mp, a1_hi_mp) + mp.power(u_mp, a2_hi_mp)  # max amplitude (at σ_hi)
    # For u=1, amplitudes equal 2 at both endpoints — safe.
    C = mp.cos(HALF_T15 * mp.log(u_mp))
    W = omega_partial_3(u_mp)
    CW = C * W
    if CW <= 0:
        re_bound_lo = A_hi * CW
        re_bound_hi = A_lo * CW
    else:
        re_bound_lo = A_lo * CW
        re_bound_hi = A_hi * CW
    return re_bound_lo, re_bound_hi

def node_im_ideal_bounds_box(u_mp, sig_lo_mp, sig_hi_mp):
    """Uniform enclosure of realThetaImN for σ ∈ [sig_lo, sig_hi]."""
    a1_lo_mp = sig_lo_mp / 2 - 1
    a2_lo_mp = (1 - sig_lo_mp) / 2 - 1
    a1_hi_mp = sig_hi_mp / 2 - 1
    a2_hi_mp = (1 - sig_hi_mp) / 2 - 1
    D_lo = mp.power(u_mp, a1_lo_mp) - mp.power(u_mp, a2_lo_mp)  # min diff (at σ_lo)
    D_hi = mp.power(u_mp, a1_hi_mp) - mp.power(u_mp, a2_hi_mp)  # max diff (at σ_hi)
    S = mp.sin(HALF_T15 * mp.log(u_mp))
    W = omega_partial_3(u_mp)
    SW = S * W
    if SW <= 0:
        im_bound_lo = D_hi * SW
        im_bound_hi = D_lo * SW
    else:
        im_bound_lo = D_lo * SW
        im_bound_hi = D_hi * SW
    return im_bound_lo, im_bound_hi

# ---------------------------------------------------------------------------
# Outward rounding
# ---------------------------------------------------------------------------
def floor_toward_minus_inf(x_mp, digits=12):
    scale = mp.mpf(10) ** digits
    scaled = mp.floor(x_mp * scale)
    return Fraction(int(scaled)) / (10 ** digits)

def ceil_toward_plus_inf(x_mp, digits=12):
    scale = mp.mpf(10) ** digits
    scaled = mp.ceil(x_mp * scale)
    return Fraction(int(scaled)) / (10 ** digits)

# ---------------------------------------------------------------------------
# Dry-run
# ---------------------------------------------------------------------------
def dry_run(K: int):
    sig_lo, sig_hi = box_sigma_range(K)
    sig_lo_mp = frac_to_mp(sig_lo)
    sig_hi_mp = frac_to_mp(sig_hi)
    p1_mp, p2_mp = box_pow_bounds(sig_lo, sig_hi)
    segments = build_segments(p1_mp, p2_mp)

    total_Q_re_cert_lo = Fraction(0)
    total_Q_re_cert_hi = Fraction(0)
    total_Q_im_cert_lo = Fraction(0)
    total_Q_im_cert_hi = Fraction(0)
    total_E_quad = mp.mpf(0)

    print("=" * 80)
    print(f"DRY RUN — Box {K}  σ ∈ [{sig_lo}, {sig_hi}]")
    print("=" * 80)
    print(f"a1 range: [{sig_lo/2 - 1}, {sig_hi/2 - 1}]")
    print(f"a2 range: [{(1-sig_hi)/2 - 1}, {(1-sig_lo)/2 - 1}]")
    print(f"p1 (max |a|):        {float(p1_mp):.6f}")
    print(f"p2 (max |a(a-1)|):   {float(p2_mp):.6f}")
    print(f"§8 envelope:         {float(E_ANALYTIC):.3e}")
    print(f"Target Rlo:  2221/500000 = {float(TARGET_RLO):.9f}")
    print(f"Target |Im|: 1/10000     = {float(TARGET_IM_HI):.9f}")
    print(f"Total segments (adaptive): {len(segments)}")
    print(f"Total panels:              {sum(s[2] for s in segments)}")
    print()

    for j, (a_j, b_j, n_j) in enumerate(segments):
        a_mp = frac_to_mp(a_j)
        b_mp = frac_to_mp(b_j)
        h_frac = (b_j - a_j) / n_j
        M_j = M_segment(a_mp, p1_mp, p2_mp)
        width_mp = b_mp - a_mp
        E_j_quad = M_j * width_mp ** 3 / (24 * n_j ** 2)
        total_E_quad += E_j_quad

        seg_re_lo = Fraction(0); seg_re_hi = Fraction(0)
        seg_im_lo = Fraction(0); seg_im_hi = Fraction(0)
        for i in range(n_j):
            u_frac = a_j + h_frac * (Fraction(i) + Fraction(1, 2))
            u_mp = frac_to_mp(u_frac)
            re_lo_mp, re_hi_mp = node_re_ideal_bounds_box(u_mp, sig_lo_mp, sig_hi_mp)
            im_lo_mp, im_hi_mp = node_im_ideal_bounds_box(u_mp, sig_lo_mp, sig_hi_mp)
            seg_re_lo += floor_toward_minus_inf(re_lo_mp)
            seg_re_hi += ceil_toward_plus_inf(re_hi_mp)
            seg_im_lo += floor_toward_minus_inf(im_lo_mp)
            seg_im_hi += ceil_toward_plus_inf(im_hi_mp)

        total_Q_re_cert_lo += h_frac * seg_re_lo
        total_Q_re_cert_hi += h_frac * seg_re_hi
        total_Q_im_cert_lo += h_frac * seg_im_lo
        total_Q_im_cert_hi += h_frac * seg_im_hi

    Q_re_lo_mp = mp.mpf(total_Q_re_cert_lo.numerator) / total_Q_re_cert_lo.denominator
    Q_re_hi_mp = mp.mpf(total_Q_re_cert_hi.numerator) / total_Q_re_cert_hi.denominator
    Q_im_lo_mp = mp.mpf(total_Q_im_cert_lo.numerator) / total_Q_im_cert_lo.denominator
    Q_im_hi_mp = mp.mpf(total_Q_im_cert_hi.numerator) / total_Q_im_cert_hi.denominator

    RE_FINAL_LO = Q_re_lo_mp - total_E_quad - E_ANALYTIC
    RE_MARGIN   = RE_FINAL_LO - frac_to_mp(TARGET_RLO)
    IM_TRUE_LO  = Q_im_lo_mp - total_E_quad - E_ANALYTIC
    IM_TRUE_HI  = Q_im_hi_mp + total_E_quad + E_ANALYTIC
    IM_MARGIN_LO = IM_TRUE_LO - frac_to_mp(TARGET_IM_LO)
    IM_MARGIN_HI = frac_to_mp(TARGET_IM_HI) - IM_TRUE_HI

    print("--- CANDIDATE (outward 12-digit, σ-uniform over box) ---")
    print(f"Q_RE_CANDIDATE_LO: {float(Q_re_lo_mp):.12e}")
    print(f"Q_RE_CANDIDATE_HI: {float(Q_re_hi_mp):.12e}")
    print(f"Q_IM_CANDIDATE_LO: {float(Q_im_lo_mp):.12e}")
    print(f"Q_IM_CANDIDATE_HI: {float(Q_im_hi_mp):.12e}")
    print(f"E_QUAD:            {float(total_E_quad):.3e}")
    print()
    print("--- FINAL Re ---")
    print(f"RE_FINAL_LO = Q_lo - E_quad - E_analytic = {float(RE_FINAL_LO):.12e}")
    print(f"Target Rlo                                = {float(TARGET_RLO):.12e}")
    print(f"RE_MARGIN                                 = {float(RE_MARGIN):.3e}   {'PASS' if RE_MARGIN > 0 else 'FAIL'}")
    print()
    print("--- FINAL Im ---")
    print(f"IM_TRUE_LO = {float(IM_TRUE_LO):.12e}")
    print(f"IM_TRUE_HI = {float(IM_TRUE_HI):.12e}")
    print(f"IM_MARGIN_LO = {float(IM_MARGIN_LO):.3e}   {'PASS' if IM_MARGIN_LO > 0 else 'FAIL'}")
    print(f"IM_MARGIN_HI = {float(IM_MARGIN_HI):.3e}   {'PASS' if IM_MARGIN_HI > 0 else 'FAIL'}")
    print()
    ok = RE_MARGIN > 0 and IM_MARGIN_LO > 0 and IM_MARGIN_HI > 0
    print(f"OVERALL: {'PASS' if ok else 'FAIL'}")
    return ok

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--box", type=int, required=True, help="box index 0..7")
    parser.add_argument("--dry-run", action="store_true", default=True)
    parser.add_argument("--all", action="store_true", help="run dry-run for all 8 boxes")
    args = parser.parse_args()
    if args.all:
        results = []
        for K in range(8):
            print(f"\n{'#'*80}\n# BOX {K}\n{'#'*80}")
            r = dry_run(K)
            results.append((K, r))
        print("\n" + "=" * 80)
        print("SUMMARY")
        print("=" * 80)
        for K, r in results:
            print(f"Box {K}: {'PASS' if r else 'FAIL'}")
        sys.exit(0 if all(r for _, r in results) else 1)
    else:
        r = dry_run(args.box)
        sys.exit(0 if r else 1)
