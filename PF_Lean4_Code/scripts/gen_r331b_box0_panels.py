#!/usr/bin/env python3
"""
gen_r331b_box0_panels.py — deterministic generator for r331b box 0
midpoint-node certificates.

## SCIENTIFIC ROLE

Emits candidate outward-safe rational lower/upper bounds for
`realThetaRe/ImIntegrandN 3 σ 15 u_{j,i}` at every midpoint of every
OPT-40-TIGHT segment.  Every emitted value is a candidate; the Lean
kernel independently verifies via `Interval.approx_le/lt` + `by approx`
+ `decide +kernel`.

NOT PROOF.  Reconnaissance/provenance only.

## GEOMETRY

40 segments × per-segment n_j midpoints on [1, 5].  Exact rational
midpoints via `fractions.Fraction`.  Total 530 midpoint nodes.

## OUTPUT MODES

    --dry-run   Report exact rational Q_RE/IM_CANDIDATE, E_QUAD, RE_MARGIN.
                Emit NO Lean files.  MUST pass before mass emission.

    --emit      Emit Lean files under PF/Analytic/Box0Panels/.
                Only run after --dry-run passes.

## ROUNDING POLICY (candidate emission)

Working precision: mpmath dps = 100.
Emitted precision: 12 digits, floor toward -∞ for lower bounds
                    (safe: emitted decimal ≤ true value),
                    ceil toward +∞ for upper bounds.
The 88-digit gap between working and emitted precision leaves ~10^80×
headroom above interval-engine decimal parsing.

## E_NODE IS DIAGNOSTIC ONLY

Once emitted certified lower sums are used in the formal proof, node
rounding is baked into the certified quantity.  Do NOT subtract E_NODE
again from Q_RE/IM_CANDIDATE.  The formal Lean chain is:

    RE_FINAL_LO := Q_RE_CANDIDATE_LO - E_QUAD - E_ANALYTIC

with margin `RE_MARGIN := RE_FINAL_LO - 2221/500000`.

Usage:
    python3 gen_r331b_box0_panels.py --dry-run
"""
import mpmath as mp
from fractions import Fraction
from decimal import Decimal, ROUND_FLOOR, ROUND_CEILING, localcontext
import argparse
import sys

mp.mp.dps = 100

# ---------------------------------------------------------------------------
# Fixed inputs
# ---------------------------------------------------------------------------
T15 = mp.mpf(15)
HALF_T15 = mp.mpf(15) / 2
N = 3
T_FRAC = Fraction(5)
T_MP = mp.mpf(5)
SIGMA_LO = Fraction(1, 2)
SIGMA_HI = Fraction(9, 16)

# π · (n+1)²
PI = mp.pi
A_n = [PI * (n + 1) ** 2 for n in range(N)]

# Uniform C² coefficients (per-coordinate provable bound at t=15):
p1 = mp.mpf(25) / 32
p2 = mp.mpf(1425) / 1024
c_val = mp.mpf(15) / 2
c_plus_c_sq = c_val + c_val * c_val  # 255/4

def M_term(L, n):
    An = A_n[n]
    coef = p2 + c_plus_c_sq + An * An + 2 * p1 * c_val + 2 * p1 * An + 2 * c_val * An
    return mp.exp(-An * L) * coef

def M_segment(L):
    """Per-coordinate M bound for the two-branch sum over n<3."""
    return 2 * sum(M_term(L, n) for n in range(N))

# §8 envelope
DELTA_N = mp.exp(-PI * (N + 1) ** 2) / (1 - mp.exp(-PI))
TRUNC_ENVELOPE = 2 * (T_MP - 1) * DELTA_N
TAIL_ENVELOPE = 2 / PI * mp.exp(-PI * T_MP) / (1 - mp.exp(-PI))
E_ANALYTIC = TRUNC_ENVELOPE + TAIL_ENVELOPE  # per coordinate

TARGET_RLO = Fraction(2221, 500000)
TARGET_IM_HI = Fraction(1, 10000)
TARGET_IM_LO = -Fraction(1, 10000)

# ---------------------------------------------------------------------------
# OPT-40-TIGHT geometry (fractions)
# ---------------------------------------------------------------------------
def build_segments():
    """Return list of (a_j, b_j, n_j) with exact rational endpoints."""
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
        M_j = M_segment(mp.mpf(a_j.numerator) / a_j.denominator)
        n_sq = width_mp ** 3 * M_j / (24 * target_per)
        n_j = max(1, int(mp.ceil(mp.sqrt(n_sq))))
        segments.append((a_j, b_j, n_j))
    return segments

SEGMENTS = build_segments()

# ---------------------------------------------------------------------------
# Integrand evaluators (exact rational u, high-precision mpmath)
# ---------------------------------------------------------------------------
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
# σ-uniform node value (at fixed rational u; A varies with σ)
# For box 0: prove per-node bounds valid for ALL σ ∈ [1/2, 9/16].
# Numerically, evaluate at both σ endpoints and take worst case.
# ---------------------------------------------------------------------------
def node_re_ideal_bounds(u_mp):
    """Return (lo, hi) of realThetaReN(σ, 15, u) uniform in σ ∈ [1/2, 9/16].

    Uses the TIGHT §9.7-tight power-sum bounds:
      A_lo_tight = 2·u^(-3/4)                     (AM-GM, tight at σ=1/2)
      A_hi_tight = u^(-23/32) + u^(-25/32)        (monotonicity, tight at σ=9/16)
    """
    A_lo = 2 * mp.power(u_mp, -mp.mpf(3)/4)
    A_hi = mp.power(u_mp, -mp.mpf(23)/32) + mp.power(u_mp, -mp.mpf(25)/32)
    C = mp.cos(HALF_T15 * mp.log(u_mp))
    W = omega_partial_3(u_mp)
    if C <= 0:
        re_bound_lo = A_hi * C * W  # most negative (bigger A · negative C·W)
        re_bound_hi = A_lo * C * W  # least negative
    else:
        re_bound_lo = A_lo * C * W
        re_bound_hi = A_hi * C * W
    return re_bound_lo, re_bound_hi

def node_im_ideal_bounds(u_mp):
    """Return (lo, hi) of realThetaImN(σ, 15, u) uniform in σ ∈ [1/2, 9/16]."""
    v_lo_sig = realThetaImN(frac_to_mp(SIGMA_LO), u_mp)  # = 0 at σ=1/2
    v_hi_sig = realThetaImN(frac_to_mp(SIGMA_HI), u_mp)
    D_hi = mp.power(u_mp, -mp.mpf(23)/32) - mp.power(u_mp, -mp.mpf(25)/32)  # ≥ 0
    S = mp.sin(HALF_T15 * mp.log(u_mp))
    W = omega_partial_3(u_mp)
    # D ∈ [0, D_hi]. Im = D · S · W. Sign depends on S.
    if S <= 0:
        im_bound_lo = D_hi * S * W  # most negative
        im_bound_hi = mp.mpf(0)      # least negative (at D=0)
    else:
        im_bound_lo = mp.mpf(0)
        im_bound_hi = D_hi * S * W
    lo = min(v_lo_sig, v_hi_sig, im_bound_lo)
    hi = max(v_lo_sig, v_hi_sig, im_bound_hi)
    return lo, hi

# ---------------------------------------------------------------------------
# Outward rounding to 12 decimal digits
# ---------------------------------------------------------------------------
def floor_toward_minus_inf(x_mp, digits=12):
    """Return Fraction ≤ x_mp with 12 significant decimal digits, floored."""
    scale = mp.mpf(10) ** digits
    scaled = mp.floor(x_mp * scale)
    return Fraction(int(scaled)) / (10 ** digits)

def ceil_toward_plus_inf(x_mp, digits=12):
    """Return Fraction ≥ x_mp with 12 significant decimal digits, ceiling'd."""
    scale = mp.mpf(10) ** digits
    scaled = mp.ceil(x_mp * scale)
    return Fraction(int(scaled)) / (10 ** digits)

# ---------------------------------------------------------------------------
# Dry-run report
# ---------------------------------------------------------------------------
def dry_run():
    total_Q_re_cert_lo = Fraction(0)
    total_Q_re_cert_hi = Fraction(0)
    total_Q_im_cert_lo = Fraction(0)
    total_Q_im_cert_hi = Fraction(0)
    total_Q_re_ideal = mp.mpf(0)
    total_Q_im_ideal = mp.mpf(0)
    total_E_quad = mp.mpf(0)
    total_E_node_re_diag = mp.mpf(0)
    total_E_node_im_diag = mp.mpf(0)

    print("=" * 80)
    print("DRY RUN — gen_r331b_box0_panels.py")
    print("=" * 80)
    print(f"§8 envelope E_ANALYTIC (per coord): {float(E_ANALYTIC):.3e}")
    print(f"Target Rlo:  2221/500000 = {float(TARGET_RLO):.9f}")
    print(f"Target |Im|: 1/10000     = {float(TARGET_IM_HI):.9f}")
    print()

    for j, (a_j, b_j, n_j) in enumerate(SEGMENTS):
        a_mp = frac_to_mp(a_j)
        b_mp = frac_to_mp(b_j)
        h_frac = (b_j - a_j) / n_j
        h_mp = frac_to_mp(h_frac)
        M_j = M_segment(a_mp)
        width_mp = b_mp - a_mp
        E_j_quad = M_j * width_mp ** 3 / (24 * n_j ** 2)
        total_E_quad += E_j_quad

        seg_Q_re_cert_lo = Fraction(0)
        seg_Q_re_cert_hi = Fraction(0)
        seg_Q_im_cert_lo = Fraction(0)
        seg_Q_im_cert_hi = Fraction(0)
        seg_Q_re_ideal = mp.mpf(0)
        seg_Q_im_ideal = mp.mpf(0)

        for i in range(n_j):
            u_frac = a_j + h_frac * (Fraction(i) + Fraction(1, 2))
            u_mp = frac_to_mp(u_frac)
            re_lo_mp, re_hi_mp = node_re_ideal_bounds(u_mp)
            im_lo_mp, im_hi_mp = node_im_ideal_bounds(u_mp)
            re_ideal = realThetaReN(frac_to_mp(SIGMA_LO), u_mp)
            im_ideal = realThetaImN(frac_to_mp(SIGMA_LO), u_mp)
            re_lo_frac = floor_toward_minus_inf(re_lo_mp)
            re_hi_frac = ceil_toward_plus_inf(re_hi_mp)
            im_lo_frac = floor_toward_minus_inf(im_lo_mp)
            im_hi_frac = ceil_toward_plus_inf(im_hi_mp)
            seg_Q_re_cert_lo += re_lo_frac
            seg_Q_re_cert_hi += re_hi_frac
            seg_Q_im_cert_lo += im_lo_frac
            seg_Q_im_cert_hi += im_hi_frac
            seg_Q_re_ideal += re_ideal
            seg_Q_im_ideal += im_ideal
            total_E_node_re_diag += max(re_ideal - frac_to_mp(re_lo_frac), mp.mpf(0)) * h_mp
            total_E_node_im_diag += max(im_ideal - frac_to_mp(im_lo_frac), mp.mpf(0)) * h_mp

        total_Q_re_cert_lo += h_frac * seg_Q_re_cert_lo
        total_Q_re_cert_hi += h_frac * seg_Q_re_cert_hi
        total_Q_im_cert_lo += h_frac * seg_Q_im_cert_lo
        total_Q_im_cert_hi += h_frac * seg_Q_im_cert_hi
        total_Q_re_ideal += h_mp * seg_Q_re_ideal
        total_Q_im_ideal += h_mp * seg_Q_im_ideal

    total_Q_re_cert_lo_mp = mp.mpf(total_Q_re_cert_lo.numerator) / total_Q_re_cert_lo.denominator
    total_Q_re_cert_hi_mp = mp.mpf(total_Q_re_cert_hi.numerator) / total_Q_re_cert_hi.denominator
    total_Q_im_cert_lo_mp = mp.mpf(total_Q_im_cert_lo.numerator) / total_Q_im_cert_lo.denominator
    total_Q_im_cert_hi_mp = mp.mpf(total_Q_im_cert_hi.numerator) / total_Q_im_cert_hi.denominator

    RE_FINAL_LO_mp = total_Q_re_cert_lo_mp - total_E_quad - E_ANALYTIC
    RE_MARGIN_mp = RE_FINAL_LO_mp - mp.mpf(TARGET_RLO.numerator) / TARGET_RLO.denominator

    IM_TRUE_LO_mp = total_Q_im_cert_lo_mp - total_E_quad - E_ANALYTIC
    IM_TRUE_HI_mp = total_Q_im_cert_hi_mp + total_E_quad + E_ANALYTIC
    IM_MARGIN_LO_mp = IM_TRUE_LO_mp - mp.mpf(TARGET_IM_LO.numerator) / TARGET_IM_LO.denominator
    IM_MARGIN_HI_mp = mp.mpf(TARGET_IM_HI.numerator) / TARGET_IM_HI.denominator - IM_TRUE_HI_mp

    print(f"Total panels:           {sum(s[2] for s in SEGMENTS)}")
    print(f"Total segments:         {len(SEGMENTS)}")
    print()
    print("--- IDEAL (mpmath dps=100, at σ=1/2 for cross-check) ---")
    print(f"Q_RE_IDEAL:             {float(total_Q_re_ideal):.12e}")
    print(f"Q_IM_IDEAL:             {float(total_Q_im_ideal):.12e}")
    print()
    print("--- CANDIDATE (outward 12-digit rounding, σ-uniform) ---")
    print(f"Q_RE_CANDIDATE_LO:      {float(total_Q_re_cert_lo_mp):.12e}")
    print(f"Q_RE_CANDIDATE_HI:      {float(total_Q_re_cert_hi_mp):.12e}")
    print(f"Q_IM_CANDIDATE_LO:      {float(total_Q_im_cert_lo_mp):.12e}")
    print(f"Q_IM_CANDIDATE_HI:      {float(total_Q_im_cert_hi_mp):.12e}")
    print()
    print("--- DIAGNOSTIC E_NODE (integral loss, do NOT subtract in formal proof) ---")
    print(f"E_NODE_RE_DIAG:         {float(total_E_node_re_diag):.3e}")
    print(f"E_NODE_IM_DIAG:         {float(total_E_node_im_diag):.3e}")
    print()
    print("--- FORMAL LEDGER ---")
    print(f"E_QUAD (Σ segments):    {float(total_E_quad):.3e}")
    print(f"E_ANALYTIC:             {float(E_ANALYTIC):.3e}")
    print()
    print("--- FINAL Re ---")
    print(f"RE_FINAL_LO := Q_RE_CANDIDATE_LO - E_QUAD - E_ANALYTIC")
    print(f"              = {float(RE_FINAL_LO_mp):.12e}")
    print(f"Target Rlo    = {float(TARGET_RLO):.12e}")
    print(f"RE_MARGIN     = {float(RE_MARGIN_mp):.3e}   {'PASS' if RE_MARGIN_mp > 0 else 'FAIL'}")
    print()
    print("--- FINAL Im ---")
    print(f"IM_TRUE_LO    = {float(IM_TRUE_LO_mp):.12e}")
    print(f"IM_TRUE_HI    = {float(IM_TRUE_HI_mp):.12e}")
    print(f"Target Im lo  = {float(TARGET_IM_LO):.12e}")
    print(f"Target Im hi  = {float(TARGET_IM_HI):.12e}")
    print(f"IM_MARGIN_LO  = {float(IM_MARGIN_LO_mp):.3e}   {'PASS' if IM_MARGIN_LO_mp > 0 else 'FAIL'}")
    print(f"IM_MARGIN_HI  = {float(IM_MARGIN_HI_mp):.3e}   {'PASS' if IM_MARGIN_HI_mp > 0 else 'FAIL'}")
    print()
    ok = RE_MARGIN_mp > 0 and IM_MARGIN_LO_mp > 0 and IM_MARGIN_HI_mp > 0
    print(f"OVERALL: {'PASS — proceed to STAGE 1 emit ONE segment' if ok else 'FAIL — diagnose before emitting'}")
    return ok

def stage1_segment_report():
    """Detailed per-node candidate bounds for Stage-1 segment [3/2, 25/16], n=23.
    Prints the exact rational data the Lean generator will emit."""
    L = Fraction(3, 2)
    U = Fraction(25, 16)
    n_j = 23
    h = (U - L) / n_j  # = 1/368
    L_mp = frac_to_mp(L)
    M_j_mp = M_segment(L_mp)
    # Choose rational M_SEG_HI slightly above M_j_mp
    M_SEG_HI = Fraction(3)  # numerical 2.493 < 3
    E_SEG = M_SEG_HI * (U - L)**3 / (24 * n_j**2)  # = M_SEG_HI / 17334272

    print("=" * 80)
    print(f"STAGE 1 SEGMENT REPORT — [{L}, {U}], n={n_j}")
    print("=" * 80)
    print(f"h = (U-L)/n = {h}")
    print(f"u_i = L + h·(i + 1/2) = (1105 + 2i)/736 for i = 0..22")
    print(f"M_j at L=3/2 (numerical): {float(M_j_mp)}")
    print(f"M_SEG_HI (rational, candidate for Lean cert): {M_SEG_HI}")
    print(f"E_SEG = M_SEG_HI · (U-L)³ / (24·n²)")
    print(f"      = {M_SEG_HI} · (1/16)³ / (24·23²)")
    print(f"      = {E_SEG}  (= {float(E_SEG):.3e})")
    print()

    seg_re_sum_lo = Fraction(0)
    seg_re_sum_hi = Fraction(0)
    seg_im_sum_lo = Fraction(0)
    seg_im_sum_hi = Fraction(0)
    print(f"{'i':>3} {'u_i':>10} {'sign_c':>6} {'sign_s':>6} "
          f"{'re_lo_i':>16} {'re_hi_i':>16} {'im_lo_i':>16} {'im_hi_i':>16}")
    for i in range(n_j):
        u_frac = L + h * (Fraction(i) + Fraction(1, 2))
        u_mp = frac_to_mp(u_frac)
        c = mp.cos(HALF_T15 * mp.log(u_mp))
        s = mp.sin(HALF_T15 * mp.log(u_mp))
        re_lo_mp, re_hi_mp = node_re_ideal_bounds(u_mp)
        im_lo_mp, im_hi_mp = node_im_ideal_bounds(u_mp)
        re_lo_frac = floor_toward_minus_inf(re_lo_mp)
        re_hi_frac = ceil_toward_plus_inf(re_hi_mp)
        im_lo_frac = floor_toward_minus_inf(im_lo_mp)
        im_hi_frac = ceil_toward_plus_inf(im_hi_mp)
        seg_re_sum_lo += re_lo_frac
        seg_re_sum_hi += re_hi_frac
        seg_im_sum_lo += im_lo_frac
        seg_im_sum_hi += im_hi_frac
        print(f"{i:>3} {str(u_frac):>10} {'-' if c<0 else '+':>6} {'-' if s<0 else '+':>6} "
              f"{float(re_lo_frac):>16.9e} {float(re_hi_frac):>16.9e} "
              f"{float(im_lo_frac):>16.9e} {float(im_hi_frac):>16.9e}")

    print()
    print(f"SEG_RE_SUM_LO (Σ re_lo_i)        = {float(seg_re_sum_lo):.12e}")
    print(f"SEG_RE_SUM_HI (Σ re_hi_i)        = {float(seg_re_sum_hi):.12e}")
    print(f"SEG_IM_SUM_LO (Σ im_lo_i)        = {float(seg_im_sum_lo):.12e}")
    print(f"SEG_IM_SUM_HI (Σ im_hi_i)        = {float(seg_im_sum_hi):.12e}")

    Q_RE_LO = h * seg_re_sum_lo
    Q_RE_HI = h * seg_re_sum_hi
    Q_IM_LO = h * seg_im_sum_lo
    Q_IM_HI = h * seg_im_sum_hi
    print(f"\nCandidate midpoint sums (h · Σ):")
    print(f"Q_RE_MID_LO = h · SEG_RE_SUM_LO  = {float(Q_RE_LO):.12e}")
    print(f"Q_RE_MID_HI = h · SEG_RE_SUM_HI  = {float(Q_RE_HI):.12e}")
    print(f"Q_IM_MID_LO = h · SEG_IM_SUM_LO  = {float(Q_IM_LO):.12e}")
    print(f"Q_IM_MID_HI = h · SEG_IM_SUM_HI  = {float(Q_IM_HI):.12e}")

    RE_INT_LO = Q_RE_LO - Fraction(int(E_SEG.numerator), int(E_SEG.denominator))
    RE_INT_HI = Q_RE_HI + Fraction(int(E_SEG.numerator), int(E_SEG.denominator))
    IM_INT_LO = Q_IM_LO - Fraction(int(E_SEG.numerator), int(E_SEG.denominator))
    IM_INT_HI = Q_IM_HI + Fraction(int(E_SEG.numerator), int(E_SEG.denominator))
    print(f"\nCandidate segment-integral enclosures:")
    print(f"RE_INT_LO = Q_RE_MID_LO - E_SEG  = {float(RE_INT_LO):.12e}")
    print(f"RE_INT_HI = Q_RE_MID_HI + E_SEG  = {float(RE_INT_HI):.12e}")
    print(f"IM_INT_LO = Q_IM_MID_LO - E_SEG  = {float(IM_INT_LO):.12e}")
    print(f"IM_INT_HI = Q_IM_MID_HI + E_SEG  = {float(IM_INT_HI):.12e}")
    print()
    print("→ These four rational bounds are what the Stage-1 Lean segment file")
    print("  must land as theorems `box0_seg1_re/im_integral_lower/upper`.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true", default=False)
    parser.add_argument("--stage1", action="store_true", default=False,
                        help="Report Stage-1 segment [3/2, 25/16] detail")
    parser.add_argument("--emit", action="store_true")
    args = parser.parse_args()
    if args.emit:
        print("--emit not yet implemented; run --dry-run + Lean Stage 1 first")
        sys.exit(1)
    if args.stage1:
        stage1_segment_report()
    elif args.dry_run or (not args.stage1 and not args.emit):
        success = dry_run()
        sys.exit(0 if success else 1)
