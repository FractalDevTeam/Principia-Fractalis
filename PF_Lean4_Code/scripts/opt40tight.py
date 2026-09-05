"""
OPT-40-TIGHT geometry — the frozen 40-macrosegment partition of [1, 5]
for r331b Box-0 Stage-2 mass production.  Read from R331B_PROGRESS.md
verbatim; segment indexing is 1..40 in the natural ordering.

Each entry: (index, L_num, L_den, U_num, U_den, n_panels, M_ceiling_num, M_ceiling_den).

The M_ceiling column is a LOOSE rational upper bound on the certified
segment M-value M(L) = 2·Σ_{n<3} thetaPowTermM 15 (25/32) (1425/1024) L n.
For Seg1 (L=3/2, M≈2.493) we use MHI=3.  For other segments, we set MHI
based on the reconnaissance M(a) column from R331B_PROGRESS.md, rounded
up to a simple rational with generous slack.

Sanity: total midpoint error = Σ MHI_j · (U-L_j)^3 / (24·n_j^2) should
match the reconnaissance ~1.78e-6.
"""
from fractions import Fraction as F

# (L, U, n, M_reference) from R331B_PROGRESS.md OPT-40-TIGHT table
# M_reference is the reconnaissance value at L; MHI is set below.
RAW = [
    # segment_idx, L (Fraction), U (Fraction), n, M_ref (float)
    (1,  F(1), F(33,32),   18, 12.00),
    (2,  F(33,32), F(17,16), 17, 10.87),
    (3,  F(17,16), F(35,32), 16, 9.856),
    (4,  F(35,32), F(9,8),  16, 8.934),
    (5,  F(9,8), F(37,32),  15, 8.099),
    (6,  F(37,32), F(19,16), 14, 7.341),
    (7,  F(19,16), F(39,32), 14, 6.655),
    (8,  F(39,32), F(5,4),  13, 6.032),
    (9,  F(5,4), F(41,32),  12, 5.468),
    (10, F(41,32), F(21,16), 12, 4.957),
    (11, F(21,16), F(43,32), 11, 4.493),
    (12, F(43,32), F(11,8), 11, 4.073),
    (13, F(11,8), F(45,32), 10, 3.692),
    (14, F(45,32), F(23,16), 10, 3.347),
    (15, F(23,16), F(47,32), 9,  3.034),
    (16, F(47,32), F(3,2),  9,  2.750),
    (17, F(3,2), F(25,16),  23, 2.493),   # ★ Seg1 = Stage-1 reference
    (18, F(25,16), F(13,8), 21, 2.049),
    (19, F(13,8), F(27,16), 19, 1.683),
    (20, F(27,16), F(7,4),  17, 1.383),
    (21, F(7,4), F(29,16),  16, 1.137),
    (22, F(29,16), F(15,8), 14, 0.934),
    (23, F(15,8), F(31,16), 13, 0.7675),
    (24, F(31,16), F(2),    12, 0.6307),
    (25, F(2), F(17,8),     30, 0.5183),
    (26, F(17,8), F(9,4),   24, 0.3499),
    (27, F(9,4), F(19,8),   20, 0.2363),
    (28, F(19,8), F(5,2),   17, 0.1596),
    (29, F(5,2), F(21,8),   14, 0.1077),
    (30, F(21,8), F(11,4),  11, 0.0728),
    (31, F(11,4), F(23,8),  9,  0.0491),
    (32, F(23,8), F(3),     8,  0.0332),
    (33, F(3), F(13,4),     18, 0.0224),
    (34, F(13,4), F(7,2),   12, 0.0102),
    (35, F(7,2), F(15,4),   8,  0.00466),
    (36, F(15,4), F(4),     6,  0.00212),
    (37, F(4), F(17,4),     4,  0.000968),
    (38, F(17,4), F(9,2),   3,  0.000441),
    (39, F(9,2), F(19,4),   2,  0.000201),
    (40, F(19,4), F(5),     2,  0.0000917),
]


def m_ceiling(m_ref: float) -> F:
    """Adaptive rational upper bound on M(L) with ~10% slack.

    Denominator is chosen by magnitude so the ceiling stays within ~10% of
    m_ref for all scales.  This keeps the summed E_j budget close to the
    reconnaissance ~1.78e-6 rather than bloating on small-M segments.
    """
    target = m_ref * 1.10
    if target >= 10:
        denom = 10          # ceiling to next 1/10 → ≤ 1% slack
    elif target >= 1:
        denom = 100         # 1/100
    elif target >= 0.1:
        denom = 1000
    elif target >= 0.01:
        denom = 10000
    elif target >= 0.001:
        denom = 100000
    elif target >= 0.0001:
        denom = 1000000
    else:
        denom = 10000000
    num = int(target * denom) + 1
    return F(num, denom)


# ---------------------------------------------------------------------------
# MHI corrections (r331b rework).
#
# m_ceiling() derives MHI from the float m_ref column.  For these 14 segments
# the result is BELOW the value emit_M_certificate can actually certify
# (2*(B0+B1+B2) > MHI), so the generator's own assertion fires and the segment
# cannot be emitted.  Each override is the certified bound rounded UP at 1e-9.
#
# Cost: E_QUAD 1.9613392867e-06 -> 1.9621020147e-06 (+7.627e-10).
# ---------------------------------------------------------------------------
MHI_OVERRIDE = {
    23: F(423000029, 500000000),
    24: F(694000027, 1000000000),
    25: F(143000003, 250000000),
    26: F(386000003, 1000000000),
    27: F(260000001, 1000000000),
    30: F(80200001, 1000000000),
    31: F(54200001, 1000000000),
    32: F(36600001, 1000000000),
    33: F(24800001, 1000000000),
    35: F(5140001, 1000000000),
    36: F(2340001, 1000000000),
    38: F(486001, 1000000000),
    39: F(222001, 1000000000),
    40: F(101001, 1000000000),
}


# Full production ledger: (idx, L, U, n, MHI, midpoint_step h, E_j)
SEGMENTS = []
for idx, L, U, n, m_ref in RAW:
    MHI = MHI_OVERRIDE.get(idx, m_ceiling(m_ref))
    delta = U - L
    h = delta / n
    E_j = MHI * (delta ** 3) / (24 * n * n)
    SEGMENTS.append({
        'idx': idx, 'L': L, 'U': U, 'n': n,
        'M_ref': m_ref, 'MHI': MHI,
        'delta': delta, 'h': h, 'E_j': E_j,
    })


def _self_test():
    total_E = sum(s['E_j'] for s in SEGMENTS)
    print(f"OPT-40-TIGHT: {len(SEGMENTS)} segments, [{SEGMENTS[0]['L']}, {SEGMENTS[-1]['U']}]")
    print(f"Total midpoint error (with MHI ceilings): {total_E} ≈ {float(total_E):.4e}")
    print(f"Reconnaissance target: ~1.78e-6")
    print()
    print(f"{'idx':>4} {'L':>10} {'U':>10} {'n':>4} {'MHI':>6} {'h':>12} {'E_j':>15}")
    for s in SEGMENTS:
        print(f"{s['idx']:>4} {str(s['L']):>10} {str(s['U']):>10} {s['n']:>4} "
              f"{str(s['MHI']):>6} {str(s['h']):>12} {float(s['E_j']):>15.4e}")


if __name__ == "__main__":
    _self_test()
