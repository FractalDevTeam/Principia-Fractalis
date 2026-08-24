#!/usr/bin/env python3
"""
gen_r120_panels_t15.py — kernel-verified panel-certificate generator for the
t = 15 specialization of the r120 certified theta-quadrature stack.

SCIENTIFIC ROLE
---------------
This script produces CANDIDATE rational lower bounds on the sums

    ∑_{i<k} nodeR15 (base + h·i)

that appear in the t = 15 mirror of PF/Analytic/XiPanels/*.  The emitted
values become premises of Lean theorems of the shape

    theorem sXXcYY : (L : ℝ) ≤ ∑ i ∈ Finset.range k, nodeR15 (base + h·i)

which are subsequently discharged inside Lean by the vendored interval engine
plus `decide +kernel`.

THIS SCRIPT IS NOT PART OF THE PROOF.  Every emitted L is a candidate whose
correctness is established solely by the Lean kernel via `Interval.approx_le`
against the interval mirror `nodeI15`.  If a value chosen here fails to
verify, it must be lowered and regenerated; it must NEVER be inserted as an
unchecked axiom.

ROUNDING POLICY
---------------
Working precision: mpmath dps = 100.
Emitted precision: 10 decimal digits.
Direction: every lower-bound certificate is truncated toward -∞
           (`mpmath.floor(x * 10**10) / 10**10`).
           For x > 0 this is truncate-toward-zero.
           For x < 0 this is truncate-away-from-zero.
           In BOTH cases the emitted decimal is ≤ x.

The 90-digit gap between working and emitted precision leaves ~10^80×
headroom above the interval engine's decimal-parse widening; if a panel
still fails to verify after re-generation, the true failure mode is either
- an under-refined partition (fewer nodes than the derivative bound
  requires), or
- an interval-engine widening blowup in a specific chunk (fix by
  splitting that chunk further).

PARTITION GEOMETRY
------------------
Identical to r120 (14 segments, 474 midpoint panels, 165 chunk-lower
bounds).  Not tunable here: any refinement must be reflected symmetrically
in the t = 15 assembly module.

OUTPUT
------
Writes to  PF/Analytic/XiPanelsT15/*.lean
- SegXX.lean   — 14 assembly files
- SegXXPY.lean — 63 subpanel files hosting the `decide +kernel` bricks
- ChunkTable_report.txt — deterministic audit trail with base/h/chunk/value

Deterministic: same mpmath version → same emitted values.

Usage:
    python3 gen_r120_panels_t15.py             # emit
    python3 gen_r120_panels_t15.py --dry-run   # print report only
"""
import mpmath as mp
import os
import sys
import argparse
from fractions import Fraction
from decimal import Decimal, localcontext

# ---------------------------------------------------------------------------
# Working precision
# ---------------------------------------------------------------------------
mp.mp.dps = 100

# t = 15 (integer).  cos((t/2)·log u) = cos(7.5·log u).
T15 = mp.mpf(15)
HALF_T15 = mp.mpf(15) / 2

def nodeR15(u):
    """nodeR at t = 15, matching XiOnLineZeroCoreT15.lean's definition:

        nodeR15 u := 2 · exp(log u · -0.75) · cos(7.5 · log u)
                     · (exp(-πu) + exp(-πu)^4 + exp(-πu)^9)

    Truncated theta integrand with N = 3, t = 15.
    """
    lu = mp.log(u)
    a = 2 * mp.exp(lu * mp.mpf('-0.75')) * mp.cos(HALF_T15 * lu)
    e = mp.exp(-(mp.pi * u))
    e4 = e**4
    e9 = e**9
    return a * (e + e4 + e9)

def floor10_int(x, digits=10):
    """Return floor(x * 10^digits) as an exact Python int.  Direction: toward -∞."""
    scale = mp.mpf(10) ** digits
    return int(mp.floor(x * scale))

def floor10(x, digits=10):
    """Truncate mpmath value to `digits` decimal digits, toward -∞."""
    return mp.mpf(floor10_int(x, digits)) / (mp.mpf(10) ** digits)

def fmt10(x):
    """Format `x` as an EXACT 10-fractional-digit decimal literal (floor toward -∞)."""
    n = floor10_int(x, 10)
    if n < 0:
        absn = -n
        int_part = absn // (10 ** 10)
        frac_part = absn % (10 ** 10)
        return f"-{int_part}.{frac_part:010d}"
    int_part = n // (10 ** 10)
    frac_part = n % (10 ** 10)
    return f"{int_part}.{frac_part:010d}"

def frac_to_lean_decimal(q):
    """Emit a Python Fraction as a terminating exact decimal literal.

    Requires q to be a terminating decimal (denominator of the form 2^a·5^b).
    Otherwise raises ValueError.
    """
    if q == 0:
        return "0"
    sign = '-' if q < 0 else ''
    q = abs(q)
    # For 2^a · 5^b denominators, find max(a, b) as decimal places.
    denom = q.denominator
    # Simplify: multiply denom to a power of 10 by matching factors of 2 and 5.
    from math import log2
    d = denom
    twos = 0
    while d % 2 == 0:
        d //= 2
        twos += 1
    fives = 0
    while d % 5 == 0:
        d //= 5
        fives += 1
    if d != 1:
        raise ValueError(f"non-terminating decimal for {q}")
    digits = max(twos, fives)
    scaled = q.numerator * (10 ** digits) // denom
    s = str(scaled).zfill(digits + 1)
    if digits == 0:
        return sign + s
    return sign + s[:-digits] + '.' + s[-digits:]

# ---------------------------------------------------------------------------
# Partition geometry (mirrors r120 exactly).  All values EXACT Fractions.
# ---------------------------------------------------------------------------
# Each entry: (seg_id, c, d, n_panels, [chunks_per_pfile])
def F(s):
    return Fraction(s)

SEGMENTS = [
    #  seg_id  c              d          n   subpanel-file layout  e0 (from XiOnLineZeroConstants; reused verbatim)
    ('01', F('1'),         F('1.0625'), 25, [4, 4, 1],             F('0.04321392')),
    ('02', F('1.0625'),    F('1.125'),  25, [4, 4, 1],             F('0.03550996')),
    ('03', F('1.125'),     F('1.1875'), 25, [4, 4, 1],             F('0.02917942')),
    ('04', F('1.1875'),    F('1.25'),   20, [4, 3],                F('0.02397746')),
    ('05', F('1.25'),      F('1.375'),  40, [4, 4, 4, 2],          F('0.01970288')),
    ('06', F('1.375'),     F('1.5'),    40, [4, 4, 4, 2],          F('0.01330401')),
    ('07', F('1.5'),       F('1.625'),  32, [4, 4, 3],             F('0.0089833')),
    ('08', F('1.625'),     F('1.75'),   25, [4, 4, 1],             F('0.00606581')),
    ('09', F('1.75'),      F('2'),      50, [4, 4, 4, 4, 1],       F('0.00409583')),
    ('10', F('2'),         F('2.25'),   40, [4, 4, 4, 2],          F('0.00186745')),
    ('11', F('2.25'),      F('2.5'),    32, [4, 4, 3],             F('0.00085144')),
    ('12', F('2.5'),       F('3'),      50, [4, 4, 4, 4, 1],       F('0.00038821')),
    ('13', F('3'),         F('4'),      50, [4, 4, 4, 4, 1],       F('0.0000807')),
    ('14', F('4'),         F('5'),      20, [4, 3],                F('0.00000349')),
]

def chunk_layout(n_panels):
    """Return list of chunk sizes: k of 3's and one leftover (size 1, 2, or 3).

    For n_panels % 3 == 0 → all chunks size 3.
    Otherwise: floor(n_panels/3) chunks of size 3, plus one leftover of
    size (n_panels % 3).
    """
    q, r = divmod(n_panels, 3)
    if r == 0:
        return [3] * q
    return [3] * q + [r]

def build_chunk_records(seg_id, c, d, n_panels):
    """Compute every chunk's (base, h, size, floor-10 sum).

    c, d are Fractions.  h = (d-c)/n_panels and u0 = c + h/2 are Fractions.
    Chunk bases stay in Fraction (exact) form; mpmath is used only for the
    transcendental evaluation.
    """
    h = Fraction(d - c, n_panels) if isinstance(d - c, int) else (d - c) / n_panels
    u0 = c + h / 2
    chunks = chunk_layout(n_panels)
    records = []
    cursor = 0
    for ci, size in enumerate(chunks, start=1):
        base = u0 + h * cursor
        # sum over `size` consecutive nodes.  Evaluate nodeR15 in mpmath
        # using base + h*j as an EXACT Fraction converted to mpf.
        s = mp.mpf(0)
        for j in range(size):
            arg = base + h * j
            # exact -> mpf via numerator/denominator division at working precision
            arg_mpf = mp.mpf(arg.numerator) / mp.mpf(arg.denominator)
            s = s + nodeR15(arg_mpf)
        # `sum_lo_int` is the CANONICAL representative: `sum_lo` = `sum_lo_int / 10^10`
        # as an exact rational.  `sum_lo_mpf` is the mpmath rendering, useful for
        # reconnaissance but subject to binary-encoding drift when re-floored — do
        # NOT re-derive `sum_lo_int` from `sum_lo_mpf`.
        #
        # SAFETY BACKOFF (−1 ULP): the tight floor `floor10(sum_hi)` can leave gaps
        # as narrow as ~10^-12 between the emitted rational and the true node sum.
        # The vendored Interval engine widens decimal literals by ≥ 10^-11 during
        # `approx_le`, which makes such tight bounds risk kernel-decide rejection.
        # We subtract 1 ULP of 10^-10 uniformly to guarantee ≥ 10^-10 headroom,
        # matching the r120-proven safety envelope.  Endpoint cost: 165 · 10^-10
        # spread across all chunks × per-seg `h·1e-10` scaling ≈ 10^-11 total,
        # vastly below the 1.38·10^-6 endpoint margin.
        sum_lo_int = floor10_int(s, 10) - 1
        records.append({
            'seg': seg_id,
            'idx': ci,
            'base': base,     # Fraction
            'h': h,           # Fraction
            'size': size,
            'sum_hi': s,                              # mpmath at working precision
            'sum_lo_int': sum_lo_int,                 # canonical integer form
            'sum_lo': mp.mpf(sum_lo_int) / (mp.mpf(10) ** 10),   # convenience
        })
        cursor += size
    return records, u0, h

# ---------------------------------------------------------------------------
# Full-segment integral lower bound (for int_lower_15 assembly)
# ---------------------------------------------------------------------------
def seg_lo_from_chunks(records):
    """
    Compute the seg-level panel-sum lower bound as the EXACT sum of chunk
    lower bounds.  Load-bearing: `linarith` inside `SegXX_15.lean` only
    has access to the per-chunk `sXXcYY : chunk_lo ≤ chunk_sum` bricks;
    it can only conclude that the seg-target is ≤ seg-sum if we set the
    seg-target to `Σ chunk_lo` EXACTLY.

    Uses `sum_lo_int` — the canonical integer form of each chunk's emitted
    rational — NOT `floor10_int(sum_hi)` (which can drift by ±1 ULP due to
    mpmath's binary rendering).

    Returns (true_sum_mpf, exact_seg_lo_Fraction).
    """
    true_sum = mp.mpf(0)
    lo_frac = Fraction(0)
    for r in records:
        true_sum = true_sum + r['sum_hi']
        lo_frac = lo_frac + Fraction(r['sum_lo_int'], 10 ** 10)
    return true_sum, lo_frac

# ---------------------------------------------------------------------------
# Per-segment mb (quadrature K-bound) and bnd (certified lower on ∫_c^d FT_15)
# ---------------------------------------------------------------------------
# At t = 15:
#   K0(15) ≤ 276.04, K1(15) ≤ 883.15, K2(15) ≤ 2684.56
#   sumK_15(c, e0) ≤ 276.04 · e0 + 0.00309    for c ≥ 1, exp(-π·c) ≤ e0
# See XiOnLineZeroT15.lean for the Lean proofs of these bounds.
K0_UPPER_15 = Fraction('276.04')
KTAIL_UPPER_15 = Fraction('0.00309')  # 883.15 · e^(-4π) + 2684.56 · e^(-9π) upper

def ceil_frac_to_decimal(q, digits):
    """Round Fraction q UP to `digits` decimal places (toward +∞)."""
    scale = 10 ** digits
    num = q.numerator * scale
    den = q.denominator
    n = -(-num // den)  # ceiling division
    return Fraction(n, scale)

def compute_seg_mb_bnd(c, d, n_panels, e0_frac, lo_frac):
    """
    Return (mb_frac, bnd_frac) as Fractions:
      mb  ≥ 276.04 · e0 + 0.00309   (rounded UP to 6 decimals — matches r120 style)
      bnd ≤ h · lo  − mb · (d − c)³ / (24 n²)   (rounded DOWN to 11 decimals)
    """
    h = Fraction(d - c, n_panels) if isinstance(d - c, int) else (d - c) / n_panels
    raw_mb = K0_UPPER_15 * e0_frac + KTAIL_UPPER_15
    mb = ceil_frac_to_decimal(raw_mb, 6)
    # bnd via exact rational, then floor to 11 decimals
    quad_err = mb * (d - c) ** 3 / (24 * n_panels ** 2)
    raw_bnd = h * lo_frac - quad_err
    # floor to 11 decimals — down toward -∞
    scale = 10 ** 11
    num = raw_bnd.numerator * scale
    den = raw_bnd.denominator
    n_bnd = num // den   # Python // rounds toward -∞
    bnd = Fraction(n_bnd, scale)
    return mb, bnd

def floor_mpf_to_frac(x_mpf, digits):
    """floor(x_mpf · 10^digits) / 10^digits as Python Fraction."""
    n = floor10_int(x_mpf, digits)
    return Fraction(n, 10 ** digits)

# ---------------------------------------------------------------------------
# Lean emitter
# ---------------------------------------------------------------------------
LEAN_HEADER = """/-
# PF.Analytic.XiPanelsT15.{name}

t = 15 mirror panel certificate — generated by
`scripts/gen_r120_panels_t15.py` (mpmath dps = 100, floor to 10 digits
toward -∞).

THIS FILE IS AUTO-GENERATED.  Regenerate via:
    python3 PF_Lean4_Code/scripts/gen_r120_panels_t15.py

Every numerical value is a CANDIDATE lower bound; the Lean kernel proves
each via `Interval.approx_le` + `decide +kernel` against `nodeI15`.
-/
"""

def fmt_num(q):
    """Lean-safe exact-decimal literal for a Python Fraction with terminating expansion."""
    return frac_to_lean_decimal(q)

def emit_subpanel_file(records, path):
    """Emit a SegXXPY.lean file with `decide +kernel` bricks for each chunk."""
    seg = records[0]['seg']
    py_name = os.path.basename(path).replace('.lean', '')
    body = LEAN_HEADER.format(name=py_name)
    body += "import PF.Analytic.XiOnLineZeroCoreT15\n"
    body += "namespace PrincipiaTractalis.XiPanelsT15\n"
    body += "open PrincipiaTractalis.XiOnLineZeroCoreT15\n"
    body += "open scoped Real\n"
    body += "set_option maxRecDepth 4000000\n\n"
    for r in records:
        seg_id, idx, base, h, size = r['seg'], r['idx'], r['base'], r['h'], r['size']
        # Use CANONICAL integer form for the emitted rational: sum_lo_int / 10^10
        L = frac_to_lean_decimal(Fraction(r['sum_lo_int'], 10 ** 10))
        base_s = fmt_num(base)
        h_s = fmt_num(h)
        body += (
            f"theorem s{seg_id}c{idx:02d} : ({L} : ℝ)\n"
            f"    ≤ ∑ i ∈ Finset.range {size}, nodeR15 ({base_s} + {h_s} * (i : ℕ)) := by\n"
            f"  refine _root_.Interval.approx_le (({L} : _root_.Interval))\n"
            f"    (nodeFold15 {size} ({base_s} : _root_.Interval) ({h_s} : _root_.Interval))\n"
            f"    ({L} : ℝ) (∑ i ∈ Finset.range {size}, nodeR15 ({base_s} + {h_s} * (i : ℕ)))\n"
            f"    (by approx) (nodeFold15_mem {size} {base_s} {h_s} _ _ (by approx) (by approx)) ?_\n"
            f"  decide +kernel\n\n"
        )
    body += "end PrincipiaTractalis.XiPanelsT15\n"
    with open(path, 'w') as f:
        f.write(body)

def emit_seg_assembly(seg_id, u0, h, n_panels, num_chunks, seg_L_frac, sub_names, path):
    """Emit a SegXX.lean file that assembles chunk bounds into the panel-sum
    lower bound `seg{seg_id}_15`."""
    body = LEAN_HEADER.format(name=f"Seg{seg_id}")
    for sub in sub_names:
        body += f"import PF.Analytic.XiPanelsT15.{sub}\n"
    body += "namespace PrincipiaTractalis.XiPanelsT15\n"
    body += "open PrincipiaTractalis.XiOnLineZeroCoreT15\n"
    body += "open scoped Real\n\n"
    u0_s = fmt_num(u0)
    h_s = fmt_num(h)
    # emit seg_L as exact 10-fractional-digit decimal (fits: seg_L is Σ n_k / 10^10)
    L_s = frac_to_lean_decimal(seg_L_frac)
    c_disp = fmt_num(u0 - h / 2)
    d_disp = fmt_num(u0 - h / 2 + h * n_panels)
    body += (
        f"/-- t = 15 panel-sum lower bound for segment {seg_id}: `[{c_disp}, "
        f"{d_disp}]`, `n = {n_panels}`. -/\n"
        f"theorem seg{seg_id}_15 : ({L_s} : ℝ)\n"
        f"    ≤ ∑ i ∈ Finset.range {n_panels}, nodeR15 ({u0_s} + {h_s} * (i : ℕ)) := by\n"
    )
    # produce nodeSum15_split hypotheses, one per interior boundary
    # split pattern: peel off 3 at a time until leftover
    q, r = divmod(n_panels, 3)
    # boundaries at positions 3, 6, ..., 3q  (relative to start)
    cursor = 0
    hi_lines = []
    hyps = []
    remaining = n_panels
    split_idx = 0
    # We produce: for k=1..num_splits, nodeSum15_split 3 (n_panels - 3k) (n_panels - 3(k-1))
    #   split boundary at u_boundary = u0 + h * 3k (relative to previous cursor)
    # Actually the r120 pattern is:
    #   h1 splits [0..n) into [0..3) + [3..n) using nodeSum_split 3 (n-3) n u0 h u_next
    # But the way r120 emits it: nodeSum_split 3 22 25 (1.00125) 0.0025 1.00875
    # meaning n1=3, n2=22, m=25, first-arg-of-split-3 nodes at u0=1.00125,
    # remaining 22 at v = u0 + h*3 = 1.00875.
    # The theorem: sum_25(1.00125) = sum_3(1.00125) + sum_22(1.00875)
    # Then h2: nodeSum_split 3 19 22 (1.00875) 0.0025 1.01625, giving
    #   sum_22(1.00875) = sum_3(1.00875) + sum_19(1.01625)
    # ...continued until sum_{leftover} at u0 + h*3*(num_splits)
    # Number of splits = q if leftover r > 0, else q - 1
    num_splits = q if r > 0 else max(q - 1, 0)
    for k in range(1, num_splits + 1):
        # remaining nodes before split k
        m_before = n_panels - 3 * (k - 1)
        m_after = m_before - 3  # after peeling 3
        u_prev = u0 + h * 3 * (k - 1)
        u_next = u_prev + h * 3
        u_prev_s = fmt_num(u_prev)
        u_next_s = fmt_num(u_next)
        body += (
            f"  have h{k} := nodeSum15_split 3 {m_after} {m_before} "
            f"({u_prev_s} : ℝ) {h_s} {u_next_s} "
            f"(by norm_num) (by norm_num)\n"
        )
    # linarith with all sXXcYY and all hi
    chunk_refs = ', '.join([f"s{seg_id}c{ci:02d}" for ci in range(1, num_chunks + 1)])
    h_refs = ', '.join([f"h{k}" for k in range(1, num_splits + 1)])
    if h_refs:
        body += f"  linarith [{chunk_refs}, {h_refs}]\n"
    else:
        body += f"  linarith [{chunk_refs}]\n"
    body += "\nend PrincipiaTractalis.XiPanelsT15\n"
    with open(path, 'w') as f:
        f.write(body)

# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------
def main():
    p = argparse.ArgumentParser()
    p.add_argument('--dry-run', action='store_true')
    p.add_argument('--out-dir', default=None)
    p.add_argument('--report', default=None)
    args = p.parse_args()

    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_lean_dir = os.path.abspath(os.path.join(script_dir, '..', 'PF', 'Analytic'))
    out_dir = args.out_dir or os.path.join(repo_lean_dir, 'XiPanelsT15')
    report_path = args.report or os.path.join(script_dir, 'ChunkTable_t15_report.txt')

    if not args.dry_run:
        os.makedirs(out_dir, exist_ok=True)

    total_chunks = 0
    report_lines = [
        "gen_r120_panels_t15.py deterministic audit trail",
        f"mpmath dps = {mp.mp.dps}",
        "emitted precision: 10 decimal digits, floor toward -∞",
        "",
        f"{'seg':<4} {'chunk':<6} {'base':<28} {'h':<20} {'size':<5} "
        f"{'sum (60d)':<32} {'floor10 (emitted)':<20}",
    ]

    seg_summaries = []  # collected for int_lower_15 authoring snippet
    for seg_id, c, d, n_panels, py_chunks, e0_frac in SEGMENTS:
        records, u0, h = build_chunk_records(seg_id, c, d, n_panels)
        # sanity: chunks fit exactly into n_panels
        assert sum(r['size'] for r in records) == n_panels
        # emit subpanel files
        cursor = 0
        sub_names = []
        for pi, pcount in enumerate(py_chunks, start=1):
            slab = records[cursor:cursor + pcount]
            sub_name = f"Seg{seg_id}P{pi}"
            sub_names.append(sub_name)
            path = os.path.join(out_dir, sub_name + '.lean')
            if not args.dry_run:
                emit_subpanel_file(slab, path)
            cursor += pcount
        assert cursor == len(records)
        # emit seg assembly with EXACT Σ chunk_lo as seg-target
        seg_sum, seg_lo_frac = seg_lo_from_chunks(records)
        seg_L = mp.mpf(seg_lo_frac.numerator) / mp.mpf(seg_lo_frac.denominator)
        seg_path = os.path.join(out_dir, f'Seg{seg_id}.lean')
        if not args.dry_run:
            emit_seg_assembly(seg_id, u0, h, n_panels, len(records),
                              seg_lo_frac, sub_names, seg_path)
        # audit report
        for r in records:
            report_lines.append(
                f"{r['seg']:<4} c{r['idx']:02d}   "
                f"{fmt_num(r['base']):<28} "
                f"{fmt_num(r['h']):<20} "
                f"{r['size']:<5} "
                f"{mp.nstr(r['sum_hi'], 30):<32} "
                f"{fmt10(r['sum_lo']):<20}"
            )
        report_lines.append(
            f"  seg{seg_id}_15 target = {fmt10(seg_L)} "
            f"(actual = {mp.nstr(seg_sum, 30)})"
        )
        # mb + bnd for int_lower_15 assembly (use exact chunk-sum lo, matching Seg assembly)
        lo_frac = seg_lo_frac
        mb, bnd = compute_seg_mb_bnd(c, d, n_panels, e0_frac, lo_frac)
        seg_summaries.append({
            'seg': seg_id, 'c': c, 'd': d, 'u0': u0, 'h': h, 'n': n_panels,
            'e0': e0_frac, 'lo': lo_frac, 'mb': mb, 'bnd': bnd,
        })
        total_chunks += len(records)

    report_lines.insert(3, f"total chunks: {total_chunks}")
    report_lines.insert(4, "")

    # ----- integrated int_lower_15 assembly report -----
    report_lines.append("")
    report_lines.append("========================================================")
    report_lines.append(" int_lower_15 authoring inputs (paste into XiOnLineZeroT15.lean)")
    report_lines.append("========================================================")
    total_bnd = Fraction(0)
    for s in seg_summaries:
        report_lines.append(
            f"  seg{s['seg']}: c={frac_to_lean_decimal(s['c'])}, "
            f"d={frac_to_lean_decimal(s['d'])}, "
            f"u0={frac_to_lean_decimal(s['u0'])}, "
            f"h={frac_to_lean_decimal(s['h'])}, "
            f"n={s['n']}, "
            f"e0={frac_to_lean_decimal(s['e0'])}, "
            f"lo={frac_to_lean_decimal(s['lo'])}, "
            f"mb={frac_to_lean_decimal(s['mb'])}, "
            f"bnd={frac_to_lean_decimal(s['bnd'])}"
        )
        total_bnd += s['bnd']
    # floor total_bnd to 10 digits — this is the achievable int_lower_15 target
    scale = 10 ** 10
    n_tot = total_bnd.numerator * scale // total_bnd.denominator
    int_lower_target = Fraction(n_tot, scale)
    report_lines.append("")
    report_lines.append(
        f"  Σ bnd (exact) = {total_bnd} = {frac_to_lean_decimal(total_bnd)}"
    )
    report_lines.append(
        f"  int_lower_15 achievable target (floor 10 digits): "
        f"{frac_to_lean_decimal(int_lower_target)}"
    )
    # sanity check against the endpoint threshold 4441/10^6
    threshold = Fraction(4441, 10 ** 6)
    delta = int_lower_target - threshold
    report_lines.append(
        f"  vs endpoint threshold 4441/10^6 = {frac_to_lean_decimal(threshold)}: "
        f"achievable − threshold = {frac_to_lean_decimal(delta)} "
        f"({'PASSES' if delta >= 0 else 'FAILS'})"
    )
    # exact rational endpoint certificate
    pole = Fraction(4, 901)
    tail = Fraction(11, 10 ** 8)
    xi15_lower = int_lower_target - pole - tail
    report_lines.append(
        f"  Xi_15 exact rational lower bound = int_lower_15 − 4/901 − 11/10^8 = "
        f"{xi15_lower.numerator}/{xi15_lower.denominator}  "
        f"≈ {float(xi15_lower):.4e}  ({'POSITIVE ✓' if xi15_lower > 0 else 'NEGATIVE ✗'})"
    )
    if not args.dry_run:
        with open(report_path, 'w') as f:
            f.write('\n'.join(report_lines) + '\n')
        print(f"Wrote {total_chunks} chunk certificates across "
              f"{len(SEGMENTS)} segments to {out_dir}")
        print(f"Audit trail: {report_path}")
    else:
        print('\n'.join(report_lines))

if __name__ == '__main__':
    main()
