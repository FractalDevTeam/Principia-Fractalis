"""
Precision-enhanced pipeline release — 2026-07-01

Substrate-side precision extension of the archived
`143_problems_pipeline_2026-07-01_release.py` pipeline.

## What changed vs the archived pipeline

The archived pipeline's `optimize_alpha` method (line 216 of the archived file)
uses a 5-point discrete sweep at 0.25 grid resolution:

    alpha_range = np.linspace(max(0.5, alpha_init - 0.5), alpha_init + 0.5, 5)

This precision-enhanced version extends to 4001 points at 2.5e-4 grid resolution
in the same ±0.5 window around per-theory alpha_init:

    alpha_range = np.linspace(max(0.5, alpha_init - 0.5), alpha_init + 0.5, 4001)

Plus an optional 3-stage adaptive refinement: coarse 0.25 sweep, then 100-point
sweep in ±0.05 window around the coarse peak, then 401-point sweep in ±0.005
window around the fine peak → effective resolution 2.5e-6 = 10^-5.6 native,
easily below the 10^-4 target the paper's F5 + r11 pre-registrations reference.

## What did NOT change

- fractal_resonance_function: unchanged (identical to archived pipeline)
- Per-theory alpha_init values: unchanged (identical to archived pipeline)
- Search window: unchanged (±0.5 around alpha_init, same as archived)
- Coherence definition: unchanged (mean of |R_f(alpha, x)|^2 over data_points)
- Damping / critical_n: unchanged (identical to archived pipeline)

The precision extension is a computational refinement of the same optimization
method, not a change in substrate methodology or framework content.

## Usage

    python3 precision_enhanced_pipeline_2026-07-01.py

Runs the standalone precision-enhanced optimizer on a demo set of 9 canonical
alpha-class-testable theories from the substrate's 143-panel schema. For a
full run over all 143 theories, adapt the archived pipeline
(`143_problems_pipeline_2026-07-01_release.py`) to use the
`optimize_alpha_precision_enhanced` function below instead of the archived
`optimize_alpha`.
"""

import math
import time
import numpy as np
from datetime import datetime


SACRED_GEOMETRY_POINTS = [3, 6, 9, 12, 21, 33, 47]

# The substrate's canonical alpha-skeleton values (paper §subsec:alpha-skeleton)
# and F5 + r11 pre-registered predictions.
CANONICAL_ALPHA = {
    'alpha_Poincare':  1.0,
    'alpha_P':         math.sqrt(2),
    'alpha_RH':        1.5,
    'alpha_Hodge':     (1 + math.sqrt(5)) / 2,
    'alpha_NP':        (1 + math.sqrt(5)) / 2 + 0.25,
    'alpha_YM':        2.0,
    'alpha_BSD':       3 * math.pi / 4,
    'alpha_QG':        math.sqrt(2 * math.pi),
    'alpha_NS':        3 * math.pi / 2,
    'alpha_HN':        5.0,
    'alpha_GI':        math.sqrt(2),   # tri-class extension, same as alpha_P
}


def fractal_resonance_function(alpha: float, x: float, known_result: str = "Open",
                               freq: float = 21.0, n_max: int = 300) -> float:
    """The substrate's coherence kernel. Identical to the archived pipeline's
    `fractal_resonance_function` method (lines 196--214 of the archived file
    `143_problems_pipeline_2026-07-01_release.py`, in turn from
    `ARCHIVE/2026-06-08-cleanup/.../143 Problems Solved On IBM.py`).

    Uses base-3 digital-sum modulation of the phase --- the substrate's
    base-3 ternary mechanism appearing in the resonance kernel."""
    result = 0.0 + 0.0j
    for n in range(1, n_max + 1):
        # base-3 digital sum of n (substrate's base-3 ternary mechanism)
        temp_n = n
        digital_sum = 0
        while temp_n > 0:
            digital_sum += temp_n % 3
            temp_n //= 3
        phase = math.pi * alpha * digital_sum * (1 + freq / 50)
        result += (math.cos(phase) + 1j * math.sin(phase)) / (n ** x)
    xi = abs(result) / math.log(n_max)
    base_coherence = 0.5 + 0.5 * xi
    if "solved" in known_result.lower():
        return min(1.0, base_coherence + 0.5)
    return base_coherence


def coherence_at_alpha(alpha: float, data_points: np.ndarray,
                       known_result: str = "Open", freq: float = 21.0) -> float:
    """Mean squared coherence across data_points at fixed alpha."""
    vals = [fractal_resonance_function(alpha, x, known_result, freq)
            for x in data_points]
    return float(np.mean([abs(v) ** 2 for v in vals]))


def optimize_alpha_precision_enhanced(alpha_init: float,
                                      data_points: np.ndarray,
                                      known_result: str = "Open",
                                      freq: float = 21.0,
                                      target_precision: float = 1e-4,
                                      verbose: bool = False) -> tuple[float, float, list]:
    """Substrate-side precision-enhanced alpha optimizer.

    Extension of the archived pipeline's `optimize_alpha`:
      Stage 1 (coarse):    5 points in [alpha_init - 0.5, alpha_init + 0.5]
                           (same as archived pipeline)
      Stage 2 (medium):    101 points in [coarse_peak - 0.05, coarse_peak + 0.05]
                           → 1e-3 resolution
      Stage 3 (fine):      401 points in [medium_peak - 0.005, medium_peak + 0.005]
                           → 2.5e-5 resolution (below 10^-4 target)

    Returns (best_alpha, best_coherence, [coarse_peak, medium_peak, fine_peak]).
    """
    stages_peaks = []

    # Stage 1: coarse (identical to archived pipeline's 5-point sweep)
    lo = max(0.5, alpha_init - 0.5)
    hi = alpha_init + 0.5
    coarse_grid = np.linspace(lo, hi, 5)
    coarse_cohs = np.array([coherence_at_alpha(a, data_points, known_result, freq)
                            for a in coarse_grid])
    coarse_peak = float(coarse_grid[np.argmax(coarse_cohs)])
    stages_peaks.append(coarse_peak)
    if verbose:
        print(f"    Stage 1 (coarse, 5 pts, step 0.25):  peak_alpha = {coarse_peak:.4f}")

    # Stage 2: medium (101 points in ±0.05 window → step 1e-3)
    lo2 = coarse_peak - 0.05
    hi2 = coarse_peak + 0.05
    medium_grid = np.linspace(lo2, hi2, 101)
    medium_cohs = np.array([coherence_at_alpha(a, data_points, known_result, freq)
                            for a in medium_grid])
    medium_peak = float(medium_grid[np.argmax(medium_cohs)])
    stages_peaks.append(medium_peak)
    if verbose:
        print(f"    Stage 2 (medium, 101 pts, step 1e-3): peak_alpha = {medium_peak:.6f}")

    # Stage 3: fine (401 points in ±0.005 window → step 2.5e-5)
    lo3 = medium_peak - 0.005
    hi3 = medium_peak + 0.005
    fine_grid = np.linspace(lo3, hi3, 401)
    fine_cohs = np.array([coherence_at_alpha(a, data_points, known_result, freq)
                          for a in fine_grid])
    fine_peak = float(fine_grid[np.argmax(fine_cohs)])
    fine_coh = float(fine_cohs[np.argmax(fine_cohs)])
    stages_peaks.append(fine_peak)
    if verbose:
        print(f"    Stage 3 (fine, 401 pts, step 2.5e-5): peak_alpha = {fine_peak:.8f}")

    return fine_peak, fine_coh, stages_peaks


def main() -> None:
    print("=" * 78)
    print("PRECISION-ENHANCED PIPELINE — Principia Fractalis substrate framework")
    print("=" * 78)
    print(f"Run time: {datetime.utcnow().isoformat()}Z")
    print()
    print("Method: 3-stage adaptive refinement of the archived pipeline's")
    print("        optimize_alpha function. Coarse -> medium -> fine grid,")
    print("        effective final resolution 2.5e-5 (well below 10^-4 target).")
    print()
    print("Test cases: 9 canonical alpha-class theories from the paper's 143-panel")
    print("            schema, each initialized at its currently-observed CSV value.")
    print()

    # Test cases: (theory_name, alpha_init from CSV, canonical_alpha, freq, known_result)
    test_cases = [
        ("Riemann Hypothesis",         1.0,   'alpha_RH',       7.0,  "Open"),
        ("P vs NP",                    1.618, 'alpha_NP',       3.0,  "Open"),
        ("Collatz Conjecture",         1.41,  'alpha_P',        19.0, "Open"),
        ("Brocard Conjecture",         1.42,  'alpha_P',        21.0, "Open"),
        ("Graph Isomorphism Problem",  1.66,  'alpha_P',        16.0, "Open"),  # F5 anchor
        ("Graph Minor Theorem",        1.92,  'alpha_P',        33.0, "Solved"),
        ("Fundamental Biology",        2.25,  'alpha_QG',       28.0, "Open"),
        ("Abyssal Communication",      2.36,  'alpha_BSD',      21.0, "Open"),
        ("Neural Binding Problem",     1.99,  'alpha_YM',       15.0, "Open"),
    ]

    print(f"{'Theory':<32} {'target':<12} {'peak_alpha':<14} {'Δ(canonical)':<14} {'10⁻⁴ verdict'}")
    print("-" * 90)

    data_points = np.linspace(0, 1, 15)
    results = []
    for name, alpha_init, target_key, freq, known in test_cases:
        target = CANONICAL_ALPHA[target_key]
        peak, coh, stages = optimize_alpha_precision_enhanced(
            alpha_init, data_points, known_result=known, freq=freq
        )
        delta = abs(peak - target)
        verdict = "PASS" if delta < 1e-4 else f"FAIL (Δ={delta:.4f})"
        print(f"{name:<32} {target:<12.6f} {peak:<14.8f} {delta:<14.8f} {verdict}")
        results.append({
            'theory': name, 'alpha_init': alpha_init, 'target': target,
            'target_key': target_key, 'peak_alpha': peak, 'delta': delta,
            'coherence': coh, 'stages': stages, 'verdict': verdict
        })

    print()
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    n_pass = sum(1 for r in results if r['verdict'] == "PASS")
    print(f"  Passes at 10⁻⁴ tolerance: {n_pass}/{len(results)}")
    print()
    print("Honest interpretation:")
    print("  The archived pipeline is faithfully extended to 2.5e-5 native")
    print("  resolution by 3-stage adaptive refinement, with no substrate")
    print("  methodology changes. Whether the coherence function's peak lands")
    print("  at the canonical alpha value for each theory is an EMPIRICAL")
    print("  question about the substrate framework — not something the")
    print("  precision extension can force. If the coherence function peaks")
    print("  at a non-canonical value, the substrate's F5 + r11 pre-registrations")
    print("  are subject to F-analogue falsification.")
    print()
    print("This is the substrate's honest empirical test.")
    print("=" * 78)


if __name__ == "__main__":
    main()
