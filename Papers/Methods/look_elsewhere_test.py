#!/usr/bin/env python3
"""
Look-elsewhere test for Principia Fractalis empirical matches.

CORRECTED VERSION (2026-06-24). The prior revision of this script computed
per-observable null hit-rates p_i and ran a Poisson tail at lambda = sum(p_i),
yielding p ~ 1.58e-7 across the Table 2 observables. That model assumes
seven RANDOM-DART throws, one per observable. The actual procedure (and the
procedure a hostile referee re-running this script would use) is BEST-OF-N
SEARCH: enumerate ~100,000 expressions in the substrate's grammar, then
keep the closest one to each measurement.

The correct null is therefore: per observable, the probability that a
best-of-N search finds an expression within N sigma is 1 - (1 - p_i)^N,
which is essentially 1 whenever p_i * N >> 1. With per-observable
within-0.5-sigma counts in the hundreds to thousands, p_i * N >> 1 for
every observable in Table 2, so the correct lambda ~ 7 and Pr[K >= 6] ~ 1.

Read straight: the grammar is too dense for the retrodictions to be
evidential under any honest null. The empirical content of the substrate's
case lives in the chronologically pre-registered forward prediction
(alpha_GI = sqrt(2) to 1e-4), where the trials denominator is fixed in
advance, not in the retrodictive Table 2 matches.

This corrected script prints both:
  - per-observable single-throw rate p_i (the wrong statistic the prior
    revision used)
  - per-observable best-of-N rate q_i = 1 - (1 - p_i)^N (the correct
    statistic)
  - both Poisson tails, so the reader can see the difference

Verdict line at the end states the honest conclusion.
"""
import mpmath as mp
from math import factorial

mp.mp.dps = 30

PHI = (1 + mp.sqrt(5)) / 2

ATOMS = {
    "1": mp.mpf(1), "2": mp.mpf(2), "3": mp.mpf(3), "4": mp.mpf(4),
    "5": mp.mpf(5), "10": mp.mpf(10),
    "1/2": mp.mpf(1)/2, "1/3": mp.mpf(1)/3, "1/4": mp.mpf(1)/4,
    "3/4": mp.mpf(3)/4, "3/2": mp.mpf(3)/2, "5/4": mp.mpf(5)/4,
    "pi": mp.pi, "phi": PHI, "sqrt2": mp.sqrt(2), "sqrt5": mp.sqrt(5),
    "sqrt2pi": mp.sqrt(2 * mp.pi), "e": mp.e,
    "pi/10": mp.pi / 10, "c2": mp.mpf(19) / 20,
    "a_Poincare": mp.mpf(1),
    "a_RH": mp.mpf(3) / 2,
    "a_NP": PHI + mp.mpf(1)/4,
    "a_NS": mp.mpf(3) * mp.pi / 2,
    "a_YM": mp.mpf(2),
    "a_BSD": mp.mpf(3) * mp.pi / 4,
    "a_Hodge": PHI,
    "a_QG": mp.sqrt(2 * mp.pi),
    "a_P": mp.sqrt(2),
}

def is_finite_positive(x, lo=1e-6, hi=1e6):
    try:
        v = float(mp.mpf(x))
        return v > lo and v < hi and not mp.isnan(x) and not mp.isinf(x)
    except Exception:
        return False

def enumerate_expressions(max_ops=3):
    seen = {}
    for k, v in ATOMS.items():
        if is_finite_positive(v):
            key = round(float(mp.mpf(v)), 18)
            if key not in seen:
                seen[key] = (v, k)
    layer = list(seen.values())
    for _ in range(max_ops):
        new_layer = []
        for a_val, a_name in layer:
            for op_name, op in [
                ("sq", lambda x: x * x),
                ("sqrt", lambda x: mp.sqrt(x) if float(mp.mpf(x)) > 0 else None),
                ("inv", lambda x: 1 / x if float(mp.mpf(x)) != 0 else None),
                ("exp", lambda x: mp.exp(x) if abs(float(mp.mpf(x))) < 20 else None),
            ]:
                try:
                    r = op(a_val)
                    if r is None:
                        continue
                    if is_finite_positive(r):
                        key = round(float(mp.mpf(r)), 18)
                        if key not in seen:
                            seen[key] = (r, f"{op_name}({a_name})")
                            new_layer.append((r, f"{op_name}({a_name})"))
                except Exception:
                    pass
            for b_val, b_name in layer:
                for op_name, op in [
                    ("mul", lambda x, y: x * y),
                    ("div", lambda x, y: x / y if float(mp.mpf(y)) != 0 else None),
                ]:
                    try:
                        r = op(a_val, b_val)
                        if r is None:
                            continue
                        if is_finite_positive(r):
                            key = round(float(mp.mpf(r)), 18)
                            if key not in seen:
                                seen[key] = (r, f"{op_name}({a_name},{b_name})")
                                new_layer.append((r, f"{op_name}({a_name},{b_name})"))
                    except Exception:
                        pass
        layer.extend(new_layer)
        if not new_layer:
            break
    return seen


def main():
    # max_ops=2 is what the external critic ran (12,600 expressions, ~30s);
    # max_ops=3 reproduces the prior revision's ~100,000-expression scope but
    # runs >3 min; the corrected verdict is the same under both.
    MAX_OPS = 2
    print(f"Enumerating expressions over substrate grammar (atoms + <={MAX_OPS} ops)...")
    all_exprs = enumerate_expressions(max_ops=MAX_OPS)
    values = sorted([(float(mp.mpf(v)), n) for v, n in all_exprs.values()])
    print(f"Total distinct positive-real expressions (1e-6 < v < 1e6): {len(values)}")

    OBS = [
        (-0.838, 0.055, -float(mp.sqrt(2*mp.pi)/3), -3.0, 3.0, "w_0 (DESI)"),
        (0.32,   0.06,  float(mp.pi/(10*mp.sqrt(2))), 0.0, 1.0, "Li-7 deficit"),
        (0.769,  0.03,  float(0.834 * mp.sqrt(1 - (mp.pi/10) * mp.mpf(0.95) * mp.mpf(0.5))), 0.0, 1.5, "S_8 (HSC-Y3)"),
        (0.0298, 0.0008, float(mp.pi * mp.sqrt(2) / 150), 0.0, 0.2, "neutrino ratio"),
        (9.8,    0.45,  10.0, 0.0, 20.0, "GW low-mass BH peak"),
        (0.74,   0.13,  float(mp.sqrt(2) / (PHI + mp.mpf(1)/4)), 0.0, 2.0, "GW mass-ratio peak"),
        (3.2,    1.0,   float(mp.pi), 0.0, 6.0, "GW redshift index"),
    ]

    print()
    print(f"{'observable':<25} {'in-band':>8} {'<=0.5sig':>9} {'<=1sig':>9} {'<=2sig':>9} {'p_i (single)':>14} {'q_i (best-of-N)':>17} {'subst sig':>11}")
    print("-" * 110)

    single_throw_p_05 = []
    best_of_N_q_05 = []
    substrate_hit_05 = []

    for meas, sig, subst_val, lo, hi, label in OBS:
        in_band = [(v, n) for v, n in values if lo <= v <= hi]
        n_band = len(in_band)
        c05 = sum(1 for v, n in in_band if abs(v - meas) <= 0.5 * sig)
        c10 = sum(1 for v, n in in_band if abs(v - meas) <= 1.0 * sig)
        c20 = sum(1 for v, n in in_band if abs(v - meas) <= 2.0 * sig)
        subst_sig = abs(subst_val - meas) / sig
        p_i = c05 / n_band if n_band else 0
        if p_i > 0 and n_band > 0:
            q_i = 1.0 - (1.0 - p_i) ** n_band
        else:
            q_i = 0.0
        single_throw_p_05.append(p_i)
        best_of_N_q_05.append(q_i)
        substrate_hit_05.append(subst_sig <= 0.5)

        print(f"{label:<25} {n_band:>8d} {c05:>9d} {c10:>9d} {c20:>9d} {p_i:>14.5e} {q_i:>17.5f} {subst_sig:>11.3f}")

    print()
    print("Single-throw model (the WRONG one):")
    lam_single = sum(single_throw_p_05)
    K = sum(substrate_hit_05)
    p_poisson_single = sum(
        mp.exp(-lam_single) * (mp.mpf(lam_single) ** k) / factorial(k)
        for k in range(K, 100)
    )
    print(f"  lambda = sum(p_i) = {lam_single:.4f}")
    print(f"  K = {K} substrate hits within 0.5 sigma")
    print(f"  Pr[X >= K | lambda] = {float(p_poisson_single):.3e}")
    print("  (This is what the prior revision of this script reported as 'structure'.)")

    print()
    print("Best-of-N model (the CORRECT one):")
    lam_best = sum(best_of_N_q_05)
    p_poisson_best = sum(
        mp.exp(-lam_best) * (mp.mpf(lam_best) ** k) / factorial(k)
        for k in range(K, 100)
    )
    print(f"  lambda = sum(q_i) = {lam_best:.4f}")
    print(f"  K = {K} substrate hits within 0.5 sigma")
    print(f"  Pr[X >= K | lambda] = {float(p_poisson_best):.3e}")

    print()
    if float(p_poisson_best) > 0.1:
        print("VERDICT: The grammar is too dense for the Table 2 retrodictions to be")
        print(f"evidential. Under the correct best-of-N null, achieving K = {K} out of 7")
        print(f"hits within 0.5 sigma is essentially what noise produces (p ~ {float(p_poisson_best):.2f}).")
        print("The substrate's empirical case rests on the chronologically-pre-registered")
        print("forward prediction (alpha_GI = sqrt(2) to 1e-4), where the trials denominator")
        print("is fixed before the measurement and the multiple-comparisons problem does")
        print("not apply. The retrodiction table is descriptive context, not evidence.")
    else:
        print(f"VERDICT: p_best-of-N = {float(p_poisson_best):.3e}, evidential under the correct null.")


if __name__ == "__main__":
    main()
