#!/usr/bin/env python3
"""
Look-elsewhere test under the SUBSTRATE-NATURAL prior.

The prior `look_elsewhere_test.py` uses a uniform grammar of arbitrary atoms
(1/3, 5/4, sqrt5, e, ...) crossed with arbitrary operations (exp, sqrt, mul,
div) up to depth 2-3. That enumerates ~10^4-10^5 expressions, which makes
best-of-N null hit-rates ~ 1 trivially.

This script enumerates instead the substrate's NATURAL prior derived from
its algebraic structure:

  Primitives:
    - 9 alpha-values forced by 12 uniqueness invariants
    - universal coupling pi/10 (H_3 Coxeter number)
    - small substrate-counting integers {1, 2, 3, 4, 10}

  Substrate-natural operations (no free exp/sqrt/log on compound expressions):
    - alpha_i * alpha_j
    - alpha_i / alpha_j
    - alpha_i / n              (small-integer divisor)
    - n * alpha_i              (small-integer multiplier)
    - (pi/10) * alpha_i        (universal coupling on alpha)
    - (pi/10) / alpha_i        (universal coupling / alpha)
    - ((pi/10)/alpha_i) * ((pi/10)/alpha_j)  (composition of two coupling factors)
    - alpha_i^2, alpha_i^{-1}  (square or inverse)
    - sign flip (s -> -s)      (the substrate signs entries; the magnitude is what's
                                enumerated, signed copies enter the band counts)

  EXCLUDED:
    - Free atoms like 1/3, 5/4, sqrt5, e
    - exp(.) of compound; sqrt(.) of compound (sqrt(2 pi) is alpha_QG, not free op)
    - Anything not decomposable into the substrate primitives above

Run it. Report every number. Print a verdict line.
"""
import mpmath as mp
from math import factorial

mp.mp.dps = 40

PHI = (1 + mp.sqrt(5)) / 2

# 9 substrate-forced alpha-values (indices match the prompt)
ALPHAS = {
    "a_Poincare": mp.mpf(1),                # a_1
    "a_RH":       mp.mpf(3) / 2,            # a_2
    "a_NP":       PHI + mp.mpf(1) / 4,      # a_3 ... NOTE: prompt indexing differs
    "a_NS":       mp.mpf(3) * mp.pi / 2,    # a_4
    "a_YM":       mp.mpf(2),                # a_5
    "a_BSD":      mp.mpf(3) * mp.pi / 4,    # a_6
    "a_Hodge":    PHI,                      # a_7
    "a_QG":       mp.sqrt(2 * mp.pi),       # a_8
    "a_P":        mp.sqrt(2),               # a_9
}

# Universal coupling forced by H_3 Coxeter h(H_3) = 10
PI_OVER_10 = mp.pi / 10

# Small substrate-counting integers
SMALL_INTS = [mp.mpf(1), mp.mpf(2), mp.mpf(3), mp.mpf(4), mp.mpf(10)]
SMALL_INT_NAMES = ["1", "2", "3", "4", "10"]


def enumerate_substrate_natural():
    """
    Enumerate the substrate-natural expression set.
    Returns dict: rounded_value -> (mp.mpf value, name).
    Values are stored unsigned (positive). Sign is applied per-observable at match time.
    """
    seen = {}

    def add(val, name):
        try:
            v = mp.mpf(val)
            if mp.isnan(v) or mp.isinf(v):
                return
            f = float(v)
            if not (1e-8 < abs(f) < 1e8):
                return
            key = round(float(abs(v)), 15)
            if key not in seen:
                seen[key] = (abs(v), name)
        except Exception:
            pass

    alpha_names = list(ALPHAS.keys())
    alpha_vals = [ALPHAS[n] for n in alpha_names]

    # Layer 0: the alpha-values themselves
    for n, v in ALPHAS.items():
        add(v, n)

    # The universal coupling itself
    add(PI_OVER_10, "pi/10")

    # Small integers (substrate-counting, will mostly be filtered by lo=1e-8 but keep 1,2,3,4)
    # We include them only as operands, not standalone expressions (substrate doesn't
    # predict "0.3" as a bare integer ratio output)

    # Layer 1a: alpha_i^2 and alpha_i^{-1}
    for n, v in ALPHAS.items():
        add(v * v, f"({n})^2")
        add(1 / v, f"1/{n}")

    # Layer 1b: alpha_i * alpha_j and alpha_i / alpha_j  (i,j over 9 alphas)
    for i, ni in enumerate(alpha_names):
        for j, nj in enumerate(alpha_names):
            add(alpha_vals[i] * alpha_vals[j], f"{ni}*{nj}")
            add(alpha_vals[i] / alpha_vals[j], f"{ni}/{nj}")

    # Layer 1c: alpha_i / n  and  n * alpha_i  (n in {1,2,3,4,10})
    for i, ni in enumerate(alpha_names):
        for k, kn in zip(SMALL_INTS, SMALL_INT_NAMES):
            add(alpha_vals[i] / k, f"{ni}/{kn}")
            add(k * alpha_vals[i], f"{kn}*{ni}")
            add(alpha_vals[i] / (k * k), f"{ni}/{kn}^2")

    # Layer 1d: (pi/10) * alpha_i  and  (pi/10) / alpha_i
    for i, ni in enumerate(alpha_names):
        add(PI_OVER_10 * alpha_vals[i], f"(pi/10)*{ni}")
        add(PI_OVER_10 / alpha_vals[i], f"(pi/10)/{ni}")

    # Layer 2: composition of two coupling factors
    # ((pi/10)/alpha_i) * ((pi/10)/alpha_j) = pi^2 / (100 * alpha_i * alpha_j)
    for i, ni in enumerate(alpha_names):
        for j, nj in enumerate(alpha_names):
            add((PI_OVER_10 / alpha_vals[i]) * (PI_OVER_10 / alpha_vals[j]),
                f"(pi/10)/{ni} * (pi/10)/{nj}")
            # Mixed: (pi/10)*alpha_i / alpha_j and (pi/10)/alpha_i * alpha_j
            add((PI_OVER_10 * alpha_vals[i]) / alpha_vals[j],
                f"(pi/10)*{ni}/{nj}")
            add((PI_OVER_10 / alpha_vals[i]) * alpha_vals[j],
                f"(pi/10)*{nj}/{ni}")
            # ((pi/10)*alpha_i)*((pi/10)*alpha_j)
            add((PI_OVER_10 * alpha_vals[i]) * (PI_OVER_10 * alpha_vals[j]),
                f"(pi/10)*{ni} * (pi/10)*{nj}")

    # Layer 2b: small-integer modulation of coupling-factor expressions
    # n * (pi/10) / alpha_i ; (pi/10)/alpha_i / n
    for i, ni in enumerate(alpha_names):
        for k, kn in zip(SMALL_INTS, SMALL_INT_NAMES):
            add(k * PI_OVER_10 / alpha_vals[i], f"{kn}*(pi/10)/{ni}")
            add(PI_OVER_10 / alpha_vals[i] / k, f"(pi/10)/{ni}/{kn}")
            add(k * PI_OVER_10 * alpha_vals[i], f"{kn}*(pi/10)*{ni}")
            add(PI_OVER_10 * alpha_vals[i] / k, f"(pi/10)*{ni}/{kn}")
            # alpha_i / alpha_j / n is layer-1d after redefinition — skip duplicates

    # Layer 2c: pi alone (it appears as alpha_NS / (3/2) = pi, alpha_BSD * 4/3, etc.).
    # The substrate doesn't introduce pi as a free atom but it emerges from
    # alpha_NS / (3/2) = pi. Add it as a derived expression.
    add(mp.pi, "alpha_NS/(3/2)=pi")
    add(mp.pi * mp.pi, "pi^2")

    return seen


def main():
    print("=" * 78)
    print("Substrate-natural look-elsewhere test")
    print("=" * 78)
    print()
    print("Enumerating substrate-natural expressions...")
    exprs = enumerate_substrate_natural()
    n_total = len(exprs)
    values = sorted([(float(v), n) for v, n in exprs.values()])
    print(f"  |G_substrate| (distinct positive magnitudes): {n_total}")
    print()

    # Observables (per prompt). subst_pred is the substrate's actual Table-2 expression.
    OBS = [
        # (label, meas, sigma, lo_band, hi_band, subst_pred_value, subst_pred_name)
        ("w_0",
         mp.mpf("-0.838"), mp.mpf("0.055"),
         mp.mpf(-3), mp.mpf(3),
         -ALPHAS["a_QG"] / 3,
         "-a_QG/3"),
        ("Li-7 deficit",
         mp.mpf("0.32"), mp.mpf("0.06"),
         mp.mpf("0.0"), mp.mpf("1.5"),
         PI_OVER_10 / ALPHAS["a_P"],
         "(pi/10)/a_P"),
        ("neutrino mass ratio",
         mp.mpf("0.0298"), mp.mpf("0.0008"),
         mp.mpf("0.0"), mp.mpf("0.2"),
         (PI_OVER_10 / ALPHAS["a_P"]) * (PI_OVER_10 / ALPHAS["a_BSD"]),
         "(pi/10)/a_P * (pi/10)/a_BSD"),
        ("GW mass ratio",
         mp.mpf("0.74"), mp.mpf("0.13"),
         mp.mpf("0.0"), mp.mpf("2.0"),
         ALPHAS["a_P"] / ALPHAS["a_NP"],
         "a_P/a_NP"),
        ("GW redshift kappa",
         mp.mpf("3.2"), mp.mpf("1.0"),
         mp.mpf("0.0"), mp.mpf("6.0"),
         mp.pi,
         "pi"),
    ]

    # Per-observable counting. We compare |v - |meas|| <= n*sigma after applying the
    # appropriate sign matching the measurement (for negative meas, we use the negative
    # of the enumerated magnitude).
    print(f"{'observable':<22} {'|in-band|':>10} {'<=0.5s':>7} {'<=1s':>7} {'<=2s':>7} "
          f"{'subst sig':>10} {'in enum?':>9}")
    print("-" * 78)

    q_05 = []      # best-of-N rate at 0.5 sigma
    p_05_single = []
    K_05 = 0       # substrate-hit count at 0.5 sigma
    K_1  = 0
    substrate_hits_05 = []
    substrate_in_enum = []

    for label, meas, sig, lo, hi, sv, sname in OBS:
        # Build signed in-band set
        sgn = 1 if meas >= 0 else -1
        in_band = []
        for v, n in values:
            sv_signed = sgn * v
            if float(lo) <= sv_signed <= float(hi):
                in_band.append((sv_signed, n))
        n_band = len(in_band)

        meas_f = float(meas)
        sig_f = float(sig)
        c05 = sum(1 for v, n in in_band if abs(v - meas_f) <= 0.5 * sig_f)
        c10 = sum(1 for v, n in in_band if abs(v - meas_f) <= 1.0 * sig_f)
        c20 = sum(1 for v, n in in_band if abs(v - meas_f) <= 2.0 * sig_f)

        sv_f = float(sv)
        subst_sig = abs(sv_f - meas_f) / sig_f
        # Is substrate's prediction in the enumeration?
        key = round(float(abs(sv_f)), 15)
        in_enum = key in exprs

        # Single-throw vs best-of-N rates at 0.5 sigma
        # Single-throw: a uniformly-random expression has prob c05/n_band of landing within 0.5 sigma
        # Best-of-N: prob that AT LEAST ONE of the n_band attempts is within 0.5 sigma
        p_i = c05 / n_band if n_band > 0 else 0.0
        if n_band > 0 and p_i > 0:
            q_i = 1.0 - (1.0 - p_i) ** n_band
        else:
            q_i = 0.0
        p_05_single.append(p_i)
        q_05.append(q_i)
        hit_05 = subst_sig <= 0.5
        hit_10 = subst_sig <= 1.0
        substrate_hits_05.append(hit_05)
        if hit_05:
            K_05 += 1
        if hit_10:
            K_1 += 1
        substrate_in_enum.append(in_enum)

        print(f"{label:<22} {n_band:>10d} {c05:>7d} {c10:>7d} {c20:>7d} "
              f"{subst_sig:>10.3f} {'YES' if in_enum else 'no':>9}")

    print()
    print(f"Substrate Table-2 predictions and exact values:")
    for label, meas, sig, lo, hi, sv, sname in OBS:
        print(f"  {label:<22} pred={sname:<35} = {float(sv):+.6f}  meas={float(meas):+.6f} +/- {float(sig)}")

    print()
    print("=" * 78)
    print("Poisson tail under SUBSTRATE-NATURAL prior")
    print("=" * 78)

    # Single-throw (each observable = one random pick from |G|)
    lam_single = sum(p_05_single)
    p_poisson_single = sum(
        mp.exp(-lam_single) * (mp.mpf(lam_single) ** k) / factorial(k)
        for k in range(K_05, 200)
    )
    print(f"\nSingle-throw model (one random pick per observable):")
    print(f"  lambda = sum(p_i) = {lam_single:.6f}")
    print(f"  K = {K_05} substrate hits within 0.5 sigma (out of {len(OBS)})")
    print(f"  Pr[X >= K | lambda] = {float(p_poisson_single):.3e}")

    # Best-of-N (worst-case: re-search the whole enumeration per observable)
    lam_best = sum(q_05)
    p_poisson_best = sum(
        mp.exp(-lam_best) * (mp.mpf(lam_best) ** k) / factorial(k)
        for k in range(K_05, 200)
    )
    print(f"\nBest-of-N model (search all {n_total} expressions per observable):")
    print(f"  lambda = sum(q_i) = {lam_best:.6f}")
    print(f"  K = {K_05} substrate hits within 0.5 sigma (out of {len(OBS)})")
    print(f"  Pr[X >= K | lambda] = {float(p_poisson_best):.3e}")

    print(f"\nAt 1 sigma threshold:")
    print(f"  K = {K_1} substrate hits within 1 sigma (out of {len(OBS)})")
    p_i_1 = []
    q_i_1 = []
    for label, meas, sig, lo, hi, sv, sname in OBS:
        sgn = 1 if meas >= 0 else -1
        in_band = [(sgn * v, n) for v, n in values if float(lo) <= sgn * v <= float(hi)]
        nb = len(in_band)
        c = sum(1 for v, n in in_band if abs(v - float(meas)) <= float(sig))
        p = c / nb if nb else 0
        p_i_1.append(p)
        q_i_1.append(1 - (1 - p) ** nb if (nb and p) else 0)
    lam_1_best = sum(q_i_1)
    p_1_best = sum(
        mp.exp(-lam_1_best) * (mp.mpf(lam_1_best) ** k) / factorial(k)
        for k in range(K_1, 200)
    )
    print(f"  lambda(1sig, best-of-N) = {lam_1_best:.6f}")
    print(f"  Pr[X >= K | lambda(1sig)] = {float(p_1_best):.3e}")

    print()
    print("=" * 78)
    print("VERDICT")
    print("=" * 78)

    p_best = float(p_poisson_best)
    in_enum_count = sum(substrate_in_enum)
    print(f"|G_substrate| = {n_total}  (vs the uniform-grammar ~10^4 of look_elsewhere_test.py)")
    print(f"Substrate's Table-2 predictions present in enumeration: "
          f"{in_enum_count}/{len(OBS)}")
    print(f"K (0.5 sigma) = {K_05}/{len(OBS)};  K (1 sigma) = {K_1}/{len(OBS)}")
    print(f"lambda_substrate-natural (best-of-N, 0.5 sigma) = {lam_best:.4f}")
    print(f"Pr[K >= K_obs | lambda_substrate-natural] = {p_best:.3e}")
    print()
    if p_best < 0.01:
        print("VERDICT: STRUCTURE. Under the substrate's own structural prior, the")
        print(f"Table-2 matches are evidential at p = {p_best:.2e}. The substrate's")
        print("algebra is narrow enough that hitting K matches by best-of-N noise is")
        print("rare. The uniform-grammar null was defeating a strawman; the substrate-")
        print("natural prior gives the substrate the credit its algebra has earned.")
    elif p_best < 0.1:
        print(f"VERDICT: SUGGESTIVE. p = {p_best:.2e} is small but not airtight.")
        print("The substrate-natural enumeration is narrow enough that the matches")
        print("carry some signal, but the corpus-level case still rests on the")
        print("pre-registered forward prediction (alpha_GI = sqrt(2) to 1e-4).")
    else:
        print(f"VERDICT: NOISE. Even under the substrate's own natural prior, the")
        print(f"Table-2 retrodictions match at p = {p_best:.2e} — best-of-N over")
        print("the substrate-natural enumeration still reproduces the observed K.")
        print("The retrodiction table is not evidential; the substrate's empirical")
        print("case lives in the pre-registered forward prediction.")


if __name__ == "__main__":
    main()
