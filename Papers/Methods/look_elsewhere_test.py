#!/usr/bin/env python3
"""
Look-elsewhere test for Principia Fractalis empirical matches.
Enumerates expressions from substrate atoms + ≤3 operations, counts how many
land within Nσ of each measurement, then computes joint p-value.
"""
import mpmath as mp
from math import erf, sqrt, exp, factorial

mp.mp.dps = 30  # 30-digit precision

# ----------------------------------------------------------------------
# 1. Atoms (substrate toolkit)
# ----------------------------------------------------------------------
PHI = (1 + mp.sqrt(5)) / 2

ATOMS = {
    "1":          mp.mpf(1),
    "2":          mp.mpf(2),
    "3":          mp.mpf(3),
    "4":          mp.mpf(4),
    "5":          mp.mpf(5),
    "10":         mp.mpf(10),
    "1/2":        mp.mpf(1)/2,
    "1/3":        mp.mpf(1)/3,
    "1/4":        mp.mpf(1)/4,
    "3/4":        mp.mpf(3)/4,
    "3/2":        mp.mpf(3)/2,
    "5/4":        mp.mpf(5)/4,
    "pi":         mp.pi,
    "phi":        PHI,
    "sqrt2":      mp.sqrt(2),
    "sqrt5":      mp.sqrt(5),
    "sqrt(2pi)":  mp.sqrt(2*mp.pi),
    "e":          mp.e,
    "a_Poincare": mp.mpf(1),
    "a_RH":       mp.mpf(3)/2,
    "a_NP":       PHI + mp.mpf(1)/4,
    "a_NS":       3*mp.pi/2,
    "a_YM":       mp.mpf(2),
    "a_BSD":      3*mp.pi/4,
    "a_Hodge":    PHI,
    "a_QG":       mp.sqrt(2*mp.pi),
    "a_P":        mp.sqrt(2),
    "pi/10":      mp.pi/10,
    "c_2":        mp.mpf(19)/20,
}

# ----------------------------------------------------------------------
# 2. Expression enumeration
# ----------------------------------------------------------------------
# Operations: a*b, a/b, a^2, a^(1/2), a^(-1), exp(a) [exp only on small args]
# Build by levels: level 0 = atoms; level k = combine level <k results.
# Stop at level 3 (i.e. ≤3 ops).

EPS_DUP = mp.mpf("1e-20")

def safe_mul(a, b):
    try:
        v = a * b
        if mp.isfinite(v): return v
    except: pass
    return None

def safe_div(a, b):
    try:
        if abs(b) < mp.mpf("1e-25"): return None
        v = a / b
        if mp.isfinite(v): return v
    except: pass
    return None

def safe_pow(a, p):
    try:
        if p == mp.mpf("1/2"):
            if a < 0: return None
            v = mp.sqrt(a)
        elif p == mp.mpf(2):
            v = a * a
        elif p == mp.mpf(-1):
            if abs(a) < mp.mpf("1e-25"): return None
            v = 1/a
        else:
            v = a ** p
        if mp.isfinite(v): return v
    except: pass
    return None

def safe_exp(a):
    try:
        if a > 30 or a < -30: return None  # keep in plausible range
        v = mp.exp(a)
        if mp.isfinite(v): return v
    except: pass
    return None


def enumerate_expressions(value_cap=mp.mpf(100), include_neg=False):
    """
    Return list of mpf values from all expressions using ≤3 operations.
    Includes negatives if include_neg=True (for w_0 which is negative).

    Level 0: atoms
    Level 1: 1 op applied to level-0 values (and pairs)
    Level 2: 1 op applied to (level-0 or level-1) values
    Level 3: 1 op applied to (level-0, 1, or 2) values

    Dedup by rounding to 1e-20.
    """
    # Level 0
    level = [v for v in ATOMS.values()]

    all_vals = list(level)
    seen_keys = set()

    def key_of(v):
        # round mantissa to 20 digits
        return mp.nstr(v, 20)

    for v in level:
        seen_keys.add(key_of(v))

    current = list(level)  # values reachable so far

    for op_round in range(3):  # apply up to 3 ops
        new_vals = []
        # Unary ops on everything in `current`
        for a in current:
            for p in [mp.mpf(2), mp.mpf("1/2"), mp.mpf(-1)]:
                r = safe_pow(a, p)
                if r is not None:
                    new_vals.append(r)
            r = safe_exp(a)
            if r is not None:
                new_vals.append(r)
            # Allow negation as a "free" unary if include_neg
            if include_neg:
                new_vals.append(-a)

        # Binary ops: pair up `current` with `current` (and original atoms)
        # To keep tractable, pair only with atoms for binary expansion at deeper levels
        partners = list(ATOMS.values()) if op_round > 0 else current
        for a in current:
            for b in partners:
                r = safe_mul(a, b)
                if r is not None:
                    new_vals.append(r)
                r = safe_div(a, b)
                if r is not None:
                    new_vals.append(r)
                r = safe_div(b, a)
                if r is not None:
                    new_vals.append(r)

        # Dedup and cap
        next_current = []
        for v in new_vals:
            if not mp.isfinite(v): continue
            av = abs(v)
            if av > value_cap: continue
            if av < mp.mpf("1e-15") and v != 0: continue
            k = key_of(v)
            if k in seen_keys: continue
            seen_keys.add(k)
            next_current.append(v)
            all_vals.append(v)

        current = current + next_current
        if len(all_vals) > 1_500_000:
            break

    return all_vals


# ----------------------------------------------------------------------
# 3. Observables
# ----------------------------------------------------------------------
OBSERVABLES = [
    # name, measurement, sigma, band_lo, band_hi, allow_negative, substrate_value
    ("w_0",          -0.838,  0.055, -3.0,  3.0,  True,  -mp.sqrt(2*mp.pi)/3),
    ("Li-7 ratio",    0.32,   0.06,   0.0,  1.0,  False, mp.pi/(10*mp.sqrt(2))),
    ("S_8",           0.769,  0.033,  0.0,  1.5,  False, mp.mpf("0.7693")),  # use book's reported value
    ("nu ratio",      0.0298, 0.0008, 0.0,  0.2,  False, mp.pi*mp.sqrt(2)/150),
    ("GW low-M peak", 9.8,    0.45,   0.0, 50.0,  False, mp.mpf(10)),
    ("GW q peak",     0.74,   0.13,   0.0,  1.0,  False, mp.sqrt(2)/(PHI + mp.mpf(1)/4)),
    ("GW kappa",      3.2,    1.0,    0.0, 20.0,  False, mp.pi),
]

# ----------------------------------------------------------------------
# 4. Run enumeration twice: one allowing negatives (for w_0), one positive
# ----------------------------------------------------------------------
print("Enumerating expressions (positive-only)...")
vals_pos = enumerate_expressions(value_cap=mp.mpf(100), include_neg=False)
print(f"  Generated {len(vals_pos)} unique positive expressions")

print("Enumerating expressions (with negation)...")
vals_signed = enumerate_expressions(value_cap=mp.mpf(100), include_neg=True)
print(f"  Generated {len(vals_signed)} unique signed expressions")


# ----------------------------------------------------------------------
# 5. Per-observable count
# ----------------------------------------------------------------------
def count_in_band(vals, meas, sigma, lo, hi, n_sigma_list=(0.5, 1.0, 2.0)):
    band_vals = [v for v in vals if (lo <= v <= hi)]
    counts = []
    for ns in n_sigma_list:
        c = sum(1 for v in band_vals if abs(float(v) - meas) <= ns*sigma)
        counts.append(c)
    return len(band_vals), counts


def substrate_in_band(substrate_val, meas, sigma, n_sigma):
    return abs(float(substrate_val) - meas) <= n_sigma * sigma


print()
print("="*100)
print("PER-OBSERVABLE TABLE")
print("="*100)
print(f"{'observable':<15} {'band_count':>10} {'≤0.5σ':>8} {'≤1σ':>8} {'≤2σ':>8} "
      f"{'subst.val':>12} {'subst.σ':>8} {'in≤0.5σ?':>9}")
print("-"*100)

per_obs_results = []
for name, meas, sigma, lo, hi, allow_neg, subst in OBSERVABLES:
    pool = vals_signed if allow_neg else vals_pos
    band_total, counts = count_in_band(pool, meas, sigma, lo, hi)
    subst_f = float(subst)
    subst_sigmas = abs(subst_f - meas) / sigma
    in_05 = substrate_in_band(subst, meas, sigma, 0.5)
    per_obs_results.append((name, band_total, counts, subst_f, subst_sigmas, in_05))
    print(f"{name:<15} {band_total:>10d} {counts[0]:>8d} {counts[1]:>8d} {counts[2]:>8d} "
          f"{subst_f:>12.5f} {subst_sigmas:>8.3f} {str(in_05):>9}")


# ----------------------------------------------------------------------
# 6. Joint analysis
# ----------------------------------------------------------------------
print()
print("="*100)
print("JOINT ANALYSIS")
print("="*100)

# per-observable expected hit rate within 0.5σ = (count ≤0.5σ) / (band total)
p_per = []
for name, band_total, counts, subst_f, subst_sigmas, in_05 in per_obs_results:
    p = counts[0] / band_total if band_total > 0 else 0.0
    p_per.append(p)
    print(f"  p({name} within 0.5σ | null) = {counts[0]}/{band_total} = {p:.5e}")

E_K = sum(p_per)
K_obs = sum(1 for r in per_obs_results if r[5])

print(f"\n  Expected hits ≤0.5σ under null: E[K] = {E_K:.4f}")
print(f"  Observed substrate hits ≤0.5σ:  K    = {K_obs} of {len(per_obs_results)}")

# Poisson tail P(X >= K_obs | lambda = E_K)
def poisson_tail(k, lam):
    if lam == 0:
        return 0.0 if k > 0 else 1.0
    # P(X >= k) = 1 - sum_{i=0}^{k-1} e^{-lam} lam^i / i!
    s = 0.0
    for i in range(k):
        s += exp(-lam) * (lam**i) / factorial(i)
    return 1 - s

p_joint = poisson_tail(K_obs, E_K)
print(f"\n  P(X ≥ {K_obs} | Poisson({E_K:.4f})) = {p_joint:.5e}")

# Also: exact Bernoulli sum for completeness
# P(K_obs or more out of 7 with varying p_i) — bound via Poisson is standard
# Verdict
print()
print("="*100)
print("VERDICT")
print("="*100)
if p_joint < 1e-3:
    verdict = "STRUCTURE"
    msg = f"Substrate's table is STRUCTURE: joint p = {p_joint:.3e} ≪ 10⁻³"
elif p_joint < 0.1:
    verdict = "BOUNDARY"
    msg = f"Substrate's table is at the BOUNDARY: joint p = {p_joint:.3e}"
else:
    verdict = "DECORATION"
    msg = f"Substrate's table is DECORATION: joint p = {p_joint:.3e} > 0.1"
print(msg)

print()
print(f"Total atoms in toolkit: {len(ATOMS)}")
print(f"Total positive expressions enumerated: {len(vals_pos)}")
print(f"Total signed expressions enumerated:   {len(vals_signed)}")
