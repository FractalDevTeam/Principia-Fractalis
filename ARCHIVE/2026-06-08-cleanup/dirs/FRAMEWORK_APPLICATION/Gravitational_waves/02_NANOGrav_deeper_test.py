"""
Wave 15 NANOGrav deeper test.

Test 2A revealed two close framework natural numbers:
  lambda_QG^8 = 6.09e-8   (0.40 dex from 2.4e-8)
  exp(-EXP_LAMBDA/15) = 9.95e-9   (0.38 dex)

These are interesting BUT we need rigorous false-positive control:
  - How many random framework combinations would match within 0.5 dex by chance?
  - Is there a NATURAL physical reason for the power 8 or the /15 denominator?
  - What does NANOGrav's strain h_c(f) actually constrain?

NANOGrav 15-yr published:
  h_c(f_yr) = A * (f/f_yr)^alpha with A = 6.4e-15, alpha = -2/3 (from inspiraling SMBHB)
  Omega_GW(f) = (2*pi^2 / 3 H_0^2) * f^2 * h_c^2(f)
  At f_yr: Omega_GW ~ 2.4e-8
"""
from mpmath import mp, mpf, pi, sqrt, log, exp, log10
import random
import itertools

mp.dps = 60

PI10 = pi / 10
PHI = (1+sqrt(5))/2
ALPHA_QG = sqrt(2*pi)
LAMBDA_QG = sqrt(pi)/(10*sqrt(2))
LAMBDA_NP = pi / (10*(PHI + mpf(1)/4))
LAMBDA_P  = pi / (10*sqrt(2))
LAMBDA_RH = pi / (10*mpf(3)/2)
CH2 = mpf("0.95")
EXP_LAMBDA = mpf("245") * CH2 * mpf("1.1875")

target = mpf("2.4e-8")
log_target = log10(target)

# Big bank of framework natural numbers
basics = {
    "pi/10": PI10,
    "ch_2": CH2,
    "1-ch_2": 1-CH2,
    "lambda_NP": LAMBDA_NP,
    "lambda_P": LAMBDA_P,
    "lambda_QG": LAMBDA_QG,
    "lambda_RH": LAMBDA_RH,
    "1/phi": 1/PHI,
    "phi-1": PHI-1,
    "exp(-EXP_LAMBDA/15)": exp(-EXP_LAMBDA/15),
    "exp(-EXP_LAMBDA/14)": exp(-EXP_LAMBDA/14),
    "exp(-EXP_LAMBDA/16)": exp(-EXP_LAMBDA/16),
}

print("=" * 70)
print("FALSE-POSITIVE CONTROL — how often do natural combos hit 2.4e-8?")
print("=" * 70)

# Generate all single-base powers 1..12 + pairwise products of two bases each ^1..6
all_candidates = {}
for k, v in basics.items():
    for p in range(1, 13):
        all_candidates[f"{k}^{p}"] = v**p

# pairwise products
for (k1, v1), (k2, v2) in itertools.combinations(basics.items(), 2):
    for p1, p2 in itertools.product(range(1, 5), range(1, 5)):
        all_candidates[f"{k1}^{p1} * {k2}^{p2}"] = (v1**p1) * (v2**p2)

# Filter positive
all_candidates = {k: v for k, v in all_candidates.items() if v > 0}
print(f"\nTotal positive natural-combo candidates: {len(all_candidates)}")

# Bin by log10
log_candidates = {k: log10(v) for k, v in all_candidates.items()}
log_min = float(min(log_candidates.values()))
log_max = float(max(log_candidates.values()))
print(f"log10 range spans: [{log_min:.2f}, {log_max:.2f}]")
density = len(all_candidates) / (log_max - log_min)
print(f"Density of candidates per dex: {density:.1f}")
print(f"  ==> Expected number within ±0.5 dex of any target: {density:.1f}")
print(f"  ==> Expected number within ±0.4 dex of any target: {density*0.8:.1f}")

# count actual matches within 0.5 dex
matches_05 = [(k, log_candidates[k]-float(log_target)) for k in log_candidates if abs(log_candidates[k]-float(log_target)) < 0.5]
print(f"\nActual candidates within 0.5 dex of 2.4e-8: {len(matches_05)}")
print(f"(Expected by chance from density: {density:.1f})")

# Top 10 closest
sorted_matches = sorted(log_candidates.items(), key=lambda x: abs(x[1]-float(log_target)))[:15]
print(f"\nTop 15 closest natural-combo candidates to 2.4e-8:")
for k, lv in sorted_matches:
    dex = float(lv - float(log_target))
    v = all_candidates[k]
    print(f"  {k:45s} = {mp.nstr(v, 4):>14s}   dex offset = {dex:+.4f}")

print(f"""
INTERPRETATION:
  With {len(all_candidates)} natural framework candidates spanning {log_max-log_min:.1f} dex,
  density is ~{density:.0f} candidates per dex.
  Finding ~{density:.0f} candidates within 0.5 dex of ANY target is GUARANTEED
  by combinatorial bulk; finding a 0.4-dex match is at best WEAK evidence.

  To distinguish FRAMEWORK PREDICTION from NUMEROLOGY we need:
    (a) a DERIVED formula linking framework constants to Omega_GW(f_yr), or
    (b) an exponent like /15 or ^8 that has INDEPENDENT meaning, or
    (c) a structural reason (e.g., kappa_GW = lambda^k for specific k).

  None of these exist in the framework for stochastic GW background.
  ==> The lambda_QG^8 ~ 6e-8 match is NUMEROLOGICAL, not predictive.
""")

# ====================================================================
# What does the framework actually say about stochastic GW?
# ====================================================================
print("=" * 70)
print("STRUCTURAL CHECK — framework's stated GW sources")
print("=" * 70)
print("""
From manuscript reading:

  Ch 13 (Solutions/Dynamics): Modifies GR via consciousness rho_C ~ 1e-10 J/m^3.
    Predicts: dc/c ~ 1e-30 at LIGO band. Extra polarizations ~1e-12.

  Ch 19 (Physical Applications): QNM frequencies shift by G*Q_C^2/(M^3 c^5).
    For astrophysical BHs Q_C ~ 0 ==> no measurable shift.

  Ch 28 (Early Universe): explicitly states ch_2 = 0 for first 1 Gyr.
    ==> No primordial GW modification, no consciousness-sourced inflation tensors.

  Ch 28 Exercise 7 (line 698): "Do consciousness fluctuations source stochastic
    gravitational wave background at f ~ 10^-9 Hz (pulsar timing) or f ~ 10^-3 Hz (LISA)?"
    ==> This is asked as an OPEN PROBLEM, not answered.

  Ch 29 (Observational Tests): explicit prediction is
    "No measurable deviation in current GW observations (LIGO/Virgo sensitivity)"
    with |tau_f| < 1e-8 phase shift parameter, NULL at current sensitivity.

CONCLUSION: The framework explicitly DOES NOT predict an observable stochastic GW
signal. The NANOGrav signal would need to be ASTROPHYSICAL (SMBHB) within the
framework. Any framework-consistent GW source is suppressed by G*rho_C/omega^2
factors that put the signal far below detection.

This is INTERNALLY CONSISTENT for the framework (gravity propagates classically
in vacuum) but it is a NEGATIVE RESULT for "framework predicts new GW physics."
""")
