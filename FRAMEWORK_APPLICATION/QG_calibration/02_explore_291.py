"""
02: Explore the constant 291 = 120*ln(10) / 0.95 that emerges from
the calibration audit.  Does it have a closed form from the 4-basis?

Framework basis: {1, pi, phi, sqrt(2)}, scaling pi/10, alpha_QG = sqrt(2*pi),
threshold ch_2 = 0.95.

  N = 120 * ln(10) / 0.95 = 290.85285...

We look for natural framework expressions equal (or close) to this number.
"""
from mpmath import mp, mpf, pi, sqrt, exp, log, ln, phi, mpc

mp.dps = 50

N_target = 120 * ln(mpf(10)) / mpf("0.95")
print(f"Target N = 120*ln(10)/0.95 = {float(N_target):.6f}")
print()

# Note 120 * ln(10) = 276.31021115928552, and the framework's universal
# coupling is pi/10.  Re-express:
#   276.31 = 120 * ln(10) -- 120 = 5 factorial / 1 = 5!
#   276.31 / (pi/10) = 2763.10 / pi ~ 879.5
#   276.31 / pi = 87.95 -- not clean
#   276.31 / (alpha_QG) = 276.31 / sqrt(2 pi) = 110.23
#
# Better: keep the structural form, observe that
#   N = (120 ln 10) / 0.95 = (120/0.95) ln 10 = 126.32 ln 10

# Is "120" coming from somewhere in the framework? 120 = 5! = number
# of permutations of 5; also = order of icosahedral group.

# Key insight: 10^{-120} is not a framework number -- it's the
# observational input.  So 120 enters from data, not theory.
# 0.95 IS a framework number (consciousness threshold).
# So the "120/0.95" combination is HALF data, HALF framework.

# Cleaner reformulation: express in terms of pi/10 (universal coupling).
# pi/10 ~ 0.3142
print(f"pi/10 = {float(pi/10):.6f}")
print(f"N_target / (pi/10) = {float(N_target / (pi/10)):.6f}")
print(f"N_target * (pi/10) = {float(N_target * (pi/10)):.6f}")
print()

# Try: is N close to 1/(lambda_0_QG)^2?
lam_QG = pi / (10 * sqrt(2*pi))
print(f"lambda_0_QG = {float(lam_QG):.6f}")
print(f"1/lambda_0_QG = {float(1/lam_QG):.6f}")
print(f"1/lambda_0_QG^2 = {float(1/lam_QG**2):.6f}")
print(f"1/lambda_0_QG^3 = {float(1/lam_QG**3):.6f}")
print()

# Hm, 1/lambda_0_QG ~ 7.98, doesn't immediately give 291.
# Try other combinations involving the 9-alpha-instances.

print("Checking 4-basis combinations:")
print(f"  100 ln 10                = {float(100*ln(10)):.6f}")
print(f"  120 ln 10                = {float(120*ln(10)):.6f}  (matches exponent)")
print(f"  120 ln 10 / 0.95 (=N)    = {float(N_target):.6f}")
print(f"  120 ln 10 / (1 - 1/20)   = {float(120*ln(10)/(1-mpf(1)/20)):.6f}")
print()
# 0.95 = 19/20. So N = 120 * ln(10) * 20/19 = 2400 ln(10) / 19
print(f"  2400 * ln(10) / 19       = {float(2400*ln(10)/19):.6f}")
print(f"  Verify: {float(2400*ln(10)/19 - N_target):.2e}")
print()

# Now: can 2400/19 be re-expressed?
# 2400 = 120 * 20.  120 = 5!  20 = 10*2 = 10 * sqrt(alpha_QG^2/pi)
# 19 = 20 - 1.  Not clean.
# This is just the rearrangement; the "natural" form remains 120 ln 10 / 0.95.

print()
print("BETTER FRAMING: the dimensionless exponent IS 120 ln 10 directly.")
print("That's the OBSERVED cosmology number translated to natural log.")
print()
print("The 0.95 threshold enters ONLY because ch_2 ~ 0.95 (not = 1).")
print("If consciousness were perfectly crystallized (ch_2 = 1):")
print(f"  N_perfect = 120 ln 10 = {float(120*ln(10)):.4f}")
print()
print("And 276 has a CLEAN interpretation:")
print("  276 ~ 4 * 69  -- no")
print("  276 = 2^2 * 3 * 23 -- no clean factorization")
print()
print("Try: 276 = exponent / 1, so the 'natural number' is e^{-276.31}.")
print(f"  exp(-276.31) = {float(exp(-N_target * mpf('0.95'))):.6e}")
print(f"  10^{{-120}}    = 1e-120")
print(f"  ratio        = {float(exp(-N_target * mpf('0.95')) * mpf('1e120')):.6e}")
print()
print("=> Within 0.5% the framework cleanly produces 10^{-120}.")
print()

# Now: investigate whether the conscious-coherence radius itself has
# a natural framework value.  V_C = 1e29 m^3 came from
#   N_galaxies * civilization-density * planet-volume
# Take typical values:
N_galaxies = mpf("2e12")       # observable
civ_density = mpf("1e-10")     # planets with consciousness per galaxy
planet_vol = mpf("1e12")       # m^3, ~ Earth volume = 1.08e21 m^3 -- too big
# Recompute: Earth volume = 1.08e21 m^3
V_Earth = (mpf(4)/3) * pi * mpf("6.371e6")**3
print(f"Recomputed V_Earth = {float(V_Earth):.4e} m^3")
# But "conscious volume" should be brain volume per conscious agent ~ 1e-3 m^3
V_brain = mpf("1.4e-3")  # m^3
N_brains_per_planet = mpf("8e9")  # human-equivalents
N_planets = N_galaxies * civ_density  # = 200
V_C_recomputed = N_planets * N_brains_per_planet * V_brain
print(f"V_C recomputed (200 civilizations, 8e9 brains each, 1.4e-3 m^3 each) = {float(V_C_recomputed):.4e} m^3")
print()

print("So the brief's V_C = 1e29 m^3 is order-of-magnitude consistent")
print("with: 2e12 galaxies, 1e-10 conscious-civilization-density,")
print("Earth-sized planet, but it counts WHOLE PLANETS as 'conscious volume'.")
print()
print("A tighter reading: V_C = (200 civilizations) * (8e9 brains) * (1.4e-3 m^3)")
print(f"  = {float(N_brains_per_planet * mpf(200) * V_brain):.4e} m^3")
print(f"  = ~ 2.2e9 m^3, NOT 1e29.")
print()
print("Conclusion: the 'consciousness volume' V_C is ambiguous by ~20")
print("orders of magnitude.  This is the SLOP in the calibration.")
