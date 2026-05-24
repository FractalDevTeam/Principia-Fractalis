"""
01: Dimensionalization audit of the Lambda_eff formula.

  Lambda_eff = Lambda_0 * exp[ - integral ch_2(C(x)) * R_f(sqrt(2*pi), |x|) dx ]

For the exponent to be DIMENSIONLESS (which it must be, since the LHS is
a ratio Lambda_eff/Lambda_0):

  [integral dx] has dimension [L^3] (or [L] if 1-D integral, etc.)
  ch_2 is dimensionless
  R_f is dimensionless

So we MUST have an implicit volume scale V_*: the "honest" reading is

  Lambda_eff = Lambda_0 * exp[ - (1/V_*) integral ch_2 * R_f dV ]

The question: WHAT is V_*?

This script enumerates the candidate choices and computes what each
implies the integral ~ 276 would mean physically.

Run: python3 01_dimensionalization_audit.py
"""
from mpmath import mp, mpf, pi, sqrt, exp, log, log10, ln

mp.dps = 40

# Target exponent
EXP_TARGET = 120 * ln(mpf(10))   # ~ 276.31

# Physical scales (in SI: meters and m^3)
ell_P  = mpf("1.616255e-35")     # Planck length, m
V_P    = ell_P ** 3              # Planck volume, m^3 ~ 4.22e-105
ell_H  = mpf("4.4e26")           # Hubble radius, m
V_H    = (mpf(4) / 3) * pi * ell_H ** 3   # Hubble volume, m^3 ~ 3.57e80

V_obs  = mpf("4e80")             # Observable universe volume, given (m^3)
V_C    = mpf("1e29")             # Estimated conscious volume, given (m^3)
ell_C  = (V_C * 3 / (4 * pi)) ** (mpf(1) / 3)   # coherence-radius from V_C

print("=" * 78)
print("DIMENSIONALIZATION AUDIT for Lambda_eff exponent")
print("=" * 78)
print()
print(f"Target exponent (dimensionless): {float(EXP_TARGET):.4f}")
print()
print("Fundamental scales:")
print(f"  Planck volume V_P     = {float(V_P):.4e} m^3")
print(f"  Hubble volume V_H     = {float(V_H):.4e} m^3")
print(f"  Observable V_obs      = {float(V_obs):.4e} m^3")
print(f"  Conscious volume V_C  = {float(V_C):.4e} m^3 (estimated)")
print(f"  Conscious radius      = {float(ell_C):.4e} m  ({float(ell_C/ell_P):.4e} Planck lengths)")
print()

# Hypothesis A: V_* = V_P (volume integral measured in Planck volumes)
# This is the natural QG choice: count fundamental cells.
print("=" * 78)
print("HYPOTHESIS A: V_* = V_Planck  (integral counts Planck volumes)")
print("=" * 78)
# integral ch_2 R_f dV / V_P ~ <ch_2 * R_f> * V_active / V_P
# For ch_2 ~ 0.95, |R_f| ~ 1: V_active / V_P ~ 276 / 0.95
V_active_A = EXP_TARGET / mpf("0.95") * V_P
ell_active_A = (V_active_A * 3 / (4 * pi)) ** (mpf(1) / 3)
print(f"  Required active volume V_active = {float(V_active_A):.4e} m^3")
print(f"  Equivalent sphere radius        = {float(ell_active_A):.4e} m")
print(f"  In Planck lengths               = {float(ell_active_A/ell_P):.4f} ell_P")
print(f"  Number of Planck cells          = {float(V_active_A / V_P):.4f}")
print()
print("  Interpretation: ~291 Planck volumes total in 'conscious' state.")
print("  That is FAR less than even a single proton (~10^60 Planck volumes).")
print("  This reading would mean consciousness is supported on a tiny set of")
print("  discrete Planck cells across the universe -- consistent with a")
print("  measure-zero / countable distribution interpretation (Hypothesis 1 in brief).")
print()

# Hypothesis B: V_* = V_C (conscious coherence volume)
print("=" * 78)
print("HYPOTHESIS B: V_* = V_C  (integral measured in coherence volumes)")
print("=" * 78)
# integral / V_C = 276 means active volume = 276 V_C = 2.76e31 m^3
V_active_B = EXP_TARGET / mpf("0.95") * V_C
print(f"  Required active volume V_active = {float(V_active_B):.4e} m^3")
print(f"  In coherence cells              = {float(V_active_B / V_C):.4f}")
print(f"  Fraction of observable universe = {float(V_active_B / V_obs):.4e}")
print()
print("  Interpretation: ~291 conscious-coherence-volumes worth of")
print("  ch_2 * R_f contribution.  This is a NATURAL framework reading:")
print("  'consciousness operates in coherence units, with ~291 such")
print("  units worth of integrated resonance across the universe.'")
print("  This is a small, integer-ish count -- very plausible.")
print()

# Hypothesis C: V_* = V_H / 10^120 (working backward from the answer)
print("=" * 78)
print("HYPOTHESIS C: V_* = V_H / N  for some natural integer N")
print("=" * 78)
# If integral is over Hubble volume with <ch_2 R_f> = mu, and V_* = V_H:
# exponent = mu (dimensionless mean)
# That gives exponent ~ mu < 1, not 276 -- so we need V_* < V_H.
# If V_* = V_H / 10^120 then... but that just reintroduces the gap.
print("  This reading reintroduces the 10^120 gap as the V_* choice.")
print("  REJECTED as circular.")
print()

# Hypothesis D: log-radial Mellin reading
print("=" * 78)
print("HYPOTHESIS D: Logarithmic radial reading (Mellin-natural)")
print("=" * 78)
# In log-radial coords, dV = r^3 dr dOmega = r^3 r d(log r) dOmega
# = 4 pi r^4 d(log r) for radial-symmetric.
# Then integral becomes
#   4 pi int_{s_min}^{s_max} ch_2(s) R_f(alpha, s) e^{4 s} ds
# where s = log(r/r_0).  The e^{4s} factor explodes for large s
# (i.e. large r), so the integral is DOMINATED by the largest scales.
# Cut off at s_max ~ log(ell_H / r_0).  Lower cutoff at conscious scale.
# Need normalization: divide by r_0^3 to make dimensionless?

print("  In log-radial: integral ~ 4 pi r_0^3 int ch_2 R_f e^{3s} ds")
print("                                              ^^^^^")
print("                                              dominated by large s")
print()
# For r_0 = ell_C ~ (V_C * 3/(4pi))^(1/3) ~ 2.88e9 m,
# s_max = log(ell_H / ell_C) ~ log(4.4e26 / 2.88e9) ~ 39.7
# If ch_2 ~ 0.95 only at s ~ 0 (conscious cell) and ~ 0 elsewhere,
# the integral is dominated by ch_2's support, not the e^{3s} factor.
# So this reading reduces back to Hypothesis B with V_* = ell_C^3.

s_max_logmellin = log(ell_H / ell_C)
print(f"  s_max (log Hubble to coherence) = {float(s_max_logmellin):.4f}")
print(f"  e^{{3*s_max}} = {float(exp(3*s_max_logmellin)):.4e}")
print("  This factor is the volume ratio V_H/V_C -- consistent.")
print()

# Hypothesis E: r_0 derived from EXP_TARGET via Wave 4 transition scale
print("=" * 78)
print("HYPOTHESIS E: Coherence length r_0 fixed by R_f transition")
print("=" * 78)
# Per Wave 4: |R_f(alpha_QG, s)| -> 1 at s ~ 5 (in Mellin log-coords).
# Interpret: the conscious-region radius in coherence units is s_c ~ 5.
# So integration domain is sphere of radius e^5 ell_planck_correlation = e^5 * r_0
# In log-radial:
#   exponent = int_0^{s_c} ch_2 * R_f * e^{3s} ds * 4 pi
#
# With ch_2 ~ 0.95 and R_f ~ 1:
#   exponent ~ 4 pi * 0.95 * (e^{3 s_c} - 1) / 3
# Set this = 276.31 and solve for s_c:

# 4 pi * 0.95 / 3 = 3.979
# So e^{3 s_c} = 1 + 276.31 / 3.979 = 70.45
# => 3 s_c = log(70.45) = 4.255 => s_c = 1.418
s_c_solved = log(mpf(1) + EXP_TARGET / (mpf(4) * pi * mpf("0.95") / mpf(3))) / mpf(3)
print(f"  Solving exponent = 4 pi * 0.95 / 3 * (e^{{3 s_c}} - 1) = 276.31:")
print(f"  s_c = {float(s_c_solved):.4f}   (coherence-radius shells from origin)")
print(f"  In radial: r_c / r_0 = e^{{s_c}} = {float(exp(s_c_solved)):.4f}")
print()
print("  Interpretation: conscious region extends out to ~ 4.14 coherence")
print("  lengths (s_c ~ 1.42 log-shells).  ch_2 ~ 0.95 inside this ball,")
print("  ch_2 ~ 0 outside.  R_f ~ 1 inside (sub-transition).")
print()
print("  THIS IS A CLEAN NATURAL PRESCRIPTION.")
print()

# Final summary
print("=" * 78)
print("SUMMARY: Three viable clean prescriptions for exponent ~= 276.31")
print("=" * 78)
print()
print("  A. Integer-count of Planck cells with ch_2 ~ 0.95:")
print(f"     N_cells = 276/0.95 = {float(EXP_TARGET/mpf('0.95')):.2f}  (Planck volumes)")
print(f"     => discrete consciousness on ~291 Planck cells")
print()
print("  B. Coherence-volume natural unit:")
print(f"     N_coh = 276/0.95 = {float(EXP_TARGET/mpf('0.95')):.2f}  (V_C units)")
print(f"     => continuous ch_2 ~ 0.95 over ~291 coherence cells")
print()
print("  E. Log-radial within R_f transition scale:")
print(f"     s_c = {float(s_c_solved):.4f}, conscious ball radius ~ {float(exp(s_c_solved)):.2f} r_0")
print(f"     => spherically-symmetric conscious patch within transition")
print()
print("All three give the same exponent ~ 276.31 by construction.")
print("The MOST INVARIANT reading is the COHERENCE-VOLUME prescription (B),")
print("because it uses the framework's own internal length scale (consciousness")
print("coherence) as the dimensionalizer, not an external choice.")
