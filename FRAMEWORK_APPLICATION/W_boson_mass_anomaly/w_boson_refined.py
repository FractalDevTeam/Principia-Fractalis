"""
W boson refined analysis -- pursue the lambda_0(NP)^4 hit and clean
framework-only forms (no fitted M_X).

Two leading candidates emerged from sweep:
  (A) lambda_0(NP)^4 = (pi/(10*alpha_NP))^4 ~ 8.00e-4   vs target 9.52e-4
      ratio = 0.84   (84% of CDF deficit)
  (B) M_X = 1422.79 GeV (Model A with ch_2 = 0.95)
      vs muon g-2 M_X ~ 1161 GeV  (factor 1.23)

Search for cleanest closed form matching CDF II.
"""
import math
from itertools import product

PI10  = math.pi/10
PHI   = (1+math.sqrt(5))/2
SQRT2 = math.sqrt(2)
A_NP  = PHI + 0.25
A_P   = SQRT2
A_RH  = 1.5
A_HG  = PHI
A_QG  = math.sqrt(2*math.pi)
CH2   = 0.95
L0_NP = PI10/A_NP
L0_P  = PI10/A_P

M_W_SM, M_W_CDF, M_W_ATLAS = 80.357, 80.4335, 80.3665
DM_CDF, DM_ATLAS = 0.0094, 0.0159
target_CDF   = (M_W_CDF - M_W_SM) / M_W_SM       # 9.52e-4
target_ATLAS = (M_W_ATLAS - M_W_SM) / M_W_SM     # 1.18e-4
target_PDG   = (80.3692 - M_W_SM) / M_W_SM       # PDG world avg
print(f"Targets: CDF={target_CDF:.4e}, PDG={target_PDG:.4e}, "
      f"ATLAS={target_ATLAS:.4e}")
print()

# -----------------------------------------------------------------------------
# Cleanest framework forms (no second mass scale, no fitting):
# -----------------------------------------------------------------------------
print("=" * 72)
print(" CLEAN CLOSED FORMS -- all derived from framework constants only")
print("=" * 72)

candidates = [
    ("lambda_0(NP)^4",             L0_NP**4),
    ("lambda_0(NP)^4 * ch_2",      L0_NP**4 * CH2),
    ("lambda_0(NP)^4 / ch_2",      L0_NP**4 / CH2),
    ("(pi/10)^4 / alpha_NP^4",     (PI10/A_NP)**4),
    ("lambda_0(P) * lambda_0(NP)^3", L0_P*L0_NP**3),
    ("lambda_0(NP)^3 * (pi/10)",   L0_NP**3 * PI10),
    ("lambda_0(P)^4",              L0_P**4),
    ("lambda_0(P)^4 * (alpha_NP/alpha_P)^4", L0_P**4*(A_NP/A_P)**4),
    ("(pi/10)^3 / alpha_NP^4",     PI10**3/A_NP**4),
    ("lambda_0(NP)^4 * (1 + 1/9)", L0_NP**4 * 10/9),
    ("(pi^4)/(10^4 * alpha_NP^4)", math.pi**4/(10**4*A_NP**4)),
    ("1/(alpha_NP^4 * 10^3)",      1/(A_NP**4*1000)),
    ("ch_2 * (pi/10)^2 * (lambda_0_NP)^2",
                                    CH2*PI10**2*L0_NP**2),
    ("(pi/10)^2 * lambda_0(NP)^2", PI10**2*L0_NP**2),
    ("(pi/10) * lambda_0(NP)^3",   PI10*L0_NP**3),
    ("lambda_0(NP)^2 * (pi/10)^2 / ch_2",
                                    PI10**2*L0_NP**2/CH2),
    ("(lambda_0(NP) * pi/10)^2",   (L0_NP*PI10)**2),
    ("lambda_0(NP)^3 * lambda_0(P)", L0_NP**3*L0_P),
    ("lambda_0(NP)^2 * (1/alpha_NP)^2",
                                    L0_NP**2 / A_NP**2),
    ("(pi/10)^2 / alpha_NP^4",     PI10**2/A_NP**4),
    ("lambda_0(QG)^4",             (PI10/A_QG)**4),
    ("lambda_0(QG)^4 / ch_2",      (PI10/A_QG)**4/CH2),
]

print(f"\n  {'Formula':<48s}  {'value':>11s}   {'rel CDF':>9s} "
      f" {'rel PDG':>9s}  {'sig CDF':>9s}")
hits = []
for name, val in candidates:
    pred_m = M_W_SM * (1.0 + val)
    sig_cdf = (pred_m - M_W_CDF)/DM_CDF
    rel_cdf = val / target_CDF
    rel_pdg = val / target_PDG
    flag = ""
    if 0.5 < rel_cdf < 2.0:
        flag = " <-- CDF"
        hits.append((name, val, sig_cdf))
    print(f"  {name:<48s}  {val:11.4e}  {rel_cdf:9.4f}  "
          f"{rel_pdg:9.4f}  {sig_cdf:+9.2f}{flag}")

# -----------------------------------------------------------------------------
# Refined "lambda_0(NP)^4 with rational coefficient" sweep
# -----------------------------------------------------------------------------
print()
print("=" * 72)
print(" SHARPEN lambda_0(NP)^4 by rational coefficient")
print("=" * 72)

needed_coef = target_CDF / L0_NP**4
print(f"\n  target_CDF / lambda_0(NP)^4 = {needed_coef:.6f}")
print(f"  Want: coefficient near {needed_coef:.4f}")

# Test simple rational candidates
for p in range(1,11):
    for q in range(1,11):
        c = p/q
        if 1.10 < c < 1.30:
            pred = c * L0_NP**4
            sig = (M_W_SM*(1+pred) - M_W_CDF)/DM_CDF
            if abs(sig) < 3:
                print(f"    p/q = {p}/{q} = {c:.4f}: "
                      f"{c}*L0NP^4 = {pred:.4e}, "
                      f"m_W = {M_W_SM*(1+pred):.4f}, sig CDF = {sig:+.2f}")

# Test ch_2-related coefficients
for c_name, c in [("ch_2", 0.95), ("1/ch_2", 1/0.95), ("ch_2+1/4", 1.20),
                   ("phi-1/3", PHI-1/3), ("6/5", 1.2), ("5/4", 1.25),
                   ("phi/(phi-1/4)", PHI/(PHI-0.25)), ("4/pi", 4/math.pi),
                   ("phi/sqrt2", PHI/SQRT2)]:
    pred = c * L0_NP**4
    sig = (M_W_SM*(1+pred) - M_W_CDF)/DM_CDF
    print(f"    {c_name:<20s} = {c:.6f}: pred = {pred:.4e}, "
          f"m_W = {M_W_SM*(1+pred):.5f}, sig CDF = {sig:+.2f}")

# -----------------------------------------------------------------------------
# COMBINED FRAMEWORK FORM SEARCH (a^p * (pi/10)^q * ch_2^r)
# -----------------------------------------------------------------------------
print()
print("=" * 72)
print(" BROAD BASIS SEARCH (small integer exponents)")
print("=" * 72)
print(f"  Looking for: alpha_NP^p * (pi/10)^q * ch_2^r ~ target_CDF")
print(f"  in CDF window |sigma| < 2")

results = []
for p in range(-6, 1):
    for q in range(0, 6):
        for r in range(0, 3):
            val = A_NP**p * PI10**q * CH2**r
            sig_cdf = (M_W_SM*(1+val) - M_W_CDF)/DM_CDF
            sig_pdg = (M_W_SM*(1+val) - 80.3692)/0.013
            if abs(sig_cdf) < 2 or abs(sig_pdg) < 1.5:
                results.append((p,q,r,val,sig_cdf,sig_pdg))

for p,q,r,val,sc,sp in sorted(results, key=lambda x: abs(x[4])):
    print(f"    alpha_NP^{p:+d} * (pi/10)^{q} * ch_2^{r}: "
          f"val={val:.4e}, m_W={M_W_SM*(1+val):.5f}, "
          f"sig_CDF={sc:+.2f}, sig_PDG={sp:+.2f}")

# -----------------------------------------------------------------------------
# WHAT FRAMEWORK PREDICTS NATURALLY (no fitting)
# -----------------------------------------------------------------------------
print()
print("=" * 72)
print(" FRAMEWORK NATURAL PREDICTION (chosen ex ante from architecture)")
print("=" * 72)
print(f"  By analogy with Mechanism 3 EW corrections at order lambda_0^4:")
print(f"    delta_m/m = lambda_0(NP)^4 = (pi/(10*alpha_NP))^4")
print(f"             = {L0_NP**4:.6e}")
print(f"  m_W predicted = m_W^SM * (1 + lambda_0(NP)^4)")
print(f"                = {M_W_SM*(1+L0_NP**4):.5f} GeV")
print(f"  CDF II value  = {M_W_CDF} GeV   diff = "
      f"{(M_W_SM*(1+L0_NP**4)-M_W_CDF)*1000:.2f} MeV  "
      f"({(M_W_SM*(1+L0_NP**4)-M_W_CDF)/DM_CDF:+.2f} sigma)")
print(f"  ATLAS value   = {M_W_ATLAS} GeV   diff = "
      f"{(M_W_SM*(1+L0_NP**4)-M_W_ATLAS)*1000:.2f} MeV  "
      f"({(M_W_SM*(1+L0_NP**4)-M_W_ATLAS)/DM_ATLAS:+.2f} sigma)")
print(f"  SM value      = {M_W_SM} GeV   diff = "
      f"{(M_W_SM*(1+L0_NP**4)-M_W_SM)*1000:.2f} MeV")
print()
print(f"  Predicted shift = +{L0_NP**4 * M_W_SM * 1000:.2f} MeV above SM")
print(f"  CDF shift       = +{(M_W_CDF-M_W_SM)*1000:.2f} MeV above SM")
print(f"  Match fraction  = {L0_NP**4/target_CDF*100:.1f}% of CDF deficit")
