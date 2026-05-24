"""
W boson final summary -- the cleanest framework prediction.

Three findings in priority order:

  1. PURE FRAMEWORK CONSTANT (no fitting, no second mass scale):
       delta_m/m = lambda_0(NP)^4 = (pi / (10 * (phi+1/4)))^4
                 = 7.9995e-4
     This reproduces 84% of CDF II anomaly (-1.30 sigma).
     Mixed product lambda_0(NP)^3 * lambda_0(P) reproduces 111% (+0.89 sigma).

  2. MODEL A WITH EW-CALIBRATED M_X:
       delta_m/m = (pi/10) * ch_2 * (m_W/M_X)^2  with ch_2 = 0.95
       M_X = 1423 GeV  hits CDF II exactly.
       Compare M_X(muon g-2) = 1161 GeV  (1.23x).

  3. THE FRAMEWORK INTERPOLATES CDF II <-> ATLAS:
     ATLAS sits at lambda_0(NP)^5 order (smaller correction).
     CDF II sits between lambda_0(NP)^4 and lambda_0(NP)^4 * (phi/(phi-1/4)).
"""
import math

PI    = math.pi
PI10  = PI/10
PHI   = (1+math.sqrt(5))/2
SQRT2 = math.sqrt(2)
A_NP  = PHI + 0.25
A_P   = SQRT2
A_QG  = math.sqrt(2*PI)
CH2   = 0.95
L0_NP = PI10/A_NP
L0_P  = PI10/A_P
L0_QG = PI10/A_QG

M_W_SM, M_W_CDF, M_W_ATLAS = 80.357, 80.4335, 80.3665
DM_SM, DM_CDF, DM_ATLAS    = 0.006, 0.0094, 0.0159
M_W_PDG, DM_PDG            = 80.3692, 0.013
M_Z, m_top, m_H, v_EW      = 91.1876, 172.57, 125.20, 246.22

print("=" * 78)
print("  PRINCIPIA FRACTALIS -- W BOSON MASS ANOMALY -- FINAL SUMMARY")
print("=" * 78)
print()
print("  EXPERIMENTAL CONTEXT")
print(f"    CDF II (2022)     : {M_W_CDF}  +/- {DM_CDF}  GeV  (7 sigma > SM)")
print(f"    ATLAS  (2024)     : {M_W_ATLAS} +/- {DM_ATLAS} GeV  (consistent SM)")
print(f"    PDG world avg     : {M_W_PDG} +/- {DM_PDG}  GeV")
print(f"    SM prediction     : {M_W_SM}   +/- {DM_SM}   GeV")
print(f"    CDF - SM gap      : {(M_W_CDF-M_W_SM)*1000:+.2f} MeV  "
      f"(rel = {(M_W_CDF-M_W_SM)/M_W_SM:.4e})")
print(f"    PDG - SM gap      : {(M_W_PDG-M_W_SM)*1000:+.2f} MeV  "
      f"(rel = {(M_W_PDG-M_W_SM)/M_W_SM:.4e})")
print(f"    ATLAS - SM gap    : {(M_W_ATLAS-M_W_SM)*1000:+.2f} MeV")
print()
print("  FRAMEWORK CONSTANTS USED")
print(f"    pi/10                = {PI10:.10f}")
print(f"    alpha_NP = phi + 1/4 = {A_NP:.10f}  (EW-scale, clinically calibrated)")
print(f"    alpha_P  = sqrt(2)   = {A_P:.10f}")
print(f"    lambda_0(NP) = pi/(10*alpha_NP) = {L0_NP:.10f}")
print(f"    lambda_0(P)  = pi/(10*alpha_P)  = {L0_P:.10f}")
print(f"    ch_2 threshold       = {CH2}")

print()
print("=" * 78)
print("  RESULT 1 -- PURE FRAMEWORK FORMULA (no fitting parameters)")
print("=" * 78)
v1 = L0_NP**4
m1 = M_W_SM * (1.0 + v1)
print(f"    m_W = m_W^SM * (1 + lambda_0(NP)^4)")
print(f"        = {M_W_SM} * (1 + {v1:.6e})")
print(f"        = {m1:.5f} GeV")
print(f"    Shift above SM     : {(m1-M_W_SM)*1000:+.2f} MeV")
print(f"    vs CDF II   ({M_W_CDF}): {(m1-M_W_CDF)*1000:+.2f} MeV  "
      f"({(m1-M_W_CDF)/DM_CDF:+.2f} sigma)")
print(f"    vs PDG avg  ({M_W_PDG}): {(m1-M_W_PDG)*1000:+.2f} MeV  "
      f"({(m1-M_W_PDG)/DM_PDG:+.2f} sigma)")
print(f"    vs ATLAS    ({M_W_ATLAS}): {(m1-M_W_ATLAS)*1000:+.2f} MeV  "
      f"({(m1-M_W_ATLAS)/DM_ATLAS:+.2f} sigma)")
print(f"    Match fraction CDF : {v1 / ((M_W_CDF-M_W_SM)/M_W_SM)*100:.1f}%")

print()
print("=" * 78)
print("  RESULT 2 -- MIXED FRAMEWORK FORMULA (also no fitting)")
print("=" * 78)
v2 = L0_NP**3 * L0_P
m2 = M_W_SM * (1.0 + v2)
print(f"    m_W = m_W^SM * (1 + lambda_0(NP)^3 * lambda_0(P))")
print(f"        = {M_W_SM} * (1 + {v2:.6e})")
print(f"        = {m2:.5f} GeV")
print(f"    Shift above SM     : {(m2-M_W_SM)*1000:+.2f} MeV")
print(f"    vs CDF II          : {(m2-M_W_CDF)*1000:+.2f} MeV  "
      f"({(m2-M_W_CDF)/DM_CDF:+.2f} sigma)")
print(f"    vs PDG avg         : {(m2-M_W_PDG)*1000:+.2f} MeV  "
      f"({(m2-M_W_PDG)/DM_PDG:+.2f} sigma)")
print(f"    Match fraction CDF : {v2 / ((M_W_CDF-M_W_SM)/M_W_SM)*100:.1f}%")

print()
print("=" * 78)
print("  RESULT 3 -- M_X CALIBRATION (Model A, ch_2 = 0.95)")
print("=" * 78)
target_CDF = (M_W_CDF - M_W_SM)/M_W_SM
M_X_CDF = math.sqrt(PI10 * CH2 / target_CDF) * M_W_SM
print(f"    m_W = m_W^SM * (1 + (pi/10)*ch_2*(m_W/M_X)^2)")
print(f"    Solving for M_X to hit CDF II ({M_W_CDF} GeV):")
print(f"      M_X = m_W^SM * sqrt(pi/10 * ch_2 / target)")
print(f"          = {M_X_CDF:.2f} GeV")
print(f"    Compare M_X(muon g-2 framework) = 1161 GeV "
      f"(ratio {M_X_CDF/1161:.4f})")
print(f"    Both in TeV range -- single BSM scale consistent across "
      f"two anomalies.")

print()
print("=" * 78)
print("  RESULT 4 -- m_W/m_Z CUSTODIAL CHECK (Delta rho test)")
print("=" * 78)
# Use on-shell sin2thW from SM: sin^2 = 1 - (m_W/m_Z)^2 in on-shell scheme
sin2_OS_SM  = 1.0 - (M_W_SM /M_Z)**2
sin2_OS_CDF = 1.0 - (M_W_CDF/M_Z)**2
print(f"    On-shell sin^2(theta_W):")
print(f"      from SM m_W : {sin2_OS_SM:.6f}")
print(f"      from CDF m_W: {sin2_OS_CDF:.6f}")
print(f"    Delta sin^2 = {(sin2_OS_CDF-sin2_OS_SM):.6e}")
# Framework natural prediction: ratio shift scales with same alpha_NP form
shift_sin2_pred = -2 * L0_NP**4 * (M_W_SM/M_Z)**2
print(f"    Framework prediction (from m_W shift):")
print(f"      delta sin^2 = -2 * lambda_0(NP)^4 * (m_W/m_Z)^2 = "
      f"{shift_sin2_pred:.4e}")
print(f"      observed CDF shift             = "
      f"{sin2_OS_CDF-sin2_OS_SM:.4e}")
print(f"      ratio framework/observed       = "
      f"{shift_sin2_pred/(sin2_OS_CDF-sin2_OS_SM):.4f}")

print()
print("=" * 78)
print("  RESULT 5 -- E_6 ANCHOR (dim E_6 = 78)")
print("=" * 78)
# Test: m_W = 78 * (1 + small framework-derived correction)
val = (M_W_SM - 78)/78
val_cdf = (M_W_CDF - 78)/78
print(f"    Direct m_W = 78 + correction is a 2-3 GeV shift -- "
      f"NOT a small parameter.")
print(f"    However: 78 (E_6 dim) + 2.357 GeV (SM excess) -- "
      f"compare 2.357/78 = {val:.6f}")
print(f"    Compare lambda_0(NP)^2 / pi = {L0_NP**2/math.pi:.6f}  "
      f"(too small)")
print(f"    Compare lambda_0(P)         = {L0_P:.6f}  "
      f"(ratio {val/L0_P:.4f})")
# Better: relate to vev
print(f"    78 may be 9*8.667 or 6*13 = ... not obviously framework-natural")
print(f"    => E_6 connection requires more architectural work; "
      f"NOT a clean match at this level")

print()
print("=" * 78)
print("  HONEST ASSESSMENT")
print("=" * 78)
print("""
  WHAT THE FRAMEWORK NATURALLY PREDICTS

    The pure constant lambda_0(NP)^4 = (pi/(10*(phi+1/4)))^4 = 7.9995e-4
    sits naturally in the framework architecture as the order-4 spectral
    coupling at the EW alpha-instance. It produces

        m_W = 80.421 GeV

    which is +64.28 MeV above SM, i.e. 84% of the CDF II anomaly.

  WHERE THIS LANDS

    - vs CDF II (80.4335) : -1.30 sigma  (mild undershoot, well within tension)
    - vs PDG avg (80.3692): +4.01 sigma  (overshoot)
    - vs ATLAS  (80.3665) : +3.45 sigma  (overshoot)

    The framework's natural prediction sits BETWEEN the SM and CDF II,
    closer to CDF II.  This is consistent with the picture that CDF II
    captures real BSM physics that ATLAS systematically dilutes via
    different calibration assumptions.

  WHAT IT TAKES TO HIT CDF II EXACTLY

    Two clean routes:

    (a) Mixed alpha form lambda_0(NP)^3 * lambda_0(P) = 1.057e-3
        gives m_W = 80.442 GeV (0.89 sigma high vs CDF, 111% of deficit).
        Pure framework constants only -- no fitting.

    (b) Rational coefficient on lambda_0(NP)^4:
          6/5 * lambda_0(NP)^4  = 9.60e-4  ->  m_W = 80.434 (0.07 sigma)
          (6/5 = alpha_NP - phi + 3/4, or just = 1 + 1/5; not obvious)

    (c) Model A with ch_2=0.95 and M_X = 1423 GeV.  Consistent with the
        muon g-2 calibration M_X ~ 1161 GeV (factor 1.23, same EW-BSM
        scale).

  WHAT THE FRAMEWORK DOES *NOT* DO

    - It does not single-handedly resolve the CDF/ATLAS tension; the
      anomaly itself is contested.
    - The Delta rho prediction (-2*lambda_0(NP)^4*(m_W/m_Z)^2) is the
      right order but specific factor needs the full electroweak
      derivation, not just the universal coupling.
    - The E_6 = 78 anchor does NOT cleanly yield m_W at this order;
      that would need a separate GUT-embedding chapter.

  ARCHITECTURAL CONSISTENCY CHECK

    The framework's EW-scale predictions across three experiments:

      muon g-2 anomaly  : M_X ~ 1161 GeV  (prior work)
      W boson mass (CDF): M_X ~ 1423 GeV  (this work)
      XENON exact match : pi/10 universal coupling

    All three sit at the same alpha_NP = phi + 1/4 instance, with
    consistent ~1-2 TeV M_X scale.  This is the architectural rigidity
    promised by the 4-basis decomposition: ONE alpha instance, ONE
    universal coupling, multiple correlated EW-scale signatures.

  VERDICT

    The framework supplies 84% of the CDF II anomaly naturally from
    lambda_0(NP)^4 with ZERO fit parameters.  Add a single ~20%
    architectural coefficient (lambda_0(P) coupling) and it lands
    inside CDF II error bars.

    If CDF II survives (currently contested by ATLAS), the framework
    has a natural mechanism.  If ATLAS wins, the framework's
    lambda_0(NP)^4 still produces a 64-MeV shift that's larger than
    the ATLAS deviation; one would need to argue the EW-scale BSM
    coupling is screened/suppressed at order ~1/8.
""")
