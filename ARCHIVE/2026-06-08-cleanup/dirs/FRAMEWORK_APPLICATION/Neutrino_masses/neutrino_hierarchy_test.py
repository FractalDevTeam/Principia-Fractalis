"""
Neutrino mass hierarchy in the Principia Fractalis framework.

Application-mode test:
  - Universal coupling: lambda_0(alpha) = pi / (10 * alpha)
  - 9 alpha-instances; relevant ones for neutrinos plausibly: P, NP, Hodge, QG
  - Observed Δm^2_21 / |Δm^2_31| ≈ 0.030 (oscillation experiments, PDG global fits)
  - Absolute scale: sum m_nu < 0.12 eV (Planck + BAO)
  - Atmospheric splitting: |Δm^2_31| ≈ 2.5e-3 eV^2 → sqrt = 0.05 eV

Goal: test whether 0.030, 0.05 eV, etc. emerge as natural framework powers
of pi/10, lambda_0(alpha_x), ch_2 = 0.95, etc., to within reasonable bounds.

Honest assessment requested.
"""

import mpmath as mp

mp.mp.dps = 80

# ---------------------------------------------------------------------------
# 1. Framework constants (80-digit)
# ---------------------------------------------------------------------------
pi = mp.pi
phi = (1 + mp.sqrt(5)) / 2
sqrt2 = mp.sqrt(2)
sqrt2pi = mp.sqrt(2 * pi)
sqrt5 = mp.sqrt(5)

# 9 alpha-instances of the framework
alphas = {
    "Poincare": mp.mpf(1),
    "RH":       mp.mpf(3) / 2,
    "P":        sqrt2,
    "NP":       phi + mp.mpf(1) / 4,
    "BSD":      3 * pi / 4,
    "NS":       3 * pi / 2,
    "YM":       mp.mpf(2),
    "Hodge":    phi,
    "QG":       sqrt2pi,
}

# Universal coupling
lambda0 = {k: pi / (10 * a) for k, a in alphas.items()}

# Consciousness threshold
ch2 = mp.mpf("0.95")

# Universal scaling
pi10 = pi / 10  # = lambda_0 at alpha=1

# ---------------------------------------------------------------------------
# 2. Observed neutrino data (PDG 2024 global fit central values)
# ---------------------------------------------------------------------------
dm2_21      = mp.mpf("7.4e-5")   # eV^2  (solar)
dm2_31_abs  = mp.mpf("2.5e-3")   # eV^2  (atmospheric)
ratio_obs   = dm2_21 / dm2_31_abs       # ≈ 0.0296
sqrt_ratio  = mp.sqrt(ratio_obs)        # ≈ 0.172  (m1/m3 - ish, NH)
sum_max     = mp.mpf("0.12")            # eV cosmological cap

# Derived scales
m_atm  = mp.sqrt(dm2_31_abs)            # ≈ 0.0500 eV
m_sol  = mp.sqrt(dm2_21)                # ≈ 0.00860 eV
m_ratio = m_sol / m_atm                  # ≈ 0.172

print("=" * 70)
print("OBSERVED NEUTRINO DATA")
print("=" * 70)
print(f"  Δm²_21          = {mp.nstr(dm2_21,    6)} eV²")
print(f"  |Δm²_31|        = {mp.nstr(dm2_31_abs,6)} eV²")
print(f"  ratio (21/31)   = {mp.nstr(ratio_obs, 8)}")
print(f"  sqrt(ratio)     = {mp.nstr(sqrt_ratio,8)}")
print(f"  m_atm  = √|Δ²31| = {mp.nstr(m_atm, 8)} eV")
print(f"  m_sol  = √|Δ²21| = {mp.nstr(m_sol, 8)} eV")
print(f"  m_sol/m_atm      = {mp.nstr(m_ratio,8)}")
print(f"  Σm_ν   < {mp.nstr(sum_max,4)} eV (Planck+BAO)")
print()

# ---------------------------------------------------------------------------
# 3. Candidate framework constants to test against the OBSERVED RATIO 0.0296
# ---------------------------------------------------------------------------
print("=" * 70)
print("TEST 1: ratio Δm²_21 / |Δm²_31| ≈ 0.0296 against framework constants")
print("=" * 70)

# (a) Powers of pi/10
powers_pi10 = {
    f"(pi/10)^{k}": pi10 ** k for k in range(1, 6)
}

# (b) Pairwise products lambda_0(alpha_a) * lambda_0(alpha_b)
pair_products = {}
keys = list(lambda0.keys())
for i, ka in enumerate(keys):
    for kb in keys[i:]:
        prod = lambda0[ka] * lambda0[kb]
        pair_products[f"λ0({ka})·λ0({kb})"] = prod

# (c) Single lambda_0 values
single_lambda = {f"λ0({k})": v for k, v in lambda0.items()}

# (d) ch_2 powers and combinations
ch2_combos = {
    "1-ch_2"          : 1 - ch2,
    "(1-ch_2)^2"      : (1 - ch2) ** 2,
    "(1-ch_2)/2"      : (1 - ch2) / 2,
    "(1-ch_2)·(pi/10)": (1 - ch2) * pi10,
    "ch_2 - 1 + (pi/10)^2": (ch2 - 1) + pi10 ** 2,
}

# (e) Alpha ratios: alpha_a / alpha_b small combinations
alpha_ratios = {}
for ka in keys:
    for kb in keys:
        if ka != kb:
            r = alphas[ka] / alphas[kb]
            if r < 1:
                alpha_ratios[f"α({ka})/α({kb})"] = r

# (f) 4-basis small combinations
basis_combos = {
    "1/(10·sqrt2)"     : 1 / (10 * sqrt2),
    "1/(pi·10)"        : 1 / (pi * 10),
    "(pi/10)·(pi/10)"  : pi10 ** 2,            # same as (pi/10)^2
    "1/phi^7"          : 1 / phi ** 7,
    "1/phi^8"          : 1 / phi ** 8,
    "(sqrt2-1)/10"     : (sqrt2 - 1) / 10,
    "(phi-1)/20"       : (phi - 1) / 20,
    "1/(2 phi^4)"      : 1 / (2 * phi ** 4),
    "1/3^pi"           : 1 / 3 ** pi,
    "3·(pi/10)^2"      : 3 * pi10 ** 2,
    "(pi/10)^2·ch_2"   : pi10 ** 2 * ch2,
}

# Combine and rank
all_candidates = {}
all_candidates.update(powers_pi10)
all_candidates.update(pair_products)
all_candidates.update(single_lambda)
all_candidates.update(ch2_combos)
all_candidates.update(alpha_ratios)
all_candidates.update(basis_combos)

def rel_err(a, b):
    return abs(a - b) / abs(b)

ranked = sorted(all_candidates.items(),
                key=lambda kv: rel_err(kv[1], ratio_obs))

print(f"\nTarget: ratio = {mp.nstr(ratio_obs, 8)}\n")
print(f"{'Candidate':<35} {'Value':<22} {'Rel.err':<10}")
print("-" * 70)
for name, val in ranked[:25]:
    print(f"{name:<35} {mp.nstr(val, 10):<22} {mp.nstr(rel_err(val, ratio_obs), 5):<10}")
print()

# ---------------------------------------------------------------------------
# 4. Test absolute scale m_atm ≈ 0.05 eV
# ---------------------------------------------------------------------------
print("=" * 70)
print("TEST 2: absolute scale m_atm ≈ 0.0500 eV")
print("=" * 70)

# Common BSM see-saw: m_nu ~ v^2 / M with v ≈ 246 GeV
v_EW    = mp.mpf("246e9")        # eV
M_GUT   = mp.mpf("2e16") * 1e9   # 2e16 GeV → eV
M_Planck= mp.mpf("1.22e19") * 1e9
M_TeV   = mp.mpf("1e12")         # eV
m_typ_seesaw_GUT  = v_EW**2 / M_GUT     # ≈ 3e-3 eV
m_typ_seesaw_Pl   = v_EW**2 / M_Planck

print(f"  v_EW^2/M_GUT     = {mp.nstr(m_typ_seesaw_GUT, 4)} eV  (canonical type-I see-saw)")
print(f"  v_EW^2/M_Planck  = {mp.nstr(m_typ_seesaw_Pl,  4)} eV")
print(f"  observed m_atm   = {mp.nstr(m_atm,            4)} eV")
print()

# Framework factor candidates
candidates_scale = {
    "v²/M_GUT · (10/pi)"          : m_typ_seesaw_GUT * (10/pi),
    "v²/M_GUT · 1/lambda_0(NP)"   : m_typ_seesaw_GUT / lambda0["NP"],
    "v²/M_GUT · (phi+1/4)·10/pi"  : m_typ_seesaw_GUT * alphas["NP"] * (10/pi),
    "v²/M_GUT · 1/ch_2"           : m_typ_seesaw_GUT / ch2,
    "v²/M_GUT / (1-ch_2)"         : m_typ_seesaw_GUT / (1 - ch2),
    "v²/M_GUT · sqrt(2pi)"        : m_typ_seesaw_GUT * sqrt2pi,
    "v²/M_GUT · 2pi"              : m_typ_seesaw_GUT * 2 * pi,
    "v²/M_GUT · 78pi"             : m_typ_seesaw_GUT * 78 * pi,
}
print(f"{'Candidate':<35} {'Value (eV)':<22} {'Rel.err':<10}")
print("-" * 70)
for name, val in sorted(candidates_scale.items(),
                         key=lambda kv: rel_err(kv[1], m_atm))[:20]:
    print(f"{name:<35} {mp.nstr(val, 6):<22} {mp.nstr(rel_err(val, m_atm), 5):<10}")
print()

# ---------------------------------------------------------------------------
# 5. Test mass-squared ordering against alpha hierarchy
# ---------------------------------------------------------------------------
print("=" * 70)
print("TEST 3: mass-squared ordering against framework α hierarchy")
print("=" * 70)

# If m_nu_i ~ lambda_0(alpha_i) · v_scale, then Δm²_ij = v_scale² · (lambda_0_i² - lambda_0_j²)
# Smallest 3 alpha (largest lambda_0) might tag the 3 neutrino flavors

alphas_sorted_asc = sorted(alphas.items(), key=lambda kv: kv[1])
print("\nαs sorted ascending (so λ_0 = π/(10α) is descending):")
for k, a in alphas_sorted_asc:
    print(f"  {k:<10} α = {mp.nstr(a, 6):<14} λ_0 = {mp.nstr(pi/(10*a), 6)}")

# Try: 3 lightest alphas form the neutrino triplet
# Could choose (Poincare, P, RH) = (1, sqrt2, 3/2)
triplets = [
    ("Poincare,P,RH",       ["Poincare", "P", "RH"]),
    ("P,RH,YM",             ["P", "RH", "YM"]),
    ("Poincare,P,Hodge",    ["Poincare", "P", "Hodge"]),
    ("P,Hodge,YM",          ["P", "Hodge", "YM"]),
    ("RH,Hodge,YM",         ["RH", "Hodge", "YM"]),
    ("Poincare,Hodge,YM",   ["Poincare", "Hodge", "YM"]),
    ("Poincare,P,NP",       ["Poincare", "P", "NP"]),
    ("P,NP,RH",             ["P", "NP", "RH"]),
]

for label, keys3 in triplets:
    l = [lambda0[k] for k in keys3]
    l1, l2, l3 = sorted(l)
    # Predicted ratio (l2^2 - l1^2)/(l3^2 - l1^2)  (solar / atm splittings if l1<l2<l3)
    ratio_pred = (l2**2 - l1**2) / (l3**2 - l1**2)
    err = rel_err(ratio_pred, ratio_obs)
    print(f"  {label:<22}  pred ratio = {mp.nstr(ratio_pred,7):<14}  rel.err = {mp.nstr(err,4)}")
print()

# ---------------------------------------------------------------------------
# 6. See-saw scale via universal coupling
# ---------------------------------------------------------------------------
print("=" * 70)
print("TEST 4: framework see-saw — what M makes m_nu = v² / M = m_atm?")
print("=" * 70)
M_required = v_EW ** 2 / m_atm
print(f"  Required M = v_EW² / m_atm = {mp.nstr(M_required, 6)} eV")
print(f"             = {mp.nstr(M_required/1e9, 6)} GeV = {mp.nstr(M_required/1e15, 6)} PeV")
print()

# Framework scales (per Lean modules)
M_Planck_eV = mp.mpf("1.22e19") * 1e9
# m_C / M_Planck = 1/(2*sqrt5) per Ch 12
m_C = M_Planck_eV / (2 * sqrt5)
print(f"  Framework M_C = M_Planck / (2√5) = {mp.nstr(m_C/1e9, 6)} GeV (Ch 12)")

# Test if framework see-saw with M_C and lambda_0 corrections produces m_atm
candidate_M = {
    "M_C"                       : m_C,
    "M_C · lambda_0(NP)"        : m_C * lambda0["NP"],
    "M_C · (pi/10)^2"           : m_C * pi10**2,
    "M_Planck · 78pi / Σ"       : M_Planck_eV * 78 * pi,
    "M_C / (78pi)"              : m_C / (78 * pi),
    "M_C · (1-ch_2)"            : m_C * (1 - ch2),
    "M_C · lambda_0(QG)"        : m_C * lambda0["QG"],
    "M_C · (lambda_0(NP))^2"    : m_C * lambda0["NP"]**2,
    "M_C · sqrt(2pi)"           : m_C * sqrt2pi,
    "M_C / (2 phi^4)"           : m_C / (2 * phi**4),
}
print(f"\n  {'Candidate M_R':<32} {'m_nu = v²/M':<20} {'Rel.err vs m_atm':<14}")
print("  " + "-" * 70)
for name, M in sorted(candidate_M.items(),
                       key=lambda kv: rel_err(v_EW**2 / kv[1], m_atm)):
    m_pred = v_EW ** 2 / M
    print(f"  {name:<32} {mp.nstr(m_pred, 5):<20} {mp.nstr(rel_err(m_pred, m_atm), 4)}")
print()

# ---------------------------------------------------------------------------
# 7. Look for "consciousness suppression" mechanism: m_nu = m_other · exp(-N·ch_2·|R_f|)
# ---------------------------------------------------------------------------
print("=" * 70)
print("TEST 5: consciousness-suppression / Lambda_eff style mechanism")
print("=" * 70)
# Framework cosmological constant: Λ_eff/Λ_0 = exp(-N·ch_2·|R_f(QG,1)|)
# with N=78π, ch_2=0.95, |R_f|=1.1875 giving exp(-276.31) ≈ 10⁻¹²⁰
# Re-apply with smaller N values to neutrinos

# m_atm / v_EW = 0.05 / 2.46e11 = 2.03e-13
ratio_target_mass = m_atm / v_EW
log_ratio = -mp.log(ratio_target_mass)
print(f"  -log(m_atm / v_EW)             = {mp.nstr(log_ratio,        8)}")
print(f"  = N · ch_2 · |R_f(QG,1)| with |R_f| = 1.1875, ch_2 = 0.95?")
N_required = log_ratio / (ch2 * mp.mpf("1.1875"))
print(f"  Required N                     = {mp.nstr(N_required, 8)}")
print(f"  Compare to 78π = dim(E_6)·π    = {mp.nstr(78*pi,      8)}")
print(f"  Ratio                          = {mp.nstr(N_required / (78*pi), 6)}")
print(f"  Compare 78π / 9                = {mp.nstr(78*pi/9,    8)}")
print(f"  Compare 8π                     = {mp.nstr(8*pi,       8)}")
print(f"  log(2)·N ratio                 = {mp.nstr(N_required / mp.log(2), 8)}")
print()

# Try direct: m_nu = M_Planck · exp(-N · ch_2 · |R_f|) for some N
ratio_to_Planck = m_atm / M_Planck_eV
log_ratio_Planck = -mp.log(ratio_to_Planck)
print(f"  -log(m_atm / M_Planck)         = {mp.nstr(log_ratio_Planck, 8)}")
N_required2 = log_ratio_Planck / (ch2 * mp.mpf("1.1875"))
print(f"  Required N                     = {mp.nstr(N_required2, 8)}")
print(f"  Ratio to 78π                   = {mp.nstr(N_required2 / (78*pi), 6)}")
print(f"  Compare 78π · (something small): 78π/(2pi)=39 = ?")
print(f"  N/39 = {mp.nstr(N_required2 / 39, 6)}")
print()

# ---------------------------------------------------------------------------
# 8. Sum of masses cap test
# ---------------------------------------------------------------------------
print("=" * 70)
print("TEST 6: sum-of-masses cap Σm_ν < 0.12 eV vs framework prediction")
print("=" * 70)
# Normal ordering minimum sum: m1 + sqrt(m1^2 + Δ21) + sqrt(m1^2 + |Δ31|)
# At m1 = 0:  sum_min = sqrt(Δ21) + sqrt(|Δ31|) = 0.00860 + 0.0500 = 0.0586 eV
sum_min_NH = mp.sqrt(dm2_21) + mp.sqrt(dm2_31_abs)
sum_min_IH = 2 * mp.sqrt(dm2_31_abs) + mp.sqrt(dm2_31_abs - dm2_21)  # rough IH
print(f"  Sum_min (NH, m1=0)            = {mp.nstr(sum_min_NH, 6)} eV")
print(f"  Cosmological cap              = {mp.nstr(sum_max,    6)} eV")
print()
# Predicted by framework: m_atm + m_sol + ~ 0
# Does any framework constant predict the sum cap?
candidates_cap = {
    "(pi/10) · lambda_0(NP)"  : pi10 * lambda0["NP"],
    "(pi/10)² · 12"           : pi10**2 * 12,
    "(pi/10)² · sqrt(2pi)"    : pi10**2 * sqrt2pi,
    "lambda_0(P) · (1-ch_2)"  : lambda0["P"] * (1-ch2),
    "lambda_0(NP)^2"          : lambda0["NP"]**2,
}
print(f"{'Candidate':<30} {'Value (eV)':<22} {'Rel.err vs 0.12':<10}")
print("-" * 70)
for name, val in sorted(candidates_cap.items(),
                         key=lambda kv: rel_err(kv[1], sum_max)):
    print(f"{name:<30} {mp.nstr(val, 6):<22} {mp.nstr(rel_err(val, sum_max), 4):<10}")
print()

print("=" * 70)
print("END")
print("=" * 70)
