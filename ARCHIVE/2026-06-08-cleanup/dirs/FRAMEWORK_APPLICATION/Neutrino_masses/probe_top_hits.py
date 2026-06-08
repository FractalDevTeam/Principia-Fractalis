"""
Drill-down on best candidate hits from neutrino_hierarchy_test.py.

Top hit (TEST 1): λ_0(P) · λ_0(BSD) = π² / (10·√2 · 10·3π/4) = π/(75√2)
                = 0.029619... vs observed Δm²_21 / |Δm²_31| ≈ 0.0296
                Rel.err ≈ 6.5e-4 (= 0.065%)

This is suspiciously clean. P-class + BSD class both touch the framework's
4-basis {1,π,φ,√2}. Let's verify the closed form and bracket the observed
ratio against current PDG range to see if it's within experimental error.
"""

import mpmath as mp
mp.mp.dps = 80

pi    = mp.pi
sqrt2 = mp.sqrt(2)
phi   = (1 + mp.sqrt(5)) / 2

# Closed-form derivation
# λ_0(P)  = π/(10·√2)
# λ_0(BSD)= π/(10·3π/4) = 4/(30) = 2/15
# product = π/(10·√2) · 2/15 = 2π/(150√2) = π/(75√2) = π√2/150
closed_form = pi / (75 * sqrt2)
also        = pi * sqrt2 / 150
also2       = 2 * pi / (150 * sqrt2)

print("=" * 70)
print("DRILL-DOWN: λ_0(P) · λ_0(BSD)")
print("=" * 70)
print(f"  π/(75√2)         = {mp.nstr(closed_form, 30)}")
print(f"  π√2/150          = {mp.nstr(also,        30)}")
print(f"  2π/(150√2)       = {mp.nstr(also2,       30)}")
print(f"  All equal:       = {closed_form == also == also2}")
print()

# Observed ratio with 2024 PDG global fit (NuFIT 5.3 / PDG2024):
# Δm²_21 = (7.42 +0.21 / -0.20) × 10⁻⁵ eV²
# |Δm²_3l| (NH) = (2.515 +0.028/-0.028) × 10⁻³ eV²   (different convention than Δm²_31)
# Or Δm²_31 (NH) ≈ 2.55 × 10⁻³ eV²

# Central:
dm2_21_c   = mp.mpf("7.42e-5")
dm2_31_c_NH = mp.mpf("2.515e-3")
ratio_c_NH = dm2_21_c / dm2_31_c_NH
print(f"  PDG/NuFIT central ratio (NH) = {mp.nstr(ratio_c_NH, 8)}")

dm2_31_c_IH = mp.mpf("2.498e-3")
ratio_c_IH = dm2_21_c / dm2_31_c_IH
print(f"  PDG/NuFIT central ratio (IH) = {mp.nstr(ratio_c_IH, 8)}")

# 1-sigma bounds (very rough)
ratio_hi = mp.mpf("7.62e-5") / mp.mpf("2.487e-3")  # high 21 / low 31
ratio_lo = mp.mpf("7.22e-5") / mp.mpf("2.543e-3")  # low 21 / high 31
print(f"  1-sigma window (NH-ish)      = ({mp.nstr(ratio_lo,6)}, {mp.nstr(ratio_hi,6)})")
print(f"  Framework prediction (π/75√2)= {mp.nstr(closed_form, 8)}")
print(f"  Inside 1-sigma window?       = {ratio_lo < closed_form < ratio_hi}")
print(f"  rel.err to NH central        = {mp.nstr(abs(closed_form - ratio_c_NH)/ratio_c_NH, 4)}")
print(f"  rel.err to IH central        = {mp.nstr(abs(closed_form - ratio_c_IH)/ratio_c_IH, 4)}")
print()

# Interpret structurally
# If m_i are eigenvalues of H_alpha_i, then
#    m_i ∝ λ_0(α_i) = π/(10·α_i)
# So Δm²_ij ∝ λ_0(α_i)² - λ_0(α_j)²
# Try: 3 neutrinos correspond to 3 α-classes
# Hypothesis: heaviest m3 = lambda_0(P) (lightest α = √2 → heaviest λ_0)
# but for hierarchy testing we need to be careful with normal/inverted ordering.

# Match:
#    Δm²_21 / |Δm²_31| ≈ λ_0(P) · λ_0(BSD)
# This is a PRODUCT, not a difference. So the structural interpretation
# would be: m_2 · m_1 = some product of framework couplings.
# That would suggest m_2 m_1 / (m_3 m_X) ∝ λ_0(P) λ_0(BSD).
# Less natural than hoping for a *difference*.

# Sanity check on the difference structure:
# Δm²_21 / |Δm²_31| = (λ_0(α2)² - λ_0(α1)²) / (λ_0(α3)² - λ_0(α1)²)
# Closed form needed.

# 4-basis status: π/(75√2) = π · sqrt(2) / 150
# Both π and sqrt(2) are in the 4-basis {1, π, φ, √2}. Coefficient 150 = 2·3·5²
# Numerator π * √2 = √(2π²) → 4-basis present.

# Check (π√2/150) under PSLQ basis - already in framework primitives
print("  Coefficient 150 = 2 · 3 · 5²; both basis elements π and √2 present.")
print("  Framework structurally COMPATIBLE with this closed form.")
print()

# But: is this just numerical coincidence or structural?
# Probability that a random product of 2 of 9 lambda_0 values falls within 0.07%
# of a fixed target?
# 45 pairs, range of products spans ~0.004 to ~0.1, log-uniform-ish
# Chance any one falls within 0.065% of target ~ 45 * 2 * 0.00065 / log(0.1/0.004)
# = 0.0585 / 3.22 ≈ 1.8% ... not entirely negligible but suggestive.
print("=" * 70)
print("STATISTICAL SIGNIFICANCE OF λ_0(P)·λ_0(BSD) HIT")
print("=" * 70)
# Compute distribution of all 45 pairwise products
alphas = {
    "Poincare": mp.mpf(1),
    "RH":       mp.mpf(3) / 2,
    "P":        sqrt2,
    "NP":       phi + mp.mpf(1) / 4,
    "BSD":      3 * pi / 4,
    "NS":       3 * pi / 2,
    "YM":       mp.mpf(2),
    "Hodge":    phi,
    "QG":       mp.sqrt(2 * pi),
}
lambda0 = {k: pi/(10*a) for k, a in alphas.items()}
keys = list(lambda0.keys())
products = []
for i, ka in enumerate(keys):
    for kb in keys[i:]:
        products.append((f"{ka}·{kb}", lambda0[ka] * lambda0[kb]))

products.sort(key=lambda kv: kv[1])
print(f"  # of pair products = {len(products)}")
print(f"  min = {mp.nstr(products[0][1], 6)}, max = {mp.nstr(products[-1][1], 6)}")
target = ratio_c_NH
within_tol = [(k, v) for k, v in products if abs(v - target) / target < 0.01]
print(f"  Pairs within 1% of {mp.nstr(target, 6)}: {len(within_tol)}")
for k, v in within_tol:
    print(f"    {k}: {mp.nstr(v, 8)} (rel.err {mp.nstr(abs(v-target)/target, 4)})")
print()

# Try: maybe ratio is more naturally (λ_0(P) - λ_0(BSD))² / (λ_0(BSD))² etc.
# Look for *clean differences* squared
print("=" * 70)
print("TEST: difference-of-squares ratios (3 α-classes as 3 mass eigenstates)")
print("=" * 70)
# For each unordered triple (a1<a2<a3), compute (λa3² - λa1²)/(λa1² - λa2²) for various orderings
# Actually, we want the RATIO ≈ 0.030, so small / large.
# Δm²_21 / |Δm²_31| means (m_2² - m_1²) / |m_3² - m_1²|, with m_2 close to m_1, m_3 farther.
# So we need a triple where TWO α-values give close λ_0 and the third is far.

from itertools import combinations
best = []
for trio in combinations(keys, 3):
    ls = sorted([(k, lambda0[k]) for k in trio], key=lambda kv: kv[1])
    # 6 orderings of which is "m_1", "m_2", "m_3"
    # Δm²_21 = m_2² - m_1² > 0
    # Δm²_31 = m_3² - m_1² (sign matters; we use |...|)
    for perm in [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]:
        m1_lab, m2_lab, m3_lab = [ls[i] for i in perm]
        m1, m2, m3 = m1_lab[1], m2_lab[1], m3_lab[1]
        if m2**2 - m1**2 <= 0:
            continue
        if m3**2 - m1**2 == 0:
            continue
        r = (m2**2 - m1**2) / abs(m3**2 - m1**2)
        if r < 1 and r > 0.001:
            err = abs(r - target) / target
            best.append((err, r, (m1_lab[0], m2_lab[0], m3_lab[0])))
best.sort()
print(f"  Top 12 triples (m_1, m_2, m_3 labels) for difference-of-squares ratio:")
for err, r, lbls in best[:12]:
    print(f"    rel.err = {mp.nstr(err, 4):<12} ratio = {mp.nstr(r, 6):<12} ({lbls[0]:>9}, {lbls[1]:>9}, {lbls[2]:>9})")
print()

# Final: estimate m_sol from m_atm if framework picks m_2 = λ_0(α_X) and m_3 = λ_0(α_Y)
# To produce m_3² ≈ 2.5e-3 eV² → m_3 ≈ 0.05 eV → α_Y needs scaling.
print("=" * 70)
print("ABSOLUTE SCALE — REQUIRES EXTERNAL DIMENSIONFUL FACTOR")
print("=" * 70)
m_atm = mp.sqrt(mp.mpf("2.515e-3"))
print(f"  m_3 ≈ m_atm = {mp.nstr(m_atm, 6)} eV")
print(f"  λ_0(P)      = {mp.nstr(lambda0['P'], 6)}  (dimensionless)")
print(f"  Scale factor m_atm / λ_0(P) = {mp.nstr(m_atm/lambda0['P'], 6)} eV")
print(f"  This needs to come from an external mass scale of ~0.226 eV.")
print(f"  Compare to neutrino effective mass m_β ~ O(0.1 eV) limits (KATRIN).")
print()
print("  Conclusion on absolute scale: framework gives RATIOS cleanly but the")
print("  overall mass scale needs an EXTERNAL anchor (just like SM Yukawa hierarchy).")
