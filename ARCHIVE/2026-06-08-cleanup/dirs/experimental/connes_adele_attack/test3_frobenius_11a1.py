"""
TEST 3: Frobenius eigenvalues for the elliptic curve 11a1.

For an elliptic curve E over Q, the trace of Frobenius at a prime p of good
reduction is a_p = p + 1 - #E(F_p). The Frobenius eigenvalues are the roots of
    x^2 - a_p * x + p = 0
giving alpha_p, beta_p = (a_p +/- sqrt(a_p^2 - 4p)) / 2.

By Hasse: |a_p| <= 2*sqrt(p), so a_p / (2*sqrt(p)) is in [-1, 1] — these are
the "Sato-Tate normalized" Frobenius eigenvalues.

The elliptic curve 11a1: y^2 + y = x^3 - x^2 - 10 x - 20  (Cremona label 11a1,
the smallest conductor elliptic curve).

Known a_p for 11a1: a_2=-2, a_3=-1, a_5=1, a_7=-2, a_11=1(*bad), a_13=4,
a_17=-2, a_19=0, a_23=-1, a_29=0, a_31=7, a_37=3, a_41=-8, a_43=-6, a_47=8,
a_53=-6, a_59=5, a_61=12, a_67=-7, a_71=-3, a_73=4, a_79=-10, a_83=-6,
a_89=15, a_97=-7

(From LMFDB.)
"""

import mpmath as mp
mp.mp.dps = 50

PI = mp.pi
TARGET = lambda a: PI / (10 * a)

ALPHAS = {
    "alpha_P=sqrt(2)":     mp.sqrt(2),
    "alpha_NP=phi+1/4":    (1 + mp.sqrt(5))/2 + mp.mpf(1)/4,
    "alpha_Hodge=phi":     (1 + mp.sqrt(5))/2,
    "alpha_NS=3pi/2":      3*PI/2,
    "alpha_YM=2":          mp.mpf(2),
    "alpha_BSD=3pi/4":     3*PI/4,
    "alpha_QG=sqrt(2pi)":  mp.sqrt(2*PI),
}

# a_p for elliptic curve 11a1 (Cremona)
AP_11A1 = {
    2: -2,  3: -1,  5: 1,   7: -2,   13: 4,
    17: -2, 19: 0,  23: -1, 29: 0,   31: 7,
    37: 3,  41: -8, 43: -6, 47: 8,   53: -6,
    59: 5,  61: 12, 67: -7, 71: -3,  73: 4,
    79: -10,83: -6, 89: 15, 97: -7,
}

# Compute Frobenius eigenvalues
print("="*78)
print("TEST 3: FROBENIUS EIGENVALUES FOR ELLIPTIC CURVE 11a1")
print("="*78)
print("\nFrobenius eigenvalues alpha_p (complex), |alpha_p| = sqrt(p),")
print("plus normalized angle phi_p where alpha_p = sqrt(p) * exp(i*phi_p).\n")

frob = []
for p, ap in sorted(AP_11A1.items()):
    a = mp.mpf(ap)
    p_mp = mp.mpf(p)
    disc = a**2 - 4*p_mp
    if disc < 0:
        sd = mp.sqrt(-disc)
        alpha = (a + mp.mpc(0, sd)) / 2
        beta = (a - mp.mpc(0, sd)) / 2
    else:
        sd = mp.sqrt(disc)
        alpha = (a + sd) / 2
        beta = (a - sd) / 2
    norm_a = alpha / mp.sqrt(p_mp)
    # Sato-Tate angle: alpha_p = sqrt(p) * e^(i*phi), so phi = arg(alpha)
    if disc < 0:
        phi = mp.atan2(mp.im(alpha), mp.re(alpha))
        cos_phi = a / (2 * mp.sqrt(p_mp))
    else:
        phi = mp.mpf(0)
        cos_phi = mp.re(alpha) / mp.sqrt(p_mp)
    frob.append({
        'p': p, 'ap': ap, 'alpha': alpha, 'beta': beta,
        'norm_alpha': norm_a, 'phi': phi, 'cos_phi': cos_phi,
        'abs_alpha': abs(alpha)
    })
    print(f"  p={p:3d} a_p={ap:>4d}  |alpha|={mp.nstr(abs(alpha),6):>8s}  "
          f"a_p/sqrt(p)={mp.nstr(a/mp.sqrt(p_mp),6):>10s}  "
          f"alpha/sqrt(p)={mp.nstr(norm_a,6)}")

# Test if alpha values match alpha_p / sqrt(p) (the normalized eigenvalue)
# Note: |alpha_p/sqrt(p)| = 1 by Hasse, so REAL alpha cannot equal alpha_p/sqrt(p)
# unless alpha = +/-1. Framework alphas are > 1 in many cases — they CANNOT be
# normalized Frobenius eigenvalues. But let's check |a_p|/sqrt(p) = 2*cos(phi_p).

print("\n" + "-"*78)
print("Hasse parameter 2*cos(phi_p) = a_p/sqrt(p) — does any framework value match?")
print("(Note: 2*cos(phi_p) is in [-2,2], so only alpha in [-2,2] can match.)")
print("-"*78)

results = []
for aname, aval in ALPHAS.items():
    if aval > 2 or aval < -2:
        print(f"  alpha={aname:25s} value={mp.nstr(aval,6)} OUT OF SATO-TATE RANGE — skip")
        continue
    # 2*cos(phi_p) = a_p/sqrt(p)
    best_p, best_dist = None, mp.mpf("inf")
    for f in frob:
        val = mp.mpf(f['ap']) / mp.sqrt(f['p'])
        d = abs(val - aval)
        if d < best_dist:
            best_dist = d
            best_p = f['p']
    print(f"  alpha={aname:25s} value={mp.nstr(aval,8):>10s} closest p={best_p:3d} dist={mp.nstr(best_dist,3)}")
    results.append((aname, "alpha vs a_p/sqrt(p)", float(best_dist)))

print("\n" + "-"*78)
print("Does pi/(10*alpha) match any a_p/sqrt(p) Sato-Tate value?")
print("-"*78)

for aname, aval in ALPHAS.items():
    tgt = TARGET(aval)
    best_p, best_dist = None, mp.mpf("inf")
    for f in frob:
        val = mp.mpf(f['ap']) / mp.sqrt(f['p'])
        d = abs(val - tgt)
        if d < best_dist:
            best_dist = d
            best_p = f['p']
    print(f"  pi/(10*{aname}) target={mp.nstr(tgt,8):>10s} closest p={best_p:3d} dist={mp.nstr(best_dist,3)}")
    results.append((aname, "pi/(10a) vs a_p/sqrt(p)", float(best_dist)))

# Also test: does pi/(10*alpha) match cos(phi_p) directly? (a_p/(2*sqrt(p)))
print("\n" + "-"*78)
print("Does pi/(10*alpha) match cos(phi_p) = a_p/(2*sqrt(p))?")
print("-"*78)
for aname, aval in ALPHAS.items():
    tgt = TARGET(aval)
    best_p, best_dist = None, mp.mpf("inf")
    for f in frob:
        val = mp.mpf(f['ap']) / (2 * mp.sqrt(f['p']))
        d = abs(val - tgt)
        if d < best_dist:
            best_dist = d
            best_p = f['p']
    print(f"  pi/(10*{aname}) target={mp.nstr(tgt,8):>10s} closest p={best_p:3d} dist={mp.nstr(best_dist,3)}")
    results.append((aname, "pi/(10a) vs cos(phi_p)", float(best_dist)))

print("\n" + "="*78)
print("FROBENIUS SUMMARY")
print("="*78)
results.sort(key=lambda x: x[2])
print("\nTop 10 closest matches:")
for r in results[:10]:
    print(f"  {r[0]:24s} {r[1]:30s} dist={r[2]:.6e}")
best = results[0]
print(f"\nBest match: {best[0]}, {best[1]}, dist={best[2]:.4e}")
if best[2] < 1e-3:
    print("VERDICT: Plausible numerical coincidence.")
elif best[2] < 1e-2:
    print("VERDICT: Marginal proximity but not a tight algebraic match.")
else:
    print("VERDICT: NO MATCH.")
