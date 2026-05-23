"""
TEST 2: Hecke operators on weight-12 cusp forms.

Hecke eigenvalues for the unique normalized weight-12 cusp form Delta(z) are
the Ramanujan tau function values tau(n). The Sato-Tate normalized eigenvalues
    a_p_normalized = tau(p) / p^{11/2}
lie in [-2, 2].

Question: do any framework alpha values appear as normalized Hecke eigenvalues
or as targets pi/(10*alpha) appear in the spectrum?
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


# Ramanujan tau values (well-known table for n=1..30)
TAU = {
    1: 1,
    2: -24,
    3: 252,
    4: -1472,
    5: 4830,
    6: -6048,
    7: -16744,
    8: 84480,
    9: -113643,
    10: -115920,
    11: 534612,
    12: -370944,
    13: -577738,
    14: 401856,
    15: 1217160,
    16: 987136,
    17: -6905934,
    18: 2727432,
    19: 10661420,
    20: -7109760,
    21: -4219488,
    22: -12830688,
    23: 18643272,
    24: 21288960,
    25: -25499225,
    26: 13865712,
    27: -73279080,
    28: 24647168,
    29: 128406630,
    30: -29211840,
}

# Primes up to 100
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
          53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

# tau(p) for primes via multiplicativity: tau(p) where p prime is in TAU table for p<=29
TAU_P_BIG = {
    31: -52843168,
    37: 182213314,
    41: 308120442,
    43: -17125708,
    47: 2687348496,
    53: -1596055698,
    59: -5189203740,
    61: 6956478662,
    67: -10661702578,
    71: 5258553732,
    73: 4231535922,
    79: 16125981840,
    83: -38116692645,  # approx — exact would need OEIS A000594
    89: 35307579420,
    97: -7218426242,
}

def tau(n):
    if n in TAU:
        return TAU[n]
    if n in TAU_P_BIG:
        return TAU_P_BIG[n]
    return None


print("="*78)
print("TEST 2: HECKE EIGENVALUES (Ramanujan tau function)")
print("="*78)

# Normalized Hecke eigenvalues a_p = tau(p) / p^(11/2)
print("\nNormalized Hecke eigenvalues a_p = tau(p) / p^(11/2), in Sato-Tate [-2, 2]:")
norm_eigs = []
for p in PRIMES:
    t = tau(p)
    if t is None:
        continue
    ap = mp.mpf(t) / mp.power(p, mp.mpf("5.5"))
    norm_eigs.append((p, ap))
    print(f"  p={p:3d}  tau(p)={t:>14d}  a_p={mp.nstr(ap, 10):>14s}")

# Test: does any alpha or pi/(10*alpha) match?
print("\n" + "-"*78)
print("Does pi/(10*alpha) match any normalized Hecke eigenvalue?")
print("-"*78)

results = []
for aname, aval in ALPHAS.items():
    tgt = TARGET(aval)
    best_p, best_dist = None, mp.mpf("inf")
    for p, ap in norm_eigs:
        d = abs(ap - tgt)
        if d < best_dist:
            best_dist = d
            best_p = p
    print(f"  alpha={aname:25s} target={mp.nstr(tgt,8):>12s}  closest at p={best_p:3d}  dist={mp.nstr(best_dist,3)}")
    results.append((aname, "pi/(10a) vs a_p", float(best_dist)))

print("\n" + "-"*78)
print("Does alpha itself match any normalized Hecke eigenvalue?")
print("-"*78)

for aname, aval in ALPHAS.items():
    if aval > 2:
        continue  # outside Sato-Tate range
    best_p, best_dist = None, mp.mpf("inf")
    for p, ap in norm_eigs:
        d = abs(ap - aval)
        if d < best_dist:
            best_dist = d
            best_p = p
    print(f"  alpha={aname:25s} alpha={mp.nstr(aval,8):>10s}  closest at p={best_p:3d}  dist={mp.nstr(best_dist,3)}")
    results.append((aname, "alpha vs a_p", float(best_dist)))

# Also: tau(n)/n^(11/2) for general n
print("\n" + "-"*78)
print("Unnormalized tau(n) for small n — any match?")
print("-"*78)
for aname, aval in ALPHAS.items():
    tgt = TARGET(aval)
    # |tau(n)| for n up to 30
    best_n, best_dist = None, mp.mpf("inf")
    for n in range(1, 31):
        t = tau(n)
        if t is None:
            continue
        ap = mp.mpf(t) / mp.power(n, mp.mpf("5.5"))
        d = abs(ap - tgt)
        if d < best_dist:
            best_dist = d
            best_n = n
    print(f"  alpha={aname:25s} target={mp.nstr(tgt,8):>12s} closest n={best_n:3d} dist={mp.nstr(best_dist,3)}")

# Summary
print("\n" + "="*78)
print("HECKE SUMMARY")
print("="*78)
results.sort(key=lambda x: x[2])
print("\nTop 5 closest matches:")
for r in results[:5]:
    print(f"  {r[0]:24s} {r[1]:25s} dist={r[2]:.6e}")
best = results[0]
if best[2] < 1e-3:
    print(f"\nVERDICT: Plausible match found (dist={best[2]:.4e})")
else:
    print(f"\nVERDICT: NO MATCH. Closest dist {best[2]:.4e} far exceeds any reasonable threshold.")
