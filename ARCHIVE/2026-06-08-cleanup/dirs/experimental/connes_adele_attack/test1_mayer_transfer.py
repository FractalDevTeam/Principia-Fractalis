"""
TEST 1: Mayer-Lewis-Zagier transfer operator T_s.

The Mayer transfer operator acts on holomorphic functions f(z) on the unit disc:
    (T_s f)(z) = sum_{n>=1} (z + n)^{-2s} * f(1/(z + n))

Its spectrum is connected to the Selberg zeta function and Riemann zeros.

We diagonalize T_s in a truncated monomial basis {z^k}_{k=0..N-1} (essentially
Taylor coefficients), computing the matrix element

    M_{jk}(s) = (1/k!) d^k/dz^k [ sum_n (z+n)^{-2s} * (1/(z+n))^j ] at z=0
              = sum_n  (1/k!) d^k/dz^k [ (z+n)^{-2s-j} ] at z=0
              = sum_n  binomial(-2s-j, k) * n^{-2s-j-k}
              = sum_n  binomial(-2s-j, k) * n^{-(2s+j+k)}
              = binomial(-2s-j, k) * zeta(2s + j + k)

with binomial(-a, k) = (-1)^k * binomial(a+k-1, k) = (-1)^k * Gamma(a+k)/(Gamma(a)*k!).
So
    M_{jk}(s) = (-1)^k * Gamma(2s + j + k) / (Gamma(2s + j) * k!) * zeta(2s + j + k).

We test for the framework's canonical alpha values whether |lambda_max(T_s)| or
any eigenvalue of T_s hits pi/(10*alpha) when s is chosen as:
    s = alpha/2 ,  s = 1/(2*alpha) ,  s = alpha , s = 1/alpha , s = pi/(20),
    s = sqrt(2)/2 , s = 1, s = 1/2 + i*14.134725 (first nontrivial RH zero).
"""

import mpmath as mp
mp.mp.dps = 50

PI = mp.pi
TARGET = lambda a: PI / (10 * a)

# Framework canonical alpha values
ALPHAS = {
    "alpha_P=sqrt(2)":     mp.sqrt(2),
    "alpha_NP=phi+1/4":    (1 + mp.sqrt(5))/2 + mp.mpf(1)/4,
    "alpha_Hodge=phi":     (1 + mp.sqrt(5))/2,
    "alpha_NS=3pi/2":      3*PI/2,
    "alpha_YM=2":          mp.mpf(2),
    "alpha_BSD=3pi/4":     3*PI/4,
    "alpha_QG=sqrt(2pi)":  mp.sqrt(2*PI),
}


def mayer_matrix(s, N):
    """Build N x N Mayer transfer matrix in monomial basis."""
    M = mp.matrix(N, N)
    for j in range(N):
        for k in range(N):
            a = 2*s + j
            # (-1)^k * Gamma(a+k) / (Gamma(a)*k!) * zeta(a+k)
            coef = mp.power(-1, k) * mp.gamma(a + k) / (mp.gamma(a) * mp.factorial(k))
            M[j, k] = coef * mp.zeta(a + k)
    return M


def eig_spectrum(s, N=24):
    """Return sorted (by |.|, descending) eigenvalues of T_s."""
    M = mayer_matrix(s, N)
    eigs = mp.eig(M, right=False, left=False)
    # Sort by |.| descending
    eigs_sorted = sorted(eigs, key=lambda z: -abs(z))
    return eigs_sorted


def closest_to_target(eigs, target):
    """Return (eigenvalue, distance) of eigenvalue nearest to target on the real line."""
    best = min(eigs, key=lambda z: abs(z - target))
    return best, abs(best - target)


def closest_to_real_target(eigs, target):
    """Compare |eig - target| on REAL part only (target is a real number)."""
    best = min(eigs, key=lambda z: abs(mp.re(z) - target))
    return best, abs(mp.re(best) - target)


print("="*78)
print("TEST 1: MAYER TRANSFER OPERATOR")
print("="*78)
print(f"\nUsing basis dim N = 24, mpmath dps = {mp.mp.dps}\n")

# Sanity check: at s=1, T_s should have eigenvalue 1 (Mayer's theorem)
print("Sanity: T_{s=1} should have eigenvalue +1 (Mayer's RH equivalence).")
eigs_s1 = eig_spectrum(mp.mpf(1), N=24)
print(f"  Top 5 eigenvalues |.|: {[mp.nstr(abs(e), 8) for e in eigs_s1[:5]]}")
print(f"  Top 3 eigenvalues:     {[mp.nstr(e, 8) for e in eigs_s1[:3]]}")
near1 = min(eigs_s1, key=lambda z: abs(z - 1))
print(f"  Closest to +1:         {mp.nstr(near1, 12)}   dist = {mp.nstr(abs(near1-1), 4)}")
near_m1 = min(eigs_s1, key=lambda z: abs(z + 1))
print(f"  Closest to -1:         {mp.nstr(near_m1, 12)}  dist = {mp.nstr(abs(near_m1+1), 4)}")

# Test framework's alpha values with various s scalings
print("\n" + "-"*78)
print("FRAMEWORK ALPHA TEST: do any T_s eigenvalues hit pi/(10*alpha)?")
print("-"*78)

results = []
s_recipes = [
    ("s=alpha/2",   lambda a: a/2),
    ("s=1/(2a)",    lambda a: 1/(2*a)),
    ("s=alpha",     lambda a: a),
    ("s=1/alpha",   lambda a: 1/a),
    ("s=pi/20",     lambda a: PI/20),
    ("s=sqrt(2)/2", lambda a: mp.sqrt(2)/2),
    ("s=1",         lambda a: mp.mpf(1)),
]

for aname, aval in ALPHAS.items():
    tgt = TARGET(aval)
    print(f"\nAlpha = {aname} = {mp.nstr(aval,10)}, target pi/(10a) = {mp.nstr(tgt,10)}")
    for sname, sf in s_recipes:
        s = sf(aval)
        # Skip s with real part <= 0.5 if it would be singular (zeta poles)
        if abs(mp.re(s)) < 0.05 and abs(mp.im(s)) < 0.05:
            continue
        try:
            eigs = eig_spectrum(s, N=20)
            best_real, dist_real = closest_to_real_target(eigs, tgt)
            print(f"  {sname:14s}: s={mp.nstr(s,8):20s}  best Re(eig)={mp.nstr(mp.re(best_real),8):14s}  dist={mp.nstr(dist_real,3)}")
            results.append((aname, sname, float(dist_real)))
        except Exception as e:
            print(f"  {sname:14s}: FAILED ({e})")

# Test at first Riemann zero
print("\n" + "-"*78)
print("RH ZERO TEST: T_s at s = 1/2 + i*14.1347 — should have eig = 1.")
print("-"*78)
s_rh = mp.mpc(mp.mpf("0.5"), mp.mpf("14.134725141734693790457251983562470270784257115699"))
try:
    eigs_rh = eig_spectrum(s_rh, N=22)
    near1 = min(eigs_rh, key=lambda z: abs(z - 1))
    print(f"  Closest to 1: {mp.nstr(near1,10)}  |dist|={mp.nstr(abs(near1-1),4)}")
    # If RH first-zero eigenvalue ~ 1 confirms operator basics, then search for target
    for aname, aval in ALPHAS.items():
        tgt = TARGET(aval)
        best_re, dist_re = closest_to_real_target(eigs_rh, tgt)
        print(f"  {aname:25s} target={mp.nstr(tgt,6):10s} best Re(eig)={mp.nstr(mp.re(best_re),6):10s} dist={mp.nstr(dist_re,3)}")
except Exception as e:
    print(f"  FAILED ({e})")

# Final summary
print("\n" + "="*78)
print("MAYER TRANSFER SUMMARY")
print("="*78)
if results:
    results.sort(key=lambda x: x[2])
    print("\nTop 10 closest matches across all (alpha, s) combinations:")
    for r in results[:10]:
        print(f"  {r[0]:24s} {r[1]:14s} dist={r[2]:.6e}")
    best = results[0]
    print(f"\nBest match: alpha={best[0]}, s-recipe={best[1]}, dist={best[2]:.4e}")
    if best[2] < 1e-3:
        print("VERDICT: Plausible match (sub-1e-3).")
    elif best[2] < 1e-2:
        print("VERDICT: Marginal proximity (1e-3 to 1e-2) — not a tight hit.")
    else:
        print("VERDICT: NO MATCH. No (alpha, s) pair produces pi/(10*alpha) as a Mayer eigenvalue.")
