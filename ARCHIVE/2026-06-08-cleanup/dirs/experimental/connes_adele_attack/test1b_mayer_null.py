"""
TEST 1b: Null control for Mayer transfer operator best match.

The Mayer test produced a single sub-1e-3 hit:
    alpha_YM = 2, s = sqrt(2)/2, |eig - pi/20| = 2.45e-4

But the Mayer operator at s = sqrt(2)/2 has DOZENS of eigenvalues spread across
the real interval — we need to check whether a randomly-chosen target in that
range has comparable likelihood of being within 2.45e-4 of an eigenvalue.

Null protocol:
- Fix s = sqrt(2)/2
- Compute full eigenvalue list at N=24
- Restrict to real eigenvalues in [-2, 2] (the dense regime)
- Draw 10000 uniform random targets in [0.02, 0.5]
- Distribution of nearest-eigenvalue distance gives the null
- Compare framework target pi/(10*alpha) for each alpha to this null
"""

import mpmath as mp
import numpy as np
mp.mp.dps = 40  # slightly lower for speed

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


def mayer_matrix(s, N):
    M = mp.matrix(N, N)
    for j in range(N):
        for k in range(N):
            a = 2*s + j
            coef = mp.power(-1, k) * mp.gamma(a + k) / (mp.gamma(a) * mp.factorial(k))
            M[j, k] = coef * mp.zeta(a + k)
    return M


def eig_spectrum(s, N=24):
    M = mayer_matrix(s, N)
    eigs = mp.eig(M, right=False, left=False)
    return [complex(e) for e in eigs]


print("="*78)
print("TEST 1b: NULL CONTROL FOR MAYER BEST MATCH (alpha_YM at s=sqrt(2)/2)")
print("="*78)

s = mp.sqrt(2)/2
print(f"\ns = sqrt(2)/2 = {float(s):.10f}")
eigs = eig_spectrum(s, N=24)
re_eigs = np.array([e.real for e in eigs])
print(f"Total eigenvalues: {len(eigs)}")
print(f"Real parts (sorted by |.|): {sorted(re_eigs, key=lambda x: abs(x))[:15]}")
print(f"Eigenvalues in [0, 1]: {sum(1 for e in re_eigs if 0 <= e <= 1)}")
print(f"Eigenvalues in [-1, 1]: {sum(1 for e in re_eigs if -1 <= e <= 1)}")

# Restrict to "small" eigenvalues where targets live
small = re_eigs[(re_eigs >= -0.5) & (re_eigs <= 1.0)]
print(f"\nEigenvalues in [-0.5, 1.0]: {len(small)}")
print(f"They are: {sorted(small)}")

# Null distribution: 10000 random targets in [0.02, 0.5]
rng = np.random.default_rng(seed=7777)
null_targets = rng.uniform(0.02, 0.5, size=10000)
null_dists = []
for t in null_targets:
    d = min(abs(re - t) for re in re_eigs)
    null_dists.append(d)
null_dists = np.array(null_dists)

print(f"\nNULL DISTRIBUTION (10000 random targets in [0.02, 0.5]):")
print(f"  Median dist: {np.median(null_dists):.4e}")
print(f"  Mean dist:   {np.mean(null_dists):.4e}")
print(f"  5th pct:     {np.percentile(null_dists, 5):.4e}")
print(f"  1st pct:     {np.percentile(null_dists, 1):.4e}")
print(f"  0.5th pct:   {np.percentile(null_dists, 0.5):.4e}")
print(f"  0.1th pct:   {np.percentile(null_dists, 0.1):.4e}")

print(f"\nFRAMEWORK TARGETS vs null distribution:")
print(f"{'alpha':25s} {'target':>12s} {'best |eig-tgt|':>16s} {'null %ile':>12s}")
print("-"*78)
for aname, aval in ALPHAS.items():
    tgt = float(TARGET(aval))
    if tgt < 0.02 or tgt > 0.5:
        print(f"{aname:25s} {tgt:>12.6f}  (out of test range)")
        continue
    d = min(abs(re - tgt) for re in re_eigs)
    pct = (null_dists <= d).mean() * 100
    print(f"{aname:25s} {tgt:>12.6f} {d:>16.4e} {pct:>11.2f}%")

# Honest verdict
print("\n" + "="*78)
print("HONEST VERDICT")
print("="*78)
print("""
The match alpha_YM = 2 -> pi/20 = 0.15708, eigenvalue 0.15732 (dist 2.45e-4)
must be assessed against the null distribution. If many random targets in the
same range achieve sub-1e-3 distances, the 'match' is COINCIDENTAL — there are
simply many eigenvalues in the relevant range, so any target has a high prior
probability of being close to one.

The Mayer operator at s = sqrt(2)/2 has approximately 24 eigenvalues spread
over a range of order [-X, +X]. The expected nearest-neighbor distance for a
random target is ~range/(2*N), and the probability of getting within d of any
eigenvalue is ~2*N*d/range. For d=2.45e-4 with ~24 eigenvalues over a range
of order 1, P(coincidence) ~ 2 * 24 * 2.45e-4 ~ 1.2% — NOT a strong signal.

The framework's other alpha values produced no match below ~3e-3 at any s
recipe tested. No (alpha, s) combination produced pi/(10*alpha) as a sharp
Mayer eigenvalue.
""")
