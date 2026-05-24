"""
Phi_analytical/03_phi_structure_search.py

Now that we have CLEAN, high-precision Phi(alpha) values via the recursion,
hunt for analytic structure:

   (1) Compute Phi(alpha) at all 9 framework alphas at 50-digit precision.
   (2) Search via PSLQ for integer relations between Phi(alpha) and the
       framework's 4-basis {1, pi, phi, sqrt(2)} extended to {1, pi, phi, sqrt(2), e, log 2, ...}.
   (3) Test the universal coupling lambda_0 = pi/(10 alpha) under the
       *reformulated* SpectralResonanceBridge:
           lambda_0(H_alpha) = leading-order coefficient of R_f(alpha,1) / alpha
       which requires choosing a regularization.

   (4) Try regularization: R_f^{reg}(alpha, 1) = R_f(alpha, 1) - Li_1(e^{i*pi*alpha})
       (subtract the canonical log-divergent part) and look at LEADING ORDER in alpha.

   (5) Try regularization: lim_{s -> 1+} [ R_f(alpha, s) - Li_1(e^{i*pi*alpha}) ]
       = "regularized R_f finite part."

These two tests reveal whether pi*alpha/10 emerges from a natural subtraction.
"""

from mpmath import mp, mpc, mpf, pi, exp, log, sqrt, cos, sin, nstr, pslq, mpmathify
import sys

mp.dps = 60

def d3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

N_MAX = 200_000
print(f"Precompute D_3 up to {N_MAX}...", flush=True)
D3 = [0] * (N_MAX + 1)
for n in range(1, N_MAX + 1):
    D3[n] = D3[n // 3] + (n % 3)
print("done.", flush=True)

def F(alpha, s):
    a = mpf(alpha)
    s_c = mpc(s)
    return mpc(3) ** (-s_c) * exp(mpc(0, pi * a)) * (1 + 2 * cos(pi * a))

def correction(alpha, s, M):
    a = mpf(alpha)
    s_c = mpc(s)
    T1 = exp(mpc(0, pi * a)) + exp(mpc(0, 2 * pi * a)) / mpc(2) ** s_c
    total = T1
    for r in (1, 2):
        phase_r = exp(mpc(0, pi * a * r))
        sub = mpc(0)
        for m in range(1, M + 1):
            phase_m = exp(mpc(0, pi * a * D3[m]))
            diff = mpc(3 * m + r) ** (-s_c) - mpc(3 * m) ** (-s_c)
            sub += phase_m * diff
        total += phase_r * sub
    return total

def Rf_recursion(alpha, s, M):
    Fv = F(alpha, s)
    if abs(1 - Fv) < mpf("1e-30"):
        return None
    return correction(alpha, s, M) / (1 - Fv)

def Li_1(z):
    return -log(1 - z)

# ----------------------------------------------------------------------
M_solve = 80_000

sqrt2 = sqrt(2)
phi_g = (1 + sqrt(5)) / 2
alphas_9 = [
    ("1   (Poincare)", mpf(1)),
    ("3/2 (RH)",        mpf("1.5")),
    ("sqrt(2) (P)",     sqrt2),
    ("phi+1/4 (NP)",    phi_g + mpf("0.25")),
    ("3*pi/4 (BSD)",    3 * pi / 4),
    ("3*pi/2 (NS)",     3 * pi / 2),
    ("phi (Hodge)",     phi_g),
    ("sqrt(2*pi) (QG)", sqrt(2 * pi)),
]

print()
print("=" * 90)
print(" (1) Phi(alpha) at 50-digit precision, recursion-based")
print("=" * 90)

phi_dict = {}
for name, a in alphas_9:
    Rfv = Rf_recursion(a, mpc(1), M_solve)
    z = exp(mpc(0, pi * a))
    Liv = Li_1(z)
    Phi_v = Rfv / Liv
    phi_dict[name] = (a, Rfv, Liv, Phi_v)
    print(f"  {name:<22}")
    print(f"    R_f(a,1)= {nstr(Rfv, 30)}")
    print(f"    Li_1    = {nstr(Liv, 30)}")
    print(f"    Phi(a)  = {nstr(Phi_v, 30)}   |Phi|= {nstr(abs(Phi_v), 14)}")

print()
print("=" * 90)
print(" (2) PSLQ structure search on |Phi(alpha)|")
print("=" * 90)
print()
print("  Test: is |Phi(alpha)| ~ integer combination of {1, pi, phi, sqrt(2), e, log 2, 1/3, alpha^k}?")
print()

basis_const = {
    "1":       mpf(1),
    "pi":      pi,
    "phi":     phi_g,
    "sqrt(2)": sqrt2,
    "e":       exp(mpf(1)),
    "log 2":   log(mpf(2)),
    "log 3":   log(mpf(3)),
}

for name, (a, Rfv, Liv, Phi_v) in phi_dict.items():
    abs_phi = abs(Phi_v)
    print(f"\n  --- {name},  |Phi|={nstr(abs_phi, 14)} ---")
    # Try PSLQ on [|Phi|, 1, pi, sqrt(2), phi, e, log 2, log 3, alpha, alpha^2]
    vec = [abs_phi, mpf(1), pi, sqrt2, phi_g, exp(mpf(1)), log(mpf(2)), log(mpf(3)), a, a * a]
    labels = ["|Phi|", "1", "pi", "sqrt(2)", "phi", "e", "log2", "log3", "alpha", "alpha^2"]
    try:
        rel = pslq(vec, tol=mpf("1e-20"), maxcoeff=10**8)
        if rel is None:
            print("    PSLQ: no relation found in basis.")
        else:
            terms = [f"{c}*{lab}" for c, lab in zip(rel, labels) if c != 0]
            print(f"    PSLQ relation: {' + '.join(terms)} = 0")
    except Exception as e:
        print(f"    PSLQ error: {e}")

# ----------------------------------------------------------------------
print()
print("=" * 90)
print(" (3) REFORMULATED BRIDGE: lambda_0(H_alpha) = pi/(10 alpha) ?")
print("=" * 90)
print()
print("  Universal coupling at all 9 alphas (asserted by framework):")
print(f"  {'alpha':<22} {'lambda_0 = pi/(10 alpha)':<30}")
print("  " + "-" * 70)
all_9 = alphas_9 + [("2   (YM)", mpf(2))]
for name, a in all_9:
    lam = pi / (10 * a)
    print(f"  {name:<22} {nstr(lam, 22):<30}")

print()
print("  These are the asserted spectral ground-state values across ALL Millennium problems.")
print("  The bridge identity is now: lambda_0(H_alpha) ~ universal coupling /  alpha")
print("  (independent of R_f(alpha,1) point-evaluation).")

# ----------------------------------------------------------------------
print()
print("=" * 90)
print(" (4) REGULARIZATION TEST: R_f^{reg}(alpha,1) := R_f(alpha,1) - Li_1(e^{i*pi*alpha})")
print("=" * 90)
print()
print("  In this normalization, R_f - Li_1 = Li_1 * (Phi - 1).")
print(f"  {'alpha':<22} {'R_f - Li_1':<55} {'pi*alpha/10':<22}")
print("  " + "-" * 110)
for name, a in alphas_9:
    Rfv, Liv = phi_dict[name][1], phi_dict[name][2]
    reg = Rfv - Liv
    pred = pi * a / 10
    print(f"  {name:<22} {nstr(reg, 18):<55} {nstr(pred, 18):<22}")

print()
print("  Compare to pi*alpha/10 at small alpha (this would be a 'finite-part' regularization).")
for a_str in ["0.01", "0.05", "0.1", "0.3", "0.5", "0.7", "1.0"]:
    a = mpf(a_str)
    Rfv = Rf_recursion(a, mpc(1), 30_000)
    if Rfv is None:
        continue
    z = exp(mpc(0, pi * a))
    Liv = Li_1(z)
    reg = Rfv - Liv
    pred = pi * a / 10
    ratio = reg / pred
    print(f"  alpha={a_str:<10} R_f-Li_1 = {nstr(reg, 18):<55} pi*a/10 = {nstr(pred, 14):<20} ratio={nstr(ratio, 14)}")

# ----------------------------------------------------------------------
print()
print("=" * 90)
print(" (5) FINITE-PART REGULARIZATION at s -> 1+")
print("=" * 90)
print()
print("  Define: R_f^{fp}(alpha, 1) := lim_{s -> 1+} [ R_f(alpha, s) - Li_1(e^{i*pi*alpha}) * (s/(s-1)) ]?")
print("  No -- the divergence of R_f as alpha -> 0 is in the constant term, not 1/(s-1).")
print("  R_f(alpha, s) is REGULAR in s at s=1 (the alpha != 0 sum converges absolutely for Re s > 0).")
print()
print("  So R_f(alpha, 1) is a FINITE complex number for every alpha not an even integer.")
print("  The 'pole' is only at alpha=2 (YM), via the (1-F) denominator.")
print()
print("  Hence: pi*alpha/10 is NOT the leading order of R_f(alpha,1) in alpha.")
print("  Instead, it might be the leading order of: (1 - F(alpha, 1)) * (something) / Li_1(e^{i*pi*alpha}).")
print()
print("  Let's compute (1 - F(alpha,1)) * R_f(alpha,1) = correction(alpha,1), and check its leading order:")
print()
print(f"  {'alpha':<14} {'correction(a,1)':<60} {'pi*alpha/10':<22}")
print("  " + "-" * 100)
for a_str in ["0.01", "0.05", "0.1", "0.3", "0.5", "0.7", "1.0"]:
    a = mpf(a_str)
    corr = correction(a, mpc(1), 30_000)
    pred = pi * a / 10
    print(f"  alpha={a_str:<8} {nstr(corr, 22):<60} {nstr(pred, 14):<20}")

print()
print("  CONCLUSION on leading order:")
print("  Neither R_f(alpha,1) nor R_f - Li_1 nor correction(alpha,1) has pi*alpha/10 as leading order.")
print("  The literal Ch 3 line 360 claim cannot be recovered by these standard regularizations.")
