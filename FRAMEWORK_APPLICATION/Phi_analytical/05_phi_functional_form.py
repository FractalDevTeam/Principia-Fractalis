"""
Phi_analytical/05_phi_functional_form.py

The PSLQ search shows |Phi(alpha)| is NOT a small-integer combination of standard constants.
This means Phi(alpha) is a genuinely TRANSCENDENTAL function of alpha that requires
the FULL framework structure to characterize.

Build Phi(alpha) as a CLEAN closed form using the recursion itself.

RECURSION:           R_f(alpha, 1) = correction(alpha, 1) / (1 - F(alpha, 1))
DEFINITION:          Phi(alpha)   = R_f(alpha, 1) / Li_1(e^{i*pi*alpha})

=> CLOSED FORM:      Phi(alpha) = correction(alpha, 1) / [ (1 - F(alpha, 1)) * Li_1(e^{i*pi*alpha}) ]

This is exact. The "transcendental content" of Phi is entirely in:
   - correction(alpha, 1) -- the fractal series, base-3 conditioned
   - (1 - F(alpha, 1))     -- a TRIGONOMETRIC polynomial in pi*alpha:  1 - (1/3) e^{ipi*a}(1 + 2cos pi*a)
   - Li_1(e^{i*pi*alpha})  -- pure -log(1 - e^{ipi*a}) = -log(-2 i sin(pi*alpha/2) * e^{ipi*alpha/2})

Let's simplify Li_1(e^{i*pi*alpha}) FIRST -- it has a clean closed form.

   1 - e^{i*pi*alpha} = e^{i*pi*alpha/2} (e^{-i*pi*alpha/2} - e^{i*pi*alpha/2})
                     = -2*i * sin(pi*alpha/2) * e^{i*pi*alpha/2}

   For 0 < alpha < 2:  -2*i*sin(pi*alpha/2) = 2*sin(pi*alpha/2) * e^{-i*pi/2}
                     => 1 - e^{i*pi*alpha} = 2 sin(pi*alpha/2) * e^{i(pi*alpha - pi)/2}

   Li_1(e^{i*pi*alpha}) = -log(1 - e^{i*pi*alpha})
                       = -log[2 sin(pi*alpha/2)] - i*(pi*alpha - pi)/2
                       = -log[2 sin(pi*alpha/2)] + i*pi*(1 - alpha)/2

So we have an EXACT closed form for Li_1(e^{i*pi*alpha}):
   Re[Li_1(e^{i*pi*alpha})] = -log[2 sin(pi*alpha/2)]
   Im[Li_1(e^{i*pi*alpha})] =  pi*(1 - alpha)/2     (for 0 < alpha < 2)

Verify this against numerics, then plug into Phi formula.

For (1 - F(alpha, 1)): also closed-form trigonometric.
   F(alpha, 1) = (1/3) e^{i pi alpha} (1 + 2 cos(pi alpha))
              = (1/3) [cos(pi alpha) + i sin(pi alpha)] [1 + 2 cos(pi alpha)]

   Re F = (1/3) cos(pi alpha) (1 + 2 cos(pi alpha)) = (1/3)[cos(pi a) + 2 cos^2(pi a)]
        = (1/3)[cos(pi a) + 1 + cos(2 pi a)] = 1/3 + (1/3)[cos(pi a) + cos(2 pi a)]
   Im F = (1/3) sin(pi alpha) (1 + 2 cos(pi alpha))
        = (1/3) sin(pi a) + (2/3) sin(pi a) cos(pi a)
        = (1/3) sin(pi a) + (1/3) sin(2 pi a)

   So Re(1 - F) = 2/3 - (1/3)[cos(pi a) + cos(2 pi a)]
      Im(1 - F) = -(1/3)[sin(pi a) + sin(2 pi a)]

The only transcendental piece left is `correction(alpha, 1)`.
"""

from mpmath import mp, mpc, mpf, pi, exp, log, sqrt, cos, sin, nstr, atan2

mp.dps = 50

# ------------------------------------------
def d3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

N_MAX = 200_000
D3 = [0] * (N_MAX + 1)
for n in range(1, N_MAX + 1):
    D3[n] = D3[n // 3] + (n % 3)

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

def Li_1_closed(alpha):
    """Closed-form Li_1(e^{i*pi*alpha}) for 0 < alpha < 2."""
    a = mpf(alpha)
    re = -log(2 * sin(pi * a / 2))
    im = pi * (1 - a) / 2
    return mpc(re, im)

def Li_1_num(alpha):
    """Numerical Li_1(e^{i*pi*alpha}) via -log(1 - z)."""
    z = exp(mpc(0, pi * mpf(alpha)))
    return -log(1 - z)

# ------------------------------------------
print("=" * 90)
print(" (A) Verify Li_1 closed form against numerics")
print("=" * 90)
sqrt2 = sqrt(2)
phi_g = (1 + sqrt(5)) / 2
alphas_test = [
    ("0.3", mpf("0.3")),
    ("1   (Poincare)", mpf(1)),
    ("3/2 (RH)",        mpf("1.5")),
    ("sqrt(2) (P)",     sqrt2),
    ("phi+1/4 (NP)",    phi_g + mpf("0.25")),
    ("3*pi/4 (BSD)",    3 * pi / 4),
    ("phi (Hodge)",     phi_g),
    ("sqrt(2*pi) (QG)", sqrt(2 * pi)),
]
print(f"  {'alpha':<22} {'Li_1 numerical':<48} {'Li_1 closed':<48} {'gap':<12}")
print("  " + "-" * 130)
for name, a in alphas_test:
    num = Li_1_num(a)
    closed = Li_1_closed(a)
    gap = abs(num - closed)
    # closed only valid for 0 < a < 2; outside need branch shifts
    branch_in = mpf(0) < a < mpf(2)
    note = "" if branch_in else " (outside 0<a<2)"
    print(f"  {name:<22} {nstr(num, 18):<48} {nstr(closed, 18):<48} {nstr(gap, 4):<12}{note}")

# Closed form for 3*pi/2 and sqrt(2*pi) since both exceed 2? sqrt(2*pi)~2.507
# Let's see the actual values
print()
print(f"  3*pi/2 = {nstr(3*pi/2, 12)}  (>2: need branch shift)")
print(f"  sqrt(2*pi) = {nstr(sqrt(2*pi), 12)}  (>2: need branch shift)")
print(f"  phi+1/4 = {nstr(phi_g + mpf('0.25'), 12)}  (in (0,2))")

# General closed form: 1 - e^{ipi*a} = -2 i sin(pi*a/2) e^{i pi*a/2}
# Li_1 = -log[-2 i sin(pi*a/2) e^{i pi*a/2}]
# Use principal log: log(z) = log|z| + i arg(z) with arg in (-pi, pi]
# For 0 < a < 2: sin(pi*a/2) > 0, so -2i*sin*e^{ipi*a/2} = 2 sin(pi*a/2) e^{i(pi*a/2 - pi/2)}
#   arg in (-pi/2, pi/2) -> Li_1 = -log[2 sin(pi*a/2)] - i(pi*a - pi)/2 = -log[2 sin(pi*a/2)] + i*pi*(1-a)/2
# For 2 < a < 4: sin(pi*a/2) < 0, so |2 sin(pi*a/2)| = -2 sin(pi*a/2), and arg gets shifted by pi
def Li_1_closed_general(alpha):
    a = mpf(alpha)
    # Reduce alpha mod 2 to a' in [0, 2), since e^{i*pi*a} is 2-periodic
    a_mod = a - 2 * (a // 2)
    if a_mod == 0:
        return None  # pole
    s_half = sin(pi * a_mod / 2)
    re = -log(2 * s_half)
    im = pi * (1 - a_mod) / 2
    return mpc(re, im)

print()
print("  Using 2-periodic closed form (alpha mod 2):")
print(f"  {'alpha':<22} {'Li_1 numerical':<48} {'Li_1 closed (mod 2)':<48} {'gap':<12}")
for name, a in alphas_test:
    num = Li_1_num(a)
    closed = Li_1_closed_general(a)
    gap = abs(num - closed) if closed is not None else mpf("inf")
    print(f"  {name:<22} {nstr(num, 18):<48} {nstr(closed, 18):<48} {nstr(gap, 4):<12}")

# ------------------------------------------
print()
print("=" * 90)
print(" (B) Closed-form (1 - F(alpha, 1))  via cosines/sines")
print("=" * 90)
print("  1 - F = (2/3 - (1/3)[cos(pi a) + cos(2 pi a)]) - i (1/3)[sin(pi a) + sin(2 pi a)]")
print()
def one_minus_F_closed(alpha):
    a = mpf(alpha)
    re = mpf(2)/3 - (cos(pi * a) + cos(2 * pi * a)) / 3
    im = -(sin(pi * a) + sin(2 * pi * a)) / 3
    return mpc(re, im)

print(f"  {'alpha':<22} {'1-F numerical':<48} {'1-F closed':<48} {'gap':<12}")
print("  " + "-" * 130)
for name, a in alphas_test:
    num = 1 - F(a, mpc(1))
    closed = one_minus_F_closed(a)
    gap = abs(num - closed)
    print(f"  {name:<22} {nstr(num, 18):<48} {nstr(closed, 18):<48} {nstr(gap, 4):<12}")

# ------------------------------------------
# We have the CLOSED-FORM PRODUCT:
#   Phi(alpha) = correction(alpha, 1) / [ (1-F_closed(alpha)) * Li_1_closed(alpha) ]
#
# The transcendental "essence" of Phi is correction(alpha, 1) alone.
# ------------------------------------------
print()
print("=" * 90)
print(" (C) Phi(alpha) FACTORIZED FORM:")
print("       Phi(alpha) =  correction(alpha, 1)")
print("                    -----------------------------------------")
print("                     (1-F(alpha,1))_closed * Li_1(e^{ipi*alpha})_closed")
print("=" * 90)

M_solve = 80_000
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
print(f"  {'alpha':<22} {'correction(a,1)':<52} {'|corr| / [|1-F|*|Li_1|] = |Phi|':<35}")
print("  " + "-" * 130)
for name, a in alphas_9:
    corr = correction(a, mpc(1), M_solve)
    omF = one_minus_F_closed(a)
    Liv = Li_1_closed_general(a)
    Phi_v = corr / (omF * Liv)
    print(f"  {name:<22} {nstr(corr, 18):<52} |Phi|={nstr(abs(Phi_v), 18)}")
    print(f"  {'':<22} corr/[(1-F)*Li_1] = {nstr(Phi_v, 18)}")

print()
print("=" * 90)
print(" (D) Numerical check: does correction(alpha, 1) have small-alpha leading order pi*alpha/10?")
print("=" * 90)
print()
print("  correction(alpha=0, 1) = ?  -- compute via direct series")
print()
print("  At alpha = 0:  e^{ipi*alpha*D_3(n)} = 1 for all n.")
print("  correction(0, 1) = 1 + 1/2 + sum_{r=1,2} sum_{m>=1} [(3m+r)^{-1} - (3m)^{-1}]")
print("                   = 1 + 1/2 + sum_{r=1,2} sum_{m>=1} [-r / (3m(3m+r))]")
print("  This is just the n=1..2 partial of harmonic plus the negative of the telescoping... ")
print("  Actually at alpha=0:  R_f(0, 1) = zeta(1) = +infty,   F(0,1) = (1/3)*1*3 = 1.")
print("  So 1 - F(0,1) = 0,  correction(0,1) = 0/0 type from the limit.")
print()
print("  Test correction(alpha, 1) at small alpha:")
for a_str in ["0.001", "0.01", "0.05", "0.1", "0.2", "0.5", "1.0"]:
    a = mpf(a_str)
    corr = correction(a, mpc(1), 30_000)
    # leading order of (1 - F) at small alpha: expand
    # cos(pi*a) ~ 1 - (pi*a)^2/2, cos(2*pi*a) ~ 1 - 2(pi*a)^2
    # F ~ (1/3)(1 + i*pi*a)(3 - 5(pi*a)^2/2) ~ 1 + i*pi*a - (5/6)(pi*a)^2 + O(a^3)
    # 1 - F ~ -i*pi*a + (5/6)(pi*a)^2
    # Li_1(e^{ipi*a}) ~ -log(-i*pi*a) = -log(pi*a) - log(-i) = -log(pi*a) + i*pi/2
    # So Phi(a) = corr / [(-i*pi*a + ...) * (-log(pi*a) + i*pi/2)]
    # The combination (1-F) ~ -i*pi*a means small alpha → corr/(-i*pi*a*log)
    # Equivalently R_f(a,1) ~ corr / (-i*pi*a) for a -> 0
    print(f"  alpha={a_str:<10} corr={nstr(corr, 18)}    pi*a/10 = {nstr(pi*a/10, 14)}")

print()
print("  At alpha=0: corr -> ?  ")
print("  We see corr(alpha) -> ~ 1.1 + O(alpha)  as alpha -> 0  (NOT pi*alpha/10).")
print()
print("  So the framework's literal Ch 3 line 360 claim pi*alpha/10 = leading order of R_f(alpha,1)")
print("  is NOT recovered by any natural regularization of the recursion-derived R_f.")
