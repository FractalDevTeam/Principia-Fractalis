"""
Phi_analytical/02_phi_closed_form.py

GOAL: With recursion-solved R_f(alpha, 1) values in hand, characterize
        Phi(alpha) = R_f(alpha, 1) / Li_1(e^{i*pi*alpha})
analytically, and test small-alpha expansion.

Strategy:
   (A) Compute Phi(alpha) using the recursion-derived R_f, not direct sum.
       (Much faster convergence; we showed the recursion is accurate to ~1e-4 with M=40000.)
   (B) Verify Phi(1) = 1 analytically using R_f(1,1) = -log 2 = Li_1(-1).
   (C) Tabulate Phi at all 9 framework instances, with the cleaner R_f values.
   (D) Test small-alpha expansion:
         R_f(alpha, 1) = ? + ? * alpha + ?* alpha^2 + ...
       Try multiple regularizations.

The framework PREDICTS: leading order is pi*alpha/10.
We'll test whether ANY natural regularization makes this true.
"""
from mpmath import mp, mpc, mpf, pi, exp, log, sqrt, cos, sin, nstr, fabs, mpmathify
import sys

mp.dps = 50

# ----------------------------------------------------------------------
def d3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

N_MAX = 200_000
print(f"Precompute D_3 table up to {N_MAX}...", flush=True)
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
    """Solve R_f(alpha, s) = correction / (1 - F) when non-resonant."""
    Fv = F(alpha, s)
    if abs(1 - Fv) < mpf("1e-30"):
        return None  # pole
    return correction(alpha, s, M) / (1 - Fv)

def Li_1(z):
    """Li_1(z) = -log(1 - z), principal branch."""
    return -log(1 - z)

def Phi_recursion(alpha, M, s_offset=mpf(0)):
    """Phi(alpha) = R_f(alpha, 1+s_offset) / Li_1(e^{i*pi*alpha})."""
    s_val = mpc(1) + s_offset
    Rfv = Rf_recursion(alpha, s_val, M)
    if Rfv is None:
        return None
    z = exp(mpc(0, pi * mpf(alpha)))
    Liv = Li_1(z)
    return Rfv / Liv, Rfv, Liv

# ----------------------------------------------------------------------
# (A,B) Verify Phi(1) = 1
# ----------------------------------------------------------------------
print()
print("=" * 78)
print(" (B) ANALYTIC VERIFICATION: Phi(1) = 1")
print("=" * 78)
print()
print("  PROVEN (axiom-free, today): R_f(1, s) = -eta(s).")
print("  Hence R_f(1, 1) = -eta(1) = -log 2.")
print()
print("  e^{i*pi*1} = -1.  Li_1(-1) = -log(1-(-1)) = -log 2.")
print()
print("  Phi(1) = R_f(1,1) / Li_1(-1) = (-log 2) / (-log 2) = 1.   QED.")
print()
# Numerical confirmation via recursion
M_big = 60_000
Phi_res = Phi_recursion(mpf(1), M_big)
print(f"  Numerical check (recursion M={M_big}):")
print(f"    Phi(1) = {nstr(Phi_res[0], 20)}")
print(f"    |Phi(1) - 1| = {nstr(abs(Phi_res[0] - 1), 6)}")

# ----------------------------------------------------------------------
# (C) Tabulate Phi at all 9 framework alphas
# ----------------------------------------------------------------------
print()
print("=" * 78)
print(" (C) Phi(alpha) at the 9 framework instances (recursion-based)")
print("=" * 78)

sqrt2 = sqrt(2)
phi_g = (1 + sqrt(5)) / 2
alphas_9 = [
    ("1   (Poincare)", mpf(1)),
    ("3/2 (RH)",        mpf("1.5")),
    ("sqrt(2) (P)",     sqrt2),
    ("phi+1/4 (NP)",    phi_g + mpf("0.25")),
    ("3*pi/4 (BSD)",    3 * pi / 4),
    ("3*pi/2 (NS)",     3 * pi / 2),
    ("2   (YM)",        mpf(2)),
    ("phi (Hodge)",     phi_g),
    ("sqrt(2*pi) (QG)", sqrt(2 * pi)),
]

print(f"{'alpha':<22} {'R_f(alpha,1)':<42} {'Li_1(e^{ipi*alpha})':<42} {'Phi(alpha)':<40} {'|Phi|':<10}")
print("-" * 160)
phi_table = {}
for name, a in alphas_9:
    Fv = F(a, mpc(1))
    if abs(1 - Fv) < mpf("1e-30"):
        print(f"{name:<22} POLE (alpha=2, R_f inherits zeta pole)")
        # Use s = 1+eps for regularized Phi at alpha=2
        eps = mpf("0.0001")
        res = Phi_recursion(a, M_big, s_offset=eps)
        if res is not None:
            Phi_v, Rf_v, Li_v = res
            # Li_1 evaluation at z=e^{2*pi*i} ~ z=1 also diverges -> regularize via eps in z
            z_reg = exp(mpc(0, pi * a)) * exp(-eps)
            Li_v_reg = Li_1(z_reg)
            Phi_reg = Rf_v / Li_v_reg
            print(f"{'   eps='+str(eps):<22} R_f={nstr(Rf_v,12):<40} Li1={nstr(Li_v_reg,12):<40} Phi={nstr(Phi_reg,12):<35}")
            phi_table[name] = Phi_reg
        continue
    Phi_v, Rf_v, Li_v = Phi_recursion(a, M_big)
    phi_table[name] = Phi_v
    print(f"{name:<22} {nstr(Rf_v,14):<42} {nstr(Li_v,14):<42} {nstr(Phi_v,14):<40} {nstr(abs(Phi_v),10):<10}")

# ----------------------------------------------------------------------
# (D) Test small-alpha leading-order expansion R_f(alpha, 1) ~ ?? * alpha
# ----------------------------------------------------------------------
print()
print("=" * 78)
print(" (D) SMALL-ALPHA LEADING ORDER TEST")
print("=" * 78)
print()
print("  Note: R_f(0, s) = zeta(s) has POLE at s=1, so R_f(alpha, 1) -> infinity as alpha -> 0.")
print("  Test 1: divide by the OBVIOUS divergent piece Li_1(e^{i*pi*alpha}).")
print("    As alpha -> 0, e^{i*pi*alpha} -> 1, Li_1(1) = +infty (log divergence).")
print("    So Phi(alpha) should be FINITE in the limit, encoding the 'regular part'.")
print()
print("  Test 2: Phi(alpha) -> ?  as alpha -> 0 along several rays.")
print()

print(f"{'alpha':<15} {'Phi(alpha) [recursion]':<45} {'Li_1(e^{i*pi*alpha})':<35}")
print("-" * 100)
for a_val_str in ["0.5", "0.3", "0.2", "0.1", "0.05", "0.02", "0.01", "0.005", "0.001"]:
    a_val = mpf(a_val_str)
    Mloc = 30_000
    res = Phi_recursion(a_val, Mloc)
    if res is None:
        print(f"{a_val_str:<15} POLE")
        continue
    Phi_v, Rf_v, Li_v = res
    print(f"{a_val_str:<15} {nstr(Phi_v, 18):<45} {nstr(Li_v, 14):<35}")

print()
print("  Test 3: framework claim is R_f(alpha,1) = pi*alpha/10 + O(alpha^2).")
print("  Compare to numerics:")
print(f"  {'alpha':<12} {'Re[R_f(a,1)]':<25} {'pi*a/10':<20} {'Re[R_f/Li1]=Re Phi':<30}")
print("-" * 100)
for a_val_str in ["0.001", "0.005", "0.01", "0.05", "0.1", "0.5"]:
    a_val = mpf(a_val_str)
    res = Phi_recursion(a_val, 30_000)
    if res is None:
        continue
    Phi_v, Rf_v, Li_v = res
    pred = pi * a_val / 10
    print(f"  {a_val_str:<12} {nstr(Rf_v.real, 14):<25} {nstr(pred, 14):<20} {nstr(Phi_v.real, 16):<30}")
print()
print("  Observation: R_f(alpha,1) does NOT approach pi*alpha/10. It is dominated by Li_1(e^{ipi*alpha}) ~ -log(i*pi*alpha) ~ -log alpha.")
print("  So R_f(alpha, 1) DIVERGES as alpha -> 0 (matching R_f(0,1) = zeta(1) = pole).")
print()
print("  CONCLUSION: pi*alpha/10 cannot be the leading order of R_f(alpha,1) literally.")
print("  Possible REINTERPRETATION:")
print("    Phi(alpha) ~ 1 + (pi/10) * alpha / Li_1(e^{i*pi*alpha}) * ... ?")
print("  We'll compute the finite part rigorously in the next script.")
