"""
02: R_f(sqrt(2*pi), s) and Phi(sqrt(2*pi)) for the QG instance.

R_f(alpha, s) = sum_{n=1}^N e^{i*pi*alpha*D_3(n)} / n^s
   where D_3(n) = base-3 digital sum.

Phi(alpha) is defined by R_f(alpha, 1) = Li_1(e^{i*pi*alpha}) * Phi(alpha)
   where Li_1(z) = -log(1-z).

We compute R_f, Li_1 anchor, and Phi(sqrt(2*pi)).  Compare with the
two values the prompt cites:
  - R_f(sqrt(2*pi), 1) ~ -0.780 + 0.895 i  (wave-4 numerical claim)
  - Phi(sqrt(2*pi))     ~ 1.335 + 0.392 i  (wave-4 numerical claim)
Note: wave-4 also gives Phi ~ 1.33 + 0.39 i for sqrt(2*pi) in REFRESHER.

Run: python3 02_R_f_QG_and_Phi.py
"""
from mpmath import mp, mpf, mpc, pi, sqrt, exp, log, ln, fabs

mp.dps = 50

alpha_QG = sqrt(2 * pi)
I = mpc(0, 1)

def D3(n):
    """Base-3 digital sum of positive integer n."""
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

def R_f(alpha, s, N):
    """Partial sum R_f(alpha, s) up to N terms (s real here)."""
    total = mpc(0, 0)
    s_mp = mpf(s)
    coef = pi * alpha
    for n in range(1, N + 1):
        d = D3(n)
        phase = exp(I * coef * d)
        total += phase / mpf(n) ** s_mp
    return total

def Li1(z):
    """Principal branch Li_1(z) = -log(1 - z), z != 1."""
    return -log(1 - z)

# Use a strong truncation; the series for s=1 converges conditionally only,
# so we increase N progressively to see settling.
print("=" * 78)
print("R_f(sqrt(2*pi), 1) convergence study  [50-digit mpmath]")
print("=" * 78)
print(f"alpha_QG = {alpha_QG}")
print()
prev = None
for N in [1000, 5000, 20000, 100000, 500000]:
    val = R_f(alpha_QG, 1, N)
    diff_str = ""
    if prev is not None:
        d = abs(val - prev)
        diff_str = f"  |delta vs prev| = {float(d):.3e}"
    print(f"  N={N:>7}: R_f = {complex(val).real:+.10f} {complex(val).imag:+.10f} i{diff_str}")
    prev = val
R_f_at_one = prev

print()
print("Wave-4 cited numerical value:")
print(f"  R_f(sqrt(2*pi), 1) ~ -0.780 + 0.895 i")
print(f"  Our high-N estimate: {complex(R_f_at_one).real:+.6f} {complex(R_f_at_one).imag:+.6f} i")

# Phi via the Li_1 split
z = exp(I * pi * alpha_QG)
Li1_val = Li1(z)

print()
print("=" * 78)
print("Phi(sqrt(2*pi)) via R_f(alpha,1) = Li_1(e^{i pi alpha}) * Phi(alpha)")
print("=" * 78)
print(f"  z = e^(i pi alpha_QG) = {complex(z).real:+.10f} {complex(z).imag:+.10f} i")
print(f"  Li_1(z) = -log(1-z)   = {complex(Li1_val).real:+.10f} {complex(Li1_val).imag:+.10f} i")
print(f"  |Li_1(z)| = {float(abs(Li1_val)):.10f}")

Phi_QG = R_f_at_one / Li1_val
print(f"  Phi(sqrt(2*pi)) = R_f / Li_1 = {complex(Phi_QG).real:+.6f} {complex(Phi_QG).imag:+.6f} i")
print(f"  |Phi(sqrt(2*pi))| = {float(abs(Phi_QG)):.6f}")
print()
print("Wave-4 cited values:")
print("  Phi(sqrt(2*pi)) ~ 1.335 + 0.392 i  (one wave)  |Phi| ~ 1.391")
print("  Phi(sqrt(2*pi)) ~ 1.33  + 0.39 i   (REFRESHER) |Phi| ~ 1.39")
print()

# Compare with the OTHER 8 alpha-instance Phi values (REFRESHER):
# This Phi(sqrt(2*pi)) value tells us whether QG sits in the "cluster around 1.4"
phi_mag = abs(Phi_QG)
print(f"Cluster check: |Phi(alpha)| values across 9 instances cluster near 1.4")
print(f"   |Phi(QG)|  = {float(phi_mag):.4f}")
print(f"   target    ~ 1.40")
print(f"   In cluster? {abs(phi_mag - mpf('1.4')) < mpf('0.15')}")

# The structural property driving Lambda_eff suppression:
# The phase coef pi * alpha_QG = pi * sqrt(2*pi) ~ 7.874.  Modulo 2*pi
# (the natural period for e^{i theta}), this gives a fractional offset.
print()
print("=" * 78)
print("Structural property of R_f at sqrt(2*pi) driving Lambda_eff suppression:")
print("=" * 78)
coef = pi * alpha_QG
print(f"  Phase coef pi * alpha_QG = {coef}")
print(f"  Mod 2*pi:                = {coef - 2*pi * int(coef / (2*pi))}")
print(f"  As fraction of 2*pi:     = {(coef - 2*pi * int(coef / (2*pi))) / (2*pi)}")
print()
print("Since pi*alpha_QG / (2*pi) = alpha_QG/2 = sqrt(2*pi)/2 ~ 1.2533")
print("the per-D_3 phase advance is alpha_QG/2 cycles, irrational.")
print("=> the digital-sum phases e^{i pi alpha_QG D_3(n)} are EQUIDISTRIBUTED mod 2*pi")
print("   on the unit circle by Weyl equidistribution (alpha_QG/2 is irrational).")
print("=> the resulting R_f cancellation produces |R_f| ~ O(1) at s=1, not divergent")
print("   (in contrast to R_f(2,1) which inherits the zeta pole).")
print()
print("This bounded |R_f| at s=1 is exactly what makes the integrand")
print("ch_2 * R_f(sqrt(2*pi), |x|)  integrable across the cosmological volume,")
print("and hence what makes the exponential suppression Lambda_eff finite.")
