#!/usr/bin/env python3
"""
Gate-2 verification: why b9d6d27e is vacuous, and what the log-weighted
theta bound on Lambda0' delivers instead.

Every number quoted in codex/GATE2_LOGWEIGHT_IS_THE_UNBLOCK_2026-10-19.md is
produced here. Verdicts are computed from residuals, never printed as strings.

Gate-2:  (1 + 2|t|)*||Lambda0(1+it)|| + (t^2 + |t|)*||Lambda0'(1+it)|| <= 2
"""
import mpmath as mp

mp.mp.dps = 25
N = 60
U = mp.mpf(50) / 1727                      # the in-tree uniform constant


def om(x):
    return mp.fsum([mp.e ** (-mp.pi * (n + 1) ** 2 * x) for n in range(N)])


def om1(x):
    return mp.fsum([-mp.pi * (n + 1) ** 2 * mp.e ** (-mp.pi * (n + 1) ** 2 * x)
                    for n in range(N)])


def om2(x):
    return mp.fsum([(mp.pi * (n + 1) ** 2) ** 2
                    * mp.e ** (-mp.pi * (n + 1) ** 2 * x) for n in range(N)])


def F_plus2(u):
    e = mp.e ** u
    return (mp.mpf(1) / 4 * mp.e ** (u / 2) * om(e)
            + 2 * (mp.e ** (u / 2) * (om1(e) * e))
            + mp.e ** (u / 2) * (om2(e) * e * e))


def F_minus2(u):
    e = mp.e ** u
    return om2(e) * e * e + om1(e) * e


def L0(s):
    return mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s) + 1 / s + 1 / (1 - s)


def load(t, c_lam, c_lamp):
    t = mp.mpf(t)
    return (1 + 2 * t) * c_lam + (t * t + t) * c_lamp


def ceiling(c_lam, c_lamp):
    """Largest t with load(t) <= 2."""
    a, b, c = c_lamp, c_lamp + 2 * c_lam, c_lam - 2
    return (-b + mp.sqrt(b * b - 4 * a * c)) / (2 * a)


print("=" * 78)
print("1. K_sum, the undischarged hypothesis of b9d6d27e")
print("=" * 78)
Ip = mp.quad(lambda u: abs(F_plus2(u)), [0, 0.5, 1, 2, 4, 8])
Im = mp.quad(lambda u: abs(F_minus2(u)), [0, 0.5, 1, 2, 4, 8])
K = Ip + Im
print(f"   int|F_plus''|  = {float(Ip):.8f}")
print(f"   int|F_minus''| = {float(Im):.8f}")
print(f"   K_sum          = {float(K):.8f}")
# independent cross-check: K_sum = -(F+'(0) + F-'(0)) = -(om(1)/2 + 2 om'(1))
K_bdry = -(om(1) / 2 + 2 * om1(1))
print(f"   cross-check via the proved boundary constant -1/4: {float(K_bdry):.8f}")
print(f"   the two agree to {abs(K - K_bdry)}")
print(f"   hypothesis K_sum <= 1/16 holds: {K <= mp.mpf(1)/16}"
      f"   (ratio {float(K * 16):.2f})")

print()
print("=" * 78)
print("2. No sharper K rescues it, and Tier-3 is worse than what it replaces")
print("=" * 78)
t_edge = mp.mpf(111) / 16
term2 = (t_edge * t_edge + t_edge) * U
need_L0 = (2 - term2) / (1 + 2 * t_edge)
K_max = (need_L0 * t_edge * t_edge - 1) / 4
print(f"   at t = 111/16 = {float(t_edge)}:")
print(f"     term2 (Lambda0' side)  = {float(term2):.5f}")
print(f"     so need ||Lambda0||   <= {float(need_L0):.6f}")
print(f"     i.e. need K_sum       <= {float(K_max):.6f}   (true K = {float(K):.6f})")
print(f"     reachable: {K <= K_max}   short by {float(K / K_max):.2f}x")
sharp = (1 + 4 * K) / (t_edge * t_edge)
print(f"     Tier-3 (1+4K)/t^2      = {float(sharp):.6f}")
print(f"     uniform 50/1727        = {float(U):.6f}")
print(f"     Tier-3 better here: {sharp < U}   (factor {float(sharp/U):.2f})")
print(f"   crossover: Tier-3 wins only for t >= {float(mp.sqrt((1+4*K)/U)):.3f}")

print()
print("=" * 78)
print("3. The binding term is Lambda0', not Lambda0")
print("=" * 78)
print(f"{'t':>9} {'||L0||':>11} {'||L0prime||':>12} {'term1':>9} {'term2':>9}"
      f" {'total':>9} {'binding':>9}")
for t in (6.9375, 13):
    s = mp.mpc(1, t)
    a, b = abs(L0(s)), abs(mp.diff(L0, s))
    t1, t2 = (1 + 2 * mp.mpf(t)) * U, (mp.mpf(t) ** 2 + t) * U
    print(f"{t:>9} {float(a):>11.6f} {float(b):>12.6f} {float(t1):>9.4f}"
          f" {float(t2):>9.4f} {float(t1+t2):>9.4f} "
          f"{'term2' if t2 > t1 else 'term1':>9}")
    print(f"{'':>9} slack factor on Lambda0: {float(U/a):.1f}x   "
          f"on Lambda0-prime: {float(U/b):.1f}x")

print()
print("=" * 78)
print("4. Cauchy cannot deliver it: the strip is pinned to sigma in [0,2]")
print("=" * 78)


def B(sig):
    """Sharp theta-rep strip bound |Lambda0(sig+it)| <= B(sig)."""
    return mp.quad(lambda x: (x ** (mp.mpf(sig) / 2 - 1)
                              + x ** (-(1 + mp.mpf(sig)) / 2)) * om(x),
                   [1, 2, 4, mp.inf])


print(f"   sharp sup on the usable strip, B(2) = {float(B(2)):.6f}"
      f"  -> only {float(U/B(2)):.2f}x better than 50/1727")
print(f"   {'R':>5} {'needs sigma <=':>15} {'B(1+R)/R':>12}")
for R in (1, 2, 4, 6):
    print(f"   {R:>5} {1+R:>15} {float(B(1+R)/R):>12.6f}")
print("   (R > 1 requires sigma > 2, where the dominating function is no longer"
      " a bare exponential)")

print()
print("=" * 78)
print("5. The landed bound and what it unlocks")
print("=" * 78)
C_an = mp.e ** (-mp.pi) / (mp.pi ** 2 * (1 - mp.e ** (-mp.pi)))
C_rat = mp.mpf(3) / 650
C_old = 2 * mp.e ** (-mp.pi) / (mp.pi * (1 - mp.e ** (-mp.pi)))
print(f"   old analytic constant 2e^-pi/(pi(1-e^-pi)) = {float(C_old):.8f}")
print(f"   its rational relaxation 50/1727            = {float(U):.8f}")
print(f"   new analytic constant e^-pi/(pi^2(1-e^-pi))= {float(C_an):.8f}")
print(f"   its rational relaxation 3/650              = {float(C_rat):.8f}")
print(f"   ratio new/old = {float(C_an/C_old):.6f}   vs 1/(2pi) = "
      f"{float(1/(2*mp.pi)):.6f}  (equal: {abs(C_an/C_old - 1/(2*mp.pi)) < mp.mpf('1e-20')})")
print(f"   3/650 is a valid relaxation: {C_rat >= C_an}")
# the exact rational chain the Lean proof uses
chain = (mp.mpf(1)/23) / ((mp.mpf(157)/50)**2 * (mp.mpf(22)/23))
print(f"   Lean chain (e^-pi<=1/23, pi>157/50, 1-e^-pi>=22/23) gives"
      f" {float(chain):.8f} <= 3/650: {chain <= C_rat}")
print()
print(f"   {'t':>9} {'load':>9} {'<= 2':>7}")
for t in (6.8125, 6.9375, 10, 13, 14.5, 15):
    L = load(t, U, C_rat)
    print(f"   {t:>9} {float(L):>9.4f} {str(L <= 2):>7}")
print()
print(f"   OLD ceiling (50/1727 both): t <= {float(ceiling(U, U)):.6f}")
print(f"   NEW ceiling (50/1727, 3/650): t <= {float(ceiling(U, C_rat)):.6f}")
print(f"   R1 march target t=13 covered: {load(13, U, C_rat) <= 2}")
print(f"   R2 upper end  t=14.5 covered: {load(14.5, U, C_rat) <= 2}")
print(f"   R3 top        t=15   covered: {load(15, U, C_rat) <= 2}")
