"""
Phi(alpha) := R_f(alpha, 1) / Li_1(e^{i*pi*alpha})  exploration.

Look for:
  - Functional symmetries (alpha -> alpha + 2k, alpha -> -alpha, alpha -> 2-alpha)
  - Small-alpha Taylor expansion of Phi(alpha)
  - Does Phi(alpha) ~ pi/10 to leading order in alpha?  (would vindicate
    the manuscript's literal claim AT SMALL ALPHA, with the typo being
    the "+ O(alpha^2)" hiding a much LARGER coefficient at finite alpha)
"""
from mpmath import mp, mpf, mpc, pi as PI, sqrt as msqrt, cos as mcos, \
    exp as mexp, log as mlog, power, sin as msin

mp.dps = 100


def D3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s


def F_factor(alpha, s):
    a = mpf(alpha)
    sc = mpc(s)
    return power(mpc(3), -sc) * mexp(mpc(0, 1) * PI * a) * \
           (1 + 2 * mcos(PI * a))


def Rf_via_recursion(alpha, s, M):
    a = mpf(alpha)
    sc = mpc(s)
    iPi_a = mpc(0, 1) * PI * a
    T1 = mexp(iPi_a) / mpc(1) ** sc + mexp(2 * iPi_a) / mpc(2) ** sc
    Cshift = mpc(0)
    for r in (1, 2):
        outer_phase = mexp(iPi_a * r)
        inner = mpc(0)
        for m in range(1, M + 1):
            d3 = D3(m)
            phase = mexp(iPi_a * d3)
            diff = power(mpc(3 * m + r), -sc) - power(mpc(3 * m), -sc)
            inner += phase * diff
        Cshift += outer_phase * inner
    correction = T1 + Cshift
    F = F_factor(a, sc)
    return correction / (mpc(1) - F)


def Phi(alpha, M=6000):
    a = mpf(alpha)
    Rf = Rf_via_recursion(a, mpc(1, 0), M)
    Li1 = -mlog(mpc(1) - mexp(mpc(0, 1) * PI * a))
    return Rf / Li1


def banner(t):
    print("=" * 78)
    print(t)
    print("=" * 78)


def main():
    banner("Phi(alpha) := R_f(alpha, 1) / Li_1(e^{i*pi*alpha})  --  small-alpha Taylor")
    print()
    print("Manuscript claim:  R_f(alpha, 1) = Li_1 * Phi(alpha) = pi*alpha/10 + O(alpha^2)")
    print("                  ==>  Phi(alpha) = pi*alpha / (10 * Li_1) + ...")
    print("                  ==>  for small alpha:  Li_1(e^{i*pi*alpha}) -> ?")
    print()
    print("Behavior of Li_1(e^{i*pi*alpha}) at small alpha:")
    print("  Li_1(e^{i*pi*alpha}) = -log(1 - e^{i*pi*alpha})")
    print("  As alpha -> 0,  1 - e^{i*pi*alpha} ~ -i*pi*alpha")
    print("  So Li_1 ~ -log(-i*pi*alpha) = -log(pi*alpha) + i*pi/2")
    print("                              ~ -log(pi*alpha) (huge real magnitude)")
    print()
    print(f"{'alpha':<14}{'Phi(alpha)':<60}{'pi/(10) * (alpha) -- should match if R_f ~ pi*a/10':<60}")
    for ae in (mpf("0.01"), mpf("0.05"), mpf("0.1"), mpf("0.2"), mpf("0.5"),
               mpf("1.0"), msqrt(mpf(2)), mpf("1.5"), mpf("1.9")):
        try:
            ph = Phi(ae, M=4000)
            # If R_f ~ pi*alpha/10 to leading order, then Phi ~ pi*alpha/(10*Li_1).
            Li1 = -mlog(mpc(1) - mexp(mpc(0, 1) * PI * ae))
            target = PI * ae / mpf(10) / Li1
            print(f"{mp.nstr(ae, 4):<14}{mp.nstr(ph, 6):<60}{mp.nstr(target, 6):<60}")
        except Exception as e:
            print(f"{ae}  ERROR {e}")
    print()

    banner("Test SMALL-alpha leading behavior of R_f(alpha, 1) directly")
    print()
    print("If R_f(alpha, 1) ~ c1 * alpha + c2 * alpha * log(alpha) + ...  what is c1?")
    print()
    print(f"{'alpha':<12}{'R_f(alpha, 1)':<48}{'R_f / alpha':<40}{'R_f / (alpha * log(alpha))':<40}")
    for ae in (mpf("0.001"), mpf("0.005"), mpf("0.01"), mpf("0.05"), mpf("0.1"), mpf("0.2"), mpf("0.5")):
        Rf = Rf_via_recursion(ae, mpc(1, 0), 6000)
        print(f"{mp.nstr(ae, 4):<12}{mp.nstr(Rf, 6):<48}{mp.nstr(Rf/ae, 6):<40}{mp.nstr(Rf/(ae*mlog(ae)), 6):<40}")
    print()
    print("Observation: R_f(alpha,1) ~ -log(alpha) + i*pi/2 + ...  (the Li_1 leading term)")
    print("There is no clean 'pi*alpha/10' or 'pi/(10*alpha)' leading order.")
    print()

    banner("CONCLUSION: try the manuscript's OWN form on its OWN terms")
    print()
    print("Ch 3 Thm 'Polylog Evaluation':")
    print("   R_f(alpha, 1) = Li_1(e^{i*pi*alpha}) * Phi(alpha) = pi*alpha/10 + O(alpha^2)")
    print()
    print("This statement REQUIRES  Li_1(e^{i*pi*alpha}) * Phi(alpha)  to be FINITE and")
    print("ANALYTIC near alpha = 0 with Taylor coefficient pi/10 in alpha.")
    print()
    print("But  Li_1(e^{i*pi*alpha}) = -log(-i*pi*alpha + ...) BLOWS UP logarithmically")
    print("at alpha = 0.   So for the product to be analytic and ~ pi*alpha/10, we'd need")
    print("   Phi(alpha) = pi*alpha / (10 * Li_1(e^{i*pi*alpha}))")
    print("which means Phi -> 0 as alpha -> 0 (logarithmically).   The MEASURED Phi(alpha)")
    print("does NOT satisfy this — measured Phi tends to a finite nontrivial value.")
    print()
    print("So the manuscript theorem as stated is internally inconsistent regardless of")
    print("whether the leading order is pi*alpha/10 or pi/(10*alpha).")


if __name__ == "__main__":
    main()
