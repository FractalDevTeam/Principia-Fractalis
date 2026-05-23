"""
Diagnostic follow-up to rf_solve.py.

Three deeper investigations:

(1) The alpha-integer singularities of F(alpha, 1).  When 1 + 2*cos(pi*alpha) = 3
    (i.e. cos(pi*alpha) = 1, alpha = 2k) the recursion factor F = 3^{-1} * 3 = 1
    and the denominator vanishes — same pole structure as the zeta pole.  When
    cos(pi*alpha) = -1/2, the factor is zero and R_f = correction.

(2) PSLQ search with a RICHER basis for R_f(sqrt(2), 1).

(3) Test whether the prior agent's "TYPO" hypothesis works at any rescaling:
    Compare R_f against pi/10, pi/(10*alpha), pi*alpha/10, AND the actual
    proposed spectral closed form  lambda_0 = pi/(10*alpha)  treated as the
    REAL PART or MODULUS of R_f.  Also check sign-flipped variants.
"""
from mpmath import mp, mpf, mpc, pi as PI, sqrt as msqrt, cos as mcos, \
    exp as mexp, log as mlog, fabs, power, pslq, im, re

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
    return correction / (mpc(1) - F), correction, mpc(1) - F


def banner(s):
    print("=" * 78)
    print(s)
    print("=" * 78)


def main():
    # (1) F-factor singularity table
    banner("(1) F(alpha, 1) = 3^{-1} * e^{i*pi*alpha} * (1 + 2*cos(pi*alpha))")
    print(f"{'alpha':<24}{'1 + 2*cos(pi*alpha)':<28}{'|F|':<20}{'|1-F|':<20}")
    test_alphas = [
        ("0 (zeta pole)", mpf(0)),
        ("1", mpf(1)),
        ("2 (YM)", mpf(2)),
        ("3/2", mpf("1.5")),
        ("sqrt(2)", msqrt(mpf(2))),
        ("phi", (mpf(1) + msqrt(mpf(5))) / mpf(2)),
        ("phi+1/4", (mpf(1) + msqrt(mpf(5))) / mpf(2) + mpf("0.25")),
        ("2/3", mpf(2) / mpf(3)),
        ("4/3", mpf(4) / mpf(3)),
    ]
    for name, a in test_alphas:
        cosfac = 1 + 2 * mcos(PI * a)
        F = F_factor(a, mpc(1, 0))
        denom = mpc(1) - F
        print(f"{name:<24}{mp.nstr(cosfac, 6):<28}{mp.nstr(abs(F), 6):<20}{mp.nstr(abs(denom), 6):<20}")
    print()
    print("Note: alpha = 0, 2  give cos(pi*alpha) = 1, so 1 + 2*cos = 3,")
    print("and F = (1/3)*1*3 = 1  exactly  ==>  denom = 0 (the zeta pole).")
    print("This explains the alpha=2 blow-up.")
    print()

    # (2) PSLQ at HIGHER precision for sqrt(2)
    banner("(2) PSLQ search for R_f(sqrt(2), 1)  at  50 digits + richer basis")
    mp.dps = 80
    a = msqrt(mpf(2))
    # Recompute at 80 digits
    Rf, _, _ = Rf_via_recursion(a, mpc(1, 0), 12000)
    print(f"R_f(sqrt(2), 1)  ~  {mp.nstr(Rf, 40)}")
    print()

    # Compute supporting constants
    pi  = PI
    ln2 = mlog(mpf(2))
    ln3 = mlog(mpf(3))
    s2  = msqrt(mpf(2))
    ln_sin = mlog(2 * abs(mp.sin(PI * a / 2)))   # |1 - e^{i*pi*alpha}| = 2|sin(pi a/2)|

    # Method 1: PSLQ on real part
    basis_re = [Rf.real, mpf(1), pi, ln2, ln3, s2, ln_sin]
    rel = pslq(basis_re, tol=mpf("1e-40"), maxcoeff=10**10)
    print(f"PSLQ on (Re Rf, 1, pi, ln2, ln3, sqrt(2), ln|1-e^(i*pi*a)|): {rel}")

    # Method 2: PSLQ on imag part
    basis_im = [Rf.imag, mpf(1), pi, ln2, ln3, s2, ln_sin]
    rel = pslq(basis_im, tol=mpf("1e-40"), maxcoeff=10**10)
    print(f"PSLQ on (Im Rf, 1, pi, ln2, ln3, sqrt(2), ln|1-e^(i*pi*a)|): {rel}")

    # Method 3: PSLQ checking if Rf = -log(1 - e^{i*pi*sqrt(2)}) ?
    # That would be the polylog Li_1(e^{i*pi*alpha}) value the manuscript
    # references.
    Li1 = -mlog(mpc(1) - mexp(mpc(0, 1) * PI * a))
    print()
    print(f"Li_1(e^{{i*pi*sqrt(2)}}) = -log(1 - e^{{i*pi*sqrt(2)}})  =  {mp.nstr(Li1, 30)}")
    print(f"R_f(sqrt(2), 1)                                       =  {mp.nstr(Rf, 30)}")
    print(f"Ratio Rf / Li_1                                       =  {mp.nstr(Rf / Li1, 30)}")
    print(f"Difference Rf - Li_1                                  =  {mp.nstr(Rf - Li1, 30)}")
    print()

    # Method 4: try ratio against rationals * powers of pi / sqrt(2)
    test_candidates = [
        ("pi/(10*sqrt(2))", PI / (mpf(10) * a)),
        ("pi*sqrt(2)/10",   PI * a / mpf(10)),
        ("pi/10",           PI / mpf(10)),
        ("-log 2",          -mlog(mpf(2))),
        ("-log 3 * sqrt(2)/2", -mlog(mpf(3)) * a / mpf(2)),
        ("Li_1(e^{i pi a}) (modulus)", abs(Li1)),
        ("|Rf|",             abs(Rf)),
        ("arg(Rf)",          mp.arg(Rf)),
        ("arg(Li_1)",        mp.arg(Li1)),
    ]
    print("Reference constants vs R_f(sqrt(2),1):")
    for name, c in test_candidates:
        print(f"  {name:<32} = {mp.nstr(c, 18)}")
    print()

    # (3) Sanity: at alpha = 0, recursion -> ... what?
    banner("(3) Sanity:  recursion at  alpha=0, s=2  reproduces  zeta(2) = pi^2/6")
    Rf_0_2, _, _ = Rf_via_recursion(mpf(0), mpc(2, 0), 5000)
    print(f"R_f(0, 2)  via recursion  =  {mp.nstr(Rf_0_2, 25)}")
    print(f"pi^2 / 6                  =  {mp.nstr(PI ** 2 / mpf(6), 25)}")
    print(f"|diff|                     =  {mp.nstr(abs(Rf_0_2 - PI ** 2 / mpf(6)), 6)}")
    print()

    # (4) Check the manuscript's hint:  R_f(alpha, 1) = Li_1(e^{i pi alpha}) * Phi(alpha)
    #     If Phi is well-behaved, Rf / Li_1 should look like a clean number for each alpha.
    banner("(4) Manuscript decomposition  R_f(alpha, 1) = Li_1(e^{i pi alpha}) * Phi(alpha)")
    print("    Compute Phi(alpha) := R_f / Li_1 for each canonical alpha:")
    print(f"{'alpha':<24}{'R_f':<40}{'Li_1':<32}{'Phi = R_f / Li_1':<32}")
    for name, a in test_alphas:
        if abs(a) < mpf("1e-30"):
            continue  # skip 0
        try:
            Rf_a, _, _ = Rf_via_recursion(a, mpc(1, 0), 5000)
            Li_a = -mlog(mpc(1) - mexp(mpc(0, 1) * PI * a))
            if abs(Li_a) < mpf("1e-50"):
                phi_val = "DIVERGENT (Li_1 ~ 0)"
            else:
                phi_val = mp.nstr(Rf_a / Li_a, 8)
            print(f"{name:<24}{mp.nstr(Rf_a, 6):<40}{mp.nstr(Li_a, 6):<32}{phi_val:<32}")
        except Exception as e:
            print(f"{name:<24} ERROR: {e}")
    print()


if __name__ == "__main__":
    main()
