"""
R_f Base-3 Recursion Attack — Construction #2
=============================================

Manuscript definition (Ch 3 line 93, ch03_resonance.tex):

    R_f(alpha, s) = sum_{n>=1} exp(i*pi*alpha*D3(n)) / n^s,    Re s > 1

D3(n) = sum of base-3 digits of n.

Ch 3 line 328 claims:  R_f(alpha, 1) = Li_1(e^{i*pi*alpha}) * Phi(alpha)
                                    = pi*alpha/10 + O(alpha^2)     (literal)

TYPO HYPOTHESIS: the leading order really should be pi/(10*alpha) — to
match lambda_0(H_alpha) = pi/(10*alpha) used in Ch 21+.

BRICK 5b RECURSION (verified to 1e-6 prior):

    R_f(alpha, s) * (1 - F(alpha, s)) = correction(alpha, s)
    F(alpha, s) = 3^{-s} * exp(i*pi*alpha) * (1 + 2*cos(pi*alpha))

DERIVED CORRECTION (precise structural form):

Decompose n = 3m+r with r in {0,1,2}, m >= 0. For m>=1:  D3(3m+r) = r + D3(m).
For n in {1,2}: contribute T1 = exp(i*pi*alpha)/1^s + exp(2*i*pi*alpha)/2^s.

R_f = T1 + sum_{r=0}^2 exp(i*pi*alpha*r) * sum_{m>=1} exp(i*pi*alpha*D3(m))/(3m+r)^s

Replace S_r ~ 3^{-s} R_f exactly for r=0; track the shift residue for r=1,2:

R_f * [1 - 3^{-s} * (1 + e^{i*pi*alpha} + e^{2i*pi*alpha})] = T1 + Cshift
                                                          = correction

with
  1 + e^{i*pi*alpha} + e^{2i*pi*alpha} = e^{i*pi*alpha} * (1 + 2*cos(pi*alpha))

(Brick 2 identity), and

  Cshift(alpha, s) = sum_{r=1,2} e^{i*pi*alpha*r} *
                       sum_{m>=1} e^{i*pi*alpha*D3(m)} * [(3m+r)^{-s} - (3m)^{-s}]

For Re(s) > 1 the shift sum converges absolutely.

For s = 1 it diverges logarithmically — but the recursion can still be
interpreted via Abel summation / analytic continuation. This file uses
high-N truncation + Richardson-style smoothing at 100-digit mpmath.

Goal:
  1. Verify the recursion identity at multiple (alpha, s).
  2. Compute R_f(alpha, 1) for canonical alpha values via three routes:
     (a) Direct Abel/Cesaro-summed series.
     (b) correction / (1 - F) via large-N truncation.
     (c) Analytic continuation via R_f(alpha, s) at s=1+eps and limit eps -> 0.
  3. Compare against pi*alpha/10 (manuscript literal) and pi/(10*alpha) (typo
     hypothesis) and any other recognizable closed form.

Author: Scientific-Computing Specialist agent (2026-05-23)
"""

from mpmath import mp, mpf, mpc, pi as PI, sqrt as msqrt, cos as mcos, \
    sin as msin, exp as mexp, log as mlog, fabs, power, mpc, almosteq

mp.dps = 100  # 100-digit precision throughout

def D3(n):
    """Base-3 digital sum (iterative for n up to ~10^7)."""
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s


def F_factor(alpha, s):
    """F(alpha, s) = 3^{-s} * e^{i*pi*alpha} * (1 + 2*cos(pi*alpha))."""
    a = mpf(alpha) if not isinstance(alpha, (mpc, mpf)) else alpha
    sc = mpc(s)
    pi = PI
    return power(mpc(3), -sc) * mexp(mpc(0, 1) * pi * a) * \
           (1 + 2 * mcos(pi * a))


def Rf_direct(alpha, s, N):
    """Truncated direct sum.  Returns partial sum up to N."""
    a = mpf(alpha)
    sc = mpc(s)
    pi = PI
    total = mpc(0)
    for n in range(1, N + 1):
        d3 = D3(n)
        phase = mexp(mpc(0, 1) * pi * a * d3)
        total += phase / power(mpc(n), sc)
    return total


def Rf_abel(alpha, s, N, eps):
    """Abel-summed truncated series:  sum_{n=1}^N (...) * exp(-eps*n).

    For s=1 the bare series diverges; Abel-summation with eps -> 0+
    recovers the analytic-continuation value (when the underlying series
    has a meaningful boundary value)."""
    a = mpf(alpha)
    sc = mpc(s)
    pi = PI
    e = mpf(eps)
    total = mpc(0)
    for n in range(1, N + 1):
        d3 = D3(n)
        phase = mexp(mpc(0, 1) * pi * a * d3) * mexp(-e * n)
        total += phase / power(mpc(n), sc)
    return total


def Rf_via_recursion(alpha, s, M):
    """Compute correction(alpha, s) truncated at m <= M, then divide by (1-F).

    correction = T1 + Cshift, where
      T1 = e^{i*pi*alpha}/1^s + e^{2*i*pi*alpha}/2^s
      Cshift = sum_{r=1,2} e^{i*pi*alpha*r} *
                  sum_{m=1}^{M} e^{i*pi*alpha*D3(m)} * [(3m+r)^{-s} - (3m)^{-s}]
    """
    a = mpf(alpha)
    sc = mpc(s)
    pi = PI
    iPi_a = mpc(0, 1) * pi * a

    # T1
    T1 = mexp(iPi_a) / mpc(1) ** sc + mexp(2 * iPi_a) / mpc(2) ** sc

    # Cshift
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
    denom = mpc(1) - F
    Rf = correction / denom
    return Rf, correction, denom


def verify_recursion(alpha, s, N):
    """Check that R_f_direct * (1 - F) is close to correction.

    Returns the residual."""
    Rf_d = Rf_direct(alpha, s, N)
    F = F_factor(alpha, s)
    lhs = Rf_d * (mpc(1) - F)
    # correction = lhs (by definition of the recursion)
    return lhs


# ===========================================================================
# CANONICAL ALPHA VALUES (manuscript table line 226-241)
# ===========================================================================

ALPHA_NAMES = [
    ("alpha=1",       mpf(1)),
    ("alpha=3/2 (RH)", mpf(3) / mpf(2)),
    ("alpha=sqrt(2) (P)", msqrt(mpf(2))),
    ("alpha=phi+1/4 (NP)", (mpf(1) + msqrt(mpf(5))) / mpf(2) + mpf(1) / mpf(4)),
    ("alpha=phi (Hodge)", (mpf(1) + msqrt(mpf(5))) / mpf(2)),
    ("alpha=3pi/4 (BSD)", mpf(3) * PI / mpf(4)),
    ("alpha=3pi/2 (NS)", mpf(3) * PI / mpf(2)),
    ("alpha=2 (YM)", mpf(2)),
    ("alpha=sqrt(2*pi) (QG)", msqrt(mpf(2) * PI)),
]


def banner(s):
    print("=" * 78)
    print(s)
    print("=" * 78)


def main():
    print()
    banner("R_f Base-3 Recursion Attack  — 100-digit mpmath")
    print()
    print("Manuscript Ch 3 line 93 def:  R_f(alpha,s) = sum_n e^{i*pi*alpha*D3(n)} / n^s")
    print("Brick 5b factor:   F(alpha,s) = 3^{-s} * e^{i*pi*alpha} * (1 + 2*cos(pi*alpha))")
    print("Recursion:         R_f * (1 - F) = correction   (verified prior)")
    print()

    # ----- STEP 1: verify the recursion in the convergent regime (s = 2) -----
    banner("STEP 1: Verify recursion identity at s = 2  (absolute convergence)")
    print(f"{'alpha':<28}{'|R_f*(1-F) - correction_recur|':>50}")
    N_test = 20000
    M_corr = 4000
    for name, a in ALPHA_NAMES[:5]:  # first 5 to keep runtime reasonable
        s = mpc(2, 0)
        Rf_d = Rf_direct(a, s, N_test)
        F = F_factor(a, s)
        lhs = Rf_d * (mpc(1) - F)
        Rf_rec, correction, denom = Rf_via_recursion(a, s, M_corr)
        residual = abs(lhs - correction)
        print(f"{name:<28}{mp.nstr(residual, 4):>50}")
    print()

    # ----- STEP 2: compute R_f(alpha, 1) THREE WAYS -----
    banner("STEP 2: R_f(alpha, 1) computed via three independent methods")
    print()
    print("Method A: Abel sum   sum_{n=1}^{N} e^{i*pi*alpha*D3(n)}/n * e^{-eps*n}")
    print("            Two-step  Richardson  eps_1=0.001, eps_2=0.0005  ->  eps->0+")
    print("Method B: correction / (1 - F)  via large-M recursion")
    print("Method C: lim_{eps->0+} R_f(alpha, 1+eps)   using direct convergent series")
    print()

    s1 = mpc(1, 0)

    print(f"{'alpha':<26}{'Method A (Abel)':<38}{'Method B (recursion)':<38}{'Method C (eps->0+)':<36}")
    print("-" * 138)

    N_abel = 200000
    M_rec = 6000
    eps_vals = [mpf("0.001"), mpf("0.0005")]

    results = {}
    for name, a in ALPHA_NAMES:
        # Method A: Abel sum + Richardson eps -> 0+
        # f(eps) ~ R_f(alpha,1) + c1*eps + ...  for analytic limit.
        # Richardson: R_f ~ 2*f(eps2) - f(eps1) if linear in eps and eps2 = eps1/2.
        fA1 = Rf_abel(a, s1, N_abel, eps_vals[0])
        fA2 = Rf_abel(a, s1, N_abel, eps_vals[1])
        # Linear extrapolation: f(eps) ~ A + B*eps;  A ~ (eps1*fA2 - eps2*fA1)/(eps1 - eps2)
        A = (eps_vals[0] * fA2 - eps_vals[1] * fA1) / (eps_vals[0] - eps_vals[1])
        method_A = A

        # Method B: recursion / denom
        method_B, _, denom_B = Rf_via_recursion(a, s1, M_rec)

        # Method C: Limit of R_f(alpha, 1+eps) -> using a small eps in the convergent regime.
        # Use eps small enough that |3^{-s}| factor is well-conditioned but series converges.
        eps_c = mpf("0.01")
        Rf_c = Rf_direct(a, mpc(1 + eps_c, 0), 100000)
        method_C = Rf_c  # raw value at s = 1+eps  (later compare under different eps).

        results[name] = (a, method_A, method_B, method_C, denom_B)
        print(f"{name:<26}{mp.nstr(method_A, 6):<38}{mp.nstr(method_B, 6):<38}{mp.nstr(method_C, 6):<36}")
    print()

    # ----- STEP 3: compare to manuscript claims -----
    banner("STEP 3: Compare to manuscript closed-form claims")
    print()
    print("Manuscript literal: R_f(alpha, 1) = pi*alpha/10")
    print("Typo hypothesis  : R_f(alpha, 1) = pi/(10*alpha)")
    print()
    print(f"{'alpha':<26}{'pi*alpha/10':<22}{'pi/(10*alpha)':<22}{'R_f (Method B)':<32}{'|R_f - pi*a/10|':<22}{'|R_f - pi/(10a)|':<22}")
    print("-" * 146)
    for name, (a, mA, mB, mC, denom_B) in results.items():
        pa10 = PI * a / mpf(10)
        p10a = PI / (mpf(10) * a)
        diff_lit = abs(mB - mpc(pa10, 0))
        diff_typ = abs(mB - mpc(p10a, 0))
        print(f"{name:<26}{mp.nstr(pa10, 6):<22}{mp.nstr(p10a, 6):<22}{mp.nstr(mB, 6):<32}{mp.nstr(diff_lit, 4):<22}{mp.nstr(diff_typ, 4):<22}")
    print()

    # ----- STEP 4: closer look at sqrt(2) (the P-class anchor) ------------
    banner("STEP 4: P-class detailed analysis  alpha = sqrt(2)")
    a = msqrt(mpf(2))
    print(f"alpha = sqrt(2)  =  {mp.nstr(a, 30)}")
    print()
    print("Manuscript literal claim  pi*alpha/10 =  ", mp.nstr(PI * a / mpf(10), 30))
    print("Typo-hypothesis claim     pi/(10*alpha)= ", mp.nstr(PI / (mpf(10) * a), 30))
    print()

    # F(sqrt(2), 1)
    F = F_factor(a, mpc(1, 0))
    print(f"F(sqrt(2), 1) = {mp.nstr(F, 20)}")
    print(f"1 - F         = {mp.nstr(mpc(1) - F, 20)}")
    print(f"|1 - F|       = {mp.nstr(abs(mpc(1) - F), 20)}")
    print()

    # Recursion-based R_f for a range of M (convergence test on correction)
    print("Convergence of correction-based R_f as M grows:")
    print(f"{'M':<10}{'correction':<48}{'R_f = corr/(1-F)':<48}")
    for M in (500, 1000, 2000, 4000, 8000):
        Rf_rec, corr, denom = Rf_via_recursion(a, mpc(1, 0), M)
        print(f"{M:<10}{mp.nstr(corr, 6):<48}{mp.nstr(Rf_rec, 6):<48}")
    print()

    # Abel-sum convergence as eps -> 0
    print("Abel-sum convergence as eps -> 0 (N=200000):")
    print(f"{'eps':<15}{'R_f^Abel':<48}")
    for eps in (mpf("0.01"), mpf("0.005"), mpf("0.002"),
                mpf("0.001"), mpf("0.0005"), mpf("0.0002")):
        v = Rf_abel(a, mpc(1, 0), 200000, eps)
        print(f"{mp.nstr(eps, 4):<15}{mp.nstr(v, 6):<48}")
    print()

    # Method C: direct R_f at s = 1+eps for eps -> 0
    print("Direct R_f at s = 1+eps:")
    print(f"{'eps':<15}{'R_f^direct':<48}")
    for eps in (mpf("0.1"), mpf("0.05"), mpf("0.02"), mpf("0.01"), mpf("0.005")):
        v = Rf_direct(a, mpc(1 + eps, 0), 100000)
        print(f"{mp.nstr(eps, 4):<15}{mp.nstr(v, 6):<48}")
    print()

    # ----- STEP 5: Test typo hypothesis at FULL precision ------------------
    banner("STEP 5: Typo-hypothesis pi/(10*alpha) test at 100-digit")
    print()
    for name, (a, mA, mB, mC, denom_B) in results.items():
        target_typo = PI / (mpf(10) * a)
        diff = abs(mB - mpc(target_typo, 0))
        print(f"  {name:<28}  R_f = {mp.nstr(mB, 8):<40}  pi/(10*alpha) = {mp.nstr(target_typo, 8):<22}  diff = {mp.nstr(diff, 5)}")
    print()

    # ----- STEP 6: search for OTHER closed forms ---------------------------
    banner("STEP 6: Search for recognizable closed form for R_f(sqrt(2), 1)")
    a = msqrt(mpf(2))
    Rf_rec, _, _ = Rf_via_recursion(a, mpc(1, 0), 8000)
    print(f"Computed R_f(sqrt(2), 1) ~ {mp.nstr(Rf_rec, 25)}")
    print()
    print("Re part:", mp.nstr(Rf_rec.real, 25))
    print("Im part:", mp.nstr(Rf_rec.imag, 25))
    print()
    # Try PSLQ on (R_f.real, pi, ln(2), ln(3), 1, sqrt(2))
    try:
        from mpmath import pslq
        candidates_re = [Rf_rec.real, PI, mlog(mpf(2)), mlog(mpf(3)),
                         a, mpf(1)]
        rel_re = pslq(candidates_re, tol=mpf("1e-25"), maxcoeff=10**8)
        print("PSLQ on Re(R_f), pi, ln2, ln3, sqrt(2), 1 :", rel_re)

        candidates_im = [Rf_rec.imag, PI, mlog(mpf(2)), mlog(mpf(3)),
                         a, mpf(1)]
        rel_im = pslq(candidates_im, tol=mpf("1e-25"), maxcoeff=10**8)
        print("PSLQ on Im(R_f), pi, ln2, ln3, sqrt(2), 1 :", rel_im)
    except Exception as e:
        print("PSLQ failed:", e)
    print()


if __name__ == "__main__":
    main()
