"""
The literal manuscript formula
   π/10 = (1/2) ∫_0^1 R_f(√2, 1/2 + ix) dx
gives -0.370 - 0.175i ≠ π/10 = 0.3142.

Test plausible variants the framework might have meant:
  (a) Re(integral)
  (b) |integral|
  (c) -integral (sign convention)
  (d) (1/2) ∫_0^1 |R_f(√2, 1/2+ix)|² dx     <- Ch 23 form uses |R_f|²
  (e) Different integration range [0, ∞), [1/2, 1], etc.
  (f) ω_c = ∫_0^T R_f at T = log(something)
  (g) The Ch 9 formula at the corrected α_c = 3/2 instead of α = √2

Also test the universal coupling form via this integral:
  λ_0(α) = (1/α) × {ω_c-style integral at this α}
for α ∈ {1, √2, 3/2, 2, √(2π)}.
"""
from mpmath import mp, mpc, mpf, exp, log, pi, sqrt, quad, nstr, fabs
import sys

mp.dps = 30

def d3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

def get_D3_table(N):
    return [d3(n) for n in range(N + 1)]

def Rf_partial(alpha, s, N, d3_table):
    total = mpc(0)
    for n in range(1, N + 1):
        phase = exp(mpc(0, pi * alpha * d3_table[n]))
        total += phase / mpc(n) ** s
    return total

def integrate(alpha, a, b, N, d3_table, mod=lambda v: v):
    """∫_a^b mod(R_f(α, 1/2 + ix)) dx via Gauss-Legendre."""
    half = mpf("0.5")
    def integrand(x):
        v = Rf_partial(alpha, mpc(half, x), N, d3_table)
        return mod(v)
    return quad(integrand, [a, b])

def main():
    N = 2000
    d3t = get_D3_table(N)
    target = pi / 10
    print(f"N = {N}, target π/10 = {nstr(target, 12)}")
    print("="*60)
    sys.stdout.flush()

    # Variant tests at α = √2
    sqrt2 = sqrt(2)

    # (a-c) The basic integral
    base = integrate(sqrt2, 0, 1, N, d3t)
    print(f"\n[α=√2] ∫_0^1 R_f = {nstr(base, 14)}")
    print(f"  Re        = {nstr(base.real, 10)},  |Re-π/10|       = {nstr(abs(base.real-target), 6)}")
    print(f"  -Re       = {nstr(-base.real, 10)}, |(-Re)-π/10|    = {nstr(abs(-base.real-target), 6)}")
    print(f"  |val|     = {nstr(abs(base), 10)},  | |val|-π/10|   = {nstr(abs(abs(base)-target), 6)}")
    print(f"  |val|/2   = {nstr(abs(base)/2, 10)}")
    print(f"  base.real / target = {nstr(base.real / target, 10)}")
    sys.stdout.flush()

    # (d) |R_f|² integral
    sq = integrate(sqrt2, 0, 1, N, d3t, mod=lambda v: fabs(v)**2)
    print(f"\n[α=√2] ∫_0^1 |R_f|² dx = {nstr(sq, 12)}")
    print(f"   /2  = {nstr(sq/2, 12)},  |.-π/10| = {nstr(abs(sq/2-target), 6)}")
    print(f"   sqrt = {nstr(sqrt(sq), 12)}")
    print(f"   sqrt/2 = {nstr(sqrt(sq)/2, 12)},  |.-π/10| = {nstr(abs(sqrt(sq)/2 - target), 6)}")
    sys.stdout.flush()

    # (d') ∫ Re(R_f)² dx — real-part-squared
    re2 = integrate(sqrt2, 0, 1, N, d3t, mod=lambda v: v.real**2)
    im2 = integrate(sqrt2, 0, 1, N, d3t, mod=lambda v: v.imag**2)
    print(f"\n   ∫ Re² = {nstr(re2, 10)},    ∫ Im² = {nstr(im2, 10)}")
    print(f"   sqrt(∫Re²)/2 = {nstr(sqrt(re2)/2, 10)},  |.-π/10| = {nstr(abs(sqrt(re2)/2-target), 6)}")
    sys.stdout.flush()

    # (e) Different ranges
    print(f"\n[α=√2] varying upper limit T (lower=0)")
    for T in [mpf("0.5"), mpf(1), mpf(2), mpf(5), mpf(10)]:
        v = integrate(sqrt2, 0, T, N, d3t)
        print(f"  T={float(T):5.2f}: |val|={nstr(abs(v),8)},  Re={nstr(v.real,8)},  Re/T={nstr(v.real/T,8)}")
        sys.stdout.flush()

    # (g) Test at α = 3/2 (manuscript line 219 says α_c = 3/2 is the critical coupling)
    print(f"\n[α=3/2] ∫_0^1 R_f")
    h = integrate(mpf("1.5"), 0, 1, N, d3t)
    print(f"  result = {nstr(h, 12)}")
    print(f"  Re = {nstr(h.real, 10)},  |Re-π/10|={nstr(abs(h.real-target),6)}")
    print(f"  |val| = {nstr(abs(h), 10)}")
    print(f"  -Re = {nstr(-h.real, 10)}")
    sys.stdout.flush()

    # Universal coupling test: try λ_0(α) = (1/α) * Re[(1/2) ∫_0^1 R_f(α, ...)]
    # or = (1/α) * |...|
    print(f"\n{'='*60}")
    print("Universal coupling test: λ_0(α) via integral / α")
    print(f"{'='*60}")
    for alpha_name, alpha_val, target_lambda in [
        ("1",     mpf(1),       pi/10),
        ("√2",    sqrt2,        pi/(10*sqrt2)),
        ("3/2",   mpf("1.5"),   pi/15),
        ("φ",     (1+sqrt(5))/2, pi/(10*(1+sqrt(5))/2)),
        ("2",     mpf(2),       pi/20),
        ("√(2π)", sqrt(2*pi),   pi/(10*sqrt(2*pi))),
    ]:
        v = integrate(alpha_val, 0, 1, N, d3t)
        # Test multiple candidates
        cand_re = v.real / alpha_val
        cand_mre = -v.real / alpha_val
        cand_abs = abs(v) / alpha_val
        cand_re_half = v.real / (2 * alpha_val)
        cand_abs_half = abs(v) / (2 * alpha_val)
        print(f"\n  α={alpha_name:5s}  target λ_0={nstr(target_lambda,10)}")
        print(f"    Re/α     = {nstr(cand_re,10)},     |diff|={nstr(abs(cand_re - target_lambda),6)}")
        print(f"    -Re/α    = {nstr(cand_mre,10)},     |diff|={nstr(abs(cand_mre - target_lambda),6)}")
        print(f"    |val|/α  = {nstr(cand_abs,10)},     |diff|={nstr(abs(cand_abs - target_lambda),6)}")
        print(f"    Re/(2α)  = {nstr(cand_re_half,10)},  |diff|={nstr(abs(cand_re_half - target_lambda),6)}")
        print(f"    |val|/(2α)={nstr(cand_abs_half,10)}, |diff|={nstr(abs(cand_abs_half - target_lambda),6)}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
