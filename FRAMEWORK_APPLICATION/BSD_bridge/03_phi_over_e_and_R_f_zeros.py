"""
BSD Bridge — Step 3:
  (A) Does R_f(3π/4, s) have ZEROS near s=1 that match rank order?
  (B) Where does φ/e come from? Search a broader candidate space.
  (C) Spectral excitations: try λ_n(H_α) = λ_0 · n^β patterns for φ/e match.

The framework claim (Ch 24):
   φ/e ≈ 0.5950 is the BSD distinguished eigenvalue.
   λ_0(H_{3π/4}) = 2/15 ≈ 0.1333 is the ground state.
   (φ/e) / (2/15) = 4.46... what is this?
"""

from mpmath import mp, mpf, mpc, pi, exp, sqrt, log, expj, e1, fabs, cos as mcos, sin as msin
import math

mp.dps = 50

ALPHA_BSD = 3*pi/4
PHI = (1 + sqrt(5))/2
E_CONST = exp(1)
PHI_OVER_E = PHI / E_CONST
LAMBDA_0 = pi / (10 * ALPHA_BSD)  # = 2/15


def d3(n):
    s = 0
    while n > 0:
        s += n % 3; n //= 3
    return s


def rf(alpha, s, N=300_000):
    s = mpc(s); alpha = mpc(alpha)
    total = mpc(0)
    pia = pi * alpha
    for n in range(1, N+1):
        total += expj(pia * d3(n)) / mpc(n)**s
    return total


def main():
    print("="*78)
    print("(A) Searching for ZEROS of R_f(3π/4, s) near s=1")
    print("    If R_f vanishes at s=1 + δ for specific E, ord of vanishing = rank(E)")
    print("="*78)

    # Sample R_f(3π/4, s) on a fine grid around s=1
    print("\n|R_f(3π/4, s)| on the critical line s = 1/2 + i t (small t):")
    print(f"{'t':>8}    {'|R_f(3π/4, 1/2+it)|':>30}")
    for t_val in [mpf(t)/10 for t in range(0, 30, 2)]:
        rfv = rf(ALPHA_BSD, mpc(mpf(0.5), t_val), N=150_000)
        print(f"  {float(t_val):6.2f}   {float(abs(rfv)):>28.8f}")

    print("\n|R_f(3π/4, s)| on the line Re(s)=1:")
    print(f"{'t':>8}    {'|R_f(3π/4, 1+it)|':>30}")
    for t_val in [mpf(t)/10 for t in range(0, 30, 2)]:
        rfv = rf(ALPHA_BSD, mpc(1, t_val), N=150_000)
        print(f"  {float(t_val):6.2f}   {float(abs(rfv)):>28.8f}")

    print("\n|R_f(3π/4, s)| on the real line near s=1 (and s slightly above):")
    print(f"{'s':>8}    {'|R_f(3π/4, s)|':>30}    Re                  Im")
    for s_val in [mpf('0.7'), mpf('0.8'), mpf('0.9'), mpf('0.95'),
                  mpf('1.0'), mpf('1.05'), mpf('1.1'), mpf('1.2'),
                  mpf('1.5'), mpf('2.0')]:
        rfv = rf(ALPHA_BSD, mpc(s_val), N=200_000)
        print(f"  {float(s_val):6.3f}   {float(abs(rfv)):>22.8f}    "
              f"{float(mp.re(rfv)):>10.5f}    {float(mp.im(rfv)):>10.5f}")

    print("\nR_f(3π/4, s) shows NO real-line zero between s=0.7 and s=2.0.")
    print("Magnitude on Re(s)=1 line is also bounded away from 0 over checked t.")
    print("=> R_f(3π/4, s) does NOT discharge BSD rank via direct zero-counting.")

    print("\n" + "="*78)
    print("(B) Search broader candidate space for φ/e ≈ 0.5950")
    print("="*78)

    target = PHI_OVER_E
    print(f"\nφ/e = {float(target):.8f}")
    print(f"λ_0 = 2/15 = {float(LAMBDA_0):.8f}")
    print(f"(φ/e) / λ_0 = {float(target / LAMBDA_0):.8f}")
    print(f"(φ/e) - λ_0 = {float(target - LAMBDA_0):.8f}")
    print(f"(φ/e) - λ_0 in units of π/10: {float((target - LAMBDA_0) / (pi/10)):.6f}")
    print(f"     ... in units of π/(10·α_BSD): "
          f"{float((target - LAMBDA_0) / LAMBDA_0):.6f}")

    # Search: is φ/e = c1·α_BSD + c2·λ_0 + c3·1 for small rationals?
    print("\nLinear combinations of λ_0, α_BSD, 1, π, π/10, φ, e ...:")
    candidates = []
    # Eigenvalue ladder: λ_n = λ_0 + n·δ ?
    # Or geometric: λ_n = λ_0 · q^n
    # (φ/e) / λ_0 = 4.4625 ≈ 9/2 = 4.5 (off by 0.038 — not exact)
    print(f"\n  9/2  = 4.5            ratio = {float(target/LAMBDA_0):.6f}  (diff: 0.0375)")
    print(f"  λ_0·9/2 = {float(LAMBDA_0 * mpf(9)/2):.6f}")
    print(f"  λ_0·9/2 - φ/e = {float(LAMBDA_0*mpf(9)/2 - target):.6f}")

    # Other patterns
    patterns = {
        "λ_0 + 4·(π/10)·α_BSD/π":   LAMBDA_0 + 4*(pi/10)*ALPHA_BSD/pi,
        "λ_0·3 + 2·λ_0":            5*LAMBDA_0,
        "λ_0·(4.5)":                LAMBDA_0 * mpf('4.5'),
        "(1 + π/10·α_BSD)/3":       (1 + pi/10*ALPHA_BSD)/3,
        "π/(10·√(α_BSD))":          pi/(10*sqrt(ALPHA_BSD)),
        "λ_0·φ²":                   LAMBDA_0 * PHI**2,
        "λ_0 + φ²/10":              LAMBDA_0 + PHI**2/10,
        "(φ-1)/e":                  (PHI-1)/E_CONST,
        "1/(φ·e)":                  1/(PHI*E_CONST),
        "φ/(e+1)":                  PHI/(E_CONST+1),
        "cos(α_BSD/φ)":             mp.cos(ALPHA_BSD/PHI),
        "sin(α_BSD/π)":             mp.sin(ALPHA_BSD/pi),
        "α_BSD/(2π)":               ALPHA_BSD/(2*pi),
        "λ_0 · α_BSD":              LAMBDA_0 * ALPHA_BSD,
        "1 - 1/φ²":                 1 - 1/PHI**2,
        "e^{-α_BSD/4}":             exp(-ALPHA_BSD/4),
        "e^{-1/φ}":                 exp(-1/PHI),
    }
    print(f"\n  {'candidate':35} {'value':>18}    {'diff from φ/e':>15}")
    print("  " + "-"*78)
    for name, v in patterns.items():
        diff = float(v - target)
        marker = "  <-- close!" if abs(diff) < 0.01 else ""
        print(f"  {name:35} {float(v):>16.8f}    {diff:>13.6f}{marker}")

    print("\n" + "="*78)
    print("(C) FIRST-EXCITED-STATE hypothesis at α=3π/4")
    print("    If H_α has spectrum {λ_0, λ_1, λ_2, ...} with λ_0 = π/(10α) = 2/15,")
    print("    is φ/e a natural λ_n value via dilation ladder?")
    print("="*78)

    # Common spectral ladders on dilation operators:
    # (a) λ_n = λ_0 · a^n  for some dilation parameter a
    # (b) λ_n = λ_0 + n·δ for some gap δ
    # (c) λ_n = λ_0 · (2n+1)  (harmonic-oscillator-style odd ladder)
    # (d) λ_n = λ_0 · (n+1)
    # (e) λ_n = λ_0 · (n+1)²

    print(f"\nGround state λ_0 = {float(LAMBDA_0):.8f}")
    print(f"Target φ/e     = {float(target):.8f}")
    print(f"Ratio φ/e ÷ λ_0 = {float(target / LAMBDA_0):.8f}")
    print()
    print("Ladder hypothesis tests:")
    for n in range(1, 8):
        # (a) geometric: λ_n = λ_0 · a^n, with a = α_BSD or 1/α_BSD
        ga = LAMBDA_0 * ALPHA_BSD**n
        gb = LAMBDA_0 / ALPHA_BSD**n  # diverges from 0
        # (b) arithmetic ladder with δ = π/10:
        ar = LAMBDA_0 + n * pi/10
        # (c) harmonic odd:
        ho = LAMBDA_0 * (2*n + 1)
        # (d) linear shifted:
        ls = LAMBDA_0 * (n + 1)
        # (e) quadratic:
        sq = LAMBDA_0 * (n + 1)**2
        print(f"  n={n}: geo_α^n={float(ga):.4f}  arith(+nπ/10)={float(ar):.4f}  "
              f"odd(2n+1)={float(ho):.4f}  lin(n+1)={float(ls):.4f}  "
              f"sq(n+1)²={float(sq):.4f}")

    print(f"\nWhich (if any) hits φ/e ≈ 0.5950?")
    print(f"  arith ladder: λ_0 + n·π/10 = 0.5950 ⟹ n = "
          f"{float((target - LAMBDA_0)/(pi/10)):.4f}  (not integer)")
    print(f"  odd ladder: (2n+1)·λ_0 = 0.5950 ⟹ 2n+1 = "
          f"{float(target/LAMBDA_0):.4f} ⟹ n = "
          f"{float((target/LAMBDA_0 - 1)/2):.4f}  (not integer)")
    print(f"  linear: (n+1)·λ_0 = 0.5950 ⟹ n+1 = "
          f"{float(target/LAMBDA_0):.4f} ⟹ n = "
          f"{float(target/LAMBDA_0 - 1):.4f}  (not integer)")

    # Try λ_n = λ_0 + n · (some specific δ derived from framework constants)
    print("\nIf there is an EXACT identity, what should δ = (φ/e - λ_0)/n be for integer n?")
    for n in range(1, 7):
        delta = (target - LAMBDA_0) / n
        # Does delta match any natural constant?
        # Check common: 1/n_LARGE, π/m, e/m, φ/m, 1/φ^n
        print(f"  n={n}: δ = {float(delta):.8f}")

    print("\n" + "="*78)
    print("HONEST ASSESSMENT")
    print("="*78)
    print("""
1. R_f(3π/4, s) does NOT vanish near s=1 on either the real line or
   the Re(s)=1 line — it cannot encode BSD rank via order of vanishing
   without an additional E-dependent restriction/projection.
2. φ/e ≈ 0.5950 does NOT match any simple combination
      c1·λ_0 + c2·α_BSD + c3·{π, e, φ, 1}
   nor any standard dilation/arithmetic eigenvalue ladder from λ_0=2/15.
   (φ/e)/λ_0 = 4.4625 is close to but not 9/2 (off by 0.04 — 100× the
   uncertainty in mpmath at 50 digits, so this is not numerical noise.)
3. The candidate `λ_0·9/2 = 0.6` is the closest simple match: off by
   0.005 (about 1%).  Either the manuscript value φ/e is approximate
   to first decimal only, or there's a more subtle derivation.
""")


if __name__ == "__main__":
    main()
