"""
BSD Application — Step 1
Compute R_f(3π/4, s) at and near s = 1 in high precision.

R_f(α, s) := Σ_{n=1}^∞ e^{iπα D_3(n)} / n^s
where D_3(n) is the base-3 digital sum.

Framework anchors:
  - R_f(0, s) = ζ(s)
  - R_f(1, s) = −η(s)   (proven axiom-free in Lean)
  - R_f(2, s) = ζ(s)    (proven axiom-free in Lean)

BSD-specific:
  - α_BSD = 3π/4 ≈ 2.35619
  - λ_0(H_{3π/4}) = π/(10 · 3π/4) = 2/15 ≈ 0.13333 (universal coupling)
  - bsd_distinguished_eigenvalue = φ/e ≈ 0.5950 (manuscript Ch 24)
  - 4-basis pinning: α_BSD = (π/2) · α_RH = (π/2)(3/2)
"""

from mpmath import mp, mpf, mpc, pi, exp, sqrt, log, zeta, expj, sin, cos, fabs

mp.dps = 50

ALPHA_BSD = 3*pi/4
PHI = (1 + sqrt(5)) / 2
E_CONST = exp(1)


def d3(n):
    """Base-3 digital sum."""
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s


def rf(alpha, s, N=200_000):
    """R_f(alpha, s) truncated to N terms; mpc arithmetic."""
    s = mpc(s)
    alpha = mpc(alpha)
    total = mpc(0)
    pia = pi * alpha
    for n in range(1, N+1):
        phase = expj(pia * d3(n))
        total += phase / mpc(n) ** s
    return total


def rf_derivative_s(alpha, s, N=200_000):
    """∂_s R_f(α, s) = -Σ e^{iπα D_3(n)} log(n) / n^s."""
    s = mpc(s)
    alpha = mpc(alpha)
    total = mpc(0)
    pia = pi * alpha
    for n in range(2, N+1):
        phase = expj(pia * d3(n))
        total += -phase * log(n) / mpc(n) ** s
    return total


def main():
    print("="*70)
    print("R_f(α, s) computation for BSD at α = 3π/4")
    print(f"mp.dps = {mp.dps}, truncation N = 200,000")
    print("="*70)

    print(f"\nα_BSD = 3π/4 = {ALPHA_BSD}")
    print(f"φ/e (distinguished eigenvalue) = {PHI/E_CONST}")
    print(f"π/(10·α_BSD) = 2/15 = {pi/(10*ALPHA_BSD)}")

    # Sanity anchors: R_f(2, s) at s=2 should match ζ(2) = π^2/6
    print("\n--- Sanity check: anchors ---")
    rf_alpha2_s2 = rf(2, 2, N=200_000)
    print(f"R_f(2, 2) = {rf_alpha2_s2}")
    print(f"ζ(2)      = {zeta(2)}")
    print(f"  difference: {fabs(rf_alpha2_s2 - zeta(2))}")

    # R_f(1, 1) should be -log 2 (since R_f(1, s) = -η(s) and η(1) = log 2)
    rf_alpha1_s1 = rf(1, 1, N=200_000)
    target = -log(2)
    print(f"\nR_f(1, 1) = {rf_alpha1_s1}")
    print(f"-log(2)   = {target}")
    print(f"  partial-sum truncation error (η converges very slowly): {fabs(rf_alpha1_s1 - target)}")

    # The main computation: R_f(3π/4, 1)
    print("\n--- Main: R_f(3π/4, 1) ---")
    val = rf(ALPHA_BSD, 1, N=500_000)
    print(f"R_f(3π/4, 1) [N=5e5]  = {val}")
    print(f"  |R_f(3π/4, 1)|      = {abs(val)}")
    print(f"  arg                 = {mp.arg(val)}")
    print(f"  Re                  = {val.real}")
    print(f"  Im                  = {val.imag}")

    print(f"\nφ/e ≈ {PHI/E_CONST}")
    print(f"|R_f(3π/4, 1)| vs φ/e: ratio = {abs(val) / (PHI/E_CONST)}")
    print(f"Re R_f(3π/4, 1) vs φ/e: ratio = {val.real / (PHI/E_CONST)}")

    # Φ(α) per framework: R_f(α,1) = Li_1(e^{iπα}) · Φ(α)
    # Li_1(z) = -log(1-z), so Li_1(e^{iπα}) = -log(1 - e^{iπα})
    z = expj(pi * ALPHA_BSD)
    li1 = -mp.log(1 - z)
    phi_val = val / li1
    print(f"\nLi_1(e^{{iπ·3π/4}}) = -log(1 - e^{{i·3π²/4}}) = {li1}")
    print(f"Φ(3π/4) = R_f / Li_1 = {phi_val}")
    print(f"|Φ(3π/4)|             = {abs(phi_val)}")
    print("  (Refresher claim: |Φ(3π/4)| ≈ 1.52, with Φ ≈ 1.44 + 0.50i)")

    # R_f near s=1: assess order of vanishing
    print("\n--- R_f(3π/4, s) for s near 1 (gauge sensitivity) ---")
    for ds in [mpf('0.1'), mpf('0.01'), mpf('0.001')]:
        v_plus = rf(ALPHA_BSD, mpf(1) + ds, N=300_000)
        v_minus = rf(ALPHA_BSD, mpf(1) - ds, N=300_000)
        print(f"  s=1+{ds}: {v_plus}")
        print(f"  s=1-{ds}: {v_minus}")

    # ∂_s R_f(3π/4, s) at s=1
    print("\n--- ∂_s R_f(3π/4, 1) (does NOT vanish if order zero) ---")
    dval = rf_derivative_s(ALPHA_BSD, 1, N=300_000)
    print(f"∂_s R_f(3π/4, 1) ≈ {dval}")
    print(f"  |∂_s R_f| = {abs(dval)}")


if __name__ == "__main__":
    main()
