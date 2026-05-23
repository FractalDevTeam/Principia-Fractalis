"""
Apply the framework: characterize Φ(α) in R_f(α, 1) = Li_1(e^{iπα}) · Φ(α).

The framework provides:
  R_f(α, s) = Σ e^(iπα D_3(n)) / n^s
  Li_1(z) = -log(1 - z)
  Bridge identity: R_f(α, 1) = Li_1(e^{iπα}) · Φ(α)

CHECK CONDITIONS from proven anchors:
  Φ(1) = 1 (since R_f(1,1) = -log 2 and Li_1(-1) = -log 2)
  Φ(2) finite (R_f(2,1) and Li_1(1) both diverge; ratio should be finite)

Today's goal: compute Φ(α) for the framework's α-instances and identify structure.

The framework PREDICTS: leading order R_f(α, 1) = πα/10. So Φ(α) ≈ (πα/10)/Li_1(e^{iπα}) at small α.
"""
from mpmath import mp, mpc, mpf, pi, exp, log, sqrt, nstr
import sys

mp.dps = 40

def d3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

def Rf_partial(alpha, s, N, d3_table):
    total = mpc(0)
    for n in range(1, N + 1):
        phase = exp(mpc(0, pi * alpha * d3_table[n]))
        total += phase / mpc(n) ** s
    return total

def Li_1(z):
    """Li_1(z) = -log(1 - z) on principal branch."""
    return -log(1 - z)

def Phi(alpha, N, d3_table):
    """Φ(α) = R_f(α, 1) / Li_1(e^{iπα}).
    Use Re(s) slightly > 1 for convergence, then take limit."""
    # Compute R_f at s slightly > 1 for convergence
    s = mpc(mpf("1.0001"), 0)  # near s=1 for regularization
    Rf = Rf_partial(alpha, s, N, d3_table)
    z = exp(mpc(0, pi * alpha))
    Li = Li_1(z)
    return Rf / Li

def main():
    N = 10000
    d3t = [d3(n) for n in range(N + 1)]
    print(f"Computing Φ(α) at N={N} terms, precision {mp.dps} digits")
    print(f"Bridge: R_f(α, 1) = Li_1(e^{{iπα}}) · Φ(α)")
    print()

    # Check conditions
    print("=" * 70)
    print("CHECK CONDITIONS at integer α (where R_f has proven closed forms)")
    print("=" * 70)

    # α = 1: R_f(1, s) = -η(s), R_f(1, 1) = -log 2; Li_1(-1) = -log 2; Φ(1) = 1
    print(f"\nα = 1:")
    Rf_at_1 = Rf_partial(mpf(1), mpf(1), N, d3t)
    Li_at_neg1 = Li_1(mpc(-1, 0))
    Phi_at_1_emp = Rf_at_1 / Li_at_neg1
    print(f"  R_f(1,1) numerical = {nstr(Rf_at_1, 10)}")
    print(f"  -log 2             = {nstr(-log(2), 10)}")
    print(f"  Li_1(-1)           = {nstr(Li_at_neg1, 10)}")
    print(f"  Φ(1) = R_f(1,1)/Li_1(-1) = {nstr(Phi_at_1_emp, 10)}")
    print(f"  PREDICTED: Φ(1) = 1")
    sys.stdout.flush()

    # α = 2: pole structure
    print(f"\nα = 2 (R_f(2, s) = ζ(s), pole at s=1):")
    # Use s = 1 + ε to avoid pole
    eps = mpf("0.01")
    Rf_at_2 = Rf_partial(mpf(2), mpc(1 + eps, 0), N, d3t)
    Li_at_1_eps = Li_1(exp(mpc(0, pi * 2)))  # Li_1(e^{2πi}) = Li_1(1) = ∞
    # Since z=1 is on cut, use z slightly off
    Li_at_1_approx = Li_1(mpc(1 - eps, 0))  # approach z=1 from below
    print(f"  R_f(2, 1+ε) at ε={eps} = {nstr(Rf_at_2, 10)}")
    print(f"  Li_1(1-ε)              = {nstr(Li_at_1_approx, 10)}")
    # Both diverge as ε → 0; ratio may be finite
    Phi_at_2_emp = Rf_at_2 / Li_at_1_approx
    print(f"  Φ(2) ratio (ε={eps})   = {nstr(Phi_at_2_emp, 10)}")
    print(f"  PREDICTED: Φ(2) finite (probably ≈ 1, or 1/2, or similar)")
    sys.stdout.flush()

    # Compute Φ(α) at all 9 framework α-instances
    print()
    print("=" * 70)
    print("Φ(α) AT THE 9 FRAMEWORK α-INSTANCES")
    print("=" * 70)
    sqrt2 = sqrt(2)
    phi = (1 + sqrt(5)) / 2
    alphas = [
        ("1 (Poincaré)",      mpf(1)),
        ("3/2 (RH)",           mpf("1.5")),
        ("√2 (P)",             sqrt2),
        ("φ+1/4 (NP)",         phi + mpf("0.25")),
        ("3π/4 (BSD)",         3*pi/4),
        ("3π/2 (NS)",          3*pi/2),
        ("2 (YM)",             mpf(2)),
        ("φ (Hodge)",          phi),
        ("√(2π) (QG)",         sqrt(2*pi)),
    ]
    print(f"{'α':<25} {'Φ(α) numerical':<35} {'|Φ|':<15}")
    print("-" * 70)
    for name, alpha_val in alphas:
        try:
            Phi_val = Phi(alpha_val, N, d3t)
            print(f"{name:<25} {nstr(Phi_val, 10):<35} {nstr(abs(Phi_val), 8):<15}")
            sys.stdout.flush()
        except Exception as e:
            print(f"{name:<25} ERROR: {e}")
            sys.stdout.flush()

    print()
    print("=" * 70)
    print("LEADING-ORDER PREDICTION TEST")
    print("=" * 70)
    print("Framework predicts: R_f(α, 1) = πα/10 + O(α²) at leading order.")
    print("Hence: Φ(α) · Li_1(e^{iπα}) should ≈ πα/10 for small α.")
    print()
    print(f"{'α':<15} {'R_f(α,1) num':<30} {'πα/10':<20} {'|diff|':<12}")
    print("-" * 80)
    for a_val in [mpf("0.01"), mpf("0.05"), mpf("0.1"), mpf("0.2"), mpf("0.5"), mpf("0.7"), mpf("1.0")]:
        try:
            # Use s slightly > 1 for convergence
            Rf_at_a = Rf_partial(a_val, mpc(mpf("1.001"), 0), N, d3t)
            predicted = pi * a_val / 10
            diff = abs(Rf_at_a - mpc(predicted, 0))
            print(f"{nstr(a_val,6):<15} {nstr(Rf_at_a,15):<30} {nstr(predicted,12):<20} {nstr(diff,6):<12}")
            sys.stdout.flush()
        except Exception as e:
            print(f"α={a_val}: ERROR {e}")

if __name__ == "__main__":
    main()
