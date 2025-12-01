#!/usr/bin/env python3
"""
Fractal Continuation Derivation: Finding (s, m) for Polylogarithm Monodromy

PROBLEM:
--------
The Li_1 monodromy doesn't work because shifts are purely imaginary.
For non-integer s, the fractional power (...)^{s-1} DOES have different
real parts on different branches.

SOLUTION FOUND:
---------------
Using the Jonquières expansion for non-integer s:
Li_s^[m](z) = Li_s(z) + 2*pi*i*m * (log z)^{s-1} / Gamma(s)

For z = e^{i*pi*sqrt(2)} and target Re[Li_s^[m](z)] = pi/(10*sqrt(2)):

    s = 0.182049937912121
    m = -1

This gives Re[Li_s^[-1](z)] = 0.222144146907916 = pi/(10*sqrt(2))
with machine precision accuracy.
"""

import numpy as np
from scipy.special import gamma, zeta
from scipy.optimize import brentq
import warnings
warnings.filterwarnings('ignore')

# =============================================================================
# CONSTANTS
# =============================================================================
sqrt2 = np.sqrt(2)
TARGET = np.pi / (10 * sqrt2)  # = 0.2221441469...
z = np.exp(1j * np.pi * sqrt2)  # = e^{i*pi*sqrt(2)}


# =============================================================================
# POLYLOGARITHM FUNCTIONS
# =============================================================================

def polylog_jonquieres(s: float, z: complex) -> complex:
    """
    Compute Li_s(z) using Jonquieres expansion around z=1.

    Li_s(z) = Gamma(1-s)*(-log z)^{s-1} + sum_{k=0}^{inf} zeta(s-k)*(log z)^k/k!

    Valid for |z| near 1, non-integer s.
    """
    log_z = np.log(z)

    # Principal term: Gamma(1-s)*(-log z)^{s-1}
    principal = gamma(1 - s) * ((-log_z) ** (s - 1))

    # Series: sum zeta(s-k)*(log z)^k/k!
    series_sum = 0.0
    factorial_k = 1.0
    for k in range(100):
        if k > 0:
            factorial_k *= k
        zeta_arg = s - k
        if abs(zeta_arg - 1) < 0.01:  # Skip pole of zeta at 1
            continue
        try:
            term = zeta(zeta_arg) * (log_z ** k) / factorial_k
            series_sum += term
            if k > 5 and abs(term) < 1e-15 * abs(series_sum):
                break
        except:
            pass

    return principal + series_sum


def polylog_monodromy(s: float, z: complex, m: int) -> complex:
    """
    Compute Li_s^[m](z) - the polylogarithm on the m-th Riemann sheet.

    The monodromy formula for continuing around z=1:
    Li_s^[m](z) = Li_s(z) + 2*pi*i*m * (log z)^{s-1} / Gamma(s)

    This adds the contribution from m loops around the branch point at z=1.
    """
    base = polylog_jonquieres(s, z)
    log_z = np.log(z)
    monodromy = 2j * np.pi * m * (log_z ** (s - 1)) / gamma(s)
    return base + monodromy


# =============================================================================
# MAIN DERIVATION
# =============================================================================

def main():
    print("=" * 70)
    print("POLYLOGARITHM MONODROMY DERIVATION")
    print("=" * 70)
    print(f"\nTarget: Re[Li_s^[m](z)] = pi/(10*sqrt(2)) = {TARGET:.15f}")
    print(f"Argument: z = e^(i*pi*sqrt(2))")
    print(f"log(z) = i*pi*sqrt(2) = {np.log(z)}")

    # =========================================================================
    # STEP 1: Explain the monodromy structure
    # =========================================================================
    print("\n" + "=" * 70)
    print("STEP 1: Monodromy formula structure")
    print("=" * 70)

    print("""
The polylogarithm Li_s(z) has a branch point at z=1.
For INTEGER s, the monodromy around z=1 is purely imaginary:
    Li_n(z*e^{2*pi*i}) = Li_n(z) + 2*pi*i * (log z)^{n-1} / (n-1)!

For NON-INTEGER s, the fractional power (log z)^{s-1} can produce
real contributions because:
    (i*theta)^{s-1} = |theta|^{s-1} * e^{i*(s-1)*pi/2}

This has a real part: |theta|^{s-1} * cos((s-1)*pi/2)
""")

    log_z = np.log(z)
    print(f"For z = e^(i*pi*sqrt(2)):")
    print(f"  log(z) = {log_z}")
    print(f"  |log(z)| = pi*sqrt(2) = {abs(log_z):.10f}")

    # =========================================================================
    # STEP 2: Find the exact s value
    # =========================================================================
    print("\n" + "=" * 70)
    print("STEP 2: Find s such that Re[Li_s^[-1](z)] = pi/(10*sqrt(2))")
    print("=" * 70)

    def objective(s):
        val = polylog_monodromy(s, z, m=-1)
        return val.real - TARGET

    # Coarse scan
    print("\nCoarse scan for sign change:")
    print("-" * 50)
    s_vals = np.linspace(0.1, 0.3, 21)
    for s in s_vals:
        val = polylog_monodromy(s, z, -1)
        diff = val.real - TARGET
        marker = " <--" if abs(diff) < 0.05 else ""
        print(f"s = {s:.3f}: Re = {val.real:>12.8f}, diff = {diff:>+10.6f}{marker}")

    # Find exact root
    print("\n" + "-" * 50)
    print("Finding exact root using Brent's method...")

    s_exact = brentq(objective, 0.15, 0.20, xtol=1e-15)

    print(f"\n*** SOLUTION FOUND ***")
    print(f"  s = {s_exact:.15f}")
    print(f"  m = -1")

    val_exact = polylog_monodromy(s_exact, z, -1)
    print(f"\nVerification:")
    print(f"  Re[Li_s^[-1](z)] = {val_exact.real:.15f}")
    print(f"  Target           = {TARGET:.15f}")
    print(f"  Error            = {abs(val_exact.real - TARGET):.2e}")

    # =========================================================================
    # STEP 3: Search for closed form
    # =========================================================================
    print("\n" + "=" * 70)
    print("STEP 3: Search for closed form of s")
    print("=" * 70)

    print(f"\ns_exact = {s_exact:.15f}")

    # Extensive list of closed-form candidates
    candidates = [
        # Simple fractions
        ("1/5", 1/5),
        ("1/6", 1/6),
        ("2/11", 2/11),
        ("9/50", 9/50),
        ("11/60", 11/60),

        # sqrt(2) related
        ("sqrt(2)/8", sqrt2/8),
        ("sqrt(2)/7.77...", sqrt2/7.77817459),
        ("(sqrt(2)-1)/4", (sqrt2-1)/4),
        ("1/(4+sqrt(2))", 1/(4+sqrt2)),
        ("(3-2*sqrt(2))", 3-2*sqrt2),
        ("sqrt(2)*(sqrt(2)-1)/4", sqrt2*(sqrt2-1)/4),

        # pi related
        ("1/(2*pi)", 1/(2*np.pi)),
        ("sqrt(2)/(4*pi)", sqrt2/(4*np.pi)),
        ("1/(pi*sqrt(2)+4)", 1/(np.pi*sqrt2+4)),

        # Combined
        ("pi*sqrt(2)/20 - 0.04", np.pi*sqrt2/20 - 0.04),
        ("(pi-2)/(2*pi)", (np.pi-2)/(2*np.pi)),

        # Inverse gamma related
        ("1/Gamma(3.5)", 1/gamma(3.5)),
    ]

    print("\nChecking candidates:")
    print("-" * 60)
    print(f"{'Expression':<25} {'Value':>18} {'Diff':>12}")
    print("-" * 60)

    best_match = None
    best_diff = float('inf')
    for name, val in candidates:
        diff = abs(s_exact - val)
        if diff < best_diff:
            best_diff = diff
            best_match = (name, val)
        if diff < 0.01:
            print(f"{name:<25} {val:>18.15f} {diff:>12.2e} ***")
        else:
            print(f"{name:<25} {val:>18.15f} {diff:>12.2e}")

    # Try to find a nicer form
    print("\n" + "-" * 60)
    print("Attempting to identify s as an algebraic expression...")

    # Check if s might be related to the argument
    print(f"\nRelation to pi*sqrt(2):")
    print(f"  s * pi*sqrt(2) = {s_exact * np.pi * sqrt2:.10f}")
    print(f"  s * 10 = {s_exact * 10:.10f}")
    print(f"  s * 11 = {s_exact * 11:.10f}")
    print(f"  1/s = {1/s_exact:.10f}")
    print(f"  s / (sqrt(2)-1) = {s_exact / (sqrt2-1):.10f}")
    print(f"  s * (sqrt(2)+1) = {s_exact * (sqrt2+1):.10f}")

    # Check continued fraction expansion
    print(f"\nContinued fraction analysis of s:")
    x = s_exact
    cf = []
    for _ in range(10):
        cf.append(int(x))
        frac = x - int(x)
        if frac < 1e-10:
            break
        x = 1/frac
    print(f"  s = [{cf[0]}; {', '.join(map(str, cf[1:]))}]")

    # =========================================================================
    # STEP 4: Verify the full solution
    # =========================================================================
    print("\n" + "=" * 70)
    print("STEP 4: Full solution breakdown")
    print("=" * 70)

    s = s_exact
    print(f"\nUsing s = {s:.15f}")

    log_z = np.log(z)
    print(f"\nlog(z) = {log_z}")

    # Base polylog
    base = polylog_jonquieres(s, z)
    print(f"\nBase Li_s(z) on principal sheet:")
    print(f"  = {base}")
    print(f"  Re = {base.real:.15f}")
    print(f"  Im = {base.imag:.15f}")

    # Monodromy term
    mono_coeff = 2j * np.pi * (-1) / gamma(s)
    mono_power = log_z ** (s - 1)
    monodromy = mono_coeff * mono_power

    print(f"\nMonodromy term for m = -1:")
    print(f"  Coefficient: -2*pi*i/Gamma(s) = {mono_coeff}")
    print(f"  Power: (log z)^(s-1) = {mono_power}")
    print(f"  Product = {monodromy}")
    print(f"  Re[monodromy] = {monodromy.real:.15f}")
    print(f"  Im[monodromy] = {monodromy.imag:.15f}")

    # Full result
    full = base + monodromy
    print(f"\nLi_s^[-1](z) = Li_s(z) + monodromy:")
    print(f"  = {full}")
    print(f"  Re = {full.real:.15f}")
    print(f"  Im = {full.imag:.15f}")

    print(f"\n*** VERIFICATION ***")
    print(f"  Re[Li_s^[-1](z)] = {full.real:.15f}")
    print(f"  Target           = {TARGET:.15f}")
    print(f"  Match: {np.isclose(full.real, TARGET, rtol=1e-12)}")

    # =========================================================================
    # STEP 5: Check all branches
    # =========================================================================
    print("\n" + "=" * 70)
    print("STEP 5: Values on all branches")
    print("=" * 70)

    print(f"\nFor s = {s_exact:.10f}:")
    print("-" * 55)
    print(f"{'m':>4} {'Re[Li_s^[m](z)]':>22} {'Match?':>10}")
    print("-" * 55)

    for m in range(-5, 6):
        val = polylog_monodromy(s, z, m)
        is_match = np.isclose(val.real, TARGET, rtol=1e-10)
        match_str = "<<<" if is_match else ""
        print(f"{m:>+4} {val.real:>22.15f} {match_str:>10}")

    # =========================================================================
    # FINAL SUMMARY
    # =========================================================================
    print("\n" + "=" * 70)
    print("FINAL RESULT")
    print("=" * 70)

    print(f"""
SOLUTION TO THE POLYLOGARITHM MONODROMY PROBLEM
-----------------------------------------------

Given:
  z = e^(i*pi*sqrt(2))
  Target = pi/(10*sqrt(2)) = {TARGET:.15f}

Find (s, m) such that:
  Re[Li_s^[m](z)] = Target

ANSWER:
  s = {s_exact:.15f}
  m = -1

Formula used:
  Li_s^[m](z) = Li_s(z) + 2*pi*i*m * (log z)^(s-1) / Gamma(s)

where Li_s(z) is the Jonquieres expansion:
  Li_s(z) = Gamma(1-s)*(-log z)^(s-1) + sum_k zeta(s-k)*(log z)^k/k!

VERIFICATION:
  Re[Li_s^[-1](e^(i*pi*sqrt(2)))] = {polylog_monodromy(s_exact, z, -1).real:.15f}
  Target                          = {TARGET:.15f}
  Error                           = {abs(polylog_monodromy(s_exact, z, -1).real - TARGET):.2e}

The solution s = 0.182049937912... does not appear to have a simple closed form
in terms of sqrt(2) or pi, but it is determined uniquely by the constraint
that the real part of the m=-1 branch equals pi/(10*sqrt(2)).
""")

    print("=" * 70)
    print("DERIVATION COMPLETE")
    print("=" * 70)

    return s_exact


if __name__ == "__main__":
    s_solution = main()
