"""
TEST: Manuscript Ch 21 line 539-627 polylog branch claim.

The manuscript explicitly conjectures that the operator H_P's ground state is
   λ_0(H_P) = Re[Li_{s*}(z_*)] on a non-principal branch,
where:
   z_* = e^{iπα} with α = √2
   s* = √2/2 (per line 627; "non-integer effective weight s* = √2/2")

NONE of today's substrate tests checked Li_s for non-integer s on non-principal
branches. We tested V_α-convolution operators, which were the WRONG operator.

This test: directly evaluate Li_s(e^{iπα}) for various s near √2/2 and various
α, on principal and several monodromy branches. Look for π/(10α).

Use mpmath polylog at 50-digit precision.
"""
from mpmath import mp, mpc, mpf, pi, exp, log, sqrt, polylog, gamma, nstr
import sys

mp.dps = 50

def main():
    print(f"Precision: {mp.dps} digits\n")

    # Target: λ_0(H_P) at α=√2 is π/(10√2)
    sqrt2 = sqrt(2)
    target = pi / (10 * sqrt2)
    print(f"Target: π/(10√2) = {nstr(target, 30)}")
    print()

    # The manuscript's relevant z_* = e^{iπ√2}
    z = exp(mpc(0, pi * sqrt2))
    print(f"z* = e^(iπ√2) = {nstr(z, 20)}")
    print(f"|z*| = {nstr(abs(z), 10)}  (should be 1)")
    print()

    # Test 1: Principal-branch Li_s(z) for various s near √2/2
    print("=" * 60)
    print("TEST 1: Li_s(e^{iπ√2}) on PRINCIPAL branch")
    print("=" * 60)
    for s_name, s_val in [
        ("1 (Mayer)", mpf(1)),
        ("1/2", mpf("0.5")),
        ("√2/2", sqrt2/2),
        ("√2", sqrt2),
        ("0 (Stieltjes)", mpf(0)),
        ("-1", mpf(-1)),
        ("π/10", pi/10),
    ]:
        try:
            val = polylog(s_val, z)
            diff = abs(val.real - target)
            print(f"  s = {s_name:15s}: Li_s = {nstr(val, 15)}")
            print(f"                       Re = {nstr(val.real, 15)},  |Re-target|={nstr(diff, 6)}")
        except Exception as e:
            print(f"  s = {s_name}: ERROR {e}")
        sys.stdout.flush()
    print()

    # Test 2: At various α, evaluate Li_s with the manuscript-prescribed s = α/2
    print("=" * 60)
    print("TEST 2: Manuscript prescription λ_0(α) = Re[Li_{α/2}(e^{iπα})] ?= π/(10α)")
    print("=" * 60)
    for alpha_name, alpha_val in [
        ("1",      mpf(1)),
        ("√2",     sqrt2),
        ("3/2",    mpf("1.5")),
        ("φ",      (1+sqrt(5))/2),
        ("φ+1/4",  (1+sqrt(5))/2 + mpf("0.25")),
        ("2",      mpf(2)),
        ("3π/4",   3*pi/4),
        ("3π/2",   3*pi/2),
        ("√(2π)",  sqrt(2*pi)),
    ]:
        target_alpha = pi / (10 * alpha_val)
        z_alpha = exp(mpc(0, pi * alpha_val))
        s_alpha = alpha_val / 2

        try:
            val = polylog(s_alpha, z_alpha)
            re_val = val.real
            im_val = val.imag
            diff = abs(re_val - target_alpha)
            print(f"  α={alpha_name:8s}  s=α/2={nstr(s_alpha,8)},  z=exp(iπα)={nstr(z_alpha,12)}")
            print(f"     Li_s(z) = {nstr(val, 15)}")
            print(f"     target π/(10α) = {nstr(target_alpha, 15)}")
            print(f"     |Re - target| = {nstr(diff, 6)},  ratio Re/target = {nstr(re_val/target_alpha, 8)}")
        except Exception as e:
            print(f"  α={alpha_name}: ERROR {e}")
        sys.stdout.flush()
        print()

    # Test 3: M_0 monodromy = add k·2πi to log z, then take Li_s.
    # For Li_1: Li_1(z) = -log(1-z), so M_0 doesn't help (changes Im not Re).
    # For non-integer s: Li_s on the M_0 sheet differs by a polynomial in log z.
    # The Jonquières inversion: Li_s(z) + (-1)^s Li_s(1/z) = (2πi)^s · B_s(...) for integer s.
    # For non-integer s, monodromy: Li_s(z e^{2πi·k}) = Li_s(z) + (2πi/Γ(s))·log^{s-1}(z)·... etc.

    print("=" * 60)
    print("TEST 3: M_0-monodromy-shifted Li_s at α=√2, s=√2/2")
    print("=" * 60)
    # Δ_s(z) = -2π · Im[ (log z)^{s-1} / Γ(s) ] (manuscript line 829)
    # The M_0 monodromy of Li_s adds (2πi)^s / Γ(s) · (log z)^{s-1} per loop
    # We test the prediction: principal Re + k·(real part of monodromy increment) = π/(10α)
    s = sqrt2 / 2
    alpha = sqrt2
    z_a = exp(mpc(0, pi * alpha))
    log_z = mpc(0, pi * alpha)  # principal log
    target_a = pi / (10 * alpha)

    print(f"  s = √2/2 = {nstr(s, 15)}")
    print(f"  α = √2, target = π/(10√2) = {nstr(target_a, 15)}")
    val_principal = polylog(s, z_a)
    print(f"  Principal Li_s(z) = {nstr(val_principal, 15)}")
    print(f"  Re = {nstr(val_principal.real, 12)},  target = {nstr(target_a, 12)}")

    # Per manuscript line 762-829: monodromy increment is
    # Δ_s(z) = -2π · Im[(log z)^{s-1} / Γ(s)]   (real part shift per loop)
    # Test by adding k·Δ_s for k = 1, 2, ..., 10
    print(f"\n  Monodromy increment Δ_s(z) per loop:")
    delta_s = -2*pi * ((log_z)**(s-1) / gamma(s)).imag
    print(f"  Δ_s(e^(iπ√2)) = -2π·Im[(iπ√2)^(s-1)/Γ(s)] = {nstr(delta_s, 12)}")

    print(f"\n  Shifted real parts: Re[Li_s] + k·Δ_s")
    for k in range(-5, 6):
        shifted = val_principal.real + k * delta_s
        diff = abs(shifted - target_a)
        marker = " <-- MATCH" if diff < mpf("0.001") else ""
        print(f"    k={k:+d}: Re = {nstr(shifted, 15)},  |diff|={nstr(diff, 6)}{marker}")
    sys.stdout.flush()
    print()

    # Test 4: ALSO try s = α (not α/2) and s = 1/α
    print("=" * 60)
    print("TEST 4: Other natural choices of s = f(α)")
    print("=" * 60)
    sqrt2 = sqrt(2)
    for desc, s_fn in [
        ("s = α/2",   lambda a: a/2),
        ("s = α",     lambda a: a),
        ("s = 1/α",   lambda a: 1/a),
        ("s = α²/2",  lambda a: a*a/2),
        ("s = 2/α",   lambda a: 2/a),
        ("s = π·α",   lambda a: pi*a),
        ("s = π/α",   lambda a: pi/a),
    ]:
        print(f"\n  --- {desc} ---")
        good = 0
        for alpha_name, alpha_val in [("1",mpf(1)),("√2",sqrt2),("3/2",mpf("1.5")),("2",mpf(2)),("√(2π)",sqrt(2*pi))]:
            target_a = pi / (10 * alpha_val)
            z_a = exp(mpc(0, pi * alpha_val))
            s_a = s_fn(alpha_val)
            try:
                val = polylog(s_a, z_a)
                diff = abs(val.real - target_a)
                relerr = diff / target_a if target_a != 0 else mpf(0)
                marker = " <-- HIT" if relerr < mpf("0.01") else ""
                print(f"     α={alpha_name:6s} s={nstr(s_a,8)}: Re={nstr(val.real,10)}, target={nstr(target_a,10)}, relerr={nstr(relerr,6)}{marker}")
                if relerr < mpf("0.01"):
                    good += 1
            except Exception as e:
                print(f"     α={alpha_name}: ERROR {e}")
        if good >= 3:
            print(f"   ★ THIS CHOICE OF s GIVES π/(10α) AT {good}+ values ★")
        sys.stdout.flush()

if __name__ == "__main__":
    main()
