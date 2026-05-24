"""
01: lambda_0(H_QG) closed-form identities at alpha = sqrt(2*pi).

Framework: universal coupling lambda_0(H_alpha) = pi / (10*alpha).
At alpha_QG = sqrt(2*pi) this becomes pi / (10*sqrt(2*pi)).

Goal: derive the cleanest algebraically equivalent forms and pick
the one most natural for Lean formalization (only Real.sqrt + pi).

Run: python 01_lambda_QG_closed_forms.py
"""
from mpmath import mp, mpf, pi, sqrt, mpc

mp.dps = 50  # 50-digit precision

alpha_QG = sqrt(2 * pi)
lambda_QG_canonical = pi / (10 * alpha_QG)            # canonical
form_A = sqrt(pi) / (10 * sqrt(mpf(2)))               # sqrt(pi)/(10 sqrt 2)
form_B = mpf(1) / 10 * sqrt(pi / 2)                   # (1/10) sqrt(pi/2)
form_C = pi / (10 * sqrt(2 * pi))                     # original canonical
form_D = mpf(1) / (10 * sqrt(2 / pi))                 # 1 / (10 sqrt(2/pi))
form_E = sqrt(2 * pi) / 20                            # alpha_QG / 20  (since pi / (10 alpha) = alpha / 20 iff alpha^2 = 2 pi)

# The last identity is the *deepest*: lambda_0 = alpha_QG / 20.
# Proof: alpha_QG^2 = 2 pi  =>  pi = alpha_QG^2 / 2
#        =>  pi / (10 * alpha_QG) = alpha_QG / 20.

forms = {
    "canonical pi/(10*sqrt(2*pi))": form_C,
    "sqrt(pi)/(10*sqrt(2))": form_A,
    "(1/10)*sqrt(pi/2)": form_B,
    "1/(10*sqrt(2/pi))": form_D,
    "alpha_QG/20 [DEEPEST: uses alpha_QG^2 = 2 pi]": form_E,
}

print("=" * 78)
print("Closed-form values of lambda_0(H_QG)  [50-digit mpmath]")
print("=" * 78)
print(f"alpha_QG = sqrt(2*pi) = {alpha_QG}")
print()
for label, val in forms.items():
    diff = abs(val - lambda_QG_canonical)
    print(f"  {label}")
    print(f"     value = {val}")
    print(f"     |diff vs canonical| = {diff}")
    print()

# Bracket check: 0.125 < lambda_0 < 0.126
print("Bracket check:")
print(f"  0.125  < lambda_0  ?  {mpf('0.125') < lambda_QG_canonical}")
print(f"  lambda_0 < 0.126   ?  {lambda_QG_canonical < mpf('0.126')}")
print(f"  numerical: {float(lambda_QG_canonical):.10f}")

# Lean naturality: which form uses only Real.sqrt + pi (no nested sqrt of irrational ratios)?
# - form A: sqrt(pi)/(10*sqrt(2))   -> two Real.sqrt calls, both on simple constants
# - form E: sqrt(2*pi)/20            -> one Real.sqrt of (2*pi)
# Form E is the SHARPEST: a single sqrt, integer denominator, uses the
# defining algebraic relation alpha_QG^2 = 2*pi directly.

print()
print("LEAN-NATURAL FORM RANKING (fewest primitives):")
print("  1. alpha_QG / 20            -> uses defined alpha_QG, integer denom (BEST)")
print("  2. sqrt(2*pi) / 20          -> one Real.sqrt, one mul, integer denom")
print("  3. sqrt(pi)/(10*sqrt(2))    -> two Real.sqrt calls")
print("  4. (1/10)*sqrt(pi/2)        -> one sqrt on a ratio (needs division in arg)")
print("  5. pi/(10*sqrt(2*pi))       -> canonical but division by an irrational")

# Cross-check the algebraic identity alpha_QG/20 = pi/(10*alpha_QG):
# alpha_QG/20 * 10 * alpha_QG = alpha_QG^2 / 2 = 2*pi/2 = pi.  QED.
identity_check = alpha_QG / 20 * 10 * alpha_QG
print()
print(f"Algebraic identity check: (alpha_QG/20) * 10 * alpha_QG = {identity_check}")
print(f"                                                  pi   = {pi}")
print(f"  difference = {abs(identity_check - pi)}")
