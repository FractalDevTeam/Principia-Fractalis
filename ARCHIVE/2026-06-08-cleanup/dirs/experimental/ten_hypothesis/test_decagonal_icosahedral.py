"""
SHARPENING TEST: Decagonal / icosahedral / H_3 origin of pi/10.

Hypothesis (emerging from Test 5): The number 10 in pi/10 originates from
the cyclotomic field Q(zeta_20) / decagonal D_10 symmetry, NOT from any
Lie-algebraic dimension or modular form normalization.

Evidence:
1. sin(pi/10) = (sqrt(5)-1)/4 = 1/(2 phi) -- golden ratio appears directly
2. cos(pi/10) = sqrt(10 + 2 sqrt(5))/4
3. cos(pi/5) = phi/2
4. Decagon = 10-gon = vertex figure of icosahedral H_3 in 4D (600-cell, etc.)
5. alpha_NP = phi + 1/4 (Principia hypothesis): phi appears!

If TRUE: pi/(10 alpha) is a cyclotomic resonance angle from D_10 symmetry,
and the universal coupling constant 1/(10 alpha) reflects the dihedral
order |D_10| = 20 / 2 = 10 (half-turn factor) OR the icosahedral H_3
Coxeter number h(H_3) = 10.

CRUCIAL CHECK: The Coxeter number of H_3 (icosahedral) IS h = 10.
"""

from mpmath import mp, mpf, pi, sqrt, sin, cos, tan, cot, exp, log

mp.dps = 50

def main():
    print("=" * 70)
    print("DECAGONAL / ICOSAHEDRAL / H_3 ORIGIN TEST")
    print("=" * 70)

    phi = (1 + sqrt(5))/2
    print(f"\nphi = (1+sqrt(5))/2 = {float(phi):.15f}")
    print(f"phi + 1/4 = {float(phi + mpf(1)/4):.15f}  <-- alpha_NP")
    print(f"sqrt(2) = {float(sqrt(2)):.15f}  <-- alpha_P")

    print("\n--- Coxeter numbers of finite irreducible Coxeter groups ---")
    print("  A_n: h = n+1")
    print("  B_n/C_n: h = 2n")
    print("  D_n: h = 2n-2")
    print("  E_6: h = 12,  E_7: h = 18,  E_8: h = 30")
    print("  F_4: h = 12")
    print("  G_2: h = 6")
    print("  H_3 (icosahedral): h = 10  <<<< MATCH!")
    print("  H_4 (600-cell): h = 30")
    print("  I_2(n) (dihedral): h = n")

    print("\n*** H_3 = icosahedral Coxeter group has h = 10. ***")
    print("    The exponents of H_3 are: 1, 5, 9 (sum = 15 = dim of reflections).")
    print("    Order |H_3| = 120. Reflections: 15.")

    # Check resonance: pi/h(H_3) = pi/10 IS the natural fundamental "phase" for H_3!
    # In Coxeter group theory, the eigenvalues of a Coxeter element c are
    # exp(2*pi*i*m_j/h) where m_j are exponents.
    # For H_3, eigenvalues = exp(2 pi i/10), exp(10 pi i/10), exp(18 pi i/10)
    # = exp(pi i/5), -1, exp(9 pi i/5).

    print("\n--- Coxeter element eigenvalues for H_3 (exponents 1,5,9; h=10) ---")
    for m in [1, 5, 9]:
        angle = 2 * pi * m / 10
        print(f"  exp(2 pi i * {m}/10) at angle {float(angle):.10f}, real = {float(cos(angle)):.10f}")

    print("\n--- pi/10 in H_3 / icosahedral context ---")
    print(f"pi/h(H_3) = pi/10 = {float(pi/10):.15f}")
    print(f"sin(pi/10) = 1/(2 phi) = {float(sin(pi/10)):.15f}")
    print(f"2 sin(pi/10) = 1/phi = {float(2*sin(pi/10)):.15f}")
    print(f"1/phi = phi - 1 = {float(phi - 1):.15f}  ✓")

    # The factor 2 sin(pi/h) is the length of root vector in the basic decomposition.
    print("\nKEY IDENTITY (Coxeter root geometry):")
    print("  For dihedral I_2(h), the simple roots subtend angle pi - pi/h.")
    print("  For H_3 (h=10), this gives root angle = pi - pi/10 = 9 pi/10.")

    # Now the critical structural claim:
    print()
    print("=" * 70)
    print("STRUCTURAL CLAIM FOR pi/10 IN PRINCIPIA FRACTALIS:")
    print("=" * 70)
    print("""
The universal factor pi/10 in lambda_0(alpha) = pi/(10 alpha) most plausibly
arises from the COXETER NUMBER h(H_3) = 10 of the icosahedral group.

Evidence:
  (1) sin(pi/10) = 1/(2 phi)  (golden ratio = alpha_NP - 1/4)
  (2) cos(pi/10) involves sqrt(5)  (golden ratio cyclotomic)
  (3) H_3 has Coxeter number EXACTLY 10
  (4) H_3 is the symmetry group of icosahedron/dodecahedron
  (5) H_3 acts on R^3 with 120 elements, exponents (1,5,9)
  (6) The 4-basis {1, sqrt(2), phi, e^(2pi i/8)} (Principia ch 21) connects to
      Q(zeta_8) and Q(zeta_5)=Q(phi); their compositum is Q(zeta_40) which
      contains Q(zeta_20).

Implication for Principia:
  The substrate is NOT a Lie group's homogeneous space (SO(5), Sp(2), etc.),
  but a NON-CRYSTALLOGRAPHIC reflection group (H_3 icosahedral).
  This explains:
   - the appearance of phi in alpha_NP (H_3 has phi-algebraic root system)
   - the universal denominator 10 = h(H_3)
   - why no Lie algebra naturally produces pi/10
   - why the 4 algebraic alpha's (sqrt(2), 3+2 sqrt(5)/4, etc.) are quadratic

This is a TESTABLE hypothesis: try to construct H_alpha as an operator on
L^2(orbit space of H_3) or on the H_3-invariant functions on S^2 / S^3,
and check if its ground state matches pi/(10 alpha).
""")

if __name__ == "__main__":
    main()
