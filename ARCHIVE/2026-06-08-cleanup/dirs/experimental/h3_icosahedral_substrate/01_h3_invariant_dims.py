"""
Task 1: H_3 (icosahedral) invariant dimensions on each spherical-harmonic level l.

The icosahedral rotation group I (= A_5, order 60) acts on S^2.
H_3 = full icosahedral group (with reflections), order 120.
Invariant dimension at level l is given by Molien-style character integration:

  dim V_l^I = (1/|G|) sum_{g in G} chi_l(g)

where chi_l(g) = sin((2l+1)*theta_g/2) / sin(theta_g/2) for rotation g by angle theta_g.

For the full H_3 (with inversion / reflections), one combines parity:
  Invariant polynomial harmonics of degree l for I exist iff l in {0, 6, 10, 12, 15, 16, 18, ...}
  (the famous icosahedral spectrum; l=15 is odd / pseudoscalar).
  For H_3 (with reflections), the truly invariant set is l in {0, 6, 10, 12, 16, 18, 20, 22, 24, 26, ...}.

We compute dimensions via the character-integration formula over conjugacy classes
of the rotation group I = A_5.
"""

import numpy as np
from fractions import Fraction

# Conjugacy classes of I = A_5 (icosahedral rotation group, order 60):
# class label : (rotation angle theta, # elements)
PI = np.pi
CONJ_CLASSES_I = [
    ("e",        0.0,            1),   # identity
    ("12 C_5",   2*PI/5,         12),  # rotations by 72  deg (vertex axes)
    ("12 C_5^2", 4*PI/5,         12),  # rotations by 144 deg (vertex axes)
    ("20 C_3",   2*PI/3,         20),  # rotations by 120 deg (face axes)
    ("15 C_2",   PI,             15),  # rotations by 180 deg (edge axes)
]
ORDER_I = 60
assert sum(c[2] for c in CONJ_CLASSES_I) == ORDER_I

def chi_l(theta, l):
    """SO(3) irrep character on a rotation by angle theta: sin((2l+1)theta/2)/sin(theta/2)."""
    if abs(theta) < 1e-12:
        return 2*l + 1
    return np.sin((2*l + 1)*theta/2.0) / np.sin(theta/2.0)

def dim_I_invariant(l):
    """Multiplicity of trivial rep of I in restriction of SO(3) irrep V_l."""
    s = 0.0
    for label, theta, mult in CONJ_CLASSES_I:
        s += mult * chi_l(theta, l)
    return s / ORDER_I

def dim_H3_invariant(l):
    """Full H_3 = I x Z_2 (Z_2 = inversion).  Inversion acts on Y_l^m by (-1)^l.
       So H_3-invariant subspace = I-invariant AND l even."""
    if l % 2 == 1:
        return 0.0
    return dim_I_invariant(l)

print("=== H_3 (full icosahedral, |H_3|=120) invariant dimensions per level l ===")
print(f"{'l':>4} {'dim V_l^I':>10} {'dim V_l^{H_3}':>14} {'l(l+1)':>10}")
nontrivial_levels = []
for l in range(0, 31):
    dI  = dim_I_invariant(l)
    dH3 = dim_H3_invariant(l)
    dI_int  = int(round(dI))
    dH3_int = int(round(dH3))
    assert abs(dI - dI_int) < 1e-9, f"non-integer at l={l}: {dI}"
    marker = "  <--" if dH3_int > 0 else ""
    print(f"{l:>4} {dI_int:>10} {dH3_int:>14} {l*(l+1):>10}{marker}")
    if dH3_int > 0:
        nontrivial_levels.append((l, dH3_int))

print("\nFirst 20 nontrivial H_3-invariant levels:")
print([l for (l,d) in nontrivial_levels])
print("with multiplicities:")
print(nontrivial_levels)

print("\nExpected icosahedral degrees of fundamental invariants on R^3: 2, 6, 10, 15")
print("(2 from |x|^2 which is trivial on S^2, so invariant harmonics start at l=6, 10, 12, 15, 16, 18, 20, ...)")
print("Note: l=15 is the pseudoscalar (odd parity), excluded from H_3 (inversion).")
