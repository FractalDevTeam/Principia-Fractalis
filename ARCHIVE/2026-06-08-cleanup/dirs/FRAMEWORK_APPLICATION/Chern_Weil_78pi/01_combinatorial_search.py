"""
Search for integer 78 as a structural invariant inside T_infty machinery.

T_infty = lim_k (N(H_k) ⊗_min F_α), H_k = ℂ^{3^k}.
K_0(T_∞) = Z[1/3], K_1(T_∞) = 0.

Targets:
  - Does 78 appear as dim of some natural subspace at level k?
  - Does 78 appear as #(orbits) of some natural group action at level k?
  - Connection to E_6 (dim = 78)?
  - 78 = 2·3·13 — what is 13 in T_∞?
"""

import math
from fractions import Fraction


def dim_Hk(k):
    """Dimension of H_k = ℂ^{3^k}."""
    return 3 ** k


def dim_endomorphisms_Hk(k):
    """dim End(H_k) = 9^k (over ℂ)."""
    return 9 ** k


def dim_traceless_endos(k):
    """dim {a in End(H_k) : Tr a = 0} = 9^k - 1."""
    return 9 ** k - 1


def dim_self_adjoint_endos(k):
    """Real dim of self-adjoint matrices in End(H_k) = (3^k)^2 = 9^k."""
    return 9 ** k


def dim_antiself_adjoint_traceless(k):
    """dim su(3^k) = (3^k)^2 - 1 = 9^k - 1 (real Lie algebra)."""
    return 9 ** k - 1


def report():
    print("=" * 60)
    print("T_infty STRUCTURAL DIMENSIONS — searching for 78 / 13")
    print("=" * 60)
    print()
    print(f"{'k':>3} {'3^k':>8} {'9^k':>10} {'9^k - 1':>10} {'9^k - 3^k':>10}  {'(9^k-1)/8':>10}")
    for k in range(0, 7):
        d = dim_Hk(k)
        e = dim_endomorphisms_Hk(k)
        t = dim_traceless_endos(k)
        diff = e - d
        # 9^k - 1 is always divisible by 8
        d8 = (e - 1) // 8
        print(f"{k:>3} {d:>8} {e:>10} {t:>10} {diff:>10}  {d8:>10}")
    print()
    print("Looking for 78 …")
    candidates = []
    for k in range(0, 7):
        d = dim_Hk(k)
        e = dim_endomorphisms_Hk(k)
        for label, val in [
            ("3^k", d),
            ("9^k", e),
            ("9^k - 1", e - 1),
            ("9^k - 3^k", e - d),
            ("(9^k - 1)/8", (e - 1) // 8),
            ("(3^(k+1) - 3)/1", 3 ** (k + 1) - 3),
            ("(3^k - 1)·3", (d - 1) * 3),
            ("(3^k - 1)·(3^k + 1)", (d - 1) * (d + 1)),
            ("3^k·(3^k - 1)/2", d * (d - 1) // 2),
            ("3^k·(3^k + 1)/2", d * (d + 1) // 2),
        ]:
            if val == 78:
                candidates.append((k, label))
            if val == 13:
                candidates.append((k, label + "  [=13]"))
    if candidates:
        for c in candidates:
            print(" HIT:", c)
    else:
        print(" No direct hit at any k <= 6.")

    print()
    print("78 factorizations:")
    print(f"   78 = 2·3·13")
    print(f"   78 = 6·13")
    print(f"   78 = sum(1..12) = 12·13/2")
    print(f"   78 = dim(E_6 Lie algebra) = 72 roots + 6 Cartan")
    print()
    print("13 factorizations / interpretations:")
    print(f"   13 = 9 + 3 + 1 = 3^2 + 3 + 1  (sum of base-3 places <= 3^2)")
    print(f"   13 = (3^3 - 1)/2 = 26/2")
    print(f"   13 = first prime > 3^2")
    print(f"   13 = dim(G_2) - 1 = 14 - 1  (G_2 has dim 14)")
    print()
    # 12·13/2: triangular T_12. Note dim(Cartan)=6, # roots = 72. 78 = T_12.
    print("Triangular interpretation:")
    print(f"   T_n = n(n+1)/2;  T_12 = {12*13//2}")
    print(f"   3^k + 3^(k-1) at k=2 = 12;  level-2 dim sum 9+3 = 12")
    print(f"   So 78 = T(dim H_1 + dim H_2) = T(3 + 9) = T(12)")
    print(f"           = T(sum of dim H_k for k=1,2) ✓")


if __name__ == "__main__":
    report()
