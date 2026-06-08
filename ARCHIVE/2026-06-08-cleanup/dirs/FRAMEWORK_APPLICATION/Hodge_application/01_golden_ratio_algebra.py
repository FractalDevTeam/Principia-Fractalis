"""
01_golden_ratio_algebra.py — Principia Fractalis: Hodge application at α = φ.

Goal: explore the algebraic simplifications of the universal coupling
    λ_0(H_φ) = π / (10 φ)
and document why φ is the framework's "rational/irrational bridge" — the
correct α for the Hodge conjecture (rational classes inside continuous geometry).

Framework anchors (NOT tested here, used AS GIVEN):
  - Universal coupling:  λ_0(H_α) = π / (10 α) for every framework α-instance.
  - 4-basis decomposition  {1, π, φ, √2}  is axiom-free in Lean.
  - 9-α architecture forces α = φ to play the Hodge role.
  - ch_2 threshold 0.95 = consciousness crystallization point.
"""

from __future__ import annotations

import mpmath as mp

mp.mp.dps = 50


def phi() -> mp.mpf:
    """Golden ratio φ = (1 + √5) / 2."""
    return (mp.mpf(1) + mp.sqrt(5)) / 2


def lambda_0_hodge() -> mp.mpf:
    """Universal coupling at α = φ.  λ_0(H_φ) = π / (10 φ)."""
    return mp.pi / (10 * phi())


def show_simplifications() -> dict:
    """
    The golden-ratio identities give *exact* equivalent forms of π / (10 φ).
    Key identity:  φ² = φ + 1  ⇒  1/φ = φ − 1.
    Therefore  π / (10 φ) = π (φ − 1) / 10.
    Further:  φ − 1 = 1/φ = 2 / (1 + √5) = (√5 − 1) / 2.
    """
    p = phi()
    f1 = mp.pi / (10 * p)                  # direct form
    f2 = mp.pi * (p - 1) / 10              # via 1/φ = φ − 1
    f3 = mp.pi * (mp.sqrt(5) - 1) / 20     # via (√5 − 1)/2
    f4 = mp.pi / (5 * (1 + mp.sqrt(5)))    # via 2/(1+√5)
    return {
        "λ_0 = π/(10φ)": f1,
        "λ_0 = π(φ-1)/10": f2,
        "λ_0 = π(√5-1)/20": f3,
        "λ_0 = π/(5(1+√5))": f4,
    }


def continued_fraction_phi(n: int = 25) -> list[int]:
    """φ has the continued-fraction expansion [1; 1, 1, 1, ...].

    This makes φ the "most irrational" number — the worst-approximable by rationals.
    Framework interpretation: φ is the *cleanest discrete/continuous bridge*.
    """
    return [1] * n


def irrationality_measure_note() -> str:
    return (
        "φ is the *most irrational* real — every convergent of its CF is a\n"
        "best rational approximation, and the constants in Hurwitz's theorem\n"
        "(|p/q − φ| ≥ 1/(√5 q²)) are saturated only by φ.  Inside the framework,\n"
        "this is precisely why α = φ is assigned to the Hodge conjecture: Hodge\n"
        "asks which RATIONAL classes sit inside an essentially continuous\n"
        "(transcendental) Hodge decomposition.  α = φ is the maximally rigid\n"
        "rational/irrational interface."
    )


def hodge_anchor_table() -> list[tuple[str, mp.mpf]]:
    p = phi()
    lam = lambda_0_hodge()
    return [
        ("φ",                        p),
        ("φ²  (= φ + 1)",            p * p),
        ("1/φ (= φ − 1)",            1 / p),
        ("π / (10 φ)         = λ_0", lam),
        ("π (φ − 1) / 10     = λ_0", mp.pi * (p - 1) / 10),
        ("π (√5 − 1) / 20    = λ_0", mp.pi * (mp.sqrt(5) - 1) / 20),
        ("ch_2 threshold",           mp.mpf("0.95")),
        ("λ_0 − ch_2_thresh",        lam - mp.mpf("0.95")),
    ]


if __name__ == "__main__":
    print("=" * 72)
    print("Principia Fractalis — Hodge at α = φ")
    print("Universal coupling λ_0(H_φ) = π / (10 φ)")
    print("=" * 72)
    print()
    print("Algebraic simplifications (all equal to the same real number):")
    for name, val in show_simplifications().items():
        print(f"  {name:30s} = {mp.nstr(val, 30)}")
    print()
    print("Hodge anchor table:")
    for name, val in hodge_anchor_table():
        print(f"  {name:35s} = {mp.nstr(val, 30)}")
    print()
    print("Continued fraction of φ (first 25 terms):")
    print(" ", continued_fraction_phi())
    print()
    print(irrationality_measure_note())
