"""
TEST 3: Symmetric 2-tensors on R^4 (10 independent components)
Hypothesis: Operator on T^2_sym(R^4) might naturally produce pi/10.

The space Sym^2(R^4) has dim = 4*5/2 = 10. Natural operators:
  (a) Casimir of O(4) acting on Sym^2(R^4)
  (b) Casimir of GL(4) acting on Sym^2
  (c) Trace-free decomposition: Sym^2(R^4) = R (trace) (+) Sym^2_0(R^4) (9-dim)

For O(4) acting on traceless symmetric 2-tensors (9-dim, equivalent to harmonic
polynomials of degree 2 on S^3), the Casimir = l(l+n-2) at l=2, n=4: 2*4 = 8.
Including trace part: just 0.

For SO(5) acting on its adjoint rep (also 10-dim), the Casimir of adj = 2*h^v
where h^v = dual Coxeter number = 3. So Casimir(adj SO(5)) = 6 in some normalization.

NONE of these give pi or pi/10 — they're all rational/integer.

The factor pi requires an INTEGRAL or harmonic-analytic origin, not a Lie-algebraic one.
So dim(Sym^2(R^4)) = 10 is a red herring.

We test: spectrum of K(x,y) = exp(-||x-y||^2) on Sym^2(R^4) basis under some natural
quadratic form. Specifically the Gaussian kernel on the 10-dim unit sphere S^9
(unit ball of Sym^2(R^4) with Frobenius norm) - look for pi/10 in eigenvalues.

On S^9 (dim 9), Laplacian eigenvalues: l(l+8) for l=0,1,2,...
First nonzero = 9. No pi/10 here either.
"""

from mpmath import mp, mpf, pi, exp, sqrt, gamma

mp.dps = 50

def laplacian_eigenvalues_sphere(n, max_l=6):
    """Laplace-Beltrami on S^n: eigenvalues l(l+n-1)."""
    return [(l, l*(l+n-1)) for l in range(max_l+1)]

def Sn_volume(n):
    """Volume of unit n-sphere."""
    return 2 * pi**((n+1)/2) / gamma((n+1)/2)

def main():
    print("=" * 70)
    print("TEST 3: Symmetric 2-tensors on R^4, dim = 10")
    print("=" * 70)

    print("\nLaplacian spectra on candidate 10-dim or related spheres:")
    print()
    for n in [3, 4, 9]:
        print(f"S^{n}: eigenvalues l(l+{n-1}) =",
              [v for (l, v) in laplacian_eigenvalues_sphere(n, 5)])
        print(f"  Vol(S^{n}) = {float(Sn_volume(n)):.10f}")
        # Check if pi/10 appears in vol or its rationals

    print()
    print("Volume ratios checked for pi/10 = ", float(pi/10))
    for n in [3, 4, 9, 10]:
        v = Sn_volume(n)
        print(f"  Vol(S^{n})/Vol(S^{n-1}) = {float(v/Sn_volume(n-1)):.10f}")

    print()
    print("SO(5) Casimir on adjoint (10-dim): 2*h^v(B_2) = 6 (integer, no pi)")
    print("O(4) on Sym^2_0(R^4) (9-dim): l(l+n-2)|_{l=2,n=4} = 8 (integer)")
    print()
    print("Verdict: dim = 10 from symmetric tensors gives Lie-algebraic integers,")
    print("NOT pi/10. No harmonic source for the pi in pi/10 from this structure.")

if __name__ == "__main__":
    main()
