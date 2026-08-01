#!/usr/bin/env python3
"""
Feasibility probe for the UNIVERSAL duplication bound.

Goal: |log H(x(2P)) - 4 log H(x(P))| <= log kappa_E for EVERY rational
Weierstrass curve, with kappa_E explicit.  The hard half is the LOWER bound,
which needs the gcd of the two homogeneous quartics to be uniformly bounded.

The keystone (verified here, not recalled):

    Res_x(phi, psi) = Delta^2      in  Z[a1..a6]

    phi = x^4 - b4 x^2 - 2 b6 x - b8       (numerator of x(2P))
    psi = 4x^3 + b2 x^2 + 2 b4 x + b6      (denominator)

From Res = Delta^2 the Sylvester matrix yields cofactors u, v in Z[a1..a6][x]
with u*phi + v*psi = Delta^2.  Homogenising gives the two Bezout identities
that bound gcd(Phi(a,b), Psi(a,b)) for coprime a,b -- uniformly, by Delta^2,
with NO per-curve content analysis.  (For 5077a1 that content step cost two
hand-built stones and a Hermite-normal-form argument.)

This script does not prove anything.  It measures whether the cofactors are
small enough to be `ring`-checkable in Lean before any Lean gets written.
"""
from sympy import symbols, Poly, resultant, expand, ZZ, gcdex, div, QQ, total_degree

a1,a2,a3,a4,a6,x = symbols('a1 a2 a3 a4 a6 x')
AV = (a1,a2,a3,a4,a6)

b2 = a1**2 + 4*a2
b4 = 2*a4 + a1*a3
b6 = a3**2 + 4*a6
b8 = a1**2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2
disc = expand(-b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6)

phi = x**4 - b4*x**2 - 2*b6*x - b8
psi = 4*x**3 + b2*x**2 + 2*b4*x + b6

P, S = Poly(phi, x), Poly(psi, x)
R = resultant(P, S)
print("keystone:  Res(phi,psi) == Delta^2 ?", expand(R - disc**2) == 0)
print()

# --- Sylvester cofactors: solve u*phi + v*psi = Res, deg u < 3, deg v < 4 -----
from sympy import Matrix, symbols as syms
us = syms('u0:3'); vs = syms('v0:4')
u = sum(c*x**i for i,c in enumerate(us))
v = sum(c*x**i for i,c in enumerate(vs))
eq = Poly(expand(u*phi + v*psi) - R, x)
sol = __import__('sympy').solve(eq.all_coeffs(), us+vs, dict=True)
assert sol, "no cofactor solution"
sol = sol[0]
U = expand(u.subs(sol)); V = expand(v.subs(sol))
print("Bezout check:  u*phi + v*psi == Delta^2 ?", expand(U*phi + V*psi - disc**2) == 0)
print()

def stats(name, e):
    p = Poly(expand(e), x, *AV)
    terms = len(p.terms())
    coeffs = [abs(int(c)) for c in p.coeffs()]
    print(f"  {name:>3}: {terms:5d} monomials, "
          f"total degree {int(total_degree(expand(e), x, *AV)):2d}, "
          f"max |coeff| {max(coeffs)}")
    return terms

print("cofactor size (this is the go/no-go):")
tu = stats("u", U); tv = stats("v", V)
print(f"  Delta^2: {len(Poly(expand(disc**2), *AV).terms())} monomials")
print(f"  TOTAL cofactor monomials: {tu+tv}")
print()

# --- The realistic Lean target: minimal models have a1,a3 in {0,1}, a2 in {-1,0,1}
print("restricted to minimal-model shapes (a1,a3 in {0,1}, a2 in {-1,0,1}) --")
print("every elliptic curve over Q has such a model, so this loses nothing:")
worst = 0
for A1 in (0,1):
    for A2 in (-1,0,1):
        for A3 in (0,1):
            sub = {a1:A1, a2:A2, a3:A3}
            uu, vv = expand(U.subs(sub)), expand(V.subs(sub))
            n = len(Poly(uu, x, a4, a6).terms()) + len(Poly(vv, x, a4, a6).terms())
            worst = max(worst, n)
print(f"  worst case over the 12 shapes: {worst} monomials in (x, a4, a6)")
print()
print("sanity -- the two curves already built by hand:")
for nm,(A1,A2,A3,A4,A6),hand in [("389a1",(0,1,1,-2,0),1728),
                                 ("5077a1",(0,0,1,-7,6),105754)]:
    sub = dict(zip(AV,(A1,A2,A3,A4,A6)))
    D = int(disc.subs(sub))
    print(f"  {nm}: Delta = {D}, uniform content bound Delta^2 = {D**2}, "
          f"hand-built kappa = {hand}")
