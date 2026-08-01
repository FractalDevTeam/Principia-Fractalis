#!/usr/bin/env python3
"""
The two UNIVERSAL Bezout identities for the duplication map, emitted as Lean.

Homogenise x = a/b:
    Phi(a,b) = a^4 - b4 a^2 b^2 - 2 b6 a b^3 - b8 b^4
    Psi(a,b) = 4 a^3 b + b2 a^2 b^2 + 2 b4 a b^3 + b6 b^4

We want explicit degree-3 witnesses

    F1*Phi + G1*Psi = R * a^7
    F2*Phi + G2*Psi = R * b^7

For coprime integers a,b these force gcd(Phi(a,b), Psi(a,b)) | R uniformly in
the curve, replacing the whole per-curve content layer.

Both come from ordinary one-variable Bezout, dehomogenised the two opposite
ways -- NOT from an 8x8 symbolic linear solve, which does not terminate:

  b-side: x = a/b.  u*phi + v*psi = Res(phi,psi),  deg phi 4, deg psi 3.
  a-side: t = b/a.  reversed polys phi~(t) = t^4 phi(1/t), psi~(t) = t^4 psi(1/t).
"""
from sympy import symbols, expand, Poly, solve, total_degree, resultant, simplify

a1,a2,a3,a4,a6,x,t,a,b = symbols('a1 a2 a3 a4 a6 x t a b')
AV = (a1,a2,a3,a4,a6)

b2 = a1**2 + 4*a2
b4 = 2*a4 + a1*a3
b6 = a3**2 + 4*a6
b8 = a1**2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2
disc = expand(-b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6)

Phi = expand(a**4 - b4*a**2*b**2 - 2*b6*a*b**3 - b8*b**4)
Psi = expand(4*a**3*b + b2*a**2*b**2 + 2*b4*a*b**3 + b6*b**4)

def bezout(p, q, var, dp, dq, tag):
    """u*p + v*q = Res(p,q), with deg u < dq, deg v < dp.  Square Sylvester system."""
    R = resultant(Poly(p, var), Poly(q, var))
    us = symbols(f'u{tag}0:{dq}'); vs = symbols(f'v{tag}0:{dp}')
    u = sum(c*var**i for i, c in enumerate(us))
    v = sum(c*var**i for i, c in enumerate(vs))
    eq = Poly(expand(u*p + v*q - R), var)
    sol = solve(eq.all_coeffs(), us+vs, dict=True)
    assert sol, f"bezout failed for {tag}"
    u, v = expand(u.subs(sol[0])), expand(v.subs(sol[0]))
    assert expand(u*p + v*q - R) == 0
    return u, v, expand(R)

# ---- b-side: x = a/b ------------------------------------------------------
phi = x**4 - b4*x**2 - 2*b6*x - b8
psi = 4*x**3 + b2*x**2 + 2*b4*x + b6
u, v, Rb = bezout(phi, psi, x, 4, 3, 'b')
print("Res(phi,psi)  == Delta^2 ?", expand(Rb - disc**2) == 0)
# U = b^2 u(a/b) (deg 2), V = b^3 v(a/b) (deg 3);  (b*U)*Phi + V*Psi = R*b^7
U = expand(b**2 * u.subs(x, a/b)); V = expand(b**3 * v.subs(x, a/b))
F2, G2 = expand(b*U), expand(V)
ok_b = expand(F2*Phi + G2*Psi - Rb*b**7) == 0
print("F2*Phi + G2*Psi == Res * b^7 ?", ok_b)

# ---- a-side: t = b/a, reversed polynomials --------------------------------
phir = expand(t**4 * phi.subs(x, 1/t))     # 1 - b4 t^2 - 2 b6 t^3 - b8 t^4
psir = expand(t**4 * psi.subs(x, 1/t))     # 4t + b2 t^2 + 2 b4 t^3 + b6 t^4
ur, vr, Ra = bezout(phir, psir, t, 4, 4, 'a')
print("Res(phi~,psi~) == Delta^2 ?", expand(Ra - disc**2) == 0,
      "   (== -Delta^2 ?", expand(Ra + disc**2) == 0, ")")
dU = max(Poly(ur, t).degree(), 0); dV = max(Poly(vr, t).degree(), 0)
k = max(dU, dV)
F1 = expand(a**k * ur.subs(t, b/a)); G1 = expand(a**k * vr.subs(t, b/a))
lhs = expand(F1*Phi + G1*Psi)
rhs = expand(Ra * a**(k+4))
print(f"deg u~ {dU}, deg v~ {dV};  F1*Phi + G1*Psi == Res * a^{k+4} ?",
      expand(lhs - rhs) == 0)

print()
for nm, e in [("F1",F1),("G1",G1),("F2",F2),("G2",G2)]:
    p = Poly(e, a, b, *AV)
    print(f"  {nm}: {len(p.terms()):4d} monomials, deg {int(total_degree(e,a,b,*AV)):2d}, "
          f"max|c| {max(abs(int(c)) for c in p.coeffs())}")

with open('codex/duplication_bezout.lean.txt','w') as fh:
    fh.write(f"-- a-side exponent: a^{k+4}   b-side exponent: b^7\n")
    fh.write(f"-- Res(phi,psi) = Delta^2 : {expand(Rb-disc**2)==0}\n")
    fh.write(f"-- Res(phi~,psi~) - Delta^2 = {expand(Ra-disc**2)}\n\n")
    for nm, e in [("Phi",Phi),("Psi",Psi),("Delta",disc),
                  ("F1",F1),("G1",G1),("F2",F2),("G2",G2)]:
        fh.write(f"-- {nm}\n{str(expand(e)).replace('**','^')}\n\n")
print("\nwrote codex/duplication_bezout.lean.txt")
