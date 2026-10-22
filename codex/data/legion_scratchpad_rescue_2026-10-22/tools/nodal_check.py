import sympy as sp

r, x, y, ell, E, m, hbar = sp.symbols('r x y ell E m hbar', positive=True)
f = sp.Function('f')

print("=== 1. Madelung radial equation near a straight nodal line ===")
# stationary, axisymmetric: v_phi = hbar*ell/(m r);  f = sqrt(rho)
# quantum HJ:  hbar^2 ell^2/(2 m r^2) + V - (hbar^2/2m)(f''+f'/r)/f = E
# =>  f'' + f'/r - (ell^2/r^2) f = (2m/hbar^2)(V-E) f
ode = sp.Eq(sp.diff(f(r), r, 2) + sp.diff(f(r), r)/r - (ell**2/r**2)*f(r), 0)
print("  leading-order ODE (V-E regular, so RHS subleading):")
print("   ", ode)
sol = sp.dsolve(ode, f(r))
print("  general solution:", sol)
print("  --> indicial exponents +-ell ; the regular branch is f ~ r^ell,")
print("      hence rho = f^2 ~ r^(2*ell).  ell is a FREE REAL PARAMETER here.")
print()

print("=== 2. is (x^2+y^2)^a smooth at the origin? ===")
for a in [sp.Rational(1,2), sp.Rational(1), sp.Rational(3,2), sp.Rational(2),
          sp.Rational(5,2), sp.Rational(3)]:
    expr = (x**2 + y**2)**a
    # test successive x-derivatives at the origin along y=0
    worst = None
    for k in range(1, 9):
        d = sp.diff(expr, x, k).subs(y, 0)
        lim = sp.limit(d, x, 0, '+')
        if lim in (sp.oo, -sp.oo, sp.zoo) or lim.has(sp.oo, sp.zoo):
            worst = k; break
    tag = "SMOOTH (polynomial)" if worst is None else ("NOT smooth: d^%d/dx^%d blows up" % (worst, worst))
    print("  a = %-6s  (x^2+y^2)^a : %s" % (a, tag))
print()
print("  --> (x^2+y^2)^a is C^inf at 0 iff a is a non-negative INTEGER.")
print("      With rho ~ r^(2 ell) = (x^2+y^2)^ell, smoothness of rho forces ell in Z_{>=0}.")
print()

print("=== 3. does finite energy force it instead? (it does not) ===")
a = sp.symbols('a', positive=True)
# kinetic:  (1/2) rho |v|^2 ~ r^(2a) * (1/r^2), volume elt r dr
kin = sp.integrate(r**(2*a) * r**(-2) * r, (r, 0, 1))
print("  kinetic  int_0^1 r^(2a-2) * r dr =", sp.simplify(kin), " -> finite for a>0")
# quantum potential: Q ~ -(hbar^2/2m) (f''+f'/r)/f with f=r^a  =>  ~ a^2/r^2
Q = sp.simplify((sp.diff(r**a, r, 2) + sp.diff(r**a, r)/r) / r**a)
print("  Q-term   (f''+f'/r)/f with f=r^a :", Q)
qint = sp.integrate(r**(2*a) * r**(-2) * r, (r, 0, 1))
print("  int rho*Q ~ same integral            -> finite for a>0")
print("  --> BOTH energy terms converge for ANY a>0, integer or not.")
print("      Finite energy does NOT force integrality. Smoothness does.")
