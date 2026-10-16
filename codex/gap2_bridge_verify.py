#!/usr/bin/env python3
"""Verification for GAP2_BRIDGE_CONSTRUCTED_2026-10-16.md

Every number quoted in that note is produced here. Run:  python3 gap2_bridge_verify.py

Checks, in order:
  A. osmotic relation and continuity equation for the Schroedinger bridge, 1-D
  B. the SAME two checks with the drift assignment swapped -- reproduces the
     error described in the note's method section (osmotic passes, continuity
     fails). A symmetric check cannot detect an antisymmetric error.
  C. the quantum-potential sign: HJ + Q (quantum) vs HJ - Q (Euclidean), 1-D
  D. A and C again in 3-D, to rule out a 1-D artifact
  E. strict interior positivity from genuinely NODAL endpoint data

Convention (this is the part that is easy to get backwards -- see note sec. 6):
  g solves the FORWARD  heat equation   d_t g = +(eps/2) Lap g
  f solves the BACKWARD heat equation   d_t f = -(eps/2) Lap f
  f is the space-time harmonic factor, (d_t + (eps/2)Lap) f = 0, so by Doob's
  h-transform the FORWARD drift is built from f:
      b = eps grad log f ,  b* = -eps grad log g
      u = (b - b*)/2  (osmotic) ,  v = (b + b*)/2  (current)
  rho = f*g ,  S = (m eps/2) log(f/g) ,  v = grad S / m ,  hbar := m eps
"""
import sympy as sp
import numpy as np

eps, m = sp.symbols("epsilon m", positive=True)
PASS = lambda ok: "PASS" if ok else "FAIL"


def bridge_checks(coords, t, swap=False):
    """Return (osmotic_residual, continuity_residual, HJ+Q, HJ-Q)."""
    f = sp.Function("f")(*coords, t)
    g = sp.Function("g")(*coords, t)
    lap = lambda E: sum(sp.diff(E, xi, 2) for xi in coords)
    grad = lambda E: [sp.diff(E, xi) for xi in coords]

    def use_heat(E):
        E = E.subs(sp.Derivative(f, t), -(eps / 2) * lap(f))
        E = E.subs(sp.Derivative(g, t), (eps / 2) * lap(g))
        return sp.expand(E)

    rho = f * g
    # the swapped (WRONG) assignment is the one the note's sec. 6 describes
    hb, hbs = (g, f) if swap else (f, g)
    b = [eps * d for d in grad(sp.log(hb))]
    bstar = [-eps * d for d in grad(sp.log(hbs))]
    u = [(b[i] - bstar[i]) / 2 for i in range(len(coords))]
    v = [(b[i] + bstar[i]) / 2 for i in range(len(coords))]

    tgt = [(eps / 2) * d for d in grad(sp.log(rho))]
    osm = sp.simplify(sp.expand(sum(u[i] - tgt[i] for i in range(len(coords)))))

    cont = sp.diff(rho, t) + sum(sp.diff(rho * v[i], coords[i]) for i in range(len(coords)))
    cont = sp.simplify(use_heat(cont))

    S = (m * eps / 2) * sp.log(f / g)
    HJ = sp.diff(S, t) + sum(d ** 2 for d in grad(S)) / (2 * m)
    HJ = use_heat(HJ)
    hbar = m * eps
    Q = -(hbar ** 2 / (2 * m)) * lap(sp.sqrt(rho)) / sp.sqrt(rho)
    return osm, cont, sp.simplify(sp.expand(HJ + Q)), sp.simplify(sp.expand(HJ - Q))


print("=" * 72)
print("A. 1-D, correct drift assignment (forward drift from the harmonic factor f)")
x = sp.Symbol("x", real=True)
t = sp.Symbol("t", real=True)
osm, cont, quant, eucl = bridge_checks([x], t)
print("   osmotic   u - (eps/2) grad log rho = %s      [%s, expect 0]" % (osm, PASS(osm == 0)))
print("   continuity d_t rho + div(rho v)    = %s      [%s, expect 0]" % (cont, PASS(cont == 0)))

print()
print("=" * 72)
print("B. 1-D, SWAPPED drift assignment -- the error from the note's sec. 6")
osmS, contS, _, _ = bridge_checks([x], t, swap=True)
print("   osmotic   = %s   <-- STILL ZERO: u is symmetric in f<->g," % osmS)
print("                      so this check cannot see the error at all.")
print("   continuity= %s" % contS)
print("   [%s: continuity must be NONZERO here, and it is what caught the bug]"
      % PASS(contS != 0))

print()
print("=" * 72)
print("C. 1-D quantum-potential sign   (hbar = m*eps, V = 0)")
print("   HJ + Q  (true Madelung / quantum)   = %s" % quant)
print("   HJ - Q  (sign-reversed / Euclidean) = %s" % eucl)
print("   [%s] quantum FAILS, Euclidean HOLDS -> the bridge solves Madelung"
      % PASS(quant != 0 and eucl == 0))
print("        with Q -> -Q. This is Zambrini's Euclidean quantum mechanics,")
print("        NOT quantum mechanics.")

print()
print("=" * 72)
print("D. 3-D: same four checks, to rule out a 1-D artifact")
X3 = sp.symbols("x1 x2 x3", real=True)
osm3, cont3, quant3, eucl3 = bridge_checks(list(X3), t)
print("   osmotic residual    = %s   [%s]" % (osm3, PASS(osm3 == 0)))
print("   continuity residual = %s   [%s]" % (cont3, PASS(cont3 == 0)))
print("   HJ + Q == 0 (quantum)   ? %s   [%s]" % (quant3 == 0, PASS(quant3 != 0)))
print("   HJ - Q == 0 (Euclidean) ? %s   [%s]" % (eucl3 == 0, PASS(eucl3 == 0)))

print()
print("=" * 72)
print("E. strict interior positivity from NODAL endpoint data")
print("   endpoint rho_0(x) = x^2 exp(-x^2) has an exact node at x = 0.")
print("   The h-transform factor g evolves it by the heat semigroup.")
N, L = 4001, 12.0
xs = np.linspace(-L, L, N)
dx = xs[1] - xs[0]
rho0 = xs ** 2 * np.exp(-xs ** 2)
print("   rho_0(0) = %.3e  (exact node)" % rho0[N // 2])
allpos = True
for tau in (1e-6, 1e-4, 1e-2):
    ker = np.exp(-(xs - xs[:, None]) ** 2 / (2 * tau)) / np.sqrt(2 * np.pi * tau)
    gt = ker.dot(rho0) * dx
    allpos &= gt.min() > 0
    print("   tau = %-8g :  g(0,tau) = %.6e    min_x g = %.6e" % (tau, gt[N // 2], gt.min()))
print("   [%s] g > 0 everywhere for every tau > 0: the node is filled" % PASS(allpos))
print("        immediately (parabolic strong maximum principle). Hence")
print("        rho_t = f_t g_t > 0 strictly on 0 < t < T, the node set is EMPTY,")
print("        and the construction produces only the zero-circulation sector.")
print()
print("=" * 72)
print("CONCLUSION: the bridge derives the kinematics (osmotic relation,")
print("continuity, and -- via Girsanov -- the fluctuation law 2D g^{mu nu}|dt|),")
print("but its dynamics is Euclidean and its densities are nodeless.")
