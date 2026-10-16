#!/usr/bin/env python3
"""Verification for WALL1_MINMAX_PARKED_2026-10-16.md

Every number and identity quoted in that note is produced here.
Run:  python3 wall1_minmax_verify.py

A. The quantum potential IS the osmotic kinetic energy.
     int rho (m/2)|u|^2  =  int rho Q  =  (hbar^2/8m) I(rho)
   with u = D grad log rho, D = hbar/2m, I = Fisher information.
   Consequence: the sign of Q in the dynamics equals the sign of the osmotic
   term in the action. The quantum action needs |v|^2 - |u|^2, a difference of
   squares -- so NON-CONVEXITY IS EQUIVALENT TO THE QUANTUM SIGN, not
   incidental to it.

B. The Yasue/Pavon action is unbounded ABOVE and BELOW, with no coercivity in
   either direction. Kills Sion-type minimax (needs compactness on one side)
   and mountain-pass (needs Palais-Smale + bounded-below structure).

C. The mean-field-game forward-backward system carries the EUCLIDEAN sign.
   Checked because MFG existence theory DOES allow law-dependent couplings and
   the MFG literature advertises a correspondence with NLS under mu*sigma^2 ->
   hbar. If that correspondence were a real-time identification, MFG existence
   theory would host the quantum sign. It is not: the sign comes out Euclidean,
   so the correspondence must route through an analytic continuation.
"""
import sympy as sp
import numpy as np

PASS = lambda ok: "PASS" if ok else "FAIL"

# ----------------------------------------------------------------------------
print("=" * 74)
print("A. the quantum potential IS the osmotic kinetic energy")
x = sp.Symbol("x", real=True)
m, hbar = sp.symbols("m hbar", positive=True)
D = hbar / (2 * m)
rho = sp.Function("rho", positive=True)(x)

osm = sp.simplify(rho * (m / 2) * (D * sp.diff(sp.log(rho), x)) ** 2)
qby = sp.simplify((hbar ** 2 / (2 * m)) * sp.diff(sp.sqrt(rho), x) ** 2)
diff = sp.simplify(sp.expand(osm - qby))
print("   rho*(m/2)|u|^2                 =", osm)
print("   (hbar^2/2m)|grad sqrt(rho)|^2  =", qby)
print("   difference                     = %s   [%s, expect 0]" % (diff, PASS(diff == 0)))
print("   both equal (hbar^2/8m)|grad rho|^2/rho = (hbar^2/8m) * Fisher information")

print()
print("   numeric, including the integration by parts (m = hbar = 1, D = 1/2):")
N, L = 200001, 14.0
xs = np.linspace(-L, L, N)
dx = xs[1] - xs[0]
ok = True
for name, r0 in [("gaussian", np.exp(-xs ** 2)),
                 ("bimodal ", np.exp(-(xs - 2) ** 2) + 0.4 * np.exp(-(xs + 3) ** 2)),
                 ("skewed  ", np.exp(-xs ** 2) * (1 + 0.5 * np.tanh(xs)) ** 2)]:
    r = r0 / (r0.sum() * dx)
    sq = np.sqrt(r)
    g = np.gradient(sq, dx)
    lap = np.gradient(g, dx)
    I_osm = np.trapz(r * 0.5 * (0.5 * np.gradient(np.log(r), dx)) ** 2, xs)
    I_Q = np.trapz(r * (-(0.5) * lap / sq), xs)
    ok &= abs(I_osm - I_Q) < 1e-6
    print("     %s  int rho(m/2)|u|^2 = %.10f   int rho*Q = %.10f" % (name, I_osm, I_Q))
print("   [%s] equal for every shape tested" % PASS(ok))

# ----------------------------------------------------------------------------
print()
print("=" * 74)
print("B. the Yasue/Pavon action is unbounded in BOTH directions")
print("   J[rho,v] = int rho[(m/2)|v|^2 - (m/2)|u|^2] = int rho(m/2)|v|^2 - I(rho)/8")
N, L = 400001, 10.0
xs = np.linspace(-L, L, N)
dx = xs[1] - xs[0]
base = np.exp(-xs ** 2)


def fisher(r):
    r = r / (r.sum() * dx)
    return np.trapz(np.gradient(r, dx) ** 2 / np.maximum(r, 1e-300), xs)


print()
print("   (A) UNBOUNDED BELOW: hold v = 0, oscillate rho. Then J = -I(rho)/8.")
print("       rho_k = exp(-x^2)(1 + 0.9 sin(k x))^2 -- smooth, positive, normalised")
prev = None
for k in [1, 2, 4, 8, 16, 32, 64]:
    I = fisher(base * (1 + 0.9 * np.sin(k * xs)) ** 2)
    ratio = "" if prev is None else "   (x%.2f)" % (I / prev)
    print("         k = %-3d  I(rho) = %11.2f   J = %12.2f%s" % (k, I, -I / 8, ratio))
    prev = I
print("       -> I(rho) ~ k^2, so J -> -infinity. No lower bound, no coercivity.")

print()
print("   (B) UNBOUNDED ABOVE: hold rho = gaussian, scale v.")
r = base / (base.sum() * dx)
for c in [1, 2, 4, 8, 16]:
    kin = np.trapz(r * (c * xs) ** 2 / 2, xs)
    print("         v = %2d*x   kinetic = %10.2f   J = %10.2f" % (c, kin, kin - fisher(r) / 8))
print("       -> J -> +infinity. No upper bound.")
print()
print("   (C) the min and max variables are NOT independent: u = D grad log rho,")
print("       and rho is the law of the very process whose drift is b = v + u.")
print("       The maximiser's admissible set is a function of the minimiser's")
print("       choice, so the domain is not a product set and this is not a game.")

# ----------------------------------------------------------------------------
print()
print("=" * 74)
print("C. the MFG forward-backward system carries the EUCLIDEAN sign")
t = sp.Symbol("t", real=True)
eps = sp.Symbol("epsilon", positive=True)
phi = sp.Function("phi")(x, t)
rh = sp.Function("rho", positive=True)(x, t)
V = sp.Function("V")(x)

# HJB (backward):  -phi_t - (eps/2) phi_xx + phi_x^2/2 = V
# FP  (forward):   rho_t + (rho * v_mfg)_x = (eps/2) rho_xx ,  v_mfg = -phi_x
phi_t = -(eps / 2) * sp.diff(phi, x, 2) + sp.diff(phi, x) ** 2 / 2 - V
rho_t = (eps / 2) * sp.diff(rh, x, 2) - sp.diff(rh * (-sp.diff(phi, x)), x)

# current velocity: absorb the FP diffusion, so continuity becomes exact
S = -(phi + (eps / 2) * sp.log(rh))
v_c = sp.diff(S, x)
cont = sp.diff(rh, t) + sp.diff(rh * v_c, x)
cont = sp.simplify(sp.expand(cont.subs(sp.Derivative(rh, t), rho_t)))
print("   continuity residual for the current velocity = %s   [%s]"
      % (cont, PASS(cont == 0)))

# HJ0 carries NO extra V: S_t already contains +V via the HJB substitution
HJ0 = sp.diff(S, t) + sp.diff(S, x) ** 2 / 2
HJ0 = HJ0.subs(sp.Derivative(phi, t), phi_t).subs(sp.Derivative(rh, t), rho_t)
HJ0 = sp.simplify(sp.expand(HJ0))
hb = eps  # mu*sigma^2 -> hbar with mu = m = 1
Q = -(hb ** 2 / 2) * sp.diff(sp.sqrt(rh), x, 2) / sp.sqrt(rh)
quant = sp.simplify(sp.expand(HJ0 + Q + V))
eucl = sp.simplify(sp.expand(HJ0 - Q - V))
print("   S_t + |grad S|^2/2 + Q + V = %s   [quantum: %s]" % (quant, PASS(quant != 0)))
print("   S_t + |grad S|^2/2 - Q - V = %s   [Euclidean: %s]" % (eucl, PASS(eucl == 0)))
print("   -> S_t + |grad S|^2/2 = Q + V_cost : the EUCLIDEAN sign.")
print("      (V_cost vs V_mech is a genuine convention -- a cost is minimised,")
print("       a mechanical potential is not. The sign of Q is NOT a convention:")
print("       it is fixed by the diffusion term, and it comes out Euclidean.)")
print("      So the MFG <-> NLS correspondence in that literature cannot be a")
print("      real-time identification; it routes through analytic continuation.")

print()
print("=" * 74)
print("CONCLUSION: the quantum sign requires an indefinite action (A); the")
print("indefinite action has no coercivity in either direction and its min/max")
print("variables are not independent (B); and the one existence framework that")
print("does allow law-dependent coupling carries the Euclidean sign anyway (C).")
print("No live min-max existence theory hosts Pavon's functional. Gap 2 parks.")
