#!/usr/bin/env python3
"""
Deriving g from the substrate, and testing it against DESI DR2.

r187 proves Lambda_eff' = -g Lambda_eff.  r219 proves w = -1 + g/(3H).
Neither says what g IS.  This script derives it from T_inf and tests the result.

THE DERIVATION.  T_inf = M_{3^inf} has exactly one intrinsic clock: the LEVEL
INDEX k.  Level k is M_{3^k}: complex dimension 9^k, minimal-projection trace
3^-k.  A tower suppression is one factor per level,

    Lambda_eff = Lambda_0 * lam^k    =>    g = ln(1/lam) * dk/dt

so g's FUNCTIONAL FORM is fixed by the embedding k(t), with lam the only free
parameter.  Two canonical embeddings:

  A  HOLOGRAPHIC   algebra dimension = Planck cells in the causal volume,
                   9^k = (ct/l_P)^3  =>  k = (3/2)log_3(ct/l_P)
                   =>  g(t) = A/t,  A = 3 ln(1/lam)/(2 ln 3) = 1.36536 ln(1/lam)
  B  LINEAR        one level per unit substrate depth, k ~ t  =>  g = const

Background: flat LCDM, Om = 0.315.  CPL (w0, wa) obtained by least squares on
0.5 <= a <= 1 (z < 1), the range DESI's SNe actually constrain.

FALSIFIERS, fixed before running:
  * embedding A predicts a SIGN for wa that does not depend on lam.  If that
    sign is wrong, A dies parameter-free.
  * embedding B is a ONE-parameter family in the (w0, wa) plane.  If that curve
    misses the DESI region, B dies too -- and by how much is the result.
  * lam = 1/3 is the canonical substrate value (minimal-projection trace).  It
    has no freedom at all.
"""
import numpy as np, math
from scipy.integrate import quad
from scipy.optimize import minimize_scalar

Om = 0.315
E      = lambda a: math.sqrt(Om * a**-3 + (1 - Om))          # H/H0
t_of_a = lambda a: quad(lambda x: 1.0/(x*E(x)), 1e-8, a)[0]  # H0 * t
t0     = t_of_a(1.0)
COEF   = 3/(2*math.log(3))                                   # A = COEF * ln(1/lam)

def cpl(wf, lo=0.5, hi=1.0, n=80):
    a = np.linspace(lo, hi, n); w = np.array([wf(x) for x in a])
    X = np.vstack([np.ones_like(a), 1-a]).T
    c, *_ = np.linalg.lstsq(X, w, rcond=None)
    return c[0], c[1]

wA = lambda A:  cpl(lambda a: -1 + A /(3*E(a)*t_of_a(a)))    # embedding A
wB = lambda gh: cpl(lambda a: -1 + gh/(3*E(a)))              # embedding B

DESI = [('DESI DR2+CMB',        -0.667, 0.088, -1.09, 0.29),
        ('DESI DR2+CMB+DESY5',  -0.752, 0.057, -0.86, 0.22),
        ('DESI DR2+CMB+Union3', -0.650, 0.100, -1.27, 0.40)]

def main():
    print(f'flat LCDM, Om={Om},  H0*t0 = {t0:.4f}\n')

    print('RESULT 1 - EMBEDDING A IS REFUTED PARAMETER-FREE')
    print('  A = 1.36536 ln(1/lam) > 0 for every lam < 1, and wa scales with A:')
    for A in (0.2, 0.5, 1.0, 2.0, 5.0):
        w0, wa = wA(A); print(f'    A={A:5.2f} -> w0={w0:+.4f}  wa={wa:+.4f}')
    print('  wa > 0 for EVERY lam.  DESI measures wa < 0 at 3.8-3.9 sigma.')
    print('  The holographic embedding fails on the SIGN. No lam rescues it.\n')

    print('RESULT 2 - EMBEDDING B: RIGHT SIGN, ~1/4 THE MAGNITUDE')
    for nm, w0o, s0, wao, sa in DESI:
        f = lambda gh: ((wB(gh)[0]-w0o)/s0)**2 + ((wB(gh)[1]-wao)/sa)**2
        r = minimize_scalar(f, bounds=(0.01, 4.0), method='bounded')
        w0, wa = wB(r.x); lam = math.exp(-r.x*t0/COEF)
        g2 = minimize_scalar(lambda g: (wB(g)[0]-w0o)**2,
                             bounds=(0.01, 4), method='bounded').x
        _, wa2 = wB(g2)
        print(f'  {nm}')
        print(f'    best fit g0/H0={r.x:.4f} (lam={lam:.4f}) -> w0={w0:+.4f}, wa={wa:+.4f}'
              f'   chi2={r.fun:.2f}')
        print(f'    at matched w0: wa={wa2:+.4f} = {100*wa2/wao:.0f}% of observed'
              f'   ({abs(wa2-wao)/sa:.1f} sigma short)')
    print()

    print('RESULT 3 - THE CANONICAL lam = 1/3 IS EXCLUDED')
    A13 = COEF*math.log(3)
    for lab, (w0, wa) in [('A (g~1/t)', wA(A13)), ('B (g=const)', wB(A13/t0))]:
        print(f'  lam=1/3, embedding {lab:<12}: w0={w0:+.4f}, wa={wa:+.4f}')
        for nm, w0o, s0, wao, sa in DESI[:2]:
            print(f'      vs {nm:<20} w0 {abs(w0-w0o)/s0:5.1f} sigma,'
                  f'  wa {abs(wa-wao)/sa:5.1f} sigma')

    print()
    print('CAVEATS, stated rather than buried:')
    print(' * the (w0,wa) errors are treated as independent; DESI reports them')
    print('   strongly anticorrelated, so the true tensions differ from these.')
    print('   The SIGN result (Result 1) is immune to that.')
    print(' * Lambda_eff back-reaction on H(a) is neglected: H is pure LCDM.')
    print(' * "one factor per level" is the simplest tower ansatz, not forced.')

if __name__ == '__main__':
    main()
