#!/usr/bin/env python3
"""
alpha_web_system.py -- exact symbolic analysis of the Principia Fractalis
alpha-web, treated as a system of simultaneous polynomial equations.

Run with:  /home/xluxx/lab/bin/python3 alpha_web_system.py

Source of the eleven invariants:
  PF_Lean4_Code/PF/Referee/PrincipiaFractalisSubstrateTheorem.lean, conjunct C8
  PF_Lean4_Code/PF/CrossMillenniumSharedInvariants.lean, capstone

Nothing here is numerics-dependent for a structural claim. Numerical checks
are done at 60 decimal digits with mpmath and are labelled as checks only.
"""

import sympy as sp
from sympy import Rational as Q
import mpmath as mp

mp.mp.dps = 60

# ----------------------------------------------------------------------
# 0. Unknowns.  pi is carried as a *symbol* p, and we work over the
#    rational function field QQ(p).  This is the correct model of
#    "pi is a transcendental constant": no polynomial over QQ vanishes
#    on it, so QQ[pi] ~ QQ[p] and QQ(pi) ~ QQ(p).
# ----------------------------------------------------------------------
p = sp.Symbol('p')                      # stands for pi
POI, P, RH, YM, HO, NP, NS, BSD, QG = sp.symbols(
    'a_Poi a_P a_RH a_YM a_Ho a_NP a_NS a_BSD a_QG')
V = [POI, P, RH, YM, HO, NP, NS, BSD, QG]
NAMES = ['a_Poincare', 'a_P', 'a_RH', 'a_YM', 'a_Hodge',
         'a_NP', 'a_NS', 'a_BSD', 'a_QG']

# ----------------------------------------------------------------------
# 1. The eleven invariants, written as polynomials f_i with f_i = 0.
# ----------------------------------------------------------------------
E = {
    1:  P**2 - YM,                     # a_P^2 = a_YM
    2:  RH**2 - Q(9, 4),               # a_RH^2 = 9/4
    3:  QG**2 - 2*p,                   # a_QG^2 = 2 pi
    4:  HO**2 - HO - 1,                # a_Hodge^2 = a_Hodge + 1
    5:  NS - 2*BSD,                    # a_NS = 2 a_BSD
    6:  NS - YM*BSD,                   # a_NS = a_YM a_BSD
    7:  YM - POI - 1,                  # a_YM = a_Poincare + 1
    8:  RH*NS - NS - BSD,              # a_RH a_NS = a_NS + a_BSD
    9:  RH*YM - 3,                     # a_RH a_YM = 3
    10: NP - HO - Q(1, 4),             # a_NP - a_Hodge = 1/4
    11: QG**2 - YM*p,                  # a_QG^2 = a_YM pi
}
GENS = [E[i] for i in sorted(E)]

# The framework's own point.
phi = (1 + sp.sqrt(5)) / 2
PT = {POI: 1, P: sp.sqrt(2), RH: Q(3, 2), YM: 2, HO: phi,
      NP: phi + Q(1, 4), NS: 3*p/2, BSD: 3*p/4, QG: sp.sqrt(2*p)}

DOM = sp.QQ.frac_field(p)   # QQ(pi)


def banner(t):
    print('\n' + '=' * 72)
    print(t)
    print('=' * 72)


# ----------------------------------------------------------------------
# 2. Sanity: the framework point satisfies all eleven.
# ----------------------------------------------------------------------
banner('2. CONSISTENCY: does the framework 9-tuple satisfy all eleven?')
for i in sorted(E):
    r = sp.simplify(sp.expand(E[i].subs(PT)))
    print(f'  I{i:<3} residual = {r}')
assert all(sp.simplify(E[i].subs(PT)) == 0 for i in E)
print('  -> all eleven hold exactly. The system is CONSISTENT.')


# ----------------------------------------------------------------------
# 3. Krull dimension of V(I) over QQ(pi).
#
#    Standard combinatorial criterion (Cox-Little-O'Shea, Ch.9 Thm 8):
#    for a Groebner basis G of I w.r.t. any graded order, dim V(I) is the
#    largest cardinality of a subset U of the variables such that no
#    leading monomial of G lies in k[U].
# ----------------------------------------------------------------------
banner('3. DIMENSION OF THE SOLUTION VARIETY over QQ(pi)')

from itertools import combinations

G = sp.groebner(GENS, *V, order='grevlex', domain=DOM)
print('  Groebner basis (grevlex), %d elements:' % len(G.exprs))
for g in G.exprs:
    print('    ', sp.expand(g))

LT = [sp.LT(g, V, order='grevlex') for g in G.polys]
lt_vars = [set(sp.Poly(t, *V).free_symbols) & set(V) for t in
           [sp.Poly(g, *V, domain=DOM).LM(order='grevlex').as_expr()
            for g in G.exprs]]
print('\n  leading-monomial supports:', [sorted(map(str, s)) for s in lt_vars])


def is_independent(U):
    """U subset of V is independent mod I iff no leading monomial of G
    is supported entirely inside U."""
    Us = set(U)
    return all(not s.issubset(Us) for s in lt_vars)


dim = 0
witness = None
for k in range(len(V), -1, -1):
    found = [U for U in combinations(V, k) if is_independent(U)]
    if found:
        dim, witness = k, found
        break
print(f'\n  dim V(I) = {dim}')
print('  maximal independent variable sets:',
      [sorted(map(str, U)) for U in witness])
print(f'  codim = {len(V) - dim}  -> at most {len(V)-dim} of the 11 '
      'invariants can be independent.')


# ----------------------------------------------------------------------
# 4. Which invariants are redundant?  Two notions:
#    (a) ideal membership: f_i in <f_j : j != i>  (reduce to 0 mod GB)
#    (b) variety redundancy: V(<f_j : j != i>) == V(I)  (compare radicals
#        via dimension + explicit solve).  We report (a), which is the
#        strict test, and additionally test (a) after saturating by pi
#        and by a_BSD where relevant.
# ----------------------------------------------------------------------
banner('4. REDUNDANCY: is each invariant implied by the other ten?')
redundant, independent_gens = [], []
for i in sorted(E):
    others = [E[j] for j in sorted(E) if j != i]
    Gi = sp.groebner(others, *V, order='grevlex', domain=DOM)
    rem = Gi.reduce(E[i])[1]
    ok = sp.simplify(rem) == 0
    print(f'  I{i:<3} in ideal generated by the other ten? {ok}')
    (redundant if ok else independent_gens).append(i)
print(f'\n  ideal-redundant: {redundant}')
print(f'  ideal-independent: {independent_gens}')
print('  (ideal-independence is strictly stronger than variety-independence;'
      '\n   see step 5 for the real-positive picture.)')


# ----------------------------------------------------------------------
# 5. A minimal generating subset: greedily drop invariants while the
#    ideal is unchanged.
# ----------------------------------------------------------------------
banner('5. MINIMAL SUBSET OF THE ELEVEN GENERATING THE SAME IDEAL')
keep = list(sorted(E))
for i in sorted(E):
    trial = [j for j in keep if j != i]
    Gt = sp.groebner([E[j] for j in trial], *V, order='grevlex', domain=DOM)
    if all(sp.simplify(Gt.reduce(E[j])[1]) == 0 for j in sorted(E)):
        keep = trial
print('  a minimal generating subset:', keep)
print('  dropped as ideal-redundant  :', [i for i in sorted(E) if i not in keep])

print('\n  ALL 8-element subsets of the eleven that generate the SAME ideal:')
full = set(sorted(E))
good8 = []
for S in combinations(sorted(E), 8):
    Gs = sp.groebner([E[j] for j in S], *V, order='grevlex', domain=DOM)
    if all(sp.simplify(Gs.reduce(E[j])[1]) == 0 for j in sorted(E)):
        good8.append(S)
for S in good8:
    print('    ', list(S), '  (drops', [i for i in sorted(E) if i not in S], ')')
print(f'  count = {len(good8)}')
print('  No 7-element subset can suffice: codim V(I) = 8, so by Krull height')
print('  the ideal needs at least 8 generators.  Hence the eleven invariants')
print('  contain exactly 8 independent constraints and 3 redundancies.')

print('\n  ELIMINATION: does the system constrain a_BSD at all?')
Gl = sp.groebner(GENS, *(  [v for v in V if v is not BSD] + [BSD] ),
                 order='lex', domain=DOM)
onlyBSD = [g for g in Gl.exprs
           if (set(sp.Poly(g, *V).free_symbols) & set(V)) <= {BSD}]
print('    I intersect QQ(pi)[a_BSD] =', onlyBSD if onlyBSD else '{0}')
print('    -> a_BSD is completely unconstrained by the eleven invariants.')
print('    NOTE: the corpus\'s own 9-of-9 rigidity theorem')
print('    (CrossMillenniumDerivedConsequences.alpha_system_rigidity_extended)')
print('    pins a_BSD only by adding a TWELFTH hypothesis, a_QG^2 = (8/3) a_BSD,')
print('    which is NOT one of the eleven invariants of conjunct C8.')


# ----------------------------------------------------------------------
# 6. Explicit real solution set with the framework's positivity.
# ----------------------------------------------------------------------
banner('6. REAL SOLUTIONS WITH ALL NINE ALPHAS POSITIVE')
t = sp.Symbol('t', positive=True)   # the free BSD scale
sol = {POI: 1, P: sp.sqrt(2), RH: Q(3, 2), YM: 2, HO: phi,
       NP: phi + Q(1, 4), NS: 2*t, BSD: t, QG: sp.sqrt(2*p)}
print('  claimed general positive solution, parameterised by t = a_BSD > 0:')
for k in V:
    print(f'    {str(k):<10} = {sol[k]}')
print('  residuals:')
for i in sorted(E):
    r = sp.simplify(sp.expand(E[i].subs(sol)))
    print(f'    I{i:<3} = {r}')
assert all(sp.simplify(E[i].subs(sol)) == 0 for i in E)
print('  -> ONE-PARAMETER FAMILY of positive solutions. t is unconstrained.')
print('     t = 3*pi/4 recovers the framework; t = 1 (or any t>0) is equally'
      ' admissible.')


# ----------------------------------------------------------------------
# 7. Jacobian rank at the framework point -> local rigidity.
# ----------------------------------------------------------------------
banner('7. JACOBIAN / PERTURBATION ANALYSIS AT THE FRAMEWORK POINT')
J = sp.Matrix([[sp.diff(E[i], v) for v in V] for i in sorted(E)])
Jp = sp.simplify(J.subs(PT))
print('  Jacobian (11 x 9) at the framework point:')
sp.pprint(Jp)
r = Jp.rank()
print(f'\n  rank J = {r}   -> local solution manifold has dimension '
      f'{len(V) - r}')
ns = Jp.nullspace()
print(f'  nullspace dimension = {len(ns)}')
for v in ns:
    print('  tangent direction (order: %s):' % ', '.join(NAMES))
    print('   ', sp.simplify(v.T))
print('  Interpretation: a nonzero tangent direction means the point is NOT'
      ' isolated.')
print('  The framework point can be moved along it and every invariant still'
      ' holds to first order -- and, by step 6, exactly.')


# ----------------------------------------------------------------------
# 8. Is the 1/4 forced?  Replace it by an unknown c.
# ----------------------------------------------------------------------
banner('8. IS THE 1/4 A FREE PARAMETER?')
c = sp.Symbol('c')
Ec = dict(E)
Ec[10] = NP - HO - c
Wc = V + [c]
Gc = sp.groebner([Ec[i] for i in sorted(Ec)], *Wc, order='lex',
                 domain=sp.QQ.frac_field(p))
elim = [g for g in Gc.exprs
        if not (set(sp.Poly(g, *Wc).free_symbols) & set(V))]
print('  Groebner basis elements involving c but no alpha (i.e. constraints'
      ' on c alone):')
print('   ', elim if elim else 'NONE')

# direct constructive proof: exhibit a solution for arbitrary c
cc = sp.Symbol('c')
solc = dict(PT); solc[NP] = phi + cc
Ec2 = dict(E); Ec2[10] = NP - HO - cc
print('\n  constructive check -- for a SYMBOLIC c, set a_NP := phi + c and'
      ' leave everything else at the framework values:')
for i in sorted(Ec2):
    print(f'    I{i:<3} = {sp.simplify(sp.expand(Ec2[i].subs(solc)))}')
assert all(sp.simplify(Ec2[i].subs(solc)) == 0 for i in Ec2)
print('  -> holds identically in c. The constant 1/4 is a FREE PARAMETER.')

# a_NP occurs in exactly one invariant -- confirm by inspection
occ = [i for i in sorted(E) if NP in E[i].free_symbols]
print(f'\n  invariants mentioning a_NP: {occ}  (count = {len(occ)})')
print('  A variable appearing in exactly one equation of a square-free'
      ' system\n  can never be over-determined: that equation *defines* it.')


# ----------------------------------------------------------------------
# 9. Genericise EVERY bare constant.  Which of them are forced by the
#    others, and how many are truly independent inputs?
# ----------------------------------------------------------------------
banner('9. GENERICISED CONSTANTS: how many independent numeric inputs?')
a, b, d, e, f, cg = sp.symbols('a b d e f c')
Gsys = [
    P**2 - YM,            # I1  (constant-free)
    RH**2 - a,            # I2  a = 9/4
    QG**2 - b,            # I3  b = 2 pi
    HO**2 - HO - 1,       # I4  (constant-free self-closure)
    NS - d*BSD,           # I5  d = 2
    NS - YM*BSD,          # I6  (constant-free)
    YM - POI - e,         # I7  e = 1
    RH*NS - NS - BSD,     # I8  (constant-free)
    RH*YM - f,            # I9  f = 3
    NP - HO - cg,         # I10 c = 1/4
    QG**2 - YM*p,         # I11 (constant-free apart from pi)
]
print('  Structural (constant-free) core: I1, I4, I6, I8, I11.')
print('  Derive the anchored constants from the core + the single ratio d:')
# From I6 and I5 (BSD != 0):        YM = d
# From I8 and I5 (BSD != 0):        RH = 1 + 1/d
# hence:
d_ = sp.Symbol('d', positive=True)
YM_of_d = d_
RH_of_d = 1 + 1/d_
print(f'    I5 & I6  (a_BSD != 0)  =>  a_YM  = {YM_of_d}')
print(f'    I5 & I8  (a_BSD != 0)  =>  a_RH  = {sp.simplify(RH_of_d)}')
print(f'    I2       =>  a = a_RH^2      = {sp.simplify(RH_of_d**2)}'
      f'   [d=2 -> {sp.simplify((RH_of_d**2).subs(d_,2))}]')
print(f'    I9       =>  f = a_RH a_YM   = {sp.simplify(RH_of_d*YM_of_d)}'
      f'   [d=2 -> {sp.simplify((RH_of_d*YM_of_d).subs(d_,2))}]')
print(f'    I3 & I11 =>  b = a_YM pi     = {sp.simplify(YM_of_d*p)}'
      f'   [d=2 -> {sp.simplify((YM_of_d*p).subs(d_,2))}]')
print(f'    I1       =>  a_P = sqrt(a_YM)= {sp.sqrt(YM_of_d)}'
      f'   [d=2 -> {sp.sqrt(2)}]')
print(f'    I7       =>  a_Poincare      = {sp.simplify(YM_of_d - e)}'
      f'   [d=2, e=1 -> 1]')
print('    I4       =>  a_Hodge = phi          (NO input -- genuine pin)')
print('    I10      =>  a_NP = a_Hodge + c     (c is an input)')
print('    ---      =>  a_BSD               UNCONSTRAINED')
print()
print('  So the anchored constants 9/4, 3, 2pi and (with e=1) 1 are all')
print('  functions of the SINGLE ratio d = a_NS/a_BSD.  Setting d = 2 fixes')
print('  all four at once.  They are five spellings of one assumption.')

# verify the five spellings really do collapse to "a_YM = 2"
print('\n  verification that each anchored invariant, given the structural')
print('  core, is equivalent to a_YM = 2:')
core = [P**2 - YM, HO**2 - HO - 1, NS - YM*BSD, RH*NS - NS - BSD, QG**2 - YM*p]
for label, extra in [('I2  a_RH^2=9/4', RH**2 - Q(9, 4)),
                     ('I3  a_QG^2=2pi', QG**2 - 2*p),
                     ('I5  a_NS=2a_BSD', NS - 2*BSD),
                     ('I9  a_RH a_YM=3', RH*YM - 3)]:
    Gx = sp.groebner(core + [extra] + [BSD*sp.Symbol('u') - 1],
                     *(V + [sp.Symbol('u')]), order='lex',
                     domain=sp.QQ.frac_field(p))
    red = sp.simplify(Gx.reduce(YM - 2)[1])
    red2 = sp.simplify(Gx.reduce(sp.expand((YM - 2)*(5*YM + 2)))[1])
    print(f'    core + {label:<18} |- a_YM = 2 ? {str(red == 0):<6}'
          f' |- (a_YM-2)(5a_YM+2)=0 ? {red2 == 0}')
print('  I2 alone leaves the spurious branch a_YM = -2/5 (from a_RH = -3/2);')
print('  positivity of a_RH removes it.  With a_RH > 0 all four are equivalent')
print('  to a_YM = 2.')

banner('9b. THE NP QUADRATIC FALLS OUT OF THE GROEBNER BASIS')
q = [g for g in G.exprs if NP in g.free_symbols and HO not in g.free_symbols]
print('  GB element in a_NP alone:', q)
print('  times 16:', [sp.expand(16*x) for x in q])
print('  This is exactly the corpus\'s "self-adjointness quadratic"')
print('  16 a_NP^2 - 24 a_NP - 11 = 0.  It is I4 and I10 combined -- i.e.')
print('  (a_NP - 1/4)^2 = (a_NP - 1/4) + 1.  It contains no information the')
print('  pair (I4, I10) did not already contain.')


# ----------------------------------------------------------------------
# 10. The pi-sector: homogeneity check.
# ----------------------------------------------------------------------
banner('10. THE PI-SECTOR: is pi structural or a scale?')
lam, mu = sp.symbols('lam mu', positive=True)
# rescale: pi -> lam*pi, a_QG -> sqrt(lam) a_QG, a_NS -> mu a_NS,
#          a_BSD -> mu a_BSD, everything else fixed.
sub = {p: lam*p, QG: sp.sqrt(lam)*QG, NS: mu*NS, BSD: mu*BSD}
print('  substitute  pi -> lam*pi,  a_QG -> sqrt(lam)*a_QG,')
print('              a_NS -> mu*a_NS,  a_BSD -> mu*a_BSD   (lam, mu > 0)')
allhom = True
for i in sorted(E):
    new = sp.expand(sp.simplify(E[i].subs(sub, simultaneous=True)))
    # is it a unit multiple of the original?
    ratio = sp.simplify(sp.cancel(new / E[i])) if E[i] != 0 else None
    hom = ratio.free_symbols.issubset({lam, mu}) if ratio is not None else False
    allhom &= bool(hom)
    print(f'    I{i:<3} -> {new}          scaling factor = {ratio}')
print(f'\n  every invariant rescales by a unit: {allhom}')
print('  => the eleven are invariant under an independent rescaling of')
print('     (pi, a_QG) and of (a_NS, a_BSD).  pi therefore enters only as')
print('     the UNIT of the QG sector; it does not communicate with the')
print('     NS/BSD sector at all.  a_NS = 3pi/2, a_BSD = 3pi/4 carry pi by')
print('     DEFINITION only -- the web says nothing beyond a_NS = 2 a_BSD.')


# ----------------------------------------------------------------------
# 11. Two distinct consistent assignments (the under-determination witness
#     that will be formalised in Lean).
# ----------------------------------------------------------------------
banner('11. TWO DISTINCT CONSISTENT ASSIGNMENTS')
A = dict(PT)                       # the framework's own
B = dict(PT); B[NS] = 2; B[BSD] = 1   # BSD := 1, NS := 2
for nm, S in [('A (framework)', A), ('B (a_BSD := 1)', B)]:
    resid = [sp.simplify(sp.expand(E[i].subs(S))) for i in sorted(E)]
    print(f'  {nm:<16} all eleven hold: {all(r == 0 for r in resid)}   '
          f'a_BSD = {S[BSD]}, a_NS = {S[NS]}')
print('  A and B differ in a_BSD and a_NS but satisfy the identical eleven')
print('  invariants and are both strictly positive.  UNDER-DETERMINED.')


# ----------------------------------------------------------------------
# 12. Numerical checks at 60 digits (labelled: checks, not claims).
# ----------------------------------------------------------------------
banner('12. NUMERICAL CHECKS (60 dps) -- verification only, no new claims')
PHI = (1 + mp.sqrt(5)) / 2
vals = {
    'phi                 ': PHI,
    'phi + 1/4           ': PHI + mp.mpf(1)/4,
    'sqrt(2)             ': mp.sqrt(2),
    'sqrt(2 pi)          ': mp.sqrt(2*mp.pi),
    '3 pi / 2            ': 3*mp.pi/2,
    '3 pi / 4            ': 3*mp.pi/4,
}
for k, v in vals.items():
    print(f'  {k} = {mp.nstr(v, 45)}')
print('  phi^2 - phi - 1     =', mp.nstr(PHI**2 - PHI - 1, 10))
print('  (3pi/2) - 2*(3pi/4) =', mp.nstr(3*mp.pi/2 - 2*(3*mp.pi/4), 10))
print('  |phi+1/4 - 1.868|   =', mp.nstr(abs(PHI + mp.mpf(1)/4
                                             - mp.mpf('1.868')), 10),
      '  <- the IBM row is 3-decimal; this is the actual gap')

banner('DONE')
