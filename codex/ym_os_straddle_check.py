#!/usr/bin/env python3
"""
Measure the time-slice decomposition the OS theorem needs.

Link partition for the torus (Fin 4 -> Fin L) under site reflection t -> -t,
L EVEN, fixed slices T0 = {0, L/2}:

  spatial link (x,j), j != 0, at time t = x_0:
      t in {0, L/2}            -> Lambda_0   (lives in a fixed slice)
      t in {1 .. L/2-1}        -> Lambda_+
      t in {L/2+1 .. L-1}      -> Lambda_-
  temporal link (x,0) with base time t (spans t, t+1):
      t in {0 .. L/2-1}        -> Lambda_+
      t in {L/2 .. L-1}        -> Lambda_-

Questions measured:
  Q1  Is theta a bijection Lambda_+ -> Lambda_- ? (sizes equal, and no fixed link)
  Q2  Does ANY plaquette contain both a Lambda_+ link and a Lambda_- link?
      (a straddling plaquette - if none, S splits with NO cross term)
"""
import itertools

PLUS, ZERO, MINUS = "+", "0", "-"


def label(link, L):
    x, mu = link
    t = x[0]
    half = L // 2
    if mu != 0:
        if t == 0 or t == half:
            return ZERO
        return PLUS if 1 <= t <= half - 1 else MINUS
    else:
        return PLUS if 0 <= t <= half - 1 else MINUS


def shift(x, mu, L):
    y = list(x)
    y[mu] = (y[mu] + 1) % L
    return tuple(y)


def theta_link(link, L):
    """Geometric site reflection on links (variant V2, measured invariant)."""
    x, mu = link
    tx = list(x)
    tx[0] = (-tx[0]) % L
    if mu != 0:
        return (tuple(tx), mu)
    tx[0] = (tx[0] - 1) % L
    return (tuple(tx), 0)


def plaquette_links(x, mu, nu, L):
    return [(x, mu),
            (shift(x, mu, L), nu),
            (shift(x, nu, L), mu),
            (x, nu)]


print("=" * 74)
print("Q1 - is theta a bijection Lambda_+ -> Lambda_- ?")
print("=" * 74)
for L in (2, 4, 6, 8):
    links = [(x, mu) for x in itertools.product(range(L), repeat=4)
             for mu in range(4)]
    lab = {l: label(l, L) for l in links}
    nplus = sum(1 for l in links if lab[l] == PLUS)
    nzero = sum(1 for l in links if lab[l] == ZERO)
    nminus = sum(1 for l in links if lab[l] == MINUS)
    fixed = [l for l in links if theta_link(l, L) == l]
    maps_ok = all(lab[theta_link(l, L)] == MINUS for l in links
                  if lab[l] == PLUS)
    zero_ok = all(lab[theta_link(l, L)] == ZERO for l in links
                  if lab[l] == ZERO)
    print(f"  L={L}:  |L+|={nplus:5d}  |L0|={nzero:5d}  |L-|={nminus:5d}  "
          f"total={len(links):5d}   theta-fixed links={len(fixed)}")
    print(f"         theta(L+) subset L- : {maps_ok}    "
          f"theta(L0) subset L0 : {zero_ok}    |L+|==|L-| : {nplus == nminus}")

print()
print("=" * 74)
print("Q2 - is there any STRADDLING plaquette (contains both a L+ and a L- link)?")
print("=" * 74)
for L in (4, 6, 8):
    links_seen = {}
    straddling = 0
    total = 0
    pure_plus = pure_minus = pure_zero = 0
    for x in itertools.product(range(L), repeat=4):
        for mu in range(4):
            for nu in range(4):
                if mu == nu:
                    continue          # degenerate: holonomy = 1, density = 0
                total += 1
                labs = {label(l, L) for l in plaquette_links(x, mu, nu, L)}
                if PLUS in labs and MINUS in labs:
                    straddling += 1
                elif labs == {ZERO}:
                    pure_zero += 1
                elif PLUS in labs:
                    pure_plus += 1
                else:
                    pure_minus += 1
    print(f"  L={L}:  non-degenerate plaquettes={total:6d}   "
          f"STRADDLING={straddling}   "
          f"S+ ={pure_plus:6d}  S- ={pure_minus:6d}  S0 ={pure_zero:5d}")
    print(f"         S+ == S- : {pure_plus == pure_minus}"
          + ("   => action splits with NO cross term"
             if straddling == 0 else "   => cross term PRESENT"))
