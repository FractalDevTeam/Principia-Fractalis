#!/usr/bin/env python3
"""
Measure the three identities the OS-RP proof actually consumes.

With the geometric site reflection theta (variant V2) and L EVEN, and the link
partition Lambda+ / Lambda0 / Lambda- :

  I1  S  = S+ + S0 + S-                       (the decomposition is exhaustive)
  I2  S-(U) = S+(theta U)   and   S0(U) = S0(theta U)      (theta-conjugacy)
  I3  S+ does not depend on any Lambda- link  (tested by perturbation)
      S- does not depend on any Lambda+ link

I3 is the independent check of "no straddling plaquette", done at the level of
the action function rather than the combinatorics.
"""
import numpy as np
import itertools

rng = np.random.default_rng(42)
PLUS, ZERO, MINUS = "+", "0", "-"


def rand_su2():
    q = rng.normal(size=4); q /= np.linalg.norm(q)
    a, b, c, d = q
    return np.array([[a + 1j * b, c + 1j * d], [-c + 1j * d, a - 1j * b]], dtype=complex)


def inv_su2(U):
    return U.conj().T


def shift(x, mu, L):
    y = list(x); y[mu] = (y[mu] + 1) % L
    return tuple(y)


def label(x, mu, L):
    t, half = x[0], L // 2
    if mu != 0:
        if t == 0 or t == half:
            return ZERO
        return PLUS if 1 <= t <= half - 1 else MINUS
    return PLUS if 0 <= t <= half - 1 else MINUS


def theta_field(F, L):
    G = np.empty_like(F)
    for x in itertools.product(range(L), repeat=4):
        tx = list(x); tx[0] = (-tx[0]) % L; tx = tuple(tx)
        for mu in range(4):
            if mu != 0:
                G[x + (mu,)] = F[tx + (mu,)]
            else:
                y = list(tx); y[0] = (y[0] - 1) % L
                G[x + (mu,)] = inv_su2(F[tuple(y) + (0,)])
    return G


def sector_actions(F, L):
    """Return (S_plus, S_zero, S_minus) using the plaquette classification."""
    Sp = Sz = Sm = 0.0
    for x in itertools.product(range(L), repeat=4):
        for mu in range(4):
            for nu in range(4):
                if mu == nu:
                    continue
                links = [(x, mu), (shift(x, mu, L), nu),
                         (shift(x, nu, L), mu), (x, nu)]
                labs = {label(lx, lm, L) for lx, lm in links}
                H = (F[x + (mu,)] @ F[shift(x, mu, L) + (nu,)]
                     @ inv_su2(F[shift(x, nu, L) + (mu,)]) @ inv_su2(F[x + (nu,)]))
                dens = 1.0 - 0.5 * np.trace(H).real
                if labs == {ZERO}:
                    Sz += dens
                elif PLUS in labs and MINUS in labs:
                    raise AssertionError("straddling plaquette found!")
                elif PLUS in labs:
                    Sp += dens
                else:
                    Sm += dens
    return Sp, Sz, Sm


def total_action(F, L):
    S = 0.0
    for x in itertools.product(range(L), repeat=4):
        for mu in range(4):
            for nu in range(4):
                H = (F[x + (mu,)] @ F[shift(x, mu, L) + (nu,)]
                     @ inv_su2(F[shift(x, nu, L) + (mu,)]) @ inv_su2(F[x + (nu,)]))
                S += 1.0 - 0.5 * np.trace(H).real
    return S


for L in (4, 6):
    F = np.empty((L,) * 4 + (4, 2, 2), dtype=complex)
    for idx in itertools.product(range(L), repeat=4):
        for mu in range(4):
            F[idx + (mu,)] = rand_su2()

    Sp, Sz, Sm = sector_actions(F, L)
    S = total_action(F, L)
    tF = theta_field(F, L)
    tSp, tSz, tSm = sector_actions(tF, L)

    print("=" * 70)
    print(f"L = {L}")
    print(f"  S+ = {Sp:.10f}   S0 = {Sz:.10f}   S- = {Sm:.10f}")
    print(f"  I1  S+ + S0 + S- = {Sp+Sz+Sm:.10f}  vs  S = {S:.10f}   "
          f"|d| = {abs(Sp+Sz+Sm-S):.2e}")
    print(f"  I2  S-(U) = {Sm:.10f}  vs  S+(thU) = {tSp:.10f}   "
          f"|d| = {abs(Sm-tSp):.2e}")
    print(f"      S0(U) = {Sz:.10f}  vs  S0(thU) = {tSz:.10f}   "
          f"|d| = {abs(Sz-tSz):.2e}")

    # I3: perturb every Lambda- link in turn; S+ must not move.
    worst_p = worst_m = 0.0
    links = [(x, mu) for x in itertools.product(range(L), repeat=4)
             for mu in range(4)]
    minus_links = [l for l in links if label(l[0], l[1], L) == MINUS]
    plus_links = [l for l in links if label(l[0], l[1], L) == PLUS]
    for l in minus_links[:12]:
        G = F.copy(); G[l[0] + (l[1],)] = rand_su2()
        worst_p = max(worst_p, abs(sector_actions(G, L)[0] - Sp))
    for l in plus_links[:12]:
        G = F.copy(); G[l[0] + (l[1],)] = rand_su2()
        worst_m = max(worst_m, abs(sector_actions(G, L)[2] - Sm))
    print(f"  I3  max |dS+| over 12 Lambda- link perturbations = {worst_p:.2e}")
    print(f"      max |dS-| over 12 Lambda+ link perturbations = {worst_m:.2e}")
    print("      => S+ is a function of (U+, U0) only; S- of (U-, U0) only"
          if max(worst_p, worst_m) < 1e-9 else "      => DEPENDENCE LEAKS")
