#!/usr/bin/env python3
"""
Measure, do not assume: is the theta landed in
PF/YangMills/ReflectionPositivityGram_2026_10_17.lean the geometric time
reflection that leaves the Wilson action invariant?

Mirrors the Lean definitions EXACTLY (WilsonMeasure_2026_10_17.lean):
  LatticeSite L   := Fin 4 -> Fin L
  LatticeLink L   := LatticeSite L x Fin 4
  shiftSite x mu  := Function.update x mu (x mu + 1)          -- mod L
  plaquetteHolonomy U (x,mu,nu) :=
      U(x,mu) * U(shift x mu, nu) * U(shift x nu, mu)^-1 * U(x,nu)^-1
  wilsonActionDensity U p := 1 - (1/2) * Re tr (plaquetteHolonomy U p)
  wilsonActionTotal U     := sum over ALL p : Plaquette L  (= sites x 4 x 4)
  timeReflectionSite x       := Function.update x 0 (-(x 0))  -- (-t) mod L
  timeReflectionLink (x,mu)  := (timeReflectionSite x, mu)    -- direction kept
  timeReflectionGaugeField U := fun l => U (timeReflectionLink l)

Variants tested:
  V1 = exactly the Lean definition (direction kept, no inverse)
  V2 = geometric site reflection: spatial links reflect in place; a temporal
       link based at t maps to the one based at (-t-1) WITH the inverse
       (reversed traversal)
  V3 = V2 without the inverse, to isolate which correction matters
"""
import numpy as np
import itertools, sys

rng = np.random.default_rng(20261017)


def rand_su2():
    q = rng.normal(size=4)
    q /= np.linalg.norm(q)
    a, b, c, d = q
    return np.array([[a + 1j * b, c + 1j * d],
                     [-c + 1j * d, a - 1j * b]], dtype=complex)


def inv_su2(U):
    return U.conj().T          # SU(2): U^-1 = U^dagger


def rand_field(L):
    # shape (L,L,L,L,4,2,2)
    F = np.empty((L, L, L, L, 4, 2, 2), dtype=complex)
    for idx in itertools.product(range(L), repeat=4):
        for mu in range(4):
            F[idx + (mu,)] = rand_su2()
    return F


def shift(x, mu, L):
    y = list(x)
    y[mu] = (y[mu] + 1) % L
    return tuple(y)


def action(F, L):
    S = 0.0
    for x in itertools.product(range(L), repeat=4):
        for mu in range(4):
            for nu in range(4):
                H = (F[x + (mu,)]
                     @ F[shift(x, mu, L) + (nu,)]
                     @ inv_su2(F[shift(x, nu, L) + (mu,)])
                     @ inv_su2(F[x + (nu,)]))
                S += 1.0 - 0.5 * np.trace(H).real
    return S


def theta_site(x, L):
    y = list(x)
    y[0] = (-y[0]) % L
    return tuple(y)


def reflect(F, L, variant):
    G = np.empty_like(F)
    for x in itertools.product(range(L), repeat=4):
        tx = theta_site(x, L)
        for mu in range(4):
            if variant == 1:                       # the Lean definition
                G[x + (mu,)] = F[tx + (mu,)]
            else:
                if mu != 0:
                    G[x + (mu,)] = F[tx + (mu,)]
                else:
                    y = list(tx)
                    y[0] = (y[0] - 1) % L          # theta(x) - e_0
                    y = tuple(y)
                    G[x + (mu,)] = inv_su2(F[y + (0,)]) if variant == 2 \
                        else F[y + (0,)]
    return G


def involution_defect(F, L, variant):
    return np.max(np.abs(reflect(reflect(F, L, variant), L, variant) - F))


# ---------------------------------------------------------------- action test
print("=" * 72)
print("TEST 1 - is the Wilson action invariant under each theta?")
print("=" * 72)
for L in (4, 5):
    F = rand_field(L)
    S0 = action(F, L)
    print(f"\nL = {L}   S(U) = {S0:.10f}")
    for v, name in ((1, "V1  Lean as-written  "),
                    (2, "V2  geometric + inv  "),
                    (3, "V3  geometric, no inv")):
        Sv = action(reflect(F, L, v), L)
        d = abs(Sv - S0)
        inv_def = involution_defect(F, L, v)
        verdict = "INVARIANT" if d < 1e-9 else "NOT INVARIANT"
        print(f"  {name}  S(thU) = {Sv:14.10f}   |dS| = {d:.3e}   "
              f"involution defect = {inv_def:.2e}   -> {verdict}")

# ------------------------------------------------- link partition / straddling
print()
print("=" * 72)
print("TEST 2 - does the link set split as Lambda+ | Lambda0 | Lambda- ,")
print("         and is any plaquette straddling?  (geometric theta, V2)")
print("=" * 72)


def classify(L):
    """Return (n_fixed_slices, n_theta_fixed_temporal_links_per_spatial_site,
    n_straddling_plaquettes) for the torus with time reflection t -> -t."""
    fixed_t = [t for t in range(L) if (-t) % L == t]
    # temporal link based at time t spans {t, t+1}; theta maps it to base -t-1
    fixed_temporal = [t for t in range(L) if (-t - 1) % L == t]
    return fixed_t, fixed_temporal


for L in (4, 5, 6, 7, 8):
    fixed_t, fixed_temporal = classify(L)
    print(f"  L = {L}:  theta-fixed time slices = {fixed_t}   "
          f"theta-fixed TEMPORAL links (base times) = {fixed_temporal}"
          + ("   <-- clean split" if not fixed_temporal else
             "   <-- NO clean split: a temporal link maps to itself reversed"))
print()
print("A theta-fixed temporal link cannot be put in Lambda+ or Lambda-, so the")
print("three-way product decomposition of Measure.pi fails for those L.")
