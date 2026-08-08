#!/usr/bin/env python3
"""
B<->Z prospective test: is the clustered/dispersed pair a discriminator for
WORD-LEVEL structure, or only for ordinary junction cooperativity?

Pablo's candidate pair.  Verified here to be matched at BOTH levels:
overlapping steps  CG x8, GC x8, CA x2, AC x2, GT x2, TG x2, and
non-overlapping units (the ones that matter)  CG x8, CA x2, TG x2.
    dispersed  CACGCACGCGCGTGCGCGTGCGCGC
    clustered  CGTGTGCGCGCGCGCGCGCGCACAC
PF's multiscale hypothesis predicts |sigma_50,clustered| < |sigma_50,dispersed|.
Z-DNA Hunter scores both 20.0 / 83.33%; additive dinucleotide energy is equal by
construction.

THE QUESTION THIS SCRIPT ANSWERS.  Z-Hunter and additive scoring are not the
state of the art.  The conventional treatment (Ho et al. 1986; Peck & Wang;
Ellison-Rich lineage) is already a two-state transfer matrix: each dinucleotide
step is B or Z, Z costs a sequence-dependent free energy, and each B/Z junction
costs a large penalty (~4-5 kcal/mol).  Does THAT model already separate the
pair?  If it does, a positive experiment confirms textbook cooperativity and
says nothing about word structure, and the prospective test as designed cannot
support the PF claim.

MODEL.  Two-state chain over the 12 NON-OVERLAPPING dinucleotide units.
    configuration weight  =  prod_i w_i(s_i) * J^(number of B/Z junctions)
    w_i(B) = 1,   w_i(Z) = exp(-(dG_i - mu)/RT),   J = exp(-dG_J/RT)
    Z = v^T M_1 ... M_{n-1} u   (exactly the ordered product formalized in r213)
`mu` is the per-step driving force supplied by negative supercoiling.  Rather
than invent supercoiling constants, we report

    mu_50  =  the driving force at which the mean Z-fraction reaches 1/2,

a monotone PROXY for |sigma_50|: larger mu_50 <=> harder to flip <=> larger
|sigma_50|.  So the PF prediction |sigma_50,clustered| < |sigma_50,dispersed|
becomes  mu_50(clustered) < mu_50(dispersed).

PARAMETERS ARE ILLUSTRATIVE AND EXTERNAL.  We do not claim literature values.
That is why the script does not report a single number: it SWEEPS dG and dG_J
across the plausible range and asks whether the SIGN of the separation is
stable.  A sign that is stable across the sweep is a property of the model
class, not of a parameter choice.

FALSIFIER FOR THIS SCRIPT'S OWN CONCLUSION: if at dG_J = 0 (no junction penalty)
the two sequences do NOT come out exactly equal, the implementation is wrong,
because at zero cooperativity the partition function depends only on
composition, which is identical by construction.  That check is asserted.
"""
import math
from collections import Counter
import itertools

RT = 0.616  # kcal/mol at 37 C -- scale only; conclusions are sign-based

DISPERSED = "CACGCACGCGCGTGCGCGTGCGCGC"
CLUSTERED = "CGTGTGCGCGCGCGCGCGCGCACAC"


def dinucs(seq):
    """NON-OVERLAPPING dinucleotide units.

    This is the physics, and getting it wrong was the first thing this script
    got wrong.  Z-DNA's repeating unit is a dinucleotide in alternating
    anti-syn conformation, so the chain sites are non-overlapping PAIRS, and
    the Ho et al. energetics are tabulated per unit.  Using overlapping steps
    instead makes a pure CG run read as CG, GC, CG, GC, ... and so charges a
    spurious high-energy GC at every other site -- which inverts the answer.
    Both sequences are matched at this level too: CA x2, CG x8, TG x2.
    """
    return [seq[i:i + 2] for i in range(0, len(seq) - 1, 2)]


def zfrac(seq, dG, dG_J, mu):
    """Mean Z-fraction by forward-backward on the two-state transfer chain."""
    d = dinucs(seq)
    n = len(d)
    J = math.exp(-dG_J / RT)
    wZ = [math.exp(-(dG[x] - mu) / RT) for x in d]

    # forward[i][s], s = 0 (B) or 1 (Z)
    fwd = [[0.0, 0.0] for _ in range(n)]
    fwd[0] = [1.0, wZ[0]]
    for i in range(1, n):
        for s in (0, 1):
            wt = 1.0 if s == 0 else wZ[i]
            fwd[i][s] = wt * (fwd[i - 1][s] + J * fwd[i - 1][1 - s])
    bwd = [[0.0, 0.0] for _ in range(n)]
    bwd[n - 1] = [1.0, 1.0]
    for i in range(n - 2, -1, -1):
        for s in (0, 1):
            bwd[i][s] = (bwd[i + 1][s] * (1.0 if s == 0 else wZ[i + 1])
                         + J * bwd[i + 1][1 - s] * (1.0 if s == 1 else wZ[i + 1]))
    Zpf = fwd[n - 1][0] + fwd[n - 1][1]
    pz = sum(fwd[i][1] * bwd[i][1] for i in range(n)) / (Zpf * n)
    return pz


def mu50(seq, dG, dG_J, lo=-10.0, hi=20.0):
    """Driving force at which mean Z-fraction = 1/2 (bisection; monotone in mu)."""
    for _ in range(200):
        mid = (lo + hi) / 2
        if zfrac(seq, dG, dG_J, mid) < 0.5:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def main():
    print("=" * 74)
    print("0. composition check -- the pair must be additively indistinguishable")
    print("=" * 74)
    a, b = Counter(dinucs(DISPERSED)), Counter(dinucs(CLUSTERED))
    print(f"   dispersed {dict(sorted(a.items()))}")
    print(f"   clustered {dict(sorted(b.items()))}")
    print(f"   identical: {a == b}")
    assert a == b, "the pair is not composition-matched; everything below is void"

    # illustrative Z-propensities, kcal/mol per NON-OVERLAPPING unit, B -> Z.
    # Ordering (CG cheapest, then CA/TG, then the rest) follows the Ho et al.
    # lineage; the numbers are illustrative and are swept below. Only the units
    # that actually occur here matter: CG, CA, TG.
    base = {"CG": 0.7, "CA": 1.3, "TG": 1.3, "GC": 4.0, "AC": 1.3, "GT": 1.3}
    for x in ("".join(p) for p in itertools.product("ACGT", repeat=2)):
        base.setdefault(x, 5.0)

    print()
    print("=" * 74)
    print("1. THE ASSERTED CHECK: at zero junction penalty the two MUST agree")
    print("=" * 74)
    m_d = mu50(DISPERSED, base, 0.0)
    m_c = mu50(CLUSTERED, base, 0.0)
    print(f"   dG_J = 0:  mu50 dispersed = {m_d:.9f}   clustered = {m_c:.9f}")
    print(f"              difference = {m_d - m_c:.3e}")
    assert abs(m_d - m_c) < 1e-6, "IMPLEMENTATION BUG: additive limit must tie"
    print("   PASSED -- at zero cooperativity composition alone decides, as it must.")

    print()
    print("=" * 74)
    print("2. the conventional cooperative model, swept over its parameters")
    print("=" * 74)
    print("   positive gap = clustered flips at LOWER driving force")
    print("                = the model already predicts |sigma50,clu| < |sigma50,dis|")
    print()
    print(f"   {'dG_J':>6} {'dG(CG)':>8} {"dG(oth)":>8} "
          f"{'mu50 disp':>11} {'mu50 clus':>11} {'gap':>10}  sign")
    signs = set(); npts = 0
    for dG_J in (0.5, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0):
        for cg in (0.3, 0.7, 1.1):
            for other in (1.0, 1.3, 1.8):
                if cg >= other:
                    continue  # unphysical: CG is the cheapest Z-former in all
                              # published tables. The ONLY sign flip in the full
                              # 63-point grid sits at (CG 1.1, other 1.0), i.e.
                              # exactly where that ordering is inverted.
                p = dict(base); p["CG"] = cg
                p["CA"] = p["TG"] = p["AC"] = p["GT"] = other
                md, mc = mu50(DISPERSED, p, dG_J), mu50(CLUSTERED, p, dG_J)
                gap = md - mc
                signs.add(gap > 1e-9); npts += 1
                if cg == 0.7 and other == 1.3:
                    print(f"   {dG_J:>6.1f} {cg:>8.1f} {other:>8.1f} "
                          f"{md:>11.5f} {mc:>11.5f} {gap:>10.5f}  "
                          f"{'clustered easier' if gap > 0 else 'dispersed easier'}")
    print()
    print(f"   swept {npts} physically-ordered parameter points (dG_CG < dG_other)")
    print(f"   distinct signs observed: {signs}")
    if signs == {True}:
        print("   => the CONVENTIONAL cooperative model predicts")
        print("      |sigma50,clustered| < |sigma50,dispersed| at EVERY point swept.")
        print()
        print("   CONSEQUENCE FOR THE PROSPECTIVE TEST: this pair separates PF from")
        print("   ADDITIVE scoring (Z-Hunter, dinucleotide energy) but NOT from the")
        print("   standard two-state cooperative model, which makes the same call.")
        print("   A confirming experiment would corroborate junction cooperativity;")
        print("   it would not evidence word-level structure.")
    else:
        print("   => sign is NOT stable across parameters. The conventional model")
        print("      does not settle the direction, so the pair may discriminate")
        print("      after all -- but only inside the parameter region to be named.")

    print()
    print("=" * 74)
    print("3. where the separation comes from: junction count, not word structure")
    print("=" * 74)
    print("   maximal runs of the CHEAPEST unit (CG), which set the junction count:")
    for name, s in (("dispersed", DISPERSED), ("clustered", CLUSTERED)):
        d = dinucs(s)
        cheap = [i for i, x in enumerate(d) if x == "CG"]
        runs, cur = [], [cheap[0]]
        for i in cheap[1:]:
            if i == cur[-1] + 1:
                cur.append(i)
            else:
                runs.append(cur); cur = [i]
        runs.append(cur)
        print(f"   {name:>10}: {len(runs)} maximal low-energy run(s), "
              f"lengths {[len(r) for r in runs]}, "
              f"=> {2*len(runs)} B/Z junctions")
    print()
    print("   The gap tracks the junction count difference. That is ordinary")
    print("   nearest-neighbour cooperativity, present in every model since 1986.")

    print()
    print("=" * 74)
    print("4. what a genuinely discriminating pair requires")
    print("=" * 74)
    print("   Two-by-two generic matrices generate a free monoid, so distinct")
    print("   orderings give distinct ordered products: the two-state model")
    print("   distinguishes essentially EVERY reordering. There is therefore no")
    print("   pair it cannot tell apart, and 'matched under the standard model'")
    print("   is unachievable exactly.")
    print()
    print("   So the discriminator must be a DISAGREEMENT, not a tie:")
    print("     find a composition-matched pair where the standard cooperative")
    print("     model and the PF word-level model predict OPPOSITE signs of")
    print("     mu50(A) - mu50(B), with a margin exceeding experimental error.")
    print("   Then the experiment refutes one of them whichever way it falls.")
    print()
    print("   BLOCKED PENDING INPUT: that search needs the PF word-level model's")
    print("   definition and parameters, which are not in this repo. Supply the")
    print("   k-mer state space and weights and the search is mechanical.")


if __name__ == "__main__":
    main()
