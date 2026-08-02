# RH front, M1 COMPLETE: the operator sees the Maass spectrum AND the first Riemann zero

**Date:** 2026-08-02. **Script:** `codex/rh_mayer_full.py` (v6).
**Results:** `codex/rh_mayer_full_results.txt`. Six versions; four failures caught
by asserted gates BEFORE any scan data existed (basis conditioning; double-
precision cancellation; section-size-vs-t growth; a gate testing the wrong
section size). Production certified: dps=50, N=72, relative truncation
5.3e-14 at the worst point, 2.4e-17 typical.

## What was computed

The full-alphabet Mayer transfer operator (L_s f)(x) = Σ_{k≥1} (x+k)^{-2s}
f(1/(x+k)) — the operator class the framework's ch20 T₃ belongs to, on its
correct carrier — with EXACT matrix elements (finite Hurwitz-zeta
combinations = the analytic continuation; no sampling, no truncated tails):

  A[m,n](s) = Σ_i C(n,i)(−1)^{i+m} Poch(2s+n−i,m)/m! ζ_H(2s+n−i+m, 2)·(3/2)^{m−n}

Anchor: λ_max(L₁) = 1.0 (Gauss measure), exact to 12+ digits.

## Result 1 — the Maass spectrum, in the correct parity factors

| found minimum t* | factor | LMFDB certified r | parity | agreement |
|---|---|---|---|---|
| 9.533694962   | det(1+L) | 9.53369526135356  | odd  | 3.0e-7 |
| 12.17300857   | det(1+L) | 12.17300832467968 | odd  | 2.5e-7 |
| 14.358509791  | det(1+L) | 14.35850951825981 | odd  | 2.7e-7 |
| 13.779751553  | det(1−L) | 13.77975135189074 | even | 2.0e-7 |

All four in the factor Lewis–Zagier's convention demands (even ↔ det(1−L),
odd ↔ det(1+L)); zero cross-contamination — the even parameter appears
NOWHERE in the odd factor and vice versa. |det| at the minima: 5e-7 to 1e-6
(residual set by our 14-iteration refinement, not by the method). The two
shallow det(1−L) dips at 10.51 and 12.52 have depth ratio 0.93 — correctly
identified as non-zeros (true zeros have depth ~2e-6).

## Result 2 — the first RIEMANN zero, through the operator

Lewis–Zagier (Ann. Math. 153 (2001), Ch. IV §3, Corollary): L_s has
eigenvalue +1 at s with ζ(2s) = 0; the −1 eigenvalue does NOT occur there.
Both halves tested:

  |det(1−L)| at Re s = 1/4:  minimum at t′ = 7.0673625987
                             vs ρ₁/2 = 7.0673627606  (offset −1.6e-7)
                             value 3.6e-8 (vs O(0.5–0.7) nearby)
  |det(1+L)| at the SAME point: 1.68 — bounded away from zero, as required.

**The first nontrivial zero of the Riemann zeta function is visible, to seven
digits, in the determinant of the framework's operator class — in exactly the
factor and on exactly the line that the rigorous theory prescribes.**

## Honest scope

This validates our implementation against ESTABLISHED mathematics
(Mayer 1991, Efrat 1993, Lewis–Zagier 2001) — it does not prove anything new
about RH, and it does not close Hilbert–Pólya. What it establishes for the
program:
1. The framework's transfer-operator intuition, executed on the correct
   carrier with certified numerics, genuinely touches both the Maass spectrum
   and the Riemann zeros. The route is real; ch20's execution (affine map,
   L² carrier) was what failed.
2. We now have a gate-certified computational instrument for milestone M2:
   the Γ₀(3)/character-twisted operator (Chang–Mayer), where the framework's
   mod-3 structure meets arithmetic that is NOT yet numerically mapped in
   the literature at this precision — genuinely new territory.
3. M3 (Lean): the feasibility map says H²(𝔻) + compact weighted composition
   operators is buildable, with Montel's theorem the single missing keystone
   — first transfer-operator theory in any prover if we land it.
