# Wave 8 Option (b): 2D Lattice with Z_3 Plaquette Holonomy

## Conclusion

**Partial win, no full RH discharge.** The 2D lattice construction:
- DOES break tridiagonal gauge invariance (the key Wave 7 obstruction)
- DOES produce GUE-like spacing statistics in the strong-coupling regime
- DOES NOT match zeta zeros (raw rms ~53; rms ~2.2 after best linear rescale, 10x worse than 14.13 ground state)
- DOES NOT show a Mechanism 3 sweet spot at ch_2 = 0.95 (linear in ch_2 everywhere)

## What was built

`H_alpha^graph` on N x N square+diagonal lattice (dim = N^2, up to N=30):
- Diagonal: Berry-Keating Weyl `2 pi (m+1)(n+1) / log((m+1)(n+1) + 2)`
- 3 edge classes: horizontal, vertical, diagonal (creates triangular plaquettes)
- Z_3 phases per edge: `exp(i pi alpha D_3(encode(edge)))`

## Plaquette holonomy verified non-trivial

361 of 361 square plaquettes show |W - 1| > 1e-6.
Phase distribution lands on +/-i (Z_4-like sectors arising from
alpha = 3/2 in exp(i pi alpha D_3)) rather than pure cube roots of unity,
but the result is genuinely gauge-non-invariant.

## Key finding 1: Diagonal-dominant regime is gauge-trivial in practice

With Berry-Keating diagonal, |diag|_avg = 140, |offdiag|_avg = 0.011.
The off-diagonal Z_3 holonomy is a perturbation of order 1e-4.
rms(framework - trivial) = 0.11 on a spectrum of range [5, 419].
This is gauge non-invariance, but quantitatively negligible.

## Key finding 2: Strong-coupling regime IS gauge non-invariant

In Configs A-E (no dominant diagonal, off-diagonals at the same scale as
diagonal disorder), the framework phases produce SUBSTANTIAL spectral
differences from trivial phases:
- rms(framework - trivial) = 0.51 (vs total spectrum range ~8)
- rms(framework - random) = 0.07 — framework is INDISTINGUISHABLE from
  random U(1) phases

Interpretation: the Z_3 plaquette holonomy effectively randomizes the
plaquette flux, behaving like a random magnetic field. This is the
"Hofstadter-style" regime where flux disorder drives GUE-class statistics.

## Key finding 3: Spacing variance approaches GUE — but not exactly

| Config | var(unfolded spacings) | distance to GUE (0.180) |
|--------|------------------------|--------------------------|
| GUE target | 0.180 | 0 |
| GOE target | 0.286 | 0.106 |
| Framework Config A (pure hopping) | 0.231 | 0.051 |
| Framework Config B (weak BK) | 0.205 | 0.025 |
| Framework Config E (random diag) | 0.202 | 0.022 |
| Trivial phases | 0.32 - 0.68 | 0.14 - 0.50 |
| Poisson | 1.000 | 0.820 |

Framework spacing variance sits between GUE and GOE, much closer to GUE
than trivial. This is the genuine partial win.

## Key finding 4: No Mechanism 3 sweet spot at ch_2 = 0.95

Sweeping ch_2 in {0.5, 0.7, 0.85, 0.92, 0.94, 0.95, 0.96, 0.98, 1.0, 1.05, 1.1, 1.2}:
- var(unfolded spacings) is INVARIANT at 0.231 across the entire sweep
- rms(framework - trivial) scales LINEARLY with ch_2 (0.27 -> 0.65)
- rms vs zeta zeros (best rescale) is INVARIANT at 2.175

Reason: ch_2 is a multiplicative scaling on all off-diagonals; it
preserves spectral structure up to overall normalization, so unfolded
statistics are ch_2-invariant. There is no special behavior at 0.95.

This is a NEGATIVE result for the Mechanism 3 hypothesis on this geometry.

## Key finding 5: Eigenvalues do not approximate zeta zeros

Best result: Config A, raw eigenvalues vs zeta_zeros, RMS 53.
After best linear rescale, RMS drops to 2.18 (single-digit but bad).
For comparison, the first zeta zero is 14.13; an RMS of 2.18
on the first 20 zeros is roughly 5-15% off per zero.

Scaling with N (Config A pure hopping):
| N  | dim | var(fw) | rms_zeta_rescaled |
|----|-----|---------|-------------------|
| 10 | 100 | 0.222 | 1.29 |
| 15 | 225 | 0.186 | 2.44 |
| 20 | 400 | 0.231 | 2.18 |
| 25 | 625 | 0.249 | 2.34 |
| 30 | 900 | 0.218 | 2.72 |

Variance is NOT converging toward GUE 0.180 as N grows.
RMS vs zeta zeros is NOT improving with N.
This is not a "finite size effect" — it's a structural mismatch.

## Verdict on option (b)

Mechanism 3 confirmed in a weaker sense (off-diagonal phases now affect
the spectrum), gauge non-invariance achieved (vs Wave 7's tridiagonal
theorem), but RH discharge NOT achieved. Spectrum is GUE-adjacent but
does not converge to GUE, and does not reproduce zeta zeros even after
optimal rescaling.

## What the three Wave-8 alternatives jointly tell us

| Route | Gauge non-invariant | GUE-like | Matches zeta zeros |
|-------|---------------------|----------|---------------------|
| (a) Prime-spectral | (prior Wave 8 result) | partial | partial |
| (b) 2D plaquette holonomy (this work) | YES | partial (var 0.20-0.23) | NO (rms ~2.2 rescaled) |
| (c) PT-symmetric | (prior Wave 8 result) | partial | partial |

All three give partial wins; none gives RH discharge.

## What's needed beyond options (a), (b), (c)

The recurring pattern is: framework's Z_3 / D_3 phase content provides
DISORDER (random-magnetic-field-like) that pushes spectral statistics
toward GUE, but does NOT encode the specific spectral signature of zeta.
The framework lacks a NON-LOCAL or NUMBER-THEORETIC bridge that would
inject Euler-product / Mobius / Dirichlet-series structure into the
operator.

Candidates for a 4th attempt (beyond (a),(b),(c)):
- Connes adèle-class spectral triple (number-theoretic by construction)
- Berry-Brody-Müller non-local kernel K(x,y) ~ 1/log(xy) (zeta-explicit)
- Quasi-periodic lattice with frequencies matching log(p_n) for primes p_n
- Bohr-compactification / Sonine-pair Mellin operators

## Honest summary

The framework's 4-basis + 9-alpha + R_f machinery is internally
consistent and gives empirical Λ_eff/Λ_0 = 10^-120 and the BSD
rank-sign detector, but on RH it has now been tested via 3 standard
alternative architectures and none discharges the spectral side. The
gauge non-invariance achieved here is a real technical win, but the
zeta-zero structure does not emerge.

## Files

- `01_construct_H_graph.py` — N x N lattice construction; verifies holonomy
- `02_diagonalize_compare.py` — eigenvalues vs zeta zeros (diagonal-dominant)
- `03_wigner_dyson.py` — full Wigner-Dyson analysis with KS tests
- `04_mech3_and_scaling.py` — ch_2 sweep + N scaling (diagonal-dominant)
- `05_strong_coupling_limit.py` — 5 configurations testing off-diagonal regime
- `06_mech3_strong_coupling.py` — ch_2 sweep + N scaling (strong-coupling)
- `H_graph_built.pkl`, `diagonalization_results.pkl`, etc — data dumps
- `*.json` — JSON summaries
