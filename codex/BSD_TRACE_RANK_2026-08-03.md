# Cross-front result: rank is readable from the TRACE of the corrected ch24 operator

**Date:** 2026-08-03. **Script:** `codex/bsd_trace_rank.py`. **Provenance of the
idea:** Pablo's standing principle that the Millennium axes are one object seen
from different perspectives. Applying the RH-front machinery (transfer
operators, holomorphic-Lefschetz traces) to the BSD face:

For the contracting system φ_p(x) = x/p with weights a_p/p^s — ch24's operator
on its CORRECT carrier — the fixed-point trace is a regularized Mestre–Nagao
sum, and near s = 1, log L(E,s) = Σ_p a_p p^{-s} + O(1) with a rank-r zero
predicts

    S_E(s) = Σ_p a_p p^{-s}  ~  r · log(s−1).

**ch24's intuition "rank is spectral" is correct at the level of the TRACE —
not the eigenvalue multiplicity the chapter originally claimed** (that version
stays falsified; see CH24_OPERATOR_QUASINILPOTENT_2026-07-30.md).

## Measurement (P = 5·10⁴, truncation-gated, ranks kernel-verified)

| curve | verified rank | fitted trace slope | spacing |
|---|---|---|---|
| 37a1 | 1 | +0.780 | — |
| 389a1 | 2 | +1.473 | +0.69 |
| 5077a1 | 3 | +2.168 | +0.70 |

Monotone in rank, evenly spaced to within the residuals (rms 0.02–0.05),
truncation drift an order below the signal. The slopes sit below the
asymptotic prediction (1, 2, 3) because P = 5·10⁴ probes s−1 ≳ 0.09, far from
the s→1 asymptote — the same finite-cutoff renormalization documented in the
07-30/31 ch24 records. The RANK INFORMATION is in the ordering and the equal
spacing, both of which are unambiguous here.

## What this sets up

1. A rigorous target with real content: the holomorphic-Lefschetz fixed-point
   formula for weighted composition operators on H² — trace = Σ w(x*)/(1−φ'(x*))
   — is a classical theorem, UNFORMALIZED anywhere, and it serves BOTH fronts
   (Mayer traces on the RH face, Mestre–Nagao traces on the BSD face). It is
   the natural r188+ Lean stone on top of r183–r186.
2. The honest analytic statement for the book's ch24 repair: replace the
   falsified multiplicity mechanism with the trace mechanism, which is (a)
   classical mathematics (Mestre–Nagao), (b) now measured on kernel-verified
   ranks, (c) formalizable.

Scope: proves nothing about BSD. It reframes ch24's surviving signal in the
operator language correctly and gives the framework's unification principle a
concrete, measured instance: one machinery, two Millennium faces.
