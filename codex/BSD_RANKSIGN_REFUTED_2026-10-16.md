# The BSD rank-sign statistic is REFUTED — do not formalize it

**Date:** 2026-10-16 (Legion). **Verdict: the sign rule of
`M_log^Re(E,X)` does not detect rank.** The ~400-declaration formalization
project is cancelled. This note exists so the question is not re-litigated.

Subject: `PF/BSDRankSignBridge.lean` — `M_log_Re_BSD_statistic`,
`fractalBSDRankSignBridge`, `partial_BSD_via_rank_sign_bridge`.
Companion: `PF/BSDRankSignBridgeObstruction_2026_10_15.lean` (commit
`ab2c6796`) proved the *current* Lean carrier vacuous. This note shows the
*repaired* statistic would fail too, so the repair is not worth building.

## The claim under test

`BSDRankSignBridge.lean:84-85`:

```
sign(M_log^Re(E, X)) = +1   <=>   rank(E(Q)) = 0
sign(M_log^Re(E, X)) = -1   <=>   rank(E(Q)) >= 1
```

with `M_log^Re(E,X) := -SUM_{p<=X} a_p(E) * Re(r_p) * log p / (p log X)`,
`r_p = p^{-1/2} e^{i pi alpha D_3(p)}`, `alpha = 3pi/4`.

## Phase reading used

The literal docstring reading: phase `= pi * alpha * D_3(p)` with
`alpha = 3pi/4`, i.e. `cos(3 pi^2 / 4 * D_3(p))`. This is the only one of the
two candidate readings that reproduces the **signs** of the file's own
published table; the alternative (`phase = alpha * D_3`) inverts every sign.
Neither reading reproduces the published **magnitudes** — see "provenance gap".

Computed with good primes only (`p | Delta` skipped, `p = 2` skipped, since the
character-sum point count needs `p` odd), `a_p = -SUM_x chi(4x^3 + b_2 x^2 +
2 b_4 x + b_6)` via the Legendre symbol, `X = 2000`.

## The test

**Group A — rank >= 1, corpus-verified.** The nine curves of conductor 37..106
that carry kernel-clean `_rank_ge_one` theorems in this repo (r134-r142).
Ranks are corpus-verified, not asserted.

**Group B — rank 0.** Ten curves found by search, each verified to carry only
torsion: a wide rational-point search (`x = u/v`, `|u| <= 60v`, `v <= 12`)
found no point of infinite order. **The same search was run on group A as a
control and DID find infinite-order generators** (37a1: 14 points, 43a1: 14,
53a1: 10 — all infinite order), so the search is strong enough to detect
rank >= 1 in this conductor range.

## Result

| group | n | M < 0 | M > 0 | range |
|---|---|---|---|---|
| A (rank >= 1) | 9 | 9 | 0 | `-0.1332 .. -0.0155` |
| B (rank 0) | 10 | **6** | 4 | `-0.1129 .. +0.0882` |

**Six of ten rank-0 curves carry the wrong sign.** The ranges overlap
heavily; the sign is right on 4/10 rank-0 curves, no better than a coin flip.

Wrong-signed rank-0 curves (a-invariants, |Delta|, torsion orders found, M):

```
(1, 1, 1,  0, 0)   15   [2,4]     -0.093501
(1, 0, 1,  0, 0)   26   [3]       -0.028828
(0, 0, 1,  0, 0)   27   [3]       -0.010933
(1, 0, 1, -1, 0)   28   [2,3,6]   -0.062830
(0, 1, 1, -3, 1)   37   [3]       -0.112948
(1, 1, 0,  1, 0)   39   [2]       -0.007300
```

## The decisive pair — conductor-matched, opposite rank, same sign

`(0, 1, 1, -3, 1)` has `|Delta| = 37`, torsion `Z/3`, and no infinite-order
point under the wide search: **rank 0**. It gives `M = -0.112948`.

`37a1 = (0, 0, 1, -1, 0)` has the same discriminant 37 and **rank 1**
(kernel-verified, r134). It gives `M = -0.085736`.

Same conductor. Opposite rank. **Same sign — and the rank-0 curve is MORE
negative than the rank-1 curve.** This is the natural experiment the sign rule
has to pass, and it fails it outright. The rank/conductor confound flagged by
`codex/` script `ch24_spectral_robustness.py` is not the only problem: here
conductor is held fixed and the statistic still cannot tell the ranks apart.

## Provenance gap (independent of the above)

The file's published table cannot be reproduced from the file's own formula:

| curve | file | phase = pi*alpha*D3 | phase = alpha*D3 |
|---|---|---|---|
| 11a1 | +0.170 | +0.061 | -0.042 |
| 37a1 | -0.580 | -0.086 | +0.055 |
| 389a1 | -0.767 | -0.141 | +0.087 |
| 5077a1 | -0.143 | -0.137 | +0.191 |

Magnitudes are 3-5x off under the literal reading and sign-inverted under the
alternative. Also, the file's claimed "monotone rank ladder 0 -> 1 -> 2 in
|M_log^Re|: (0.17, 0.58, 1.05)" does not appear at all: rank 1 spans
-0.015..-0.133, rank 2 is -0.141, rank 3 is -0.137 — ranks 2 and 3 sit inside
the rank-1 range. Only the sign ever carried information, and the sign is now
refuted.

Note the published 4-curve table used exactly ONE rank-0 curve, 11a1, which is
one of the 4 of 10 that happen to get the right sign. The "4/4 correct" rested
on a lucky draw.

## What was cancelled, and what remains true

CANCELLED: implementing `M_log_Re_BSD_statistic` for real. The scope was
35-60 declarations (Fintype on `W.Point` over a finite field — absent from
mathlib entirely; `#E(F_p)`; `a_p`; the analytic wrapper) plus ~300 certified
per-prime `a_p` facts per curve for in-kernel evaluation, with bad primes
blocked on Tate's algorithm (also entirely absent). None of that is worth
building for a refuted sign rule.

STILL TRUE, and unaffected: `fractalBSDRankSignBridge E` is false for every
`E` as currently defined (`ab2c6796`), and
`partial_BSD_via_rank_sign_bridge` is vacuous. Independently, even a correct
statistic would leave the bridge Prop open at Goldfeld+GRH strength — the file
says so itself at `:92`.

NOT claimed here: that no R_f-twisted statistic can detect rank. This refutes
**the statistic as specified in this file**, at `alpha = 3pi/4` with this
weight, on this 19-curve set. An impossibility theorem for the whole family
would need its own argument.

Scripts: `scratchpad/confound2.py` (the test), `verify_rank0.py` (the
rank-0 verification with controls). Numerics only; nothing was tuned, and no
value was chosen to produce this outcome.
