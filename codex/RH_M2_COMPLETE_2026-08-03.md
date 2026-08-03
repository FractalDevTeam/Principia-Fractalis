# RH front, M2 COMPLETE: the Γ₀(3) transfer operator reproduces the certified level-3 spectrum to 8 digits

**Date:** 2026-08-03. **Scripts:** `codex/rh_gamma03_m2.py` (construction +
validations + gated scan), `codex/rh_gamma03_refine.py` (refinement).
**Raw outputs:** `rh_gamma03_m2_results.txt`, `rh_gamma03_refined.txt`.
**Pilot record:** commit `9da46096`. Reference data fetched by an independent
agent from LMFDB's rigorous collection and Fraczek–Mayer (arXiv:1011.4441);
the targets never appeared in any scan or refinement script.

## The digit-level table

P-twisted ρ₃ factor of Z_{Γ₀(3)}, Re s = 1/2, dps=40, N=56 (gate-certified):

| refined t* | factor | LMFDB certified r | parity | agreement |
|---|---|---|---|---|
| 4.38805359256 | det(1+PL) | 4.38805356322 | odd  | 2.9e-8 |
| 5.09874192868 | det(1−PL) | 5.09874190873 | even | 2.0e-8 |
| 6.12057552283 | det(1+PL) | 6.12057553309 | odd  | 1.0e-8 |
| 6.75741524181 | det(1+PL) | 6.75741527775 | odd  | 3.6e-8 |
| 7.75813318201 | det(1+PL) | 7.75813319502 | odd  | 1.3e-8 |
| 8.03886124016 | det(1−PL) | 8.03886120386 | even | 3.6e-8 |
| 8.19303589686 | det(1+PL) | 8.19303593168 | odd  | 3.5e-8 |
| 8.77828237791 | det(1−PL) | 8.77828239355 | even | 1.6e-8 |
| 9.29237936829 | det(1+PL) | 9.29237932822 | odd  | 4.0e-8 |
| 9.53369522128 | det(1+PL) | 9.53369526135 | odd  | 4.0e-8 |

Ten for ten at 1–4 × 10⁻⁸; parity split exact (even ↔ det(1−PL), odd ↔
det(1+PL), the level-1 convention persisting); the tenth line is the level-1
oldform appearing a SECOND time in the ρ₃ factor — the multiplicity-2 oldform
prediction, confirmed quantitatively. The next certified value (9.7437) lies
past the scan edge and is correctly absent. |det| at minima: 4e-8 – 4e-7.

**The near-coincidence test passed.** The reference agent flagged the trap in
advance: the level-3 even form at 8.038861 sits 9×10⁻⁴ from the first
Dirichlet L(s,χ₃) zero at 8.039737. Our minimum lands on the Maass form and
NOT the L-zero — the operator resolves two values a part-in-ten-thousand
apart, and lands on the one the theory says it must (Huxley's determinant:
L(s,χ₃) cannot appear in the Γ₀(3) trivial-character scattering; χ₃ is odd,
inadmissible at weight 0).

## What M2 establishes

1. The framework's mod-3 structure, executed through the induced-representation
   transfer operator, reproduces genuine level-3 arithmetic — the Maass
   spectrum of Γ₀(3) — at 8 digits, with structural features (parity factors,
   oldform multiplicity) correct and unfitted.
2. The instrument now covers congruence level: the same machinery extends to
   Γ₀(N) for any N (index grows; the method does not change).
3. Negative result stated plainly: no route from this operator to Dirichlet
   L(s,χ₃) at weight 0 exists; that hope is closed, not deferred.

## Process note

Two wrong configurations were caught before producing data: the untwisted
determinant (not the Selberg zeta — Fraczek–Mayer Thm 2.1.1) and an N=48
truncation 4% over its gate. Both fixed by correcting the configuration.
The intertwining relations P·ρ(S) = ρ(S)·P, P·ρ(T) = ρ(T⁻¹)·P are asserted
in code — the symmetry operator is proved right, not assumed.

## Next

M3 (Lean): H²(𝔻) + compact weighted composition operators, Montel keystone —
turning this validated numerics into kernel-checked mathematics is what makes
it Paper-Gate material. The numerics here are the map; the Lean is the claim.
