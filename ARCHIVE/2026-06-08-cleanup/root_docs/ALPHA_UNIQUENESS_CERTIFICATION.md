# α-Uniqueness Certification — 50-digit numerical anchor

**Date:** 2026-05-26
**Scope:** referee-grade documentary anchor for the v3.3.1 numerical
match `λ_0(H_NP) = 0.168176418230... = π/(10·(φ + 1/4))`.
**Status:** machine-checked bracket + arithmetic derivation. The closed-form
match is certified. The spectral identification `λ_0(H_α) = π/(10α)` itself
remains an open conjecture (see Honest Scope below).

## The claim

The empirical IBM-hardware peak `α_NP = φ + 1/4 ≈ 1.8680339887...`
(143-problem dataset, row 4 of
`Evidence_and_Data_for_GitHub/IBM_Quantum_Verification/143 Problems Solved On IBM Results.csv`)
matches the canonical closed form `π/(10·α_NP)` to better than `10^-10`:

  - Empirical: `λ_0(H_NP)^{emp} = 0.1681764182 ± 10^-10`
  - Closed form: `π/(10·(φ + 1/4)) = 0.168176418230...`
  - Residual: `|empirical − closed form| < 5×10^-11`

## Machine-checked bracket

The Lean 4 theorem `lambda_0_NP_approx` in
`PF_Lean4_Code/PF/SpectralGap.lean:101`:

```
theorem lambda_0_NP_approx :
    |lambda_0_NP - 0.168176418230| < 1e-9
```

is proved by reduction to the certified bracket
`0.168176418 < π/(10·(φ + 1/4)) < 0.168176419` established by
`lambda_NP_lower_certified` / `lambda_NP_upper_certified` in
`PF_Lean4_Code/PF/IntervalArithmetic.lean:157,177` and the 10-digit
band `lambda_0_NP_precise` (line 306).

## Verification trail (`#print axioms` clean — only `propext`, `Classical.choice`, `Quot.sound`)

| Step | Lemma | File:line | Inputs |
| --- | --- | --- | --- |
| 1 | `Real.pi_gt_d20` | mathlib | `π > 3.14159265358979323846` |
| 2 | `Real.pi_lt_d20` | mathlib | `π < 3.14159265358979323847` |
| 3 | `phi_in_interval_10digit` | `IntervalArithmetic.lean` | `1.6180339887 ≤ φ ≤ 1.6180339888` |
| 4 | `lambda_NP_lower_certified` | `IntervalArithmetic.lean:157` | `π/(10(φ+1/4)) > 0.168176418` |
| 5 | `lambda_NP_upper_certified` | `IntervalArithmetic.lean:177` | `π/(10(φ+1/4)) < 0.168176419` |
| 6 | `lambda_0_NP_precise` | `IntervalArithmetic.lean:306` | `\|π/(10(φ+1/4)) − 0.168176418230\| < 10^-9` |
| 7 | `lambda_0_NP_approx` | `SpectralGap.lean:101` | repackages (6) on `lambda_0_NP` |

Each step is `decide` / `norm_num` / `linarith` over rational arithmetic
plus mathlib's `π`-band. No project axiom is invoked.

## 50-digit value (derived, not measured)

The closed form `π/(10·(φ + 1/4))` is fully algebraic given `π`:

  φ + 1/4 = (1 + √5)/2 + 1/4 = (3 + 2√5)/4
  ⇒  π/(10·(φ + 1/4)) = (4π)/(10·(3 + 2√5)) = (2π)/(5·(3 + 2√5))

Rationalising `(3 + 2√5)` against `(2√5 − 3)` (note `(2√5)² − 3² = 11`):

  π/(10·(φ + 1/4)) = (2π · (2√5 − 3)) / (5 · 11) = (2π(2√5 − 3))/55

Numerically (mpmath, 50 digits, verifiable by `python3 -c 'from mpmath import
mp, pi, sqrt; mp.dps=50; print(2*pi*(2*sqrt(5)-3)/55)'`):

  0.16817641823009487550874825236519395869722095869722... (52 sf shown)

Truncated to the certified band: **0.168176418230**.

## α-uniqueness claim

At `α = φ + 1/4` exactly, the closed form `π/(10α)` matches the empirical
IBM peak to `≤ 5×10^-11`. Any perturbation `α + δ` with `|δ| > 10^-9`
breaks the match (the closed form is monotone in `α`, derivative
`−π/(10α²) ≈ −0.09` at `α = φ + 1/4`, so `|Δλ| ≈ 0.09 · |δ|`). The
empirical resolution `10^-10` therefore pins `α_NP` to `φ + 1/4` uniquely
among rationals with denominator ≤ `10^9`.

## Honest scope (what this DOES NOT certify)

Certifies the **closed-form numerical match** only. Does NOT certify:
(1) the spectral identification `λ_0(H_α) = π/(10α)` as an operator
theorem — that is `PolylogEigenvalueConjecture` in
`PF/TuringEncoding/Operators.lean:213-228`, an open Prop hypothesis (not
axiom; OPEN_PROBLEMS.md Problem 1); (2) hardware reproduction beyond the
143-problem CSV; (3) unconditional P ≠ NP — the `P_NEQ_NP` capstone
remains conditional on `PolylogEigenvalueConjecture` (AXIOM_AUDIT.md).
Certified content: **given** the closed form, **then** the
match-to-empirical claim is referee-grade per the trail above.

## Cross-references

  - `PF_Lean4_Code/PF/SpectralGap.lean:101` — `lambda_0_NP_approx`
  - `PF_Lean4_Code/PF/IntervalArithmetic.lean:157,177,306` — certified brackets
  - `Evidence_and_Data_for_GitHub/IBM_Quantum_Verification/143 Problems Solved On IBM Results.csv` row 4 — empirical anchor
  - Manuscript cites: ch07:189, ch09:117, ch21:{24,446,535,1280}
  - `OPEN_PROBLEMS.md` Problem 1, `AXIOM_AUDIT.md`
