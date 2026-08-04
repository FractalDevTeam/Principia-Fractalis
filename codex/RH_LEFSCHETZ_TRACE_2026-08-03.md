# The Holomorphic Lefschetz Trace Formula — CLOSED (r188/r188b/r188c)

**Date:** 2026-08-03
**Commits:** `c4431fe7` (r188 foundations), `ba2a9d19` (r188b assembly), `4a762ef0` (r188c residues)
**Files:** `PF/TransferTrace_r188.lean`, `PF/TransferResidue_r188c.lean`
**Build:** `lake build PF` green, 4695 jobs. All theorems on
`[propext, Classical.choice, Quot.sound]`. No `sorry`, no `native_decide`,
no project axioms. Non-vacuity witness compiled through the main theorem.

## The theorem

For the transfer matrix of a weighted composition system
(K branches, weights `w_k`, branches `φ_k`, disc-normalized basis scale `R`,
contour radius `R₁`, contraction radius `τ`, with `0 ≤ τ < R < R₁`):

**r188b (`trace_eq_contour`)** — geometry only (continuity on the circle +
contraction into `closedBall c τ`):

    Σ'_m A[m,m]  =  (2πi)⁻¹ ∮_{|z−c|=R₁}  Σ_k w_k(z)/(z − φ_k(z)) dz

**r188c (`trace_eq_residues`)** — adding holomorphy inside the disc
(`DiffContOnCl`) and the simple-zero factorization
`z − φ_k(z) = (z − x_k)·g_k(z)`, `g_k` holomorphic nonvanishing:

    Σ'_m A[m,m]  =  Σ_k  w_k(x_k) / (1 − φ_k'(x_k))

This is the holomorphic Lefschetz fixed-point formula for transfer operators —
the identity the Mayer/Ruelle program and ch24's trace–rank mechanism
(BSD_TRACE_RANK_2026-08-03.md: rank as trace slope, measured
+0.780/+1.473/+2.168 for ranks 1/2/3) both stand on. The numerically measured
regularized traces now have a kernel-checked structural identity behind them.

## Proof route (what a referee will check)

1. **Diagonal entry as contour** (`diag_eq_contour`): `cauchyPowerSeries_apply`
   at the constant argument 1; the basis scale `R^m` cancels the `/R^m` in the
   image expansion exactly — the trace is scale-free.
2. **Interchange** (`intervalIntegral_tsum`, r188 stone 1): dominated
   convergence for tsum against interval integrals — bound
   `K·W·(τ/R₁)^m`, geometric. mathlib has no such lemma at the pin; built from
   `MeasureTheory.integral_tsum` + continuity.
3. **Pointwise resummation** (`tsum_diagIntegrand`): geometric series
   `Σ_m q_k^m = (z−c)/(z−φ_k z)` per branch (`tsum_ratio_pow`), finite/infinite
   sum swap via `Summable.tsum_finsetSum`.
4. **Residues** (`contour_eq_residue_single`): Cauchy integral formula
   (`two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`,
   s = ∅) applied to `w·g⁻¹`; the factorization hypothesis is the honest
   interface for "x is the unique simple zero of z − φ(z)".
5. **Cofactor** (`cofactor_eq_one_sub_deriv`): differentiate the factorization
   at the fixed point: `g(x) = 1 − φ'(x)`.

## Scope — what is and is not claimed

- PROVED: the trace formula for any system satisfying the stated geometry +
  holomorphy + factorization hypotheses. Fully generic (`c R R₁ τ W K w φ` free).
- The factorization is a hypothesis, not derived from contraction alone
  (deriving it needs the argument principle / Rouché; mathlib has the machinery
  but that is a separate stone if ever needed — for PF branches it is checkable
  by explicit division).
- NOT claimed: nuclearity, trace-class identification of Σ|A[m,m]|-type
  operator traces with spectral traces (Lidskii), or anything about ζ zeros.
  The chain r183–r186 gives compactness; Lidskii is not at the pin.

## Lean frictions (new entries for the ledger)

- `tsum_sum` deprecated → `Summable.tsum_finsetSum` (the alias resolves to a
  Sum-type lemma and fails unification — use the full name).
- `congr 1` on `a * Σ = a' * Σ'` splits the product, not the sum: use
  `apply Finset.sum_congr rfl` after peeling constants with `Finset.mul_sum`.
- `field_simp` stalls on symbolic powers `(x/y)^m`: finish with an explicit
  `mul_pow`-combine (`show ... from by rw [mul_pow, mul_pow]; ring`) then
  `mul_div_mul_left`.
- Eta-contracted `Continuous (deriv (circleMap c R))`: `simp only
  [deriv_circleMap]` makes no progress; use
  `((continuous_circleMap 0 R).mul continuous_const).congr fun θ =>
  (deriv_circleMap c R θ).symm`.
- `circleIntegral.integral_congr` hands you `z ∈ sphere c |R|`: convert with
  `simpa [abs_of_pos hR]`.
- Under `intervalIntegral.integral_congr` the pointwise goal arrives
  un-beta-reduced: `dsimp only` before any `rw`.
- Cauchy formula lives in namespace `Complex`; needs
  `import Mathlib.Analysis.Complex.CauchyIntegral` (NOT pulled in by the
  circle-integral or power-series files).

## Next

- mathlib candidate #5: extract the trace chain (esp. `intervalIntegral_tsum`
  and `trace_eq_contour`) into `mathlib_candidates/` generic form.
- Application stone: instantiate `trace_eq_residues` on a concrete PF system
  (Mayer-type branch family or the ch24 elliptic weights) — connects the
  kernel identity to the bsd_trace_rank.py measurements.
