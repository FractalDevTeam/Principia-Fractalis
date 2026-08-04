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

## r189 — concrete instantiation on Gauss branch data (commit d778149e)

**File:** `PF/GaussTrace_r189.lean`, kernel-clean, 4696-job build.

The formula applied to the ACTUAL Mayer branches: `φ_j(z) = 1/(z+j)` with the
s = 1 Mayer weights `w_j(z) = 1/(z+j)²` (the Gauss–Kuzmin–Wirsing operator,
rational weights — no complex powers) on Mayer's disc `|z−1| ≤ 3/2`.

- **Geometry in the kernel** (`gaussBranch_mem`): every branch maps the circle
  `|z−1| = 3/2` into `|w−1| ≤ 1`, via the inversion estimate
  `‖z+j−1‖ ≤ ‖z+j‖` from `Re z ≥ −1/2` (normSq comparison + nlinarith).
  Constants: τ = 1 < R = 5/4 < R₁ = 3/2, W = 4.
- **Fixed points** = the noble continued fractions
  `x_j = (√(j²+4) − j)/2 = [0; j,j,j,…]`; factorization is exact rational
  algebra `z − 1/(z+j) = (z − x_j)(z + j + x_j)/(z+j)` (linear_combination
  from `x² + jx = 1`).
- **`gauss_trace`**: for every depth K,
  `Σ'_m A[m,m] = Σ_{j=1}^K x_j²/(1 + x_j²)`
  (since `x_j + j = 1/x_j` gives `w_j(x_j) = x_j²`, `φ_j'(x_j) = −x_j²`).
- **`gauss_trace_one`** (the golden case): K = 1, x₁ = 1/φ,
  `trace = (5 − √5)/10 = 0.27639320225…` — a closed-form, kernel-checked
  trace of a GKW transfer matrix.

**Numerical cross-check** (mpmath, dps 30): direct contour integral vs the
residue sum agrees to 2e-20 at K = 1, 3, 5; the golden closed form to 5e-32.

Scope: depth-K TRUNCATED systems (the RH_MOBIUS3 finite Möbius systems).
The full Mayer operator (infinitely many branches, complex exponent 2s) is
not formalized; s = 1 was chosen precisely because the weights are rational.

New frictions: `div_inv_eq_mul` (not `div_inv_eq`); `div_eq_div_iff` takes
`≠ 0` arguments at this pin; `HasDerivAt.inv` yields the Pi-inverse form
`(fun z => …)⁻¹` — bridge with an explicitly-typed `have` before `.deriv`.

## r190 — complex-s Mayer weights: the full Mayer trace (commit f92f4c73)

**File:** `PF/MayerTrace_r190.lean`, kernel-clean, 4697-job build. Date 2026-08-04.

- **`mayer_trace`**: for EVERY s : ℂ and depth K,
  `Σ'_m A[m,m](s) = Σ_{j=1}^K x_j^{2s}/(1 + x_j²)` — the actual Mayer weights
  `(z+j)^(−2s)`, principal branch. The branch cut never matters: on the disc
  `Re(z+j) ≥ 1/2` (slit-plane condition, kernel-checked). The uniform weight
  bound comes from compactness of the circle (`exists_uniform_bound`) — zero
  cpow norm estimates in the main theorem.
- **`summable_mayerTerm`**: Mayer's classical convergence threshold
  **Re s > 1/2 is DERIVED in the kernel**: ‖x_j^{2s}/(1+x_j²)‖ ≤ x_j^{2σ} ≤
  (j+1)^{−2σ} (using `x_j ≤ 1/j`, `gaussFix_le_inv`), a p-series.
- **`tendsto_mayer_trace`**: the truncated kernel traces converge to
  `mayerTrace s := Σ'_j x_{j+1}^{2s}/(1+x_{j+1}²)` — **the full Mayer trace
  realized as a limit of kernel theorems**.
- **`mayer_trace_one_golden`**: s=1, K=1 reproduces (5−√5)/10 through the
  cpow→pow bridge (consistency with r189).

**Numerics** (mpmath dps 30–40): contour vs residues ≤ 8e-14 at complex s
including s = 1/4 + 7.0673625987i (the first-Riemann-zero point on Mayer's
line Re s = 1/4... note: zero at s = ρ/2) and at Re s < 0 (truncated identity
holds for all s; only the K→∞ limit needs σ > 1/2). mayerTrace(1) =
0.7711255236556589 — the classical GKW trace. Tail ~ 1/K as the p-series
bound predicts.

Scope: the infinite-branch OPERATOR L_s is not constructed; `mayerTrace` is
the limit of truncated traces (= what the classical residue trace formula
evaluates Tr L_s to). Nuclearity/Lidskii for the infinite system stays open.
No Selberg/RH claims.

New frictions: ℝ≥0 notation needs `open scoped NNReal` (repeat offender);
`div_le_div_iff` gone at pin — use `le_div_iff₀` + linarith with
`(2:ℝ)/a = 2*(1/a)` bridge; `Summable.of_norm_bounded` takes (hg, h) with g
IMPLICIT at this pin; `Finset.le_sup` under exact_mod_cast needs explicit
`(f := …)`.

## r191 — traces of powers L^n: the n-cycle Lefschetz formula (commit d7c098cf)

**File:** `PF/TransferPower_r191.lean`, kernel-clean, 4698-job build. 2026-08-04.

The n-th power of a transfer operator is itself a weighted composition
system over the K^n words: branches compose (`listBranch`), weights are
Birkhoff products (`listWeight`). The stone proves **closure of the
r186/r188 hypothesis class under composition** — by list induction:
- `listBranch_cons_mem_tau`: nonempty compositions contract into the τ-ball
  (base hypothesis strengthened from sphere to closedBall);
- `norm_listWeight_le`: ‖W_α‖ ≤ W^{|α|};
- `differentiableAt_listBranch/listWeight`: holomorphy composes;
- `deriv_listBranch_cons`: the chain-rule step Φ'_{k::l}(z) = Φ'_l(φ_k z)·φ'_k(z).

**`trace_pow_eq_residues`**: Σ'_m A⁽ⁿ⁾[m,m] = Σ_{|α|=n} W_α(x_α)/(1 − Φ_α'(x_α))
— the sum over n-periodic points. These are the periodic-orbit sums from
which det(1∓L_s) and the Selberg-zeta factorization are classically built.

**Witness `gauss_square_trace`**: squared golden branch (K=1, n=2):
trace of L² = x⁴/(1−x⁴) = **(3√5−5)/10** — kernel-checked closed form
(linear_combination coefficient (3S³−7S²+13S−17)/16 against S²=5,
precomputed by sympy).

**Numerics**: contour vs periodic residues ≤ 1e-29 at (K,n) ∈
{(1,2),(2,2),(2,3),(3,2)}; witness to 5e-32.

**Scope — NOT claimed**: A⁽ⁿ⁾ = Aⁿ as matrix powers (the operator
composition property; needs coefficientwise composition of Cauchy
expansions — the natural next stone if the determinant road is pursued).
No determinants, no zeta, no RH.

New frictions: pattern-matching defs (`listBranch`) don't beta-reduce under
`rw` of the list argument — add `@[simp]` rfl-equation lemmas and
`simp only` them; for words over `Fin 1` use `Subsingleton.elim` to
`fun _ => 0` then `decide` for the concrete `List.ofFn` value;
`linear_combination` residuals that factor as (poly)·(identity) mean the
coefficient was off by that poly — recompute, don't stack terms.

## r192 — A⁽ⁿ⁾ = Aⁿ: the transfer matrix is a semigroup (commit c908382f)

**File:** `PF/TransferCompose_r192.lean`, kernel-clean, 4699-job build. 2026-08-04.

- **`coeff_comp`** (analytic core): if `H(y) = Σ'_p b_p((y−c)/R)^p` on the
  contraction ball with `‖b_p‖ ≤ C(R/R₁)^p`, the m-th Cauchy coefficient of
  `z ↦ Σ_k w_k(z)H(φ_k z)` is `Σ'_p A[m,p]b_p` — extraction commutes with
  the series (dominated interchange, bound (R/R₁)^p(τ/R)^p = (τ/R₁)^p).
- **`hasSum_transferMatrix_series`** (Taylor bridge): the image functions
  of a holomorphic system are their own coefficient series on the disc
  (DiffContOnCl.hasFPowerSeriesOnBall; cauchyPowerSeries = mkPiRing so
  constant-vector evaluation is the monomial series).
- **`transferMatrix_pow`**: A⁽ⁿ⁺¹⁾ = matPowPos A n — the word-system matrix
  IS the honest ℓ²-matrix power.  Induction: word regrouping
  (finFunctionFinEquiv → Fin.consEquiv → Fintype.sum_prod_type → ofFn_cons),
  base geometry closed under composition (r191), inner-matrix column decay
  from geomBound (r186).
- **`trace_matPow_eq_residues`** (capstone): Σ'_m (Aⁿ⁺¹)[m,m] =
  Σ_{|α|=n+1} W_α(x_α)/(1−Φ_α'(x_α)).  The periodic orbits compute the
  traces of every power of ONE matrix.

**Numerics**: A⁽²⁾ vs A·A for the Gauss K=2 system — discrepancy is pure
ℓ²-truncation tail: 2e-8 at 16 product terms → 1.4e-20 at 60, geometric
rate (2/3)^p = (R/R₁)(τ/R), exactly as GeomBound predicts.

**Where the road now stands** (the honest map):
Tr(Aⁿ) for all n ≥ 1 = periodic-orbit sums, kernel-checked.  These are the
complete inputs of det(1−tA) = exp(−Σ_n tⁿ·Tr(Aⁿ)/n) — Ruelle's dynamical
zeta / the truncated Mayer determinants det(1∓L_s) whose zeros carry the
Maass spectrum and (Lewis–Zagier, even factor) the Riemann zeros at s=ρ/2,
as validated numerically at 7–8 digits in RH_M1/M2.  Next stone(s): the
determinant assembly — exp/log convergence in t (needs Σ_n |Tr Aⁿ|/n·|t|ⁿ < ∞
from the geometric trace bounds, all in hand), then the truncated
det(1∓L_s) as kernel objects with certified truncation error.  What that
road does NOT reach by itself: infinite-branch operators (nuclearity),
Lidskii (spectral trace = matrix trace), Selberg theory, or RH.  Realistic
deliverable: the first kernel-checked dynamical-determinant framework +
a formalization paper; the Mayer numerics get a verified analytic backbone.

New frictions: ℝ≥0∞ notation strikes again (open scoped ENNReal);
`x |>.mpr` after applied args is a parse error — parenthesize;
`DifferentiableAt.sum` wants Finset-sum-of-functions — funext-split the
lambda first (Finset.sum_apply); `Fintype.sum_equiv` with `_ _` stalls
typeclass search (AddCommMonoid ?m) — always pass f and g explicitly;
`congr 1` on `a :: l = b :: l'` auto-discharges rfl heads (bullets shift);
field_simp/simp closing goals leaves dangling tactics — trim after compile.
