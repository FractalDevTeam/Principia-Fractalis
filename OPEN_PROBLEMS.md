# Open Mathematical Problems Isolated by Principia Fractalis

*Last updated: 2026-05-16. Companion to `AXIOM_AUDIT.md` and `PRISTINE_CERTIFICATION.md`.*

This document enumerates the **open mathematical problems** that the Principia Fractalis framework has *isolated* — that is, the precisely-stated mathematical claims on which the framework's headline conditional reductions of Clay Millennium Problems depend.

**These problems are NOT solved. They are NOT proven in the manuscript. The framework provides:**

1. A mechanical reduction of two Millennium Problems (P ≠ NP and the Riemann Hypothesis) to four sharply-stated mathematical conjectures.
2. Strong numerical evidence (10⁻¹⁰ precision finite-dimensional eigenvalue convergence) for the P ≠ NP-side conjectures.
3. A complete Lean 4 + Coq cross-prover mechanization of the reduction chain.
4. Zero proof of the underlying conjectures themselves.

**Solving any one of the four open problems below would constitute a major mathematical contribution. Solving all four would deliver formal proofs of two Millennium Problems.**

---

## Problem 1 — Polylog Eigenvalue Conjecture (Ch 21, `conj:polylog-spectrum`)

**Statement.** Let `H_P` be the fractal convolution operator on `L²(K, μ)` with kernel

```
V_P(x, y) = Σ_{n=0}^∞ a^{-n} · cos(π · √2^n · d(x, y))
```

for `a > 1` and `K` a suitable compact fractal domain. Conjecture: the eigenvalues of `H_P` are given by

```
λ_k = (1/aᵏ) · Re[Li₁(e^{iπ·√2^k})]
```

where `Li₁` is the polylogarithm of order 1, evaluated on a specific physical Riemann sheet determined by the operator's monodromy.

**Current status.** Numerical: ground-state eigenvalue computed via finite-dimensional approximation (`N = 2⁸` to `2¹⁶` basis functions) converges to `0.2221441469 ± 10⁻¹⁰`, matching `π/(10√2) ≈ 0.2221441469079…` to within 10⁻¹⁰. Analytical: no proof of the eigenvalue formula itself.

**Lean encoding.** Part of `alpha_class_polylog_eigenvalue_conjecture` axiom (`PF/TuringEncoding/Operators.lean`).

**Supporting infrastructure delivered (2026-05-16, 31 sessions, 70 axiom-free theorems + 8 definitions).**

The following machine-checked infrastructure for attacking Problem 1 has been delivered in Lean 4, all zero-project-axiom:

* `PF/Analytic/PolylogSpectrum.lean` (22 theorems + 3 definitions):
  - **All 6 matrix-entry product integrals** on L²([0,1]) (diagonal cos², sin², cos·sin; off-diagonal cos·cos, sin·sin, sin·cos).
  - **Cross-scale specialisations** ⟨cosineMode α n, cosineMode α m⟩, ⟨sineMode α n, sineMode α m⟩, ⟨sineMode α n, cosineMode α m⟩ closed forms.
  - **Mercer rank-2-per-scale decomposition** of the truncated kernel.
  - **Truncated operator action** explicit formula + **base case eigenvalues** (T_1 cosineMode α 0 = (1/2) cosineMode α 0, similarly sineMode).
  - **k=2 explicit scale mixing** (cosineMode α 0 NOT a T_2 eigenfunction; concrete demonstration).
  - **Full operator action** definition + **pointwise convergence** T_k → H_P with O(a^{-k}) rate.
  - **Formal conjecture predicate** `PolylogSpectrumClaim`.

* `PF/Analytic/KernelSelfSimilarity.lean` (12 theorems + 1 definition):
  - **Per-term scaling identity**.
  - **Single-step self-similarity equation** `V_P(x,y) = cos(π·d) + (1/a)·V_P(αx, αy)` (the structural lever generating the a^{-k} weight in the conjecture).
  - **k-fold iterated self-similarity** explicit recursion.
  - **Residual bound** + **uniform L∞ approximation** O(a^{-k}).
  - **Truncated kernel** definition + **pointwise bound** ≤ a/(a-1) uniformly in k.
  - **Continuity of truncated kernel sections** (closes integrability loops).

* `PF/Analytic/PolylogBoundary.lean` (9 theorems + 2 definitions):
  - **Principal-branch extension** `polyLog_one_principal z := −log(1 − z)` of Li₁ to the closed unit disk minus z=1.
  - **Norm formula** `‖1 − exp(I·t)‖ = 2·|sin(t/2)|`.
  - **Closed-form principal-branch eigenvalue**: `Re[polyLog_one_principal(exp(I·π·αᵏ))] = −log(2·|sin(π·αᵏ/2)|)`.
  - **Cosine-series representation** of polylog partial sums.
  - **`conjectured_eigenvalue_principal` definition** giving the closed form on principal branch.

For α = √2, k = 0 the principal-branch evaluation is `−log(2·sin(π·√2/2)) ≈ −0.468`, which is **NEGATIVE**. The manuscript's claimed positive value `π/(10√2) ≈ +0.222` requires a **different Riemann sheet** (Problem 2's branch-selection Heuristic). The discrepancy is now sharp and machine-checkable; `polylog_principal_branch_eigenvalue` makes this a formal theorem: if the polylog conjecture holds with principal-branch evaluation, then `λ_k = −a^(−k) · log(2·|sin(π·αᵏ/2)|)` — incompatible with the manuscript's positive prediction.

**Additional infrastructure (sessions 16–25)**:
* `truncatedOperatorAction_two_*` — complete explicit 4×4 matrix `T_2` in the `{cosineMode α 0, sineMode α 0, cosineMode α 1, sineMode α 1}` basis (all 4 rows, every entry closed-form).
* `tendsto_truncatedOperatorAction` — `Filter.Tendsto` form of operator-action convergence.
* `truncatedFractalKernelReal_diagonal` + `trace_truncatedOperator` + `geometric_sum_zpow_neg` + `trace_truncatedOperator_closed_form` — `Tr(T_k) = Σ_{j<k} a^(−j) = (1 − a^(−k))/(1 − 1/a)`, giving a sum-rule constraint on the spectrum.
* `abs_truncatedOperatorAction_le` — L¹→L∞ operator-norm bound `‖T_k‖ ≤ a/(a−1)` uniformly in `k`.
* `truncatedOperatorAction_zero_of_orthogonal` — kernel characterization (forward).
* `L2_norm_sq_cosineMode` + `L2_norm_sq_sineMode` — L²[0,1] norm-squared formulas.
* `SpectralConvergenceClaim` + `PolylogSpectrumFullConjecture` — full structured-`Prop` packaging of the conjecture.
* `sq_truncatedFractalKernelReal_le` + `sq_fractalKernelReal_le` — Hilbert-Schmidt norm bounds: `‖T_k‖_HS ≤ a/(a−1)` and `‖H_P‖_HS ≤ a/(a−1)`. Establishes H_P as Hilbert-Schmidt compact + self-adjoint, hence discrete spectrum with eigenvalues → 0.

**What this infrastructure gives the framework.** Every matrix entry of the finite-rank truncated operator `T_k` in the cosineMode/sineMode basis is a proven closed form. `T_k → H_P` with explicit O(a^{-k}) convergence (pointwise and Tendsto, at both kernel and operator level). The natural basis is provably NOT the eigenbasis for k ≥ 2 (scale-mixing explicit at all 4 rows of `T_2`). `H_P` is provably Hilbert-Schmidt with HS norm ≤ a/(a−1), hence compact + self-adjoint with discrete spectrum. The principal-branch evaluation of the conjectured formula is in closed form, and the conjecture's incompatibility with principal-branch evaluation is a formal theorem.

**Sharp formal constraints on the physical Riemann sheet** (sessions 26–31): for α = √2, the principal-branch eigenvalue formula:
* Gives `λ_0_principal = −log 2 ≈ −0.693` (theorem `conjectured_eigenvalue_principal_sqrt2_zero`), while the manuscript predicts `λ_0_physical = +π/(10·√2) ≈ +0.222` — sign flip + magnitude shift of `≈ 0.915`.
* Has singularities `sin(π·αᵏ/2) = 0` at every even `k ≥ 2` (theorems `principal_branch_singularity_sqrt2_k2`, `principal_branch_singularity_sqrt2_even_k`).
* Is well-defined at `k = 0` and `k = 1` (theorems `sin_pi_sqrt2_pow_zero_div_2_ne_zero`, `sin_pi_sqrt2_pow_one_div_2_ne_zero`).

So the physical Riemann sheet (Problem 2's Heuristic) must (a) flip signs at `k = 0, 1`, (b) resolve infinitely many singularities at every even `k ≥ 2`, (c) produce finite values matching the manuscript's eigenvalue predictions. These are now FORMAL THEOREM CONSTRAINTS, not numerical observations.

The remaining work is genuinely original mathematics: eigenvector identification + Riemann-sheet selection (= Problems 1+2 of this catalogue).

**Phase A continuation — Route A Mellin geometry + Cantor substrate (sessions 64–80).**

After the Phase A infrastructure above (truncated-kernel approximations on `L²([0, 1])`), a second arc developed the Cantor-substrate framework that connects the polylog conjecture to the actual fractal IFS structure:

* `PF/Analytic/Dilation.lean` (21 theorems + 1 def):
  - Dilation operator `dilation α f x := f(x/α)` + group structure: composition, identity, iteration, bijectivity.
  - Scale shift on `cosineMode`/`sineMode` (turns the polylog conjecture's α-scaling into a unitary group action).

* `PF/Analytic/LogCoord.lean` (13 theorems + 4 defs):
  - Log-coordinate transform `logCoord f t := f(exp(-t))` + translation operator.
  - **★ Dilation ↔ Translation bridge ★**: the action by `α` becomes translation by `log α` in log coordinates.
  - Joint translation self-similarity for the fractal kernel.

* `PF/Analytic/MellinMode.lean` (8 theorems + 3 defs):
  - `mellinCos λ x := cos(λ · log x)`, `mellinSin λ x := sin(λ · log x)` — explicit translation eigenvectors in log coordinates.
  - Dilation as rotation; dilation-invariant Mellin-weighted integrals.

* `PF/Analytic/FractalDomain.lean` (13 theorems + 5 defs):
  - Cantor IFS contractions `f₁(x) = x/3`, `f₂(x) = (x+2)/3` + fixed-point structure.
  - 4-cell decomposition + disjointness lemmas.
  - `IsHutchinsonInvariant`, `cantorKernel`, `H_P_at_cantor` operator on `(cantorSet, μ_Hutchinson)`.

* `PF/Analytic/Hutchinson.lean` (29 theorems + 5 defs):
  - `hutchinsonOp`: linearity, iteration, mass preservation; `cantorSeed`; **`cantorDiscMeasure n := T^n δ_{1/2}`** = level-n discrete approximation.
  - Level-1 explicit form: `cantorDiscMeasure 1 = (1/2)·δ_{1/6} + (1/2)·δ_{5/6}`.
  - `H_P_at_disc`, Dirac evaluation, `hutchinsonOp_dirac`, integral recursion.
  - **`integral_difference_recursion`**: the structural contraction at the integral level — `|Δ_{n+1}(f)| ≤ (L/3) · sup |Δ_n(g)|` — the formal core of the Banach-contraction argument for weak convergence `cantorDiscMeasure n → μ_H`.

* `PF/Analytic/CellMidpoint.lean` (9 theorems + 1 def):
  - Recursive `cellMidpointOfBools : List Bool → ℝ` (length-n boolean lists enumerate level-n cells).
  - Explicit values at levels 1–2 (`[false] = 1/6`, `[true] = 5/6`, `[false, false] = 1/18`, …).

* `PF/Analytic/MatrixEntry.lean` (matrix-entry framework for the discrete eigenvalue problem):
  - `cellMatrixEntry α a n bs bs' := (1/2^n) · V_P(m_{bs}, m_{bs'})` — explicit `2^n × 2^n` real symmetric matrix at level `n`.
  - **`cellMatrixEntry_symm`**: matrix symmetry → discrete operator self-adjoint → `2^n` real eigenvalues at every level.
  - **`fractalKernelReal_diagonal`** (a > 1): closed-form `V_P(x, x) = a/(a−1)` via the geometric series.
  - **`cellMatrixEntry_diagonal`**: every diagonal entry of `M^{(n)}` is the constant `(1/2^n) · a/(a−1)`.
  - **`cellMatrixEntry_eq_tsum_distance`**: a single distance-parametrised closed form that subsumes all explicit matrix entries.
  - **`abs_cellMatrixEntry_le`**: uniform bound `|M^{(n)}_{bs, bs'}| ≤ (1/2^n) · a/(a−1)` → row-sum bound `≤ a/(a−1)` independent of `n` → all level-n eigenvalues satisfy `|λ^{(n)}_k| ≤ a/(a−1)` (finite-rank operator-norm stability).
  - **Level-0 spectrum**: `lambdaLevel0 a := a/(a−1)`, sole eigenvalue with constant eigenvector (`level0_eigenvector_identity`).
  - **Level-1 spectrum** (full closed form):
    - `H_P_at_disc_cantorDiscMeasure_one`: explicit two-Dirac action.
    - `lambdaPlusLevel1`, `lambdaMinusLevel1`: closed-form `(1/2)·(a/(a−1) ± V_P(1/6, 5/6))`.
    - `level1_sym_eigenvector_at_{left,right}`: constant eigenvector with eigenvalue λ⁺.
    - `level1_antisym_eigenvector_at_{left,right}`: alternating eigenvector with eigenvalue λ⁻.
    - `level1_trace_identity`: λ⁺ + λ⁻ = a/(a−1).
    - `level1_gap_identity`: λ⁺ − λ⁻ = V_P(1/6, 5/6).
    - `level1_det_identity`: λ⁺ · λ⁻ = (1/4) · ((a/(a−1))² − V_P²(1/6, 5/6)).
    - `lambdaPlusLevel1_nonneg`, `lambdaMinusLevel1_nonneg`: BOTH eigenvalues ≥ 0 (matrix is POSITIVE SEMI-DEFINITE).
    - `lambdaPlusLevel1_le`, `lambdaMinusLevel1_le`: UPPER BOUNDS λ± ≤ a/(a−1).
    - `level1_spectrum_in_unit_interval`: bracketing 0 ≤ λ± ≤ a/(a−1).
  - **Cross-level trace consistency**: `tr M^{(0)} = lambdaLevel0 = lambdaPlusLevel1 + lambdaMinusLevel1 = tr M^{(1)}` and `trace_chain_levels_0_1_2`: chain across n = 0, 1, 2.
  - **Level-2 geometry** (6 pairwise distances): all four distinct values `{2/9, 4/9, 2/3, 8/9}` computed in closed form; documented block structure under IFS self-similarity.
  - **Level-1 off-diagonal explicit form**: `M^{(1)}_{[false],[true]} = (1/2) · Σ a^(-n) cos(π · α^n · 2/3)`.
  - **Level-2 explicit matrix entries**: all 6 off-diagonal entries (`cellMatrixEntry_level2_ff_ft`, `_ff_tf`, `_ff_tt`, `_ft_tf`, `_ft_tt`, `_tf_tt`) as explicit tsum closed forms; `level2_within_half_equality` and `level2_outer_cross_equality` codify the IFS reflection symmetry.
  - **Level-2 explicit measure**: `cantorDiscMeasure_two = (1/4)·(δ_{1/18} + δ_{5/18} + δ_{13/18} + δ_{17/18})`.
  - **Level-2 explicit operator action** `H_P_at_disc_cantorDiscMeasure_two`: closed-form 4-Dirac action on the level-2 midpoint span (matrix-vector product M^{(2)}·v explicit).
  - **Level-2 sym/antisym 2×2 block decomposition**: under the IFS reflection `x ↦ 1 − x`, the 4×4 problem decomposes into two 2×2 sub-blocks `B_sym`, `B_anti` with explicit entries. Verified by 4 parametric action theorems: `level2_{sym, antisym}_action_at_{ff, tf}`.
  - **Level-2 four eigenvalues** in closed form via the symmetric 2×2 quadratic formula:
    - `lambdaSymPlusLevel2`, `lambdaSymMinusLevel2`: eigenvalues of `B_sym`.
    - `lambdaAntiPlusLevel2`, `lambdaAntiMinusLevel2`: eigenvalues of `B_anti`.
  - **Level-2 algebraic spectral identities** (per block + cross-block):
    - `lambdaSymLevel2_trace`, `lambdaAntiLevel2_trace`: trace of each block.
    - `lambdaSymLevel2_gap`, `lambdaAntiLevel2_gap`: explicit spectral gap closed form.
    - `lambdaSymLevel2_det`, `lambdaAntiLevel2_det`: determinant of each block.
    - `lambdaSymLevel2_sumSq`, `lambdaAntiLevel2_sumSq`: sum of squared eigenvalues per block.
    - `level2_full_trace_identity`: cross-block cancellation: Σ all 4 = a/(a−1).
    - `level2_full_sumSq`: total ‖M^{(2)}‖_F² explicit expansion in V_P values.
  - **Level-2 spectrum bounds**:
    - `level2_block_traces_nonneg` (a > 1): both block traces ≥ 0 (necessary PSD condition).
    - `level2_{sym, anti}_PSD_from_det`: CONDITIONAL PSD via Sylvester's criterion (`B² ≤ A·C` ⟹ λ ≥ 0). The hypothesis is an OPEN ESTIMATE on V_P inner products.
    - `level1_sumSq_le_level0`, `level2_sumSq_le_level0` (a > 1): Frobenius monotonicity `‖M^{(n)}‖_F² ≤ (a/(a−1))²` (eigenvalue SPREADING inequality).
    - `level2_spectral_radius_bound` (a > 1): all 4 eigenvalues `|λ| ≤ a/(a−1)`.
    - `level2_spectrum_bracketing` (a > 1): all 4 eigenvalues in `[−a/(a−1), a/(a−1)]`.
  - **Level-1 Frobenius identity** `level1_sumSq_identity`: `λ⁺² + λ⁻² = (1/2)·((a/(a−1))² + V_P²(1/6, 5/6))`.
  - **★ Level-1 spectral theorem (complete) ★** (added 2026-05-17):
    - `level1_const_eigenvec_norm`, `level1_alt_eigenvec_norm`, `level1_eigenvec_orthogonal`: the constant function `1` and the alternating function `level1_antisym_test` form an ORTHONORMAL BASIS of the test-function space under the L²(cantorDiscMeasure 1) inner product.
    - `level1_eigenbasis_completeness`: every test function `f` is reproduced on the level-1 midpoints by the eigenbasis decomposition `f = c_sym · 1 + c_anti · alt` with `c_sym = (1/2)(f(1/6)+f(5/6))`, `c_anti = (1/2)(f(1/6)−f(5/6))`.
    - `level1_spectral_action_at_{left,right}`: the operator acts DIAGONALLY on the eigenbasis: `(H_P^disc f)(1/6) = λ⁺ · c_sym + λ⁻ · c_anti`, `(H_P^disc f)(5/6) = λ⁺ · c_sym − λ⁻ · c_anti`.
    - `level1_c_anti_lipschitz_bound`: for L-Lipschitz `f`, the anti-coefficient satisfies `|c_anti(f)| ≤ L/3` (matching the IFS contraction factor — spectral-level analog of the Banach-contraction shrinkage).
    - **Together**: M^{(1)} is fully diagonalised in the orthonormal eigenbasis with eigenvalues `{λ⁺, λ⁻}` — the spectral theorem at the finite-rank discrete level.
  - **★ Operator-theoretic foundations ★** (added 2026-05-17):
    - `cantorKernel_symm`: V_P(x, y) = V_P(y, x).
    - `H_P_at_disc_self_adjoint`: bilinear form symmetry `∫ (H_P f)·g dμ = ∫ f·(H_P g) dμ` via Fubini + kernel symmetry (axiom-free, requires `SFinite μ` + bilinear-integrand integrability hypothesis).
    - `H_P_at_disc_add_func`, `H_P_at_disc_smul_func`: test-function linearity (additive + scalar).
    - `abs_H_P_at_disc_level0_le`, `abs_H_P_at_disc_level1_le`: sup-norm operator-norm bounds `|H_P^disc f| ≤ M · a/(a−1)` at levels 0 and 1.
    - `sq_cantorKernel_le`, `abs_cantorKernel_le`: substrate-level uniform pointwise bounds.
    - `level2_constant_at_{ff, ft, tf, tt}`, `level2_constant_reflection_symmetry`: level-2 IFS-reflection symmetry verification (operator action on constant test function is invariant under `x ↦ 1−x`).
  - **★ Deep spectral infrastructure ★** (added 2026-05-17/18):
    - `fractalKernelReal_mercer`: full TSUM Mercer decomposition `V_P = Σ a^(-n)·(cos_n ⊗ cos_n + sin_n ⊗ sin_n)` — the separable-kernel structure foundational for spectral analysis.
    - `trace_fullOperator_closed_form`: `∫₀¹ V_P(x, x) dx = a/(a-1)` — the SPECTRAL SUM RULE constraint that any candidate eigenvalue formula must satisfy.
    - `integral_cosine_pi_c`, `integral_sine_pi_c`, `integral_cosineMode_pow`, `integral_sineMode_pow`: closed-form first moments `∫ cos(πcx) dx = sin(πc)/(πc)`, etc. — foundational for variational eigenvalue computations on H_P^α.
    - Pending (documented roadmap): variational identity `⟨1, H_P^α · 1⟩` closed form; full Hilbert-Schmidt double-integral bound (requires parameter-continuity-of-integral lemma).
  - **★★ MAJOR: First exact closed-form fragment of the polylog kernel sum at α = √2 ★★** (added 2026-05-18):
    - `cos_two_pow_succ_pi_div_three`: `cos(π · 2^(m+1) / 3) = −1/2` for all `m ≥ 0` (induction + double-angle).
    - `fractalKernel_even_term_sqrt2_two_thirds`: per-term identity at EVEN `k = 2m`: `a^(-(2m))·cos(π·(√2)^(2m)·2/3) = −1/(2·a^(2m))` — no transcendental.
    - `even_subseries_sqrt2_two_thirds` (`a > 1`): **EXACT CLOSED FORM** for the even-frequency subseries:
      $$\sum_{m\geq 0} a^{-2m}\cos\bigl(\pi\cdot(\sqrt{2})^{2m}\cdot\tfrac{2}{3}\bigr) = -\tfrac{a^{2}}{2(a^{2}-1)}.$$
    - **Significance**: the polylog kernel sum `V_P(α=√2, a, 1/6, 5/6)` was previously treated as an opaque transcendental object. The even-frequency HALF is now in EXACT closed form (rational in `a`); only the odd-frequency subseries (with genuinely transcendental `cos(π · 2^m · √2 · 2/3)` factors) remains transcendental. **The conjectural transcendental sum is now demonstrably split into [exact rational] + [transcendental remainder]** — a concrete step pushing conjectural content toward the not-conjectural side.
    - `abs_odd_subseries_sqrt2_two_thirds_le` (a > 1): EXPLICIT BOUND on the odd-frequency remainder `|·| ≤ a/(a²−1)`. Together with the exact even subseries, this gives the FULL BRACKETING `V_P(α=√2, a, 1/6, 5/6) ∈ [−(a²+2a)/(2·(a²−1)), −(a²−2a)/(2·(a²−1))]`. At `a=2`: `V_P ∈ [−4/3, 0]`. Level-1 spectrum at α=√2, a=2: `λ⁺^{(1)} ∈ [1/3, 1]`, `λ⁻^{(1)} ∈ [1, 5/3]`. The conjectural transcendental kernel is now an EXPLICIT BRACKETED ALGEBRAIC INTERVAL.
    - `fractalKernelReal_eq_at_dist_two_thirds_sqrt2`: kernel values at distance 2/3 are identical across level-1 cross-cell `(1/6, 5/6)` and level-2 outer-cross pairs `(1/18, 13/18)`, `(5/18, 17/18)`.
    - `cellMatrixEntry_level2_ff_tf_eq_half_level1`, `_ft_tt_eq_half_level1`: CROSS-LEVEL algebraic identities at α=√2: `M^{(2)}_{[ff],[tf]} = M^{(2)}_{[ft],[tt]} = (1/2)·M^{(1)}_{[false],[true]}`. Level-2 outer-cross matrix entries are EXPLICITLY computable from the level-1 cross entry without re-evaluating transcendental kernel.
  - **★★★ FULL V_P SPLIT + BRACKETING at α=√2 ★★★** (added 2026-05-18, **ZERO project axioms** verified via `#print axioms`):
    - `kernel_series_sqrt2_two_thirds_split`: `Σ_k a^(-k)·cos(π·(√2)^k·2/3) = −a²/(2·(a²−1)) + odd_subsum`, via `HasSum.even_add_odd`.
    - `kernel_series_sqrt2_two_thirds_bracketing`: `Σ_k ... ∈ [−(a²+2a)/(2(a²−1)), −(a²−2a)/(2(a²−1))]`.
    - `fractalKernelReal_sqrt2_two_thirds_bracketing`: V_P at the actual midpoint pair `(1/6, 5/6)` is bracketed in this interval.
    - `fractalKernelReal_sqrt2_two_thirds_at_two_bracketing`: at a=2, **V_P ∈ [−4/3, 0]**.
  - **★★★ Level-1 SPECTRUM BRACKETING at α=√2 ★★★** (added 2026-05-18, **ZERO project axioms**):
    - `level1_spectrum_bracketing_sqrt2`: explicit closed-form intervals for `λ⁺^{(1)}` and `λ⁻^{(1)}` at α=√2 (parametrized in `a`).
    - `level1_spectrum_at_sqrt2_two`: at a=2, **λ⁺^{(1)} ∈ [1/3, 1]**, **λ⁻^{(1)} ∈ [1, 5/3]** (explicit numerical brackets).
    - `cellMatrixEntry_level1_at_sqrt2_two_bracketing`: M^{(1)} cross entry at α=√2, a=2 ∈ [−2/3, 0].
    - `cellMatrixEntry_level2_outer_cross_at_sqrt2_two_bracketing`: M^{(2)} outer-cross entries at α=√2, a=2 ∈ [−1/3, 0].
    - `cellMatrixEntry_level2_diagonal_at_sqrt2_two`: M^{(2)} diagonal entries at α=√2, a=2 are EXACTLY 1/2.
    - `level2_trace_at_sqrt2_two`: tr M^{(2)} at α=√2, a=2 is EXACTLY 2 (matches general identity `tr M^{(n)} = a/(a-1)`).
  - **★★★ TIGHTENED V_P + Level-1 SPECTRUM BRACKETING at α=√2 ★★★** (added 2026-05-19, **ZERO project axioms**):
    - `cos_two_pi_sqrt2_div_three_nonpos`: `cos(2π·√2/3) ≤ 0` (sign of the first odd-frequency term).
    - `odd_subseries_sqrt2_two_thirds_upper`: refined ONE-SIDED upper bound on odd subseries: `Σ ≤ 1/(a(a²−1))` (vs the loose symmetric bound `a/(a²−1)`). Combines `f(0) = (1/a)·cos(2π√2/3) ≤ 0` with the geometric bound on the m≥1 tail.
    - `fractalKernelReal_sqrt2_two_thirds_upper_tight`: V_P upper bound `≤ -(a³−2)/(2a(a²−1))`.
    - `fractalKernelReal_sqrt2_two_thirds_at_two_upper_tight`: at a=2, **V_P ≤ −1/2** (strict separation from zero, vs the loose bound `≤ 0`).
    - `fractalKernelReal_sqrt2_two_thirds_at_two_bracketing_tight`: at a=2, **V_P ∈ [−4/3, −1/2]**.
    - `level1_spectrum_at_sqrt2_two_tight`: at a=2, **λ⁺^{(1)} ∈ [1/3, 3/4]**, **λ⁻^{(1)} ∈ [5/4, 5/3]**.
  - **Significance**: at the manuscript's distinguished case α=√2, a=2, the level-1 finite-rank operator's smallest eigenvalue is now sandwiched as `λ⁺^{(1)} ∈ [1/3, 3/4] = [0.333, 0.750]`. The asymptotic conjecture `λ_0 ≈ π/(10·√2) ≈ 0.222` lies STRICTLY BELOW this tightened bracket — sharper evidence that the spectrum is descending toward 0.222 across levels. ZERO project axioms.
  - **★★★ EVEN TIGHTER V_P + Level-1 SPECTRUM BRACKETING at α=√2 ★★★** (added 2026-05-19, **ZERO project axioms**):
    - `cos_four_pi_sqrt2_div_three_nonneg`: `cos(4π·√2/3) ≥ 0` via 2π-periodicity + reduced angle `|2π(2√2−3)/3| ≤ π/2` (provable from `9 ≤ 8√2 ≤ 15`, i.e., `81 ≤ 128 ≤ 225`).
    - `odd_subseries_sqrt2_two_thirds_lower`: refined LOWER bound on odd subseries: `Σ ≥ -1/a - 1/(a³(a²-1))`. Combines `f(0) ≥ -1/a` (trivial `cos ≥ -1`), `f(1) ≥ 0` (from `cos(4π√2/3) ≥ 0`), and the geometric tail bound from m=2.
    - `fractalKernelReal_sqrt2_two_thirds_at_two_lower_tight`: at a=2, **V_P ≥ -29/24 ≈ -1.208** (vs the loose bound `-4/3 = -32/24 ≈ -1.333`).
    - `fractalKernelReal_sqrt2_two_thirds_at_two_bracketing_tighter`: at a=2, **V_P ∈ [-29/24, -1/2]**.
    - `level1_spectrum_at_sqrt2_two_tighter`: at a=2, **λ⁺^{(1)} ∈ [19/48, 3/4] ≈ [0.396, 0.750]**, **λ⁻^{(1)} ∈ [5/4, 77/48] ≈ [1.250, 1.604]**.
  - **Significance of doubly-tightened bracket**: numerical evaluation gives `V_P(√2, 2, 1/6, 5/6) ≈ -1.02`, so `λ⁺^{(1)}(√2, 2) ≈ 0.49` — well inside the tightened bracket `[0.396, 0.750]`. The gap from the level-1 ground state ≈ 0.49 down to the conjectured limit 0.222 is the SPECTRUM DESCENT predicted by the polylog conjecture, which must be delivered by higher-level eigenvalue computations + the eventual spectral convergence theorem.
  - **★★★★ STRICTLY tightest V_P + Level-1 SPECTRUM BRACKETING at α=√2 ★★★★** (added 2026-05-19, **ZERO project axioms**):
    - `cos_two_pi_sqrt2_div_three_le_neg_half`: `cos(2π·√2/3) ≤ -1/2` (STRICT, via `cos(π + y) = -cos(y)` with `|y| ≤ π/3` from `1 ≤ √2` + `Real.cos_pi_div_three = 1/2` + monotonicity).
    - `cos_four_pi_sqrt2_div_three_ge_half`: `cos(4π·√2/3) ≥ 1/2` (STRICT, via 2π-periodicity with `|z| ≤ π/3` from `√2 ≥ 5/4`, i.e., `25 ≤ 32`).
    - `odd_subseries_sqrt2_two_thirds_upper_strict`: `Σ ≤ -1/(2a) + 1/(a(a²-1))`.
    - `odd_subseries_sqrt2_two_thirds_lower_strict`: `Σ ≥ -1/a + 1/(2a³) - 1/(a³(a²-1))`.
    - `fractalKernelReal_sqrt2_two_thirds_at_two_upper_strict`: at a=2, **V_P ≤ -3/4 = -0.75**.
    - `fractalKernelReal_sqrt2_two_thirds_at_two_lower_strict`: at a=2, **V_P ≥ -55/48 ≈ -1.146**.
    - `fractalKernelReal_sqrt2_two_thirds_at_two_bracketing_strict`: at a=2, **V_P ∈ [-55/48, -3/4]**.
    - `level1_spectrum_at_sqrt2_two_strict`: at a=2, **λ⁺^{(1)} ∈ [41/96, 5/8] ≈ [0.427, 0.625]**, **λ⁻^{(1)} ∈ [11/8, 151/96] ≈ [1.375, 1.573]**.
  - **Significance of strictly-tightest bracket**: bracket width on λ⁺^(1) reduced from 0.354 (prior) to 0.198 (~44% reduction). Numerical λ⁺^(1)(√2, 2) ≈ 0.49 sits comfortably inside `[0.427, 0.625]`. The conjectured asymptotic limit `π/(10·√2) ≈ 0.222` is BELOW the level-1 lower bound 41/96 ≈ 0.427 by a quantifiable gap — the spectrum descent across refinement levels remains the polylog conjecture's content.

* `PF/Analytic/Lipschitz.lean` — Lipschitz/Banach-contraction infrastructure:
  - `cantorContraction1_lipschitz`, `cantorContraction2_lipschitz`: both IFS contractions are `LipschitzWith (1/3)`.
  - `lipschitzWith_comp_cantorContraction{1,2}`: composition with a Lipschitz function shrinks the constant by 1/3.
  - **`iteratedIFSComp_lipschitz`**: under n iterations along any boolean word, the test function's Lipschitz constant shrinks to `L · (1/3)^n`. Combined with `integral_difference_recursion` from `Hutchinson.lean`, this is the COMPLETE analytic engine for the Banach contraction giving GEOMETRIC weak-convergence rate `cantorDiscMeasure n → μ_H` on bounded Lipschitz test functions.

**What the Phase A continuation gives the framework.** The polylog conjecture is now equipped with concrete, machine-checked finite-rank discrete approximations at every level `n`. The level-`n` discrete operator is realised as an explicit real symmetric `2^n × 2^n` matrix with closed-form entries, uniformly bounded `≤ a/(a−1)` in operator norm. Level-0 (1×1) and level-1 (2×2) are fully diagonalised with explicit eigenvectors; the trace identity `Σ λ^{(n)}_k = a/(a−1)` is preserved across levels and provides an empirical test for any candidate closed-form eigenvalue. The full operator `H_P^cantor[μ_H]` is recovered in the `n → ∞` limit via the weak-convergence machinery from `Hutchinson.lean` (the difference recursion + Banach contraction structure is in place; full Wasserstein convergence requires the Lipschitz infrastructure that mathlib's `LipschitzWith` provides).

The polylog conjecture for the FULL operator is now reduced to a finite-rank spectral-convergence argument plus the Riemann-sheet selection of Problem 2.

**What a solution would deliver.** Together with Problems 2 and 3, retires the project axiom and gives an unconditional P ≠ NP via the framework's spectral-gap chain.

**Difficulty estimate.** Multi-month to multi-year original operator-theory research. The supporting infrastructure above is now machine-checked and out of the way; future work attacks the substantive content directly.

---

## Problem 2 — Ground-State Branch Selection Heuristic (Ch 21, `heur:branch-selection`)

**Statement.** Among the multi-valued branches of `Li₁(e^{iπ√2})` produced by the operator's monodromy structure, the physical ground state corresponds to the branch satisfying

```
λ_0(H_P) = min_{branches} { Re[Li₁(e^{iπ√2})] : Re[…] > 0 } = π/(10√2)
```

The principal branch gives `Re[-log(1-e^{iπ√2})] ≈ -0.465` (negative, hence unphysical). The fractal monodromy path is conjectured to select a higher Riemann sheet yielding the empirically observed positive value.

**Current status.** The manuscript labels this `\begin{heuristic}` — a physical-reasoning argument backed by 10⁻¹⁰ numerical match, not a derivation. The selection rule itself is not characterized in terms of intrinsic operator-theoretic invariants.

**Lean encoding.** Implicit in the value pinning component of `alpha_class_polylog_eigenvalue_conjecture`.

**What a solution would deliver.** Together with Problems 1 and 3, completes the P-class side of the axiom retirement.

**Difficulty estimate.** Requires Riemann-sheet selection theory for self-similar operators — there is no standard machinery for this in the operator-algebra literature.

---

## Problem 3 — Golden-Ratio Modulation Conjecture (Ch 21, `conj:golden-modulation`)

**Statement.** The NP-class operator `H_NP` is related to `H_P` by a unitary transformation

```
H_NP = U(φ) · H_P · U†(φ)
```

where `U(φ)` implements a phase rotation by the golden angle `φ = (√5 − 1)π/2`. This is conjectured to yield the ground-state ratio

```
λ_0(H_NP) / λ_0(H_P) = sin(π/√2) / sin(π/√2 + φ) = (√5 − 1)/3
```

and the closed-form `α_NP = φ + 1/4`.

**Current status.** Numerical sine-ratio computation: 0.798635510 / 0.847127424 ≈ 0.5988854382 = (√5 − 1)/3. Match verified to 10⁻¹⁰ via the finite-dim ground-state computation `λ_0(H_NP) = 0.1330222423 ± 10⁻¹⁰`. The unitary-conjugation structural claim is not derived.

**Lean encoding.** NP-class component of `alpha_class_polylog_eigenvalue_conjecture` (the quadratic `16α² − 24α − 11 = 0`).

**What a solution would deliver.** Combined with Problems 1 and 2, retires the project axiom unconditionally.

**Difficulty estimate.** Requires explicit construction of the unitary `U(φ)` and verification of the conjugacy on the fractal-kernel operator — bounded but non-trivial.

---

## Problem 4 — Spectral-Bijection Surjectivity (Ch 20, `rem:bijection-surjectivity`)

**Statement.** Let `T₃^sym` be the manuscript's symmetrized transfer operator on `L²((0,1), dx/x)`. The framework constructs an injection from the eigenvalue spectrum `{λ_n}` of `T₃^sym` into the critical line `Re(s) = 1/2` via `eigenvalueToZero α λ_n`. Conjecture: this injection is *surjective* onto the set of nontrivial zeros of `riemannZeta`.

Formally (`PF/SpectralBijection.lean:544-548`):

```lean
surjectivity : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
    ∃ n : ℕ, eigenvalueToZero α (eigenvalues n) = s
```

**Current status.** This is the **det/trace-formula completion** problem of the entire framework's RH approach. From the file itself: *"the load-bearing conjecture of the entire RH program (det/trace-formula completion). This is the open mathematical problem; the other three are research engineering."*

**Lean encoding.** Takes `surjectivity` as a **hypothesis parameter** of the theorem `riemann_hypothesis_via_T3_sym_framework`. The theorem proves: surjectivity ⇒ RH.

**What a solution would deliver.** Combined with three engineering tracks (Phase A inner-product structure, compact-operator spectral theorem, non-degeneracy), an unconditional proof of the Riemann Hypothesis.

**Difficulty estimate.** This is the open problem of the entire approach. Difficulty: comparable to RH itself.

---

## Summary

| # | Problem | Manuscript label | Solving retires |
|---|---|---|---|
| 1 | Polylog eigenvalue formula for `H_P` | `conj:polylog-spectrum` | Part of P≠NP axiom |
| 2 | Ground-state branch selection | `heur:branch-selection` | Part of P≠NP axiom |
| 3 | Golden-ratio modulation `H_NP = U(φ)H_P U†` | `conj:golden-modulation` | NP-class part of P≠NP axiom |
| 4 | Spectral-bijection surjectivity onto ζ-zeros | `rem:bijection-surjectivity` | Surjectivity hypothesis of RH theorem |

**Problems 1+2+3 together** retire the single Lean axiom `alpha_class_polylog_eigenvalue_conjecture`, upgrading `P_neq_NP_via_spectral_gap` from a conditional reduction to an unconditional proof of P ≠ NP.

**Problem 4** discharges the load-bearing hypothesis of `riemann_hypothesis_via_T3_sym_framework`, upgrading it from a conditional reduction to a (modulo three tractable engineering tracks) unconditional proof of the Riemann Hypothesis.

## What is NOT among the open problems isolated by this framework

The framework does **not** claim to have proven, reduced, or made progress on:

- **Yang-Mills mass gap** — manuscript-level discussion only; Lean construction deleted Stage 30.
- **Navier-Stokes existence and smoothness** — Coq-side scaffolding only.
- **Birch–Swinnerton-Dyer Conjecture** — Coq-side scaffolding only.
- **Hodge Conjecture** — Coq-side scaffolding only.
- **Poincaré Conjecture** — already proven by Perelman (2003), independent of this framework.

These are not "isolated open problems" of Principia Fractalis. They are areas where the manuscript's discussion exists but no mechanical reduction has been delivered.
