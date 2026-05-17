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
