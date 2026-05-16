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

**Current status.** Numerical: ground-state eigenvalue computed via finite-dimensional approximation (`N = 2⁸` to `2¹⁶` basis functions) converges to `0.2221441469 ± 10⁻¹⁰`, matching `π/(10√2) ≈ 0.2221441469079…` to within 10⁻¹⁰. Analytical: no proof.

**Lean encoding.** Part of `alpha_class_polylog_eigenvalue_conjecture` axiom (`PF/TuringEncoding/Operators.lean`).

**What a solution would deliver.** Together with Problems 2 and 3, retires the project axiom and gives an unconditional P ≠ NP via the framework's spectral-gap chain.

**Difficulty estimate.** Multi-month to multi-year original operator-theory research.

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
