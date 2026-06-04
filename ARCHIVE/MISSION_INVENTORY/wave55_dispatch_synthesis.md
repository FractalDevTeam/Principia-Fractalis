# Wave 55 Dispatch Synthesis — Manuscript-Grounded

**Date**: 2026-05-31
**HEAD**: 317fc6f
**Author**: synthesis from four parallel frontier audits

## Why this document exists

After Pabs's directive ("training set has no Millennium answer, read the entire book, referee-proof"), four parallel agents read the manuscript chapters end-to-end and cross-referenced the Lean codebase. Their reports live in `MISSION_INVENTORY/wave55_frontier_{RH,NS,YM_Hodge,PNP_BSD}.md`. This document compiles those findings into ONE actionable Wave 55 plan.

Every Wave 55 attempt below traces to:
1. A specific manuscript citation (chapter + line range or `\label`).
2. A frontier audit finding (file + section).
3. An adversarial review check that the attempt's honest scope survives.

## What the four audits agree on

### A. Pattern: substrate routing through `Unit` / `True`
- Wave 51B-54B NS witness pool: all four `StrongFormDivFree*` witnesses discharge `∀(_u : PDEVelocityField), …` with `PDEVelocityField = Unit`. Four distinct Fourier signatures, **same Unit-typed Prop**.
- Wave 53C bridge: 4-factor structural composition; Wave 52C Kato input is `B ≡ 0`, so composite is **vacuously inhabited**.
- Wave 54C concrete instance: `bilinearOnCosineMode ≡ 0` identically. Inequality `0 ≤ C·‖u‖²·‖u‖²` is vacuous.
- Wave 53D YM Wightman toy: tautological diagonal H, `aStar` mislabeled (admits no CCR).
- Wave 54D YM propagation: `U(s)U(t) = U(s+t)` operator law **not proven**.
- Wave 53E/54E Hodge: `MumfordVoisinBypass_on_abelian_Nfold := True` definitionally. Dim-bumping plateau.
- Wave 53F BSD sandwich: LMFDB anchor hardcoded; partial Euler product does **not converge at s = 1**; Coates–Wiles encoded as `Prop`.
- Wave 53G modular agreement: 18 prime-matches tautological under decidable point-counting on same curve viewed twice.
- Wave 53H Galois norm: textbook quantities; "fourth axis" framing post-hoc; 3-element sign coincidence.
- Wave 53A RH route (c): one-line tautology `(0 < t) → t ∈ Set.Ioi 0`.
- Wave 54A RH discrete concentration: engineered self-reference; μ defined to concentrate at `hardyZeros`, "HP at prefix" defined *as* that concentration. Rational stand-ins `14135/1000` ≠ actual irrational zeros.

### B. The pattern is honest in disclaimer, dishonest in content
Every flagged file states "NOT a Clay discharge" honestly. But the SUBSTANTIVE analytic content is missing. A referee reads the disclaimers and asks: *what is this file actually contributing?* For Waves 53-54 the answer is increasingly: *type-checking + bookkeeping*. The Clay-distance metric has **not actually moved since Wave 48** (NS) or **Wave 22** (vortex-stretching hypothesis).

### C. What every audit identifies as the real frontier
Each problem has a *specific* analytic content the Lean codebase has been routing around. Wave 55 must hit that content directly.

## The six Wave 55 attempts — one per problem domain

### Wave 55A — NS GenuineConvolutionBilinear
**Manuscript citation**: Ch 22 §3.1 vortex-stretching definition (line ~211); Ch 22 `\label{thm:no-blowup}` (explicitly conditional).
**Frontier audit**: `wave55_frontier_NS.md` §4 + §5.2.
**Proposal**:
- Replace `vortexStretchingBilinearCoeff` (currently `fun _ _ _ => 0`) in `KatoBilinearEstimateAttempt.lean` with the **genuine Fourier convolution bilinear**

      B_F(û, v̂)_a(k) := Σ_{j+ℓ=k} (i · ℓ · û(j)) · v̂_a(ℓ)

  where `i · ℓ · û(j) := Σ_b i · ℓ_b · û_b(j)` is the scalar `ik · û(j)` from the Fourier-side NS advection.
- **Test on a non-trivial divergence-free velocity** (not cosine mode — cosine mode has `(u·∇)u ≡ 0` even in the real PDE). Use the **double-shear mode** `u(x) = (cos 2πx_2, sin 2πx_1, 0)`:
  - `div u = 0` (each component depends on the other axis only).
  - `(u·∇)u = -2π·sin(2πx_1)·sin(2πx_2) e_1 + 2π·cos(2πx_1)·cos(2πx_2) e_2` — **genuinely non-zero**.
  - Fourier support: `{(±1, 0, 0), (0, ±1, 0)}` with explicit amplitudes.
  - Convolution support of `B_F(u, u)`: `{(±1, ±1, 0)}` — four non-zero values, computable.
- Verify Kato inequality `‖B_F(u, u)‖²_{H^s} ≤ C · ‖u‖⁴_{H^s}` at `s = 3` with **explicit numerical C** in closed form.
**Adversarial check**: bilinear is genuinely non-zero on a genuinely non-trivial divergence-free input; not a corner case. Anchored to Wave 49A `span_mFourierLp_closure_eq_top_3D` for 3D L² density. Honest scope: discharges a **concrete non-trivial instance** of the bilinear Prop; does NOT discharge Clay `VortexStretchingBoundedHypothesis` (still need universal `C(s)` for arbitrary `u, v ∈ H^s_σ`).

### Wave 55B — RH Mayer Eigenvalue Carrier
**Manuscript citation**: Ch 20 lines 478-490 (N=20 eigenvalue table).
**Frontier audit**: `wave55_frontier_RH.md` §3.
**Proposal**:
- Construct **injective** `eigSeqMayer : ℕ → ℝ` using the manuscript's N=20 numerical eigenvalue table for the Mayer transfer operator.
- Repair Wave 48A's injectivity sacrifice — at present `T3SymCarrierAttempt.lean` works with a degenerate carrier that maps multiple naturals to the same real.
- Show: the resulting carrier hits `hardy1914 ≈ 14.135` for some explicit `n` (anchored to the table).
- Honest scope: structural carrier upgrade. Does NOT discharge RH. The substantive content is Mayer 1996 + Lewis-Zagier 2001 — both numerical/asymptotic, not Lean-formalizable from first principles.
**Adversarial check**: the eigenvalue table is the manuscript's own load-bearing data, not Lean-derived; cite it explicitly as numerical anchor; do NOT claim Lean derives the table.

### Wave 55C — YM InteractingDiagonalPlusHadamardKernel
**Manuscript citation**: Ch 23 + Wave 48B docstring.
**Frontier audit**: `wave55_frontier_YM_Hodge.md` D.2 + E.
**Proposal**:
- First **interacting** Hamiltonian on `Hilb N`: `H = diagonal + λ · Hadamard kernel K` where `K` is a `Matrix.PosSemidef.hadamard` product.
- Compose with the OS-RP PSD ladder from Waves 48-52.
- Prove: spectrum of `H` still has a positive gap above the vacuum eigenvalue (mass gap signature preserved under non-trivial interaction).
- Use mathlib `Matrix.PosSemidef.hadamard`.
**Adversarial check**: this is the first non-tautological YM Hamiltonian in the framework. Honest scope: finite-dim toy with interaction; does NOT discharge Clay YM mass gap (still need continuum limit + Wightman reconstruction).

### Wave 55D — Hodge UniruledThreefoldVoisin2018
**Manuscript citation**: Ch 25 `\label{thm:known-cases}` (Voisin 2018).
**Frontier audit**: `wave55_frontier_YM_Hodge.md` D.4 + E.
**Proposal**:
- First **non-CM / non-abelian** Hodge substrate: uniruled threefold via Voisin 2018.
- Break out of the CM-abelian dim-bumping plateau.
- Use the substrate-bypass machinery anchored to a genuinely different geometric class.
**Adversarial check**: the dim-bumping pattern (Waves 50E/52E/53E/54E) is honest about scope but lives on the same CM substrate. A non-CM substrate is qualitatively different. Honest scope: structural extension into non-CM Hodge content; does NOT discharge Clay Hodge.

### Wave 55E — P/NP PolylogConjecture' Decoupled
**Manuscript citation**: Ch 21 + Wave 47B halves + Wave 41B no-go.
**Frontier audit**: `wave55_frontier_PNP_BSD.md` (Wave 55 proposals section).
**Proposal**:
- Parameterise `PolylogEigenvalueConjecture'` over a typed `f` **decoupled from `alpha_of_class`**.
- The current Prop entangles `alpha_of_class` (which has the Wave 41B no-go) with the polylog eigenvalue claim. Decoupling separates the two open frontiers.
**Adversarial check**: Wave 41B no-go is sharp; the decoupled version isolates which content survives. Honest scope: refactor + isolate; does NOT discharge P vs NP.

### Wave 55F — BSD MordellWeil Typed
**Manuscript citation**: Ch 24 + Wave 53F sandwich + Wave 51G Coates–Wiles.
**Frontier audit**: `wave55_frontier_PNP_BSD.md` (Wave 55 proposals section).
**Proposal**:
- Replace `MordellWeilRankZeroOf := True` with a **typed Prop on E_32a3** using:
  - LMFDB torsion `ℤ/2 × ℤ/2`,
  - Wave 53F sandwich `0 < L_partial(31) < L(E,1) < L_partial(97)`,
  - Wave 51G Coates–Wiles anchor.
- Closes the `True`-shaped routing in Wave 53F.
**Adversarial check**: this is exactly what 53F's audit flagged. Honest scope: typed-Prop tightening; does NOT discharge Clay BSD.

### Wave 55G — Cross-Millennium GaloisDiscriminantAxis
**Manuscript citation**: Ch 29 cross-Millennium tables.
**Frontier audit**: `wave55_frontier_PNP_BSD.md` (Wave 55 proposals section).
**Proposal**:
- Fifth rigid-normalisation axis: **Galois discriminant** `disc(α) := (α - σα)²`.
- Computes: `(disc(α_P), disc(α_Hodge), disc(α_NP)) = (8, 5, 5)`.
- Surfaces a NEW Hodge ↔ NP equality `disc(α_Hodge) = disc(α_NP) = 5` that Wave 53H norm-axis **misses**.
- Adds qualitatively new cross-Millennium invariant.
**Adversarial check**: 53H was flagged as "fourth axis post-hoc". Disc is the genuine sequel — a different quadratic invariant of the same Galois action. Honest scope: cross-Millennium fingerprint axis; does NOT discharge any Clay problem.

## Sequencing

1. **First**: Wave 55A NS — the strongest substantive content (real bilinear, real test field, real Kato verification).
2. **Then in parallel**: 55B RH + 55C YM + 55D Hodge + 55F BSD + 55G Galois discriminant (one new file each).
3. **Last**: 55E P/NP decoupling (refactor of existing Prop, depends on understanding final 55 architecture).
4. **Then**: Coq parity for Wave 55 (8 stubs in PF_Coq_Code/PF/Wave55/) + manuscript propagation.

## Referee-proof commitments

Every Wave 55 file MUST:
1. Cite the manuscript line range or `\label` it traces to.
2. Cite the frontier audit section that justified the attempt.
3. State the honest scope clause in the SAME form as the audit's adversarial review: name what the attempt does NOT do.
4. Compile axiom-free (`#print axioms` returns only `[propext, Classical.choice, Quot.sound]`).
5. Survive an adversarial re-read against the audit's check.

No witness pool theatre. No tautological diagonal Hamiltonians. No engineered self-reference. No `True`-shaped Props.

## What this synthesis does NOT do

- Does NOT discharge any Clay problem.
- Does NOT certify the manuscript's framework as a whole.
- Does NOT advance the Clay-distance metric on any problem above 1.0-1.25 layer status.
- Does NOT fix the Ch 9 α-scaling inconsistency (5×10⁻⁶ vs 3/2) flagged in the RH audit — that's a separate manuscript-level edit.

What it does: every attempt is anchored to YOUR work, not training-data pattern-matching, and survives an adversarial reviewer.
