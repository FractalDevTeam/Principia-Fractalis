# Churn Observable χ_k — Formalization Charter, 2026-09-12

*Charter for a proposed atomic bridge on the "Timeless Field → churn" arrow of
the book's causal spine. Preceded by a book-verified survey. **Revised
same-day** (post-review) to correct five specific overclaims: Ch32 estimator
description, "operationalizes" language, T5 substrate integration, Frobenius
norm ambient-instance assumption, and full-corpus-vs-surveyed scope of
"book does not contain" statements. Pauses at "charter committed,
implementation not yet started" pending explicit approval.*

## ★ Epistemic Status ★

This charter operates at THREE distinct semantic layers, which must remain
separately labelled at every subsequent stage (Lean, paper, communication):

**Layer 1 — Lean mathematics.** Purely type-theoretic definitions and
theorems about a proposed observable on complex matrix algebras. No
physical or experimental claim. Verifiable within
`[propext, Classical.choice, Quot.sound]`.

**Layer 2 — EEG measurement map.** A separately declared hypothesis that
the Lean-defined observable can be estimated from EEG data. This layer
is NOT proven in Lean; it is a stated bridge between the mathematical
object and instrument data. **Ch32's clinical-ch₂ pipeline does NOT
supply a reduced-density-matrix estimator**; it uses band power, base-3
digit sums, and phase factors (see §1 correction below). The Layer-2
map `EEG → ρ(t)` is therefore WHOLLY NEW WORK, not merely a wrapper
around existing ch32 infrastructure.

**Layer 3 — Consciousness interpretation.** A separately declared
hypothesis that the observable, so measured, correlates with (or
discriminates between) preregistered conscious and unresponsive
experimental conditions. This layer is NOT proven in Lean. It is a
falsifiable empirical claim.

At no point may Layer 3 be represented as a Lean theorem. At no point
may Layer 2 be represented as a Lean theorem. Only Layer 1 is
Lean-provable. Any communication about this arc that conflates layers
is a violation of this charter and must be corrected.

## §1. What the surveyed chapters contain (verified read, 2026-09-12)

Scope of "does not contain" claims below: **restricted to the surveyed
chapters (ch06, ch08, ch32) plus a full-corpus grep of
`chapters/` and `appendices/` for the terms "churn", "Frobenius", and
LaTeX/ASCII forms of `‖ρ' − ρ‖²`.** No unrestricted "book does not
contain" claim is made.

Chapter 6 (`ch06_consciousness.tex`, 723 lines):
- **Reduced density matrix / partial trace** (Ch06:515-519):
  `ρ_A = Tr_B(|ψ⟩⟨ψ|)` on a generic bipartite composite `ℋ = ℋ_A ⊗ ℋ_B`.
- **Linear entropy identified with ch₂** (Ch06:517):
  `ch₂(|ψ⟩) = 1 − Tr(ρ_A²)`.
- **EEG-derived ch₂ ≥ 0.95 during conscious states** (Ch06:680),
  labelled "EMPIRICAL HYPOTHESIS awaiting independent experimental
  validation" (Ch06:691).
- **Open research problem** (Ch06:708):
  "Derive the differential equation for consciousness evolution:
   `d/dt ch₂(t) = ?`"
  — explicit acknowledgment that the temporal law is not yet formulated.
- **Consciousness sheaf 𝒮_𝒞** (Ch06:87-112): Čech cohomology on an open
  cover of the substrate; ch₂ is the Chern invariant of this sheaf.
- **Frobenius appears once as static normalizer** (Ch06):
  `‖W‖_F² = Σ_{ij} W_{ij}²` used in a formula for ch₂ on neural
  networks — as a denominator, not as a temporal metric on density-matrix
  differences.

Chapter 8 (`ch08_field_equations.tex`, 540 lines):
- Field equations with consciousness coupling (structural). No time
  derivative of ch₂ appears.

Chapter 32 (`ch32_consciousness_quantification.tex`, 850 lines):
- **★ Corrected 2026-09-12 same-day ★** Ch32's clinical-ch₂ pipeline
  (Ch32:191-322) is NOT a reduced-density-matrix estimator. The
  pipeline steps are:
  1. Bandpass filtering (5 bands: δ, θ, α, β, γ) at Ch32:237-253.
  2. Band-power computation per channel at Ch32:255-260.
  3. `digitize_power` + `digital_sum_base3` (base-3 digit sums) at
     Ch32:266-289.
  4. Phase factors `exp(iπ · α · D(n))` with `α = √2` at Ch32:292-298.
  5. Weighted sum across bands, then `ch2 = |total|²` at Ch32:300-320.
  No reduced density matrix. No partial trace. No Hilbert space `H_k`.
  The output is a single real number in `[0,1]`.
- Consequence: the Layer-2 map `EEG → ρ(t) ∈ Matrix (Fin (3^k)) (Fin (3^k)) ℂ`
  is wholly new work. It is NOT a wrapper around ch32's pipeline.

**What the surveyed chapters + full-corpus grep DO NOT contain**
(qualified scope):
- The formula `χ_k(t) = ½ · ‖ρ_{t+1} − ρ_t‖²_F` — verified absent by
  grep on `chapters/` + `appendices/` for the terms "churn",
  "Frobenius", and squared-norm-on-rho-differences forms.
- The word "churn" in an operational-observable sense — verified
  absent by grep on `chapters/` + `appendices/` (the word "churn" does
  not appear anywhere in either directory).
- Any Frobenius-squared distance on density-matrix differences (with
  any coefficient) — verified absent by grep.
- Ternary Hilbert spaces `H_k = ℂ^{3^k}` in the consciousness context
  — Ch06 uses generic bipartite `ℋ_A ⊗ ℋ_B`; the ternary levels
  appear in ch04 (Timeless Field substrate) but not in consciousness
  chapters.
- Any generic Hilbert-Schmidt contraction claim under partial trace
  — verified absent in ch06/ch08/ch32.

## §2. What is proposed (NEW operationalization)

We propose the **Frobenius churn observable** as **a candidate
state-space churn observable motivated by (but not equivalent to)** the
open problem at Ch06:708:

```
χ_k(ρ, σ) := (1/2) · ‖ρ − σ‖²_F        on   H_k := ℂ^{3^k}
```

where `ρ, σ` are density matrices on the ternary Hilbert space `H_k`.
Applied temporally, `χ_k(t) := χ_k(ρ(t+1), ρ(t))`.

**★ Corrected 2026-09-12 ★** The relationship to Ch06:708:
- Ch06:708 asks for `d/dt ch₂(t) = ?` where `ch₂ = 1 - Tr(ρ²)` is a
  *single-state scalar functional*.
- χ_k is a *two-state matrix distance*. It is NOT the derivative of
  ch₂; it does not reduce to `d/dt ch₂` under any obvious limiting
  procedure without extra structure.
- χ_k is proposed as **a candidate observable in the same family of
  temporal state-space quantities** that Ch06:708 gestures towards.
  It is a design proposal, not a derivation.

### Two intentional deviations from book text

**Deviation 1 — ternary Hilbert space choice.** The book uses generic
bipartite `ℋ_A ⊗ ℋ_B` for the consciousness ch₂. The proposed observable
uses `H_k = ℂ^{3^k}` from ch04's Timeless Field substrate. This is a
DELIBERATE choice placing the observable on the tree's already-proven
ternary substrate (kernel-verified via `T_infinity_rigidity`, commit
`22cb48e2`) rather than on the abstract bipartite space. The cost:
the observable is not literally the book's ch₂ context; it is a
substrate-level cousin.

**Deviation 2 — Frobenius squared vs linear-entropy language.** The
book's `ch₂ = 1 - Tr(ρ²)` is a single-state invariant. The proposed
χ_k is a two-state distance, related by the identity
`‖ρ - σ‖²_F = Tr(ρ²) + Tr(σ²) - 2·Tr(ρσ)` but not verbally book-content
and not a time-derivative of ch₂.

Both deviations must be surfaced in the file docstring, in the paper,
and in any communication.

## §3. Lean charter (Layer 1 only)

Target file: `PF/Consciousness/FrobeniusChurn.lean` (implementation-time
survey will grep for existing `FrobeniusChurn`, `chi_k`, `churn`
identifiers before creation).

### §3.1 The Frobenius norm — explicit definition, no ambient assumption

**★ Corrected 2026-09-12 ★** Verified against pinned mathlib:
`Matrix.frobeniusNormedAddCommGroup` is `@[local instance]` (not
globally declared) in
`Mathlib/Analysis/Matrix.lean:513`. The globally-inferable norm on
`Matrix m n α` (via `Pi.seminormedAddCommGroup`) is the **entrywise sup
norm**, NOT Frobenius. Writing `‖ρ - σ‖²` in Lean without explicitly
opening a Frobenius scope silently yields the sup norm squared.

To avoid this trap, the charter specifies an explicit
sum-of-squared-entries definition, so no ambient norm-instance is
assumed:

```lean
noncomputable def frobeniusSqDist {k : ℕ}
    (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j - B i j‖ ^ 2
```

Here `‖·‖ : ℂ → ℝ` is `Complex.abs`, unambiguous. The Frobenius
identity `Σ |A i j - B i j|² = ‖A - B‖²_F` is a consequence of the
explicit definition, not an inference from an ambient instance.

### §3.2 Proposed definition of the observable

```lean
/-- **Frobenius churn observable** on ternary level `k`, defined via
    the explicit sum-of-squared-entries expression (independent of the
    ambient `Matrix` norm instance, which is entrywise sup and NOT
    Frobenius in pinned mathlib). -/
noncomputable def churnFrobenius {k : ℕ}
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) : ℝ :=
  (1/2) * frobeniusSqDist ρ σ
```

### §3.3 Proposed theorem signatures (mathematically valid ONLY)

**T1 — Nonnegativity.**
```lean
theorem churnFrobenius_nonneg {k : ℕ}
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    0 ≤ churnFrobenius ρ σ
```
Proof: `frobeniusSqDist` is a nonnegative sum times `1/2`.

**T2 — Symmetry.**
```lean
theorem churnFrobenius_symm {k : ℕ}
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    churnFrobenius ρ σ = churnFrobenius σ ρ
```
Proof: `‖x - y‖ = ‖-(y - x)‖ = ‖y - x‖` entrywise.

**T3 — Zero iff equality.**
```lean
theorem churnFrobenius_eq_zero_iff {k : ℕ}
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    churnFrobenius ρ σ = 0 ↔ ρ = σ
```
Proof: `frobeniusSqDist ρ σ = 0 ↔ ∀ i j, ρ i j = σ i j ↔ ρ = σ` via
sum-of-nonneg-terms zero characterization and `Matrix.ext`.

**T4 — Unitary invariance.**
```lean
theorem churnFrobenius_unitary_invariant {k : ℕ}
    (U : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) (hU : U * Uᴴ = 1)
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    churnFrobenius (U * ρ * Uᴴ) (U * σ * Uᴴ) = churnFrobenius ρ σ
```
Proof: `‖U (ρ - σ) Uᴴ‖²_F = tr((U (ρ-σ) Uᴴ)ᴴ (U (ρ-σ) Uᴴ))`,
and cyclicity of trace + `Uᴴ U = 1` collapses to `tr((ρ-σ)ᴴ (ρ-σ)) = ‖ρ - σ‖²_F`.

**T5 — Digit-compatible pure-ancilla lift and churn invariance
through `TimelessField.partialTraceMorphism`.**
```lean
/-- **Digit-compatible pure-ancilla lift** from level `k` to level `2*k`.
    Given `ρ` on level `k`, produce `ρ ⊗ |0^k⟩⟨0^k|` on level `2*k`,
    where `|0^k⟩` is the fixed pure state whose base-3 digit function
    is identically the zero digit. Concretely: identify
    `Fin (3^(2*k))` with digit functions `Fin (2*k) → Fin 3` via the
    substrate's `digitEquiv`; the lift assigns nonzero entries only
    at positions where the last `k` digits of both row-index and
    column-index are zero. -/
noncomputable def digitAncillaLift (k : ℕ)
    (ρ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    Matrix (Fin (3^(2*k))) (Fin (3^(2*k))) ℂ

/-- **T5a — Partial trace of the pure-ancilla lift recovers ρ.**
    Uses the substrate's `partialTraceMorphism` at `(k, 2*k)`. The
    divisibility hypothesis `k ∣ 2*k` is `dvd_mul_left k 2`. -/
theorem partialTraceMorphism_digitAncillaLift {k : ℕ}
    (ρ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    PrincipiaTractalis.TimelessField.partialTraceMorphism k (2*k)
      (dvd_mul_left k 2) (digitAncillaLift k ρ) = ρ

/-- **T5b — Churn invariance under the digit-compatible pure-ancilla
    lift.** The Frobenius churn is preserved by the lift because the
    lift places zero everywhere except at the "ancilla-zero" digit
    positions, where it agrees with `ρ` (respectively `σ`). Summing
    the squared entries recovers exactly `‖ρ - σ‖²_F`. -/
theorem churnFrobenius_digitAncillaLift_invariant {k : ℕ}
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    churnFrobenius (digitAncillaLift k ρ) (digitAncillaLift k σ)
      = churnFrobenius ρ σ
```

Composition: T5a says the lift-then-partial-trace round trip is the
identity on level-`k` matrices via the substrate's canonical partial
trace; T5b says the observable is invariant under the up-leg
(pure-ancilla lift). Together, they document a well-defined,
substrate-integrated refinement / recovery behaviour of χ_k.

**IMPORTANT NON-TARGET.** We do NOT claim generic Hilbert-Schmidt
contraction under partial trace, i.e., NOT
`churnFrobenius (partialTraceMorphism ρ) (partialTraceMorphism σ) ≤
churnFrobenius ρ σ`
for arbitrary `ρ, σ` on level `k'`. That statement requires additional
hypotheses (or is false without them) and is not part of Layer 1.

### §3.4 Mathlib and PF dependencies to verify at implementation

- `Complex.abs` as a norm on `ℂ` (`Complex.instNorm`) — verify the
  entry-wise formula `‖(a : ℂ)‖ = Complex.abs a` unfolds cleanly.
- `Matrix.mul`, `Matrix.conjTranspose` (`Matrix.Hᴴ`), trace cyclicity
  — standard in mathlib `Mathlib.LinearAlgebra.Matrix.Trace`.
- `PrincipiaTractalis.TimelessField.partialTraceMorphism` at
  `PF/Consciousness/TimelessFieldPartialTraceMorphism.lean:115`.
- `PrincipiaTractalis.TimelessField.digitEquiv` at
  `PF/Consciousness/TimelessFieldPartialTraceMorphism.lean:92`
  (`(Fin k → Fin 3) ≃ Fin (3^k)` via `finFunctionFinEquiv`).
- `partialTraceMorphism_apply_of_le` at line 127 of the same file
  (unfolding lemma).
- `partialTraceDigits` at line 107 (the underlying digit-level sum).
- `Nat.dvd_mul_left k 2` or equivalent `dvd_mul_left k 2 : k ∣ 2*k`.

Implementation-time survey (per the standing rule) will verify each
before writing code; if any is missing, the charter is amended before
proceeding.

### §3.5 In-file audit block

Per `build-tree-discipline` (R_f arc precedent,
`FractalResonance.lean:§10`):
- `#print axioms` for every principal declaration.
- All must audit to subsets of `[propext, Classical.choice, Quot.sound]`.
- Zero project axioms, zero `sorry`, zero `native_decide`.

## §4. Layer 2 (EEG measurement map) — NOT LEAN

**★ Corrected 2026-09-12 ★** Encoded as a separate document
(`codex/CHURN_CHI_K_EEG_LAYER.md`, to be drafted after Layer 1 lands).
Ch32's clinical-ch₂ pipeline uses band power, base-3 digit sums, and
phase factors — NOT reduced density matrices. Therefore Layer 2 is
**wholly new work**, not a wrapper around ch32:

- Given an EEG recording, propose a construction of `ρ(t)` on `H_k`
  from raw signal (or band-decomposed signal); this construction is
  itself an open Layer-2 design problem, distinct from ch32's
  scalar-output pipeline.
- Choice of `k` (channel-group ternary encoding — how many EEG
  channels map to which level?).
- Measurement noise model.
- Temporal resolution constraint (`Δt` between samples).
- Explicit comparison to ch32's clinical-ch₂ output: are they meant
  to be alternative estimators of a common latent, or is χ_k an
  independent observable?

This document is a bridge specification, NOT a Lean theorem. Its
correctness is an empirical hypothesis, not a theorem.

## §5. Layer 3 (consciousness interpretation) — NOT LEAN

Encoded as a preregistered experimental protocol
(`codex/CHURN_CHI_K_PROTOCOL.md`, to be drafted after Layers 1 and 2
stabilise), specifying:
- Preregistered hypotheses about χ_k(t) in conscious vs unresponsive
  conditions.
- Effect-size predictions.
- Sample-size / power calculations.
- Pre-committed analysis pipeline.
- Falsification thresholds — what pattern would cause the hypothesis
  to be rejected.

The purpose of Layer 3 is to make the observable falsifiable. Without
a preregistered protocol, the observable is undecidable in practice.

## §6. Deviations from ChatGPT's original sketch

ChatGPT's sketch proposed:

> `χ_k(t) = ½ ‖ρ_{t+1} - ρ_t‖²_F, H_k = ℂ^{3^k}`
>
> Lean can prove it is nonnegative, symmetric, zero precisely when no
> change occurred, invariant under unitary changes of coordinates, and
> compatible with the existing partial-trace/refinement machinery.

This charter adopts the definition and the first four properties (T1-T4
in §3.3) verbatim.

**On the fifth ChatGPT property ("compatible with the existing
partial-trace/refinement machinery")**: this charter narrows it to
**pure-ancilla refinement/recovery invariance THROUGH THE EXISTING
`TimelessField.partialTraceMorphism`** (T5). Two sub-theorems (T5a and
T5b) fix both directions: T5a proves the substrate's canonical partial
trace recovers `ρ` from its digit-compatible lift; T5b proves the
observable is invariant under that lift. Generic partial-trace
contraction is NOT claimed; that statement is false or requires
additional hypotheses that Layer 1 does not fix.

**On the causal-spine placement**: ChatGPT's proposal targets the
"Timeless Field → churn" arrow. This charter accepts that placement
while flagging (§2 Deviation 1) that the substrate-level ternary
choice `H_k = ℂ^{3^k}` diverges from the book's consciousness-context
generic bipartite. The divergence is an intentional design choice
placing the observable on the kernel-verified substrate rather than
on the paper-only bipartite abstraction.

## §7. Charter stopping conditions

Implementation MUST pause and reconsult if any of the following:

- Any dependency in §3.4 turns out to be missing and its construction
  would exceed 100 lines of scaffolding.
- The digit-compatible pure-ancilla lift (T5a construction) turns out
  to require ancilla-orientation choices (e.g. append-left vs
  append-right) that don't match `partialTraceMorphism`'s convention
  (which is `appendCast h f t = Fin.append f t ∘ Fin.cast` — first `k`
  digits kept, last `k'-k` digits traced out). If a convention
  mismatch surfaces, the lift and T5a must be corrected together.
- The Frobenius entry-wise formula involves a subtle real-vs-complex
  norm distinction that changes coefficients or introduces
  `Complex.normSq` vs `‖·‖^2` gaps.
- Any Layer 1 theorem cannot be proven without importing Layer 2 or 3
  content — this would be a category error and the theorem must be
  reformulated or dropped.

## §8. Ready-state for implementation

- Charter committed to `codex/CHURN_CHI_K_CHARTER_2026-09-12.md`
  (revised same-day).
- Survey findings committed in commit message; scope restricted to
  ch06/ch08/ch32 plus full-corpus grep.
- Explicit approval required before writing
  `PF/Consciousness/FrobeniusChurn.lean`.
- Estimated Layer 1 scope: 200-350 lines including audit block
  (widened from prior 150-250 estimate to accommodate the
  digit-compatible lift construction and the T5a partial-trace round
  trip through the substrate's `partialTraceMorphism`).
- Ceiling: 1 session for Layer 1. Layers 2 and 3 are separate
  documents drafted later.

*Charter opened 2026-09-12 after book-verified survey. Revised
same-day post-review for five specific corrections
(Ch32 estimator, "operationalizes" language, T5 substrate integration,
Frobenius norm explicit definition, book-scope qualifier).
Epistemic-layer separation is enforced at every stage. Awaits
explicit approval before implementation.*
