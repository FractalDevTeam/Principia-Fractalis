# Churn Observable χ_k — Formalization Charter, 2026-09-12

*Charter for a proposed atomic bridge on the "Timeless Field → churn" arrow of
the book's causal spine. Preceded by a book-verified survey
(codex/CH09_SPECTRAL_UNITY_SURVEY_2026-09-12.md discipline;
this charter's survey lives in the commit thread and in the sections below).
Pauses at the "charter committed, implementation not yet started" state
pending explicit approval.*

## ★ Epistemic Status ★

This charter operates at THREE distinct semantic layers, which must remain
separately labelled at every subsequent stage (Lean, paper, communication):

**Layer 1 — Lean mathematics.** Purely type-theoretic definitions and
theorems about a proposed observable on complex matrix algebras. No physical
or experimental claim. Verifiable within `[propext, Classical.choice, Quot.sound]`.

**Layer 2 — EEG measurement map.** A separately declared hypothesis that the
Lean-defined observable can be estimated from EEG-derived reduced density
matrices via a specific measurement protocol (ch32 style). This layer is
NOT proven in Lean; it is a stated bridge between the mathematical object
and instrument data.

**Layer 3 — Consciousness interpretation.** A separately declared hypothesis
that the observable, so measured, correlates with (or discriminates between)
preregistered conscious and unresponsive experimental conditions. This layer
is NOT proven in Lean. It is a falsifiable empirical claim.

At no point may Layer 3 be represented as a Lean theorem. At no point may
Layer 2 be represented as a Lean theorem. Only Layer 1 is Lean-provable.
Any communication about this arc that conflates layers is a violation of
this charter and must be corrected.

## §1. What the book contains (verified read, 2026-09-12)

Chapter 6 (`ch06_consciousness.tex`, 723 lines):
- **Reduced density matrix / partial trace** (Ch06:515-519):
  `ρ_A = Tr_B(|ψ⟩⟨ψ|)` on a generic bipartite composite `ℋ = ℋ_A ⊗ ℋ_B`.
- **Linear entropy identified with ch₂** (Ch06:517):
  `ch₂(|ψ⟩) = 1 − Tr(ρ_A²)`. The book uses `ch₂` for the linear entropy
  of the reduced state.
- **EEG-derived ch₂ ≥ 0.95 during conscious states** (Ch06:680),
  labelled "EMPIRICAL HYPOTHESIS awaiting independent experimental
  validation" (Ch06:691). NOT a proven claim.
- **Open research problem** (Ch06:708):
  "Derive the differential equation for consciousness evolution:
   `d/dt ch₂(t) = ?`"
  — explicit acknowledgment that the temporal law is not yet formulated.
- **Consciousness sheaf 𝒮_𝒞** (Ch06:87-112): Čech cohomology on an open
  cover of the substrate; ch₂ is the Chern invariant of this sheaf; the
  binding problem is resolved by the sheaf gluing conditions. This is
  the Grothendieck local-to-global machinery on the spine.

Chapter 8 (`ch08_field_equations.tex`, 540 lines):
- Field equations with consciousness coupling (structural). No time
  derivative of ch₂ appears.

Chapter 32 (`ch32_consciousness_quantification.tex`, 850 lines):
- Full EEG-based ch₂ measurement protocol (Ch32:65+): channels, band
  selection, reduced-density-matrix estimation procedure.
- No Frobenius-difference observable appears.

**What the book does NOT contain (verified):**
- The formula `χ_k(t) = ½ · ‖ρ_{t+1} − ρ_t‖²_F`.
- Any Frobenius-squared distance on density-matrix differences (with
  any coefficient).
- The word "churn" in an operational-observable sense.
- Ternary Hilbert spaces `H_k = ℂ^{3^k}` in the consciousness context.
  The book uses generic bipartite `ℋ_A ⊗ ℋ_B`.
- Any generic Hilbert-Schmidt contraction claim under partial trace.

## §2. What is proposed (NEW operationalization)

We propose the **Frobenius churn observable** as a new operationalization
of the open problem at Ch06:708, motivated by (but not recovered from)
book ingredients:

```
χ_k(ρ, σ) := (1/2) · ‖ρ − σ‖²_F        on   H_k := ℂ^{3^k}
```

where `ρ, σ` are density matrices (unit-trace positive Hermitian) on the
ternary Hilbert space `H_k`. Applied temporally,
`χ_k(t) := χ_k(ρ(t+1), ρ(t))`. The name "χ_k" foregrounds the k-dependence
(refinement level) matching the substrate's ternary tower from
`PF/SubstrateRigidity.lean:T_infinity_rigidity`.

### Two intentional deviations from book text

**Deviation 1 — ternary Hilbert space choice.** The book uses generic
bipartite `ℋ_A ⊗ ℋ_B` for the consciousness ch₂. The proposed observable
uses `H_k = ℂ^{3^k}` from ch04's Timeless Field substrate. This is a
DELIBERATE choice — it places the observable on the tree's already-proven
ternary substrate (kernel-verified via `T_infinity_rigidity`, commit
`22cb48e2`) rather than on the abstract bipartite space. The consequence:
theorems about χ_k are theorems on the substrate levels, immediately
compatible with the ternary Timeless Field. The cost: the observable is
not literally the book's ch₂ context; it is a substrate-level cousin.

**Deviation 2 — Frobenius squared vs linear-entropy language.** The book's
`ch₂ = 1 - Tr(ρ²)` is a *single-state* invariant. The proposed χ_k is a
*two-state* distance. The relationship (via the identity
`‖ρ - σ‖²_F = Tr(ρ²) + Tr(σ²) - 2·Tr(ρσ)`) is mathematical but not
verbally book-content.

Both deviations should be surfaced in the file docstring, in the paper,
and in any communication.

## §3. Lean charter (Layer 1 only)

Target file: `PF/Consciousness/FrobeniusChurn.lean` (name to verify no
collision at implementation time; survey step at start of implementation
will grep for existing `FrobeniusChurn`, `chi_k`, `churn` identifiers).

### §3.1 Definitions (matrix-algebra formulation)

Work over `Matrix (Fin (3^k)) (Fin (3^k)) ℂ` for `k : ℕ`. Take `ρ, σ : ℂ`-valued
matrices of that shape; no need to formalize a `DensityMatrix` predicate
initially — the theorems below hold for arbitrary Hermitian matrices and
the density-matrix specialization is a labelling.

```lean
/-- **Frobenius churn** between two matrices on the ternary level `H_k`. -/
noncomputable def churnFrobenius {k : ℕ}
    (ρ σ : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) : ℝ :=
  (1/2) * ‖ρ - σ‖²  -- Frobenius = Euclidean = HS norm on finite matrices
```

Use `Matrix.frobeniusNormedAddCommGroup` (or equivalent) for the Frobenius
norm. The `‖·‖²` here is the squared Frobenius norm.

### §3.2 Theorems Layer 1 aims to prove (mathematically valid ONLY)

**T1 — Nonnegativity.** `∀ ρ σ, 0 ≤ churnFrobenius ρ σ`.
Proof: `(1/2) * ‖·‖² ≥ 0` from `sq_nonneg`.

**T2 — Symmetry.** `∀ ρ σ, churnFrobenius ρ σ = churnFrobenius σ ρ`.
Proof: `‖ρ - σ‖ = ‖-(σ - ρ)‖ = ‖σ - ρ‖`.

**T3 — Zero iff equality.** `churnFrobenius ρ σ = 0 ↔ ρ = σ`.
Proof: `‖x‖² = 0 ↔ x = 0` (norm-definiteness); the (1/2) coefficient
is nonzero.

**T4 — Unitary invariance.**
`∀ U : unitary_group, churnFrobenius (U ρ U†) (U σ U†) = churnFrobenius ρ σ`.
Proof: unitary conjugation preserves the Frobenius inner product;
`‖U(ρ - σ)U†‖_F = ‖ρ - σ‖_F`.

**T5 — Pure-ancilla refinement/recovery invariance.**
For a fixed pure ancilla state `|0⟩⟨0| : Matrix (Fin (3^m)) (Fin (3^m)) ℂ`,
```
churnFrobenius (ρ ⊗ |0⟩⟨0|) (σ ⊗ |0⟩⟨0|) = churnFrobenius ρ σ
```
Proof: `‖A ⊗ P‖²_F = ‖A‖²_F · ‖P‖²_F`; for `P = |0⟩⟨0|`, `‖P‖²_F = 1`.

**IMPORTANT NON-TARGET.** We do NOT claim generic Hilbert-Schmidt
contraction under partial trace, i.e., NOT
`churnFrobenius (Tr_B(ρ ⊗ B)) (Tr_B(σ ⊗ B')) ≤ churnFrobenius ρ σ`
for arbitrary `B, B'`. That statement is false without additional
hypotheses. Only the **pure-ancilla** case (T5) is claimed.

### §3.3 Mathlib dependencies to verify at implementation

- `Matrix.frobeniusNormedAddCommGroup` or similar norm instance on
  `Matrix (Fin n) (Fin n) ℂ`.
- Unitary group / conjugation infrastructure.
- Tensor product of matrices with the norm identity `‖A ⊗ B‖ = ‖A‖ · ‖B‖`.
- Pure-state projector `|0⟩⟨0|` construction; verify `‖|0⟩⟨0|‖_F² = 1`.

These are standard finite-dimensional linear algebra; mathlib should have
all of them or their obvious composites. If any is missing, the
implementation-time survey (per the standing rule) surfaces it before
writing code.

### §3.4 In-file audit block

Per `build-tree-discipline` (R_f arc precedent, `FractalResonance.lean:§10`):
- `#print axioms` for every principal declaration.
- All must audit to subsets of `[propext, Classical.choice, Quot.sound]`.
- Zero project axioms, zero `sorry`, zero `native_decide`.

## §4. Layer 2 (EEG measurement map) — NOT LEAN

Encoded as a separate document (`codex/CHURN_CHI_K_EEG_LAYER.md`, to be
drafted after Layer 1 lands), specifying:

- Given an EEG recording, the estimation procedure for `ρ(t)` on `H_k`
  at level `k`.
- The choice of `k` (channels grouped ternarily, per ch32 protocol).
- The measurement noise model.
- The temporal resolution constraint (`Δt` between samples).

This document is a bridge specification, NOT a Lean theorem. Its correctness
is an empirical hypothesis, not a theorem.

## §5. Layer 3 (consciousness interpretation) — NOT LEAN

Encoded as a preregistered experimental protocol (`codex/CHURN_CHI_K_PROTOCOL.md`,
to be drafted after Layers 1 and 2 stabilise), specifying:

- Preregistered hypotheses about χ_k(t) in conscious vs unresponsive
  conditions.
- Effect-size predictions.
- Sample-size / power calculations.
- Pre-committed analysis pipeline.
- Falsification thresholds — what pattern would cause the hypothesis to
  be rejected.

The purpose of Layer 3 is to make the observable falsifiable. Without a
preregistered protocol, the observable is undecidable in practice.

## §6. Deviations from ChatGPT's original sketch

ChatGPT's sketch proposed:

> `χ_k(t) = ½ ‖ρ_{t+1} - ρ_t‖²_F, H_k = ℂ^{3^k}`
>
> Lean can prove it is nonnegative, symmetric, zero precisely when no
> change occurred, invariant under unitary changes of coordinates, and
> compatible with the existing partial-trace/refinement machinery.

This charter adopts the definition and the first four properties (T1-T4
in §3.2) verbatim.

**On the fifth ChatGPT property ("compatible with the existing
partial-trace/refinement machinery")**: this charter narrows it to
**pure-ancilla refinement/recovery invariance** (T5) — the sharp
statement that is actually true. Generic partial-trace contraction is
NOT claimed; that statement is false or requires additional hypotheses
that Layer 1 does not fix.

**On the causal-spine placement**: ChatGPT's proposal targets the
"Timeless Field → churn" arrow. This charter accepts that placement
while flagging (§2 Deviation 1) that the substrate-level ternary
choice `H_k = ℂ^{3^k}` diverges from the book's consciousness-context
generic bipartite. The divergence is an intentional design choice
placing the observable on the kernel-verified substrate rather than
on the paper-only bipartite abstraction.

## §7. Charter stopping conditions

Implementation MUST pause and reconsult if any of the following:

- Any mathlib dependency in §3.3 turns out to be missing and its
  construction would exceed 100 lines of scaffolding.
- The pure-ancilla invariance (T5) turns out to require the ancilla
  to be normalised or Hermitian in ways the trivial `|0⟩⟨0|` doesn't
  satisfy (edge case check).
- Any Layer 1 theorem cannot be proven without importing Layer 2 or 3
  content — this would be a category error and the theorem must be
  reformulated or dropped.
- The Frobenius norm on complex matrices has a mathlib convention
  (real vs complex inner product) that changes the coefficient of T5.

## §8. Ready-state for implementation

- Charter committed to `codex/CHURN_CHI_K_CHARTER_2026-09-12.md`.
- Survey findings committed in commit message.
- Explicit approval required before writing `PF/Consciousness/FrobeniusChurn.lean`.
- Estimated Layer 1 scope: 150-250 lines including audit block.
- Ceiling: 1 session for Layer 1. Layers 2 and 3 are separate documents
  drafted later.

*Charter opened 2026-09-12 after book-verified survey of ch06/ch08/ch32.
Epistemic-layer separation is enforced at every stage. Awaits explicit
approval before implementation.*
