/-
# r108: Substrate UHF COMPLETION-TIER trace-detection — the M3.3 SUMMIT attempt

★ 2026-07-22 r108 — an assault on `SubstrateCompletionTraceDetectsIdeals`,
the last hypothesis gating UNCONDITIONAL completion-tier faithfulness of
the substrate UHF trace (r106). ★

## What r108 establishes (all UNCONDITIONAL, kernel-only)

The r106 development reduced completion-tier faithfulness of `τ_UHF` to a
single named hypothesis

    `SubstrateCompletionTraceDetectsIdeals :=
       ∀ I : TwoSidedIdeal T∞, I ≠ ⊥ → ∃ x ∈ I, τ_UHF x ≠ 0`,

proving `SubstrateCompletionTraceDetectsIdeals → faithfulness` via the
averaging + Neumann engine. r108 asks whether trace-detection can itself
be discharged. The honest answer, PROVED here, is a sharp EQUIVALENCE:

**★ THE CENTRAL r108 EQUIVALENCE ★** — for the substrate UHF completion
`T∞`, the following four statements are UNCONDITIONALLY equivalent:

  (1) `SubstrateCompletionTraceDetectsIdeals`  (trace-detection of ideals)
  (2) `traceNullTwoSidedIdeal = ⊥`             (the trace-null ideal is trivial)
  (3) `∀ x, τ_UHF (x⋆ x) = 0 → x = 0`          (faithfulness of `τ_UHF`)
  (4) `∀ I : TwoSidedIdeal T∞, I = ⊥ ∨ I = ⊤`  (algebraic simplicity of `T∞`)

The cycle is closed with fully kernel-verified steps:

    (4) → (3)   `UHF_trace_faithful_of_simple`                (r103)
    (3) → (2)   `traceNull_eq_bot_of_faithful`                (r108, new)
    (2) → (1)   `traceDetects_of_traceNull_eq_bot`            (r108, new)
    (1) → (4)   `completion_twoSidedIdeal_bot_or_top_of_traceDetects` (r106)

**The consequence for the SUMMIT.** This is the precise, honest
obstruction map. It shows that the r106 hypothesis
`SubstrateCompletionTraceDetectsIdeals` is NOT strictly weaker than the
goal it was meant to unlock: it is LOGICALLY EQUIVALENT to faithfulness
itself (and to Glimm simplicity of the completion). Hence trace-detection
cannot be discharged by any argument genuinely weaker than a proof of
faithfulness/simplicity — the classical hard input (Glimm 1960) is really
required, and no "cheaper" hypothesis will do. This settles the status of
r106's residual: it is exactly the mountain, restated.

## The projection route (Route A), and where it stalls

We additionally formalize the classical spectral-projection route and
pin down EXACTLY the two walls it hits, using the PR-3 spectral
projection API (`CStarAlgebra.spectralProjection`):

  * `exists_ne_zero_mem_quasispectrum` — UNCONDITIONAL: a nonzero
    selfadjoint element has a nonzero quasispectral value (via `cfcₙ_id`).
    So the *spectral value* always exists.
  * `TraceDetectsProjections` — the named residual (WALL B): every nonzero
    projection has nonzero trace. UNCONDITIONALLY IMPLIED BY faithfulness
    (`traceDetectsProjections_of_faithful`), confirming it too is
    equivalent, not weaker.
  * `traceDetects_closed_of_projTrace_finiteSpectrum` — the conditional
    Route-A close for a CLOSED ideal possessing a finite-quasispectrum
    witness: `TraceDetectsProjections` + such a witness ⇒ detection.

This exhibits the two independent obstacles of Route A explicitly:

    (i)  **finite-quasispectrum supply** — `Finite (quasispectrum ℝ z)`
         holds for level (finite-matrix) elements but FAILS for a general
         element of the infinite UHF completion; and
    (iii) **the projection trace lower bound** (`TraceDetectsProjections`)
         — equivalent to faithfulness, so not independently reachable.

## The single critical-path missing layer

Neither wall is a mere lemma gap: both are discharged classically by the
**trace-preserving conditional expectation** `E_k : T∞ → M_{3^k}` (the
`ℓ²(τ)`-orthogonal projection onto the level-k corner), which is a
`‖·‖₂`-contraction with `E_k x → x`. From `E_k` one gets faithfulness
directly: `τ(x⋆x)=0 ⇒ ‖E_k x‖₂ = 0 ⇒ E_k x = 0` (matrix faithfulness)
`⇒ x = 0` (density). `E_k` is obstruction (ii) and is the TRUE critical
path: closing it alone closes all of (1)–(4). It is not in mathlib
(conditional expectations on inductive-limit C*-algebras are absent), so
the SUMMIT needs a substantial new mathlib-tier layer, not a bounded
patch.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project axioms.
Zero sorries.

Stage 2026-07-22 r108 — the trace-detection ⇔ faithfulness ⇔ simplicity
equivalence, the Route-A wall isolation, and the E_k critical-path
identification.
-/

import PF.SubstrateCompletionSimplicity
import PF.ForMathlib.ClopenSpectralProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateTraceDetectionAttempt

open scoped ComplexOrder
open SubstrateTimelessFieldCompletion
open SubstrateUHFBoundedTrace
open SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceNullIdeal
open SubstrateCompletionSimplicity

/-! ## §1 — The two new edges of the equivalence cycle -/

/-- **★ r108.a: FAITHFULNESS ⇒ the trace-null ideal is trivial ★**

    If `τ_UHF (x⋆ x) = 0 → x = 0` for all `x`, then
    `traceNullTwoSidedIdeal = ⊥`: every element of the trace-null ideal
    is trace-null (`mem_traceNullTwoSidedIdeal_iff`), hence zero. -/
theorem traceNull_eq_bot_of_faithful
    (hf : ∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0) :
    traceNullTwoSidedIdeal = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [TwoSidedIdeal.mem_bot]
  exact hf x ((mem_traceNullTwoSidedIdeal_iff x).mp hx)

/-- **★ r108.b: the trace-null ideal is trivial ⇒ TRACE-DETECTION ★**

    If `traceNullTwoSidedIdeal = ⊥`, then every nonzero two-sided ideal
    `I` contains an element of nonzero trace. Concretely: pick `0 ≠ y ∈ I`;
    then `x := y⋆ y ∈ I` (two-sided absorption) and `τ_UHF x ≠ 0`, since
    `τ_UHF (y⋆ y) = 0` would place `y` in the (now trivial) trace-null
    ideal, forcing `y = 0`. -/
theorem traceDetects_of_traceNull_eq_bot
    (h : traceNullTwoSidedIdeal = ⊥) :
    SubstrateCompletionTraceDetectsIdeals := by
  intro I hI
  -- I ≠ ⊥ yields a nonzero element.
  have hne : ∃ y, y ∈ I ∧ y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hI (le_antisymm (fun z hz => by
      rw [TwoSidedIdeal.mem_bot]; exact hcon z hz) bot_le)
  obtain ⟨y, hyI, hy0⟩ := hne
  refine ⟨star y * y, I.mul_mem_left _ _ hyI, ?_⟩
  intro hτ
  have hymem : y ∈ traceNullTwoSidedIdeal := (mem_traceNullTwoSidedIdeal_iff y).mpr hτ
  rw [h] at hymem
  exact hy0 ((TwoSidedIdeal.mem_bot _).mp hymem)

/-! ## §2 — ★★★ THE CENTRAL r108 EQUIVALENCE ★★★ -/

/-- **★★★ r108.c: TRACE-DETECTION ⇔ FAITHFULNESS ⇔ SIMPLICITY ⇔
    TRACE-NULL-TRIVIALITY ★★★**

    For the substrate UHF completion `T∞`, the four statements are
    UNCONDITIONALLY equivalent. The forward chain
    `(4)→(3)→(2)→(1)→(4)` uses r103 faithfulness-from-simplicity, the two
    new r108 edges, and the r106 averaging engine.

    This is the precise obstruction map: the r106 residual hypothesis is
    exactly faithfulness, not a weaker surrogate. -/
theorem traceDetects_tfae :
    List.TFAE
      [ SubstrateCompletionTraceDetectsIdeals,
        traceNullTwoSidedIdeal = ⊥,
        (∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0),
        (∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤) ] := by
  tfae_have 4 → 3 := UHF_trace_faithful_of_simple
  tfae_have 3 → 2 := traceNull_eq_bot_of_faithful
  tfae_have 2 → 1 := traceDetects_of_traceNull_eq_bot
  tfae_have 1 → 4 := completion_twoSidedIdeal_bot_or_top_of_traceDetects
  tfae_finish

/-- **r108.c′: the equivalence in explicit two-way form** — the two
    "headline" edges most useful downstream:
    trace-detection ⇔ faithfulness, and trace-detection ⇔ simplicity. -/
theorem traceDetects_iff_faithful :
    SubstrateCompletionTraceDetectsIdeals ↔
      (∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0) :=
  traceDetects_tfae.out 0 2

theorem traceDetects_iff_simple :
    SubstrateCompletionTraceDetectsIdeals ↔
      (∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤) :=
  traceDetects_tfae.out 0 3

theorem traceDetects_iff_traceNull_eq_bot :
    SubstrateCompletionTraceDetectsIdeals ↔ traceNullTwoSidedIdeal = ⊥ :=
  traceDetects_tfae.out 0 1

/-! ## §3 — Route A: the spectral-projection route and its two walls -/

/-- **r108.d (UNCONDITIONAL): a nonzero selfadjoint element has a nonzero
    quasispectral value.**

    If `σₙ ℝ z ⊆ {0}` then the identity and the zero function agree on
    `σₙ ℝ z`, so `z = cfcₙ id z = cfcₙ 0 z = 0` by the non-unital cfc.
    Contrapositive gives a nonzero `μ ∈ σₙ ℝ z`. This shows the *spectral
    value* Route A needs always exists — the wall is never "no spectral
    value", it is finiteness/isolation (wall i) and the trace bound
    (wall iii). -/
theorem exists_ne_zero_mem_quasispectrum {z : TimelessFieldCompletion}
    (hz : IsSelfAdjoint z) (hz0 : z ≠ 0) :
    ∃ μ ∈ quasispectrum ℝ z, μ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hz0
  have hEqOn : (quasispectrum ℝ z).EqOn (id : ℝ → ℝ) (0 : ℝ → ℝ) := by
    intro μ hμ
    simp only [id_eq, Pi.zero_apply]
    exact hcon μ hμ
  calc z = cfcₙ (id : ℝ → ℝ) z := (cfcₙ_id ℝ z).symm
    _ = cfcₙ (0 : ℝ → ℝ) z := cfcₙ_congr hEqOn
    _ = 0 := cfcₙ_zero ℝ z

/-- **r108.e: the named Route-A residual (WALL B) — trace-detection of
    projections.**

    Every nonzero projection (selfadjoint idempotent) of `T∞` has nonzero
    UHF trace. (By positivity `τ_UHF q = τ_UHF (q⋆ q) ≥ 0`, so this is a
    strict positivity `τ_UHF q > 0` statement.) -/
def TraceDetectsProjections : Prop :=
  ∀ q : TimelessFieldCompletion,
    IsSelfAdjoint q → IsIdempotentElem q → q ≠ 0 → UHF_trace q ≠ 0

/-- **r108.f: WALL B is IMPLIED BY faithfulness** — so it is not a strictly
    weaker foothold.

    If `q` is a nonzero projection, then `q = q⋆ q` (selfadjoint +
    idempotent), so `τ_UHF q = τ_UHF (q⋆ q)`; were this `0`, faithfulness
    would force `q = 0`. -/
theorem traceDetectsProjections_of_faithful
    (hf : ∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0) :
    TraceDetectsProjections := by
  intro q hq hqi hq0 hτ
  have hqsq : star q * q = q := by
    rw [hq.star_eq]; exact hqi
  apply hq0
  apply hf q
  rw [hqsq]; exact hτ

/-- **★ r108.g: the conditional Route-A close for a closed ideal with a
    finite-spectrum witness ★**

    Suppose the projection residual `TraceDetectsProjections` holds, and a
    CLOSED two-sided ideal `I` contains a nonzero selfadjoint element `z`
    whose quasispectrum is finite. Then `I` contains an element of nonzero
    trace.

    Proof (the classical spectral-projection argument, PR-3): a nonzero
    quasispectral value `μ ≠ 0` exists (r108.d); finiteness makes `{μ}`
    clopen, so `q := spectralProjection z {μ}` is a nonzero projection
    (`spectralProjection_singleton_ne_zero`) lying in the closed ideal `I`
    (`spectralProjection_mem`); `TraceDetectsProjections` gives
    `τ_UHF q ≠ 0`.

    The two hypotheses are EXACTLY Route A's two walls: `Finite
    (quasispectrum ℝ z)` (wall i — fails for general completion elements)
    and `TraceDetectsProjections` (wall iii — equivalent to faithfulness
    by r108.f). -/
theorem traceDetects_closed_of_projTrace_finiteSpectrum
    (hProj : TraceDetectsProjections)
    (I : TwoSidedIdeal TimelessFieldCompletion)
    (hIcl : IsClosed (I : Set TimelessFieldCompletion))
    (z : TimelessFieldCompletion) (hzI : z ∈ I)
    (hz : IsSelfAdjoint z) (hz0 : z ≠ 0)
    [Finite (quasispectrum ℝ z)] :
    ∃ x, x ∈ I ∧ UHF_trace x ≠ 0 := by
  -- `T∞` carries no *registered* C*-order instance; install the canonical
  -- spectral order locally so PR-3's `spectralProjection_mem` typechecks.
  letI : PartialOrder TimelessFieldCompletion := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing TimelessFieldCompletion := CStarAlgebra.spectralOrderedRing _
  obtain ⟨μ, hμσ, hμ0⟩ := exists_ne_zero_mem_quasispectrum hz hz0
  refine ⟨CStarAlgebra.spectralProjection z {μ}, ?_, ?_⟩
  · exact CStarAlgebra.spectralProjection_mem hIcl hzI {μ}
  · refine hProj _ (CStarAlgebra.isSelfAdjoint_spectralProjection z {μ})
      (CStarAlgebra.isIdempotentElem_spectralProjection
        (CStarAlgebra.isClopen_of_finite_quasispectrum {μ}) (by simpa using hμ0.symm))
      (CStarAlgebra.spectralProjection_singleton_ne_zero hz hμσ hμ0)

/-! ## §4 — r108 capstone -/

/-- **★★★ r108 SUBSTRATE TRACE-DETECTION EQUIVALENCE + ROUTE-A WALL
    ISOLATION CAPSTONE ★★★**

    Bundles the r108 content:

      (E1) **`traceDetects_tfae`** — the central equivalence:
           trace-detection ⇔ trace-null-triviality ⇔ faithfulness ⇔
           simplicity, UNCONDITIONALLY.
      (E2) **`traceDetects_iff_faithful`** — the sharpest reading: the
           r106 residual IS faithfulness, hence not strictly weaker.
      (A1) **`exists_ne_zero_mem_quasispectrum`** — the spectral value
           Route A needs always exists (unconditional).
      (A2) **`traceDetectsProjections_of_faithful`** — WALL B is implied
           by the very goal (so equivalent, not weaker).
      (A3) **`traceDetects_closed_of_projTrace_finiteSpectrum`** — the
           conditional Route-A close isolating walls (i) and (iii).

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r108 delivers the PRECISE obstruction map for
    the SUMMIT. `SubstrateCompletionTraceDetectsIdeals` is equivalent to
    completion faithfulness/simplicity; Route A's two walls are finite-
    quasispectrum supply and projection-trace positivity, both discharged
    classically only by the trace-preserving conditional expectation
    `E_k : T∞ → M_{3^k}` — the single critical-path layer absent from
    mathlib. -/
theorem r108_substrate_trace_detection_equivalence_capstone :
    List.TFAE
      [ SubstrateCompletionTraceDetectsIdeals,
        traceNullTwoSidedIdeal = ⊥,
        (∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0),
        (∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤) ] ∧
    (SubstrateCompletionTraceDetectsIdeals ↔
      (∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0)) ∧
    (∀ {z : TimelessFieldCompletion}, IsSelfAdjoint z → z ≠ 0 →
      ∃ μ ∈ quasispectrum ℝ z, μ ≠ 0) ∧
    ((∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0) →
      TraceDetectsProjections) :=
  ⟨traceDetects_tfae,
   traceDetects_iff_faithful,
   fun hz hz0 => exists_ne_zero_mem_quasispectrum hz hz0,
   traceDetectsProjections_of_faithful⟩

/-! ## §5 — Axiom audit -/

#print axioms traceNull_eq_bot_of_faithful
#print axioms traceDetects_of_traceNull_eq_bot
#print axioms traceDetects_tfae
#print axioms traceDetects_iff_faithful
#print axioms traceDetects_iff_simple
#print axioms traceDetects_iff_traceNull_eq_bot
#print axioms exists_ne_zero_mem_quasispectrum
#print axioms traceDetectsProjections_of_faithful
#print axioms traceDetects_closed_of_projTrace_finiteSpectrum
#print axioms r108_substrate_trace_detection_equivalence_capstone

end SubstrateTraceDetectionAttempt
end PrincipiaTractalis
