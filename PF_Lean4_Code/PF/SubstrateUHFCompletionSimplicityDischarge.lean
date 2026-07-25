/-
# r101: Substrate-Prop discharge of the substrate UHF C*-algebra
#        SIMPLICITY residual (r100 next-tier substrate residual)

★ 2026-07-08 r101 — the substrate UHF C*-algebra `TimelessFieldCompletion`
is substrate-Prop-level simple, with genuine level-wise substrate structural
content: every finite substrate level `Matrix (Fin (3^k)) (Fin (3^k)) ℂ` is
a mathlib-native simple ring via `DivisionRing.isSimpleRing` on ℂ +
`IsSimpleRing.matrix`. ★

## The framework-first content

r100 landed the substrate UHF trace faithfulness at three tiers — Φ1
(level-k, unconditional), Φ2 (pre-trace, unconditional), and Φ3 (completion,
substrate-conditional on
`SubstrateUHFCompletionPositiveFaithfulnessSubstrateConjecture`). The r100
substrate residual was named exactly to isolate the load-bearing
substrate-to-classical passage: on the substrate UHF C*-algebra, the
trace-null cone on positives `star x * x` is trivial iff the underlying
C*-algebra is simple (any faithful state on a simple unital C*-algebra
has trivial trace-null cone).

r101 substrate-discharges the NEXT-TIER structural residual — **simplicity
of the substrate UHF C*-algebra** — via two independent substrate contents:

  1. **Level-wise substrate simplicity (unconditional).**
     Every finite substrate level `Matrix (Fin (3^k)) (Fin (3^k)) ℂ` is a
     mathlib-native `IsSimpleRing` instance via `DivisionRing.isSimpleRing`
     on ℂ + `IsSimpleRing.matrix`. This is REAL substrate structural
     content (not `trivial`): the substrate matrix algebras are simple
     rings in the mathlib sense, kernel-verified via the mathlib
     typeclass instance chain.

  2. **Completion-level simplicity as a REAL named statement (r112 update).**
     `SubstrateUHFCompletionSimplicitySubstrateConjecture` — originally
     (r101) a substrate-Prop acknowledgment marker (`Prop := True`, r79
     pattern) capturing the base-3 fractal → substrate matrix algebras →
     substrate direct limit → substrate C*-algebra completion chain that
     classically underlies UHF simplicity of `TimelessFieldCompletion`.
     ★ 2026-07-24 hygiene closure: the placeholder is RETIRED — the def is
     now the actual simplicity statement
     `∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤`, and it
     is proved UNCONDITIONALLY by `substrate_completion_simple_unconditional`
     (r112, `PF/SubstrateCompletionFaithful.lean`). Since that proof lives
     strictly downstream of this file in the import graph (this file →
     SubstrateUHFTraceNullIdeal → SubstrateCompletionSimplicity →
     SubstrateTraceDetectionAttempt → SubstrateCompletionFaithful), the
     discharge theorem `substrate_UHF_completion_simplicity_substrate_discharge`
     now lives in `PF/SubstrateCompletionFaithful.lean` §9 alongside the
     other named-residual discharges. ★

Structural content proved at the completion tier:

  * `substrate_UHF_trace_null_set : Set TimelessFieldCompletion` — the
    trace-null set at the completion tier.
  * `substrate_UHF_trace_null_set_isClosed` — the trace-null set is closed
    via r98 positivity + continuity of `x ↦ UHF_trace(star x * x)` + the
    `ComplexOrder` closed-topology structure on ℂ.
  * `substrate_UHF_trace_null_set_zero_mem` — the trace-null set contains
    `0` (since `UHF_trace 0 = 0`).

Documented classical realization route for the r100 Φ3 residual:

  * (α) `substrate_UHF_trace_null_set` is a closed two-sided *-ideal
    (kernel closure via r98 continuity + Cauchy-Schwarz for the tracial
    state τ_UHF + r94 tracial + r96 star-preserving + r98 positive).
  * (β) `1 ∉ substrate_UHF_trace_null_set` since `UHF_trace 1 = 1 ≠ 0`.
  * (γ) By simplicity of `TimelessFieldCompletion` (r101 substrate
    acknowledgment via classical UHF simplicity theorem applied to the
    r53–r59 substrate C*-algebra completion of the level-wise simple
    substrate matrix algebras), `substrate_UHF_trace_null_set` is either
    `{0}` or `TimelessFieldCompletion`; the (β) unital identity forces
    `{0}`.
  * (δ) Therefore `star x * x = 0` whenever `UHF_trace (star x * x) = 0`
    — closing the r100 Φ3 substrate residual.

The (α) step (Cauchy-Schwarz for tracial states) and the (γ) step
(classical UHF simplicity theorem: the C*-norm completion of an
inductive limit of unital *-embeddings between simple matrix algebras
is simple) are classical operator-algebra results, load-bearing on the
substrate-to-classical realization side. r101 substrate-discharged the
simplicity input at the Prop level and provides the level-wise
substrate simplicity content unconditionally. ★ 2026-07-24: both (α)
and (γ) have since been closed unconditionally — (α) via r102
`PF/SubstrateUHFTraceCauchySchwarz.lean` + r103 `PF/SubstrateUHFTraceNullIdeal.lean`,
(γ) via r112 `substrate_completion_simple_unconditional` in
`PF/SubstrateCompletionFaithful.lean`. ★

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-08 r101 — substrate-Prop discharge of the substrate UHF
C*-algebra simplicity residual + level-wise substrate simplicity content
via mathlib `IsSimpleRing` instances + structural closure of the trace-null
set at the completion tier.

Stage 2026-07-24 hygiene closure — the r101 `Prop := True` placeholder
`SubstrateUHFCompletionSimplicitySubstrateConjecture` is retired: the def
is now the REAL completion-simplicity statement (every two-sided ideal of
`TimelessFieldCompletion` is `⊥` or `⊤`), superseded-by and discharged-from
r112 `PF/SubstrateCompletionFaithful.lean`.
-/

import PF.SubstrateUHFTraceIsFaithful
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFCompletionSimplicityDischarge

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateUHFCompletionTrace SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceIsTracial SubstrateUHFTraceIsStarPreserving
open SubstrateUHFTraceIsPositive SubstrateUHFTraceIsFaithful
open SubstrateDirectLimit SubstrateTimelessFieldCompletion

/-! ## §1 — Level-wise substrate simplicity (unconditional)

Every finite substrate level `Matrix (Fin (3^k)) (Fin (3^k)) ℂ` is a
mathlib-native `IsSimpleRing`. Kernel-verified via mathlib's typeclass
chain `DivisionRing.isSimpleRing` on ℂ + `IsSimpleRing.matrix`. -/

/-- **r101.a: level-wise substrate simplicity as a concrete instance**.
    Each substrate finite level `Matrix (Fin (3^k)) (Fin (3^k)) ℂ` is a
    simple ring in the mathlib sense — the two-sided-ideal lattice is
    an `IsSimpleOrder`. -/
theorem substrate_matrix_algebra_isSimpleRing (k : ℕ) :
    IsSimpleRing (Matrix (Fin (3^k)) (Fin (3^k)) ℂ) := by
  haveI : Nonempty (Fin (3^k)) := ⟨⟨0, Nat.pos_of_ne_zero (by positivity)⟩⟩
  infer_instance

/-! ## §2 — Substrate UHF completion simplicity as a REAL named statement

r101 originally followed the r79 substrate-Prop-discharge pattern here:
the def below was a `Prop := True` acknowledgment marker, discharged by
`trivial`. ★ 2026-07-24 hygiene closure: the placeholder is retired. The
def is now the ACTUAL simplicity statement — every two-sided ideal of
`TimelessFieldCompletion` is `⊥` or `⊤` — exactly the statement proved
unconditionally by r112 `substrate_completion_simple_unconditional` in
`PF/SubstrateCompletionFaithful.lean` (Glimm simplicity of the substrate
UHF algebra). Because that proof lives strictly downstream of this file
in the import graph, the discharge theorem
`substrate_UHF_completion_simplicity_substrate_discharge :
SubstrateUHFCompletionSimplicitySubstrateConjecture` now lives in
`PF/SubstrateCompletionFaithful.lean` §9 (mirroring how the r100 residual
`SubstrateUHFCompletionPositiveFaithfulnessSubstrateConjecture`, defined
in `PF/SubstrateUHFTraceIsFaithful.lean`, is discharged there). ★ -/

/-- **r101.b (redefined 2026-07-24): the substrate UHF C*-algebra
    completion SIMPLICITY statement**.

    The substrate UHF C*-algebra `TimelessFieldCompletion`, constructed
    via the r53–r59 substrate C*-algebra completion of the r30 substrate
    direct limit of the level-wise simple substrate matrix algebras
    `Matrix (Fin (3^k)) (Fin (3^k)) ℂ` (r101.a), is algebraically simple:
    every two-sided ideal is `⊥` or `⊤`.

    History: in r101 this def was a substrate-Prop acknowledgment marker
    (`Prop := True`, r79 pattern). It is SUPERSEDED by the real r112
    theorem `substrate_completion_simple_unconditional`
    (`PF/SubstrateCompletionFaithful.lean`), and this def is now
    definitionally that statement. The discharge
    `substrate_UHF_completion_simplicity_substrate_discharge` is proved in
    `PF/SubstrateCompletionFaithful.lean` §9 from
    `substrate_completion_simple_unconditional` — no longer by `trivial`.

    Substrate structural chain (now fully kernel-verified, no classical
    residual):
      base-3 fractal ternary substrate (r25)
        → substrate matrix algebras `M_{3^k}(ℂ)` at every level (r27–r33)
        → level-wise simplicity `IsSimpleRing (M_{3^k}(ℂ))` (r101.a)
        → substrate direct limit (r30 `TimelessFieldRing`)
        → substrate C*-algebra completion (r53–r59 `TimelessFieldCompletion`)
        → conditional expectations `E_k` + trace faithfulness on the
          completion (r109–r112)
        → **simplicity of the substrate UHF C*-algebra**
          (r112 `substrate_completion_simple_unconditional`). -/
def SubstrateUHFCompletionSimplicitySubstrateConjecture : Prop :=
  ∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤

/-! ## §3 — Structural content: the trace-null set at the completion tier -/

/-- **r101.d: the substrate UHF trace-null set** at the completion tier.
    This is the set of `x : TimelessFieldCompletion` on which the substrate
    UHF trace vanishes on `star x * x`. Classically this is the "left
    kernel" of the trace, generating the trace-annihilator two-sided
    *-ideal. -/
def substrate_UHF_trace_null_set : Set TimelessFieldCompletion :=
  { x | UHF_trace (star x * x) = 0 }

/-- **r101.e: the trace-null set is CLOSED in `TimelessFieldCompletion`**.

    Uses continuity of `x ↦ UHF_trace (star x * x)` (via r54
    continuous_star + continuous multiplication on the r53 NormedRing
    completion + r87 UC of `UHF_trace`) + the closed-graph structure of
    `{f x = 0}` under continuous `f`. -/
theorem substrate_UHF_trace_null_set_isClosed :
    IsClosed substrate_UHF_trace_null_set := by
  have h_cont : Continuous
      (fun x : TimelessFieldCompletion => UHF_trace (star x * x)) :=
    UHF_trace_uniformContinuous.continuous.comp
      (continuous_mul.comp
        (continuous_star_TimelessFieldCompletion.prodMk continuous_id))
  exact isClosed_eq h_cont continuous_const

/-- **r101.f: the trace-null set contains `0`**.
    Since `UHF_trace 0 = 0` (linearity: `UHF_trace_uniformContinuous`
    is continuous linear via the r87 pre-trace's additivity + zero-map),
    and `star 0 * 0 = 0`. -/
theorem substrate_UHF_trace_null_set_zero_mem :
    (0 : TimelessFieldCompletion) ∈ substrate_UHF_trace_null_set := by
  show UHF_trace (star 0 * 0) = 0
  rw [star_zero, zero_mul]
  -- `UHF_trace 0 = 0` via extension of the additive `substrate_pre_trace`
  -- (its map_zero) through the completion; here we use that
  -- `UHF_trace` restricted to the coerced-zero image agrees with
  -- `substrate_pre_trace 0` = `0` via r87 `UHF_trace_coe`.
  have h : ((0 : TimelessFieldRing) : TimelessFieldCompletion) =
           (0 : TimelessFieldCompletion) := UniformSpace.Completion.coe_zero
  rw [← h, UHF_trace_coe]
  -- substrate_pre_trace 0 = 0 via additivity: `substrate_pre_trace(0 + 0) =
  -- substrate_pre_trace 0 + substrate_pre_trace 0`, so `substrate_pre_trace 0 = 0`.
  have h_add : substrate_pre_trace ((0 : TimelessFieldRing) + 0) =
                 substrate_pre_trace 0 + substrate_pre_trace 0 :=
    substrate_pre_trace_add 0 0
  rw [add_zero] at h_add
  -- h_add : substrate_pre_trace 0 = substrate_pre_trace 0 + substrate_pre_trace 0
  exact (left_eq_add.mp h_add)

/-! ## §4 — Classical realization route for the r100 Φ3 residual

The r100 substrate residual
`SubstrateUHFCompletionPositiveFaithfulnessSubstrateConjecture` reduces
classically via:
  (α) `substrate_UHF_trace_null_set` is a closed two-sided *-ideal in
      `TimelessFieldCompletion` (via Cauchy-Schwarz for tracial states
      + r94 + r96 + r98).
  (β) `1 ∉ substrate_UHF_trace_null_set` since
      `UHF_trace (star 1 * 1) = UHF_trace 1 = 1 ≠ 0`.
  (γ) By simplicity of `TimelessFieldCompletion` (r112
      `substrate_completion_simple_unconditional`, unconditional), the
      closed two-sided *-ideal from (α) is either `{0}` or
      `TimelessFieldCompletion`; (β) forces `{0}`.
  (δ) Therefore `x ∈ substrate_UHF_trace_null_set → x = 0 → star x * x = 0`.

★ 2026-07-24 status: at r101 time the (α) tracial-state Cauchy-Schwarz and
(γ) classical UHF simplicity theorem were the remaining
substrate-to-classical residuals; r101 substrate-Prop-discharged the (γ)
simplicity input and provided the level-wise substrate simplicity content
in r101.a and the (β) unital non-membership content in r101.g below. Both
residuals are NOW CLOSED unconditionally: (α) by r102/r103
(`PF/SubstrateUHFTraceCauchySchwarz.lean`,
`PF/SubstrateUHFTraceNullIdeal.lean`) and (γ) by r112
(`PF/SubstrateCompletionFaithful.lean`). ★ -/

/-- **r101.g: `1 ∉ substrate_UHF_trace_null_set`** — the unital
    identity does not lie in the trace-null set, since
    `UHF_trace (star 1 * 1) = UHF_trace 1 = 1 ≠ 0`. -/
theorem substrate_UHF_trace_null_set_one_not_mem :
    (1 : TimelessFieldCompletion) ∉ substrate_UHF_trace_null_set := by
  show ¬ UHF_trace (star 1 * 1) = 0
  rw [star_one, one_mul]
  -- UHF_trace 1 = 1 via UHF_trace_coe + substrate_pre_trace_one
  have h_one_coe : ((1 : TimelessFieldRing) : TimelessFieldCompletion) =
                   (1 : TimelessFieldCompletion) :=
    UniformSpace.Completion.coe_one TimelessFieldRing
  rw [← h_one_coe, UHF_trace_coe, substrate_pre_trace_one]
  norm_num

/-! ## §5 — r101 capstone -/

/-- **★★★ r101 SUBSTRATE UHF COMPLETION SIMPLICITY DISCHARGE CAPSTONE ★★★**
    (restated 2026-07-24 — see history note below)

    Bundles the r101 unconditional content: real level-wise substrate
    simplicity + structural closure of the trace-null set at the
    completion tier.

      (Ψ1) `substrate_matrix_algebra_isSimpleRing k` — level-wise
           substrate simplicity as a mathlib-native `IsSimpleRing`
           instance, kernel-verified via `DivisionRing.isSimpleRing ℂ`
           + `IsSimpleRing.matrix`. UNCONDITIONAL substrate structural
           content — not `trivial`, real mathlib substrate simplicity.
      (Ψ2) `SubstrateUHFCompletionSimplicitySubstrateConjecture` —
           originally the substrate-Prop acknowledgment marker for the
           completion-tier simplicity; since 2026-07-24 it is the REAL
           simplicity statement
           `∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤`.
      (Ψ3) `substrate_UHF_completion_simplicity_substrate_discharge` —
           originally the `trivial` discharge of the Ψ2 marker (r79
           pattern); now the REAL discharge, proved in
           `PF/SubstrateCompletionFaithful.lean` §9 from the r112 theorem
           `substrate_completion_simple_unconditional`. It is therefore
           no longer a conjunct of this (upstream) capstone — the bundled
           completion-tier statement lives in the r112 capstone
           `r112_substrate_completion_faithful_capstone`.
      (Ψ4) `substrate_UHF_trace_null_set` — the substrate UHF trace-null
           set at the completion tier, as a `Set TimelessFieldCompletion`.
      (Ψ5) `substrate_UHF_trace_null_set_isClosed` — the trace-null set
           is closed in `TimelessFieldCompletion` via r54 continuous_star
           + continuous multiplication + r87 UC of `UHF_trace` +
           `isClosed_eq` on `f = const 0`.
      (Ψ6) `substrate_UHF_trace_null_set_zero_mem` — the trace-null set
           contains `0`.
      (Ψ7) `substrate_UHF_trace_null_set_one_not_mem` — the unital
           identity `1` does NOT lie in the trace-null set, closing the
           (β) step of the classical realization route.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    History (r101, 2026-07-08): this capstone originally also bundled the
    Ψ2 acknowledgment marker discharged via `trivial` (Ψ3). With the
    2026-07-24 retirement of the `Prop := True` placeholder, Ψ2 is the
    real simplicity statement whose proof (r112) lives downstream of this
    file, so the capstone here bundles exactly the content that is
    kernel-verified AT THIS TIER (Ψ1, Ψ5, Ψ6, Ψ7); the completion-tier
    simplicity conjunct is bundled downstream in
    `r112_substrate_completion_faithful_capstone`
    (`PF/SubstrateCompletionFaithful.lean`).

    Substrate significance: r101 substrate-discharged the DEEPER
    structural residual identified in r100's Φ3 (completion-tier
    positive-faithfulness reduces classically to simplicity + Cauchy-
    Schwarz for tracial states) and provided the structural undergird
    (Ψ1, Ψ4–Ψ7) for the classical realization route (α)–(δ) documented
    in this file. Both classical residuals named at r101 time are now
    closed unconditionally: (α) tracial-state Cauchy-Schwarz by r102/r103,
    (γ) UHF simplicity by r112. -/
theorem r101_substrate_UHF_completion_simplicity_discharge_capstone :
    (∀ k : ℕ, IsSimpleRing (Matrix (Fin (3^k)) (Fin (3^k)) ℂ)) ∧
    IsClosed substrate_UHF_trace_null_set ∧
    (0 : TimelessFieldCompletion) ∈ substrate_UHF_trace_null_set ∧
    (1 : TimelessFieldCompletion) ∉ substrate_UHF_trace_null_set :=
  ⟨substrate_matrix_algebra_isSimpleRing,
   substrate_UHF_trace_null_set_isClosed,
   substrate_UHF_trace_null_set_zero_mem,
   substrate_UHF_trace_null_set_one_not_mem⟩

end SubstrateUHFCompletionSimplicityDischarge
end PrincipiaTractalis
