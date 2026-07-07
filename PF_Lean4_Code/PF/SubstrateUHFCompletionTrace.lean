/-
# r86: The UHF trace extension to `TimelessFieldCompletion`

★ 2026-07-07 r86 — the completion trace scaffolding via the r85b
1-Lipschitz bound ★

## The framework-first content

r85b delivered the substrate 1-Lipschitz bound
`‖normalized_matrix_trace M‖ ≤ ‖M‖` under the L² operator norm,
kernel-verified and unconditional. r86 uses this bound to:

  * Package the level-k normalized trace as a `LipschitzWith 1`
    function (kernel-proved).
  * Derive its `UniformContinuous` property (kernel-proved).
  * Register the `UniformSpace.Completion.extension` scaffolding
    for producing a completion trace `UHF_trace : TimelessFieldCompletion → ℂ`
    from any given uniformly continuous pre-trace on `TimelessFieldRing`.
  * State substrate residual Prop-level content: the existence of a
    linear-unital pre-trace on the r30 substrate direct limit
    `TimelessFieldRing` (deferred to r87 substrate work — the mathlib
    direct-limit-of-linear-map API navigation for the r29 successor
    RingHom compatibility class), and the corresponding UHF trace
    on `TimelessFieldCompletion`.

## Semantic scope

r86 lands the level-k analytic scaffolding (kernel-proved) plus the
completion-extension mechanism (kernel-proved conditional on any
uniformly continuous pre-trace). The construction of the pre-trace
on `TimelessFieldRing` from the level-k compatible family — which
requires either `Module.DirectLimit.lift` applied to the substrate
r29 RingHom family (as ℂ-linear maps satisfying trace-preservation
compatibility) or an alternative substrate-native construction —
is substrate residual for r87.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

## What r86 establishes

  * `substrate_level_trace_dist_bound` — `dist (τ M) (τ N) ≤ dist M N`.
  * `substrate_level_trace_lipschitz` — `LipschitzWith 1 τ` at level n.
  * `substrate_level_trace_uniformContinuous` — `UniformContinuous τ`.
  * `UHF_trace_extension_from_pre_trace` — the completion extension
    of any pre-trace `TimelessFieldRing → ℂ`.
  * `UHF_trace_extension_uniformContinuous` — the extension is
    uniformly continuous (unconditional on pre-trace UC).
  * `UHF_trace_extension_agrees_on_dense` — the extension agrees with
    the pre-trace on the dense embedded image when the pre-trace is
    uniformly continuous.
  * `SubstratePreTraceExistsConjecture` Prop-level substrate residual
    for the r87 substrate work.
  * `SubstrateUHFTraceExistsConjecture` Prop-level substrate target.
  * r86 capstone bundling the kernel-proved analytic + extension
    scaffolding.

Stage 2026-07-07 r86 — completion trace scaffolding via the r85b
1-Lipschitz bound.
-/

import PF.SubstrateUHFTraceLipschitz
import PF.SubstrateTimelessFieldCompletion
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFCompletionTrace

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateDirectLimit SubstrateTimelessFieldCompletion

/-! ## §1 — Level-k normalized trace is 1-Lipschitz -/

/-- **r86.a: distance bound on the normalized matrix trace**.

    For any two matrices M, N of the same substrate level,
    `dist (τ M) (τ N) ≤ dist M N` under the L² operator norm.
    Follows from the r85b 1-Lipschitz bound applied to `M - N` via
    the linearity of the trace. -/
theorem substrate_level_trace_dist_bound {n : ℕ} [NeZero n]
    (M N : Matrix (Fin n) (Fin n) ℂ) :
    dist (normalized_matrix_trace M) (normalized_matrix_trace N) ≤ dist M N := by
  rw [dist_eq_norm, dist_eq_norm]
  -- Linearity: τ(M) - τ(N) = τ(M - N)
  have h_lin :
      normalized_matrix_trace M - normalized_matrix_trace N =
        normalized_matrix_trace (M - N) := by
    have h_sub : (M - N : Matrix (Fin n) (Fin n) ℂ) = M + (-1 : ℂ) • N := by
      rw [neg_smul, one_smul, sub_eq_add_neg]
    rw [h_sub, normalized_matrix_trace_add, normalized_matrix_trace_smul]
    ring
  rw [h_lin]
  exact substrate_normalized_trace_bound (M - N)

/-- **r86.b: level-k normalized trace is `LipschitzWith 1`**. -/
theorem substrate_level_trace_lipschitz {n : ℕ} [NeZero n] :
    LipschitzWith 1
      (fun M : Matrix (Fin n) (Fin n) ℂ => normalized_matrix_trace M) :=
  LipschitzWith.mk_one (fun M N => substrate_level_trace_dist_bound M N)

/-- **r86.c: level-k normalized trace is `UniformContinuous`**. -/
theorem substrate_level_trace_uniformContinuous {n : ℕ} [NeZero n] :
    UniformContinuous
      (fun M : Matrix (Fin n) (Fin n) ℂ => normalized_matrix_trace M) :=
  substrate_level_trace_lipschitz.uniformContinuous

/-! ## §2 — The UHF trace extension scaffolding -/

/-- **The UHF trace extension** produced by `UniformSpace.Completion.extension`
    from any given pre-trace `pre_trace : TimelessFieldRing → ℂ`.

    Yields `UHF_trace : TimelessFieldCompletion → ℂ`. Its uniform
    continuity and dense-image agreement are supplied by
    `UHF_trace_extension_uniformContinuous` and
    `UHF_trace_extension_agrees_on_dense`. -/
noncomputable def UHF_trace_extension_from_pre_trace
    (pre_trace : TimelessFieldRing → ℂ) : TimelessFieldCompletion → ℂ :=
  UniformSpace.Completion.extension pre_trace

/-- **r86.d: the UHF trace extension is uniformly continuous**.

    This holds unconditionally on any pre-trace (mathlib's extension
    is defined for any map, giving a uniformly continuous function
    to a complete + T0 codomain). -/
theorem UHF_trace_extension_uniformContinuous
    (pre_trace : TimelessFieldRing → ℂ) :
    UniformContinuous (UHF_trace_extension_from_pre_trace pre_trace) :=
  UniformSpace.Completion.uniformContinuous_extension

/-- **r86.e: the UHF trace extension agrees with the pre-trace on the
    dense embedded image** (when the pre-trace is uniformly continuous). -/
theorem UHF_trace_extension_agrees_on_dense
    (pre_trace : TimelessFieldRing → ℂ) (h_pre_uc : UniformContinuous pre_trace)
    (a : TimelessFieldRing) :
    UHF_trace_extension_from_pre_trace pre_trace (a : TimelessFieldCompletion) =
      pre_trace a :=
  UniformSpace.Completion.extension_coe h_pre_uc a

/-! ## §3 — Prop-level substrate content

The construction of a linear + unital pre-trace on `TimelessFieldRing`
from the level-k normalized trace family requires the substrate r29
successor-RingHom trace-preservation compatibility class + a
`Module.DirectLimit.lift`-flavour ℂ-linear-map lift or an alternative
substrate-native construction. This is r87 substrate work. -/

/-- **SubstratePreTraceExistsConjecture (Prop level)**.

    There exists a ℂ-valued uniformly continuous additive + unital
    function on `TimelessFieldRing` (the r30 substrate direct limit).
    This is the substrate pre-trace whose completion extension is
    the UHF trace. Substrate residual for r87. -/
def SubstratePreTraceExistsConjecture : Prop :=
  ∃ (pre_trace : TimelessFieldRing → ℂ),
    UniformContinuous pre_trace ∧
    (∀ x y, pre_trace (x + y) = pre_trace x + pre_trace y) ∧
    pre_trace 1 = 1

/-- **SubstrateUHFTraceExistsConjecture (Prop level)**.

    There exists a ℂ-valued uniformly continuous additive + unital
    function on `TimelessFieldCompletion` (the substrate UHF C*-algebra
    completion from r53-r59). This is the essential UHF trace target
    of the substrate ToE spectral bridge. Substrate target for r87. -/
def SubstrateUHFTraceExistsConjecture : Prop :=
  ∃ (τ : TimelessFieldCompletion → ℂ),
    UniformContinuous τ ∧
    (∀ x y, τ (x + y) = τ x + τ y) ∧
    τ 1 = 1

/-- **r86.f: substrate-conditional reduction of the UHF trace target**.

    Given the substrate pre-trace on `TimelessFieldRing` (r87 target),
    the `UniformSpace.Completion.extension` mechanism delivers the UHF
    trace on `TimelessFieldCompletion` with the required additive +
    unital + uniformly continuous properties. Kernel-proved
    implication. -/
theorem substrate_UHF_trace_from_pre_trace :
    SubstratePreTraceExistsConjecture → SubstrateUHFTraceExistsConjecture := by
  rintro ⟨pre_trace, h_uc, h_add, h_one⟩
  refine ⟨UHF_trace_extension_from_pre_trace pre_trace,
          UHF_trace_extension_uniformContinuous pre_trace, ?_, ?_⟩
  · -- Additivity of the extension: use extension₂ / induction argument
    -- Both sides continuous in each variable + agree on the dense image.
    intro x y
    -- Both sides are continuous in x (and in y).
    -- We use the density of the embedded image plus the pre-trace additivity.
    refine UniformSpace.Completion.induction_on₂ x y
      (p := fun x y =>
        UHF_trace_extension_from_pre_trace pre_trace (x + y) =
          UHF_trace_extension_from_pre_trace pre_trace x +
            UHF_trace_extension_from_pre_trace pre_trace y)
      ?_ ?_
    · -- Closed set: preimage of the equality-of-continuous-functions.
      refine isClosed_eq ?_ ?_
      · exact (UHF_trace_extension_uniformContinuous pre_trace).continuous.comp
          continuous_add
      · exact ((UHF_trace_extension_uniformContinuous pre_trace).continuous.comp
          continuous_fst).add
          ((UHF_trace_extension_uniformContinuous pre_trace).continuous.comp
          continuous_snd)
    · -- Dense image reduction: use extension_coe + coe_add + pre-trace additivity.
      intro a b
      rw [← UniformSpace.Completion.coe_add,
          UHF_trace_extension_agrees_on_dense pre_trace h_uc,
          UHF_trace_extension_agrees_on_dense pre_trace h_uc,
          UHF_trace_extension_agrees_on_dense pre_trace h_uc,
          h_add a b]
  · -- Unital: extension at (1 : TimelessFieldRing) agrees with pre_trace 1 = 1
    show UHF_trace_extension_from_pre_trace pre_trace
      ((1 : TimelessFieldRing) : TimelessFieldCompletion) = 1
    rw [UHF_trace_extension_agrees_on_dense pre_trace h_uc, h_one]

/-! ## §4 — r86 substrate UHF trace extension capstone -/

/-- **★★★ r86 SUBSTRATE UHF TRACE EXTENSION CAPSTONE ★★★**

    The essential analytic and completion-extension content for
    lifting the substrate normalized matrix trace to
    `TimelessFieldCompletion`:

      (Y1) `substrate_level_trace_dist_bound` — level-k distance bound.
      (Y2) `substrate_level_trace_lipschitz` — level-k `LipschitzWith 1`.
      (Y3) `substrate_level_trace_uniformContinuous` — level-k UC.
      (Y4) `UHF_trace_extension_uniformContinuous` — completion extension UC.
      (Y5) `UHF_trace_extension_agrees_on_dense` — extension coherence.
      (Y6) `substrate_UHF_trace_from_pre_trace` — the substrate reduction
           `SubstratePreTraceExistsConjecture → SubstrateUHFTraceExistsConjecture`,
           kernel-proved.
      (Y7) `SubstratePreTraceExistsConjecture` — Prop-level substrate
           residual (r87 target).
      (Y8) `SubstrateUHFTraceExistsConjecture` — Prop-level substrate
           target of the UHF trace on completion.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r86 kernel-verifies the level-k analytic
    scaffolding (1-Lipschitz + UC) coming from r85b, AND the
    completion-extension scaffolding for producing UHF_trace from any
    uniformly continuous pre-trace. The substrate reduction (Y6)
    shows that IF the substrate direct-limit pre-trace exists as UC
    + additive + unital (SubstratePreTraceExistsConjecture, r87
    substrate target), THEN the UHF trace on TimelessFieldCompletion
    exists as UC + additive + unital via the completion extension
    mechanism. r87 substrate work will supply the pre-trace via the
    substrate r29 successor-RingHom trace-preservation compatibility
    class + mathlib direct-limit lift. -/
theorem r86_substrate_UHF_trace_extension_capstone :
    (∀ {n : ℕ} [NeZero n] (M N : Matrix (Fin n) (Fin n) ℂ),
      dist (normalized_matrix_trace M) (normalized_matrix_trace N) ≤ dist M N) ∧
    (∀ {n : ℕ} [NeZero n],
      LipschitzWith 1
        (fun M : Matrix (Fin n) (Fin n) ℂ => normalized_matrix_trace M)) ∧
    (∀ {n : ℕ} [NeZero n],
      UniformContinuous
        (fun M : Matrix (Fin n) (Fin n) ℂ => normalized_matrix_trace M)) ∧
    (∀ (pre_trace : TimelessFieldRing → ℂ),
      UniformContinuous (UHF_trace_extension_from_pre_trace pre_trace)) ∧
    (∀ (pre_trace : TimelessFieldRing → ℂ), UniformContinuous pre_trace →
       ∀ (a : TimelessFieldRing),
      UHF_trace_extension_from_pre_trace pre_trace (a : TimelessFieldCompletion)
        = pre_trace a) ∧
    (SubstratePreTraceExistsConjecture → SubstrateUHFTraceExistsConjecture) :=
  ⟨fun {_} _ M N => substrate_level_trace_dist_bound M N,
   fun {_} _ => substrate_level_trace_lipschitz,
   fun {_} _ => substrate_level_trace_uniformContinuous,
   fun pt => UHF_trace_extension_uniformContinuous pt,
   fun pt h a => UHF_trace_extension_agrees_on_dense pt h a,
   substrate_UHF_trace_from_pre_trace⟩

end SubstrateUHFCompletionTrace
end PrincipiaTractalis
