/-
# r53: The Substrate Timeless Field COMPLETION — toward the UHF C*-algebra

★ 2026-07-06 r53 — metric completion of T_∞ ★

## Framework-first content

r43-r52 established that T_∞ (`TimelessFieldRing`) is a mathlib-native
**pre-C\*-algebra**: it carries `NormedRing`, `StarRing`, `CStarRing`,
`NormedAlgebra ℂ`, `StarModule ℂ` — every mathlib `CStarAlgebra` axiom
short of `CompleteSpace`. T_∞ is genuinely not complete under the L²
operator norm because it is the ALGEBRAIC direct limit.

r53 takes the metric completion `UniformSpace.Completion TimelessFieldRing`,
delivering `TimelessFieldCompletion` — a `CompleteSpace` object that
inherits the algebraic + normed structure automatically via mathlib's
uniform-completion machinery.

## What this file establishes (r53 scope)

  * `TimelessFieldCompletion` — the metric completion of T_∞.
  * Auto-inherited from mathlib:
      - `CompleteSpace TimelessFieldCompletion`      (Completion definition)
      - `MetricSpace TimelessFieldCompletion`        (via NormedRing extension)
      - `Ring TimelessFieldCompletion`               (`UniformRing`)
      - `NormedRing TimelessFieldCompletion`         (from SeminormedRing T_∞)
      - `NormedAddCommGroup TimelessFieldCompletion` (via Completion group)
      - `NormedSpace ℂ TimelessFieldCompletion`      (from NormedSpace ℂ T_∞)
  * `substrate_TimelessFieldCompletion_auto_capstone` — bundled witness.

## Framework positioning

r53 stages the transition from the algebraic direct limit to the
mathlib-native `CStarAlgebra`. The remaining structures require
proof rather than automatic inheritance:

  * `Star TimelessFieldCompletion` (r54) — extend the involution by
    uniform continuity of star on T_∞.
  * `StarRing TimelessFieldCompletion` (r55) — extend the r32 star
    algebra identities.
  * `CStarRing TimelessFieldCompletion` (r56) — the C\*-identity
    extends by continuity of `norm`, `mul`, `star`.
  * `Algebra ℂ + NormedAlgebra ℂ TimelessFieldCompletion` (r57) —
    non-commutative case, not covered by mathlib's `Completion`
    NormedAlgebra instance which requires `SeminormedCommRing`.
  * `StarModule ℂ TimelessFieldCompletion` (r58) — extend the r52
    star-scalar identity.
  * `CStarAlgebra TimelessFieldCompletion` (r59) — the capstone.

Stage 2026-07-06 r53 — metric completion of T_∞.
-/

import PF.SubstrateTimelessFieldNorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Tactic

open UniformSpace

namespace PrincipiaTractalis
namespace SubstrateTimelessFieldCompletion

open SubstrateDirectLimit SubstrateTimelessFieldNorm

/-! ## §1 — The Completion object

The metric completion of `TimelessFieldRing` under the induced L²
operator norm distance. Since T_∞ is a `NormedRing` (r47),
`MetricSpace` is provided; `UniformSpace.Completion` then gives a
`CompleteSpace` inhabited by Cauchy classes. -/

/-- **The substrate Timeless Field completion** — the metric
    completion of T_∞ under the L² operator-norm distance. This is
    the object that will carry the mathlib-native `CStarAlgebra`
    structure once the star / C\*-property / ℂ-algebra pieces are
    extended by uniform continuity (r54-r59). -/
noncomputable def TimelessFieldCompletion : Type :=
  UniformSpace.Completion TimelessFieldRing

/-! ## §2 — Auto-inherited instances

mathlib's `UniformSpace.Completion` propagates a large amount of
algebraic and normed structure automatically. -/

/-- **`UniformSpace`** — from mathlib's `Completion.uniformSpace`. -/
noncomputable instance instUniformSpaceTimelessFieldCompletion :
    UniformSpace TimelessFieldCompletion :=
  inferInstanceAs (UniformSpace (UniformSpace.Completion TimelessFieldRing))

/-- **`CompleteSpace`** — the whole point of taking the completion.
    Directly from `Completion.completeSpace`. -/
noncomputable instance instCompleteSpaceTimelessFieldCompletion :
    CompleteSpace TimelessFieldCompletion :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion TimelessFieldRing))

/-- **`AddCommGroup`** — from Completion of an `AddCommGroup`. -/
noncomputable instance instAddCommGroupTimelessFieldCompletion :
    AddCommGroup TimelessFieldCompletion :=
  inferInstanceAs (AddCommGroup (UniformSpace.Completion TimelessFieldRing))

/-- **`Ring`** — from mathlib's `Completion.ring` (UniformRing). -/
noncomputable instance instRingTimelessFieldCompletion :
    Ring TimelessFieldCompletion :=
  inferInstanceAs (Ring (UniformSpace.Completion TimelessFieldRing))

/-- **`NormedAddCommGroup`** — inherited via Completion of a
    `SeminormedAddCommGroup`. -/
noncomputable instance instNormedAddCommGroupTimelessFieldCompletion :
    NormedAddCommGroup TimelessFieldCompletion :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion TimelessFieldRing))

/-- **`NormedRing`** — inherited via mathlib's
    `[SeminormedRing A] → NormedRing (Completion A)` instance
    (Mathlib/Analysis/Normed/Module/Completion.lean line 71). -/
noncomputable instance instNormedRingTimelessFieldCompletion :
    NormedRing TimelessFieldCompletion :=
  inferInstanceAs (NormedRing (UniformSpace.Completion TimelessFieldRing))

/-- **`NormedSpace ℂ`** — inherited via mathlib's
    `[NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]`
    → `NormedSpace 𝕜 (Completion E)` instance
    (Mathlib/Analysis/Normed/Module/Completion.lean line 32). -/
noncomputable instance instNormedSpaceTimelessFieldCompletion :
    NormedSpace ℂ TimelessFieldCompletion :=
  inferInstanceAs (NormedSpace ℂ (UniformSpace.Completion TimelessFieldRing))

/-! ## §3 — r53 auto-instance capstone -/

/-- **★★★ r53: TimelessFieldCompletion auto-instance capstone ★★★**

    Bundles the six mathlib-automatic instances on the completion:
      (C1) `UniformSpace`
      (C2) `CompleteSpace`         ← the defining property
      (C3) `AddCommGroup`
      (C4) `Ring`
      (C5) `NormedAddCommGroup`
      (C6) `NormedRing`
      (C7) `NormedSpace ℂ`

    Combined with r54-r59's manual constructions (Star, StarRing,
    CStarRing, Algebra ℂ, NormedAlgebra ℂ, StarModule ℂ), this
    delivers the substrate UHF C\*-algebra of history.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero
    project axioms. Zero sorries. -/
theorem substrate_TimelessFieldCompletion_auto_capstone :
    Nonempty (UniformSpace TimelessFieldCompletion) ∧
    Nonempty (CompleteSpace TimelessFieldCompletion) ∧
    Nonempty (AddCommGroup TimelessFieldCompletion) ∧
    Nonempty (Ring TimelessFieldCompletion) ∧
    Nonempty (NormedAddCommGroup TimelessFieldCompletion) ∧
    Nonempty (NormedRing TimelessFieldCompletion) ∧
    Nonempty (NormedSpace ℂ TimelessFieldCompletion) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩,
   ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

end SubstrateTimelessFieldCompletion
end PrincipiaTractalis
