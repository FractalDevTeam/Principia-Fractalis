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
    extended by uniform continuity (r54-r59).

    Declared as `abbrev` (reducible def) so that coercions
    `TimelessFieldRing → TimelessFieldCompletion` and mathlib
    `UniformSpace.Completion` instances are transparently accessible
    without explicit type unfolding. -/
abbrev TimelessFieldCompletion : Type :=
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

/-! ## §4 — r54: Star on TimelessFieldCompletion

The r32 involution on T_∞ is an **isometry** — a consequence of the
r49 C*-property via mathlib's `CStarRing.to_normedStarGroup` and
`norm_star`. Isometries are uniformly continuous, so `star` extends
to the completion via `UniformSpace.Completion.map`. -/

/-- **Star is an isometry on T_∞** — key input for the Completion
    lift. `dist (star x) (star y) = ‖star x - star y‖ = ‖star (x - y)‖
    = ‖x - y‖ = dist x y`, using `norm_star` from
    `NormedStarGroup TimelessFieldRing` (auto-provided by the r49
    `CStarRing` instance via `CStarRing.to_normedStarGroup`). -/
theorem isometry_star_TimelessField :
    Isometry (star : TimelessFieldRing → TimelessFieldRing) := by
  refine Isometry.of_dist_eq (fun x y => ?_)
  rw [dist_eq_norm_sub, dist_eq_norm_sub, ← star_sub, norm_star]

/-- **Star is uniformly continuous on T_∞** — immediate corollary
    of the isometry, feeds `Completion.map`. -/
theorem uniformContinuous_star_TimelessField :
    UniformContinuous (star : TimelessFieldRing → TimelessFieldRing) :=
  isometry_star_TimelessField.uniformContinuous

/-- **★★★ r54: Star instance on TimelessFieldCompletion ★★★**

    The involution on T_∞ extends to the completion via
    `UniformSpace.Completion.map`, using uniform continuity from
    the isometry. On the image of the canonical embedding
    `TimelessFieldRing ↪ TimelessFieldCompletion`, this new star
    reduces to the r32 involution — the compatibility lemma
    `star_coe_TimelessFieldCompletion` witnesses this. -/
noncomputable instance instStarTimelessFieldCompletion :
    Star TimelessFieldCompletion where
  star := UniformSpace.Completion.map (star : TimelessFieldRing → TimelessFieldRing)

/-- **Star / coercion compatibility**: on the image of the canonical
    embedding, the r54 completion-star agrees with the r32 T_∞ star.
        `star ((↑a : TimelessFieldCompletion)) = ↑(star a)`. -/
theorem star_coe_TimelessFieldCompletion (a : TimelessFieldRing) :
    star ((a : TimelessFieldCompletion) : TimelessFieldCompletion) =
      ((star a : TimelessFieldRing) : TimelessFieldCompletion) :=
  UniformSpace.Completion.map_coe uniformContinuous_star_TimelessField a

/-! ## §5 — r54 capstone -/

/-- **★★★ r54: STAR EXTENDS TO THE COMPLETION ★★★**

    The substrate involution extends from T_∞ to the metric
    completion. Bundles:
      (T1) `Isometry (star : T_∞ → T_∞)`
      (T2) `UniformContinuous (star : T_∞ → T_∞)`
      (T3) `Star TimelessFieldCompletion` (r54 instance)
      (T4) star / coercion compatibility on the dense image

    Kernel-only [propext, Classical.choice, Quot.sound]. -/
theorem substrate_TimelessFieldCompletion_star_capstone :
    Isometry (star : TimelessFieldRing → TimelessFieldRing) ∧
    UniformContinuous (star : TimelessFieldRing → TimelessFieldRing) ∧
    Nonempty (Star TimelessFieldCompletion) ∧
    (∀ a : TimelessFieldRing,
      star ((a : TimelessFieldCompletion) : TimelessFieldCompletion) =
        ((star a : TimelessFieldRing) : TimelessFieldCompletion)) :=
  ⟨isometry_star_TimelessField,
   uniformContinuous_star_TimelessField,
   ⟨inferInstance⟩,
   star_coe_TimelessFieldCompletion⟩

end SubstrateTimelessFieldCompletion
end PrincipiaTractalis
