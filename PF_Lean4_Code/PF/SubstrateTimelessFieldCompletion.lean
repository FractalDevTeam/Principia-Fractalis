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

/-! ## §6 — r55: StarRing on TimelessFieldCompletion

Extend the r32 star algebra identities (star_add, star_mul,
star_involutive) from T_∞ to the metric completion via
`UniformSpace.Completion.induction_on` / `induction_on₂` on
`IsClosed` propositions.

Each identity holds on the dense image (T_∞ embedded via the r53
Completion coercion) by the r54.d `star_coe` bridge together with
the r32 T_∞ identities. Continuity of `star`, `+`, `*` on the
Completion closes the induction. -/

/-- **`star` is continuous on TimelessFieldCompletion** — immediate
    from `UniformSpace.Completion.continuous_map`, since our r54
    instance defines `star := Completion.map star`. -/
theorem continuous_star_TimelessFieldCompletion :
    Continuous (star : TimelessFieldCompletion → TimelessFieldCompletion) :=
  UniformSpace.Completion.continuous_map

/-- **r55.a: `star_involutive` on TimelessFieldCompletion**.
    Lifted via `induction_on` + r32's `star_involutive` on T_∞. -/
theorem star_involutive_TimelessFieldCompletion :
    Function.Involutive (star : TimelessFieldCompletion → TimelessFieldCompletion) := by
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (continuous_star_TimelessFieldCompletion.comp
        continuous_star_TimelessFieldCompletion)
      continuous_id
  | ih a =>
    rw [star_coe_TimelessFieldCompletion, star_coe_TimelessFieldCompletion,
        star_star]

/-- **InvolutiveStar instance on Completion**. -/
noncomputable instance instInvolutiveStarTimelessFieldCompletion :
    InvolutiveStar TimelessFieldCompletion where
  star_involutive := star_involutive_TimelessFieldCompletion

/-- **r55.b: `star_add` on TimelessFieldCompletion**.
    Lifted via `induction_on₂` + r32's `star_add` on T_∞. -/
theorem star_add_TimelessFieldCompletion (x y : TimelessFieldCompletion) :
    star (x + y) = star x + star y := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq
      (continuous_star_TimelessFieldCompletion.comp
        (continuous_fst.add continuous_snd))
      ((continuous_star_TimelessFieldCompletion.comp continuous_fst).add
        (continuous_star_TimelessFieldCompletion.comp continuous_snd))
  | ih a b =>
    rw [← UniformSpace.Completion.coe_add,
        star_coe_TimelessFieldCompletion, star_add,
        UniformSpace.Completion.coe_add,
        star_coe_TimelessFieldCompletion,
        star_coe_TimelessFieldCompletion]

/-- **StarAddMonoid instance on Completion**. -/
noncomputable instance instStarAddMonoidTimelessFieldCompletion :
    StarAddMonoid TimelessFieldCompletion where
  star_add := star_add_TimelessFieldCompletion

/-- **r55.c: `star_mul` on TimelessFieldCompletion** — the reversed
    multiplication identity. Lifted via `induction_on₂` + r32's
    `star_mul` on T_∞. -/
theorem star_mul_TimelessFieldCompletion (x y : TimelessFieldCompletion) :
    star (x * y) = star y * star x := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq
      (continuous_star_TimelessFieldCompletion.comp
        (continuous_fst.mul continuous_snd))
      ((continuous_star_TimelessFieldCompletion.comp continuous_snd).mul
        (continuous_star_TimelessFieldCompletion.comp continuous_fst))
  | ih a b =>
    rw [← UniformSpace.Completion.coe_mul,
        star_coe_TimelessFieldCompletion, star_mul,
        UniformSpace.Completion.coe_mul,
        star_coe_TimelessFieldCompletion,
        star_coe_TimelessFieldCompletion]

/-- **StarMul instance on Completion**. -/
noncomputable instance instStarMulTimelessFieldCompletion :
    StarMul TimelessFieldCompletion where
  star_mul := star_mul_TimelessFieldCompletion

/-- **★★★ r55: StarRing TimelessFieldCompletion ★★★**

    The full StarRing structure descends from T_∞ to the Completion.
    Combines the r55.a-c identities (star_involutive, star_add,
    star_mul) via mathlib's standard StarRing packaging. -/
noncomputable instance instStarRingTimelessFieldCompletion :
    StarRing TimelessFieldCompletion where
  star_add := star_add_TimelessFieldCompletion
  star_mul := star_mul_TimelessFieldCompletion

/-! ## §7 — r55 capstone -/

/-- **★★★ r55: STAR RING EXTENDS TO THE COMPLETION ★★★**

    The substrate star algebra identities lift to
    `TimelessFieldCompletion`. Bundles:
      (S1) `star_involutive` — the involution is self-inverse
      (S2) `star_add`         — star distributes over addition
      (S3) `star_mul`         — star reverses multiplication
      (S4) `InvolutiveStar TimelessFieldCompletion`
      (S5) `StarAddMonoid TimelessFieldCompletion`
      (S6) `StarMul TimelessFieldCompletion`
      (S7) `StarRing TimelessFieldCompletion`

    Kernel-only [propext, Classical.choice, Quot.sound]. -/
theorem substrate_TimelessFieldCompletion_starRing_capstone :
    Function.Involutive
      (star : TimelessFieldCompletion → TimelessFieldCompletion) ∧
    (∀ x y : TimelessFieldCompletion, star (x + y) = star x + star y) ∧
    (∀ x y : TimelessFieldCompletion, star (x * y) = star y * star x) ∧
    Nonempty (InvolutiveStar TimelessFieldCompletion) ∧
    Nonempty (StarAddMonoid TimelessFieldCompletion) ∧
    Nonempty (StarMul TimelessFieldCompletion) ∧
    Nonempty (StarRing TimelessFieldCompletion) :=
  ⟨star_involutive_TimelessFieldCompletion,
   star_add_TimelessFieldCompletion,
   star_mul_TimelessFieldCompletion,
   ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-! ## §8 — r56: CStarRing on TimelessFieldCompletion

The C*-identity `‖x⋆ * x‖ = ‖x‖²` — via mathlib's modern
`CStarRing` class asking only for `‖x‖ * ‖x‖ ≤ ‖star x * x‖` — lifts
from T_∞ to its metric completion by `induction_on` on the closed
inequality set. Both sides are continuous in `x`: LHS is
`‖·‖ * ‖·‖` (norm composed with itself), RHS is `‖·‖ ∘ (star * id)`.
On the dense image the inequality is r49's `cstar_ineq_TimelessField`
composed with `norm_coe` (isometric coercion) + r54.d `star_coe` +
`Completion.coe_mul`. -/

/-- **r56: C*-inequality on TimelessFieldCompletion**:
        `‖x‖ * ‖x‖ ≤ ‖star x * x‖`
    Lifted via `induction_on` from r49's `cstar_ineq_TimelessField`. -/
theorem cstar_ineq_TimelessFieldCompletion (x : TimelessFieldCompletion) :
    ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le
      (continuous_norm.mul continuous_norm)
      (continuous_norm.comp
        (continuous_star_TimelessFieldCompletion.mul continuous_id))
  | ih a =>
    rw [UniformSpace.Completion.norm_coe, star_coe_TimelessFieldCompletion,
        ← UniformSpace.Completion.coe_mul,
        UniformSpace.Completion.norm_coe]
    exact CStarRing.norm_mul_self_le a

/-- **★★★ r56: CStarRing TimelessFieldCompletion ★★★**

    The metric completion of T_∞ carries the full C*-identity. -/
noncomputable instance instCStarRingTimelessFieldCompletion :
    CStarRing TimelessFieldCompletion where
  norm_mul_self_le := cstar_ineq_TimelessFieldCompletion

/-! ## §9 — r56 capstone -/

/-- **★★★ r56: C*-RING EXTENDS TO THE COMPLETION ★★★**

    The C*-identity extends from T_∞ to the metric completion.
    Bundles:
      (C1) The C*-inequality `‖x‖ * ‖x‖ ≤ ‖star x * x‖` on Completion.
      (C2) `CStarRing TimelessFieldCompletion` instance.
      (C3) The full C*-identity `‖star x * x‖ = ‖x‖ * ‖x‖` via
           `CStarRing.norm_star_mul_self`.

    Kernel-only [propext, Classical.choice, Quot.sound]. -/
theorem substrate_TimelessFieldCompletion_cstar_capstone :
    (∀ x : TimelessFieldCompletion, ‖x‖ * ‖x‖ ≤ ‖star x * x‖) ∧
    Nonempty (CStarRing TimelessFieldCompletion) ∧
    (∀ x : TimelessFieldCompletion, ‖star x * x‖ = ‖x‖ * ‖x‖) :=
  ⟨cstar_ineq_TimelessFieldCompletion,
   ⟨inferInstance⟩,
   fun _ => CStarRing.norm_star_mul_self⟩

end SubstrateTimelessFieldCompletion
end PrincipiaTractalis
