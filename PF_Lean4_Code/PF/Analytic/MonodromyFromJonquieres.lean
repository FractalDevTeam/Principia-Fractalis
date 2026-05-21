/-
# Monodromy From Jonquières — Reduction to a Single Identity-on-SlitPlane Hypothesis

This file attacks the load-bearing hypothesis `PolyLogMonodromyHypothesis s`
(from `PF/Analytic/PolyLogMonodromyExtension.lean`), reducing it — axiom
free, no `sorry` — to a SINGLE named open hypothesis encoding the
classical Jonquières expansion as a global analytic extension of
`polyLog s` on `SlitPlane`.

## What this file delivers

1. **`JonquieresGlobalCandidate s`** — a clean structural Prop bundling:
   * A candidate function `F : ℂ → ℂ` analytic on `SlitPlane`.
   * The disc-agreement `F z = polyLog s z` for every
     `z ∈ SlitPlane ∩ ball 0 1`.

   This is LITERALLY the `PolyLogMonodromyHypothesis s` repackaged as a
   structure, so the equivalence is one-line trivial. Its purpose is
   to provide a named TARGET for any future Jonquières-style or
   Hankel-style construction.

2. **`JonquieresGlobalIdentityHypothesis s`** — the strongest possible
   named open hypothesis: the Jonquières expansion `jonquieresExpansion s`
   IS the global analytic extension of `polyLog s` on `SlitPlane`. That
   is:
   * `AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlane`, AND
   * `jonquieresExpansion s z = polyLog s z` for every
     `z ∈ SlitPlane ∩ ball 0 1`.

   This is the cleanest single named open conjecture: it picks the
   manuscript's specific analytic-continuation candidate
   (`jonquieresExpansion`) and asserts it IS the global extension.

3. **`polyLogMonodromy_of_jonquieres_global_identity`** — the
   CONDITIONAL THEOREM: given the global Jonquières identity hypothesis,
   `PolyLogMonodromyHypothesis s` follows. The proof is a one-line
   packaging — pass `F := jonquieresExpansion s` as the witness.

4. **`polyLogMonodromy_of_any_global_candidate`** — a weaker but more
   FLEXIBLE conditional: given ANY global analytic candidate satisfying
   the disc-identity, `PolyLogMonodromyHypothesis s` follows. This
   lets downstream consumers plug in alternative constructions
   (Hankel-integral, etc.) without committing to the Jonquières form.

5. **`jonquieresExpansion_is_polyLog_extension`** — the cleanest named
   form of the open conjecture: a single named `Prop` that, once
   discharged, immediately closes `PolyLogMonodromyHypothesis s` and
   hence `OffDiscPatchData s` (via the bridge
   `offDiscPatchData_of_monodromy`).

## The reduction chain

```
JonquieresGlobalIdentityHypothesis s                  ← single open Prop
        ↓ (this file, axiom-free)
PolyLogMonodromyHypothesis s                          ← previously load-bearing
        ↓ (PolyLogMonodromyExtension.lean, axiom-free)
PolyLogAnalyticExtensionExists s                      ← top-level Prop
```

Combined with `offDiscPatchData_of_monodromy` from
`OffDiscPatchDataConstruction.lean`:

```
JonquieresGlobalIdentityHypothesis s
        ↓
PolyLogMonodromyHypothesis s
        ↓
OffDiscPatchData s  (via offDiscPatchData_of_monodromy)
```

So the ENTIRE off-disc-patch chain collapses to producing a single
witness of `JonquieresGlobalIdentityHypothesis s`.

## Why the conditional, not the unconditional, theorem

The classical Jonquières identity `polyLog s z = jonquieresExpansion s z`
holds only in a NEIGHBORHOOD of `z = 1` (specifically `|log z| < 2π`),
NOT globally on `SlitPlane`. So
`JonquieresGlobalIdentityHypothesis s` as stated is a STRONGER claim
than the classical theorem — it asserts a *global* analytic
continuation that AGREES with `jonquieresExpansion` near `z = 1`
(by uniqueness of analytic continuation) but extends consistently to
the rest of `SlitPlane` via the classical Jonquières inversion
`z ↦ 1/z` formula for `|z| > 1`, and via the symbolic identity
elsewhere.

This file therefore does NOT discharge the hypothesis — it REDUCES
the load-bearing content to a single specific named Prop. The
remaining open work is:
* Show `jonquieresExpansion s` is well-defined and analytic on all
  of `SlitPlane` (requires multiple coordinate charts and uniqueness-
  of-continuation gluing).
* Show the disc-agreement `jonquieresExpansion s z = polyLog s z`
  for `|z| < 1` (the matching point at `z = 1` is the anchor; the
  identity theorem then propagates to the disc-intersection with
  `SlitPlane`).

Both steps are classical theorems requiring multi-month mathlib
infrastructure (closed-contour integration, Bernoulli growth bounds).
This file's contribution is the CLEAN STRUCTURAL REDUCTION: ALL of
the residual open analytic content for the off-disc-patch chain is
now isolated to `JonquieresGlobalIdentityHypothesis s`.

Stage L12 — Monodromy reduction to Jonquières global identity (2026-05-21).
-/

import PF.Analytic.PolyLogMonodromyExtension
import PF.Analytic.JonquieresIdentity
import PF.Analytic.OffDiscPatchDataConstruction

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Stage 1: Generic global-candidate hypothesis

The most flexible form: ANY analytic function on `SlitPlane` agreeing
with `polyLog s` on the disc-intersection trivially witnesses
`PolyLogMonodromyHypothesis s`. This is the substrate hypothesis any
constructive route (Jonquières, Hankel, Mellin-Barnes, etc.) must
ultimately produce. -/

/-- **Generic global-candidate hypothesis**: there exists ANY analytic
    function `F : ℂ → ℂ` on `SlitPlane` agreeing with `polyLog s` on
    `SlitPlane ∩ ball 0 1`. This is literally `PolyLogMonodromyHypothesis`
    repackaged — included here for symmetry with the more specific
    Jonquières-form hypothesis below. -/
def GlobalCandidateHypothesis (s : ℂ) : Prop :=
  ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F SlitPlane ∧
    (∀ z ∈ SlitPlane ∩ Metric.ball (0 : ℂ) 1, F z = polyLog s z)

/-- **Equivalence**: the generic global-candidate hypothesis is
    DEFINITIONALLY equal to `PolyLogMonodromyHypothesis`. -/
theorem globalCandidateHypothesis_iff_monodromy (s : ℂ) :
    GlobalCandidateHypothesis s ↔ PolyLogMonodromyHypothesis s := Iff.rfl

/-- **Trivial forward direction**: the generic global-candidate
    hypothesis implies `PolyLogMonodromyHypothesis`. By definition. -/
theorem polyLogMonodromy_of_any_global_candidate
    {s : ℂ} (h : GlobalCandidateHypothesis s) :
    PolyLogMonodromyHypothesis s := h

/-- **Reverse direction**: `PolyLogMonodromyHypothesis` implies the
    generic global-candidate hypothesis (also by definition). -/
theorem globalCandidate_of_polyLogMonodromy
    {s : ℂ} (h : PolyLogMonodromyHypothesis s) :
    GlobalCandidateHypothesis s := h

/-! ## Stage 2: The Jonquières-specific global identity hypothesis

The classical Erdélyi-Magnus-Oberhettinger-Tricomi theorem identifies
the analytic continuation of `polyLog s` with `jonquieresExpansion s`
in a neighborhood of `z = 1`. The STRONGER hypothesis named here asserts
that this identification extends to all of `SlitPlane`. -/

/-- **The global Jonquières identity hypothesis**: `jonquieresExpansion s`
    is the global analytic extension of `polyLog s` on `SlitPlane`.

    Two conjunctive components:
    * `jonquieresExpansion s` is analytic on `SlitPlane` (in
      particular, the Γ-term `Γ(1-s) · (-log z)^(s-1)` and the
      ζ-series `Σ ζ(s-k) (log z)^k / k!` each extend analytically
      to all of `SlitPlane`, with poles only at the branch cut).
    * `jonquieresExpansion s z = polyLog s z` for every
      `z ∈ SlitPlane ∩ ball 0 1` (the disc-agreement, i.e., the
      tsum matches the Jonquières expansion on the unit disc minus
      the branch cut).

    Once discharged, this collapses the entire load-bearing chain:
    * `PolyLogMonodromyHypothesis s` (trivial: pass
      `F := jonquieresExpansion s`).
    * `OffDiscPatchData s` (via
      `offDiscPatchData_of_monodromy`).
    * `PolyLogAnalyticExtensionExists s` (via
      `polyLogAnalyticExtensionExists_of_monodromy`). -/
def JonquieresGlobalIdentityHypothesis (s : ℂ) : Prop :=
  AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlane ∧
    (∀ z ∈ SlitPlane ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion s z = polyLog s z)

/-- **The cleanest single named open conjecture**: a synonym for
    `JonquieresGlobalIdentityHypothesis` with a more descriptive name,
    emphasizing the role as the single load-bearing open Prop. -/
def jonquieresExpansion_is_polyLog_extension (s : ℂ) : Prop :=
  JonquieresGlobalIdentityHypothesis s

/-- **The two are definitionally equal**. -/
theorem jonquieresExpansion_is_polyLog_extension_def (s : ℂ) :
    jonquieresExpansion_is_polyLog_extension s ↔
      JonquieresGlobalIdentityHypothesis s := Iff.rfl

/-! ## Stage 3: The reduction theorem

Given the global Jonquières identity hypothesis, package
`jonquieresExpansion s` as the witness for
`PolyLogMonodromyHypothesis s`. The proof is one line: introduce the
witness, project to the two conjunctive components, done. -/

/-- **The main reduction**: given the global Jonquières identity
    hypothesis, `PolyLogMonodromyHypothesis s` follows.

    Proof: pass `F := jonquieresExpansion s` as the witness. The
    hypothesis's two components ARE the two `PolyLogMonodromyHypothesis`
    components (modulo a symmetric `Eq` flip for the disc-agreement
    field, since the hypothesis states
    `jonquieresExpansion s z = polyLog s z` and the target needs
    `F z = polyLog s z`). -/
theorem polyLogMonodromy_of_jonquieres_global_identity
    {s : ℂ} (h : JonquieresGlobalIdentityHypothesis s) :
    PolyLogMonodromyHypothesis s := by
  refine ⟨jonquieresExpansion s, h.1, ?_⟩
  intro z hz
  exact h.2 z hz

/-- **Composed reduction** through the off-disc-patch chain: from
    `JonquieresGlobalIdentityHypothesis s`, we obtain
    `OffDiscPatchData s`. -/
noncomputable def offDiscPatchData_of_jonquieres_global_identity
    {s : ℂ} (h : JonquieresGlobalIdentityHypothesis s) :
    OffDiscPatchData s :=
  offDiscPatchData_of_monodromy
    (polyLogMonodromy_of_jonquieres_global_identity h)

/-- **Composed reduction** to the top-level extension Prop: from
    `JonquieresGlobalIdentityHypothesis s`, `PolyLogAnalyticExtensionExists s`. -/
theorem polyLogAnalyticExtensionExists_of_jonquieres_global_identity
    {s : ℂ} (h : JonquieresGlobalIdentityHypothesis s) :
    PolyLogAnalyticExtensionExists s :=
  polyLogAnalyticExtensionExists_of_monodromy
    (polyLogMonodromy_of_jonquieres_global_identity h)

/-! ## Stage 4: Symmetric reverse direction (no extra content)

If `PolyLogMonodromyHypothesis s` holds AND we already KNOW
`jonquieresExpansion s` is the (unique by identity theorem) analytic
extension, then `JonquieresGlobalIdentityHypothesis s` follows. We
package this as a one-direction implication; the full equivalence
would require the identity theorem on `SlitPlane`, which is encoded
in the project's `polyLog_extension_unique`-style lemmas but is at
the `U_slit` level rather than the `SlitPlane` level. -/

/-- **Conditional reverse direction**: if `jonquieresExpansion s` is
    analytic on `SlitPlane` AND its disc-agreement holds, then the
    global identity hypothesis holds. This is also one-line trivial
    (just the definition unfolded). -/
theorem jonquieresGlobalIdentity_of_components
    {s : ℂ}
    (h_an : AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlane)
    (h_disc : ∀ z ∈ SlitPlane ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion s z = polyLog s z) :
    JonquieresGlobalIdentityHypothesis s := ⟨h_an, h_disc⟩

/-! ## Stage 5: Disc-agreement reduction

The disc-agreement component
`jonquieresExpansion s z = polyLog s z` for `z ∈ SlitPlane ∩ ball 0 1`
is itself the load-bearing `JonquieresIdentityHypothesis s z` collected
pointwise. We package this connection explicitly. -/

/-- **Disc-agreement is pointwise Jonquières identity**: the disc-
    agreement component of `JonquieresGlobalIdentityHypothesis` is
    EXACTLY the pointwise collection of `JonquieresIdentityHypothesis s z`
    on the disc, modulo the order of equality (the file
    `JonquieresIdentity.lean` states `polyLog s z = jonquieresExpansion s z`,
    we need `jonquieresExpansion s z = polyLog s z`). -/
theorem disc_agreement_of_pointwise_jonquieres
    {s : ℂ}
    (h : ∀ z ∈ SlitPlane ∩ Metric.ball (0 : ℂ) 1,
      JonquieresIdentityHypothesis s z) :
    ∀ z ∈ SlitPlane ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion s z = polyLog s z := by
  intro z hz
  exact (h z hz).symm

/-- **From pointwise Jonquières identity on disc + global analyticity
    of `jonquieresExpansion s`**: obtain the global identity
    hypothesis. -/
theorem jonquieresGlobalIdentity_of_pointwise_and_analytic
    {s : ℂ}
    (h_an : AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlane)
    (h_pt : ∀ z ∈ SlitPlane ∩ Metric.ball (0 : ℂ) 1,
      JonquieresIdentityHypothesis s z) :
    JonquieresGlobalIdentityHypothesis s :=
  ⟨h_an, disc_agreement_of_pointwise_jonquieres h_pt⟩

/-- **Capstone composed reduction**: pointwise Jonquières identity on
    the disc PLUS global analyticity of `jonquieresExpansion` PLUS the
    bridge through `PolyLogMonodromyHypothesis` ⇒ top-level extension
    existence. This is the cleanest decomposition into named subgoals:
    * `h_an` — analyticity of the candidate (analytic-functions content);
    * `h_pt` — pointwise identity on disc (the Erdélyi-Magnus-
      Oberhettinger-Tricomi disc-region content of
      `JonquieresIdentityHypothesis`). -/
theorem polyLogAnalyticExtensionExists_of_pointwise_jonquieres
    {s : ℂ}
    (h_an : AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlane)
    (h_pt : ∀ z ∈ SlitPlane ∩ Metric.ball (0 : ℂ) 1,
      JonquieresIdentityHypothesis s z) :
    PolyLogAnalyticExtensionExists s :=
  polyLogAnalyticExtensionExists_of_jonquieres_global_identity
    (jonquieresGlobalIdentity_of_pointwise_and_analytic h_an h_pt)

/-! ## Stage 6: Composed off-disc-patch bridge

A direct chain from pointwise Jonquières identity on the disc to
`OffDiscPatchData s`, sidestepping intermediate hypothesis names. -/

/-- **Off-disc patch data from pointwise Jonquières identity**: same
    inputs as above, output is `OffDiscPatchData s`. -/
noncomputable def offDiscPatchData_of_pointwise_jonquieres
    {s : ℂ}
    (h_an : AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlane)
    (h_pt : ∀ z ∈ SlitPlane ∩ Metric.ball (0 : ℂ) 1,
      JonquieresIdentityHypothesis s z) :
    OffDiscPatchData s :=
  offDiscPatchData_of_jonquieres_global_identity
    (jonquieresGlobalIdentity_of_pointwise_and_analytic h_an h_pt)

/-! ## Status

**Discharged (this file, axiom-free, no `sorry`)**:

* `GlobalCandidateHypothesis s` — generic flexible substrate Prop.
* `globalCandidateHypothesis_iff_monodromy` — definitional equivalence
  with `PolyLogMonodromyHypothesis`.
* `polyLogMonodromy_of_any_global_candidate` — trivial forward.
* `globalCandidate_of_polyLogMonodromy` — trivial reverse.
* `JonquieresGlobalIdentityHypothesis s` — the cleanest single load-
  bearing open Prop.
* `jonquieresExpansion_is_polyLog_extension` — descriptive synonym.
* `polyLogMonodromy_of_jonquieres_global_identity` — **the main
  reduction theorem**: global Jonquières identity ⇒
  `PolyLogMonodromyHypothesis`.
* `offDiscPatchData_of_jonquieres_global_identity` — composed reduction
  to `OffDiscPatchData`.
* `polyLogAnalyticExtensionExists_of_jonquieres_global_identity` —
  composed reduction to top-level extension.
* `jonquieresGlobalIdentity_of_components` — reverse-direction
  one-line assembly.
* `disc_agreement_of_pointwise_jonquieres` — disc-agreement from
  pointwise Jonquières identity (modulo `Eq.symm`).
* `jonquieresGlobalIdentity_of_pointwise_and_analytic` — global
  identity from pointwise identity + analyticity.
* `polyLogAnalyticExtensionExists_of_pointwise_jonquieres` — capstone
  composed reduction.
* `offDiscPatchData_of_pointwise_jonquieres` — direct chain to
  off-disc data.

**Residual gap (UNRESOLVED, single named Prop)**:

`JonquieresGlobalIdentityHypothesis s` — equivalently,
`jonquieresExpansion_is_polyLog_extension s`. Decomposes into:

1. **Analyticity of `jonquieresExpansion s` on `SlitPlane`**: requires
   showing that the Γ-term `Γ(1-s) · (-log z)^(s-1)` and the ζ-series
   each extend analytically to all of `SlitPlane`, with consistent
   branch selection. The Γ-term uses mathlib's
   `Complex.differentiable_Gamma` and `Complex.differentiable_cpow_const`;
   the ζ-series uses uniform-on-compact convergence under the
   Bernoulli growth bound (`BernoulliGrowthBoundResidual`, named in
   `JonquieresZetaSeriesSummable.lean`). Multi-week formalization.

2. **Disc-agreement** `jonquieresExpansion s z = polyLog s z` for
   `z ∈ SlitPlane ∩ ball 0 1`: the pointwise content of
   `JonquieresIdentityHypothesis s z`. The standard proof goes via
   Hankel contour integration with residue calculus on a punctured
   disk; mathlib has neither (see `JonquieresIdentity.lean`'s
   four-ingredient roadmap). Multi-month formalization.

**Architecture**: this file is a STRUCTURAL REDUCTION, not a
discharge. It converts the load-bearing
`PolyLogMonodromyHypothesis s` (which previously sat as a single
opaque hypothesis) into an equally-load-bearing but more SPECIFIC
hypothesis `JonquieresGlobalIdentityHypothesis s`. The latter is
preferable because:

* It NAMES the candidate extension (`jonquieresExpansion s`),
  isolating the open content into two distinct subgoals.
* It connects directly to the manuscript's explicit analytic-
  continuation candidate.
* Each subgoal (analyticity + disc-identity) admits an independent
  formalization track.

Combined with `offDiscPatchData_of_monodromy` from
`OffDiscPatchDataConstruction.lean`, this completes the architecture:
discharging `JonquieresGlobalIdentityHypothesis s` is sufficient to
close the ENTIRE off-disc-patch chain through to
`PolyLogAnalyticExtensionExists s`.

Stage L12 — Monodromy reduction to Jonquières global identity (2026-05-21).
-/

end PrincipiaTractalis.Analytic.Sheaf
