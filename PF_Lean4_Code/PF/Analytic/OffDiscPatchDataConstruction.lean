/-
# OffDiscPatchData Construction — Reduction From a Global Monodromy Hypothesis

This file attacks the residual gap `OffDiscPatchData s` named in
`PF/Analytic/PolyLogLocalPatches.lean`. It DOES NOT discharge the
open analytic-continuation content (which requires either the
Jonquières identity, the Hankel-contour integral, or an equivalent
multi-month classical-analysis formalization not currently in mathlib).

What it DOES deliver, axiom-free and `sorry`-free, is a clean
**interface refactor**: it shows that `OffDiscPatchData s` is
constructible from a `PolyLogMonodromyHypothesis s` witness — the
single-function packaging of the global monodromy data.

## What this buys

1. **Smaller surface area for the residual gap**: any downstream
   discharge of `OffDiscPatchData` can be obtained from the
   simpler global-function form `PolyLogMonodromyHypothesis s` —
   one function `F`, two properties (analyticity on `SlitPlane`,
   disc-agreement). The off-disc patch family is then derived
   mechanically by setting `V z₀ := SlitPlane` and `g z₀ := F` for
   every off-disc base point.

2. **Flexibility for downstream consumers**: callers who already have
   (or can produce) a global analytic extension on `SlitPlane`
   matching `polyLog` on the disc — for instance, from a
   Hankel-integral construction — can plug into either downstream
   chain via this bridge.

3. **Composition with `polyLog_extension_exists_of_off_disc_data`**:
   chained together, the two give a self-contained `Monodromy →
   Extension` derivation that goes THROUGH the off-disc-patch
   architecture, providing a single, unified residual gap surface.

## What this DOES NOT do

The construction here does NOT discharge `OffDiscPatchData s` from
nothing. It assumes a `PolyLogMonodromyHypothesis s` — which is
itself the load-bearing open hypothesis encoding the polyLog's
analytic continuation off the unit disc. That hypothesis remains
open and requires one of:

* The Jonquières identity in the convergence region near `z = 1`
  (`polyLog_eq_jonquieresExpansion`, OPEN in `Jonquieres.lean`);
* The Hankel-contour integral representation
  (`polyLog_eq_hankel_integral`, OPEN in `PolyLogHankelRealization.lean`);
* A direct analytic-continuation chain via path-lifting on
  `SlitPlane`.

All three are multi-month classical-analysis deliverables not
discharged here.

The Hankel identity content (specifically the agreement between
the polyLog tsum and any candidate off-disc extension at the
unit-disc boundary intersection) is the same content another
agent is working on.

## Architecture summary

```
PolyLogMonodromyHypothesis s         ← named open hypothesis (single F)
        ↓ (this file, axiom-free)
OffDiscPatchData s                   ← named open hypothesis (patch family)
        ↓ (PolyLogLocalPatches.lean, axiom-free)
PolyLogMonodromyHypothesisLocal s    ← local-patch packaging
        ↓ (MonodromyTheorem.lean, axiom-free)
PolyLogAnalyticExtensionExists s     ← top-level extension Prop
```

Stage L11 — OffDiscPatchData construction bridge (2026-05-21).
-/

import PF.Analytic.PolyLogLocalPatches

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Construction: OffDiscPatchData from a global monodromy hypothesis

Given a single analytic function `F : ℂ → ℂ` on `SlitPlane` that
agrees with `polyLog s` on `SlitPlane ∩ ball 0 1`, manufacture the
off-disc patch data trivially:

* `V z₀ := SlitPlane` for every off-disc base.
* `g z₀ := F` for every off-disc base.
* All five geometric fields (`open_V`, `mem_V`, `V_subset`,
  `g_analytic`, `g_agree_disc`) reduce to the two `F`-properties +
  openness of `SlitPlane`.
* `coherent_off_off` is reflexivity (`g z₀ = g z₁ = F`). -/

/-- **OffDiscPatchData from a global monodromy hypothesis (axiom-free)**.

    The off-disc data is manufactured by taking `V z₀ := SlitPlane`
    (an open set containing every `z₀ ∈ SlitPlane`) and `g z₀ := F`
    (the single global witness) for every base point. All six
    structure fields collapse:

    * `open_V` ← `SlitPlane_isOpen`.
    * `mem_V` ← the base point's membership in `SlitPlane`.
    * `V_subset` ← `SlitPlane ⊆ SlitPlane`.
    * `g_analytic` ← `hF_an : AnalyticOnNhd ℂ F SlitPlane`.
    * `g_agree_disc` ← `hF_agree` (the disc-agreement of `F` with
      `polyLog s`).
    * `coherent_off_off` ← reflexivity (same `F` everywhere). -/
noncomputable def offDiscPatchData_of_monodromy
    {s : ℂ} (h : PolyLogMonodromyHypothesis s) :
    OffDiscPatchData s :=
  let F : ℂ → ℂ := Classical.choose h
  let hF : AnalyticOnNhd ℂ F SlitPlane ∧
    (∀ z ∈ SlitPlane ∩ Metric.ball (0 : ℂ) 1, F z = polyLog s z) :=
    Classical.choose_spec h
  { V := fun _ => SlitPlane
    g := fun _ => F
    open_V := fun _ _ _ => SlitPlane_isOpen
    mem_V := fun _ hz₀ _ => hz₀
    V_subset := fun _ _ _ => le_refl _
    g_analytic := fun _ _ _ => hF.1
    g_agree_disc := fun _ _ _ w hw => hF.2 w hw
    coherent_off_off := fun _ _ _ _ _ _ _ _ => rfl }

/-! ## Headline conditional bridges

Two composed forms: starting from a global monodromy hypothesis, we
obtain (a) the off-disc patch data, and (b) the polyLog analytic
extension on `U_slit`. -/

/-- **Bridge**: a global monodromy hypothesis yields off-disc patch
    data axiom-freely. -/
theorem offDiscPatchData_exists_of_monodromy
    {s : ℂ} (h : PolyLogMonodromyHypothesis s) :
    Nonempty (OffDiscPatchData s) :=
  ⟨offDiscPatchData_of_monodromy h⟩

/-- **Headline conditional through the off-disc-patch chain**: a
    global monodromy hypothesis yields the polyLog analytic
    extension, via the unconditional gluing of the off-disc patch
    data with the trivial on-disc patches.

    This provides an alternate path to the conclusion of
    `polyLogAnalyticExtensionExists_of_monodromy` (from
    `PolyLogMonodromyExtension.lean`), routed through the local-
    patch / off-disc-patch architecture. Both paths consume the
    SAME residual hypothesis (a global analytic extension of
    polyLog matching the tsum on the disc), so the two are
    logically interchangeable; this bridge documents the
    equivalence between the structural packagings. -/
theorem polyLog_extension_exists_via_off_disc_of_monodromy
    {s : ℂ} (hs : 0 ≤ s.re) (h : PolyLogMonodromyHypothesis s) :
    PolyLogAnalyticExtensionExists s :=
  polyLog_extension_exists_of_off_disc_data hs
    (offDiscPatchData_of_monodromy h)

/-! ## Status

**Discharged (this file, axiom-free, no `sorry`)**:

* `offDiscPatchData_of_monodromy` — explicit construction of
  `OffDiscPatchData s` from `PolyLogMonodromyHypothesis s`.
* `offDiscPatchData_exists_of_monodromy` — `Nonempty` form.
* `polyLog_extension_exists_via_off_disc_of_monodromy` — composed
  conditional `Monodromy → Extension` routed through the off-disc-
  patch chain.

**Fields of `OffDiscPatchData s` filled axiom-free** (given a
`PolyLogMonodromyHypothesis s` witness): ALL SIX (`open_V`, `mem_V`,
`V_subset`, `g_analytic`, `g_agree_disc`, `coherent_off_off`).

**Fields of `OffDiscPatchData s` UNCONDITIONALLY discharged from
nothing**: zero. The construction here is a REDUCTION, not a
discharge — it converts one named hypothesis into another, smaller
one, in a way that documents their logical equivalence.

**Residual gap (UNRESOLVED)**: `PolyLogMonodromyHypothesis s`. This
is the single named open hypothesis encoding the existence of an
analytic extension of polyLog from the open unit disc to all of
`SlitPlane`. The disc-agreement field of any candidate construction
is the same Hankel-identity content currently being worked on
elsewhere in the project (see `PolyLogHankelRealization.lean` and
`Jonquieres.lean`).

**Why a full discharge of `OffDiscPatchData s` is not feasible in
this session**:

1. The Jonquières expansion `polyLog s z = jonquieresExpansion s z`
   is OPEN (named `JonquieresIdentityHypothesis` in
   `JonquieresIdentity.lean`).

2. The Hankel-contour integral representation
   `polyLog s z = hankelIntegral s z` is OPEN (named in
   `PolyLogHankelRealization.lean`).

3. Both representations would be needed to construct an explicit
   `g z₀` that agrees with the polyLog tsum on the disc-overlap
   region `V z₀ ∩ ball 0 1`. The `g_agree_disc` field is precisely
   this Hankel-identity content.

4. Even the Jonquières expansion's convergence region
   `|log z| < 2π` does NOT cover all of `SlitPlane \ ball 0 1`;
   covering the full off-disc region would require multiple
   coordinate charts (e.g., Jonquières near `z ≈ 1`, the
   `z → 1/z` inversion formula for large `|z|`, plus continuation
   along paths in between).

This file therefore concentrates on the interface-refactor
contribution: shrinking the OffDiscPatchData hypothesis to the
even-simpler PolyLogMonodromyHypothesis form, so that any future
discharge of the latter automatically discharges the former.

Stage L11 — OffDiscPatchData construction bridge (2026-05-21).
-/

end PrincipiaTractalis.Analytic.Sheaf
