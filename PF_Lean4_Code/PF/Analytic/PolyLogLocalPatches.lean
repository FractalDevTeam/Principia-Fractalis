/-
# PolyLog Local Patches — Construction Toward PolyLogMonodromyHypothesisLocal

This file attacks the residual gap identified by `PolyLogMonodromyExtension.lean`
and `MonodromyTheorem.lean`: construct a `PolyLogMonodromyHypothesisLocal s`
witness so that the unconditional monodromy theorem (proved in
`MonodromyTheorem.lean`) yields `PolyLogAnalyticExtensionExists s`.

## The full target (UNRESOLVED at z₀ outside the unit disc)

```
PolyLogMonodromyHypothesisLocal s :=
  ∀ z₀ ∈ SlitPlane, ∃ V open neighborhood, ∃ g analytic on V,
    g agrees with polyLog s on V ∩ ball 0 1, with patch-coherence.
```

The cleanest existing analytic representation of `polyLog s` is the formal
power-series tsum, which is genuinely analytic only on `ball 0 1`. At
`z₀ ∈ SlitPlane` with `‖z₀‖ ≥ 1`, the Jonquières expansion would give the
patch — but that identity (`polyLog_eq_jonquieresExpansion`) is OPEN in
`PF/Analytic/Jonquieres.lean`, and the underlying ζ-series summability is
also open (`JonquieresZetaSeriesSummable.lean`).

## What this file delivers (PROVEN — axiom-free, no `sorry`)

### Stage A — Topological infrastructure

1. **`ball_subset_SlitPlane`** — the open unit ball lies inside the slit
   plane (since `z.re ≤ ‖z‖ < 1` rules out the cut `[1, ∞)`).

2. **`SlitPlaneCapBall`** — the set `SlitPlane ∩ ball 0 1` is precisely
   `ball 0 1` (since `ball 0 1 ⊆ SlitPlane`).

### Stage B — Disc-only patch family (UNCONDITIONAL)

3. **`PolyLogMonodromyHypothesisLocalOnDisc s`** — a weakened patch
   structure requiring local extensions only for `z₀ ∈ SlitPlane ∩ ball 0 1`
   (i.e., effectively `z₀ ∈ ball 0 1`).

4. **`polyLog_local_patches_on_disc`** — UNCONDITIONAL construction of the
   weakened structure: for every `z₀ ∈ ball 0 1`, use `V := ball 0 1`
   and `g := polyLog s`. Analyticity from `polyLog_analyticOnNhd_ball`;
   coherence is trivial (same `g` everywhere).

### Stage C — Reduction of the full local hypothesis to an off-disc gap

5. **`OffDiscPolyLogPatchExists s`** — a clean named Prop encoding the
   residual analytic-continuation content: at every `z₀ ∈ SlitPlane` with
   `‖z₀‖ ≥ 1`, there exists a coherent local patch. This is the precise
   off-disc content of `PolyLogMonodromyHypothesisLocal`.

6. **`polyLog_monodromy_local_of_off_disc_patches`** — given the
   off-disc-patch Prop, assemble the full
   `PolyLogMonodromyHypothesisLocal s` structure. Patches on the disc are
   provided by Stage B; coherence between on- and off-disc patches is
   delegated to the off-disc data.

7. **`polyLog_extension_exists_of_off_disc_patches`** — the headline
   conditional: given `OffDiscPolyLogPatchExists s`, the analytic
   extension `PolyLogAnalyticExtensionExists s` follows by feeding the
   assembled `PolyLogMonodromyHypothesisLocal s` through the unconditional
   monodromy theorem from `MonodromyTheorem.lean`.

## The residual gap (named precisely)

The single residual Prop is `OffDiscPolyLogPatchExists s`:

```
∀ z₀ ∈ SlitPlane, 1 ≤ ‖z₀‖ →
  ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ SlitPlane ∧
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g V ∧
      (∀ w ∈ V ∩ Metric.ball 0 1, g w = polyLog s w) ∧
      (∀ z₁ ∈ SlitPlane, ∀ w ∈ V ∩ {w | w ∈ Metric.ball 0 1 ∨ 1 ≤ ‖w‖},
         True)  -- placeholder coherence consumed downstream
```

(In practice, the cleanest packaging is a `PolyLogMonodromyHypothesisLocal s`
with the on-disc patches restricted to having `V z₀ = ball 0 1`; off-disc
patches come from the residual data and must agree with the on-disc tsum
on their disc intersection. This is the Jonquières / Hankel identity
content.)

## Architecture

* **Stage A**: `ball 0 1 ⊆ SlitPlane`.
* **Stage B**: Unconditional on-disc patch construction.
* **Stage C**: Off-disc reduction Prop + assembly + headline conditional.

Stage L10 — PolyLog local patches (2026-05-20).
-/

import PF.Analytic.MonodromyTheorem

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Stage A: Topological infrastructure -/

/-- **The open unit ball lies in the slit plane**.

    For `z ∈ ball 0 1` we have `‖z‖ < 1`, hence `z.re ≤ ‖z‖ < 1`, so
    `1 ≤ z.re` fails. Therefore `z ∉ BranchCut = {z | z.im = 0 ∧ 1 ≤ z.re}`,
    i.e., `z ∈ SlitPlane = BranchCutᶜ`. -/
theorem ball_subset_SlitPlane :
    Metric.ball (0 : ℂ) 1 ⊆ SlitPlane := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  -- ‖z‖ < 1
  unfold SlitPlane BranchCut
  rw [Set.mem_compl_iff]
  intro ⟨_, h_re⟩
  -- h_re : 1 ≤ z.re; combined with z.re ≤ ‖z‖ < 1, contradiction
  have h_re_le : z.re ≤ ‖z‖ := Complex.re_le_norm z
  linarith

/-- **The intersection `SlitPlane ∩ ball 0 1 = ball 0 1`**. -/
theorem SlitPlane_inter_ball_eq_ball :
    SlitPlane ∩ Metric.ball (0 : ℂ) 1 = Metric.ball (0 : ℂ) 1 := by
  apply Set.inter_eq_self_of_subset_right ball_subset_SlitPlane

/-! ## Stage B: Unconditional on-disc patches

For every `z₀ ∈ ball 0 1` we provide the trivial patch:
* `V z₀ := ball 0 1`
* `g z₀ := polyLog s`
* analyticity of `polyLog s` on `ball 0 1` is `polyLog_analyticOnNhd_ball`
* disc-agreement holds by reflexivity (`g z₀ w = polyLog s w` by definition)
* coherence between any two patches on `ball 0 1` is reflexivity. -/

/-- **Weakened local-hypothesis structure: only on-disc patches**.

    Restricts `PolyLogMonodromyHypothesisLocal` to the case where the
    patch-base point lies in the open unit disc (intersected with
    `SlitPlane`, which by `ball_subset_SlitPlane` adds nothing). -/
structure PolyLogMonodromyHypothesisLocalOnDisc (s : ℂ) where
  /-- Local patch family on the disc. -/
  V : ℂ → Set ℂ
  g : ℂ → (ℂ → ℂ)
  open_V : ∀ z₀ ∈ Metric.ball (0 : ℂ) 1, IsOpen (V z₀)
  mem_V : ∀ z₀ ∈ Metric.ball (0 : ℂ) 1, z₀ ∈ V z₀
  V_subset_disc_inter_slit : ∀ z₀ ∈ Metric.ball (0 : ℂ) 1,
    V z₀ ⊆ SlitPlane ∩ Metric.ball (0 : ℂ) 1
  g_analytic : ∀ z₀ ∈ Metric.ball (0 : ℂ) 1,
    AnalyticOnNhd ℂ (g z₀) (V z₀)
  g_agree_disc : ∀ z₀ ∈ Metric.ball (0 : ℂ) 1,
    ∀ w ∈ V z₀ ∩ Metric.ball (0 : ℂ) 1, g z₀ w = polyLog s w
  patch_coherent : ∀ z₀ ∈ Metric.ball (0 : ℂ) 1,
    ∀ z₁ ∈ Metric.ball (0 : ℂ) 1,
    ∀ w ∈ V z₀ ∩ V z₁, g z₀ w = g z₁ w

/-- **Unconditional construction of on-disc patches** for any `s` with
    `0 ≤ Re s`.

    Trivial choice: `V z₀ = ball 0 1` (independent of `z₀`),
    `g z₀ = polyLog s`. Analyticity from `polyLog_analyticOnNhd_ball`;
    coherence is reflexivity since `g z₀ = g z₁` as functions. -/
noncomputable def polyLog_local_patches_on_disc {s : ℂ} (hs : 0 ≤ s.re) :
    PolyLogMonodromyHypothesisLocalOnDisc s where
  V := fun _ => Metric.ball (0 : ℂ) 1
  g := fun _ => polyLog s
  open_V := fun _ _ => Metric.isOpen_ball
  mem_V := fun _ hz₀ => hz₀
  V_subset_disc_inter_slit := fun _ _ => by
    intro w hw
    refine ⟨?_, hw⟩
    exact ball_subset_SlitPlane hw
  g_analytic := fun _ _ => polyLog_analyticOnNhd_ball hs
  g_agree_disc := fun _ _ _ _ => rfl
  patch_coherent := fun _ _ _ _ _ _ => rfl

/-! ## Stage C: Reduction of the full local hypothesis

To assemble the full `PolyLogMonodromyHypothesisLocal s`, we need patches
at every `z₀ ∈ SlitPlane`, including those outside the open unit disc.

The cleanest packaging: define a `Prop` that asserts the existence of a
full local-patch family. The full structure follows by taking that Prop
directly (this is the trivial reduction: the off-disc Prop IS the full
structure).

A more refined packaging would isolate the off-disc patches and glue
them to the on-disc ones. We provide both forms. -/

/-- **The off-disc patch Prop**: there exists a complete local-patch
    family on `SlitPlane`. This is logically equivalent to
    `Nonempty (PolyLogMonodromyHypothesisLocal s)` and isolates the
    residual analytic-continuation content. -/
def OffDiscPolyLogPatchExists (s : ℂ) : Prop :=
  Nonempty (PolyLogMonodromyHypothesisLocal s)

/-- **Headline conditional**: given the off-disc patch existence
    (equivalently, a complete local-patch family on `SlitPlane`), the
    polyLog analytic extension exists.

    This is the FULL CHAIN:
    * Off-disc patches provide `PolyLogMonodromyHypothesisLocal s`.
    * The unconditional monodromy theorem
      `polyLogAnalyticExtensionExists_of_local_monodromy_unconditional`
      from `MonodromyTheorem.lean` produces
      `PolyLogAnalyticExtensionExists s`. -/
theorem polyLog_extension_exists_of_off_disc_patches
    {s : ℂ} (hoff : OffDiscPolyLogPatchExists s) :
    PolyLogAnalyticExtensionExists s := by
  obtain ⟨H⟩ := hoff
  exact polyLogAnalyticExtensionExists_of_local_monodromy_unconditional H

/-! ### A more granular reduction: glue on-disc patches with explicit
    off-disc data.

The structure below packages the residual off-disc work in a finer way
than the all-or-nothing `OffDiscPolyLogPatchExists` Prop. It records:

* For each `z₀ ∈ SlitPlane` with `1 ≤ ‖z₀‖`, an explicit patch
  `(V z₀, g z₀)` with the required properties.
* Cross-coherence between off-disc and on-disc patches.

We then assemble the full `PolyLogMonodromyHypothesisLocal` by case-
splitting on whether `‖z₀‖ < 1`. -/

/-- **Granular off-disc patch data**: for each `z₀ ∈ SlitPlane` with
    `1 ≤ ‖z₀‖`, an explicit local extension of `polyLog s`.

    The `g_agree_polyLog` coherence is the key off-disc content: any
    point `w` of the patch that happens to lie in the unit disc
    must satisfy `g z₀ w = polyLog s w` (so the patch agrees with the
    tsum on its disc intersection — this is the Jonquières/Hankel
    identity content). -/
structure OffDiscPatchData (s : ℂ) where
  V : ℂ → Set ℂ
  g : ℂ → (ℂ → ℂ)
  open_V : ∀ z₀ ∈ SlitPlane, 1 ≤ ‖z₀‖ → IsOpen (V z₀)
  mem_V : ∀ z₀ ∈ SlitPlane, 1 ≤ ‖z₀‖ → z₀ ∈ V z₀
  V_subset : ∀ z₀ ∈ SlitPlane, 1 ≤ ‖z₀‖ → V z₀ ⊆ SlitPlane
  g_analytic : ∀ z₀ ∈ SlitPlane, 1 ≤ ‖z₀‖ → AnalyticOnNhd ℂ (g z₀) (V z₀)
  g_agree_disc : ∀ z₀ ∈ SlitPlane, 1 ≤ ‖z₀‖ →
    ∀ w ∈ V z₀ ∩ Metric.ball (0 : ℂ) 1, g z₀ w = polyLog s w
  /-- Coherence between two off-disc patches. -/
  coherent_off_off : ∀ z₀ ∈ SlitPlane, 1 ≤ ‖z₀‖ →
    ∀ z₁ ∈ SlitPlane, 1 ≤ ‖z₁‖ →
    ∀ w ∈ V z₀ ∩ V z₁, g z₀ w = g z₁ w

/-- **Helper choice**: pick an off-disc patch base from `SlitPlane`
    (the witness `-1` from `neg_one_mem_SlitPlane`, which has norm 1). -/
private theorem off_disc_default_in_SlitPlane :
    (-1 : ℂ) ∈ SlitPlane := neg_one_mem_SlitPlane

private theorem off_disc_default_norm_ge_one :
    (1 : ℝ) ≤ ‖(-1 : ℂ)‖ := by
  rw [norm_neg, norm_one]

/-- **Assembly**: given `OffDiscPatchData s` (the residual off-disc
    analytic-continuation content), construct the full
    `PolyLogMonodromyHypothesisLocal s` by gluing with the trivial
    on-disc patches.

    The construction:
    * If `z₀ ∈ ball 0 1`: use the on-disc patch
      `V := ball 0 1, g := polyLog s`.
    * Else (`1 ≤ ‖z₀‖`): use the off-disc data
      `V := off.V z₀, g := off.g z₀`.

    The on-disc / off-disc coherence is exactly the off-disc
    `g_agree_disc` (when an off-disc patch contains a disc point, it
    agrees with `polyLog s` there, hence with the on-disc `g`). -/
noncomputable def polyLog_local_patches_of_off_disc
    {s : ℂ} (hs : 0 ≤ s.re) (off : OffDiscPatchData s) :
    PolyLogMonodromyHypothesisLocal s where
  V := fun z₀ =>
    if ‖z₀‖ < 1 then Metric.ball (0 : ℂ) 1 else off.V z₀
  g := fun z₀ =>
    if ‖z₀‖ < 1 then polyLog s else off.g z₀
  open_V := by
    intro z₀ hz₀
    by_cases h : ‖z₀‖ < 1
    · simp only [if_pos h]; exact Metric.isOpen_ball
    · simp only [if_neg h]
      exact off.open_V z₀ hz₀ (not_lt.mp h)
  mem_V := by
    intro z₀ hz₀
    by_cases h : ‖z₀‖ < 1
    · simp only [if_pos h]
      rw [Metric.mem_ball, dist_zero_right]; exact h
    · simp only [if_neg h]
      exact off.mem_V z₀ hz₀ (not_lt.mp h)
  V_subset := by
    intro z₀ hz₀
    by_cases h : ‖z₀‖ < 1
    · simp only [if_pos h]; exact ball_subset_SlitPlane
    · simp only [if_neg h]
      exact off.V_subset z₀ hz₀ (not_lt.mp h)
  g_analytic := by
    intro z₀ hz₀
    by_cases h : ‖z₀‖ < 1
    · simp only [if_pos h]
      exact polyLog_analyticOnNhd_ball hs
    · simp only [if_neg h]
      exact off.g_analytic z₀ hz₀ (not_lt.mp h)
  g_agree_disc := by
    intro z₀ hz₀ w hw
    by_cases h : ‖z₀‖ < 1
    · simp only [if_pos h] at hw ⊢
    · simp only [if_neg h] at hw ⊢
      exact off.g_agree_disc z₀ hz₀ (not_lt.mp h) w hw
  patch_coherent := by
    intro z₀ hz₀ z₁ hz₁ w hw
    obtain ⟨hw₀, hw₁⟩ := hw
    by_cases h₀ : ‖z₀‖ < 1
    · by_cases h₁ : ‖z₁‖ < 1
      · -- Both on-disc: g z₀ = g z₁ = polyLog s
        simp only [if_pos h₀, if_pos h₁]
      · -- z₀ on-disc, z₁ off-disc: need g z₀ w = g z₁ w
        -- g z₀ w = polyLog s w (on-disc def)
        -- g z₁ w = off.g z₁ w; w ∈ off.V z₁ ∩ ball 0 1 (from hw₁ and h₀-derived membership of w in ball)
        simp only [if_pos h₀] at hw₀
        simp only [if_neg h₁] at hw₁
        simp only [if_pos h₀, if_neg h₁]
        -- w ∈ Metric.ball 0 1 from hw₀
        symm
        exact off.g_agree_disc z₁ hz₁ (not_lt.mp h₁) w ⟨hw₁, hw₀⟩
    · by_cases h₁ : ‖z₁‖ < 1
      · -- z₀ off-disc, z₁ on-disc: symmetric to above
        simp only [if_neg h₀] at hw₀
        simp only [if_pos h₁] at hw₁
        simp only [if_neg h₀, if_pos h₁]
        exact off.g_agree_disc z₀ hz₀ (not_lt.mp h₀) w ⟨hw₀, hw₁⟩
      · -- Both off-disc
        simp only [if_neg h₀] at hw₀
        simp only [if_neg h₁] at hw₁
        simp only [if_neg h₀, if_neg h₁]
        exact off.coherent_off_off z₀ hz₀ (not_lt.mp h₀) z₁ hz₁ (not_lt.mp h₁) w ⟨hw₀, hw₁⟩

/-- **Headline conditional via granular data**: given `OffDiscPatchData s`
    (the residual off-disc analytic-continuation infrastructure), the
    polyLog analytic extension exists. -/
theorem polyLog_extension_exists_of_off_disc_data
    {s : ℂ} (hs : 0 ≤ s.re) (off : OffDiscPatchData s) :
    PolyLogAnalyticExtensionExists s :=
  polyLogAnalyticExtensionExists_of_local_monodromy_unconditional
    (polyLog_local_patches_of_off_disc hs off)

/-! ## Status and roadmap

**Discharged (this file, axiom-free, no `sorry`)**:

* `ball_subset_SlitPlane` — the open unit ball lies in the slit plane.
* `SlitPlane_inter_ball_eq_ball` — `SlitPlane ∩ ball 0 1 = ball 0 1`.
* `PolyLogMonodromyHypothesisLocalOnDisc s` — weakened on-disc local form.
* `polyLog_local_patches_on_disc` — UNCONDITIONAL construction of the
  weakened on-disc form (trivial trivial-patch family
  `V z₀ = ball 0 1`, `g z₀ = polyLog s`).
* `OffDiscPolyLogPatchExists s` — clean Prop for the residual gap.
* `polyLog_extension_exists_of_off_disc_patches` — headline conditional
  via the off-disc Prop.
* `OffDiscPatchData s` — granular structural data for the off-disc gap.
* `polyLog_local_patches_of_off_disc` — UNCONDITIONAL assembly of the
  full `PolyLogMonodromyHypothesisLocal` from `OffDiscPatchData` +
  on-disc patches.
* `polyLog_extension_exists_of_off_disc_data` — headline conditional via
  the granular off-disc data.

**Residual gap (UNRESOLVED)**: construction of `OffDiscPatchData s`
(equivalently, `OffDiscPolyLogPatchExists s`). At each `z₀ ∈ SlitPlane`
with `1 ≤ ‖z₀‖`, this requires a local analytic representation of
`polyLog s` (i.e., the Jonquières expansion near `z₀ ≈ 1`, the Hankel
contour integral globally, or a direct analytic-continuation chain).

The Jonquières-route open identities:
* `polyLog_eq_jonquieresExpansion` from `PF/Analytic/Jonquieres.lean`.
* `JonquieresZetaSummable_classical` from
  `PF/Analytic/JonquieresZetaSeriesSummable.lean`.

The Hankel-route open identities:
* `polyLog_eq_hankel_integral` from `PF/Analytic/PolyLogHankelRealization.lean`.

Both routes are multi-month classical-analysis formalization deliverables.
This file does NOT discharge them; instead, it cleanly reduces the
analytic-extension target to the precise residual gap, packaged as
`OffDiscPatchData s` for downstream consumption.

**What this file's contribution to the load-bearing chain looks like**:

```
Local on-disc patches  (PROVEN, UNCONDITIONAL)
  +
Off-disc patch data    (RESIDUAL GAP — Jonquières/Hankel)
  ↓
Full PolyLogMonodromyHypothesisLocal s   (assembled, UNCONDITIONAL given the data)
  ↓ via MonodromyGluingLemma_proven (UNCONDITIONAL, MonodromyTheorem.lean)
PolyLogAnalyticExtensionExists s
```

The chain is **fully mechanized** except for the off-disc analytic
continuation, which is the precise residual content of the manuscript's
load-bearing open claim.

Stage L10 — PolyLog local patches (2026-05-20).
-/

end PrincipiaTractalis.Analytic.Sheaf
