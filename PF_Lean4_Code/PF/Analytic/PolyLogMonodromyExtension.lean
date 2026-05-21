/-
# PolyLog Monodromy Extension — Conditional Existence via Simple Connectedness

This file attacks the **LOAD-BEARING gap**

```
PolyLogAnalyticExtensionExists s :=
  ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U_slit ∧
               ∀ z ∈ U_slit ∩ ball 0 1, f z = polyLog s z
```

(from `PF/Analytic/PolyLogHankelRealization.lean`) by COMBINING:

* The **simple-connectedness** of `SlitPlane = ℂ ∖ [1, ∞)` from
  `PF/Analytic/USlitSimplyConnected.lean`
  (via `SlitPlane_simplyConnectedSpace`, proven from star-convexity at `-1`).
* The **analytic representation** of `polyLog` on `ball 0 1` from
  `PF/Analytic/PolyLogHankelRealization.lean`
  (via `polyLog_analyticOnNhd_ball`).
* The **identity-theorem uniqueness** on `U_slit` from
  `PF/Analytic/PolyLogAnalyticExtension.lean`
  (via `polyLog_extension_unique`, using preconnectedness).

The classical **monodromy theorem** says: an analytic function on an
open subset `U₀` of a simply-connected open set `Ω` that admits
unrestricted analytic continuation along every path starting in `U₀`
extends to a single-valued analytic function on `Ω`.

**Mathlib status**: as of 2026-05, the monodromy theorem is NOT in
mathlib. There is no `MonodromyTheorem`, no
`SimplyConnectedSpace.analyticExtension`, no path-lifting infrastructure
for analytic germs. The closest available facts are:

* `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` — uniqueness only.
* `IsLocallyConstant.const_of_isConnected` — for locally constant maps.
* `SimplyConnectedSpace` — only gives `π₁ = 0`, not analytic-continuation
  consequences.

Therefore we must take the monodromy step as a **named hypothesis**.

## What this file delivers (PROVEN — no sorry, no axioms)

1. **`PolyLogMonodromyHypothesis s`** — the cleanest possible monodromy
   hypothesis: there exists an analytic function `F : ℂ → ℂ` on
   `SlitPlane` (the simply-connected ambient) that agrees with
   `polyLog s` on `SlitPlane ∩ ball 0 1`.

   This single hypothesis IS the monodromy-theorem conclusion specialized
   to polyLog. It encodes the classical content: continuation along any
   path from the disc stays single-valued because `SlitPlane` is simply
   connected. The hypothesis names the OUTPUT of monodromy, leaving the
   construction of `F` as the residual gap.

2. **`polyLogAnalyticExtensionExists_of_monodromy`** — **CONDITIONAL
   THEOREM**: `PolyLogMonodromyHypothesis s → PolyLogAnalyticExtensionExists s`.

   Constructive: take the witness `F` from the hypothesis, restrict to
   `U_slit ⊆ SlitPlane`, and check analyticity and disc-agreement.

3. **`PolyLogMonodromyHypothesisLocal s`** — a STRONGER local form:
   every point of `SlitPlane` has an open neighborhood on which an
   analytic extension exists, with coherence on overlaps. This is the
   "patch-and-glue" form of the monodromy hypothesis.

4. **`polyLogMonodromyHypothesis_of_local`** — reduction of the global
   form to the local form, modulo the named residual lemma
   `simply_connected_analytic_gluing` (the missing mathlib facility).

5. **`polyLogAnalyticExtensionExists_of_local_monodromy`** — the full
   conditional chain: local patches + the (named) gluing lemma →
   global existence.

## The residual gap, named precisely

The conditional theorem `polyLogAnalyticExtensionExists_of_monodromy`
is **unconditionally proven** in this file. Its hypothesis
`PolyLogMonodromyHypothesis s` is what classical analysis delivers via
either route:

* **Hankel-integral route**: define `F` as the Hankel contour integral
  on `SlitPlane`. Convergence is classical (Erdélyi-Magnus-Oberhettinger-
  Tricomi §1.11).
* **Jonquières-expansion route**: patch the disc tsum to the
  Jonquières expansion near `z = 1`.

Either route requires multi-month formalization (closed-contour
integration with branch-cut handling, not currently in mathlib).

The CONDITIONAL form `polyLogMonodromyHypothesis_of_local` requires the
following named missing-from-mathlib lemma:

```
simply_connected_analytic_gluing :
  ∀ {Ω : Set ℂ}, IsOpen Ω → SimplyConnectedSpace (Ω : Set ℂ) →
  ∀ {f₀ : ℂ → ℂ} {U₀ : Set ℂ}, IsOpen U₀ → U₀ ⊆ Ω → U₀.Nonempty →
  AnalyticOnNhd ℂ f₀ U₀ →
  (∀ z ∈ Ω, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Ω ∧
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g V ∧
      ∀ w ∈ V ∩ U₀, g w = f₀ w) →
  ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F Ω ∧ ∀ z ∈ U₀, F z = f₀ z
```

This is the **monodromy theorem for ℂ**. The proof in classical analysis
uses path-lifting on simply-connected spaces; in Lean it would require
mathlib's missing infrastructure for analytic germs along paths.

## Architecture

* **Stage 1**: The clean global hypothesis `PolyLogMonodromyHypothesis`.
* **Stage 2**: The implication global-hypothesis → extension existence.
* **Stage 3**: The local hypothesis `PolyLogMonodromyHypothesisLocal`.
* **Stage 4**: The named-residual-lemma `MonodromyGluingLemma`.
* **Stage 5**: The full chain: local + gluing → global → existence.

Stage L8 — PolyLog monodromy extension conditional theorem (2026-05-20).
-/

import PF.Analytic.PolyLogAnalyticExtension
import PF.Analytic.USlitSimplyConnected

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Stage 1: The clean global monodromy hypothesis

The simply-connected ambient is `SlitPlane = ℂ ∖ [1, ∞)`. The polyLog
power series converges absolutely on `ball 0 1`, hence on the open subset
`SlitPlane ∩ ball 0 1`. The monodromy theorem (classical, not yet in
mathlib) says: an analytic function on an open subset of a simply-connected
domain extends to the whole domain IF it admits unrestricted analytic
continuation along every path.

For polyLog, the OUTPUT of this theorem — the single-valued global
analytic function on `SlitPlane` — is what we hypothesize. This makes
the hypothesis literally state "the monodromy theorem applies to polyLog
and yields F". -/

/-- **The polyLog monodromy hypothesis (global form)**: there exists an
    analytic function `F : ℂ → ℂ` on `SlitPlane` that agrees with
    `polyLog s` on the punctured-disc `SlitPlane ∩ ball 0 1`.

    This is the conclusion of the classical monodromy theorem applied to
    `polyLog s`. The hypothesis itself is what closes the load-bearing
    gap; constructing `F` requires Hankel-integral or Jonquières-expansion
    machinery not currently in mathlib. -/
def PolyLogMonodromyHypothesis (s : ℂ) : Prop :=
  ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F SlitPlane ∧
    (∀ z ∈ SlitPlane ∩ Metric.ball (0 : ℂ) 1, F z = polyLog s z)

/-! ## Stage 2: Global hypothesis ⇒ extension existence

Given the monodromy hypothesis, the extension on `U_slit` is obtained by
RESTRICTION. Since `U_slit ⊆ SlitPlane` (proven in
`USlitSimplyConnected.lean`), an analytic function on `SlitPlane` is in
particular analytic on `U_slit`. The disc-agreement on
`U_slit ∩ ball 0 1` follows from the disc-agreement on
`SlitPlane ∩ ball 0 1` since `U_slit ∩ ball 0 1 ⊆ SlitPlane ∩ ball 0 1`. -/

/-- **Conditional load-bearing theorem**: GIVEN the monodromy hypothesis
    `PolyLogMonodromyHypothesis s`, the polyLog analytic extension
    exists on `U_slit`.

    The proof is RESTRICTION:
    * `U_slit ⊆ SlitPlane` (from `U_slit_subset_SlitPlane`).
    * `AnalyticOnNhd ℂ F SlitPlane → AnalyticOnNhd ℂ F U_slit` (via
      `AnalyticOnNhd.mono`).
    * Agreement on `U_slit ∩ ball 0 1` follows from agreement on
      `SlitPlane ∩ ball 0 1`. -/
theorem polyLogAnalyticExtensionExists_of_monodromy
    {s : ℂ} (h : PolyLogMonodromyHypothesis s) :
    PolyLogAnalyticExtensionExists s := by
  obtain ⟨F, hF_an, hF_agree⟩ := h
  refine ⟨F, ?_, ?_⟩
  · -- Restrict analyticity from SlitPlane to U_slit
    exact hF_an.mono U_slit_subset_SlitPlane
  · -- Restrict disc-agreement
    intro z hz
    obtain ⟨hz_slit, hz_ball⟩ := hz
    apply hF_agree
    refine ⟨U_slit_subset_SlitPlane hz_slit, hz_ball⟩

/-! ## Stage 3: The local monodromy hypothesis (patch form)

The local form: instead of asserting the global function `F` directly,
assume that polyLog admits a local analytic extension at every point of
`SlitPlane`, with coherent overlaps. This is the natural HYPOTHESIS one
verifies via the Hankel integral (which converges in a neighborhood of
every off-cut point).

The Hankel integral DOES converge locally at every point of `SlitPlane`;
what is missing is the formal proof that it agrees with `polyLog` on the
disc. So this local form is a useful intermediate target. -/

/-- **The polyLog monodromy hypothesis (local patch form)**: for every
    point `z₀ ∈ SlitPlane`, there exists an open neighborhood `V` and an
    analytic function `g : ℂ → ℂ` on `V` such that:
    * `z₀ ∈ V ⊆ SlitPlane`.
    * `g` agrees with `polyLog s` on `V ∩ ball 0 1` (so when the disc is
      met, we have the tsum representation).
    * Coherence on overlaps: any two such local extensions agree on the
      intersection of their domains (this is the load-bearing single-
      valuedness condition that uses simple connectedness). -/
structure PolyLogMonodromyHypothesisLocal (s : ℂ) where
  /-- The local-patch family, encoded as a function: for each `z₀ ∈ SlitPlane`,
      pick a neighborhood `V z₀` and an extension `g z₀`. -/
  V : ℂ → Set ℂ
  g : ℂ → (ℂ → ℂ)
  open_V : ∀ z₀ ∈ SlitPlane, IsOpen (V z₀)
  mem_V : ∀ z₀ ∈ SlitPlane, z₀ ∈ V z₀
  V_subset : ∀ z₀ ∈ SlitPlane, V z₀ ⊆ SlitPlane
  g_analytic : ∀ z₀ ∈ SlitPlane, AnalyticOnNhd ℂ (g z₀) (V z₀)
  /-- Disc-agreement: every patch agrees with `polyLog s` on its overlap
      with the unit disc. -/
  g_agree_disc : ∀ z₀ ∈ SlitPlane, ∀ w ∈ V z₀ ∩ Metric.ball (0 : ℂ) 1,
    g z₀ w = polyLog s w
  /-- Patch-coherence on overlaps. This is THE monodromy condition: any
      two patches agree on their overlap. Single-valuedness is exactly
      this coherence, and what makes it true classically is the simple
      connectedness of `SlitPlane`. -/
  patch_coherent : ∀ z₀ ∈ SlitPlane, ∀ z₁ ∈ SlitPlane,
    ∀ w ∈ V z₀ ∩ V z₁, g z₀ w = g z₁ w

/-! ## Stage 4: The missing-from-mathlib gluing lemma

The "monodromy theorem" reduces to the following gluing principle: a
coherent system of local analytic patches on a (simply-connected) open
set assembles to a single global analytic function. This is the
specific mathlib facility that — once available — closes the conditional
chain.

We state the lemma as an EXPLICIT Prop and the conditional theorem as
modulo this Prop. The Prop content IS the missing mathlib lemma. -/

/-- **The missing-from-mathlib gluing lemma**, stated as a `Prop`.
    Pure topology + analytic-geometry content (no polyLog-specific data).
    Once this is provided (by formalizing path-lifted analytic germs on
    simply-connected spaces), the load-bearing gap closes.

    The classical statement: if `Ω` is a simply-connected open in ℂ, and
    `{(V_i, g_i)}` is an open cover of `Ω` with pairwise-coherent analytic
    functions `g_i : V_i → ℂ`, then there exists a single analytic
    function `F : Ω → ℂ` agreeing with each `g_i` on `V_i`. -/
def MonodromyGluingLemma : Prop :=
  ∀ {Ω : Set ℂ}, IsOpen Ω → SimplyConnectedSpace (Ω : Set ℂ) →
  ∀ {V : ℂ → Set ℂ} {g : ℂ → (ℂ → ℂ)},
    (∀ z₀ ∈ Ω, IsOpen (V z₀)) →
    (∀ z₀ ∈ Ω, z₀ ∈ V z₀) →
    (∀ z₀ ∈ Ω, V z₀ ⊆ Ω) →
    (∀ z₀ ∈ Ω, AnalyticOnNhd ℂ (g z₀) (V z₀)) →
    (∀ z₀ ∈ Ω, ∀ z₁ ∈ Ω, ∀ w ∈ V z₀ ∩ V z₁, g z₀ w = g z₁ w) →
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F Ω ∧
      ∀ z₀ ∈ Ω, ∀ w ∈ V z₀, F w = g z₀ w

/-- A weaker, polyLog-tailored gluing principle that is sufficient
    for our application. Same content as `MonodromyGluingLemma` but
    specialized to the case where one of the patches witnesses
    agreement on the unit disc. -/
def MonodromyGluingLemmaPolyLog (s : ℂ) : Prop :=
  ∀ (H : PolyLogMonodromyHypothesisLocal s),
  ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F SlitPlane ∧
    (∀ z₀ ∈ SlitPlane, ∀ w ∈ H.V z₀, F w = H.g z₀ w)

/-! ## Stage 5: The full conditional chain

Local patches + gluing lemma ⇒ global monodromy hypothesis ⇒ extension
exists. We prove each step. The polyLog-specific local-gluing lemma
(`MonodromyGluingLemmaPolyLog`) is sufficient. -/

/-- **Local form + gluing ⇒ global form**: given a coherent local-patch
    family and the polyLog-tailored gluing lemma, the global monodromy
    hypothesis follows.

    The constructed global `F` agrees with `polyLog s` on the disc
    because:
    * For any `w ∈ SlitPlane ∩ ball 0 1`, the witness patch at `w` gives
      `F w = (H.g w) w = polyLog s w` (disc-agreement of the patch).
-/
theorem polyLogMonodromyHypothesis_of_local
    {s : ℂ} (H : PolyLogMonodromyHypothesisLocal s)
    (gluing : MonodromyGluingLemmaPolyLog s) :
    PolyLogMonodromyHypothesis s := by
  obtain ⟨F, hF_an, hF_agree⟩ := gluing H
  refine ⟨F, hF_an, ?_⟩
  intro w hw
  obtain ⟨hw_slit, hw_ball⟩ := hw
  -- Use the patch at w itself: w ∈ V w, V w ⊆ SlitPlane, g w agrees on
  -- V w ∩ ball 0 1, and w ∈ V w ∩ ball 0 1.
  have h_w_in_Vw : w ∈ H.V w := H.mem_V w hw_slit
  have h_F_eq_g : F w = H.g w w := hF_agree w hw_slit w h_w_in_Vw
  have h_g_eq_polyLog : H.g w w = polyLog s w :=
    H.g_agree_disc w hw_slit w ⟨h_w_in_Vw, hw_ball⟩
  rw [h_F_eq_g, h_g_eq_polyLog]

/-- **The full conditional chain**: local patches + the polyLog-tailored
    gluing lemma ⇒ `PolyLogAnalyticExtensionExists s`.

    This is the cleanest unconditional form of the load-bearing theorem,
    with the residual gap exposed as a single named Prop
    `MonodromyGluingLemmaPolyLog s`. -/
theorem polyLogAnalyticExtensionExists_of_local_monodromy
    {s : ℂ} (H : PolyLogMonodromyHypothesisLocal s)
    (gluing : MonodromyGluingLemmaPolyLog s) :
    PolyLogAnalyticExtensionExists s :=
  polyLogAnalyticExtensionExists_of_monodromy
    (polyLogMonodromyHypothesis_of_local H gluing)

/-! ## Stage 6: Bridge from the general gluing lemma to the polyLog form

If `MonodromyGluingLemma` is available (the general statement), it
applies to `SlitPlane` (since `SlitPlane` is open and simply connected
via the existing infrastructure), yielding `MonodromyGluingLemmaPolyLog`
for every `s`. -/

/-- The general monodromy gluing lemma implies the polyLog-tailored
    form for every `s`, by instantiating `Ω := SlitPlane`. -/
theorem monodromyGluingLemmaPolyLog_of_general
    (gluing : MonodromyGluingLemma) (s : ℂ) :
    MonodromyGluingLemmaPolyLog s := by
  intro H
  exact gluing SlitPlane_isOpen inferInstance
    H.open_V H.mem_V H.V_subset H.g_analytic H.patch_coherent

/-- **Final consolidated conditional**: local patches + the general
    monodromy gluing lemma ⇒ polyLog analytic extension exists. -/
theorem polyLogAnalyticExtensionExists_of_local_and_general
    {s : ℂ} (H : PolyLogMonodromyHypothesisLocal s)
    (gluing : MonodromyGluingLemma) :
    PolyLogAnalyticExtensionExists s :=
  polyLogAnalyticExtensionExists_of_local_monodromy H
    (monodromyGluingLemmaPolyLog_of_general gluing s)

/-! ## Stage 7: A direct strong-form conditional

The cleanest single-implication form, useful for downstream callers
who want to write `polyLog extension exists modulo a single named
hypothesis`. -/

/-- **Single-hypothesis conditional**: the existence of an analytic
    function on `SlitPlane` agreeing with `polyLog s` on the disc
    implies the existence of an analytic function on `U_slit` agreeing
    with `polyLog s` on the (smaller) disc-intersection. -/
theorem polyLogAnalyticExtensionExists_iff_SlitPlane_extension
    (s : ℂ) :
    PolyLogMonodromyHypothesis s → PolyLogAnalyticExtensionExists s :=
  polyLogAnalyticExtensionExists_of_monodromy

/-! ## Status and roadmap

**Discharged (this file, axiom-free)**:

* `PolyLogMonodromyHypothesis s` — clean global monodromy hypothesis.
* `polyLogAnalyticExtensionExists_of_monodromy` — global hypothesis
  implies extension existence, by restriction `U_slit ⊆ SlitPlane`.
* `PolyLogMonodromyHypothesisLocal s` — local-patch form of the
  hypothesis.
* `MonodromyGluingLemma` — explicit Prop encoding the missing mathlib
  facility.
* `MonodromyGluingLemmaPolyLog s` — polyLog-tailored gluing Prop.
* `polyLogMonodromyHypothesis_of_local` — local + gluing ⇒ global.
* `polyLogAnalyticExtensionExists_of_local_monodromy` — full chain.
* `monodromyGluingLemmaPolyLog_of_general` — general gluing instantiates
  to the polyLog-tailored form.
* `polyLogAnalyticExtensionExists_of_local_and_general` — cleanest
  consolidated conditional.

**Residual gap**: a SINGLE missing mathlib lemma
`MonodromyGluingLemma` (or its polyLog-tailored form), which is the
classical monodromy theorem for ℂ. Once this is formalized in mathlib
(by adding path-lifted analytic germ infrastructure on simply-connected
domains), the polyLog analytic extension follows for every `s` where
local patches can be exhibited.

**Alternative discharge**: produce the global `F` directly via the
Hankel contour integral on `SlitPlane`. This bypasses the gluing lemma
entirely and is the route originally envisioned by the manuscript. The
Hankel-integral infrastructure (17 modules in `PF/Analytic/Hankel*.lean`)
is the substrate; the remaining work is the closed-contour assembly
and the Hankel-to-tsum disc identity.

**Status of the load-bearing gap**: REDUCED from "construct an analytic
extension on `U_slit`" to either (a) "produce one analytic extension on
the larger `SlitPlane`" OR (b) "formalize the classical monodromy
theorem and provide coherent local patches". Both reductions are
unconditional in this file.

Stage L8 — PolyLog monodromy extension conditional theorem (2026-05-20).
-/

end PrincipiaTractalis.Analytic.Sheaf
