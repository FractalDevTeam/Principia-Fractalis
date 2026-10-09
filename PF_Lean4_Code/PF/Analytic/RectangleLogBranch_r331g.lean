/-
# r331g — RECTANGLE LOG-BRANCH BRIDGE: closed-form evaluation of
#          `RectangleIntegral' (logDeriv ξ) zF wF`

★ **ELABORATES CLEAN — kernel-verified 2026-10-08.** `lake env lean` on this
  file exits 0 with **zero diagnostics** (Lean 4.24.0-rc1, mathlib
  `eed770a4`, imports r325/r326/r327 at current oleans). `#print axioms` on
  `rectangleIntegral'_logDeriv_eq_of_branch_chain`,
  `rectangleIntegral'_logDeriv_eq_of_right_edge_chain`,
  `hIntegral_logDeriv_eq_log_sub` and `log_neg_I_mul_sub_log` each returns
  exactly `[propext, Classical.choice, Quot.sound]` — **zero project axioms**,
  no `sorry`, no `native_decide`. The design needed no tactic repair; it went
  through on the first elaboration pass.

  This closes the blocker named in `codex/RH_BELOW_15_ROUTE_2026-10-01.md`:
  *"nothing turns `RectangleIntegral' (logDeriv ξ) zF wF` into a number."*
  It now does, conditional on the standing sign hypotheses below.

  **Remaining distance to `RectangleIntegral' = 2`:** of the seven hypotheses
  standing in `rectangleIntegral'_logDeriv_eq_of_right_edge_chain`, the bottom
  edge is proved at `RiemannXiBottomEdgeAtMinus15_r331d:87` and the top edge at
  `RiemannXiTopEdge_r331c:76`. **Three genuinely new half-plane sign facts
  remain — R1, R2, R3 on `t ∈ [0,15]`** — their `t ∈ [-15,0]` mirrors being
  discharged by §6 from r326's reflection. That is the whole gap. ★

## What this file is for

`codex/RH_BELOW_15_ROUTE_2026-10-01.md` §3 and §9.1. The argument principle on a
rectangle is already in the corpus and already instantiated on `[0,1] × [-15,15]`
(`PF/Analytic/RectangleArgumentPrinciple_r327.lean`,
`PF/Analytic/RiemannXiFullRectangleBoundary_r331e.lean:171`). What was missing is
the layer above: nothing turned `RectangleIntegral' (logDeriv ξ) zF wF` into a
number. This file is that bridge.

The mechanism, with no winding number and no numerics inside the integral:

1. **Rotated branch primitives.** For `ω ≠ 0`, if `ω · f` stays in
   `Complex.slitPlane` along an edge segment, then `s ↦ Complex.log (ω * f s)` is
   a primitive of `logDeriv f` there — the `ω` cancels in `f'/f` — and FTC-2
   evaluates the edge integral in closed form (`hIntegral_logDeriv_eq_log_sub`,
   `vIntegral_logDeriv_eq_log_sub`). `|ω| = 1` is *not* needed; `ω ≠ 0` is, and
   it follows from the `slitPlane` hypothesis rather than being assumed.
2. **Rotation mismatch is a constant.** At a subdivision point `p` where
   segments with rotations `ω_j`, `ω_{j+1}` meet, the defect
   `Complex.log (ω_j * f p) - Complex.log (ω_{j+1} * f p)` is `± Complex.log (-I)`,
   **independent of `f p`**. All four transitions actually used on this contour
   are multiplication by `-I` (or its inverse), so a single master lemma
   (`log_neg_I_mul_sub_log`) covers all eight subdivision points. This is the
   step that makes the winding integer combinatorial.
3. **Assembly.** Telescoping around the closed contour cancels every
   `Complex.log` term; what is left is `-8 * Complex.log (-I) = 4πI`, hence
   `RectangleIntegral' = 2`.

The eight (here twelve, see the honesty note) half-plane sign facts are taken as
explicit hypotheses. They are other lanes' work. §6 reduces the five left-edge
hypotheses to the five right-edge ones via r326's reflection, so the standing
input is: bottom edge, top edge, and three right-edge segments (R1/R2/R3) with
their conjugate mirrors — exactly the route document's §6 table.

## Honesty notes

* **Hypothesis count.** The route document says "the eight half-plane sign
  facts". The assembly below takes **twelve** (five right-edge segments, five
  left-edge segments, bottom, top), because the right edge needs five segments
  over `t ∈ [-15,15]` once the `t < 0` conjugate mirror is written out, not
  three. §6 then discharges the five left-edge ones from the five right-edge
  ones, leaving **seven** standing hypotheses in
  `rectangleIntegral'_logDeriv_eq_of_right_edge_chain`, of which the route
  document reports bottom (`r331d:87`) and top (`r331c:76`) as already proved.
  Three genuinely new numerical facts remain: R1, R2, R3 on `t ∈ [0,15]`,
  mirrored to `t ∈ [-15,0]`. Nothing here weakens any statement; the count
  simply is what it is.
* **Corners.** `zF`/`wF` below are defined locally, *identically* to
  `PrincipiaTractalis.FullRectangleBoundaryR331e.zF`/`.wF`
  (`⟨0,-15⟩` and `⟨1,15⟩`), so the two are `rfl`-interchangeable and this
  theorem composes with `xi_full_rectangle_zero_count_identity` without any
  bridging lemma. They are *not* imported, deliberately: r331e sits downstream
  of the panel rebuild, whereas r324/r325/r326/r327 oleans are current (the same
  reasoning `RiemannXiZeroCountLowerBound_r331f.lean` records in its header).
  When r331e's oleans are current, delete §2's `zF`/`wF` and import r331e
  instead.
* **What is NOT here.** No discharge of any sign hypothesis. No numerics. No
  claim that the integer is `2` unconditionally — that is exactly what the
  hypotheses buy. No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.

## mathlib dependencies, each verified to exist at the pin
### (`eed770a43495`, Lean v4.24.0-rc1)

| name | file:line |
|---|---|
| `HasDerivAt.clog_real` | `Mathlib/Analysis/SpecialFunctions/Complex/LogDeriv.lean:103` (root namespace: it is **after** `end Complex` at :72) |
| `intervalIntegral.integral_eq_sub_of_hasDerivAt` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1144` |
| `intervalIntegral.integral_add_adjacent_intervals` | `.../IntervalIntegral/Basic.lean:1011` |
| `intervalIntegral.integral_const_mul` | `.../IntervalIntegral/Basic.lean:764` (`@[simp]`) |
| `ContinuousOn.intervalIntegrable` | `.../IntervalIntegral/Basic.lean:446` |
| `IntervalIntegrable.trans` | `.../IntervalIntegral/Basic.lean:181` |
| `Complex.slitPlane` | `Mathlib/Analysis/Complex/Basic.lean:574` |
| `Complex.mem_slitPlane_iff` | `Mathlib/Analysis/Complex/Basic.lean:576` |
| `Complex.zero_notMem_slitPlane` | `Mathlib/Analysis/Complex/Basic.lean:603` |
| `Complex.log_mul_eq_add_log_iff` | `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:81` |
| `Complex.log_neg_I` | `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:102` |
| `Complex.two_pi_I_ne_zero` | `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:126` |
| `Complex.arg_neg_I` | `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:194` |
| `Complex.abs_arg_lt_pi_div_two_iff` | `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:379` |
| `Complex.mk_eq_add_mul_I` | `Mathlib/Data/Complex/Basic.lean:246` |
| `Complex.continuous_ofReal` | `Mathlib/Analysis/Complex/Basic.lean:252` |
| `Differentiable.analyticAt` | `Mathlib/Analysis/Complex/CauchyIntegral.lean:598` |
| `AnalyticAt.deriv` | `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:449` |
| `HasDerivAt.comp` (`x` **explicit**) | `Mathlib/Analysis/Calculus/Deriv/Comp.lean:247`. The `{x : 𝕜}` at :48 is **shadowed** by the `variable … (x)` ending the block at :67–68, whose own comment says "we put x explicit to help the elaborator". Confirmed by `HasDerivAt.clog`'s body (`…/Complex/LogDeriv.lean:101`) calling `.comp x h₁`. |
| `hasDerivAt_id'` (`x` **explicit**, `variable (s x L)` at :615) | `Mathlib/Analysis/Calculus/Deriv/Basic.lean:626` |
| `hasDerivAt_const` (explicit args are `(c, x)` — `variable (c : F) (s x L)` at :660) | `Mathlib/Analysis/Calculus/Deriv/Basic.lean:716` |
| `HasDerivAt.comp_ofReal` | `Mathlib/Analysis/Complex/RealDeriv.lean:95` |
| `HasDerivAt.comp_add_const` | `Mathlib/Analysis/Calculus/Deriv/Shift.lean:28` |
| `HasDerivAt.const_mul` | `Mathlib/Analysis/Calculus/Deriv/Mul.lean:366` |
| `HasDerivAt.mul_const` | `Mathlib/Analysis/Calculus/Deriv/Mul.lean:314` |
| `ContinuousOn.div₀` | `Mathlib/Topology/Algebra/GroupWithZero.lean:219` |
| `Set.left_mem_uIcc` | `Mathlib/Order/Interval/Set/UnorderedInterval.lean:91` |
| `logDeriv_apply` | `Mathlib/Analysis/Calculus/LogDeriv.lean:31` |

Searched for and **not found** at this pin (so not used): any `windingNumber`,
any residue/argument-principle API in `Mathlib/Analysis/`, any `Jensen` formula,
`ContinuousOn.div` in the λ-form (it exists only as `(f / g)`; `div₀` is the
λ-form), `IntervalIntegrable.const_mul` (avoided by building the `I *` factor
into the `ContinuousOn` step).

## Corpus dependencies

* `PF/Analytic/PNT/ResidueCalcOnRectangles_r327.lean:46,49,67,73` —
  `HIntegral`, `VIntegral`, `RectangleIntegral`, `RectangleIntegral'`, all in the
  **root** namespace (that file declares no namespace).
* `PF/Analytic/RiemannXiEntire_r325.lean:89` —
  `PrincipiaTractalis.RiemannXiEntire.differentiable_riemannXiEntire`.
* `PF/Analytic/RiemannXiSymmetries_r326.lean:109` —
  `PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_reflect_vertical`.

Namespace root `PrincipiaTractalis` follows the corpus convention
(`PrincipiaTractalis.FullRectangleBoundaryR331e`,
`PrincipiaTractalis.XiZeroCountLowerBound`, …).

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.PNT.ResidueCalcOnRectangles_r327
import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannXiSymmetries_r326

namespace PrincipiaTractalis
namespace RectangleLogBranchR331g

open Complex
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiSymmetries
open scoped ComplexConjugate

noncomputable section

/-! ## §0 — Pointwise helpers

Nothing in this section is specific to ξ; it is the arithmetic that the two
primitives and the mismatch lemmas need. -/

/-- The two spellings of a point on a horizontal/vertical line agree.
`HIntegral`/`VIntegral` use `↑x + ↑y * I`; the ξ API uses `⟨x, y⟩`. -/
lemma coe_add_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I) = (⟨x, y⟩ : ℂ) :=
  (Complex.mk_eq_add_mul_I x y).symm

/-- A positive real part puts a point in the slit plane. -/
lemma slit_of_re_pos {z : ℂ} (h : 0 < z.re) : z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl h)

/-- `0 < (ω * z).re` forces `z ≠ 0`. -/
lemma ne_zero_of_re_pos_mul {ω z : ℂ} (h : 0 < (ω * z).re) : z ≠ 0 := by
  intro hz
  rw [hz, mul_zero] at h
  simp at h

/-- `0 < (ω * z).re` forces `ω ≠ 0`. -/
lemma rot_ne_zero_of_re_pos_mul {ω z : ℂ} (h : 0 < (ω * z).re) : ω ≠ 0 := by
  intro hω
  rw [hω, zero_mul] at h
  simp at h

/-- Cancel a common nonzero left factor in a quotient. Proved by hand rather
than with `field_simp` so that the step is deterministic. -/
lemma div_cancel_left₀ {ω a b : ℂ} (hω : ω ≠ 0) : (ω * a) / (ω * b) = a / b := by
  rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
  calc ω * a * (ω⁻¹ * b⁻¹) = ω * ω⁻¹ * (a * b⁻¹) := by ring
    _ = a * b⁻¹ := by rw [mul_inv_cancel₀ hω, one_mul]

/-- The `VIntegral` shape of `div_cancel_left₀`: the path derivative `I` floats
out past the cancellation. -/
lemma div_cancel_left_mul_I₀ {ω a b : ℂ} (hω : ω ≠ 0) :
    (ω * (a * I)) / (ω * b) = I * (a / b) := by
  rw [div_cancel_left₀ hω, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-! ### The four rotation products

`ring` does not know `I * I = -1`, so the four products that drive the mismatch
lemmas are recorded explicitly. -/

lemma neg_I_mul_neg_I : (-I : ℂ) * (-I) = -1 := by
  rw [neg_mul_neg, Complex.I_mul_I]

lemma neg_I_mul_I : (-I : ℂ) * I = 1 := by
  rw [neg_mul, Complex.I_mul_I, neg_neg]

/-! ## §1 — Derivatives along the two edge directions

These are the only compositions in the file. `HasDerivAt.comp_ofReal`
(`Mathlib/Analysis/Complex/RealDeriv.lean:95`) restricts a `ℂ`-derivative to an
`ℝ`-parameter, which is exactly the `HIntegral`/`VIntegral` shape. -/

/-- `deriv f` is continuous when `f` is entire. -/
lemma continuous_deriv_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Continuous (deriv f) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact ((hf.analyticAt z).deriv).continuousAt

/-- Derivative along the horizontal line `Im = y`. The path derivative is `1`. -/
lemma hasDerivAt_horizontal {f : ℂ → ℂ} (hf : Differentiable ℂ f) (y t : ℝ) :
    HasDerivAt (fun s : ℝ => f ((s : ℂ) + (y : ℂ) * I))
      (deriv f ((t : ℂ) + (y : ℂ) * I)) t := by
  have hC : HasDerivAt (fun u : ℂ => f (u + (y : ℂ) * I))
      (deriv f ((t : ℂ) + (y : ℂ) * I)) ((t : ℂ)) :=
    HasDerivAt.comp_add_const ((t : ℂ)) ((y : ℂ) * I) (hf _).hasDerivAt
  exact hC.comp_ofReal

/-- Derivative along the vertical line `Re = x`. The path derivative is `I`. -/
lemma hasDerivAt_vertical {f : ℂ → ℂ} (hf : Differentiable ℂ f) (x t : ℝ) :
    HasDerivAt (fun s : ℝ => f ((x : ℂ) + (s : ℂ) * I))
      (deriv f ((x : ℂ) + (t : ℂ) * I) * I) t := by
  -- `simp` strips the additive constant from the goal on its own (a constant does not
  -- change the derivative), leaving exactly `HasDerivAt (fun u => u * I) I t`. So the
  -- `hasDerivAt_const`-plus-`add` wrapper is not only unnecessary, it reintroduces the
  -- constant and causes a mismatch against the simplified goal.
  have hin : HasDerivAt (fun u : ℂ => (x : ℂ) + u * I) I ((t : ℂ)) := by
    simpa using (hasDerivAt_id' ((t : ℂ))).mul_const I
  have hout : HasDerivAt f (deriv f ((x : ℂ) + (t : ℂ) * I)) ((x : ℂ) + (t : ℂ) * I) :=
    (hf _).hasDerivAt
  have hC : HasDerivAt (fun u : ℂ => f ((x : ℂ) + u * I))
      (deriv f ((x : ℂ) + (t : ℂ) * I) * I) ((t : ℂ)) := by
    simpa [Function.comp_def] using hout.comp ((t : ℂ)) hin
  exact hC.comp_ofReal

/-! ### Continuity and integrability of `logDeriv f` along an edge -/

/-- `logDeriv f` is continuous along a horizontal segment on which `f ≠ 0`. -/
lemma continuousOn_logDeriv_hline {f : ℂ → ℂ} (hf : Differentiable ℂ f) {y a b : ℝ}
    (hne : ∀ s ∈ Set.uIcc a b, f ((s : ℂ) + (y : ℂ) * I) ≠ 0) :
    ContinuousOn (fun s : ℝ => logDeriv f ((s : ℂ) + (y : ℂ) * I)) (Set.uIcc a b) := by
  have hpath : Continuous (fun s : ℝ => ((s : ℂ) + (y : ℂ) * I)) :=
    Complex.continuous_ofReal.add continuous_const
  have hnum : Continuous (fun s : ℝ => deriv f ((s : ℂ) + (y : ℂ) * I)) :=
    (continuous_deriv_of_differentiable hf).comp hpath
  have hden : Continuous (fun s : ℝ => f ((s : ℂ) + (y : ℂ) * I)) := hf.continuous.comp hpath
  simp only [logDeriv_apply]
  exact hnum.continuousOn.div₀ hden.continuousOn hne

/-- `logDeriv f` is continuous along a vertical segment on which `f ≠ 0`. -/
lemma continuousOn_logDeriv_vline {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x a b : ℝ}
    (hne : ∀ s ∈ Set.uIcc a b, f ((x : ℂ) + (s : ℂ) * I) ≠ 0) :
    ContinuousOn (fun s : ℝ => logDeriv f ((x : ℂ) + (s : ℂ) * I)) (Set.uIcc a b) := by
  have hpath : Continuous (fun s : ℝ => ((x : ℂ) + (s : ℂ) * I)) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hnum : Continuous (fun s : ℝ => deriv f ((x : ℂ) + (s : ℂ) * I)) :=
    (continuous_deriv_of_differentiable hf).comp hpath
  have hden : Continuous (fun s : ℝ => f ((x : ℂ) + (s : ℂ) * I)) := hf.continuous.comp hpath
  simp only [logDeriv_apply]
  exact hnum.continuousOn.div₀ hden.continuousOn hne

lemma intervalIntegrable_logDeriv_hline {f : ℂ → ℂ} (hf : Differentiable ℂ f) {y a b : ℝ}
    (hne : ∀ s ∈ Set.uIcc a b, f ((s : ℂ) + (y : ℂ) * I) ≠ 0) :
    IntervalIntegrable (fun s : ℝ => logDeriv f ((s : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume a b :=
  (continuousOn_logDeriv_hline hf hne).intervalIntegrable

lemma intervalIntegrable_logDeriv_vline {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x a b : ℝ}
    (hne : ∀ s ∈ Set.uIcc a b, f ((x : ℂ) + (s : ℂ) * I) ≠ 0) :
    IntervalIntegrable (fun s : ℝ => logDeriv f ((x : ℂ) + (s : ℂ) * I))
      MeasureTheory.volume a b :=
  (continuousOn_logDeriv_vline hf hne).intervalIntegrable

/-- The `I *` variant, built at the `ContinuousOn` level so that no
`IntervalIntegrable.const_mul` is needed (that name is not at this pin). -/
lemma intervalIntegrable_I_mul_logDeriv_vline {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {x a b : ℝ} (hne : ∀ s ∈ Set.uIcc a b, f ((x : ℂ) + (s : ℂ) * I) ≠ 0) :
    IntervalIntegrable (fun s : ℝ => I * logDeriv f ((x : ℂ) + (s : ℂ) * I))
      MeasureTheory.volume a b :=
  (continuousOn_const.mul (continuousOn_logDeriv_vline hf hne)).intervalIntegrable

/-! ## §2 — The two edge primitives

For `ω ≠ 0`, `s ↦ Complex.log (ω * f s)` is a primitive of `logDeriv f` on any
segment along which `ω * f` stays in the slit plane: the `ω` cancels in `f'/f`.
`|ω| = 1` is not used anywhere; `ω ≠ 0` is derived from `hmem`, since
`0 ∉ slitPlane`. -/

/-- **Horizontal edge in closed form.** -/
theorem hIntegral_logDeriv_eq_log_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {x₁ x₂ y : ℝ} (ω : ℂ)
    (hmem : ∀ x ∈ Set.uIcc x₁ x₂, ω * f (⟨x, y⟩ : ℂ) ∈ Complex.slitPlane) :
    HIntegral (fun s => logDeriv f s) x₁ x₂ y
      = Complex.log (ω * f (⟨x₂, y⟩ : ℂ)) - Complex.log (ω * f (⟨x₁, y⟩ : ℂ)) := by
  -- restate the hypothesis in the `↑x + ↑y * I` spelling the integral uses
  have hmem' : ∀ x ∈ Set.uIcc x₁ x₂, ω * f ((x : ℂ) + (y : ℂ) * I) ∈ Complex.slitPlane := by
    intro x hx
    rw [coe_add_mul_I]
    exact hmem x hx
  have hne : ∀ x ∈ Set.uIcc x₁ x₂, f ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro x hx hzero
    have hmm := hmem' x hx
    rw [hzero, mul_zero] at hmm
    exact Complex.zero_notMem_slitPlane hmm
  have hω : ω ≠ 0 := by
    intro h
    have hmm := hmem' x₁ Set.left_mem_uIcc
    rw [h, zero_mul] at hmm
    exact Complex.zero_notMem_slitPlane hmm
  -- the primitive
  have hderiv : ∀ x ∈ Set.uIcc x₁ x₂,
      HasDerivAt (fun s : ℝ => Complex.log (ω * f ((s : ℂ) + (y : ℂ) * I)))
        (logDeriv f ((x : ℂ) + (y : ℂ) * I)) x := by
    intro x hx
    have hlog := ((hasDerivAt_horizontal hf y x).const_mul ω).clog_real (hmem' x hx)
    have hval : (ω * deriv f ((x : ℂ) + (y : ℂ) * I)) / (ω * f ((x : ℂ) + (y : ℂ) * I))
        = logDeriv f ((x : ℂ) + (y : ℂ) * I) := by
      rw [logDeriv_apply]
      exact div_cancel_left₀ hω
    rw [← hval]
    exact hlog
  have hint := intervalIntegrable_logDeriv_hline hf hne
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- `:=` rather than `rw`: `HIntegral` unfolds by delta and the integrand matches by beta/eta,
  -- which `isDefEq` handles and keyed rewriting might not.
  have hval : HIntegral (fun s => logDeriv f s) x₁ x₂ y
      = Complex.log (ω * f ((x₂ : ℂ) + (y : ℂ) * I))
        - Complex.log (ω * f ((x₁ : ℂ) + (y : ℂ) * I)) := hFTC
  rw [hval]
  simp only [coe_add_mul_I]

/-- **Vertical edge in closed form.** `VIntegral` carries `I •` and the path
`y ↦ ⟨x, y⟩` has derivative `I`, so the two `I`s absorb. -/
theorem vIntegral_logDeriv_eq_log_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {x y₁ y₂ : ℝ} (ω : ℂ)
    (hmem : ∀ y ∈ Set.uIcc y₁ y₂, ω * f (⟨x, y⟩ : ℂ) ∈ Complex.slitPlane) :
    VIntegral (fun s => logDeriv f s) x y₁ y₂
      = Complex.log (ω * f (⟨x, y₂⟩ : ℂ)) - Complex.log (ω * f (⟨x, y₁⟩ : ℂ)) := by
  have hmem' : ∀ y ∈ Set.uIcc y₁ y₂, ω * f ((x : ℂ) + (y : ℂ) * I) ∈ Complex.slitPlane := by
    intro y hy
    rw [coe_add_mul_I]
    exact hmem y hy
  have hne : ∀ y ∈ Set.uIcc y₁ y₂, f ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy hzero
    have hmm := hmem' y hy
    rw [hzero, mul_zero] at hmm
    exact Complex.zero_notMem_slitPlane hmm
  have hω : ω ≠ 0 := by
    intro h
    have hmm := hmem' y₁ Set.left_mem_uIcc
    rw [h, zero_mul] at hmm
    exact Complex.zero_notMem_slitPlane hmm
  have hderiv : ∀ y ∈ Set.uIcc y₁ y₂,
      HasDerivAt (fun s : ℝ => Complex.log (ω * f ((x : ℂ) + (s : ℂ) * I)))
        (I * logDeriv f ((x : ℂ) + (y : ℂ) * I)) y := by
    intro y hy
    have hlog := ((hasDerivAt_vertical hf x y).const_mul ω).clog_real (hmem' y hy)
    have hval : (ω * (deriv f ((x : ℂ) + (y : ℂ) * I) * I)) / (ω * f ((x : ℂ) + (y : ℂ) * I))
        = I * logDeriv f ((x : ℂ) + (y : ℂ) * I) := by
      rw [logDeriv_apply]
      exact div_cancel_left_mul_I₀ hω
    rw [← hval]
    exact hlog
  have hint := intervalIntegrable_I_mul_logDeriv_vline hf hne
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- pull the path derivative `I` out of the integral so it can meet `VIntegral`'s `I •`
  rw [intervalIntegral.integral_const_mul] at hFTC
  -- `VIntegral` unfolds by delta and `ℂ`-on-`ℂ` `•` is `*`, both by `isDefEq`
  have hval : VIntegral (fun s => logDeriv f s) x y₁ y₂
      = Complex.log (ω * f ((x : ℂ) + (y₂ : ℂ) * I))
        - Complex.log (ω * f ((x : ℂ) + (y₁ : ℂ) * I)) := hFTC
  rw [hval]
  simp only [coe_add_mul_I]

/-! ## §3 — Rotation mismatch is a constant

This is the step that removes all numerics from the integral. At a subdivision
point `p`, both `ω_j * f p` and `ω_{j+1} * f p` have positive real part, and
every transition on this contour is multiplication by `-I` in one direction or
the other. Then

  `Complex.log (-I * w) - Complex.log w = Complex.log (-I)`

with no dependence on `w` beyond `0 < w.re`. **No numerical value of `arg` is
ever required**; `Complex.log (-I)` is carried symbolically all the way to the
last line of §5, where `Complex.log_neg_I` evaluates it once.

`Complex.log_mul` has a side condition (`Complex.log_mul_eq_add_log_iff` asks
`arg x + arg y ∈ Set.Ioc (-π) π`). Here `arg (-I) = -π/2` and `0 < w.re` gives
`|arg w| < π/2` (`Complex.abs_arg_lt_pi_div_two_iff`), so the sum lies in
`(-π, 0) ⊆ Ioc (-π) π` and the side condition is discharged *from the sign fact
alone* — no `Complex.arg` arithmetic beyond that bound is needed. -/

/-- **★ The master mismatch lemma ★** — only `0 < w.re` is required. -/
theorem log_neg_I_mul_sub_log {w : ℂ} (hw : 0 < w.re) :
    Complex.log (-I * w) - Complex.log w = Complex.log (-I) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hI0 : (-I : ℂ) ≠ 0 := by simp
  have habs : |Complex.arg w| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  rw [abs_lt] at habs
  have harg : Complex.arg (-I) + Complex.arg w ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_neg_I]
    refine Set.mem_Ioc.mpr ⟨?_, ?_⟩
    · linarith [habs.1]
    · linarith [habs.2, Real.pi_pos]
  rw [(Complex.log_mul_eq_add_log_iff hI0 hw0).mpr harg]
  ring

/-! ### The four rotations actually used, `ω ∈ {1, -I, -1, I}`

The transitions that occur on this contour are, in traversal order on the right
edge, `-1 → I → 1 → -I → -1`, and on the left edge `-1 → -I → 1 → I → -1`. Each
is a multiplication by `-I` or by `I`; the four lemmas below are the `-I`
direction, and the `I` direction is their negation (used that way in §5).

In each case the hypothesis is the *single* sign fact that the earlier segment
already supplies at its endpoint — the full quadrant information is available
there (e.g. `ξ(1+13i)` is in Q1) but is not needed. -/

/-- `ω : 1 → -I`. At the node, `0 < (1 * z).re` (Q1 or Q4 of `z`). -/
theorem log_rot_one_to_negI {z : ℂ} (hz : 0 < ((1 : ℂ) * z).re) :
    Complex.log ((-I) * z) - Complex.log ((1 : ℂ) * z) = Complex.log (-I) := by
  have hrw : (-I : ℂ) * z = -I * ((1 : ℂ) * z) := by ring
  rw [hrw]
  exact log_neg_I_mul_sub_log hz

/-- `ω : -I → -1`. At the node, `0 < (-I * z).re`, i.e. `0 < z.im`. -/
theorem log_rot_negI_to_negOne {z : ℂ} (hz : 0 < ((-I) * z).re) :
    Complex.log ((-1 : ℂ) * z) - Complex.log ((-I) * z) = Complex.log (-I) := by
  have hrw : (-1 : ℂ) * z = -I * ((-I) * z) := by
    rw [← mul_assoc, neg_I_mul_neg_I]
  rw [hrw]
  exact log_neg_I_mul_sub_log hz

/-- `ω : -1 → I`. At the node, `0 < (-1 * z).re`, i.e. `z.re < 0`. -/
theorem log_rot_negOne_to_I {z : ℂ} (hz : 0 < ((-1 : ℂ) * z).re) :
    Complex.log (I * z) - Complex.log ((-1 : ℂ) * z) = Complex.log (-I) := by
  have hrw : (I : ℂ) * z = -I * ((-1 : ℂ) * z) := by ring
  rw [hrw]
  exact log_neg_I_mul_sub_log hz

/-- `ω : I → 1`. At the node, `0 < (I * z).re`, i.e. `z.im < 0`. -/
theorem log_rot_I_to_one {z : ℂ} (hz : 0 < (I * z).re) :
    Complex.log ((1 : ℂ) * z) - Complex.log (I * z) = Complex.log (-I) := by
  have hrw : (1 : ℂ) * z = -I * (I * z) := by
    rw [← mul_assoc, neg_I_mul_I]
  rw [hrw]
  exact log_neg_I_mul_sub_log hz

/-! ## §4 — Chaining five segments along a vertical edge

`VIntegral` is additive in the parameter interval; summing the five closed-form
segment values telescopes, leaving the two endpoint logs plus one *defect* per
interior node. Each defect is `± Complex.log (-I)` by §3. -/

lemma ne_zero_line {f : ℂ → ℂ} {ω : ℂ} {x u v : ℝ}
    (h : ∀ y ∈ Set.uIcc u v, 0 < (ω * f (⟨x, y⟩ : ℂ)).re) :
    ∀ y ∈ Set.uIcc u v, f ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  intro y hy
  rw [coe_add_mul_I]
  exact ne_zero_of_re_pos_mul (h y hy)

lemma vIntegral_add_adjacent {g : ℂ → ℂ} {x a b c : ℝ}
    (hab : IntervalIntegrable (fun s : ℝ => g ((x : ℂ) + (s : ℂ) * I)) MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (fun s : ℝ => g ((x : ℂ) + (s : ℂ) * I)) MeasureTheory.volume b c) :
    VIntegral g x a b + VIntegral g x b c = VIntegral g x a c := by
  simp only [VIntegral, ← smul_add]
  rw [intervalIntegral.integral_add_adjacent_intervals hab hbc]

/-- **Five-segment chain along a vertical edge.** The right-hand side is the
telescoped form: endpoint difference, plus one node defect per interior
subdivision point. Nothing about the rotations is assumed beyond the five
half-plane facts, so this lemma serves both the right and the left edge. -/
theorem vIntegral_logDeriv_chain5 {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℝ}
    {a₀ a₁ a₂ a₃ a₄ a₅ : ℝ} (ω₁ ω₂ ω₃ ω₄ ω₅ : ℂ)
    (h₁ : ∀ y ∈ Set.uIcc a₀ a₁, 0 < (ω₁ * f (⟨x, y⟩ : ℂ)).re)
    (h₂ : ∀ y ∈ Set.uIcc a₁ a₂, 0 < (ω₂ * f (⟨x, y⟩ : ℂ)).re)
    (h₃ : ∀ y ∈ Set.uIcc a₂ a₃, 0 < (ω₃ * f (⟨x, y⟩ : ℂ)).re)
    (h₄ : ∀ y ∈ Set.uIcc a₃ a₄, 0 < (ω₄ * f (⟨x, y⟩ : ℂ)).re)
    (h₅ : ∀ y ∈ Set.uIcc a₄ a₅, 0 < (ω₅ * f (⟨x, y⟩ : ℂ)).re) :
    VIntegral (fun s => logDeriv f s) x a₀ a₅
      = (Complex.log (ω₅ * f (⟨x, a₅⟩ : ℂ)) - Complex.log (ω₁ * f (⟨x, a₀⟩ : ℂ)))
        + (Complex.log (ω₁ * f (⟨x, a₁⟩ : ℂ)) - Complex.log (ω₂ * f (⟨x, a₁⟩ : ℂ)))
        + (Complex.log (ω₂ * f (⟨x, a₂⟩ : ℂ)) - Complex.log (ω₃ * f (⟨x, a₂⟩ : ℂ)))
        + (Complex.log (ω₃ * f (⟨x, a₃⟩ : ℂ)) - Complex.log (ω₄ * f (⟨x, a₃⟩ : ℂ)))
        + (Complex.log (ω₄ * f (⟨x, a₄⟩ : ℂ)) - Complex.log (ω₅ * f (⟨x, a₄⟩ : ℂ))) := by
  -- the five segment values
  have e₁ := vIntegral_logDeriv_eq_log_sub (x := x) (y₁ := a₀) (y₂ := a₁) hf ω₁
    (fun y hy => slit_of_re_pos (h₁ y hy))
  have e₂ := vIntegral_logDeriv_eq_log_sub (x := x) (y₁ := a₁) (y₂ := a₂) hf ω₂
    (fun y hy => slit_of_re_pos (h₂ y hy))
  have e₃ := vIntegral_logDeriv_eq_log_sub (x := x) (y₁ := a₂) (y₂ := a₃) hf ω₃
    (fun y hy => slit_of_re_pos (h₃ y hy))
  have e₄ := vIntegral_logDeriv_eq_log_sub (x := x) (y₁ := a₃) (y₂ := a₄) hf ω₄
    (fun y hy => slit_of_re_pos (h₄ y hy))
  have e₅ := vIntegral_logDeriv_eq_log_sub (x := x) (y₁ := a₄) (y₂ := a₅) hf ω₅
    (fun y hy => slit_of_re_pos (h₅ y hy))
  -- the five integrabilities
  have i₁ := intervalIntegrable_logDeriv_vline (a := a₀) (b := a₁) hf (ne_zero_line h₁)
  have i₂ := intervalIntegrable_logDeriv_vline (a := a₁) (b := a₂) hf (ne_zero_line h₂)
  have i₃ := intervalIntegrable_logDeriv_vline (a := a₂) (b := a₃) hf (ne_zero_line h₃)
  have i₄ := intervalIntegrable_logDeriv_vline (a := a₃) (b := a₄) hf (ne_zero_line h₄)
  have i₅ := intervalIntegrable_logDeriv_vline (a := a₄) (b := a₅) hf (ne_zero_line h₅)
  -- glue the parameter intervals
  have hadd₁ : VIntegral (fun s => logDeriv f s) x a₀ a₁
      + VIntegral (fun s => logDeriv f s) x a₁ a₂
      = VIntegral (fun s => logDeriv f s) x a₀ a₂ := vIntegral_add_adjacent i₁ i₂
  have hadd₂ : VIntegral (fun s => logDeriv f s) x a₀ a₂
      + VIntegral (fun s => logDeriv f s) x a₂ a₃
      = VIntegral (fun s => logDeriv f s) x a₀ a₃ :=
    vIntegral_add_adjacent (i₁.trans i₂) i₃
  have hadd₃ : VIntegral (fun s => logDeriv f s) x a₀ a₃
      + VIntegral (fun s => logDeriv f s) x a₃ a₄
      = VIntegral (fun s => logDeriv f s) x a₀ a₄ :=
    vIntegral_add_adjacent ((i₁.trans i₂).trans i₃) i₄
  have hadd₄ : VIntegral (fun s => logDeriv f s) x a₀ a₄
      + VIntegral (fun s => logDeriv f s) x a₄ a₅
      = VIntegral (fun s => logDeriv f s) x a₀ a₅ :=
    vIntegral_add_adjacent (((i₁.trans i₂).trans i₃).trans i₄) i₅
  rw [← hadd₄, ← hadd₃, ← hadd₂, ← hadd₁, e₁, e₂, e₃, e₄, e₅]
  ring

/-! ## §5 — Assembly on the full rectangle `[0,1] × [-15,15]` -/

/-- SW corner. Definitionally equal to
`PrincipiaTractalis.FullRectangleBoundaryR331e.zF`. -/
def zF : ℂ := ⟨0, -15⟩

/-- NE corner. Definitionally equal to
`PrincipiaTractalis.FullRectangleBoundaryR331e.wF`. -/
def wF : ℂ := ⟨1, 15⟩

lemma zF_re : zF.re = 0 := rfl
lemma zF_im : zF.im = -15 := rfl
lemma wF_re : wF.re = 1 := rfl
lemma wF_im : wF.im = 15 := rfl

/-- **★★★ The bridge ★★★** — the contour value is exactly `2`, given the twelve
segment sign facts.

The rotation chain is, in traversal order:

```
bottom  t = -15, σ : 0 → 1            ω = -1
right   σ =  1,  t : -15 → 15         ω = -1, I, 1, -I, -1
top     t =  15, σ : 1 → 0            ω = -1
left    σ =  0,  t : 15 → -15         ω = -1, -I, 1, I, -1
```

so all four corners are rotation-matched (no defect) and the eight interior
subdivision points each contribute `± Complex.log (-I)`: four with one sign on
the right edge, four with the other on the left edge. Every `Complex.log` of a
ξ-value cancels; `-8 * Complex.log (-I) = 4πI` survives, and the `1/(2πi)` in
`RectangleIntegral'` turns it into `2`.

Composes with `xi_full_rectangle_zero_count_identity`
(`RiemannXiFullRectangleBoundary_r331e.lean:171`) to give
`∑ ρ ∈ Z, (analyticOrderNatAt riemannXiEntire ρ : ℂ) = 2`, hence
`XiRectangleCountAtMostTwo` and `NoOffLineZeroInRightHalf`
(`RiemannXiZeroCountLowerBound_r331f.lean:175,301`). -/
theorem rectangleIntegral'_logDeriv_eq_of_branch_chain
    (hBot : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, 0 < ((-1 : ℂ) * riemannXiEntire (⟨σ, -15⟩ : ℂ)).re)
    (hTop : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, 0 < ((-1 : ℂ) * riemannXiEntire (⟨σ, 15⟩ : ℂ)).re)
    (hR1 : ∀ t ∈ Set.uIcc (-15 : ℝ) (-29/2),
      0 < ((-1 : ℂ) * riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR2 : ∀ t ∈ Set.uIcc (-29/2 : ℝ) (-13),
      0 < (I * riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR3 : ∀ t ∈ Set.uIcc (-13 : ℝ) 13,
      0 < ((1 : ℂ) * riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR4 : ∀ t ∈ Set.uIcc (13 : ℝ) (29/2),
      0 < ((-I) * riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR5 : ∀ t ∈ Set.uIcc (29/2 : ℝ) 15,
      0 < ((-1 : ℂ) * riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hL1 : ∀ t ∈ Set.uIcc (-15 : ℝ) (-29/2),
      0 < ((-1 : ℂ) * riemannXiEntire (⟨0, t⟩ : ℂ)).re)
    (hL2 : ∀ t ∈ Set.uIcc (-29/2 : ℝ) (-13),
      0 < ((-I) * riemannXiEntire (⟨0, t⟩ : ℂ)).re)
    (hL3 : ∀ t ∈ Set.uIcc (-13 : ℝ) 13,
      0 < ((1 : ℂ) * riemannXiEntire (⟨0, t⟩ : ℂ)).re)
    (hL4 : ∀ t ∈ Set.uIcc (13 : ℝ) (29/2),
      0 < (I * riemannXiEntire (⟨0, t⟩ : ℂ)).re)
    (hL5 : ∀ t ∈ Set.uIcc (29/2 : ℝ) 15,
      0 < ((-1 : ℂ) * riemannXiEntire (⟨0, t⟩ : ℂ)).re) :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF = (2 : ℂ) := by
  have hd : Differentiable ℂ riemannXiEntire := differentiable_riemannXiEntire
  -- ## the two horizontal edges, rotation `-1`
  have hb := hIntegral_logDeriv_eq_log_sub (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ)) (y := (-15 : ℝ))
    hd (-1 : ℂ) (fun σ hσ => slit_of_re_pos (hBot σ hσ))
  have ht := hIntegral_logDeriv_eq_log_sub (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ)) (y := (15 : ℝ))
    hd (-1 : ℂ) (fun σ hσ => slit_of_re_pos (hTop σ hσ))
  -- ## the two vertical edges, five segments each
  have hVr := vIntegral_logDeriv_chain5 (x := (1 : ℝ)) (a₀ := (-15 : ℝ)) (a₁ := (-29/2 : ℝ))
    (a₂ := (-13 : ℝ)) (a₃ := (13 : ℝ)) (a₄ := (29/2 : ℝ)) (a₅ := (15 : ℝ))
    hd (-1 : ℂ) I (1 : ℂ) (-I) (-1 : ℂ) hR1 hR2 hR3 hR4 hR5
  have hVl := vIntegral_logDeriv_chain5 (x := (0 : ℝ)) (a₀ := (-15 : ℝ)) (a₁ := (-29/2 : ℝ))
    (a₂ := (-13 : ℝ)) (a₃ := (13 : ℝ)) (a₄ := (29/2 : ℝ)) (a₅ := (15 : ℝ))
    hd (-1 : ℂ) (-I) (1 : ℂ) I (-1 : ℂ) hL1 hL2 hL3 hL4 hL5
  -- ## the four right-edge node defects: `-1 → I → 1 → -I → -1`, each `-log(-I)`
  have nR1 : Complex.log ((-1 : ℂ) * riemannXiEntire (⟨1, -29/2⟩ : ℂ))
      - Complex.log (I * riemannXiEntire (⟨1, -29/2⟩ : ℂ)) = -Complex.log (-I) := by
    have h := log_rot_negOne_to_I (z := riemannXiEntire (⟨1, -29/2⟩ : ℂ))
      (hR1 (-29/2) Set.right_mem_uIcc)
    rw [← h]; ring
  have nR2 : Complex.log (I * riemannXiEntire (⟨1, -13⟩ : ℂ))
      - Complex.log ((1 : ℂ) * riemannXiEntire (⟨1, -13⟩ : ℂ)) = -Complex.log (-I) := by
    have h := log_rot_I_to_one (z := riemannXiEntire (⟨1, -13⟩ : ℂ))
      (hR2 (-13) Set.right_mem_uIcc)
    rw [← h]; ring
  have nR3 : Complex.log ((1 : ℂ) * riemannXiEntire (⟨1, 13⟩ : ℂ))
      - Complex.log ((-I) * riemannXiEntire (⟨1, 13⟩ : ℂ)) = -Complex.log (-I) := by
    have h := log_rot_one_to_negI (z := riemannXiEntire (⟨1, 13⟩ : ℂ))
      (hR3 13 Set.right_mem_uIcc)
    rw [← h]; ring
  have nR4 : Complex.log ((-I) * riemannXiEntire (⟨1, 29/2⟩ : ℂ))
      - Complex.log ((-1 : ℂ) * riemannXiEntire (⟨1, 29/2⟩ : ℂ)) = -Complex.log (-I) := by
    have h := log_rot_negI_to_negOne (z := riemannXiEntire (⟨1, 29/2⟩ : ℂ))
      (hR4 (29/2) Set.right_mem_uIcc)
    rw [← h]; ring
  -- ## the four left-edge node defects: `-1 → -I → 1 → I → -1`, each `+log(-I)`
  have nL1 : Complex.log ((-1 : ℂ) * riemannXiEntire (⟨0, -29/2⟩ : ℂ))
      - Complex.log ((-I) * riemannXiEntire (⟨0, -29/2⟩ : ℂ)) = Complex.log (-I) :=
    log_rot_negI_to_negOne (z := riemannXiEntire (⟨0, -29/2⟩ : ℂ))
      (hL2 (-29/2) Set.left_mem_uIcc)
  have nL2 : Complex.log ((-I) * riemannXiEntire (⟨0, -13⟩ : ℂ))
      - Complex.log ((1 : ℂ) * riemannXiEntire (⟨0, -13⟩ : ℂ)) = Complex.log (-I) :=
    log_rot_one_to_negI (z := riemannXiEntire (⟨0, -13⟩ : ℂ))
      (hL3 (-13) Set.left_mem_uIcc)
  have nL3 : Complex.log ((1 : ℂ) * riemannXiEntire (⟨0, 13⟩ : ℂ))
      - Complex.log (I * riemannXiEntire (⟨0, 13⟩ : ℂ)) = Complex.log (-I) :=
    log_rot_I_to_one (z := riemannXiEntire (⟨0, 13⟩ : ℂ))
      (hL4 13 Set.left_mem_uIcc)
  have nL4 : Complex.log (I * riemannXiEntire (⟨0, 29/2⟩ : ℂ))
      - Complex.log ((-1 : ℂ) * riemannXiEntire (⟨0, 29/2⟩ : ℂ)) = Complex.log (-I) :=
    log_rot_negOne_to_I (z := riemannXiEntire (⟨0, 29/2⟩ : ℂ))
      (hL5 (29/2) Set.left_mem_uIcc)
  -- ## telescoping: every ξ-log cancels, `-8 * log (-I)` survives
  -- `show` (not `simp only [RectangleIntegral]`) so that the function argument is never
  -- eta-contracted out from under the `rw`s below.
  have hR : RectangleIntegral (fun s => logDeriv riemannXiEntire s) zF wF
      = -(8 : ℂ) * Complex.log (-I) := by
    show HIntegral (fun s => logDeriv riemannXiEntire s) zF.re wF.re zF.im
          - HIntegral (fun s => logDeriv riemannXiEntire s) zF.re wF.re wF.im
          + VIntegral (fun s => logDeriv riemannXiEntire s) wF.re zF.im wF.im
          - VIntegral (fun s => logDeriv riemannXiEntire s) zF.re zF.im wF.im
        = -(8 : ℂ) * Complex.log (-I)
    rw [zF_re, zF_im, wF_re, wF_im]
    rw [hb, ht, hVr, hVl, nR1, nR2, nR3, nR4, nL1, nL2, nL3, nL4]
    ring
  -- ## the scalar: `(1/(2πi)) * (-8 * log (-I)) = 2`
  have hden : (2 * (Real.pi : ℂ) * I) ≠ 0 := Complex.two_pi_I_ne_zero
  have hfinal : (1 / (2 * (Real.pi : ℂ) * I)) * (-(8 : ℂ) * Complex.log (-I)) = 2 := by
    rw [Complex.log_neg_I, div_mul_eq_mul_div, one_mul, div_eq_iff hden]
    ring
  -- `RectangleIntegral'` is an abbrev and `ℂ`-on-`ℂ` `•` is `*`, so `show` does both unfoldings.
  show (1 / (2 * (Real.pi : ℂ) * I))
      * RectangleIntegral (fun s => logDeriv riemannXiEntire s) zF wF = (2 : ℂ)
  rw [hR]
  exact hfinal

/-! ## §6 — The left edge is free

`riemannXiEntire_reflect_vertical` (r326:109) gives
`ξ⟨1-σ, t⟩ = conj (ξ⟨σ, t⟩)`, so at `σ = 0` we get `ξ⟨0,t⟩ = conj (ξ⟨1,t⟩)`.
Conjugation fixes `Re`, flips `Im`, and therefore swaps the roles of the
rotations `I` and `-I` while fixing `1` and `-1`. That is exactly the
right-edge/left-edge rotation chain difference in §5, so the five left-edge
hypotheses are *consequences* of the five right-edge ones. Half the contour is
free, as the route document's §6 says. -/

lemma xi_left_eq_conj_right (t : ℝ) :
    riemannXiEntire (⟨0, t⟩ : ℂ) = conj (riemannXiEntire (⟨1, t⟩ : ℂ)) := by
  have h := riemannXiEntire_reflect_vertical 1 t
  simp only [sub_self] at h
  exact h

lemma re_neg_one_mul_conj (z : ℂ) : ((-1 : ℂ) * conj z).re = ((-1 : ℂ) * z).re := by
  simp

lemma re_one_mul_conj (z : ℂ) : ((1 : ℂ) * conj z).re = ((1 : ℂ) * z).re := by
  simp

lemma re_neg_I_mul_conj (z : ℂ) : ((-I) * conj z).re = (I * z).re := by
  simp

lemma re_I_mul_conj (z : ℂ) : (I * conj z).re = ((-I) * z).re := by
  simp

/-- **★ The bridge with the left edge discharged ★** — seven standing
hypotheses: bottom, top, and the five right-edge segments (of which the two
`t < 0` ones are themselves the conjugate mirrors of R2/R3 and the `t ∈
[-15,-29/2]` one the mirror of R1, per the route document's §6). -/
theorem rectangleIntegral'_logDeriv_eq_of_right_edge_chain
    (hBot : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, 0 < ((-1 : ℂ) * riemannXiEntire (⟨σ, -15⟩ : ℂ)).re)
    (hTop : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, 0 < ((-1 : ℂ) * riemannXiEntire (⟨σ, 15⟩ : ℂ)).re)
    (hR1 : ∀ t ∈ Set.uIcc (-15 : ℝ) (-29/2),
      0 < ((-1 : ℂ) * riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR2 : ∀ t ∈ Set.uIcc (-29/2 : ℝ) (-13),
      0 < (I * riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR3 : ∀ t ∈ Set.uIcc (-13 : ℝ) 13,
      0 < ((1 : ℂ) * riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR4 : ∀ t ∈ Set.uIcc (13 : ℝ) (29/2),
      0 < ((-I) * riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR5 : ∀ t ∈ Set.uIcc (29/2 : ℝ) 15,
      0 < ((-1 : ℂ) * riemannXiEntire (⟨1, t⟩ : ℂ)).re) :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF = (2 : ℂ) := by
  refine rectangleIntegral'_logDeriv_eq_of_branch_chain hBot hTop hR1 hR2 hR3 hR4 hR5
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [xi_left_eq_conj_right t, re_neg_one_mul_conj]
    exact hR1 t ht
  · intro t ht
    rw [xi_left_eq_conj_right t, re_neg_I_mul_conj]
    exact hR2 t ht
  · intro t ht
    rw [xi_left_eq_conj_right t, re_one_mul_conj]
    exact hR3 t ht
  · intro t ht
    rw [xi_left_eq_conj_right t, re_I_mul_conj]
    exact hR4 t ht
  · intro t ht
    rw [xi_left_eq_conj_right t, re_neg_one_mul_conj]
    exact hR5 t ht

end

end RectangleLogBranchR331g
end PrincipiaTractalis
