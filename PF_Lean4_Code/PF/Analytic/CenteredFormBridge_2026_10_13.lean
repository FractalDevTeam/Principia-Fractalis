/-
# CenteredFormBridge_2026_10_13 — the mean-value sign bridge for the right edge

Pure-real-analysis bridge: if `f : ℝ → ℝ` has a derivative bounded in modulus by
`L` on `[c - r, c + r]`, and `f c` exceeds `L · r` in absolute value, then `f`
has the same strict sign throughout `[c - r, c + r]`.

This is the mathematical content of the "centered / mean-value form"
`f(t) ∈ f(c) + f'(box) · [-r, r]` analysed empirically in
`codex/TBOX_CENTERED_FORM_LEVER_2026-10-10.md` and
`codex/ARB_CERTIFIED_MARCH_2026-10-10.md`. Those notes measured the
interval-dependency collapse 30–184× on R1/R2/R3; this file supplies the exact
Lean statement that converts a certified `(f(c), L)` pair into a per-box sign
over the whole closed `t`-box.

### What this file is / is NOT

* **IS:** the kernel-clean, additive, generic Lean consumer. Given any pair
  `(point value at c, modulus bound L on f')` plus a strict margin
  `L · r < |f c|`, concludes `0 < f` (or `f < 0`) uniformly on `[c - r, c + r]`.
* **IS NOT:** a certified `(f(c), L)` producer for `ξ(1 + it)`. That is the
  genuinely-new ingredient of the campaign (certified interval enclosures of
  `completedRiemannZeta₀` and its derivative, through `t`-boxed theta
  quadrature), the next piece after this one. See
  `TBOX_CENTERED_FORM_LEVER_2026-10-10.md` §Consequence for the generator
  transpose.
* **IS NOT:** a claim about the open Riemann Hypothesis. `rh_below_15_conditional`
  is RH on one finite rectangle, classically known since Riemann and Gram.
  Nothing here bears on the open problem.

### Specialisations

`edgeRe t := Re ξ(1+it)` and `edgeIm t := Im ξ(1+it)` are differentiable `ℝ → ℝ`
by composition: `riemannXiEntire` is entire (`differentiable_riemannXiEntire`,
r325) and the line `t ↦ 1 + it : ℝ → ℂ` is differentiable. The per-box R1/R2/R3
specialisations state the sign claim as a function of `(center value, derivative
modulus bound L on `deriv edgeRe` / `deriv edgeIm`, box radius r, strict margin)`.

### No sorry / native_decide / axiom / Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-13.
-/

import PF.Analytic.EdgeSignNeighborhoods_2026_10_13
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace PrincipiaTractalis
namespace CenteredFormBridge20261013

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013

noncomputable section

/-! ## §0 — Generic centered-form sign bridges

The core statement: a modulus bound on `f'` plus a strict margin on `f c`
propagate the sign to the whole closed box `[c - r, c + r]`, via the mean-value
inequality `|f t - f c| ≤ L · |t - c| ≤ L · r`.

The derivative function `f'` is passed as an argument so the caller can plug in
any concrete derivative. -/

/-- **Centered-form positivity bridge.** If `f` is differentiable with
derivative modulus bounded by `L` on `[c - r, c + r]`, and `L · r < f c`, then
`0 < f t` for every `t ∈ [c - r, c + r]`. -/
theorem centered_form_pos
    {f f' : ℝ → ℝ} {c r L : ℝ}
    (hr : 0 ≤ r)
    (hderiv : ∀ x ∈ Icc (c - r) (c + r), HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Icc (c - r) (c + r), |f' x| ≤ L)
    (hmargin : L * r < f c) :
    ∀ t ∈ Icc (c - r) (c + r), 0 < f t := by
  intro t ht
  have hc_mem : c ∈ Icc (c - r) (c + r) := by
    rw [Set.mem_Icc]; refine ⟨by linarith, by linarith⟩
  have hL_nn : 0 ≤ L := by
    have h1 : |f' c| ≤ L := hbound c hc_mem
    have h2 : 0 ≤ |f' c| := abs_nonneg _
    linarith
  have hconvex : Convex ℝ (Icc (c - r) (c + r)) := convex_Icc _ _
  -- Mean-value inequality: ‖f t - f c‖ ≤ L * ‖t - c‖, instantiated at x := c, y := t.
  have hlip : ‖f t - f c‖ ≤ L * ‖t - c‖ :=
    hconvex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hderiv x hx).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hbound x hx)
      hc_mem ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hlip
  rw [Set.mem_Icc] at ht
  have h_tr : |t - c| ≤ r := by
    rcases le_or_gt t c with hle | hgt
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)]; linarith
    · rw [abs_of_pos (sub_pos.mpr hgt)]; linarith
  have hLr : L * |t - c| ≤ L * r := mul_le_mul_of_nonneg_left h_tr hL_nn
  have hlower : f c - L * r ≤ f t := by
    have h1 : -(L * |t - c|) ≤ f t - f c := neg_le_of_abs_le hlip
    linarith
  linarith

/-- **Centered-form negativity bridge.** If `f` is differentiable with
derivative modulus bounded by `L` on `[c - r, c + r]`, and `f c < -(L · r)`,
then `f t < 0` for every `t ∈ [c - r, c + r]`. -/
theorem centered_form_neg
    {f f' : ℝ → ℝ} {c r L : ℝ}
    (hr : 0 ≤ r)
    (hderiv : ∀ x ∈ Icc (c - r) (c + r), HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Icc (c - r) (c + r), |f' x| ≤ L)
    (hmargin : f c < -(L * r)) :
    ∀ t ∈ Icc (c - r) (c + r), f t < 0 := by
  -- Apply the positivity bridge to `-f` with derivative `fun x => -f' x`.
  have hd' : ∀ x ∈ Icc (c - r) (c + r), HasDerivAt (fun y => -f y) (-f' x) x :=
    fun x hx => (hderiv x hx).neg
  have hb' : ∀ x ∈ Icc (c - r) (c + r), |(-f' x)| ≤ L := by
    intro x hx; rw [abs_neg]; exact hbound x hx
  have hm' : L * r < (fun y => -f y) c := by
    show L * r < -f c; linarith
  have hpos := centered_form_pos (f := fun y => -f y) (f' := fun x => -f' x)
    hr hd' hb' hm'
  intro t ht
  have := hpos t ht
  show f t < 0
  linarith

/-! ## §1 — Differentiability of the right-edge functions `edgeRe` / `edgeIm`

Composition: `edgeRe = Re ∘ ξ ∘ edgeLine`, where `edgeLine : ℝ → ℂ`,
`edgeLine s = 1 + i·s`. Each factor is differentiable; the composition is
differentiable. `edgeIm` is the same chain with `Im`. -/

/-- The line `t ↦ 1 + it` is `ℝ`-differentiable. -/
theorem differentiable_edgeLine : Differentiable ℝ (fun s : ℝ => (⟨1, s⟩ : ℂ)) := by
  have h : (fun s : ℝ => (⟨1, s⟩ : ℂ))
      = fun s : ℝ => Complex.I * (s : ℂ) + 1 := by
    funext s; apply Complex.ext <;> simp
  rw [h]
  have hofReal : Differentiable ℝ (fun s : ℝ => (s : ℂ)) :=
    Complex.ofRealCLM.differentiable
  exact (hofReal.const_mul Complex.I).add_const 1

/-- `edgeRe` is `ℝ`-differentiable. -/
theorem differentiable_edgeRe : Differentiable ℝ edgeRe := by
  unfold edgeRe
  exact Complex.reCLM.differentiable.comp
    ((differentiable_riemannXiEntire.restrictScalars ℝ).comp differentiable_edgeLine)

/-- `edgeIm` is `ℝ`-differentiable. -/
theorem differentiable_edgeIm : Differentiable ℝ edgeIm := by
  unfold edgeIm
  exact Complex.imCLM.differentiable.comp
    ((differentiable_riemannXiEntire.restrictScalars ℝ).comp differentiable_edgeLine)

/-- `edgeRe` has derivative `deriv edgeRe t` at every real `t`. -/
theorem hasDerivAt_edgeRe (t : ℝ) : HasDerivAt edgeRe (deriv edgeRe t) t :=
  (differentiable_edgeRe t).hasDerivAt

/-- `edgeIm` has derivative `deriv edgeIm t` at every real `t`. -/
theorem hasDerivAt_edgeIm (t : ℝ) : HasDerivAt edgeIm (deriv edgeIm t) t :=
  (differentiable_edgeIm t).hasDerivAt

/-! ## §2 — Per-box R1 / R2 / R3 centered-form sign claims

Each specialisation takes a `(c, r, L, Mc)` producer bundle plus a strict margin
and concludes `R1_box` / `R2_box` / `R3_box`-compatible sign over the whole
closed box `[c - r, c + r]`. The `Mc = f c` and `L` are inputs; a future
certified producer discharges them. -/

/-- **R1 centered-form box** — right-edge real-part positivity on
`[c - r, c + r]` from a `(Re ξ(1 + ic), L)` certification with margin. -/
theorem R1_box_centered
    {c r L Mc : ℝ}
    (hr : 0 ≤ r)
    (hvalue : (riemannXiEntire (⟨1, c⟩ : ℂ)).re = Mc)
    (hbound : ∀ x ∈ Icc (c - r) (c + r), |deriv edgeRe x| ≤ L)
    (hmargin : L * r < Mc) :
    ∀ t ∈ Icc (c - r) (c + r), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have hmargin' : L * r < edgeRe c := by
    show L * r < (riemannXiEntire (⟨1, c⟩ : ℂ)).re; rw [hvalue]; exact hmargin
  exact centered_form_pos (f := edgeRe) (f' := deriv edgeRe)
    hr (fun x _ => hasDerivAt_edgeRe x) hbound hmargin'

/-- **R2 centered-form box** — right-edge imaginary-part positivity on
`[c - r, c + r]` from a `(Im ξ(1 + ic), L)` certification with margin. -/
theorem R2_box_centered
    {c r L Mc : ℝ}
    (hr : 0 ≤ r)
    (hvalue : (riemannXiEntire (⟨1, c⟩ : ℂ)).im = Mc)
    (hbound : ∀ x ∈ Icc (c - r) (c + r), |deriv edgeIm x| ≤ L)
    (hmargin : L * r < Mc) :
    ∀ t ∈ Icc (c - r) (c + r), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im := by
  have hmargin' : L * r < edgeIm c := by
    show L * r < (riemannXiEntire (⟨1, c⟩ : ℂ)).im; rw [hvalue]; exact hmargin
  exact centered_form_pos (f := edgeIm) (f' := deriv edgeIm)
    hr (fun x _ => hasDerivAt_edgeIm x) hbound hmargin'

/-- **R3 centered-form box** — right-edge real-part negativity on
`[c - r, c + r]` from a `(Re ξ(1 + ic), L)` certification with margin. -/
theorem R3_box_centered
    {c r L Mc : ℝ}
    (hr : 0 ≤ r)
    (hvalue : (riemannXiEntire (⟨1, c⟩ : ℂ)).re = Mc)
    (hbound : ∀ x ∈ Icc (c - r) (c + r), |deriv edgeRe x| ≤ L)
    (hmargin : Mc < -(L * r)) :
    ∀ t ∈ Icc (c - r) (c + r), (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0 := by
  have hmargin' : edgeRe c < -(L * r) := by
    show (riemannXiEntire (⟨1, c⟩ : ℂ)).re < -(L * r); rw [hvalue]; exact hmargin
  exact centered_form_neg (f := edgeRe) (f' := deriv edgeRe)
    hr (fun x _ => hasDerivAt_edgeRe x) hbound hmargin'

end

/-! ## §Axiom check -/

#print axioms centered_form_pos
#print axioms centered_form_neg
#print axioms differentiable_edgeLine
#print axioms differentiable_edgeRe
#print axioms differentiable_edgeIm
#print axioms hasDerivAt_edgeRe
#print axioms hasDerivAt_edgeIm
#print axioms R1_box_centered
#print axioms R2_box_centered
#print axioms R3_box_centered

end CenteredFormBridge20261013
end PrincipiaTractalis
