/-
# PF.Analytic.Lambda0IBPIdentity_2026_10_15

**L4 of the IBP decay chain** — the integration-by-parts identity for `Λ₀` on
the edge `Re s = 1`, with the zeroth-order boundary terms CANCELLED.

Rio's directive 2026-10-15. The target identity is

  `Λ₀(1 + it) = (2/(it)) · [ ∫_{u>0} F₋'(u)·e^{-itu/2} du
                            − ∫_{u>0} F₊'(u)·e^{+itu/2} du ]`,

whose point is the **zeroth-order boundary cancellation**: `F₊(0) = F₋(0) = ω(1)`,
and the two branches carry opposite frequencies `±t/2`, so the `O(1/t)` boundary
contributions cancel exactly and the true decay rate is `1/t²`, not `1/|t|`.
This corrects `LAMBDA0_IBP_DECAY_STRATEGY_2026-10-14.md`, which reported `1/|t|`,
as flagged in `PILOT14_GATE_ANALYSIS_2026-10-14.md`.

## This file

§0  `(e^u)^w = e^{uw}` and the two `Real.exp` image identities.
§1  **Edge representation.** `Λ₀(1+it) = ∫_{u>0} F₊(u)e^{itu/2} + ∫_{u>0} F₋(u)e^{-itu/2}`,
    obtained from Riemann's symmetric theta representation
    (`XiThetaIntegral.completedRiemannZeta₀_eq_theta_integral`, valid on ALL of ℂ,
    so no analytic-continuation argument is needed) by the change of variables
    `x = e^u` on `Ioi 1` via `MeasureTheory.integral_comp_smul_deriv_Ioi`
    at `f = Real.exp`, `a = 0`.

Why this shape: `F₊(u) = e^{u/2}·ω(e^u)` and `F₋(u) = ω(e^u)` are precisely the
two Mellin branches of the symmetric representation after `x = e^u`; the
`e^u` Jacobian is what turns the exponents `s/2−1` and `(1−s)/2−1` into
`+itu/2` and `−itu/2` with the `e^{u/2}` landing on the plus branch only.

Foundations consumed, all landed: `OmegaDerivativeBounds_2026_10_15`
(`F_plus_integrable_Ioi`, `F_minus_integrable_Ioi`) and `XiThetaIntegral`
(`completedRiemannZeta₀_eq_theta_integral`, `continuousOn_omega`,
`integrableOn_cpow_smul_evenKernel_sub_one`).

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-15.
-/

import PF.Analytic.OmegaDerivativeBounds_2026_10_15
import PF.Analytic.XiThetaIntegral

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Lambda0IBPIdentity20261015

open Complex Set MeasureTheory Filter Topology HurwitzZeta
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaDerivativeBounds20261015

noncomputable section

/-! ## §0 — elementary bridges -/

/-- `(e^u)^w = e^{u·w}` for real `u` and complex exponent `w`: the base is a
positive real, so `Complex.log` of it is the real log and the branch cut is
never touched. -/
theorem exp_ofReal_cpow (u : ℝ) (w : ℂ) :
    ((Real.exp u : ℝ) : ℂ) ^ w = Complex.exp ((u : ℂ) * w) := by
  have hne : ((Real.exp u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos u).le,
    Real.log_exp]

/-- `‖e^{c·x}‖ = 1` whenever `c` is purely imaginary and `x` real. -/
theorem norm_exp_mul_ofReal {c : ℂ} (hcre : c.re = 0) (x : ℝ) :
    ‖Complex.exp (c * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (c * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, hcre]
  rw [h, Real.exp_zero]

/-- `(i·t/2).re = 0`. -/
theorem re_phase_plus (t : ℝ) : (Complex.I * ((t : ℂ) / 2)).re = 0 := by simp

/-- `(−i·t/2).re = 0`. -/
theorem re_phase_minus (t : ℝ) : (-(Complex.I * ((t : ℂ) / 2))).re = 0 := by simp

/-- Multiplying by a unit-modulus phase preserves integrability on `(0,∞)`.
This is the single lemma behind all four phase-integrability side conditions
(`F₊`, `F₋`, `F₊'`, `F₋'`). -/
theorem integrableOn_phase_of_integrableOn {g : ℝ → ℝ} {c : ℂ} (hcre : c.re = 0)
    (hg : IntegrableOn g (Ioi (0 : ℝ))) :
    IntegrableOn (fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ)))
      (Ioi (0 : ℝ)) := by
  refine Integrable.mono' hg.abs ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      hg.aestronglyMeasurable).mul
      (Complex.continuous_exp.comp
        (by continuity : Continuous fun y : ℝ => c * (y : ℂ))).aestronglyMeasurable
  · filter_upwards with u
    rw [norm_mul, norm_exp_mul_ofReal hcre, mul_one, Complex.norm_real,
      Real.norm_eq_abs]

/-- `Real.exp '' Ioi 0 = Ioi 1`. -/
theorem exp_image_Ioi_zero : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have := Real.exp_lt_exp.mpr (mem_Ioi.mp hu)
    rw [Real.exp_zero] at this
    exact mem_Ioi.mpr this
  · intro hx
    have hx1 : (1 : ℝ) < x := mem_Ioi.mp hx
    exact ⟨Real.log x, mem_Ioi.mpr (Real.log_pos hx1),
      Real.exp_log (lt_trans zero_lt_one hx1)⟩

/-- `Real.exp '' Ici 0 = Ici 1`. -/
theorem exp_image_Ici_zero : Real.exp '' Ici (0 : ℝ) = Ici (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have := Real.exp_le_exp.mpr (mem_Ici.mp hu)
    rw [Real.exp_zero] at this
    exact mem_Ici.mpr this
  · intro hx
    have hx1 : (1 : ℝ) ≤ x := mem_Ici.mp hx
    exact ⟨Real.log x, mem_Ici.mpr (Real.log_nonneg hx1),
      Real.exp_log (lt_of_lt_of_le zero_lt_one hx1)⟩

/-! ## §1 — the edge representation -/

/-- The symmetric theta integrand of Riemann's representation, specialised to
the edge point `s = 1 + it`. -/
def edgeThetaIntegrand (t : ℝ) (x : ℝ) : ℂ :=
  ((x : ℂ) ^ ((⟨1, t⟩ : ℂ) / 2 - 1) + (x : ℂ) ^ ((1 - (⟨1, t⟩ : ℂ)) / 2 - 1))
    * ((omega x : ℝ) : ℂ)

/-- `s = 1 + it` in rectangular form. -/
theorem edge_point_eq (t : ℝ) : (⟨1, t⟩ : ℂ) = 1 + Complex.I * (t : ℂ) := by
  apply Complex.ext <;> simp

/-- **The Jacobian computation.** Under `x = e^u` the `e^u` Jacobian turns the
symmetric theta integrand into the two `F`-branches with frequencies `±t/2`. -/
theorem exp_smul_edgeThetaIntegrand (t u : ℝ) :
    (Real.exp u : ℝ) • edgeThetaIntegrand t (Real.exp u)
      = ((F_plus u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))
        + ((F_minus u : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)) := by
  have hFp : ((F_plus u : ℝ) : ℂ)
      = Complex.exp ((u : ℂ) / 2) * ((omega (Real.exp u) : ℝ) : ℂ) := by
    rw [F_plus, Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hFm : ((F_minus u : ℝ) : ℂ) = ((omega (Real.exp u) : ℝ) : ℂ) := by
    rw [F_minus]
  have hA : (u : ℂ) + (u : ℂ) * ((1 + Complex.I * (t : ℂ)) / 2 - 1)
      = (u : ℂ) / 2 + Complex.I * ((t : ℂ) / 2) * (u : ℂ) := by ring
  have hB : (u : ℂ) + (u : ℂ) * ((1 - (1 + Complex.I * (t : ℂ))) / 2 - 1)
      = -(Complex.I * ((t : ℂ) / 2)) * (u : ℂ) := by ring
  rw [edgeThetaIntegrand, exp_ofReal_cpow, exp_ofReal_cpow, hFp, hFm,
    Complex.real_smul, Complex.ofReal_exp, edge_point_eq]
  have step :
      Complex.exp ((u : ℂ))
          * ((Complex.exp ((u : ℂ) * ((1 + Complex.I * (t : ℂ)) / 2 - 1))
              + Complex.exp ((u : ℂ) * ((1 - (1 + Complex.I * (t : ℂ))) / 2 - 1)))
            * ((omega (Real.exp u) : ℝ) : ℂ))
        = (Complex.exp ((u : ℂ) + (u : ℂ) * ((1 + Complex.I * (t : ℂ)) / 2 - 1))
            + Complex.exp ((u : ℂ)
                + (u : ℂ) * ((1 - (1 + Complex.I * (t : ℂ))) / 2 - 1)))
          * ((omega (Real.exp u) : ℝ) : ℂ) := by
    rw [Complex.exp_add, Complex.exp_add]; ring
  rw [step, hA, hB, Complex.exp_add]
  ring

/-! ### §1b — side conditions for the change of variables -/

/-- `x ↦ x^w · ω(x)` is integrable on `(1,∞)` for EVERY complex exponent `w`,
inherited from the all-`s` convergence of the strong FE-pair's Mellin transform
(`integrableOn_cpow_smul_evenKernel_sub_one`) via `θ − 1 = 2ω`. -/
theorem integrableOn_cpow_mul_omega (w : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ w * ((omega x : ℝ) : ℂ)) (Ioi (1 : ℝ)) := by
  have h := integrableOn_cpow_smul_evenKernel_sub_one w
  have key : ∀ x ∈ Ioi (1 : ℝ),
      (x : ℂ) ^ w • (((evenKernel 0 x : ℝ) : ℂ) - 1)
        = (2 : ℂ) * ((x : ℂ) ^ w * ((omega x : ℝ) : ℂ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one (mem_Ioi.mp hx)
    rw [evenKernel_zero_eq hx0, smul_eq_mul]
    push_cast
    ring
  have h2 : IntegrableOn
      (fun x : ℝ => (2 : ℂ) * ((x : ℂ) ^ w * ((omega x : ℝ) : ℂ))) (Ioi (1 : ℝ)) :=
    h.congr_fun key measurableSet_Ioi
  simpa using h2.const_mul (2 : ℂ)⁻¹

/-- The edge theta integrand is integrable on `(1,∞)`. -/
theorem integrableOn_edgeThetaIntegrand (t : ℝ) :
    IntegrableOn (edgeThetaIntegrand t) (Ioi (1 : ℝ)) := by
  have hp := integrableOn_cpow_mul_omega ((⟨1, t⟩ : ℂ) / 2 - 1)
  have hm := integrableOn_cpow_mul_omega ((1 - (⟨1, t⟩ : ℂ)) / 2 - 1)
  have hsum : IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ ((⟨1, t⟩ : ℂ) / 2 - 1) * ((omega x : ℝ) : ℂ)
        + (x : ℂ) ^ ((1 - (⟨1, t⟩ : ℂ)) / 2 - 1) * ((omega x : ℝ) : ℂ))
      (Ioi (1 : ℝ)) := hp.add hm
  refine hsum.congr_fun (fun x _ => ?_) measurableSet_Ioi
  rw [edgeThetaIntegrand]
  ring

/-- The edge theta integrand is continuous on `(1,∞)`. -/
theorem continuousOn_edgeThetaIntegrand (t : ℝ) :
    ContinuousOn (edgeThetaIntegrand t) (Ioi (1 : ℝ)) := by
  have hcpow : ∀ w : ℂ, ContinuousOn (fun x : ℝ => (x : ℂ) ^ w) (Ioi (1 : ℝ)) := by
    intro w x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one (mem_Ioi.mp hx)
    exact (Complex.continuousAt_ofReal_cpow_const x w
      (Or.inr (ne_of_gt hx0))).continuousWithinAt
  have homega : ContinuousOn (fun x : ℝ => ((omega x : ℝ) : ℂ)) (Ioi (1 : ℝ)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_omega.mono
        (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx))))
  exact ((hcpow _).add (hcpow _)).mul homega

/-- The `+` branch with its unit-modulus phase is integrable on `(0,∞)`. -/
theorem integrableOn_F_plus_phase (t : ℝ) :
    IntegrableOn (fun u : ℝ =>
        ((F_plus u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)))
      (Ioi (0 : ℝ)) :=
  integrableOn_phase_of_integrableOn (re_phase_plus t) F_plus_integrable_Ioi

/-- The `−` branch with its unit-modulus phase is integrable on `(0,∞)`. -/
theorem integrableOn_F_minus_phase (t : ℝ) :
    IntegrableOn (fun u : ℝ =>
        ((F_minus u : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)))
      (Ioi (0 : ℝ)) :=
  integrableOn_phase_of_integrableOn (re_phase_minus t) F_minus_integrable_Ioi

/-! ### §1c — ★ the edge representation ★ -/

/-- **★★★ EDGE REPRESENTATION ★★★** — for EVERY real `t`:

  `Λ₀(1 + it) = ∫_{u>0} F₊(u)·e^{+itu/2} du + ∫_{u>0} F₋(u)·e^{−itu/2} du`.

Riemann's symmetric theta representation is valid on all of ℂ, so this needs no
analytic continuation; the change of variables `x = e^u` is
`MeasureTheory.integral_comp_smul_deriv_Ioi` at `f = Real.exp`, `a = 0`. -/
theorem lambda0_edge_eq_F_integrals (t : ℝ) :
    completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
      = (∫ u in Ioi (0 : ℝ),
            ((F_plus u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)))
        + ∫ u in Ioi (0 : ℝ),
            ((F_minus u : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)) := by
  have hrep : completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
      = ∫ x in Ioi (1 : ℝ), edgeThetaIntegrand t x := by
    rw [completedRiemannZeta₀_eq_theta_integral]
    rfl
  have hIci : IntegrableOn (edgeThetaIntegrand t) (Ici (1 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_edgeThetaIntegrand t)
  have hphasesum : IntegrableOn (fun u : ℝ =>
      ((F_plus u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))
        + ((F_minus u : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)))
      (Ioi (0 : ℝ)) :=
    (integrableOn_F_plus_phase t).add (integrableOn_F_minus_phase t)
  have hg2 : IntegrableOn
      (fun x : ℝ => Real.exp x • (edgeThetaIntegrand t ∘ Real.exp) x) (Ici (0 : ℝ)) := by
    refine (integrableOn_Ici_iff_integrableOn_Ioi).mpr ?_
    exact hphasesum.congr_fun
      (fun u _ => (exp_smul_edgeThetaIntegrand t u).symm) measurableSet_Ioi
  have hcov : (∫ x in Ioi (0 : ℝ), Real.exp x • (edgeThetaIntegrand t ∘ Real.exp) x)
      = ∫ u in Ioi (1 : ℝ), edgeThetaIntegrand t u := by
    have h := integral_comp_smul_deriv_Ioi
      (f := Real.exp) (f' := Real.exp) (g := edgeThetaIntegrand t) (a := 0)
      Real.continuous_exp.continuousOn Real.tendsto_exp_atTop
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (by rw [exp_image_Ioi_zero]; exact continuousOn_edgeThetaIntegrand t)
      (by rw [exp_image_Ici_zero]; exact hIci)
      hg2
    rwa [Real.exp_zero] at h
  have hsplit : (∫ x in Ioi (0 : ℝ), Real.exp x • (edgeThetaIntegrand t ∘ Real.exp) x)
      = (∫ u in Ioi (0 : ℝ),
            ((F_plus u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)))
        + ∫ u in Ioi (0 : ℝ),
            ((F_minus u : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)) := by
    rw [← integral_add (integrableOn_F_plus_phase t) (integrableOn_F_minus_phase t)]
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun u _ => exp_smul_edgeThetaIntegrand t u)
  rw [hrep, ← hcov, hsplit]

/-! ## §2 — improper integration by parts against a unit-modulus phase -/

/-- `x ↦ e^{c·x}` has derivative `c·e^{c·x}`, as a map `ℝ → ℂ`. -/
theorem hasDerivAt_exp_mul_ofReal (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (c * Complex.exp (c * (x : ℂ))) x := by
  have hlin : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
  simpa [mul_comm] using (Complex.hasDerivAt_exp (c * (x : ℂ))).comp x hlin

/-- **★ IMPROPER INTEGRATION BY PARTS ★** — for a real function `F` that is
differentiable on `(0,∞)`, continuous at `0` from the right and vanishing at
infinity, tested against a purely-imaginary phase `e^{cx}`:

  `∫_{x>0} F(x)·e^{cx} dx = −F(0)/c − (1/c)·∫_{x>0} F'(x)·e^{cx} dx`.

The boundary term at `∞` vanishes because `F → 0` and `‖e^{cx}‖ = 1`; the
boundary term at `0` is `F(0)/c`. This is the single lemma the two `F₊`/`F₋`
branches are both instances of, with `c = ±it/2`. -/
theorem ibp_phase {F F' : ℝ → ℝ} {c : ℂ} (hc : c ≠ 0) (hcre : c.re = 0)
    (hFderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F (F' x) x)
    (hFcont0 : ContinuousWithinAt F (Ici 0) 0)
    (hFtop : Tendsto F atTop (𝓝 0))
    (hFint : IntegrableOn
      (fun u : ℝ => ((F u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ))) (Ioi 0))
    (hF'int : IntegrableOn
      (fun u : ℝ => ((F' u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ))) (Ioi 0)) :
    (∫ u in Ioi (0 : ℝ), ((F u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ)))
      = -(((F 0 : ℝ) : ℂ) / c)
        - (1 / c) * ∫ u in Ioi (0 : ℝ),
            ((F' u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ)) := by
  -- the antiderivative of the phase
  set V : ℝ → ℂ := fun y => Complex.exp (c * (y : ℂ)) / c with hV
  have hVderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt V (Complex.exp (c * (x : ℂ))) x := by
    intro x _
    have h := (hasDerivAt_exp_mul_ofReal c x).div_const c
    rw [hV]
    simpa [mul_comm, mul_div_assoc, mul_div_cancel_left₀ _ hc] using h
  have hUderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => ((F y : ℝ) : ℂ)) ((F' x : ℝ) : ℂ) x :=
    fun x hx => (hFderiv x hx).ofReal_comp
  -- the two integrability side conditions, in the shapes mathlib wants
  have huv' : IntegrableOn
      (fun u : ℝ => ((F u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ))) (Ioi 0) := hFint
  have hF'div : IntegrableOn
      (fun u : ℝ => ((F' u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ)) / c) (Ioi 0) :=
    hF'int.div_const c
  have hu'v : IntegrableOn (fun u : ℝ => ((F' u : ℝ) : ℂ) * V u) (Ioi 0) :=
    hF'div.congr_fun (fun u _ => by rw [hV]; ring) measurableSet_Ioi
  -- boundary behaviour at `0⁺`
  have h_zero : Tendsto (fun y : ℝ => ((F y : ℝ) : ℂ) * V y) (𝓝[>] (0 : ℝ))
      (𝓝 (((F 0 : ℝ) : ℂ) / c)) := by
    have hF0 : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
      hFcont0.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have hVt : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 (1 / c)) := by
      have : ContinuousAt V 0 := by
        rw [hV]
        exact ((Complex.continuous_exp.comp
          (by continuity : Continuous fun y : ℝ => c * (y : ℂ))).div_const c).continuousAt
      have h0 : V 0 = 1 / c := by rw [hV]; simp
      rw [← h0]
      exact this.continuousWithinAt.tendsto
    have := (Complex.continuous_ofReal.continuousAt.tendsto.comp hF0).mul hVt
    simpa [div_eq_mul_inv, one_div] using this
  -- boundary behaviour at `∞`
  have h_infty : Tendsto (fun y : ℝ => ((F y : ℝ) : ℂ) * V y) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ y : ℝ, ‖((F y : ℝ) : ℂ) * V y‖ = |F y| * (1 / ‖c‖) := by
      intro y
      rw [hV]
      rw [norm_mul, norm_div, norm_exp_mul_ofReal hcre, Complex.norm_real,
        Real.norm_eq_abs]
    simp only [hnorm]
    have : Tendsto (fun y : ℝ => |F y|) atTop (𝓝 0) := by
      simpa using (continuous_abs.continuousAt.tendsto.comp hFtop)
    simpa using this.mul_const (1 / ‖c‖)
  -- apply mathlib's improper IBP
  have hmain := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => ((F y : ℝ) : ℂ)) (u' := fun y : ℝ => ((F' y : ℝ) : ℂ))
    (v := V) (v' := fun y : ℝ => Complex.exp (c * (y : ℂ))) (a := 0)
    hUderiv hVderiv huv' hu'v h_zero h_infty
  rw [hmain, zero_sub]
  have hrw : (∫ u in Ioi (0 : ℝ), ((F' u : ℝ) : ℂ) * V u)
      = (1 / c) * ∫ u in Ioi (0 : ℝ), ((F' u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ)) := by
    rw [hV, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    ring
  rw [hrw]

/-! ## §3 — the two branches, and the boundary cancellation -/

/-- `i·t/2 ≠ 0` when `t ≠ 0`. -/
theorem phase_plus_ne_zero {t : ℝ} (ht : t ≠ 0) : Complex.I * ((t : ℂ) / 2) ≠ 0 := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  exact mul_ne_zero Complex.I_ne_zero (by simpa using htc)

/-- `−i·t/2 ≠ 0` when `t ≠ 0`. -/
theorem phase_minus_ne_zero {t : ℝ} (ht : t ≠ 0) :
    -(Complex.I * ((t : ℂ) / 2)) ≠ 0 := neg_ne_zero.mpr (phase_plus_ne_zero ht)

/-- `deriv F_plus` is integrable on `(0,∞)` — the variation of `F₊` is finite
because `F₊` is monotone, continuous at `0` and vanishes at infinity. -/
theorem integrableOn_deriv_F_plus : IntegrableOn (deriv F_plus) (Ioi (0 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonpos
    (F_plus_continuous.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl))
    (fun x _ => (F_plus_hasDerivAt x).congr_deriv ((F_plus_hasDerivAt x).deriv).symm)
    (fun _ hx => deriv_F_plus_nonpos_on_Ioi (mem_Ioi.mp hx))
    F_plus_tendsto_atTop_zero

/-- `deriv F_minus` is integrable on `(0,∞)`. -/
theorem integrableOn_deriv_F_minus : IntegrableOn (deriv F_minus) (Ioi (0 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonpos
    (F_minus_continuous.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl))
    (fun x _ => (F_minus_hasDerivAt x).congr_deriv ((F_minus_hasDerivAt x).deriv).symm)
    (fun x _ => deriv_F_minus_nonpos x)
    F_minus_tendsto_atTop_zero

/-- **The boundary values coincide:** `F₊(0) = ω(1)`. -/
theorem F_plus_zero : F_plus 0 = omega 1 := by
  rw [F_plus]
  norm_num

/-- **The boundary values coincide:** `F₋(0) = ω(1)`. -/
theorem F_minus_zero : F_minus 0 = omega 1 := by
  rw [F_minus]
  norm_num

/-- IBP on the `+` branch. -/
theorem ibp_F_plus_branch {t : ℝ} (ht : t ≠ 0) :
    (∫ u in Ioi (0 : ℝ),
        ((F_plus u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)))
      = -(((omega 1 : ℝ) : ℂ) / (Complex.I * ((t : ℂ) / 2)))
        - (1 / (Complex.I * ((t : ℂ) / 2)))
            * ∫ u in Ioi (0 : ℝ),
                ((deriv F_plus u : ℝ) : ℂ)
                  * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)) := by
  have h := ibp_phase (F := F_plus) (F' := deriv F_plus)
    (phase_plus_ne_zero ht) (re_phase_plus t)
    (fun x _ => (F_plus_hasDerivAt x).congr_deriv ((F_plus_hasDerivAt x).deriv).symm)
    (F_plus_continuous.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl))
    F_plus_tendsto_atTop_zero
    (integrableOn_phase_of_integrableOn (re_phase_plus t) F_plus_integrable_Ioi)
    (integrableOn_phase_of_integrableOn (re_phase_plus t) integrableOn_deriv_F_plus)
  rwa [F_plus_zero] at h

/-- IBP on the `−` branch. -/
theorem ibp_F_minus_branch {t : ℝ} (ht : t ≠ 0) :
    (∫ u in Ioi (0 : ℝ),
        ((F_minus u : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)))
      = -(((omega 1 : ℝ) : ℂ) / (-(Complex.I * ((t : ℂ) / 2))))
        - (1 / (-(Complex.I * ((t : ℂ) / 2))))
            * ∫ u in Ioi (0 : ℝ),
                ((deriv F_minus u : ℝ) : ℂ)
                  * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)) := by
  have h := ibp_phase (F := F_minus) (F' := deriv F_minus)
    (phase_minus_ne_zero ht) (re_phase_minus t)
    (fun x _ => (F_minus_hasDerivAt x).congr_deriv ((F_minus_hasDerivAt x).deriv).symm)
    (F_minus_continuous.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl))
    F_minus_tendsto_atTop_zero
    (integrableOn_phase_of_integrableOn (re_phase_minus t) F_minus_integrable_Ioi)
    (integrableOn_phase_of_integrableOn (re_phase_minus t) integrableOn_deriv_F_minus)
  rwa [F_minus_zero] at h

/-! ## §4 — ★ THE L4 IDENTITY ★ -/

/-- **★★★★★ L4 — THE IBP IDENTITY WITH BOUNDARY CANCELLATION ★★★★★**

For every nonzero real `t`:

  `Λ₀(1 + it) = (2/(it)) · [ ∫_{u>0} F₋'(u)·e^{−itu/2} du
                            − ∫_{u>0} F₊'(u)·e^{+itu/2} du ]`.

The zeroth-order boundary terms are `−ω(1)/(it/2)` on the `+` branch and
`+ω(1)/(it/2)` on the `−` branch — equal in magnitude, opposite in sign,
because `F₊(0) = F₋(0) = ω(1)` and the two branches carry opposite
frequencies. They cancel EXACTLY, which is why the decay rate of `Λ₀` on the
edge is `1/t²` and not `1/|t|`: the surviving terms each carry one explicit
factor `1/t`, and one further integration by parts on `∫F'e^{±itu/2}` — whose
boundary term `F'(0)` does NOT vanish — supplies the second.

This is the correction to `LAMBDA0_IBP_DECAY_STRATEGY_2026-10-14.md` that
`PILOT14_GATE_ANALYSIS_2026-10-14.md` flagged, now machine-checked. -/
theorem lambda0_edge_ibp_identity {t : ℝ} (ht : t ≠ 0) :
    completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
      = (2 / (Complex.I * (t : ℂ)))
          * ((∫ u in Ioi (0 : ℝ),
                ((deriv F_minus u : ℝ) : ℂ)
                  * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)))
             - ∫ u in Ioi (0 : ℝ),
                ((deriv F_plus u : ℝ) : ℂ)
                  * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))) := by
  have hI : Complex.I * (t : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht)
  rw [lambda0_edge_eq_F_integrals, ibp_F_plus_branch ht, ibp_F_minus_branch ht]
  field_simp
  ring

end

/-! ## §Axiom check

Every declaration below must report exactly
`[propext, Classical.choice, Quot.sound]` — mathlib's own three foundations,
which are unavoidable for any statement mentioning `ℝ` (mathlib builds `ℝ` as a
quotient of Cauchy sequences, so `Quot.sound` is in the kernel path of every
real-number fact). No project axiom, no `sorry`, no `native_decide`. -/

#print axioms exp_ofReal_cpow
#print axioms norm_exp_mul_ofReal
#print axioms integrableOn_phase_of_integrableOn
#print axioms exp_image_Ioi_zero
#print axioms exp_image_Ici_zero
#print axioms exp_smul_edgeThetaIntegrand
#print axioms integrableOn_cpow_mul_omega
#print axioms integrableOn_edgeThetaIntegrand
#print axioms continuousOn_edgeThetaIntegrand
#print axioms lambda0_edge_eq_F_integrals
#print axioms hasDerivAt_exp_mul_ofReal
#print axioms ibp_phase
#print axioms integrableOn_deriv_F_plus
#print axioms integrableOn_deriv_F_minus
#print axioms F_plus_zero
#print axioms F_minus_zero
#print axioms ibp_F_plus_branch
#print axioms ibp_F_minus_branch
#print axioms lambda0_edge_ibp_identity

end Lambda0IBPIdentity20261015
end PrincipiaTractalis
