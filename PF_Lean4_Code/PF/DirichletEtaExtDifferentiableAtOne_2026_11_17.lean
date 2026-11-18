import PF.DirichletEtaExtension_r269
import PF.DirichletEtaExtDifferentiable_r278
import PF.DirichletEtaExtDifferentiableAtOneDisclosure_2026_11_16
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Topology.Separation.Basic

/-!
# `DifferentiableAt ℂ dirichletEtaExtFilled 1`

Closes Dirichlet open-item 2 of `PF/DirichletChainStatus_2026_11_16.lean`
by proving the filled extension `dirichletEtaExtFilled` (introduced in
`DirichletEtaExtDifferentiableAtOneDisclosure_2026_11_16`) is
differentiable at `s = 1`.

## Route

1. `HasDerivAt (fun s => 1 - 2^(1-s)) (Complex.log 2) 1` via
   `HasDerivAt.const_cpow` and `HasDerivAt.const_sub`.
2. `Tendsto ((s - 1)⁻¹ * (1 - 2^(1-s))) (𝓝[≠] 1) (𝓝 (Complex.log 2))`
   via `hasDerivAt_iff_tendsto_slope`.
3. `Tendsto dirichletEtaExt (𝓝[≠] 1) (𝓝 (Complex.log 2))` by factoring
   `dirichletEtaExt s = ((s-1)⁻¹ · (1 - 2^(1-s))) · ((s-1) · ζ s)`
   for `s ≠ 1` and multiplying with `riemannZeta_residue_one`.
4. `ContinuousAt dirichletEtaExtFilled 1` via `continuousAt_update_same`.
5. `DifferentiableAt ℂ dirichletEtaExtFilled 1` via
   `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/

namespace PrincipiaTractalis.DirichletEtaExtDifferentiableAtOne_2026_11_17

open Complex Filter Topology
open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)
open PrincipiaTractalis.DirichletEtaExtDifferentiable
  (dirichletEtaExt_differentiableAt
   dirichletEtaExt_differentiableOn_ne_one)
open PrincipiaTractalis.DirichletEtaExtDifferentiableAtOneDisclosure
  (dirichletEtaExtFilled
   dirichletEtaExtFilled_at_one
   dirichletEtaExtFilled_eq_dirichletEtaExt_of_ne_one
   dirichletEtaExt_eval_at_one)

/-! ## §1  Derivative of `s ↦ 1 - 2^(1-s)` at `s = 1`. -/

/-- `d/ds [1 - 2^(1-s)] at s = 1 is Complex.log 2`. Composition:
    `(1 - 2^(1-s)) = 1 - exp((1-s)·log 2)`; chain rule gives derivative
    `log 2 · 2^(1-s)`, which evaluates to `log 2` at `s = 1`. -/
theorem hasDerivAt_oneMinusTwoCpow_oneSub_atOne :
    HasDerivAt (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) (Complex.log 2) 1 := by
  -- Step A: (1 - s) has derivative -1 at s = 1.
  have hinner : HasDerivAt (fun s : ℂ => (1 : ℂ) - s) (-1) 1 :=
    (hasDerivAt_id' (1 : ℂ)).const_sub 1
  -- Step B: 2^(1-s) has derivative 2^(1-s) * log 2 * (-1) via HasDerivAt.const_cpow.
  have hpow : HasDerivAt (fun s : ℂ => (2 : ℂ) ^ ((1 : ℂ) - s))
      ((2 : ℂ) ^ ((1 : ℂ) - (1 : ℂ)) * Complex.log 2 * (-1)) 1 :=
    hinner.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  -- Step C: simplify 2^0 = 1, so the derivative value is -log 2.
  have hpow' : HasDerivAt (fun s : ℂ => (2 : ℂ) ^ ((1 : ℂ) - s))
      (-Complex.log 2) 1 := by
    convert hpow using 1
    have h0 : (2 : ℂ) ^ ((1 : ℂ) - (1 : ℂ)) = 1 := by
      simp
    rw [h0]; ring
  -- Step D: 1 - (2^(1-s)) has derivative -(-log 2) = log 2.
  have hfinal : HasDerivAt (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s))
      (-(-Complex.log 2)) 1 :=
    hpow'.const_sub 1
  simpa using hfinal

/-! ## §2  Slope at `s = 1` tends to `log 2`. -/

/-- The difference quotient `(1 - 2^(1-s)) / (s - 1)` tends to
    `Complex.log 2` as `s → 1` through values `s ≠ 1`. -/
theorem tendsto_slopeFactor_atOne :
    Tendsto (fun s : ℂ => (s - 1)⁻¹ * ((1 : ℂ) - (2 : ℂ) ^ (1 - s)))
      (𝓝[≠] 1) (𝓝 (Complex.log 2)) := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp hasDerivAt_oneMinusTwoCpow_oneSub_atOne
  refine hslope.congr' ?_
  filter_upwards with s
  -- slope f 1 s = (s - 1)⁻¹ • (f s - f 1); here f 1 = 1 - 2^0 = 0 (simp evaluates it).
  simp [slope, smul_eq_mul]

/-! ## §3  The classical limit `η(s) → log 2` as `s → 1`. -/

/-- **Euler's classical limit** at the removable singularity: the extended
    Dirichlet eta `dirichletEtaExt s = (1 - 2^(1-s)) · ζ(s)` tends to
    `Complex.log 2` as `s → 1` through values `s ≠ 1`. The factor
    `(1 - 2^(1-s))` has a simple zero at `s = 1` whose slope is `log 2`
    (§1), cancelling the simple pole of `ζ` at `s = 1` whose residue is
    `1` (mathlib's `riemannZeta_residue_one`). -/
theorem tendsto_dirichletEtaExt_atOne :
    Tendsto dirichletEtaExt (𝓝[≠] 1) (𝓝 (Complex.log 2)) := by
  have h1 : Tendsto (fun s : ℂ => (s - 1)⁻¹ * ((1 : ℂ) - (2 : ℂ) ^ (1 - s)))
      (𝓝[≠] 1) (𝓝 (Complex.log 2)) := tendsto_slopeFactor_atOne
  have h2 : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (𝓝[≠] 1) (𝓝 1) := riemannZeta_residue_one
  have hprod :
      Tendsto (fun s : ℂ => ((s - 1)⁻¹ * ((1 : ℂ) - (2 : ℂ) ^ (1 - s))) *
                            ((s - 1) * riemannZeta s))
        (𝓝[≠] 1) (𝓝 (Complex.log 2 * 1)) := h1.mul h2
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : s - 1 ≠ 0 := by
    have : s ≠ 1 := hs
    exact sub_ne_zero.mpr this
  unfold PrincipiaTractalis.DirichletEtaExtension.dirichletEtaExt
  field_simp

/-! ## §4  Continuity of `dirichletEtaExtFilled` at `s = 1`. -/

/-- The filled extension is continuous at `s = 1`: it equals
    `Complex.log 2` there (by construction) and its limit through
    `𝓝[≠] 1` is also `Complex.log 2` (§3). -/
theorem continuousAt_dirichletEtaExtFilled_atOne :
    ContinuousAt dirichletEtaExtFilled 1 := by
  show ContinuousAt (Function.update dirichletEtaExt 1 (Complex.log 2)) 1
  exact continuousAt_update_same.mpr tendsto_dirichletEtaExt_atOne

/-! ## §5  Differentiability of `dirichletEtaExtFilled` at `s = 1`. -/

/-- **Headline.** The filled extension `dirichletEtaExtFilled` is
    differentiable at `s = 1`. Closes Dirichlet open-item 2.

    Route: `dirichletEtaExtFilled` agrees with the raw `dirichletEtaExt`
    on `ℂ \ {1}` (open neighbourhood of every non-one point), where
    `dirichletEtaExt` is differentiable (`dirichletEtaExt_differentiableAt`,
    r278). It is continuous at `1` by §4. Then mathlib's weak removable-
    singularity theorem (`Complex.analyticAt_of_differentiable_on_
    punctured_nhds_of_continuousAt`) gives analyticity, hence
    differentiability. -/
theorem dirichletEtaExtFilled_differentiableAt_atOne :
    DifferentiableAt ℂ dirichletEtaExtFilled 1 := by
  have hd : ∀ᶠ z in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ dirichletEtaExtFilled z := by
    filter_upwards [self_mem_nhdsWithin] with z (hz : z ∈ ({1} : Set ℂ)ᶜ)
    have hne : z ≠ 1 := hz
    -- On an open neighbourhood of z (namely {1}ᶜ), filled equals raw.
    have heq : dirichletEtaExtFilled =ᶠ[𝓝 z] dirichletEtaExt := by
      have hopen : ({(1 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 z :=
        isOpen_compl_singleton.mem_nhds hne
      filter_upwards [hopen] with w (hw : w ∈ ({(1 : ℂ)}ᶜ : Set ℂ))
      have : w ≠ 1 := hw
      exact dirichletEtaExtFilled_eq_dirichletEtaExt_of_ne_one this
    rw [heq.differentiableAt_iff]
    exact dirichletEtaExt_differentiableAt hne
  have hc : ContinuousAt dirichletEtaExtFilled 1 :=
    continuousAt_dirichletEtaExtFilled_atOne
  exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
          hd hc).differentiableAt

/-! ## §6  Axiom check. -/

#print axioms hasDerivAt_oneMinusTwoCpow_oneSub_atOne
#print axioms tendsto_slopeFactor_atOne
#print axioms tendsto_dirichletEtaExt_atOne
#print axioms continuousAt_dirichletEtaExtFilled_atOne
#print axioms dirichletEtaExtFilled_differentiableAt_atOne

end PrincipiaTractalis.DirichletEtaExtDifferentiableAtOne_2026_11_17
