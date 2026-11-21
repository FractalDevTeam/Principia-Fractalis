/-
# The steady vorticity transport equation, derived from the momentum equation

**Date**: 2026-11-21 (Legion).

The four terms of the curl of the momentum equation are each already
proved in this directory:

| term | theorem | file |
|---|---|---|
| `curl(∇p) = 0` | `vorticity_gradient_eq_zero` | `…VorticityTransport…` |
| `curl(∂ₜu) = ∂ₜω` | `curl_commutes_with_dt` | `…Exchange…` |
| `curl(νΔu) = νΔω` | `curl_commutes_with_laplacian` | `…TransportDerivation…` |
| `curl((u·∇)u) = (u·∇)ω − (ω·∇)u + ω div u` | `curl_convective_identity` | `…ConvectiveIdentity…` |

What remained was assembly, and for the **steady** case it closes here
with no time-derivative bridge. This file derives

    `(u·∇)ω₃ = (ω·∇)u₃ + νΔω₃`

from the steady momentum equation `(u·∇)u + ∇p = νΔu` together with
`div u = 0`. The vorticity formulation is a **consequence**, not a
hypothesis.

## How the assembly works

The momentum equation must hold as an equality of *fields* for the curl
to be taken at all, since the curl differentiates. Given that, applying
the curl to both sides is `congrArg`. Splitting the left side needs only
additivity of the curl over fields (§1), and the right side its
commutation with scalar multiplication (§1); both come straight from
`fderiv_add` and `fderiv_const_smul`. The pressure then vanishes (§2),
the convective term supplies `(u·∇)ω − (ω·∇)u` plus `ω div u` which
incompressibility kills, and the viscous term passes through the
Laplacian exchange.

§4 discharges the three regularity side conditions from `C⁴` smoothness,
so the smooth form of the theorem carries no differentiability
hypotheses at all.

## §5 is the part that decides whether any of this is worth anything

A conditional theorem whose hypothesis cannot be met proves nothing, and
a conclusion that is a tautology proves nothing either. §5 settles both
with explicit witnesses:

* **`steadyMomentum_shear`** — plane Couette flow `u(y) = (y₂,0,0)` with
  zero pressure satisfies `SteadyMomentum` exactly, is divergence-free,
  and has `ω₃ = −1 ≠ 0`. So the hypothesis set is satisfiable, and
  satisfiable with *nonzero vorticity* rather than at a degenerate zero
  field.
* **`strainRot_not_steady`** — for the divergence-free strain-rotation
  field the conclusion is `0 = 4`, which is false. So the conclusion is
  not a tautology, the momentum hypothesis is load-bearing, and as a
  corollary that field is **not** a steady Navier-Stokes flow for any
  viscosity and any `C²` pressure.

The second witness is the same field whose strictly positive enstrophy
production (`strainRot_production_pos = 8`) makes geometric depletion a
substantive constraint rather than a vacuous one.

## Scope — stated plainly

Steady only. The unsteady equation needs in addition the slice/joint
bridge on the `∂ₜ` side, which is bookkeeping rather than mathematics.

**This is not a Navier-Stokes existence result and claims no part of the
Clay problem.** It is the vorticity formulation of the steady equations,
derived rather than postulated, plus two witnesses showing the
derivation is not vacuous.
-/

import PF.NavierStokes.Fefferman2000_Faithful_ConvectiveIdentity_2026_11_21
import PF.NavierStokes.Fefferman2000_Faithful_TransportDerivation_2026_11_21
import PF.NavierStokes.Fefferman2000_Faithful_VorticityTransport_2026_11_21
import PF.NavierStokes.Fefferman2000_Faithful_GeometricDepletion_2026_11_21
import PF.NavierStokes.Fefferman2000_Faithful_Slots_2026_11_21

namespace PF.NavierStokes.FeffermanFaithful

open InnerProductSpace

/-! ## §1 — The curl is linear over fields

`sVortCoord` is built from `sg`, a composite of `fderiv` with a
coordinate projection; both are linear, so the curl inherits additivity
and homogeneity from `fderiv`. The unfolding of the third component is
the existing `sVortCoord_two`. -/

/-- `sg` is additive in the field. `fderiv_add` is stated for the
    pointwise sum `u + w`, which is definitionally the lambda. -/
theorem sg_add (u w : V → V) (x : V) (j k : Fin 3)
    (hu : DifferentiableAt ℝ u x) (hw : DifferentiableAt ℝ w x) :
    sg (fun y => u y + w y) x j k = sg u x j k + sg w x j k := by
  have hfun : (fun y : V => u y + w y) = u + w := rfl
  unfold sg
  rw [hfun, fderiv_add hu hw]
  simp

/-- `sg` commutes with scalar multiplication of the field. -/
theorem sg_const_smul (c : ℝ) (u : V → V) (x : V) (j k : Fin 3)
    (hu : DifferentiableAt ℝ u x) :
    sg (fun y => c • u y) x j k = c * sg u x j k := by
  have hfun : (fun y : V => c • u y) = c • u := rfl
  unfold sg
  rw [hfun, fderiv_const_smul hu c]
  simp

/-- The third curl component is additive over fields. -/
theorem sVortCoord_two_add (u w : V → V) (x : V)
    (hu : DifferentiableAt ℝ u x) (hw : DifferentiableAt ℝ w x) :
    sVortCoord (fun y => u y + w y) x 2
      = sVortCoord u x 2 + sVortCoord w x 2 := by
  rw [sVortCoord_two, sVortCoord_two, sVortCoord_two,
      sg_add u w x 0 1 hu hw, sg_add u w x 1 0 hu hw]
  ring

/-- The third curl component commutes with scalar multiplication. -/
theorem sVortCoord_two_const_smul (c : ℝ) (u : V → V) (x : V)
    (hu : DifferentiableAt ℝ u x) :
    sVortCoord (fun y => c • u y) x 2 = c * sVortCoord u x 2 := by
  rw [sVortCoord_two, sVortCoord_two,
      sg_const_smul c u x 0 1 hu, sg_const_smul c u x 1 0 hu]
  ring

/-! ## §2 — The pressure drops out

Same content as `vorticity_gradient_eq_zero`, restated in the spatial
`sg`/`sVortCoord` language this file works in: the velocity gradient of
`∇p` is the second derivative `D²p`, symmetric for a `C²` function, and
the curl is its antisymmetric part. -/

/-- **The curl of a gradient vanishes.** -/
theorem sVortCoord_two_gradient (p : V → ℝ) (x : V) (hp : ContDiffAt ℝ 2 p x) :
    sVortCoord (fun y : V => gradient p y) x 2 = 0 := by
  have hsymm := hp.isSymmSndFDerivAt (by simp)
  have key : ∀ j k : Fin 3,
      sg (fun y : V => gradient p y) x j k
        = fderiv ℝ (fderiv ℝ p) x (EuclideanSpace.single j (1 : ℝ))
            (EuclideanSpace.single k (1 : ℝ)) := by
    intro j k
    calc sg (fun y : V => gradient p y) x j k
        = inner ℝ (fderiv ℝ (fun y : V => gradient p y) x
              (EuclideanSpace.single j (1 : ℝ)))
            (EuclideanSpace.single k (1 : ℝ)) := coord_eq_inner _ k
      _ = fderiv ℝ (fderiv ℝ p) x (EuclideanSpace.single j (1 : ℝ))
            (EuclideanSpace.single k (1 : ℝ)) := inner_fderiv_gradient p x _ _
  rw [sVortCoord_two, key 0 1, key 1 0,
      hsymm (EuclideanSpace.single 0 (1 : ℝ)) (EuclideanSpace.single 1 (1 : ℝ)),
      sub_self]

/-- `curl(Δu)` in the `sVortCoord` language is `sCurlOfLap` at the index
    pair `(0,1)`. Definitional. -/
theorem sVortCoord_two_laplacian (u : V → V) (x : V) :
    sVortCoord (fun y : V => InnerProductSpace.laplacian u y) x 2
      = sCurlOfLap u x 0 1 := by
  rw [sVortCoord_two]
  rfl

/-! ## §3 — The steady equations -/

/-- The steady momentum equation, as an identity of fields:
    `(u·∇)u + ∇p = νΔu`.

    It is stated as a field identity rather than pointwise because the
    vorticity equation is obtained by differentiating it; a pointwise
    hypothesis at a single point carries no derivative information. -/
def SteadyMomentum (ν : ℝ) (u : V → V) (p : V → ℝ) : Prop :=
  (fun y : V => sConv u y + gradient p y)
    = fun y : V => ν • InnerProductSpace.laplacian u y

/-- **★ THE STEADY VORTICITY TRANSPORT EQUATION, DERIVED.**

      `(u·∇)ω₃ = (ω·∇)u₃ + νΔω₃`

    from the steady momentum equation together with `div u = 0`. Every
    step is a proved theorem of this directory; nothing is postulated.

    The three `DifferentiableAt` hypotheses are side conditions, not
    assumptions about the flow: §4 discharges all three from smoothness.
    §5 shows the hypothesis set is satisfiable and the conclusion is not
    a tautology. -/
theorem steady_vorticity_transport (ν : ℝ) (u : V → V) (p : V → ℝ) (x : V)
    (hu : ContDiffAt ℝ 3 u x)
    (hp : ContDiffAt ℝ 2 p x)
    (hconv : DifferentiableAt ℝ (sConv u) x)
    (hgrad : DifferentiableAt ℝ (fun y : V => gradient p y) x)
    (hlap : DifferentiableAt ℝ (fun y : V => InnerProductSpace.laplacian u y) x)
    (hdiv : divergence u x = 0)
    (hmom : SteadyMomentum ν u p) :
    fderiv ℝ (fun y => sVortCoord u y 2) x (u x)
      = (fderiv ℝ u x (sVort u x)) 2 + ν * sLapOfCurl u x 0 1 := by
  -- Take the curl of both sides. The momentum equation is a field
  -- identity, so this is `congrArg`.
  have hcurl : sVortCoord (fun y : V => sConv u y + gradient p y) x 2
      = sVortCoord (fun y : V => ν • InnerProductSpace.laplacian u y) x 2 :=
    congrArg (fun f : V → V => sVortCoord f x 2) hmom
  -- Left side: split off the pressure, which then vanishes.
  have hL : sVortCoord (fun y : V => sConv u y + gradient p y) x 2
      = sVortCoord (sConv u) x 2
        + sVortCoord (fun y : V => gradient p y) x 2 :=
    sVortCoord_two_add (sConv u) (fun y : V => gradient p y) x hconv hgrad
  have hP : sVortCoord (fun y : V => gradient p y) x 2 = 0 :=
    sVortCoord_two_gradient p x hp
  -- The convective term, with incompressibility killing `ω div u`.
  have hC : sVortCoord (sConv u) x 2
      = fderiv ℝ (fun y => sVortCoord u y 2) x (u x)
        - (fderiv ℝ u x (sVort u x)) 2
        + sVortCoord u x 2 * divergence u x :=
    curl_convective_identity u x (hu.of_le (by norm_num))
  rw [hdiv, mul_zero, add_zero] at hC
  -- Right side: the scalar comes out, then the Laplacian exchange.
  have hR : sVortCoord (fun y : V => ν • InnerProductSpace.laplacian u y) x 2
      = ν * sLapOfCurl u x 0 1 := by
    rw [sVortCoord_two_const_smul ν _ x hlap, sVortCoord_two_laplacian u x,
        curl_commutes_with_laplacian u x hu 0 1]
  rw [hL, hP, add_zero, hC, hR] at hcurl
  linarith [hcurl]

/-! ## §4 — The regularity side conditions, discharged

None of the three differentiability hypotheses above is an assumption
about the flow: each follows from smoothness. This section proves them,
so the smooth form of the theorem has no side conditions. -/

/-- `(u·∇)u` is differentiable where `u` is `C²`. This is the
    differentiability half of `fderiv_sConv`. -/
theorem differentiableAt_sConv (u : V → V) (x : V) (hu : ContDiffAt ℝ 2 u x) :
    DifferentiableAt ℝ (sConv u) x := by
  have hc : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x :=
    (differentiableAt_fderiv_of_contDiffAt u x hu).hasFDerivAt
  have hU : HasFDerivAt u (fderiv ℝ u x) x :=
    (hu.differentiableAt (by norm_num)).hasFDerivAt
  show DifferentiableAt ℝ (fun y => fderiv ℝ u y (u y)) x
  exact (hc.clm_apply hU).differentiableAt

/-- `∇p` is differentiable where `p` is `C²`: the gradient is the Riesz
    image of `fderiv p`, and a continuous linear equivalence preserves
    differentiability. -/
theorem differentiableAt_gradient (p : V → ℝ) (x : V) (hp : ContDiffAt ℝ 2 p x) :
    DifferentiableAt ℝ (fun y : V => gradient p y) x := by
  have hfd : DifferentiableAt ℝ (fun y : V => fderiv ℝ p y) x :=
    (hp.fderiv_right (by norm_num)).differentiableAt (le_refl 1)
  have hg : (fun y : V => gradient p y)
      = (⇑(InnerProductSpace.toDual ℝ V).symm) ∘ (fun y : V => fderiv ℝ p y) := by
    funext y; rfl
  rw [hg]
  exact (InnerProductSpace.toDual ℝ V).symm.differentiableAt.comp x hfd

/-- `Δu` is differentiable where `u` is `C³`: the Laplacian is a finite
    sum of second partials, and the second-derivative map of a `C³`
    function is differentiable. -/
theorem differentiableAt_laplacian (u : V → V) (x : V) (hu : ContDiffAt ℝ 3 u x) :
    DifferentiableAt ℝ (fun y : V => InnerProductSpace.laplacian u y) x := by
  have hdF2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) x :=
    differentiableAt_fderiv_fderiv u x hu
  have hfun : (fun y : V => InnerProductSpace.laplacian u y)
      = fun y : V => ∑ i : Fin 3, fderiv ℝ (fderiv ℝ u) y
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) := by
    funext y; exact laplacian_eq_sum_second_partials u y
  rw [hfun]
  -- each summand is `D²u` evaluated at two fixed vectors; the
  -- operator-valued map must be given explicitly, since left as `_` the
  -- value type of `differentiableAt_eval` stays a metavariable
  have hterm : ∀ i : Fin 3, DifferentiableAt ℝ
      (fun y : V => fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))) x := by
    intro i
    have h1 : DifferentiableAt ℝ
        (fun y : V => fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i (1 : ℝ))) x :=
      differentiableAt_eval (fderiv ℝ (fderiv ℝ u)) x
        (EuclideanSpace.single i (1 : ℝ)) hdF2
    exact differentiableAt_eval
      (fun y : V => fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i (1 : ℝ))) x
      (EuclideanSpace.single i (1 : ℝ)) h1
  -- `DifferentiableAt.sum` is for a sum of functions; the lambda form is
  -- `fun_sum`
  exact DifferentiableAt.fun_sum (fun i _ => hterm i)

/-- **★ The steady vorticity transport equation for a smooth field, with
    no side conditions at all.**

      `(u·∇)ω₃ = (ω·∇)u₃ + νΔω₃`

    Hypotheses: `u` is `C⁴` at `x`, `p` is `C²` at `x`, `u` is
    divergence-free at `x`, and the steady momentum equation holds. That
    is the whole input. -/
theorem steady_vorticity_transport_of_contDiff (ν : ℝ) (u : V → V) (p : V → ℝ)
    (x : V)
    (hu : ContDiffAt ℝ 4 u x)
    (hp : ContDiffAt ℝ 2 p x)
    (hdiv : divergence u x = 0)
    (hmom : SteadyMomentum ν u p) :
    fderiv ℝ (fun y => sVortCoord u y 2) x (u x)
      = (fderiv ℝ u x (sVort u x)) 2 + ν * sLapOfCurl u x 0 1 :=
  steady_vorticity_transport ν u p x
    (hu.of_le (by norm_num)) hp
    (differentiableAt_sConv u x (hu.of_le (by norm_num)))
    (differentiableAt_gradient p x hp)
    (differentiableAt_laplacian u x (hu.of_le (by norm_num)))
    hdiv hmom

/-! ## §5 — The two witnesses

Everything above is a conditional. This section shows the condition can
be met, and that the conclusion is not a tautology. Without both, the
theorem would be worth nothing. -/

/-- The Laplacian of a real-valued constant function vanishes. The
    existing `laplacian_const_fun` is for a `V`-valued constant; the
    curl components are real-valued, so this is the scalar case. -/
theorem laplacian_const_scalar (c : ℝ) (x : V) :
    InnerProductSpace.laplacian (fun _ : V => c) x = 0 := by
  rw [laplacian_eq_sum_second_partials]
  simp

/-! ### Witness A — plane Couette flow satisfies the hypotheses

`u(y) = (y₂, 0, 0)`, zero pressure. An exact steady Navier-Stokes
solution: the convective term vanishes because `u` points along `e₁`
while varying only in `y₂`, and the Laplacian vanishes because `u` is
linear. -/

/-- The shear field as a spatial (steady) velocity field. -/
noncomputable def shearSpatial : V → V := fun y => shearCLM y

@[simp] theorem fderiv_shearSpatial (x : V) :
    fderiv ℝ shearSpatial x = shearCLM := by
  unfold shearSpatial
  simp

theorem contDiff_shearSpatial {n : WithTop ℕ∞} : ContDiff ℝ n shearSpatial :=
  shearCLM.contDiff

/-- The shear field is divergence-free. -/
theorem shearSpatial_divFree (x : V) : divergence shearSpatial x = 0 := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  unfold divergence
  rw [Fin.sum_univ_three, fderiv_shearSpatial]
  simp [shearCLM_apply, h10, h20, EuclideanSpace.single_apply]

/-- **The convective term vanishes on the shear field.** `u` points
    along `e₁` and `shearCLM` reads the `e₂` coordinate, which is zero
    on the image. -/
theorem sConv_shearSpatial (y : V) : sConv shearSpatial y = 0 := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  show fderiv ℝ shearSpatial y (shearSpatial y) = 0
  rw [fderiv_shearSpatial]
  ext k
  simp [shearSpatial, shearCLM_apply, h10]

/-- **The Laplacian vanishes on the shear field**, which is linear, so
    its derivative is constant and its second derivative zero. -/
theorem laplacian_shearSpatial (x : V) :
    InnerProductSpace.laplacian shearSpatial x = 0 := by
  have hc : fderiv ℝ shearSpatial = fun _ : V => shearCLM := by
    funext y; exact fderiv_shearSpatial y
  rw [laplacian_eq_sum_second_partials, hc]
  simp

/-- The gradient of the zero pressure vanishes. -/
theorem gradient_zero_fun (y : V) :
    gradient (fun _ : V => (0 : ℝ)) y = 0 := by
  simp [gradient]

/-- **★ WITNESS A: the hypothesis set of the transport theorem is
    satisfiable.** Plane Couette flow with zero pressure satisfies the
    steady momentum equation exactly, for every viscosity. -/
theorem steadyMomentum_shear (ν : ℝ) :
    SteadyMomentum ν shearSpatial (fun _ : V => (0 : ℝ)) := by
  unfold SteadyMomentum
  funext y
  rw [sConv_shearSpatial y, gradient_zero_fun y, laplacian_shearSpatial y]
  simp

/-- **★ …and satisfiable with nonzero vorticity**, so the witness is not
    a degenerate zero field: `ω₃ = −1`. -/
theorem shearSpatial_vort_two (x : V) : sVortCoord shearSpatial x 2 = -1 := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  rw [sVortCoord_two]
  unfold sg
  rw [fderiv_shearSpatial]
  simp [shearCLM_apply, h10, EuclideanSpace.single_apply]

/-- The hypotheses of the smooth transport theorem are jointly
    satisfiable, with nonzero vorticity. This is the statement that
    `steady_vorticity_transport_of_contDiff` is not vacuous. -/
theorem steady_hypotheses_satisfiable (ν : ℝ) :
    ∃ u : V → V, ∃ p : V → ℝ,
      ContDiffAt ℝ 4 u 0 ∧ ContDiffAt ℝ 2 p 0 ∧
      divergence u 0 = 0 ∧ SteadyMomentum ν u p ∧
      sVortCoord u 0 2 ≠ 0 :=
  ⟨shearSpatial, fun _ => (0 : ℝ),
   contDiff_shearSpatial.contDiffAt, contDiffAt_const,
   shearSpatial_divFree 0, steadyMomentum_shear ν, by
     rw [shearSpatial_vort_two]; norm_num⟩

/-! ### Witness B — the conclusion is not a tautology

For the divergence-free strain-rotation field the conclusion reads
`0 = 4`. Its vorticity `2e₃` lies along the stretching axis, so the
stretching term is nonzero while the transport term vanishes (the
vorticity is constant). Hence that field cannot satisfy the momentum
equation — the hypothesis is doing real work. -/

theorem contDiff_strainRot {n : WithTop ℕ∞} : ContDiff ℝ n strainRot :=
  strainRotCLM.contDiff

/-- `ω₃ = 2` for the strain-rotation field. -/
theorem strainRot_vort_two (x : V) : sVortCoord strainRot x 2 = 2 := by
  obtain ⟨_, h01, _, h10, _, _, _, _, _⟩ := strainRot_entries x
  rw [sVortCoord_two, h01, h10]
  norm_num

/-- The vorticity is constant, so the transport term vanishes. -/
theorem strainRot_transport_zero (x : V) :
    fderiv ℝ (fun y => sVortCoord strainRot y 2) x (strainRot x) = 0 := by
  have hconst : (fun y : V => sVortCoord strainRot y 2) = fun _ : V => (2 : ℝ) := by
    funext y; exact strainRot_vort_two y
  rw [hconst]
  simp

/-- The viscous term vanishes: the curl is constant, so its Laplacian
    is zero. -/
theorem strainRot_sLapOfCurl (x : V) : sLapOfCurl strainRot x 0 1 = 0 := by
  have hc : (fun y : V =>
      (fderiv ℝ strainRot y (EuclideanSpace.single 0 (1 : ℝ))) 1
        - (fderiv ℝ strainRot y (EuclideanSpace.single 1 (1 : ℝ))) 0)
      = fun _ : V => (1 : ℝ) - (-1 : ℝ) := by
    funext y
    obtain ⟨_, h01, _, h10, _, _, _, _, _⟩ := strainRot_entries y
    show sg strainRot y 0 1 - sg strainRot y 1 0 = (1 : ℝ) - (-1 : ℝ)
    rw [h01, h10]
  unfold sLapOfCurl
  rw [hc]
  exact laplacian_const_scalar _ x

/-- **The stretching term is `4`** — nonzero, because the vorticity
    `2e₃` lies along the stretching axis of the strain. -/
theorem strainRot_stretching (x : V) :
    (fderiv ℝ strainRot x (sVort strainRot x)) 2 = 4 := by
  obtain ⟨_, _, _, _, _, _, _, _, h22⟩ := strainRot_entries x
  have h : (strainRotCLM (EuclideanSpace.single 2 (1 : ℝ))) 2 = 2 := by
    rw [← sg_strainRot x 2 2]; exact h22
  rw [strainRot_vort, fderiv_strainRot, map_smul]
  simp [h]
  norm_num

/-- **★ WITNESS B: the strain-rotation field is not a steady
    Navier-Stokes flow**, for any viscosity and any `C²` pressure.

    Proved *by* the transport theorem: the field is smooth and
    divergence-free, so if it satisfied the momentum equation the
    transport equation would give `0 = 4`.

    The `C²` hypothesis on `p` is the Fefferman regularity class for a
    pressure, and it is what makes the curl of `∇p` vanish; nothing
    weaker would let the pressure be eliminated. -/
theorem strainRot_not_steady (ν : ℝ) (p : V → ℝ) (hp : ContDiffAt ℝ 2 p 0) :
    ¬ SteadyMomentum ν strainRot p := by
  intro hmom
  have h := steady_vorticity_transport_of_contDiff ν strainRot p 0
    contDiff_strainRot.contDiffAt hp (strainRot_divFree 0) hmom
  rw [strainRot_transport_zero 0, strainRot_stretching 0,
      strainRot_sLapOfCurl 0] at h
  norm_num at h

/-- **★ The conclusion of the transport theorem is not a tautology.**
    There is a smooth divergence-free field for which it fails — so the
    momentum hypothesis is load-bearing and the theorem has content. -/
theorem transport_conclusion_not_tautological (ν : ℝ) :
    ∃ u : V → V, ContDiff ℝ (4 : ℕ) u ∧ divergence u 0 = 0 ∧
      fderiv ℝ (fun y => sVortCoord u y 2) 0 (u 0)
        ≠ (fderiv ℝ u 0 (sVort u 0)) 2 + ν * sLapOfCurl u 0 0 1 :=
  ⟨strainRot, contDiff_strainRot, strainRot_divFree 0, by
    rw [strainRot_transport_zero 0, strainRot_stretching 0,
        strainRot_sLapOfCurl 0]
    norm_num⟩

#print axioms sg_add
#print axioms sVortCoord_two_add
#print axioms sVortCoord_two_const_smul
#print axioms sVortCoord_two_gradient
#print axioms sVortCoord_two_laplacian
#print axioms steady_vorticity_transport
#print axioms differentiableAt_sConv
#print axioms differentiableAt_gradient
#print axioms differentiableAt_laplacian
#print axioms steady_vorticity_transport_of_contDiff
#print axioms laplacian_const_scalar
#print axioms sConv_shearSpatial
#print axioms laplacian_shearSpatial
#print axioms steadyMomentum_shear
#print axioms shearSpatial_vort_two
#print axioms steady_hypotheses_satisfiable
#print axioms strainRot_vort_two
#print axioms strainRot_transport_zero
#print axioms strainRot_sLapOfCurl
#print axioms strainRot_stretching
#print axioms strainRot_not_steady
#print axioms transport_conclusion_not_tautological

end PF.NavierStokes.FeffermanFaithful
