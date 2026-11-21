/-
# The vorticity transport equation, and the first analytic step toward slot 3

**Date**: 2026-11-21 (Legion).

Taking the curl of the momentum equation turns Navier-Stokes into

    ∂ₜω + (u·∇)ω = (ω·∇)u + νΔω

and this is the form in which the 3D regularity problem is actually
attacked. Three things make it the useful form:

* the pressure disappears, because the curl of a gradient vanishes;
* the only nonlinearity left is the stretching term `(ω·∇)u`;
* pairing against `ω` turns it into a differential inequality for
  `‖ω‖`, which is exactly the Beale-Kato-Majda input.

This file states the equation faithfully and proves the parts that are
provable at this pin, including the pairing step.

## What is proved

* `vorticity_eq_zero_of_gradComp_symm` — a velocity field whose spatial
  gradient is symmetric is irrotational. This is the precise sense in
  which vorticity *is* the antisymmetric part of `∇u`.
* `vorticity_gradient_eq_zero` — **the curl of a gradient vanishes**, for
  any `C²` potential. This is why the pressure drops out of the momentum
  equation under the curl, and so why the vorticity formulation exists.
  Proved the classical way: the velocity gradient of `∇P` is the second
  derivative `D²P` (`gradComp_gradient`, via the Riesz isomorphism in
  `inner_fderiv_gradient`), which is symmetric for `C²` functions
  (`ContDiffAt.isSymmSndFDerivAt`).
* `enstrophy_production_le` — `⟪ω, (ω·∇)u⟫ ≤ ‖∇u‖‖ω‖²`. The enstrophy
  production is controlled by the velocity gradient. Cauchy-Schwarz plus
  the operator-norm bound.
* `enstrophy_rate_le_of_transport` — **the payoff.** Given the transport
  equation at a point and a bound `‖∇u‖ ≤ G` there, the paired rate
  `⟪ω, ∂ₜω + (u·∇)ω − νΔω⟫` is at most `G‖ω‖²`. This is the Grönwall
  input: it is how a velocity-gradient bound becomes a bound on
  vorticity growth, which by BKM is what rules out blow-up.

## What is NOT proved

`VorticityTransportAt` itself. It is a **classical identity** of vector
calculus — not an open problem — but deriving it inside Lean needs the
curl to commute with `Δ` and with `∂ₜ`, i.e. derivative-exchange lemmas
for jointly-`C^∞` fields. The faithful solution class supplies that
smoothness; the exchange lemmas are a formalisation task, not a
mathematical gap. It is stated here as a named hypothesis with that
status, exactly as slots 1 and 2 are in
`Fefferman2000_Faithful_Slots_2026_11_21.lean`.

**Nothing here proves Navier-Stokes.** What it does is make the chain
`‖∇u‖ bounded → enstrophy growth bounded → no blow-up → Clay` explicit
and machine-checked at the one step that is pure estimate.
-/

import PF.NavierStokes.Fefferman2000_Faithful_Slots_2026_11_21
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace PF.NavierStokes.FeffermanFaithful

/-! ## §1 — Vorticity is the antisymmetric part of the velocity gradient -/

/-- **A field with symmetric velocity gradient is irrotational.**

    Each vorticity component is a difference `∂ⱼuₖ − ∂ₖuⱼ`, so symmetry
    of `gradComp` kills all three. Pure algebra — the analytic input is
    isolated in the hypothesis, which is where it belongs. -/
theorem vorticity_eq_zero_of_gradComp_symm (U : V × ℝ → V) (t : ℝ) (x : V)
    (h : ∀ j k : Fin 3, gradComp U t x j k = gradComp U t x k j) :
    vorticity U t x = 0 := by
  rw [eq_zero_iff_coords]
  intro i
  rw [vorticity_apply]
  unfold vorticityCoord vort1 vort2 vort3
  by_cases h0 : i = 0
  · simp [h0, h 1 2, sub_self]
  · by_cases h1 : i = 1
    · simp [h1, h 2 0, sub_self]
    · simp [h0, h1, h 0 1, sub_self]

/-- The coordinate of a vector is its inner product against the
    corresponding basis vector. -/
theorem coord_eq_inner (w : V) (k : Fin 3) :
    w k = inner ℝ w (EuclideanSpace.single k (1 : ℝ)) := by
  simp [EuclideanSpace.inner_single_right]

/-- A gradient's directional derivative, in inner-product form: this is
    the Riesz characterisation `⟪∇P, v⟫ = DP v`. -/
theorem inner_gradient (P : V → ℝ) (x v : V) :
    inner ℝ (gradient P x) v = fderiv ℝ P x v := by
  unfold gradient
  exact InnerProductSpace.toDual_symm_apply

/-- **A gradient field's velocity gradient is the second derivative.**

    `∇P = (toDual)⁻¹ ∘ DP`, and `(toDual)⁻¹` is a continuous linear
    equivalence, so differentiating commutes with it; pairing against
    `w` then undoes the Riesz isomorphism. Unconditional — if `DP` is
    not differentiable at `x` both sides are `0`. -/
theorem inner_fderiv_gradient (P : V → ℝ) (x v w : V) :
    inner ℝ (fderiv ℝ (fun y : V => gradient P y) x v) w
      = fderiv ℝ (fderiv ℝ P) x v w := by
  have hg : (fun y : V => gradient P y)
      = (⇑(InnerProductSpace.toDual ℝ V).symm) ∘ (fun y : V => fderiv ℝ P y) := by
    funext y; rfl
  rw [hg, (InnerProductSpace.toDual ℝ V).symm.comp_fderiv]
  exact InnerProductSpace.toDual_symm_apply

/-- `gradComp` of a gradient field, in coordinates: `∂ⱼ(∇P)ₖ = D²P eⱼ eₖ`. -/
theorem gradComp_gradient (P : V → ℝ) (t : ℝ) (x : V) (j k : Fin 3) :
    gradComp (fun q : V × ℝ => gradient P q.1) t x j k
      = fderiv ℝ (fderiv ℝ P) x (EuclideanSpace.single j (1 : ℝ))
          (EuclideanSpace.single k (1 : ℝ)) := by
  calc gradComp (fun q : V × ℝ => gradient P q.1) t x j k
      = inner ℝ (fderiv ℝ (fun y : V => gradient P y) x
            (EuclideanSpace.single j (1 : ℝ))) (EuclideanSpace.single k (1 : ℝ)) :=
        coord_eq_inner _ k
    _ = fderiv ℝ (fderiv ℝ P) x (EuclideanSpace.single j (1 : ℝ))
          (EuclideanSpace.single k (1 : ℝ)) :=
        inner_fderiv_gradient P x _ _

/-- **★ The curl of a gradient vanishes.**

    This is why the pressure disappears when the curl is applied to the
    momentum equation, and hence why the vorticity formulation exists at
    all. The proof is exactly the classical one: the velocity gradient
    of `∇P` is the second derivative `D²P`, which is symmetric for a
    `C²` function (`ContDiffAt.isSymmSndFDerivAt`), and vorticity is the
    antisymmetric part. -/
theorem vorticity_gradient_eq_zero (P : V → ℝ) (t : ℝ) (x : V)
    (hP : ContDiffAt ℝ 2 P x) :
    vorticity (fun q : V × ℝ => gradient P q.1) t x = 0 := by
  refine vorticity_eq_zero_of_gradComp_symm _ t x (fun j k => ?_)
  rw [gradComp_gradient, gradComp_gradient]
  exact hP.isSymmSndFDerivAt (by simp) _ _

/-! ## §2 — The transport equation

The three differential operators acting on the vorticity field, each
built from genuine mathlib primitives, and then the equation itself. -/

/-- `∂ₜω` — the time derivative of the vorticity at a fixed point. -/
noncomputable def vorticityDt (U : V × ℝ → V) (t : ℝ) (x : V) : V :=
  deriv (fun s : ℝ => vorticity U s x) t

/-- `(u·∇)ω` — the convective transport of vorticity by the flow: the
    spatial derivative of `ω` in the direction `u`. -/
noncomputable def vorticityConv (U : V × ℝ → V) (t : ℝ) (x : V) : V :=
  fderiv ℝ (fun y : V => vorticity U t y) x (U (x, t))

/-- `Δω` — the vorticity Laplacian, mathlib's genuine Laplacian. -/
noncomputable def vorticityLap (U : V × ℝ → V) (t : ℝ) (x : V) : V :=
  InnerProductSpace.laplacian (fun y : V => vorticity U t y) x

/-- **The vorticity transport equation at a point**:

      `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω`

    obtained by taking the curl of the momentum equation. The pressure
    is absent because the curl of a gradient vanishes (§1).

    **Classical identity, not an open problem.** It is stated as a named
    hypothesis because deriving it in Lean needs the curl to commute
    with `Δ` and with `∂ₜ` — derivative-exchange lemmas for jointly
    `C^∞` fields. That is formalisation work, not mathematics. -/
def VorticityTransportAt (U : V × ℝ → V) (ν : ℝ) (t : ℝ) (x : V) : Prop :=
  vorticityDt U t x + vorticityConv U t x
    = vortexStretchingFaithful U t x + ν • vorticityLap U t x

/-- The transport equation holding throughout the space-time half-space,
    for a given viscosity. -/
def VorticityTransport (U : V × ℝ → V) (ν : ℝ) : Prop :=
  ∀ (x : V) (t : ℝ), 0 ≤ t → VorticityTransportAt U ν t x

/-! ## §3 — Pairing against ω: the Beale-Kato-Majda input -/

/-- **Enstrophy production is controlled by the velocity gradient**:

      `⟪ω, (ω·∇)u⟫ ≤ ‖∇u‖ ‖ω‖²`

    Cauchy-Schwarz, then the operator-norm bound on the stretching term.
    This is the quantity whose control is the whole content of 3D
    regularity. -/
theorem enstrophy_production_le (U : V × ℝ → V) (t : ℝ) (x : V) :
    inner ℝ (vorticity U t x) (vortexStretchingFaithful U t x)
      ≤ ‖fderiv ℝ (fun y : V => U (y, t)) x‖ * ‖vorticity U t x‖ ^ 2 := by
  calc inner ℝ (vorticity U t x) (vortexStretchingFaithful U t x)
      ≤ ‖vorticity U t x‖ * ‖vortexStretchingFaithful U t x‖ :=
        real_inner_le_norm _ _
    _ ≤ ‖vorticity U t x‖ *
          (‖fderiv ℝ (fun y : V => U (y, t)) x‖ * ‖vorticity U t x‖) :=
        mul_le_mul_of_nonneg_left (norm_vortexStretchingFaithful_le U t x)
          (norm_nonneg _)
    _ = ‖fderiv ℝ (fun y : V => U (y, t)) x‖ * ‖vorticity U t x‖ ^ 2 := by
        ring

/-- **★ The Grönwall input.**

    Given the transport equation at a point, and a bound `‖∇u‖ ≤ G`
    there, the paired vorticity rate obeys

      `⟪ω, ∂ₜω + (u·∇)ω − νΔω⟫ ≤ G‖ω‖²`.

    This is precisely how a velocity-gradient bound becomes a bound on
    the growth of `‖ω‖`: integrating such an inequality in time is the
    Grönwall step, and finiteness of `∫‖ω‖_∞` is Beale-Kato-Majda's
    no-blow-up criterion. So this theorem is the one pure-estimate link
    in the chain `‖∇u‖ bounded → no blow-up → Clay`.

    The transport equation is a hypothesis; the estimate is proved. -/
theorem enstrophy_rate_le_of_transport
    (U : V × ℝ → V) (ν G : ℝ) (t : ℝ) (x : V)
    (htr : VorticityTransportAt U ν t x)
    (hG : ‖fderiv ℝ (fun y : V => U (y, t)) x‖ ≤ G) :
    inner ℝ (vorticity U t x)
        (vorticityDt U t x + vorticityConv U t x - ν • vorticityLap U t x)
      ≤ G * ‖vorticity U t x‖ ^ 2 := by
  have hrw : vorticityDt U t x + vorticityConv U t x - ν • vorticityLap U t x
      = vortexStretchingFaithful U t x := by
    unfold VorticityTransportAt at htr
    rw [htr]
    abel
  rw [hrw]
  calc inner ℝ (vorticity U t x) (vortexStretchingFaithful U t x)
      ≤ ‖fderiv ℝ (fun y : V => U (y, t)) x‖ * ‖vorticity U t x‖ ^ 2 :=
        enstrophy_production_le U t x
    _ ≤ G * ‖vorticity U t x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hG (sq_nonneg _)

/-- Irrotational flow has zero enstrophy production — the degenerate
    case, and a sanity check that the production functional is not
    measuring something spurious. -/
@[simp] theorem enstrophy_production_of_vorticity_zero
    (U : V × ℝ → V) (t : ℝ) (x : V) (h : vorticity U t x = 0) :
    inner ℝ (vorticity U t x) (vortexStretchingFaithful U t x) = 0 := by
  rw [h, inner_zero_left]

/-! ## §4 — Where this leaves the 3D axis

Chain, with each link's status:

| link | status |
|---|---|
| `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω` | classical; `VorticityTransportAt`, hypothesis |
| `⟪ω, (ω·∇)u⟫ ≤ ‖∇u‖‖ω‖²` | **PROVED** (`enstrophy_production_le`) |
| `‖∇u‖ ≤ G ⇒ paired rate ≤ G‖ω‖²` | **PROVED** (`enstrophy_rate_le_of_transport`) |
| Grönwall: rate bound ⇒ `‖ω(t)‖` bound | classical; needs ODE comparison |
| `∫‖ω‖_∞ < ∞ ⇒` no blow-up | classical; BKM, slot 2 |
| uniform-in-`T` vorticity bound | **OPEN**; slot 3 = `NoBlowup3D` |

The open link is unchanged and remains the only one: a bound on `‖∇u‖`
uniform in time. What this file adds is that the step *from* such a
bound *to* control of vorticity growth is now machine-checked rather
than asserted.
-/

#print axioms vorticity_eq_zero_of_gradComp_symm
#print axioms inner_gradient
#print axioms inner_fderiv_gradient
#print axioms gradComp_gradient
#print axioms vorticity_gradient_eq_zero
#print axioms enstrophy_production_le
#print axioms enstrophy_rate_le_of_transport

end PF.NavierStokes.FeffermanFaithful
