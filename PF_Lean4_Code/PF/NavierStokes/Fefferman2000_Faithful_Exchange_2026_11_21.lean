/-
# Exchange lemmas: curl past the time derivative

**Date**: 2026-11-21 (Legion).

`Fefferman2000_Faithful_VorticityTransport_2026_11_21.lean` states the
vorticity transport equation as a hypothesis, because deriving it needs
the curl to commute with `∂ₜ` and with `Δ`. This file proves the first of
those and says exactly what is missing for the second.

## What the derivation needs, and where each piece stands

Applying the curl to `∂ₜu + (u·∇)u + ∇p = νΔu`:

| term | needs | status |
|---|---|---|
| `curl(∇p) = 0` | 2nd-order symmetry | **PROVED** (transport file) |
| `curl(∂ₜu) = ∂ₜω` | space-time mixed partials commute | **PROVED HERE** |
| `curl(νΔu) = νΔω` | 3rd-order symmetry | NOT done — see §4 |
| `curl((u·∇)u) = (u·∇)ω − (ω·∇)u` | 2nd-order symmetry + `div u = 0` | NOT done — see §4 |

## The method

The partial derivatives that `gradComp` and `vorticityDt` use are taken
on *slices* — `fderiv (fun y => U (y,t)) x` and
`deriv (fun s => U (x,s)) t`. Symmetry of the second derivative is a fact
about the **joint** map `U : V × ℝ → V`. So §1 bridges the two: a slice
partial is the joint derivative composed with the corresponding
inclusion (`ContinuousLinearMap.inl` / `inr`).

Once both partials are expressed jointly, `∂ₜ∂ⱼ = ∂ⱼ∂ₜ` is literally
`IsSymmSndFDerivAt` applied at the directions `(eⱼ, 0)` and `(0, 1)` —
no analysis beyond what mathlib already has, which is the point: the
exchange is not a separate theorem, it is the second-derivative symmetry
of the space-time map read in two particular directions.

**Nothing here proves Navier-Stokes.** It removes one hypothesis from the
transport equation's derivation.
-/

import PF.NavierStokes.Fefferman2000_Faithful_VorticityTransport_2026_11_21
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace PF.NavierStokes.FeffermanFaithful

/-! ## §1 — Slice partials are joint partials

A spatial partial derivative of the time-`t` slice, and the time
derivative at fixed `x`, are both the joint Fréchet derivative composed
with an inclusion. These two lemmas are what let a statement about
slices be proved by a fact about the joint map. -/

/-- The time-`t` slice inclusion `y ↦ (y,t)` has derivative `inl`. -/
theorem fderiv_sliceSpace (t : ℝ) (x : V) :
    fderiv ℝ (fun y : V => ((y, t) : V × ℝ)) x = ContinuousLinearMap.inl ℝ V ℝ :=
  ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)).fderiv

/-- The point-`x` slice inclusion `s ↦ (x,s)` has derivative `inr`. -/
theorem fderiv_sliceTime (x : V) (t : ℝ) :
    fderiv ℝ (fun s : ℝ => ((x, s) : V × ℝ)) t = ContinuousLinearMap.inr ℝ V ℝ :=
  ((hasFDerivAt_const x t).prodMk (hasFDerivAt_id t)).fderiv

/-- **Spatial slice partial = joint derivative in a space direction.** -/
theorem fderiv_slice_eq_joint (U : V × ℝ → V) (x : V) (t : ℝ) (v : V)
    (h : DifferentiableAt ℝ U (x, t)) :
    fderiv ℝ (fun y : V => U (y, t)) x v = fderiv ℝ U (x, t) (v, 0) := by
  have hi : HasFDerivAt (fun y : V => ((y, t) : V × ℝ))
      (ContinuousLinearMap.inl ℝ V ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  have hcomp : HasFDerivAt (fun y : V => U (y, t))
      ((fderiv ℝ U (x, t)).comp (ContinuousLinearMap.inl ℝ V ℝ)) x :=
    h.hasFDerivAt.comp x hi
  rw [hcomp.fderiv]
  rfl

/-- **Time slice partial = joint derivative in the time direction.** -/
theorem deriv_slice_eq_joint (U : V × ℝ → V) (x : V) (t : ℝ)
    (h : DifferentiableAt ℝ U (x, t)) :
    deriv (fun s : ℝ => U (x, s)) t = fderiv ℝ U (x, t) (0, 1) := by
  have hi : HasFDerivAt (fun s : ℝ => ((x, s) : V × ℝ))
      (ContinuousLinearMap.inr ℝ V ℝ) t :=
    (hasFDerivAt_const x t).prodMk (hasFDerivAt_id t)
  have hcomp : HasFDerivAt (fun s : ℝ => U (x, s))
      ((fderiv ℝ U (x, t)).comp (ContinuousLinearMap.inr ℝ V ℝ)) t :=
    h.hasFDerivAt.comp t hi
  rw [hcomp.hasDerivAt.deriv]
  rfl

/-- `gradComp` in joint form. -/
theorem gradComp_eq_joint (U : V × ℝ → V) (t : ℝ) (x : V) (j k : Fin 3)
    (h : DifferentiableAt ℝ U (x, t)) :
    gradComp U t x j k
      = (fderiv ℝ U (x, t) (EuclideanSpace.single j (1 : ℝ), 0)) k := by
  unfold gradComp
  rw [fderiv_slice_eq_joint U x t _ h]

/-! ## §2 — Space-time directions and joint second partials -/

/-- The `j`-th space direction in space-time. -/
noncomputable def spaceDir (j : Fin 3) : V × ℝ :=
  (EuclideanSpace.single j (1 : ℝ), 0)

/-- The time direction in space-time. -/
def timeDir : V × ℝ := (0, 1)

/-- The joint second derivative of the space-time field, in two
    directions: `D²U q v w`. Taking `v` and `w` from `spaceDir`/`timeDir`
    picks out the mixed partials. -/
noncomputable def jSnd (U : V × ℝ → V) (q : V × ℝ) (v w : V × ℝ) : V :=
  fderiv ℝ (fderiv ℝ U) q v w

/-! ## §3 — The exchange -/

/-- **Space-time mixed partials commute**: `∂ₜ∂ⱼuₖ = ∂ⱼ∂ₜuₖ`.

    This is `IsSymmSndFDerivAt` for the joint map, read at the directions
    `(eⱼ,0)` and `(0,1)`. No new analysis — the content is that the
    exchange of a spatial and a temporal derivative is an instance of
    second-derivative symmetry on space-time, not a separate fact. -/
theorem mixed_partial_exchange (U : V × ℝ → V) (q : V × ℝ)
    (hU : ContDiffAt ℝ 2 U q) (v w : V × ℝ) :
    jSnd U q v w = jSnd U q w v :=
  hU.isSymmSndFDerivAt (by simp) v w

/-- Componentwise form of the exchange. -/
theorem mixed_partial_exchange_apply (U : V × ℝ → V) (q : V × ℝ)
    (hU : ContDiffAt ℝ 2 U q) (v w : V × ℝ) (k : Fin 3) :
    (jSnd U q v w) k = (jSnd U q w v) k := by
  rw [mixed_partial_exchange U q hU v w]

/-! ### The curl of `∂ₜu` equals `∂ₜ` of the curl

Each vorticity component is an antisymmetric difference `∂ⱼuₖ − ∂ₖuⱼ`.
Writing the curl of the time derivative and the time derivative of the
curl in joint second-partial form, the two differ only by the order of
the two derivative slots — which §3 says is immaterial. -/

/-- `(curl ∂ₜu)₁ = ∂₂(∂ₜu)₃ − ∂₃(∂ₜu)₂`, in joint form. -/
noncomputable def curlOfDt1 (U : V × ℝ → V) (q : V × ℝ) : ℝ :=
  (jSnd U q (spaceDir 1) timeDir) 2 - (jSnd U q (spaceDir 2) timeDir) 1

/-- `(∂ₜ curl u)₁ = ∂ₜ(∂₂u₃ − ∂₃u₂)`, in joint form. -/
noncomputable def dtOfCurl1 (U : V × ℝ → V) (q : V × ℝ) : ℝ :=
  (jSnd U q timeDir (spaceDir 1)) 2 - (jSnd U q timeDir (spaceDir 2)) 1

/-- `(curl ∂ₜu)₂`, in joint form. -/
noncomputable def curlOfDt2 (U : V × ℝ → V) (q : V × ℝ) : ℝ :=
  (jSnd U q (spaceDir 2) timeDir) 0 - (jSnd U q (spaceDir 0) timeDir) 2

/-- `(∂ₜ curl u)₂`, in joint form. -/
noncomputable def dtOfCurl2 (U : V × ℝ → V) (q : V × ℝ) : ℝ :=
  (jSnd U q timeDir (spaceDir 2)) 0 - (jSnd U q timeDir (spaceDir 0)) 2

/-- `(curl ∂ₜu)₃`, in joint form. -/
noncomputable def curlOfDt3 (U : V × ℝ → V) (q : V × ℝ) : ℝ :=
  (jSnd U q (spaceDir 0) timeDir) 1 - (jSnd U q (spaceDir 1) timeDir) 0

/-- `(∂ₜ curl u)₃`, in joint form. -/
noncomputable def dtOfCurl3 (U : V × ℝ → V) (q : V × ℝ) : ℝ :=
  (jSnd U q timeDir (spaceDir 0)) 1 - (jSnd U q timeDir (spaceDir 1)) 0

/-- **★ THE EXCHANGE LEMMA: curl commutes with `∂ₜ`.**

    All three components of `curl(∂ₜu)` agree with those of `∂ₜ(curl u)`,
    for any jointly `C²` space-time velocity field.

    This discharges one of the two hypotheses the transport equation's
    derivation rests on. The pressure term was already handled
    (`vorticity_gradient_eq_zero`); what remains is the Laplacian
    exchange and the convective identity, both in §4. -/
theorem curl_commutes_with_dt (U : V × ℝ → V) (q : V × ℝ)
    (hU : ContDiffAt ℝ 2 U q) :
    curlOfDt1 U q = dtOfCurl1 U q ∧
    curlOfDt2 U q = dtOfCurl2 U q ∧
    curlOfDt3 U q = dtOfCurl3 U q := by
  refine ⟨?_, ?_, ?_⟩
  · unfold curlOfDt1 dtOfCurl1
    rw [mixed_partial_exchange_apply U q hU (spaceDir 1) timeDir,
        mixed_partial_exchange_apply U q hU (spaceDir 2) timeDir]
  · unfold curlOfDt2 dtOfCurl2
    rw [mixed_partial_exchange_apply U q hU (spaceDir 2) timeDir,
        mixed_partial_exchange_apply U q hU (spaceDir 0) timeDir]
  · unfold curlOfDt3 dtOfCurl3
    rw [mixed_partial_exchange_apply U q hU (spaceDir 0) timeDir,
        mixed_partial_exchange_apply U q hU (spaceDir 1) timeDir]

/-! ## §4 — What is still missing, precisely

### One bridge remains on the `∂ₜ` side

`curl_commutes_with_dt` is stated through the joint second partials
`jSnd`, which is where the content lives. The transport equation's
`vorticityDt` is instead defined on slices, as
`deriv (fun s => vorticity U s x) t`. Connecting them needs

    `deriv (fun s => gradComp U s x j k) t = (jSnd U (x,t) timeDir (spaceDir j)) k`

which is differentiation through two continuous-linear maps — evaluation
of an operator at a fixed direction, then a coordinate projection —
given `DifferentiableAt ℝ (fderiv ℝ U) (x,t)`. `gradComp_eq_joint` above
is the first-order half of exactly this. It is a bridge, not a gap in
the mathematics, but it is not proved here and the exchange should not
be described as applying to `vorticityDt` until it is.

### The Laplacian exchange `curl(Δu) = Δ(curl u)` — NOT proved

Both sides are **third**-order in `u`: `Δ` is two derivatives and `curl`
adds one. In components the claim is

    `∂ⱼ∂ᵢ∂ᵢuₘ = ∂ᵢ∂ᵢ∂ⱼuₘ`

i.e. moving `∂ⱼ` past two copies of `∂ᵢ`.

**mathlib has no symmetry result above order 2** — `IsSymmSndFDerivAt` and
`IsSymmSndFDerivAt.iteratedFDeriv_cons` are both order 2, and a search
for permutation symmetry of `iteratedFDeriv` finds nothing. So this is
not a one-line instantiation like §3.

It is reachable, and the route is two applications of order-2 symmetry:

1. `∂ⱼ∂ᵢ(∂ᵢu) = ∂ᵢ∂ⱼ(∂ᵢu)` — order-2 symmetry applied to the field
   `∂ᵢu`, which needs `∂ᵢu` to be `C²`, i.e. `u` to be `C³`;
2. `∂ᵢ(∂ⱼ∂ᵢu) = ∂ᵢ(∂ᵢ∂ⱼu)` — differentiating the order-2 symmetry for
   `u` itself.

The remaining work after that is bookkeeping, but real: relating the
nested-`fderiv` form above to mathlib's
`InnerProductSpace.laplacian`, which is defined as
`tensorIteratedFDerivTwo` applied to the canonical covariant tensor
rather than as `Σᵢ ∂ᵢ∂ᵢ`. That identification is the clean missing lemma
and is worth stating on its own.

### The convective identity `curl((u·∇)u) = (u·∇)ω − (ω·∇)u` — NOT proved

Order 2 only, so no symmetry gap, but it is a genuine computation: the
identity holds **only for divergence-free `u`**, and proving it means
expanding the curl of a product in three components and cancelling using
`div u = 0`. Tractable with the §1 bridges; not attempted here.

### So the transport equation's status

`VorticityTransportAt` remains a hypothesis, but its content is now
one-quarter proved and three-quarters precisely itemised, rather than
opaque. The open Clay estimate is still slot 3 and is untouched by any
of this.
-/

#print axioms fderiv_slice_eq_joint
#print axioms deriv_slice_eq_joint
#print axioms gradComp_eq_joint
#print axioms mixed_partial_exchange
#print axioms curl_commutes_with_dt

end PF.NavierStokes.FeffermanFaithful
