/-
# The convective identity

**Date**: 2026-11-21 (Legion).

The last of the four terms in the vorticity transport derivation:

    `curl((u·∇)u) = (u·∇)ω − (ω·∇)u + ω (div u)`

The literature usually quotes this for divergence-free `u`, where the
last term vanishes. The general form is what is actually true, and
carrying the `ω (div u)` term explicitly is the honest statement — the
div-free corollary then follows by hypothesis rather than by assumption
baked into the identity.

## The computation

Write `gⱼₖ = ∂ⱼuₖ`. With `w = (u·∇)u`, the product rule gives

    `∂ⱼw = D²u(eⱼ, u) + Du(∂ⱼu)`

The `D²` part matches `(u·∇)ω` exactly, by second-derivative symmetry
(`D²u(eⱼ,u) = D²u(u,eⱼ)`). What remains is purely algebraic:

    `∑ₗ(g₀ₗgₗ₁ − g₁ₗgₗ₀) = −∑ₗ ωₗ gₗ₂ + (g₀₁−g₁₀)(g₀₀+g₁₁+g₂₂)`

and the bracket is `ω₃ · div u`. So the extra term is forced; it is not
an artifact of the encoding.

This file builds the pieces; §3 assembles them.
-/

import PF.NavierStokes.Fefferman2000_Faithful_TransportDerivation_2026_11_21

namespace PF.NavierStokes.FeffermanFaithful

/-! ## §1 — Spatial field machinery

The transport file's `gradComp` and `vorticity` act on space-time
fields. The convective identity is purely spatial (it holds at each
fixed time), so these are the spatial counterparts. -/

/-- `∂ⱼuₖ` for a spatial field. -/
noncomputable def sg (u : V → V) (x : V) (j k : Fin 3) : ℝ :=
  (fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) k

/-- Components of `curl u` for a spatial field. -/
noncomputable def sVortCoord (u : V → V) (x : V) : Fin 3 → ℝ := fun i =>
  if i = 0 then sg u x 1 2 - sg u x 2 1
  else if i = 1 then sg u x 2 0 - sg u x 0 2
  else sg u x 0 1 - sg u x 1 0

/-- `curl u` for a spatial field, as a vector. -/
noncomputable def sVort (u : V → V) (x : V) : V :=
  ∑ i : Fin 3, sVortCoord u x i • EuclideanSpace.single i (1 : ℝ)

/-- The convective term `(u·∇)u`, as a field. -/
noncomputable def sConv (u : V → V) : V → V := fun y => fderiv ℝ u y (u y)

@[simp] theorem sVort_apply (u : V → V) (x : V) (j : Fin 3) :
    sVort u x j = sVortCoord u x j := by
  unfold sVort
  rw [Finset.sum_apply]
  simp [EuclideanSpace.single_apply]

/-! ## §2 — The three computational inputs -/

/-- Every vector is its basis expansion. -/
theorem eq_sum_basis (v : V) :
    v = ∑ l : Fin 3, (v l) • EuclideanSpace.single l (1 : ℝ) := by
  ext j
  rw [Finset.sum_apply]
  simp [EuclideanSpace.single_apply]

/-- **Directional derivative expanded over the basis**:
    `[Du(v)]ₖ = ∑ₗ vₗ gₗₖ`. -/
theorem fderiv_apply_eq_sum (u : V → V) (x v : V) (k : Fin 3) :
    (fderiv ℝ u x v) k = ∑ l : Fin 3, (v l) * sg u x l k := by
  have h1 : fderiv ℝ u x v
      = fderiv ℝ u x (∑ l : Fin 3, (v l) • EuclideanSpace.single l (1 : ℝ)) :=
    congrArg (fun w => fderiv ℝ u x w) (eq_sum_basis v)
  rw [h1, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp [sg]

/-- `fderiv u` is differentiable at `x` when `u` is `C²` there. -/
theorem differentiableAt_fderiv_of_contDiffAt (u : V → V) (x : V)
    (hu : ContDiffAt ℝ 2 u x) : DifferentiableAt ℝ (fderiv ℝ u) x :=
  (hu.fderiv_right (by norm_num) : ContDiffAt ℝ 1 (fderiv ℝ u) x).differentiableAt
    (le_refl _)

/-- **Product rule for the convective term**:
    `∂ₑ((u·∇)u) = Du(Du(e)) + D²u(e, u)`.

    `(u·∇)u` is the application of the operator-valued field `Du` to the
    vector field `u`, so this is `HasFDerivAt.clm_apply`. -/
theorem fderiv_sConv (u : V → V) (x : V) (hu : ContDiffAt ℝ 2 u x) (e : V) :
    fderiv ℝ (sConv u) x e
      = fderiv ℝ u x (fderiv ℝ u x e) + (fderiv ℝ (fderiv ℝ u) x e) (u x) := by
  have hc : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x :=
    (differentiableAt_fderiv_of_contDiffAt u x hu).hasFDerivAt
  have hU : HasFDerivAt u (fderiv ℝ u x) x :=
    (hu.differentiableAt (by norm_num)).hasFDerivAt
  have h := hc.clm_apply hU
  have hfd : fderiv ℝ (sConv u) x
      = (fderiv ℝ u x).comp (fderiv ℝ u x)
        + (fderiv ℝ (fderiv ℝ u) x).flip (u x) := by
    unfold sConv
    exact h.fderiv
  rw [hfd]
  simp

/-- **Derivative of a velocity-gradient component**:
    `∂ᵥ(gⱼₖ) = [D²u(v, eⱼ)]ₖ`.

    Differentiating through the evaluation at `eⱼ` and the coordinate
    projection, both continuous linear. -/
theorem fderiv_sg (u : V → V) (x v : V) (j k : Fin 3)
    (hu : ContDiffAt ℝ 2 u x) :
    fderiv ℝ (fun y => sg u y j k) x v
      = ((fderiv ℝ (fderiv ℝ u) x v) (EuclideanSpace.single j (1 : ℝ))) k := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_contDiffAt u x hu
  have hev : DifferentiableAt ℝ
      (fun y => fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) x :=
    differentiableAt_eval _ x _ hd
  have h1 : fderiv ℝ (fun y => sg u y j k) x v
      = (EuclideanSpace.proj (𝕜 := ℝ) k)
          (fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) x v) :=
    fderiv_clm_comp (EuclideanSpace.proj (𝕜 := ℝ) k)
      (fun y => fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) x v hev
  rw [h1, fderiv_eval_apply (fderiv ℝ u) x
        (EuclideanSpace.single j (1 : ℝ)) v hd]
  rfl

/-! ## §3 — The algebraic core

Stripped of all analysis: a polynomial identity in the nine components
`gⱼₖ`. This is where the `ω (div u)` term comes from, and it is forced —
the identity is false without it.

Verified by `ring`, so the hand computation in the header is
machine-checked rather than asserted. -/

/-- **The algebraic core of the convective identity.**

    `∑ₗ(g₀ₗgₗ₁ − g₁ₗgₗ₀) = −∑ₗ ωₗgₗ₂ + ω₃(g₀₀+g₁₁+g₂₂)`

    where `ω₁ = g₁₂−g₂₁`, `ω₂ = g₂₀−g₀₂`, `ω₃ = g₀₁−g₁₀`.

    Pure algebra in nine real numbers: no derivatives, no smoothness, no
    Navier-Stokes. The last term is the divergence contribution, and
    dropping it makes the statement false. -/
theorem convective_algebra (g : Fin 3 → Fin 3 → ℝ) :
    (∑ l : Fin 3, g 0 l * g l 1) - (∑ l : Fin 3, g 1 l * g l 0)
      = -((g 1 2 - g 2 1) * g 0 2
          + (g 2 0 - g 0 2) * g 1 2
          + (g 0 1 - g 1 0) * g 2 2)
        + (g 0 1 - g 1 0) * (g 0 0 + g 1 1 + g 2 2) := by
  simp only [Fin.sum_univ_three]
  ring

/-! ## §4 — Assembly -/

@[simp] theorem sVortCoord_zero (u : V → V) (x : V) :
    sVortCoord u x 0 = sg u x 1 2 - sg u x 2 1 := by
  simp [sVortCoord]

@[simp] theorem sVortCoord_one (u : V → V) (x : V) :
    sVortCoord u x 1 = sg u x 2 0 - sg u x 0 2 := by
  have h : (1 : Fin 3) ≠ 0 := by decide
  simp [sVortCoord, h]

@[simp] theorem sVortCoord_two (u : V → V) (x : V) :
    sVortCoord u x 2 = sg u x 0 1 - sg u x 1 0 := by
  have h0 : (2 : Fin 3) ≠ 0 := by decide
  have h1 : (2 : Fin 3) ≠ 1 := by decide
  simp [sVortCoord, h0, h1]

/-- The divergence in gradient components. -/
theorem divergence_eq_sum_sg (u : V → V) (x : V) :
    divergence u x = ∑ i : Fin 3, sg u x i i := rfl

/-- A velocity-gradient component is differentiable where `u` is `C²`. -/
theorem differentiableAt_sg (u : V → V) (x : V) (j k : Fin 3)
    (hu : ContDiffAt ℝ 2 u x) : DifferentiableAt ℝ (fun y => sg u y j k) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_contDiffAt u x hu
  have hev : DifferentiableAt ℝ
      (fun y => fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) x :=
    differentiableAt_eval _ x _ hd
  exact ((EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp x
    hev.hasFDerivAt).differentiableAt

/-- The convective term's gradient components: the quadratic part plus
    the second-derivative part. -/
theorem sg_sConv (u : V → V) (x : V) (hu : ContDiffAt ℝ 2 u x) (j k : Fin 3) :
    sg (sConv u) x j k
      = (∑ l : Fin 3, sg u x j l * sg u x l k)
        + ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single j (1 : ℝ))) (u x)) k := by
  unfold sg
  rw [fderiv_sConv u x hu (EuclideanSpace.single j (1 : ℝ))]
  simp only [PiLp.add_apply]
  congr 1
  rw [fderiv_apply_eq_sum u x (fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) k]
  rfl

/-- Derivative of the third vorticity component, in second-derivative
    form. -/
theorem fderiv_sVortCoord_two (u : V → V) (x v : V) (hu : ContDiffAt ℝ 2 u x) :
    fderiv ℝ (fun y => sVortCoord u y 2) x v
      = ((fderiv ℝ (fderiv ℝ u) x v) (EuclideanSpace.single 0 (1 : ℝ))) 1
        - ((fderiv ℝ (fderiv ℝ u) x v) (EuclideanSpace.single 1 (1 : ℝ))) 0 := by
  have hfun : (fun y => sVortCoord u y 2)
      = fun y => sg u y 0 1 - sg u y 1 0 := by
    funext y; exact sVortCoord_two u y
  rw [hfun, fderiv_fun_sub (differentiableAt_sg u x 0 1 hu)
        (differentiableAt_sg u x 1 0 hu)]
  simp only [ContinuousLinearMap.sub_apply]
  rw [fderiv_sg u x v 0 1 hu, fderiv_sg u x v 1 0 hu]

/-- **★ THE CONVECTIVE IDENTITY**, third component:

      `curl((u·∇)u)₃ = (u·∇)ω₃ − (ω·∇)u₃ + ω₃ (div u)`

    The general form. The `ω (div u)` term is forced — `convective_algebra`
    is false without it — so the usual div-free statement is a corollary,
    not the identity.

    The second-derivative contributions cancel by second-derivative
    symmetry (`D²u(eⱼ,u) = D²u(u,eⱼ)`); what remains is the algebraic
    core. -/
theorem curl_convective_identity (u : V → V) (x : V) (hu : ContDiffAt ℝ 2 u x) :
    sVortCoord (sConv u) x 2
      = fderiv ℝ (fun y => sVortCoord u y 2) x (u x)
        - (fderiv ℝ u x (sVort u x)) 2
        + sVortCoord u x 2 * divergence u x := by
  have hsymm := hu.isSymmSndFDerivAt (by simp)
  -- the two second-derivative terms, with the symmetry applied
  have hD0 : ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single 0 (1 : ℝ))) (u x))
      = ((fderiv ℝ (fderiv ℝ u) x (u x)) (EuclideanSpace.single 0 (1 : ℝ))) :=
    hsymm (EuclideanSpace.single 0 (1 : ℝ)) (u x)
  have hD1 : ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single 1 (1 : ℝ))) (u x))
      = ((fderiv ℝ (fderiv ℝ u) x (u x)) (EuclideanSpace.single 1 (1 : ℝ))) :=
    hsymm (EuclideanSpace.single 1 (1 : ℝ)) (u x)
  rw [sVortCoord_two, sg_sConv u x hu 0 1, sg_sConv u x hu 1 0,
      fderiv_sVortCoord_two u x (u x) hu,
      fderiv_apply_eq_sum u x (sVort u x) 2,
      divergence_eq_sum_sg, hD0, hD1]
  simp only [sVort_apply, sVortCoord_zero, sVortCoord_one, sVortCoord_two,
             Fin.sum_univ_three]
  ring

/-- **The divergence-free case** — the form the vorticity transport
    equation uses. Immediate from the general identity. -/
theorem curl_convective_identity_of_divFree (u : V → V) (x : V)
    (hu : ContDiffAt ℝ 2 u x) (hdiv : divergence u x = 0) :
    sVortCoord (sConv u) x 2
      = fderiv ℝ (fun y => sVortCoord u y 2) x (u x)
        - (fderiv ℝ u x (sVort u x)) 2 := by
  rw [curl_convective_identity u x hu, hdiv]
  ring

#print axioms sVort_apply
#print axioms fderiv_apply_eq_sum
#print axioms fderiv_sConv
#print axioms fderiv_sg
#print axioms convective_algebra
#print axioms sg_sConv
#print axioms fderiv_sVortCoord_two
#print axioms curl_convective_identity
#print axioms curl_convective_identity_of_divFree

end PF.NavierStokes.FeffermanFaithful
