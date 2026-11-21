/-
# Geometric depletion: the vorticity bound from vortex geometry

**Date**: 2026-11-21 (Legion).

Slot 3 — a vorticity bound uniform in the time horizon — is the Clay
problem and is not closed here. What *is* done here is the thing that
actually attacks it: every known conditional regularity result for 3D
Navier-Stokes is a statement about **vorticity geometry**, and this file
formalises that mechanism.

## Why geometry is the right lever

The enstrophy production `⟪ω, (ω·∇)u⟫` is the only term that can grow
`‖ω‖` (`enstrophy_rate_le_of_transport`). Its *size* is free — bounded by
`‖∇u‖‖ω‖²` by the operator-norm inequality, which is why
`VortexStretchingBoundedHypothesis` turned out to be a theorem and why a
`K = 1` bound carries no information. Its **sign** is not free. If the
geometry forces the production non-positive, enstrophy cannot grow.

That is exactly how the known results work:

* **2D**: `ω` is orthogonal to the plane of motion, so `(ω·∇)u = 0`
  identically. Global regularity, classical.
* **Axisymmetric without swirl**: `ω` is azimuthal and `ω_θ/r` is
  transported, giving a bound. Global regularity — Ladyzhenskaya 1968,
  Ukhovskii–Yudovich 1968.
* **Constantin–Fefferman 1993**: regularity of the vorticity *direction*
  in regions of large vorticity rules out blow-up.

A double-toroidal counter-rotating configuration is an axisymmetric
geometry, and counter-rotation is precisely the alignment condition that
depletes stretching. So the framework's mechanism is of the same type as
the three results above, and the theorems below are its formal content.

## What is proved

* `aligned_imp_depleted` — if the velocity is unchanged along the
  vorticity direction, the production vanishes.
* `enstrophy_rate_nonpos_of_depleted` — depletion plus the transport
  equation forces the paired enstrophy rate `≤ 0`: enstrophy cannot grow.
* `planar_imp_aligned` — a planar flow satisfies alignment. This is the
  mechanism **reproducing the known 2D result**, which is the validation
  that it is the right mechanism and not a convenient one.
* `strainRot_production_pos` — a divergence-free field with
  `⟪ω,(ω·∇)u⟫ = 8 > 0`. So depletion is a **real constraint**: unlike the
  `K = 1` bound it is not satisfied by every field, and it cannot be had
  for free.

## What is NOT proved

Slot 3 itself. Depletion gives the *differential* inequality; turning
that into a bound on `‖ω(t)‖` is the Grönwall/ODE comparison step, and
that the framework's toroidal geometry *implies* alignment is a physical
hypothesis about the solution, not a theorem proved here. **This does not
close the Clay problem** and nothing below should be cited as if it did.
-/

import PF.NavierStokes.Fefferman2000_Faithful_ConvectiveIdentity_2026_11_21

namespace PF.NavierStokes.FeffermanFaithful

/-! ## §1 — Alignment and depletion -/

/-- **Depletion**: the enstrophy production is non-positive everywhere on
    the forward time range. The *sign* condition — the part that is not
    free. -/
def EnstrophyDepleted (U : V × ℝ → V) : Prop :=
  ∀ (x : V) (t : ℝ), 0 ≤ t →
    inner ℝ (vorticity U t x) (vortexStretchingFaithful U t x) ≤ 0

/-- **Alignment**: the velocity field is unchanged along the vorticity
    direction, `(ω·∇)u = 0`. The geometric condition that 2D, and
    axisymmetric-without-swirl flow, satisfy. -/
def VorticityAligned (U : V × ℝ → V) : Prop :=
  ∀ (x : V) (t : ℝ), 0 ≤ t →
    fderiv ℝ (fun y : V => U (y, t)) x (vorticity U t x) = 0

/-- Alignment kills the production outright. -/
theorem production_eq_zero_of_aligned (U : V × ℝ → V) (t : ℝ) (x : V)
    (h : fderiv ℝ (fun y : V => U (y, t)) x (vorticity U t x) = 0) :
    inner ℝ (vorticity U t x) (vortexStretchingFaithful U t x) = 0 := by
  unfold vortexStretchingFaithful
  rw [h, inner_zero_right]

/-- **Alignment implies depletion.** -/
theorem aligned_imp_depleted (U : V × ℝ → V) (h : VorticityAligned U) :
    EnstrophyDepleted U := by
  intro x t ht
  rw [production_eq_zero_of_aligned U t x (h x t ht)]

/-- **★ Depletion forces the enstrophy not to grow.**

    With the transport equation, the paired rate
    `⟪ω, ∂ₜω + (u·∇)ω − νΔω⟫` is at most `0`. This is the differential
    inequality a vorticity bound comes from: the production is the only
    term that can grow `‖ω‖`, and depletion removes it.

    Turning this into a bound on `‖ω(t)‖` is the Grönwall/ODE comparison
    step and is not done here. -/
theorem enstrophy_rate_nonpos_of_depleted (U : V × ℝ → V) (ν : ℝ) (t : ℝ) (x : V)
    (ht : 0 ≤ t)
    (htr : VorticityTransportAt U ν t x)
    (hdep : EnstrophyDepleted U) :
    inner ℝ (vorticity U t x)
        (vorticityDt U t x + vorticityConv U t x - ν • vorticityLap U t x) ≤ 0 := by
  have hrw : vorticityDt U t x + vorticityConv U t x - ν • vorticityLap U t x
      = vortexStretchingFaithful U t x := by
    unfold VorticityTransportAt at htr
    rw [htr]; abel
  rw [hrw]
  exact hdep x t ht

/-! ## §2 — The 2D case: the mechanism reproducing a known theorem

If the flow is planar — no dependence on the third coordinate and no
third velocity component — then the vorticity points along `e₃` and the
velocity is constant in that direction, so alignment holds. This is the
exact reason 2D Navier-Stokes has no blow-up, and recovering it is the
check that the depletion mechanism is the right one. -/

/-- A planar flow: the velocity does not vary in the `e₃` direction and
    has no `e₃` component. -/
def PlanarAt (u : V → V) (x : V) : Prop :=
  (fderiv ℝ u x (EuclideanSpace.single 2 (1 : ℝ)) = 0) ∧ (∀ j : Fin 3, sg u x j 2 = 0)

/-- For a planar flow the first two vorticity components vanish. -/
theorem planar_vort_zero_zero (u : V → V) (x : V) (h : PlanarAt u x) :
    sVortCoord u x 0 = 0 := by
  obtain ⟨hz, h3⟩ := h
  rw [sVortCoord_zero, h3 1]
  have : sg u x 2 1 = 0 := by unfold sg; rw [hz]; rfl
  rw [this, sub_zero]

theorem planar_vort_zero_one (u : V → V) (x : V) (h : PlanarAt u x) :
    sVortCoord u x 1 = 0 := by
  obtain ⟨hz, h3⟩ := h
  rw [sVortCoord_one, h3 0]
  have : sg u x 2 0 = 0 := by unfold sg; rw [hz]; rfl
  rw [this, zero_sub, neg_zero]

/-- **The vorticity of a planar flow lies along `e₃`.** -/
theorem planar_vort_eq (u : V → V) (x : V) (h : PlanarAt u x) :
    sVort u x = (sVortCoord u x 2) • EuclideanSpace.single 2 (1 : ℝ) := by
  have h0 := planar_vort_zero_zero u x h
  have h1 := planar_vort_zero_one u x h
  unfold sVort
  rw [Fin.sum_univ_three, h0, h1]
  simp

/-- **★ A planar flow satisfies alignment**: `(ω·∇)u = 0`.

    The vorticity is along `e₃` and the velocity does not vary along
    `e₃`, so the directional derivative vanishes. This is the 2D
    no-blow-up mechanism, recovered from the general machinery. -/
theorem planar_imp_aligned (u : V → V) (x : V) (h : PlanarAt u x) :
    fderiv ℝ u x (sVort u x) = 0 := by
  rw [planar_vort_eq u x h, map_smul, h.1, smul_zero]

/-! ## §3 — Depletion is a real constraint

The *size* of the production is free (operator-norm inequality). Its
*sign* is not: here is a divergence-free field whose production is
strictly positive, so depletion genuinely excludes flows and cannot be
obtained for nothing — unlike the `K = 1` vortex-stretching bound, which
is a theorem. -/

/-- `u(y) = (−y₀ − y₁, y₀ − y₁, 2y₂)` — a rotation plus axial strain.
    Divergence-free, with vorticity `2e₃` along the stretching axis. -/
noncomputable def strainRotCLM : V →L[ℝ] V :=
  (EuclideanSpace.proj (0 : Fin 3)).smulRight (EuclideanSpace.single (0 : Fin 3) (-1 : ℝ))
  + (EuclideanSpace.proj (1 : Fin 3)).smulRight (EuclideanSpace.single (0 : Fin 3) (-1 : ℝ))
  + (EuclideanSpace.proj (0 : Fin 3)).smulRight (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
  + (EuclideanSpace.proj (1 : Fin 3)).smulRight (EuclideanSpace.single (1 : Fin 3) (-1 : ℝ))
  + (EuclideanSpace.proj (2 : Fin 3)).smulRight (EuclideanSpace.single (2 : Fin 3) (2 : ℝ))

/-- The strain-rotation field as a velocity field. -/
noncomputable def strainRot : V → V := fun y => strainRotCLM y

@[simp] theorem fderiv_strainRot (x : V) : fderiv ℝ strainRot x = strainRotCLM := by
  unfold strainRot
  simp

/-- Its velocity-gradient entries. -/
theorem sg_strainRot (x : V) (j k : Fin 3) :
    sg strainRot x j k = (strainRotCLM (EuclideanSpace.single j (1 : ℝ))) k := by
  unfold sg
  rw [fderiv_strainRot]

theorem strainRot_entries (x : V) :
    sg strainRot x 0 0 = -1 ∧ sg strainRot x 0 1 = 1 ∧ sg strainRot x 0 2 = 0 ∧
    sg strainRot x 1 0 = -1 ∧ sg strainRot x 1 1 = -1 ∧ sg strainRot x 1 2 = 0 ∧
    sg strainRot x 2 0 = 0 ∧ sg strainRot x 2 1 = 0 ∧ sg strainRot x 2 2 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [sg_strainRot]; unfold strainRotCLM;
     simp [EuclideanSpace.single_apply])

/-- **The field is divergence-free.** So it is an admissible
    incompressible velocity field, not a degenerate example. -/
theorem strainRot_divFree (x : V) : divergence strainRot x = 0 := by
  obtain ⟨h00, _, _, _, h11, _, _, _, h22⟩ := strainRot_entries x
  rw [divergence_eq_sum_sg, Fin.sum_univ_three, h00, h11, h22]
  norm_num

/-- Its vorticity is `2e₃` — along the stretching axis. -/
theorem strainRot_vort (x : V) :
    sVort strainRot x = (2 : ℝ) • EuclideanSpace.single 2 (1 : ℝ) := by
  obtain ⟨_, h01, h02, h10, _, h12, h20, h21, _⟩ := strainRot_entries x
  unfold sVort
  rw [Fin.sum_univ_three, sVortCoord_zero, sVortCoord_one, sVortCoord_two,
      h01, h10, h02, h12, h20, h21]
  norm_num

/-- **★ Depletion is a real constraint.**

    This divergence-free field has strictly positive enstrophy
    production, `⟪ω, (ω·∇)u⟫ = 8`. So `EnstrophyDepleted` genuinely
    excludes flows — it is **not** satisfiable by every field.

    Contrast `VortexStretchingBoundedHypothesis`, which bounds the
    production's *size* and is a theorem for free at `K = 1`. The sign
    condition is where the content is. -/
theorem strainRot_production_pos (x : V) :
    inner ℝ (sVort strainRot x) (fderiv ℝ strainRot x (sVort strainRot x))
      = (8 : ℝ) := by
  rw [strainRot_vort, fderiv_strainRot, map_smul, real_inner_smul_left,
      real_inner_smul_right]
  unfold strainRotCLM
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  norm_num

/-- Hence the production can be strictly positive. -/
theorem exists_positive_enstrophy_production :
    ∃ (u : V → V) (x : V), divergence u x = 0 ∧
      0 < inner ℝ (sVort u x) (fderiv ℝ u x (sVort u x)) := by
  refine ⟨strainRot, 0, strainRot_divFree 0, ?_⟩
  rw [strainRot_production_pos]
  norm_num

/-! ## §4 — Slot 3 from the geometry

The chain the framework's mechanism completes:

    geometry → alignment → depletion → enstrophy cannot grow
      → [Grönwall] → vorticity bound = slot 3 → [slots 1,2] → Clay

Everything but the Grönwall step and the geometry-implies-alignment step
is proved. The Grönwall step is classical and is named below as an input,
in the same style as slots 1 and 2. -/

/-- **Classical input**: if every local solution with a given datum has
    non-growing enstrophy, the vorticity obeys a bound uniform in the
    time horizon.

    This is the Grönwall / ODE-comparison step: a non-positive rate
    integrates to a bound set by the initial data, and the bound does not
    degrade with `T` precisely because the rate never becomes positive.
    Classical analysis; not formalised here. -/
def GronwallFromDepletion : Prop :=
  ∀ u0 : SchwartzMap V V, AdmissibleDatum u0 →
    (∀ (T ν : ℝ) (U : V × ℝ → V) (P : V × ℝ → ℝ),
      0 < T → 0 < ν → IsFaithfulNSOn ν U P (Set.Icc 0 T) →
      (∀ x : V, U (x, 0) = u0 x) → EnstrophyDepleted U) →
    ∃ M : ℝ, 0 ≤ M ∧ VorticityBoundedBy u0 M

/-- **The framework's geometric hypothesis**: every admissible datum's
    local solutions are enstrophy-depleted.

    This is what the double-toroidal counter-rotating vortex geometry
    asserts, in the only form that bears on regularity. It is a
    hypothesis about solutions, not a theorem — and by
    `exists_positive_enstrophy_production` it is a **substantive** one,
    since depletion fails for some divergence-free fields. -/
def GeometricDepletionHypothesis : Prop :=
  ∀ u0 : SchwartzMap V V, AdmissibleDatum u0 →
    ∀ (T ν : ℝ) (U : V × ℝ → V) (P : V × ℝ → ℝ),
      0 < T → 0 < ν → IsFaithfulNSOn ν U P (Set.Icc 0 T) →
      (∀ x : V, U (x, 0) = u0 x) → EnstrophyDepleted U

/-- **★ SLOT 3 FROM THE GEOMETRY.**

    The geometric depletion hypothesis, with the classical Grönwall step,
    yields `VorticityAPrioriBound` — slot 3, the open Clay estimate.

    Both premises are hypotheses and neither is proved: the Grönwall step
    is classical analysis awaiting formalisation, and the depletion
    hypothesis is the framework's physical claim about the vortex
    geometry. **This does not close the Clay problem.** What it does is
    reduce slot 3 to exactly those two things — one textbook, one
    physical — rather than leaving it as the bare Clay statement. -/
theorem apriori_bound_of_geometric_depletion
    (hG : GronwallFromDepletion)
    (hgeo : GeometricDepletionHypothesis) :
    VorticityAPrioriBound := by
  intro u0 hu0
  exact hG u0 hu0 (fun T ν U P hT hν hNS hinit => hgeo u0 hu0 T ν U P hT hν hNS hinit)

/-- **★ And therefore the Clay statement**, from the geometry plus the
    three classical inputs.

    Chain, with every link's status explicit: Fujita-Kato local existence
    (classical), BKM continuation (classical), Grönwall comparison
    (classical), and the geometric depletion hypothesis (the framework's
    physical claim). Four hypotheses, none discharged here.

    **No Millennium problem is solved by this theorem.** Its content is
    that the gap is exactly those four, and that three of them are
    textbook. -/
theorem clay_from_geometry
    (h1 : FujitaKato_Faithful)
    (h2 : BKMContinuation_Faithful)
    (hG : GronwallFromDepletion)
    (hgeo : GeometricDepletionHypothesis) :
    Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful :=
  clay_from_the_three_slots h1 h2 (apriori_bound_of_geometric_depletion hG hgeo)

#print axioms production_eq_zero_of_aligned
#print axioms aligned_imp_depleted
#print axioms enstrophy_rate_nonpos_of_depleted
#print axioms planar_imp_aligned
#print axioms sg_strainRot
#print axioms strainRot_divFree
#print axioms strainRot_production_pos
#print axioms exists_positive_enstrophy_production
#print axioms apriori_bound_of_geometric_depletion
#print axioms clay_from_geometry

end PF.NavierStokes.FeffermanFaithful
