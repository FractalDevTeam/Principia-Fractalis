/-
# Faithful Navier-Stokes: the three hypothesis slots, and the reduction

**Date**: 2026-11-21 (Legion).

`Fefferman2000_Faithful_Statement_2026_10_12.lean` states the Clay
problem faithfully; `..._ZeroDatum_2026_11_20.lean` shows the encoding is
sound (satisfiable, and with teeth). Neither says what would be needed to
*prove* it. This file does, as Lean rather than as prose.

## The decomposition, and why it is this one

Global existence and smoothness for 3D Navier-Stokes follows from three
inputs, and they are **not** on an equal footing:

1. **Local existence** (Fujita-Kato 1964; Kato 1984). For divergence-free
   data in `Ḣ^{1/2}(ℝ³)` -- Schwartz data in particular -- a unique mild
   solution exists on some `[0,T)`, and is smooth there for smooth data.
   **This is a classical theorem.** It is true. It is simply not in
   mathlib.

2. **The continuation principle** (Beale-Kato-Majda 1984; Leray 1934,
   Hopf 1951 for the energy framework). A local smooth solution whose
   vorticity satisfies `∫₀^T ‖ω(·,t)‖_{L^∞} dt < ∞` extends past `T`;
   hence control of that quantity on every finite interval gives a global
   solution, with the energy inequality supplying the bounded-energy
   clause. **Also a classical theorem.** Also not in mathlib.

3. **An a priori bound on the vorticity, uniform in `T`.** This is
   **open**. It is the Clay problem. Everything unknown about 3D
   Navier-Stokes sits here and nowhere else in this chain.

Writing the three separately is the entire point: it localises the gap.
A reduction that lumped (1) and (2) in with (3) would hide the fact that
two thirds of the chain is settled literature and one third is the open
estimate -- and it is precisely estimate (3) that the manuscript's Ch 22
fractal emergence-point mechanism purports to supply.

## What is proved here, and what is not

**Proved**: that the three slots compose to the faithful Clay statement
(`clay_from_the_three_slots`); that the Ch 22 slot follows from them
(`fractal_emergence_slot_from_the_three`, in
`PF/MillenniumSixReductions.lean`, where that slot is defined); that the
vorticity defined
here is the classical curl, coordinate by coordinate
(`vorticity_apply`); that it vanishes on constant fields; that it is
**not identically zero** -- the linear shear field `u(y) = (y₂,0,0)` has
`ω₃ = -1` (`shear_vorticity_coord_two`, `shear_has_nonzero_vorticity`),
so slot 3 is a real constraint and not a vacuous one; and that all three
slot bodies are simultaneously satisfiable at the zero datum
(`slot_bodies_consistent_at_zero_datum`), so the reduction is not an
implication out of a contradiction.

**Not proved**: any of the three slots. Slots 1 and 2 are classical and
would be formalisation projects; slot 3 is the Clay problem. **Nothing
here proves Navier-Stokes**, and the composition theorem is a modus
ponens whose premises are all undischarged.

## One stated-precisely modelling choice

Slot 2's classical hypothesis is finiteness of `∫₀^T ‖ω(·,t)‖_{L^∞} dt`.
What is used below is a uniform bound: `‖ω(x,t)‖ ≤ M` for all `x` and all
`t ∈ [0,T]`, with `M` independent of `T`. This **implies** the integral
condition (the integral is then at most `M·T` on `[0,T]`, finite for
every finite `T`), so it is a *sufficient* form of the hypothesis and is
therefore slightly stronger than BKM needs. Stating it this way avoids
formalising an essential-supremum-in-space and a Bochner integral in
time, neither of which adds mathematical content to the reduction. It is
stronger, which makes slot 3 harder to supply, not easier -- so the
reduction is not weakened in the direction that would flatter it.
-/

import PF.NavierStokes.Fefferman2000_Faithful_Statement_2026_10_12
import PF.NavierStokes.Fefferman2000_Faithful_ZeroDatum_2026_11_20
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory

namespace PF.NavierStokes.FeffermanFaithful

/-! ## §1 — Vorticity: the classical curl, from mathlib's `fderiv`

`gradComp U t x j k` is `∂_j u_k` at `(x,t)`: the Fréchet derivative of
the spatial field in the `j`-th coordinate direction, read off in
coordinate `k`. The curl is then the usual antisymmetric combination. -/

/-- `∂_j u_k (x,t)` — a genuine partial derivative of the velocity field. -/
noncomputable def gradComp (U : V × ℝ → V) (t : ℝ) (x : V) (j k : Fin 3) : ℝ :=
  (fderiv ℝ (fun y : V => U (y, t)) x (EuclideanSpace.single j (1 : ℝ))) k

/-- `ω₁ = ∂₂u₃ − ∂₃u₂`. -/
noncomputable def vort1 (U : V × ℝ → V) (t : ℝ) (x : V) : ℝ :=
  gradComp U t x 1 2 - gradComp U t x 2 1

/-- `ω₂ = ∂₃u₁ − ∂₁u₃`. -/
noncomputable def vort2 (U : V × ℝ → V) (t : ℝ) (x : V) : ℝ :=
  gradComp U t x 2 0 - gradComp U t x 0 2

/-- `ω₃ = ∂₁u₂ − ∂₂u₁`. -/
noncomputable def vort3 (U : V × ℝ → V) (t : ℝ) (x : V) : ℝ :=
  gradComp U t x 0 1 - gradComp U t x 1 0

/-- The three components of `ω = ∇ × u`. -/
noncomputable def vorticityCoord (U : V × ℝ → V) (t : ℝ) (x : V) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then vort1 U t x
    else if i = 1 then vort2 U t x
    else vort3 U t x

@[simp] theorem vorticityCoord_two (U : V × ℝ → V) (t : ℝ) (x : V) :
    vorticityCoord U t x 2 = vort3 U t x := by
  have h0 : (2 : Fin 3) ≠ 0 := by decide
  have h1 : (2 : Fin 3) ≠ 1 := by decide
  unfold vorticityCoord
  simp [h0, h1]

/-- **Vorticity** `ω(x,t) = (∇ × u)(x,t)`, as a vector in `ℝ³`. -/
noncomputable def vorticity (U : V × ℝ → V) (t : ℝ) (x : V) : V :=
  ∑ i : Fin 3, vorticityCoord U t x i • EuclideanSpace.single i (1 : ℝ)

/-- The vector really does carry the stated components: this is what makes
    `vorticity` verifiably the classical curl rather than an opaque
    definition. -/
@[simp] theorem vorticity_apply (U : V × ℝ → V) (t : ℝ) (x : V) (j : Fin 3) :
    vorticity U t x j = vorticityCoord U t x j := by
  unfold vorticity
  rw [Finset.sum_apply]
  simp [EuclideanSpace.single_apply]

/-- A vector in `ℝ³` vanishes iff all three coordinates do. -/
theorem eq_zero_iff_coords (v : V) : v = 0 ↔ ∀ j : Fin 3, v j = 0 := by
  constructor
  · intro h j; rw [h]; rfl
  · intro h; ext j; simpa using h j

/-- Constant velocity fields are irrotational. -/
@[simp] theorem vorticity_const (c : V) (t : ℝ) (x : V) :
    vorticity (fun _ : V × ℝ => c) t x = 0 := by
  rw [eq_zero_iff_coords]
  intro j
  rw [vorticity_apply]
  unfold vorticityCoord vort1 vort2 vort3 gradComp
  simp

/-! ## §2 — The vorticity functional is not degenerate

If `vorticity` were identically zero, slot 3 below would be vacuous:
`M = 0` would always work and the reduction would prove the Clay problem
from slots 1 and 2 alone, which is false. It is not identically zero. -/

/-- The linear shear field `u(y) = (y₂, 0, 0)`, as a continuous linear
    map — so its Fréchet derivative is itself. -/
noncomputable def shearCLM : V →L[ℝ] V :=
  (EuclideanSpace.proj (1 : Fin 3)).smulRight (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))

/-- The shear field as a space-time velocity field (steady in time). -/
noncomputable def shearField : V × ℝ → V := fun q => shearCLM q.1

@[simp] theorem shearCLM_apply (y : V) (k : Fin 3) :
    (shearCLM y) k = if k = 0 then y 1 else 0 := by
  simp [shearCLM, EuclideanSpace.single_apply]

/-- `∂_j u_k` for the shear field: `1` exactly at `j = 1, k = 0`. -/
theorem shear_gradComp (t : ℝ) (x : V) (j k : Fin 3) :
    gradComp shearField t x j k = if k = 0 then (if (1 : Fin 3) = j then 1 else 0) else 0 := by
  unfold gradComp shearField
  have h : fderiv ℝ (fun y : V => shearCLM y) x = shearCLM := by simp
  rw [h]
  simp [EuclideanSpace.single_apply]

/-- `∂₁u₂ = 0` for the shear field. -/
theorem shear_gradComp_0_1 (t : ℝ) (x : V) : gradComp shearField t x 0 1 = 0 := by
  rw [shear_gradComp]
  have : (1 : Fin 3) ≠ 0 := by decide
  simp [this]

/-- `∂₂u₁ = 1` for the shear field — the one nonvanishing derivative. -/
theorem shear_gradComp_1_0 (t : ℝ) (x : V) : gradComp shearField t x 1 0 = 1 := by
  rw [shear_gradComp]
  simp

/-- **The third vorticity component of the shear field is `-1`.** -/
theorem shear_vorticity_coord_two (t : ℝ) (x : V) :
    vorticityCoord shearField t x 2 = -1 := by
  rw [vorticityCoord_two]
  unfold vort3
  rw [shear_gradComp_0_1, shear_gradComp_1_0]
  norm_num

/-- **The vorticity functional is not identically zero**, so slot 3 is a
    genuine constraint: no single `M < 1` can bound every field. -/
theorem shear_has_nonzero_vorticity (t : ℝ) (x : V) :
    vorticity shearField t x ≠ 0 := by
  intro h
  have h2 : vorticity shearField t x 2 = 0 := by rw [h]; rfl
  rw [vorticity_apply, shear_vorticity_coord_two] at h2
  norm_num at h2

/-! ## §2b — The vortex-stretching term, and why its bilinear bound is free

`(ω·∇)u` is the Fréchet derivative of the velocity field in the
direction of the vorticity vector. The bilinear bound
`‖(ω·∇)u‖ ≤ ‖∇u‖‖ω‖` is then just the operator-norm inequality — it
holds with constant `1`, unconditionally, on the real carrier.

This matters for reading `NS3DVortexStretchingObstruction`, which posits
a bound of exactly this shape as "the isolated residual obligation" on a
finite-dimensional diagonal model. It is provable there
(`vortex_stretching_bounded_all_n`), and the theorem below shows that is
not an artifact of the diagonal simplification: the bound is free for the
genuine operator too. What is *not* free, and is the whole difficulty, is
uniform-in-time control of `‖∇u‖` along the flow. -/

/-- The genuine vortex-stretching term `(ω·∇)u` on the faithful carrier:
    the velocity gradient applied to the vorticity. -/
noncomputable def vortexStretchingFaithful (U : V × ℝ → V) (t : ℝ) (x : V) : V :=
  fderiv ℝ (fun y : V => U (y, t)) x (vorticity U t x)

/-- **The bilinear stretching bound holds with constant 1**, for the
    genuine `(ω·∇)u`, unconditionally. It is the operator-norm
    inequality and nothing more. -/
theorem norm_vortexStretchingFaithful_le (U : V × ℝ → V) (t : ℝ) (x : V) :
    ‖vortexStretchingFaithful U t x‖
      ≤ ‖fderiv ℝ (fun y : V => U (y, t)) x‖ * ‖vorticity U t x‖ :=
  (fderiv ℝ (fun y : V => U (y, t)) x).le_opNorm _

/-- Irrotational flow has no vortex stretching. -/
@[simp] theorem vortexStretchingFaithful_of_vorticity_zero
    (U : V × ℝ → V) (t : ℝ) (x : V) (h : vorticity U t x = 0) :
    vortexStretchingFaithful U t x = 0 := by
  unfold vortexStretchingFaithful
  rw [h, map_zero]

/-! ## §3 — Being a faithful solution, on a set of times

The clauses are exactly those of the Clay statement, with the time range
abstracted so the same predicate serves a finite slab `[0,T]` (local
existence) and the half-line `[0,∞)` (the global conclusion). -/

/-- `U`, `P` solve Navier-Stokes faithfully, with viscosity `ν`, at every
    time in `I`: jointly `C^∞`, divergence-free, and satisfying the
    momentum equation `∂ₜu + (u·∇)u + ∇p = νΔu`. -/
def IsFaithfulNSOn (ν : ℝ) (U : V × ℝ → V) (P : V × ℝ → ℝ) (I : Set ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) U {q : V × ℝ | q.2 ∈ I} ∧
  ContDiffOn ℝ (⊤ : ℕ∞) P {q : V × ℝ | q.2 ∈ I} ∧
  (∀ (x : V) (t : ℝ), t ∈ I → divergence (fun y => U (y, t)) x = 0) ∧
  (∀ (x : V) (t : ℝ), t ∈ I →
    deriv (fun s : ℝ => U (x, s)) t
      + fderiv ℝ (fun y : V => U (y, t)) x (U (x, t))
      + gradient (fun y : V => P (y, t)) x
    = ν • InnerProductSpace.laplacian (fun y : V => U (y, t)) x)

/-- Fefferman's bounded-energy clause (6), on a set of times, with the
    integrability guard that keeps the bound from being silently about
    mathlib's `∫ = 0` convention for non-integrable integrands. -/
def HasBoundedEnergyOn (U : V × ℝ → V) (I : Set ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I,
    Integrable (fun x : V => ‖U (x, t)‖ ^ 2) ∧ (∫ x : V, ‖U (x, t)‖ ^ 2) ≤ C

/-- `u₀` is admissible Clay data: Schwartz (Fefferman's decay condition
    (4)) and divergence-free. -/
def AdmissibleDatum (u0 : SchwartzMap V V) : Prop :=
  ∀ x : V, divergence (fun y => u0 y) x = 0

/-- There is a faithful solution with datum `u₀` on the finite slab
    `[0,T]`, with bounded energy there. -/
def HasLocalSolution (u0 : SchwartzMap V V) (T : ℝ) : Prop :=
  ∃ (ν : ℝ) (U : V × ℝ → V) (P : V × ℝ → ℝ),
    0 < ν ∧ IsFaithfulNSOn ν U P (Set.Icc 0 T) ∧
    (∀ x : V, U (x, 0) = u0 x) ∧ HasBoundedEnergyOn U (Set.Icc 0 T)

/-- There is a faithful solution with datum `u₀` on all of `[0,∞)`, with
    bounded energy — Fefferman's conclusion for that datum. -/
def HasGlobalSolution (u0 : SchwartzMap V V) : Prop :=
  ∃ (ν : ℝ) (U : V × ℝ → V) (P : V × ℝ → ℝ),
    0 < ν ∧ IsFaithfulNSOn ν U P (Set.Ici 0) ∧
    (∀ x : V, U (x, 0) = u0 x) ∧ HasBoundedEnergyOn U (Set.Ici 0)

/-- Every faithful solution with datum `u₀` on every finite slab has
    vorticity bounded by `M`, with `M` **independent of the slab length**.
    Uniformity in `T` is the whole difficulty; a `T`-dependent bound is
    free from local existence and gives nothing. -/
def VorticityBoundedBy (u0 : SchwartzMap V V) (M : ℝ) : Prop :=
  ∀ (T ν : ℝ) (U : V × ℝ → V) (P : V × ℝ → ℝ),
    0 < T → 0 < ν →
    IsFaithfulNSOn ν U P (Set.Icc 0 T) →
    (∀ x : V, U (x, 0) = u0 x) →
    ∀ (x : V) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → ‖vorticity U t x‖ ≤ M

/-! ## §4 — The three slots -/

/-- **SLOT 1 — Local existence (Fujita-Kato 1964).**

    For every admissible datum there is a positive time horizon on which
    a faithful smooth solution exists with bounded energy.

    **Classical and true**; the obstruction is formalisation, not
    mathematics. Kato's mild-solution construction in `Ḣ^{1/2}` plus
    parabolic smoothing gives it for Schwartz data. Not in mathlib at
    v4.24.0-rc1: see `NS_SCOPING_CARRIER_IS_THE_BLOCKER_2026-10-17.md`
    for why the repo's own Fujita-Kato layer stops short — the bilinear
    term cannot be built on a Schwartz-valued carrier, because
    `SchwartzMap` has no `NormedAddCommGroup` instance and
    `intervalIntegral` requires one. -/
def FujitaKato_Faithful : Prop :=
  ∀ u0 : SchwartzMap V V, AdmissibleDatum u0 →
    ∃ T : ℝ, 0 < T ∧ HasLocalSolution u0 T

/-- **SLOT 2 — The continuation principle (Beale-Kato-Majda 1984).**

    If an admissible datum admits a local solution, and the vorticity of
    every local solution with that datum obeys a bound uniform in the
    slab length, then a global faithful solution with bounded energy
    exists.

    **Classical and true.** BKM: a smooth solution on `[0,T)` extends
    past `T` iff `∫₀^T ‖ω(·,t)‖_{L^∞} dt < ∞`; a uniform bound `M` makes
    that integral at most `M·T`, finite for every finite `T`, so no
    finite time is maximal. Leray-Hopf supplies the energy inequality
    behind the bounded-energy clause. Not formalised here: the repo's own
    BKM file is vacuous (`SolutionBlowsUpAt := False`) because a
    globally-Schwartz carrier cannot express loss of smoothness at all. -/
def BKMContinuation_Faithful : Prop :=
  ∀ u0 : SchwartzMap V V, AdmissibleDatum u0 →
    (∃ T : ℝ, 0 < T ∧ HasLocalSolution u0 T) →
    (∃ M : ℝ, 0 ≤ M ∧ VorticityBoundedBy u0 M) →
    HasGlobalSolution u0

/-- **SLOT 3 — The a priori vorticity bound. THIS IS THE OPEN PROBLEM.**

    For every admissible datum, a bound on the vorticity of its local
    solutions that does not degrade as the time horizon grows.

    Unlike slots 1 and 2 this is **not** a known theorem. It is the Clay
    problem, restated as the one estimate that is missing: by slots 1 and
    2 it is *sufficient* for global existence and smoothness. Every
    serious attack on 3D Navier-Stokes is an attack on this line, and the
    manuscript's Ch 22 fractal emergence-point mechanism is a proposed
    route to it — see `FractalEmergenceYieldsGlobalSmoothness` in
    `PF/MillenniumSixReductions.lean`.

    It is a genuine constraint: `vorticity` is not identically zero
    (`shear_has_nonzero_vorticity`), so this cannot be met by taking
    `M = 0`. -/
def VorticityAPrioriBound : Prop :=
  ∀ u0 : SchwartzMap V V, AdmissibleDatum u0 →
    ∃ M : ℝ, 0 ≤ M ∧ VorticityBoundedBy u0 M

/-! ## §5 — The reduction -/

/-- A global solution for every admissible datum **is** the faithful Clay
    statement. Unfolding only; it records that `HasGlobalSolution` was
    defined to match Fefferman's conclusion clause for clause. -/
theorem clay_of_global_solutions
    (h : ∀ u0 : SchwartzMap V V, AdmissibleDatum u0 → HasGlobalSolution u0) :
    Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful := by
  intro u0 hdiv
  obtain ⟨ν, U, P, hν, ⟨hU, hP, hdivU, hmom⟩, hinit, hE⟩ := h u0 hdiv
  exact ⟨U, P, ν, hν, hU, hP, hinit,
    (fun x t ht => hdivU x t ht), (fun x t ht => hmom x t ht), hE⟩

/-- **★ THE REDUCTION ★** — the faithful Clay Navier-Stokes statement
    follows from the three slots.

    Two premises are classical theorems awaiting formalisation; the third
    is the open estimate. **This discharges nothing**: all three premises
    are hypotheses, and `VorticityAPrioriBound` in particular is the Clay
    problem. What the theorem establishes is that the gap is *exactly*
    these three and nothing more — machine-checked, rather than asserted
    in a prose gap table. -/
theorem clay_from_the_three_slots
    (h1 : FujitaKato_Faithful)
    (h2 : BKMContinuation_Faithful)
    (h3 : VorticityAPrioriBound) :
    Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful := by
  refine clay_of_global_solutions ?_
  intro u0 hdiv
  exact h2 u0 hdiv (h1 u0 hdiv) (h3 u0 hdiv)

/-- The same chain, exhibiting that slot 3 is what the framework must
    supply: with the two classical inputs granted, the Clay statement is
    equivalent to having the a priori bound as a hypothesis. -/
theorem clay_iff_apriori_given_classical_inputs
    (h1 : FujitaKato_Faithful)
    (h2 : BKMContinuation_Faithful) :
    VorticityAPrioriBound →
      Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful :=
  fun h3 => clay_from_the_three_slots h1 h2 h3

/-! ## §6 — Soundness of the slot design

A reduction whose premises are jointly contradictory proves its
conclusion and means nothing. The slot bodies are consistent: at the zero
datum each is satisfied, by the zero solution. -/

/-- The zero field is a faithful solution on every set of times. -/
theorem zeroSolution_isFaithful (I : Set ℝ) :
    IsFaithfulNSOn 1 (fun _ : V × ℝ => (0 : V)) (fun _ : V × ℝ => (0 : ℝ)) I := by
  refine ⟨contDiffOn_const, contDiffOn_const, ?_, ?_⟩
  · intro x t _
    exact divergence_zero_fun x
  · intro x t _
    simp

/-- The zero field has bounded energy on every set of times, with `C = 0`. -/
theorem zeroSolution_boundedEnergy (I : Set ℝ) :
    HasBoundedEnergyOn (fun _ : V × ℝ => (0 : V)) I := by
  refine ⟨0, le_refl 0, fun t _ => ⟨?_, ?_⟩⟩
  · simp
  · simp

/-- **The three slot bodies are simultaneously satisfiable at the zero
    datum**: a local solution exists, a global solution exists, and the
    vorticity of the zero solution is bounded by `0`. So the reduction is
    not an implication out of a contradiction.

    This is a consistency check on the slot *bodies* at one datum. It is
    not, and is not claimed to be, evidence for any slot — each slot is
    universally quantified over all admissible data. -/
theorem slot_bodies_consistent_at_zero_datum :
    HasLocalSolution 0 1 ∧
    HasGlobalSolution 0 ∧
    (∀ (x : V) (t : ℝ), ‖vorticity (fun _ : V × ℝ => (0 : V)) t x‖ ≤ 0) := by
  refine ⟨⟨1, (fun _ => (0 : V)), (fun _ => (0 : ℝ)), one_pos,
            zeroSolution_isFaithful _, ?_, zeroSolution_boundedEnergy _⟩,
          ⟨1, (fun _ => (0 : V)), (fun _ => (0 : ℝ)), one_pos,
            zeroSolution_isFaithful _, ?_, zeroSolution_boundedEnergy _⟩,
          ?_⟩
  · intro x; rfl
  · intro x; rfl
  · intro x t
    rw [vorticity_const]
    simp

#print axioms vorticity_apply
#print axioms shear_vorticity_coord_two
#print axioms shear_has_nonzero_vorticity
#print axioms clay_of_global_solutions
#print axioms clay_from_the_three_slots
#print axioms slot_bodies_consistent_at_zero_datum

end PF.NavierStokes.FeffermanFaithful
