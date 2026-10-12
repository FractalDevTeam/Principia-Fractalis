/-
# Faithful Fefferman-2000 NS statement — additive residual bridge + non-vacuity facts

Companion to `Fefferman2000_Faithful_Statement_2026_10_12.lean`
(branch `ns-faithful-migration`). Imports ONLY mathlib. Elaborated in the main
`PF_Lean4_Code` tree with `taskset -c 0,1 lake env lean`; see adjacent log.

Two build-verified facts, both proved from core/confirmed mathlib lemmas:

(B1) `faithful_momentum_residual_form` — the FEASIBLE half of the bridge to the
     genuine `ConvectiveDerivativeConnection.momentumResidual`. The faithful
     momentum clause `∂ₜu + (u·∇)u + ∇p = ν•Δu` is equivalent to the vanishing
     of the residual `∂ₜu + (u·∇)u + ∇p − ν•Δu = 0`. This matches the algebraic
     shape of `momentumResidual = ∂ₜu + (u·∇)u − νΔu + ∇p − f` (with f = 0) up to
     additive commutativity of the ∇p and −ν•Δu terms. CRUCIALLY the time
     derivative is `deriv (fun s => U (x,s)) t` and the pressure term is
     `gradient (fun y => P (y,t)) x` — both GENUINE operators of U and P, NOT the
     free `dtu`/`gradp` arguments that `momentumResidual` carries. The faithful
     carrier therefore does not inherit `momentumResidual`'s free-slot caveat.

(B2) `divergence_zero` — the incompressibility hypothesis `div u₀ = 0` is a real
     constraint computed through a genuine `fderiv`, and it is satisfiable: the
     zero field is divergence-free. (Non-vacuity sanity for the hypothesis slot.)

What is NOT provided (and must not be forced): a bridge INTO the actual
`ConvectiveDerivativeConnection.IsNSSolution`/`momentumResidual`, which live on
the COMPLEX space-in-Schwartz carrier `TimeFieldR3C = ℝ → 𝓢(ℝ³,ℂ³)` over
`Set.Icc 0 T`, whereas the faithful statement is REAL-valued on
`EuclideanSpace ℝ (Fin 3)`, only `ContDiffOn`+bounded-energy (NOT Schwartz in
space), and GLOBAL (t ≥ 0). A real translation would require (i) a ℝ→ℂ /
component reindex, (ii) the laplacian identity `InnerProductSpace.laplacian = Σⱼ
∂ⱼ∂ⱼ` in the Euclidean basis, and (iii) a Schwartz-in-space restriction the
faithful solution class does not supply. These are research-grade and are
specified, not elaborated.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace PF.NavierStokes.FeffermanFaithful

/-- Physical/velocity space, identical to the faithful statement's `V`. -/
abbrev V : Type := EuclideanSpace ℝ (Fin 3)

/-- Divergence helper, identical to the faithful statement's. -/
noncomputable def divergence (g : V → V) (x : V) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) i

/-- **(B1) Additive residual form of the faithful momentum clause.**

The faithful momentum equation (the exact LHS/RHS used in the committed
statement) holds iff the momentum residual vanishes. The time derivative and the
pressure gradient appear as genuine operators of `U` and `P`, so no free
`dtu`/`gradp` slot exists to trivialise the equation. -/
theorem faithful_momentum_residual_form
    (U : V × ℝ → V) (P : V × ℝ → ℝ) (ν : ℝ) (x : V) (t : ℝ) :
    ( deriv (fun s : ℝ => U (x, s)) t
        + fderiv ℝ (fun y : V => U (y, t)) x (U (x, t))
        + gradient (fun y : V => P (y, t)) x
      = ν • InnerProductSpace.laplacian (fun y : V => U (y, t)) x )
    ↔
    ( deriv (fun s : ℝ => U (x, s)) t
        + fderiv ℝ (fun y : V => U (y, t)) x (U (x, t))
        + gradient (fun y : V => P (y, t)) x
        - ν • InnerProductSpace.laplacian (fun y : V => U (y, t)) x
      = 0 ) := by
  constructor
  · intro h; rw [h, sub_self]
  · intro h; exact sub_eq_zero.mp h

/-- **(B2) The zero field is divergence-free** — the incompressibility
hypothesis slot is a genuine `fderiv`-computed constraint and is satisfiable. -/
theorem divergence_zero (x : V) : divergence (fun _ : V => (0 : V)) x = 0 := by
  unfold divergence
  have h : fderiv ℝ (fun _ : V => (0 : V)) x = 0 := fderiv_const_apply _
  simp [h]

end PF.NavierStokes.FeffermanFaithful
