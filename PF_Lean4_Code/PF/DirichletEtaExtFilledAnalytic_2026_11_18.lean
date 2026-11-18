import PF.DirichletEtaExtFilledDifferentiable_2026_11_18
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# `AnalyticOnNhd ℂ dirichletEtaExtFilled Set.univ`

Upgrades `Differentiable ℂ dirichletEtaExtFilled` (commit 6131c331) to
analyticity everywhere via mathlib's `DifferentiableOn.analyticOnNhd`
on the open set `Set.univ`.

The filled extension of Dirichlet eta is honestly entire — both
differentiable and analytic — with the only subtle point being the
removable singularity at `s = 1`, which was closed by the 2026-11-17
differentiability brick and today's entire-function strengthening.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/

namespace PrincipiaTractalis.DirichletEtaExtFilledAnalytic_2026_11_18

open PrincipiaTractalis.DirichletEtaExtDifferentiableAtOneDisclosure
  (dirichletEtaExtFilled)
open PrincipiaTractalis.DirichletEtaExtFilledDifferentiable_2026_11_18
  (dirichletEtaExtFilled_differentiable)

/-- The filled extension is analytic (on a neighborhood of every point)
    everywhere. Immediate from `Differentiable ℂ`, which gives
    `DifferentiableOn ℂ · Set.univ`, and mathlib's Cauchy-integral
    upgrade `DifferentiableOn.analyticOnNhd` for open sets. -/
theorem dirichletEtaExtFilled_analyticOnNhd :
    AnalyticOnNhd ℂ dirichletEtaExtFilled Set.univ :=
  dirichletEtaExtFilled_differentiable.differentiableOn.analyticOnNhd isOpen_univ

/-- Corollary: analytic at every point. -/
theorem dirichletEtaExtFilled_analyticAt (s : ℂ) :
    AnalyticAt ℂ dirichletEtaExtFilled s :=
  dirichletEtaExtFilled_analyticOnNhd s (Set.mem_univ s)

#print axioms dirichletEtaExtFilled_analyticOnNhd
#print axioms dirichletEtaExtFilled_analyticAt

end PrincipiaTractalis.DirichletEtaExtFilledAnalytic_2026_11_18
