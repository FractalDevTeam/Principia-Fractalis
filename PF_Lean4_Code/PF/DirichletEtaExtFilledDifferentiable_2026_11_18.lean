import PF.DirichletEtaExtension_r269
import PF.DirichletEtaExtDifferentiable_r278
import PF.DirichletEtaExtDifferentiableAtOneDisclosure_2026_11_16
import PF.DirichletEtaExtDifferentiableAtOne_2026_11_17
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Topology.Separation.Basic

/-!
# `Differentiable ℂ dirichletEtaExtFilled`

Strengthens the pointwise `DifferentiableAt ℂ dirichletEtaExtFilled 1`
(`dirichletEtaExtFilled_differentiableAt_atOne`, 2026-11-17) to the
global statement that `dirichletEtaExtFilled` is differentiable at
*every* `s : ℂ`.

Pieces in place:
  - r278 `dirichletEtaExt_differentiableAt : s ≠ 1 → DifferentiableAt ℂ dirichletEtaExt s`.
  - disclosure 2026-11-16 `dirichletEtaExtFilled_eq_dirichletEtaExt_of_ne_one`.
  - 2026-11-17 `dirichletEtaExtFilled_differentiableAt_atOne`.

At every `s ≠ 1`, `dirichletEtaExtFilled` agrees with `dirichletEtaExt`
on the open neighbourhood `{1}ᶜ` of `s`, so differentiability transfers
via `Filter.EventuallyEq.differentiableAt_iff`. At `s = 1`, the 2026-11-17
headline gives the result directly.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/

namespace PrincipiaTractalis.DirichletEtaExtFilledDifferentiable_2026_11_18

open Complex Filter Topology
open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)
open PrincipiaTractalis.DirichletEtaExtDifferentiable
  (dirichletEtaExt_differentiableAt)
open PrincipiaTractalis.DirichletEtaExtDifferentiableAtOneDisclosure
  (dirichletEtaExtFilled
   dirichletEtaExtFilled_eq_dirichletEtaExt_of_ne_one)
open PrincipiaTractalis.DirichletEtaExtDifferentiableAtOne_2026_11_17
  (dirichletEtaExtFilled_differentiableAt_atOne)

/-- Pointwise differentiability of `dirichletEtaExtFilled` at any `s ≠ 1`:
    the filled extension agrees with the raw `dirichletEtaExt` on the
    open set `{1}ᶜ` (a neighbourhood of every such `s`), and r278 gives
    `DifferentiableAt ℂ dirichletEtaExt s`. -/
theorem dirichletEtaExtFilled_differentiableAt_of_ne_one
    {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ dirichletEtaExtFilled s := by
  have heq : dirichletEtaExtFilled =ᶠ[𝓝 s] dirichletEtaExt := by
    have hopen : ({(1 : ℂ)}ᶜ : Set ℂ) ∈ 𝓝 s :=
      isOpen_compl_singleton.mem_nhds hs
    filter_upwards [hopen] with w (hw : w ∈ ({(1 : ℂ)}ᶜ : Set ℂ))
    exact dirichletEtaExtFilled_eq_dirichletEtaExt_of_ne_one hw
  rw [heq.differentiableAt_iff]
  exact dirichletEtaExt_differentiableAt hs

/-- **Headline.** `dirichletEtaExtFilled` is differentiable on all of `ℂ`.
    Split: at `s = 1` by the 2026-11-17 removable-singularity closure; at
    every `s ≠ 1` by agreement with `dirichletEtaExt` on `{1}ᶜ`. -/
theorem dirichletEtaExtFilled_differentiable :
    Differentiable ℂ dirichletEtaExtFilled := by
  intro s
  by_cases hs : s = 1
  · subst hs
    exact dirichletEtaExtFilled_differentiableAt_atOne
  · exact dirichletEtaExtFilled_differentiableAt_of_ne_one hs

/-! ## Axiom check. -/

#print axioms dirichletEtaExtFilled_differentiableAt_of_ne_one
#print axioms dirichletEtaExtFilled_differentiable

end PrincipiaTractalis.DirichletEtaExtFilledDifferentiable_2026_11_18
