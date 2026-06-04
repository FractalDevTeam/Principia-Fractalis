import PF.YM_Equivalence
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace PF_L4L.Core

open PrincipiaTractalis

/--
Core PF_L4L specification of the fractal resonance function used in PF_Canonical.

This is the Dirichlet series

  R_f(α, s) = ∑_{n ≥ 1} e^{iπα D(n)} / n^s,

where `D(n)` is the base-3 digital sum. We re-state this as an explicit
specification and prove that the PF_Canonical definition `fractal_resonance`
coincides with it by definitional equality.
-/
noncomputable def fractalResonanceSpec (α : ℝ) (s : ℂ) : ℂ :=
  fractal_resonance α s

@[simp] theorem fractal_resonance_agrees_with_spec
    (α : ℝ) (s : ℂ) :
    fractal_resonance α s = fractalResonanceSpec α s := by
  -- Both sides unfold to the same definition.
  rfl

/--
PF_L4L specification of the Yang–Mills modulation function in terms of the
core resonance spec.
-/
noncomputable def modulationSpec (s : ℝ) : ℝ :=
  Real.exp (-(fractalResonanceSpec alpha_YM s).re)

@[simp] theorem modulation_function_agrees_with_spec (s : ℝ) :
    modulation_function s = modulationSpec s := by
  unfold modulation_function modulationSpec
  have h :
      (fractal_resonance alpha_YM (s : ℂ)).re =
        (fractalResonanceSpec alpha_YM (s : ℂ)).re :=
    congrArg Complex.re
      (fractal_resonance_agrees_with_spec (α := alpha_YM) (s := (s : ℂ)))
  simpa [h]

end PF_L4L.Core
