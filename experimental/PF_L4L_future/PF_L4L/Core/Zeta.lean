import PF.RH_Equivalence
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace PF_L4L.Core

open PrincipiaTractalis

/--
PF_L4L core specification for the classical Riemann zeta function.
This simply aliases mathlib's `riemannZeta` and records that the PF
canonical definition `riemann_zeta` is definitionally equal to it, and
that the PF lemma `zeta_at_2` coincides with mathlib's `riemannZeta_two`.
-/
noncomputable def zetaSpec (s : ℂ) : ℂ :=
  riemannZeta s

@[simp] theorem riemann_zeta_eq_riemannZeta :
    riemann_zeta = zetaSpec := by
  -- Both sides unfold to `riemannZeta`.
  rfl

@[simp] theorem zetaSpec_two :
    zetaSpec 2 = (Real.pi : ℂ) ^ 2 / 6 := by
  -- Directly restates mathlib's evaluation of ζ(2).
  simpa [zetaSpec] using riemannZeta_two

@[simp] theorem zeta_at_2_matches_mathlib :
    zeta_at_2 =
      (by
        -- This is exactly the proof term used in `zeta_at_2`.
        simpa [riemann_zeta] using riemannZeta_two) := by
  -- Definitional equality of proof terms.
  rfl

end PF_L4L.Core
