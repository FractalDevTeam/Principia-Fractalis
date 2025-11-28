import PF.RH_Equivalence
import PF_L4L.Core.Zeta

namespace PF_L4L.Ch20

open PrincipiaTractalis PF_L4L.Core

/--
Chapter 20 contract for the Riemann Hypothesis pillar.

This minimal contract records that:

* The PF canonical `riemann_zeta` is exactly mathlib's `riemannZeta`
  (via the PF_L4L core `zetaSpec`), and
* The PF canonical `riemann_hypothesis` proposition coincides with the
  standard `RiemannHypothesis` statement from mathlib.

Axiom dependency tagging (via an axiom-audit layer) will be added in a
separate module; here we only record the core mathematical identifications.
-/
structure RHContract where
  /-- PF zeta is the classical Riemann zeta from mathlib. -/
  zeta_is_mathlib : PrincipiaTractalis.riemann_zeta = zetaSpec
  /-- PF RH proposition matches the standard `RiemannHypothesis`. -/
  RH_is_classical : PrincipiaTractalis.riemann_hypothesis ↔ RiemannHypothesis

/-- The PF canonical development satisfies the minimal RH contract. -/
noncomputable def rhContractPF : RHContract :=
  { zeta_is_mathlib := riemann_zeta_eq_riemannZeta
  , RH_is_classical := by
      -- `riemann_hypothesis` is a definitionally equal alias for `RiemannHypothesis`.
      unfold PrincipiaTractalis.riemann_hypothesis
      exact Iff.rfl }

@[simp] theorem rhContractPF_zeta_is_mathlib :
    rhContractPF.zeta_is_mathlib = riemann_zeta_eq_riemannZeta := rfl

@[simp] theorem rhContractPF_RH_is_classical :
    rhContractPF.RH_is_classical =
      (by
        unfold PrincipiaTractalis.riemann_hypothesis
        exact (Iff.rfl : RiemannHypothesis ↔ RiemannHypothesis)) := rfl

end PF_L4L.Ch20
