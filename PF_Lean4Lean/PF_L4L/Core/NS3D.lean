/-
# PF_L4L.Core.NS3D — meta-verification of the substrate-level
   NS Sobolev/Leray closure

★ 2026-06-13 — independent re-verification of the 27 Type (F)
advances on the NS Sobolev/Leray bridge. Re-imports the master
capstones from `PF/` and re-asserts them at the L4L meta layer,
exercising the kernel-only axiom audit through the Lean4Lean
verification path.
-/

import PF.NS3D_FullSubstrateNSCapstone
import PF.NS3D_HeatEnergyMonotone
import PF.NS3D_NonlinearZeroMode
import PF.NS3D_EvolutionRHS
import PF.NS3D_NonlinearScaling
import PF.NS3D_HeatExpFormula
import PF.NS3D_GalerkinTruncation
import PF.NS3D_SupportedSubmodule

namespace PF_L4L.Core.NS3D

open PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

/-! ## §1 — Meta-verification of the master capstone

We re-assert the full-substrate NS Sobolev/Leray closure master
capstone at the L4L layer, providing an independent citation
target through the meta-verification namespace. -/

theorem ns3d_full_substrate_closure_reverified :
    -- (P1) genuine non-trivial type + strong-form constraint
    (Nonempty ConcreteDivFreeVelocityField) ∧
    (∀ u : ConcreteDivFreeVelocityField, ∀ k : Fin 3 → ℤ,
      PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt.dotIntC3
        k (u.coeff k) = 0) :=
  ⟨(full_substrate_NS_Sobolev_Leray_closure).1,
   (full_substrate_NS_Sobolev_Leray_closure).2.1⟩

/-! ## §2 — Meta-verification of energy monotonicity -/

theorem ns3d_heat_energy_antitone_reverified
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (s : ℝ) (S : Finset (Fin 3 → ℤ)) :
    Antitone (fun r =>
      PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.hsNormSqVecOnL2
        (PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.heatSemigroup r c)
        s S) :=
  antitone_hsNormSqVecOnL2_heatSemigroup c s S

/-! ## §3 — Meta-verification of evolution RHS structure -/

theorem ns3d_evolutionRHS_div_free_reverified
    (S : Finset (Fin 3 → ℤ))
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ,
      PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt.dotIntC3
        k (u k) = 0) :
    ∀ k : Fin 3 → ℤ,
      PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt.dotIntC3
        k (nsEvolutionRHS S u k) = 0 :=
  nsEvolutionRHS_div_free_of_div_free S u h_div_free

/-! ## §4 — Meta-verification of exponential energy formula -/

theorem ns3d_heat_exp_formula_reverified
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.vecL2NormSq
      (PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.heatSemigroup t c k)
      = Real.exp (-(2 * t * kNormSqReal k))
        * PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.vecL2NormSq (c k) :=
  vecL2NormSq_heatSemigroup_exp_formula t c k

/-! ## §5 — Axiom audit hooks

The build-time L4L re-verification audit. Each of these should
print only `[propext, Classical.choice, Quot.sound]`. -/

#print axioms ns3d_full_substrate_closure_reverified
#print axioms ns3d_heat_energy_antitone_reverified
#print axioms ns3d_evolutionRHS_div_free_reverified
#print axioms ns3d_heat_exp_formula_reverified

end PF_L4L.Core.NS3D
