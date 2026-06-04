import PF.P_NP_Equivalence
import PF_L4L.Core.SpectralGap

namespace PF_L4L.Ch21

open PrincipiaTractalis PF_L4L.Core

/--
Chapter 21 contract for the P vs NP pillar.

This minimal contract records that:

* The spectral gap data used in the proof is exactly the PF_L4L core
  `SpectralGapSpec` instance `spectralGapSpecPF`, and
* The PF canonical theorem `P_neq_NP_via_spectral_gap` provides the
  complexity separation result.

A detailed axiom audit (which PF assumptions are used) will be added in
separate PF_L4L modules; here we focus on the core spectral-contract link.
-/
structure PNPContract where
  /-- Spectral gap specification used for the P vs NP proof. -/
  gapSpec : SpectralGapSpec
  /-- The abstract Delta used in PF canonical code is this gap. -/
  Delta_def : PrincipiaTractalis.Delta = gapSpec.gap
  /-- The main separation result: P ≠ NP via the spectral gap. -/
  P_neq_NP_result : PrincipiaTractalis.P_neq_NP_def

/-- The PF canonical development satisfies the minimal P vs NP contract. -/
noncomputable def pnpContractPF : PNPContract :=
  { gapSpec := spectralGapSpecPF
  , Delta_def := by
      -- Delta is just the canonical spectral_gap, which equals gapSpec.gap.
      unfold PrincipiaTractalis.Delta
      -- goal: spectral_gap = spectralGapSpecPF.gap
      -- rewrite the RHS using the core spec lemma
      simpa [spectralGapSpecPF_gap] using (rfl : spectral_gap = spectral_gap)
  , P_neq_NP_result := PrincipiaTractalis.P_neq_NP_via_spectral_gap }

@[simp] theorem pnpContractPF_gapSpec :
    pnpContractPF.gapSpec = spectralGapSpecPF := rfl

@[simp] theorem pnpContractPF_PneqNP :
    pnpContractPF.P_neq_NP_result = PrincipiaTractalis.P_neq_NP_via_spectral_gap := rfl

end PF_L4L.Ch21
