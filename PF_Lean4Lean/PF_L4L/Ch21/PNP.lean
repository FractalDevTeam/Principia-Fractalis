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
  complexity separation result UNDER the `PolylogEigenvalueConjecture`
  hypothesis (Wave 47+ Clay-precision form: enum-level
  hypothesis is required to bridge to the literal Clay separation;
  see `PF.TuringEncoding.PNPClassSeparationPrecisionBridge`).

A detailed axiom audit (which PF assumptions are used) will be added in
separate PF_L4L modules; here we focus on the core spectral-contract link.

API drift note (2026-06-03): `P_neq_NP_via_spectral_gap` now takes a
`PolylogEigenvalueConjecture` hypothesis (was unconditional in the
pre-2026-04-28 statement). The contract is updated accordingly; the
hypothesis is exposed as a Prop field of the structure.
-/
structure PNPContract where
  /-- Spectral gap specification used for the P vs NP proof. -/
  gapSpec : SpectralGapSpec
  /-- The abstract Delta used in PF canonical code is this gap. -/
  Delta_def : PrincipiaTractalis.Delta = gapSpec.gap
  /-- The main separation result: P ≠ NP via the spectral gap, conditional
      on the polylog eigenvalue conjecture. -/
  P_neq_NP_result :
    TuringEncoding.PolylogEigenvalueConjecture → PrincipiaTractalis.P_neq_NP_def

/-- The PF canonical development satisfies the minimal P vs NP contract. -/
noncomputable def pnpContractPF : PNPContract :=
  { gapSpec := spectralGapSpecPF
  , Delta_def := by
      -- Delta is just the canonical spectral_gap, which equals gapSpec.gap
      -- (definitional unfolding via `spectralGapSpecPF_gap`).
      unfold PrincipiaTractalis.Delta
      simp [spectralGapSpecPF_gap]
  , P_neq_NP_result := PrincipiaTractalis.P_neq_NP_via_spectral_gap }

@[simp] theorem pnpContractPF_gapSpec :
    pnpContractPF.gapSpec = spectralGapSpecPF := rfl

-- Build-time L4L re-verification audit hook.
#print axioms pnpContractPF

end PF_L4L.Ch21
