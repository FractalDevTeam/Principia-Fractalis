/-
# PF_L4L — Meta-Verification Layer (Third Certification Layer)

This is the root module for the Principia Fractalis Lean4Lean meta-checker.
It imports the L4L modules that successfully re-verify portions of the
canonical `PF_Lean4_Code/PF/` library against an independent contract layer.

## Build status (2026-06-04)

REACHABLE (build clean, depend only on `propext, Classical.choice, Quot.sound`):
  * PF_L4L.Core.SpectralGap — re-verifies PF.SpectralGap (lambda_0_P / lambda_0_NP / spectral_gap)
  * PF_L4L.Ch21.PNP        — re-verifies PF.P_NP_Equivalence (conditional on PolylogEigenvalueConjecture)

GATED (currently un-buildable; see README.md "Architectural Gap" section):
  * PF_L4L.Core.Resonance, PF_L4L.Core.Zeta, PF_L4L.Core.AxiomAudit
  * PF_L4L.Ch20.RH, PF_L4L.Ch23.YM, PF_L4L.Ch24.BSD
  These depend on top-level `RH_Equivalence`, `YM_Equivalence`, `BSD_Equivalence`,
  `Axioms`, `ConsciousnessCore` files that are no longer part of the `PF` lake
  library namespace (they live at PF_Lean4_Code/ root, not PF_Lean4_Code/PF/).
  Restoring requires modifying PF_Lean4_Code/lakefile.toml to expose them, which
  is out of scope for this verification layer.
-/

-- Reachable modules: actively re-verify portions of PF_Lean4_Code/PF/
import PF_L4L.Core.SpectralGap
import PF_L4L.Ch21.PNP
import PF_L4L.Referee.FlagshipReverification
import PF_L4L.Referee.V2AndMasterReverification

-- Gated modules: kept in the source tree for the future PF-namespace
-- refactor; they do NOT participate in the current build.
-- import PF_L4L.Core.Resonance
-- import PF_L4L.Core.Zeta
-- import PF_L4L.Core.AxiomAudit
-- import PF_L4L.Ch20.RH
-- import PF_L4L.Ch23.YM
-- import PF_L4L.Ch24.BSD
