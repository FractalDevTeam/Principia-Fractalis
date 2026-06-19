/-
# PF_L4L.Referee.Fefferman2000_LiteralClayNS_2026_06_19_Reverification

External Lean4Lean re-verification of the 2026-06-19 literal Clay
NS statement (Fefferman 2000) formalization plus the substrate-to-
literal bridge.
-/

import PF.NavierStokes.Fefferman2000_LiteralClayNS3D_Statement_2026_06_19

namespace PF_L4L.Referee

def literalClayNSSubstrateBridgeAuditTrail_reverified :=
  @PF.NavierStokes.Fefferman2000_LiteralClayNS3D_Statement_2026_06_19.literal_clay_NS_substrate_bridge_audit_trail

#print axioms literalClayNSSubstrateBridgeAuditTrail_reverified

def substrateToLiteralClayNSBridgeConditional_reverified :=
  @PF.NavierStokes.Fefferman2000_LiteralClayNS3D_Statement_2026_06_19.substrate_to_literal_clay_NS_bridge_conditional

#print axioms substrateToLiteralClayNSBridgeConditional_reverified

end PF_L4L.Referee
