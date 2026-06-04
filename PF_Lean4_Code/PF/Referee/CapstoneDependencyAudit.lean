/-
# PF.Referee.CapstoneDependencyAudit

Diagnostic re-export module: emits `#print axioms` for every Clay-axis
capstone, so a reader can verify in one file that no project axiom has
crept into any Clay proof path. No new theorems, no semantic claims.

Source roadmap: `codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md`
(Submission Readiness Criterion, item 6: "axiom list for every capstone").
-/

import PF.Millennium
import PF.MillenniumReductionSoundness
import PF.Wave57MasterCapstone
import PF.Referee.RHCapstoneTypedBridge
import PF.Referee.PNPCapstoneTypedBridge
import PF.Referee.YMCapstoneTypedBridge
import PF.Referee.BSDCapstoneTypedBridge
import PF.Referee.HodgeCapstoneTypedBridge
import PF.Consciousness.TimelessFieldConcreteMorphism
import PF.Referee.PFUnifiedSubstrate
import PF.Referee.FractalMathematicsCore
import PF.Analytic.T3SymMercerTailT3SymDischarge
import PF.BSD_LSeriesAbsConvergenceDischarge
import PF.BSD_WilesModularityAnalyticContinuationDischarge
import PF.Analytic.JonquieresGlobalIdentityDischarge
import PF.CrossMillenniumDerivedConsequences

namespace PF.Referee.CapstoneDependencyAudit

/-- Provenness tag (Rule #1: ProvennessTag) — this module re-exports
    and inspects capstones; carries no Clay-level content of its own. -/
def capstoneAudit_isInspectionOnly : Prop := True

theorem capstoneAudit_isInspectionOnly_holds :
    capstoneAudit_isInspectionOnly := trivial

/-! ## Per-capstone axiom inspection -/

#check @PrincipiaTractalis.principia_fractalis_millennium_capstone
#check @PrincipiaTractalis.all_clay_via_soundness_and_capstones
#check @PrincipiaTractalis.principia_fractalis_wave57_master_capstone

#print axioms PrincipiaTractalis.principia_fractalis_millennium_capstone
#print axioms PrincipiaTractalis.all_clay_via_soundness_and_capstones
#print axioms PrincipiaTractalis.principia_fractalis_wave57_master_capstone

/-! ## Per-typed-bridge axiom inspection (HEAD 96faade additions)

The four genuine typed-bridge witnesses (YM finite-dim, BSD over Fin 6,
Hodge multi-substrate, plus the RH/PNP retype-only bridges) and the
Ch 4 Timeless Field capstone. Each is inspected for axiom dependencies. -/

#check @PF.Referee.YMCapstoneTypedBridge.PF_YM_capstone_yields_Clay_YangMills_standard
#check @PF.Referee.BSDCapstoneTypedBridge.PF_BSD_capstone_yields_Clay_BSD_standard
#check @PF.Referee.HodgeCapstoneTypedBridge.PF_Hodge_multisubstrate_capstone
#check @PrincipiaTractalis.TimelessField.timelessFieldExistenceClaim_holds

#print axioms PF.Referee.YMCapstoneTypedBridge.PF_YM_capstone_yields_Clay_YangMills_standard
#print axioms PF.Referee.BSDCapstoneTypedBridge.PF_BSD_capstone_yields_Clay_BSD_standard
#print axioms PF.Referee.HodgeCapstoneTypedBridge.PF_Hodge_multisubstrate_capstone
#print axioms PrincipiaTractalis.TimelessField.timelessFieldExistenceClaim_holds

/-! ## HEAD 22e8802 additions — fresh attack results

Six new audit targets reflecting the structural-strengthening
commits since HEAD ee51039. -/

#check @PF.Referee.PFUnifiedSubstrate.unifiedSubstrateUnification_holds
#check @PF.Referee.FractalMathematicsCore.fractalMathematicsCore_realized
-- Note: PF.Referee.PFCompleteFrameworkCapstone.pfCompleteFramework_realized
-- imports this audit module transitively; auditing it here would create a
-- build cycle. Audit it directly from PFCompleteFrameworkCapstone.lean's
-- own #print axioms call.
#check @PrincipiaTractalis.T3SymMercerTail_of_compact_at_T3_sym_CLM
#check @PrincipiaTractalis.BSD_LSeriesAbsConvergenceDischarge.lSeriesSummable_of_hasseTower_on_open_halfplane
#check @PrincipiaTractalis.BSD_WilesModularityAnalyticContinuationDischarge.wave57BSD_A4_strengthened
#check @PrincipiaTractalis.Analytic.Sheaf.literal_iff_reduced_and_negReal_strong
#check @PF.CrossMillenniumDerivedConsequences.cross_millennium_derived_capstone

#print axioms PF.Referee.PFUnifiedSubstrate.unifiedSubstrateUnification_holds
#print axioms PF.Referee.FractalMathematicsCore.fractalMathematicsCore_realized
#print axioms PrincipiaTractalis.T3SymMercerTail_of_compact_at_T3_sym_CLM
#print axioms PrincipiaTractalis.BSD_LSeriesAbsConvergenceDischarge.lSeriesSummable_of_hasseTower_on_open_halfplane
#print axioms PrincipiaTractalis.BSD_WilesModularityAnalyticContinuationDischarge.wave57BSD_A4_strengthened
#print axioms PrincipiaTractalis.Analytic.Sheaf.literal_iff_reduced_and_negReal_strong
#print axioms PF.CrossMillenniumDerivedConsequences.cross_millennium_derived_capstone

end PF.Referee.CapstoneDependencyAudit
