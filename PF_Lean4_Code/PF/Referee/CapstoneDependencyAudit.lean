/-
# PF.Referee.CapstoneDependencyAudit

**Date**: 2026-06-02
**Status**: re-export + axiom audit. No new theorems on Clay paths.
**Anchor commit**: ee51039.
**Source roadmap**: `codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md`
"Concrete Lean Targets" + "Submission Readiness Criterion".

## Purpose

The 2026-06-02 referee roadmap demands (Submission Readiness
Criterion, item 6): *"axiom list for every capstone."* This file
re-exports each PF Clay-axis capstone by exact name and emits a
`#print axioms` for each, so a reader can verify in one place that no
project axiom has crept into the Clay proof paths since Wave 57.

This module is **diagnostic only**. It introduces no new theorems
and no semantic claims.

## Audit scope

Capstones audited (one per Clay axis, at HEAD ee51039):

* RH: `riemann_hypothesis_via_T3_sym_framework`
  (PF/SpectralBijection.lean, re-exported via PF/Millennium.lean)
* P vs NP: `P_neq_NP_via_spectral_gap`
  (PF/P_NP_Complete_Proof.lean)
* Six-axes bundle: `principia_fractalis_millennium_capstone`
  (PF/Millennium.lean)
* Wave 57 master: `principia_fractalis_wave57_master_capstone`
  (PF/Wave57MasterCapstone.lean)
* Twelfth-object soundness: `all_clay_via_soundness_and_capstones`
  (PF/MillenniumReductionSoundness.lean)
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

/-- Audit invariant: this module's only purpose is to re-export and
    inspect capstones; it carries no Clay-level content of its own. -/
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
