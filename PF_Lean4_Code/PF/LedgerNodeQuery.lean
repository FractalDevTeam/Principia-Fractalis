/-
# Ledger node query — NOT a result module.

Directive §3 requires the dependency ledger to record, per load-bearing node:
source file, FQN, deps, `#print axioms`, closed-term status, rebuilt-from-source
status. This module emits the kernel-side half of that (axioms + closed-term)
for the ledger's theorem nodes, so those fields are filled from the kernel rather
than asserted.

It proves nothing and is not part of any chain. It is a query.
-/

import PF.PrincipiaFractalisMillenniumSupremeCapstoneUniversal_r301
import PF.AlphaWebDegreesOfFreedom_r124
import PF.AlphaSkeletonUniqueness_r128
import PF.SubstrateTheoremContent_r216
import PF.AlphaFromSubstrateKTheory_r123
import PF.AlphaL5PiScalingObstruction_r332
import PF.UnifiedTheoryPremiseAudit_r333

/-! ## Layer 2 — α-skeleton -/
#print axioms PrincipiaTractalis.AlphaWebDegreesOfFreedom.alpha_web_admits_every_positive_BSD
#print axioms PrincipiaTractalis.AlphaFromSubstrateKTheory.alpha_table_memZ13_verdict
#print axioms PrincipiaTractalis.AlphaL5PiScalingObstruction.pi_not_ktheoretic_ratio

/-! ## Layer 4 — top-level -/
#print axioms PrincipiaTractalis.PrincipiaFractalisMillenniumSupremeCapstoneUniversal.principia_fractalis_millennium_supreme_capstone_universal_at_HEAD
#print axioms PrincipiaTractalis.UnifiedTheoryPremiseAudit.rh_from_bulletproof_bundle_by_application

/-! ## Closed-term status — `@` shows every binder; a closed term shows none. -/
#check @PrincipiaTractalis.AlphaL5PiScalingObstruction.pi_not_ktheoretic_ratio
#check @PrincipiaTractalis.AlphaWebDegreesOfFreedom.alpha_web_admits_every_positive_BSD
#check @PrincipiaTractalis.PrincipiaFractalisMillenniumSupremeCapstoneUniversal.principia_fractalis_millennium_supreme_capstone_universal_at_HEAD
#check @PrincipiaTractalis.AlphaFromSubstrateKTheory.alpha_table_memZ13_verdict
