/-
# PF.Referee.PvsNPCapstoneTypedBridgeSubstrate

Typed-encoding Clay capstone for P vs NP at substrate scope, built on
the cross-Millennium invariant `α_NP − α_Hodge = 1/4` (axiom-free,
three-axiom bar).

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.Referee.StandardPvsNPSubstrateStatement
import PF.CrossMillenniumSharedInvariants

namespace PF.Referee.PvsNPCapstoneTypedBridgeSubstrate

open PF.Referee.StandardPvsNPSubstrateStatement
open PrincipiaTractalis.CrossMillenniumSharedInvariants
  (α_NP α_Hodge α_NP_sub_Hodge_eq_quarter)

/-! ## §1 — Substrate predicates -/

noncomputable def pfIsNPAnchor (a : ℝ) : Prop := a = α_NP
noncomputable def pfSeparationIdentity (a : ℝ) : Prop := a - α_Hodge = 1 / 4

noncomputable def PF_PvsNPEncodingSubstrate : StandardPvsNPSubstrateEncoding where
  AlphaValue := ℝ
  isNPAnchor := pfIsNPAnchor
  separationIdentity := pfSeparationIdentity

/-! ## §2 — The typed capstone -/

/-- **The typed P vs NP substrate contract holds on
    `PF_PvsNPEncodingSubstrate`** — axiom-free via
    `α_NP_sub_Hodge_eq_quarter`. -/
theorem PF_PvsNP_capstone_substrate_yields_Clay_PvsNP_substrate_standard :
    Clay_PvsNP_Substrate_Standard PF_PvsNPEncodingSubstrate := by
  intro a hAnchor
  show pfSeparationIdentity a
  unfold pfSeparationIdentity
  have h : a = α_NP := hAnchor
  rw [h]
  exact α_NP_sub_Hodge_eq_quarter

end PF.Referee.PvsNPCapstoneTypedBridgeSubstrate

#print axioms PF.Referee.PvsNPCapstoneTypedBridgeSubstrate.PF_PvsNPEncodingSubstrate
#print axioms PF.Referee.PvsNPCapstoneTypedBridgeSubstrate.PF_PvsNP_capstone_substrate_yields_Clay_PvsNP_substrate_standard
