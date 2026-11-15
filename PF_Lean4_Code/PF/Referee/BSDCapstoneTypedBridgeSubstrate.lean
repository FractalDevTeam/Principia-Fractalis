/-
# PF.Referee.BSDCapstoneTypedBridgeSubstrate

Typed-encoding Clay capstone for BSD at substrate scope, built on the
cross-Millennium invariant `α_NS = 2 · α_BSD` (axiom-free, three-axiom bar).

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.Referee.StandardBSDSubstrateStatement
import PF.CrossMillenniumSharedInvariants

namespace PF.Referee.BSDCapstoneTypedBridgeSubstrate

open PF.Referee.StandardBSDSubstrateStatement
open PrincipiaTractalis.CrossMillenniumSharedInvariants
  (α_NS α_BSD α_NS_eq_two_α_BSD)

/-! ## §1 — Substrate predicates -/

noncomputable def pfIsBSDAnchor (a : ℝ) : Prop := a = α_BSD
noncomputable def pfAnchorDoubling (a : ℝ) : Prop := α_NS = 2 * a

noncomputable def PF_BSDEncodingSubstrate : StandardBSDSubstrateEncoding where
  AlphaValue := ℝ
  isBSDAnchor := pfIsBSDAnchor
  anchorDoubling := pfAnchorDoubling

/-! ## §2 — The typed capstone -/

/-- **The typed BSD substrate contract holds on `PF_BSDEncodingSubstrate`**
    — axiom-free via `α_NS_eq_two_α_BSD`. -/
theorem PF_BSD_capstone_substrate_yields_Clay_BSD_substrate_standard :
    Clay_BSD_Substrate_Standard PF_BSDEncodingSubstrate := by
  intro a hAnchor
  show pfAnchorDoubling a
  unfold pfAnchorDoubling
  have h : a = α_BSD := hAnchor
  rw [h]
  exact α_NS_eq_two_α_BSD

end PF.Referee.BSDCapstoneTypedBridgeSubstrate

#print axioms PF.Referee.BSDCapstoneTypedBridgeSubstrate.PF_BSDEncodingSubstrate
#print axioms PF.Referee.BSDCapstoneTypedBridgeSubstrate.PF_BSD_capstone_substrate_yields_Clay_BSD_substrate_standard
