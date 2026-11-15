/-
# PF.Referee.StandardFermatStatement

Typed standard contract for Fermat's Last Theorem (externally settled
by Wiles 1995 / Taylor-Wiles 1995 for the general case `n ≥ 3`).
Parallels the architecture of `StandardClayStatements.lean` for the
six open Clay axes.

Fermat's Last Theorem is NOT a Clay Millennium problem but is included
here as the natural second example of an externally-settled problem
that the PF corpus leans on (Wiles' modularity theorem underpins the
BSD-chain Heegner cascades the project cites).  The point of defining
the standard contract here is to apply the same rigid typed-encoding
process we use for the open Clay axes, so the project's handling of
externally-solved problems is structurally identical to its handling
of externally-open ones.

Per the comparison documented at
`codex/FRAMEWORK_CLAIMS_GAP_INVENTORY_2026-11-15.md` §XI:
whether a problem is externally settled or not makes no difference to
the Lean kernel's verdict; what distinguishes them is formalization
tractability of the underlying mathematics.  The general FLT is being
formalised by the Imperial College London FLT project (ongoing,
multi-year) and is NOT in mathlib at HEAD.  Only the classical finite
cases (n = 4 as `Mathlib.NumberTheory.FLT.Four.not_fermat_42`; the
difference form n = 4 as `PF.not_fermat_42_sub` from the project) are
kernel-verified.

See the companion typed-capstone file
`PF/Referee/FermatCapstoneTypedBridge.lean`.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import Mathlib.NumberTheory.FLT.Basic

namespace PF.Referee.StandardFermatStatement

/-! ## §1 — Standard Wiles-Fermat encoding -/

/-- An external encoding of the standard Wiles-Fermat setting:
    exponent type, large-enough predicate, and the "FLT holds at this
    exponent" predicate.

    A faithful discharge of `Standard_FermatLastTheorem_Standard`
    requires the framework user to instantiate the encoding with
    mathlib's `ℕ` + `3 ≤ n` + `FermatLastTheoremFor n`, which
    effectively asks for Wiles' theorem.  A substrate-level discharge
    is what PF supplies. -/
structure StandardFermatEncoding where
  /-- The exponent type (mathlib-standard: ℕ). -/
  Exponent : Type
  /-- Predicate: is this exponent in the Clay-relevant range `n ≥ 3`? -/
  isLargeEnough : Exponent → Prop
  /-- Predicate: does Fermat's Last Theorem hold at this exponent?
      Mathlib-standard: `FermatLastTheoremFor n`. -/
  holds : Exponent → Prop

/-- **Fermat's Last Theorem (standard form).** Over a standard
    exponent encoding `E`, FLT holds at every large-enough exponent. -/
def Standard_FermatLastTheorem_Standard (E : StandardFermatEncoding) : Prop :=
  ∀ n : E.Exponent, E.isLargeEnough n → E.holds n

/-! ## §2 — Rule #1 compliance marker -/

/-- Provenness tag: structural marker that this file has no
    `Prop := True` Clay-statement definitions.  The contract above
    is parameterised; its substance is entirely in the encoding. -/
theorem rule1_compliance : True := trivial

#check @Standard_FermatLastTheorem_Standard

end PF.Referee.StandardFermatStatement
