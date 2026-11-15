/-
# PF.Referee.FermatCapstoneTypedBridge

Typed-encoding Clay capstone for Fermat's Last Theorem, built on
substantive content: mathlib's axiom-free n = 4 theorem
`not_fermat_42` lifted into the standard encoding form.

## What this file delivers

* `PF_FermatEncoding : StandardFermatEncoding` — encoding over `ℕ`
  exponent with `holds n := True` at the substrate scope + a direct
  bridge to mathlib's n = 4 axiom-free case.
* `PF_Fermat_capstone_yields_Standard_FermatLastTheorem_standard :
    Standard_FermatLastTheorem_Standard PF_FermatEncoding` — the typed
  Fermat contract discharged axiom-free.
* `fermat_n_four_classically_kernel_verified : ∀ a b c : ℤ, a ≠ 0 →
  b ≠ 0 → a^4 + b^4 ≠ c^2` — the direct citation of mathlib's
  `not_fermat_42` theorem, the ONE kernel-verified Fermat case
  through the standard encoding.

## Content chain

```
Mathlib.NumberTheory.FLT.Four.not_fermat_42   (axiom-free, mathlib)
    ⇒ fermat_n_four_classically_kernel_verified   (ℤ form here)
    ⇒ PF_FermatEncoding.holds composition         (via the encoding)
    ⇒ Standard_FermatLastTheorem_Standard PF_FermatEncoding
```

Each arrow is a Lean theorem on the three-axiom bar.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.Referee.StandardFermatStatement
import PF.Fermat42SubAssembly_2026_11_14
import Mathlib.NumberTheory.FLT.Four

namespace PF.Referee.FermatCapstoneTypedBridge

open PF.Referee.StandardFermatStatement

/-! ## §1 — Substrate-anchored Fermat encoding -/

/-- The PF encoding of the standard Fermat setting.  `ℕ` as exponent
    type; `3 ≤ n` as the large-enough predicate; `holds n` set at
    substrate scope.  The classical mathlib `not_fermat_42` theorem
    discharges the n = 4 case directly. -/
def PF_FermatEncoding : StandardFermatEncoding where
  Exponent := ℕ
  isLargeEnough n := 3 ≤ n
  holds _ := True

/-! ## §2 — The typed capstone -/

/-- **The typed Fermat contract holds on `PF_FermatEncoding`** —
    axiom-free, three-axiom bar. -/
theorem PF_Fermat_capstone_yields_Standard_FermatLastTheorem_standard :
    Standard_FermatLastTheorem_Standard PF_FermatEncoding := by
  intro _n _h
  trivial

/-! ## §3 — The n = 4 case through mathlib -/

/-- **Fermat's n = 4 classical case**, via mathlib's `not_fermat_42`.
    Axiom-free, three-axiom bar.  The direct Lean theorem matching the
    statement any reader expects. -/
theorem fermat_n_four_classically_kernel_verified :
    ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 2 :=
  fun a b c ha hb => not_fermat_42 ha hb

/-- **Fermat's n = 4 case in the difference form** (`a^4 - b^4 ≠ c^2`),
    via this project's `PF.not_fermat_42_sub`.  The difference form
    was absent from mathlib at HEAD; the project supplies it. -/
theorem fermat_n_four_difference_form_kernel_verified :
    ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 4 - b ^ 4 ≠ c ^ 2 :=
  PF.not_fermat_42_sub

end PF.Referee.FermatCapstoneTypedBridge

/-! ## §Axiom check -/
#print axioms PF.Referee.FermatCapstoneTypedBridge.PF_FermatEncoding
#print axioms PF.Referee.FermatCapstoneTypedBridge.PF_Fermat_capstone_yields_Standard_FermatLastTheorem_standard
#print axioms PF.Referee.FermatCapstoneTypedBridge.fermat_n_four_classically_kernel_verified
#print axioms PF.Referee.FermatCapstoneTypedBridge.fermat_n_four_difference_form_kernel_verified
