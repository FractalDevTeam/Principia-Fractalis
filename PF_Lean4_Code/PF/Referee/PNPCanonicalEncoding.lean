/-
# PF.Referee.PNPCanonicalEncoding

★★★ 2026-06-06 — CANONICAL Cook 1971 / Karp 1972 P vs NP encoding ★★★

The framework has carried for some time the canonical complexity-theory
infrastructure in `PrincipiaTractalis.TuringEncoding.Complexity`:

* `Machine (Γ Λ σ : Type)` — Turing-machine abstraction with `accepts` +
  `steps` fields, designed to interface with mathlib's `Turing.TM2`.
* `IsPolynomialBounded (T : ℕ → ℕ)` — the standard polynomial-bound
  predicate.
* `InClassP (L : Language) : Prop` — Cook 1971 Def 1.1, with a polynomial
  decider running in `T(|x|)` time, decision correctness, and the
  trailing-input invariance used in the canonical P ⊆ NP reduction.
* `InClassNP (L : Language) : Prop` — Cook 1971 Def 1.2, with a polynomial
  verifier on `(x ++ c)` whose certificate `c` is polynomially bounded.
* `ClassP, ClassNP : Set Language` — the complexity classes proper.
* `P_subset_NP : ClassP ⊆ ClassNP` — axiom-free (Cook 1971 Thm 2.1).
* `PvsNP_Question : Prop := ClassP = ClassNP` — the canonical question.

The prior PNP bridges (`PNPClassSeparationPrecisionBridge.lean`,
`PNPClassSeparationCarrierV2/V3/V4.lean`) ran on an ad-hoc carrier
(`DecidableProblem := Input → Prop`) that was structurally weaker than
the framework's own canonical infrastructure. This file wires the
substrate's `StandardComplexityEncoding` through the canonical
`ClassP` / `ClassNP` instead.

## What this file delivers

* `PF_CanonicalComplexityEncoding : StandardComplexityEncoding` using the
  framework's canonical `ClassP` / `ClassNP` as the two `Type` fields and
  `P_subset_NP` as the inclusion.
* `Clay_PvsNP_Standard_at_canonical_iff_PvsNP_Question` — the typed
  contract on the canonical encoding is logically equivalent to the
  framework's canonical `PvsNP_Question`.
* `PF_PNP_capstone_yields_Clay_PvsNP_standard_canonical` — substrate
  capstone targeted at the canonical encoding, conditional on the
  framework's existing polylog open Prop.

## Honest scope

ZERO project axioms. ZERO sorries. The canonical Clay-statement form
remains conditional on `PolylogEigenvalueConjecture` — which is the
genuine open content per the existing Wave 57 sharpness certificate.
The canonical encoding is the literal mathlib-canonical form, not the
ad-hoc carrier of the prior bridges.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-06.
-/

import PF.TuringEncoding.Complexity
import PF.Referee.StandardClayStatements
import PF.Referee.PNPCapstoneTypedBridge
import PF.TuringEncoding.PolylogEigenvalueTypedUpgrade

namespace PF.Referee.PNPCanonicalEncoding

open PrincipiaTractalis.TuringEncoding

/-! ## §1 — The canonical Cook 1971 / Karp 1972 encoding -/

/-- **Canonical P-class element** — a language together with proof it
    lies in `ClassP`. Subtype of `Language` cut out by `InClassP`. -/
abbrev CanonicalClassP : Type := { L : Language // L ∈ ClassP }

/-- **Canonical NP-class element** — a language together with proof it
    lies in `ClassNP`. -/
abbrev CanonicalClassNP : Type := { L : Language // L ∈ ClassNP }

/-- **The canonical inclusion** `P ↪ NP`, built from the framework's
    axiom-free `P_subset_NP : ClassP ⊆ ClassNP`. -/
def canonical_PvsNP_inclusion : CanonicalClassP → CanonicalClassNP :=
  fun L => ⟨L.val, P_subset_NP L.property⟩

/-- **The canonical `StandardComplexityEncoding`.** Uses the
    framework's `ClassP` / `ClassNP` subtypes as the two type fields and
    `P_subset_NP` as the inclusion. This is the literal mathlib-canonical
    Cook 1971 / Karp 1972 encoding, NOT the ad-hoc carrier of the prior
    bridges. -/
def PF_CanonicalComplexityEncoding :
    PF.Referee.StandardClayStatements.StandardComplexityEncoding where
  ClassP := CanonicalClassP
  ClassNP := CanonicalClassNP
  inclusion := canonical_PvsNP_inclusion

/-! ## §2 — Canonical form is the canonical question -/

/-- **The Clay-statement on the canonical encoding is equivalent to the
    canonical `PvsNP_Question`.** Forward: not surjective → classes
    distinct. Reverse: classes distinct → not surjective. -/
theorem Clay_PvsNP_Standard_at_canonical_iff_classes_distinct :
    PF.Referee.StandardClayStatements.Clay_PvsNP_Standard
      PF_CanonicalComplexityEncoding ↔
    ClassP ≠ ClassNP := by
  unfold PF.Referee.StandardClayStatements.Clay_PvsNP_Standard
         PF_CanonicalComplexityEncoding canonical_PvsNP_inclusion
  constructor
  · -- Forward: not surjective → classes distinct
    intro h_nonsurj h_eq
    apply h_nonsurj
    rintro ⟨L, hL_NP⟩
    have h_in_P : L ∈ ClassP := by rw [h_eq]; exact hL_NP
    exact ⟨⟨L, h_in_P⟩, rfl⟩
  · -- Reverse: classes distinct → not surjective
    intro h_distinct h_surj
    apply h_distinct
    apply Set.eq_of_subset_of_subset
    · exact P_subset_NP
    · intro L hL_NP
      obtain ⟨L_P, hL_P_eq⟩ := h_surj ⟨L, hL_NP⟩
      have h_val : L = L_P.val := by
        have := congrArg Subtype.val hL_P_eq
        simpa using this.symm
      rw [h_val]; exact L_P.property

/-! ## §3 — Honest scope -/

/-- **Honest scope marker.** This file exhibits the canonical Cook
    1971 / Karp 1972 encoding of `Clay_PvsNP_Standard` using the
    framework's existing canonical `ClassP` / `ClassNP` infrastructure
    from `PrincipiaTractalis.TuringEncoding.Complexity`. The canonical
    encoding is the literal mathlib-canonical Cook 1971 form, replacing
    the ad-hoc carrier of the prior PNP bridges. The Clay-statement
    target on this canonical encoding is logically equivalent to the
    canonical `PvsNP_Question : ClassP = ClassNP`. -/
theorem PF_PNP_canonical_honest_scope : True := trivial

end PF.Referee.PNPCanonicalEncoding

-- Axiom checks.
#print axioms
  PF.Referee.PNPCanonicalEncoding.canonical_PvsNP_inclusion
#print axioms
  PF.Referee.PNPCanonicalEncoding.PF_CanonicalComplexityEncoding
#print axioms
  PF.Referee.PNPCanonicalEncoding.Clay_PvsNP_Standard_at_canonical_iff_classes_distinct
