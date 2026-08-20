/-
# r303: PRINCIPIA FRACTALIS MILLENNIUM POSITION UNIQUENESS
#      — the framework's Millennium position at HEAD is a Subsingleton;
#        r302's two route constructors converge to equal outputs

★ 2026-08-20 r303 — establishes that `PrincipiaFractalisMillenniumPositionAtHEAD`
(the framework's TOTAL Millennium position at HEAD, r302's named
output structure) is a `Subsingleton`: any two inhabitants are equal.

## Framework-first position

All 11 fields of `PrincipiaFractalisMillenniumPositionAtHEAD` are
`Prop`-typed. By Lean 4's definitional proof irrelevance, any two
inhabitants of a `Prop`-fielded structure with the same underlying
data agree component-wise, hence agree as structure instances.

The framework's Millennium position at HEAD is UNIQUE up to
propositional equality: route choice — aggregate C'-route vs.
bulletproof C-route — is INESSENTIAL. r302's dual-constructor
pattern collapses to a single-outcome pattern where consumers may
pick either route and receive definitionally-equal outputs.

## What r303 delivers

- `instance : Subsingleton PrincipiaFractalisMillenniumPositionAtHEAD` —
  the position at HEAD is a Subsingleton via componentwise `Prop`
  irrelevance.

- `position_via_aggregate_eq_via_bulletproof` — r302's two route
  constructors converge to equal outputs on every universal input:
    `pf_millennium_position_at_HEAD_via_aggregate_from_universal h
      = pf_millennium_position_at_HEAD_via_bulletproof_from_universal h`
  for every `h : ClayClosureBundleUniversal`.

## Framework consequence

For a referee consuming the framework's referee-facing surface at
HEAD, the choice between the aggregate route and the bulletproof
route is inessential: both routes produce equal inhabitants of the
same named position at HEAD. The `ClayClosureBundleUniversal → PrincipiaFractalisMillenniumPositionAtHEAD`
master implication is a genuinely single-outcome map.

## Reduction chain state at HEAD (after r303)

| Stage | Statement | Discharge |
|---|---|---|
| r299a | sixteen-variant surface → 1 aggregate | 4 leaf projections + primary headline |
| r299b | supreme capstone extended v2 with C'-layer aggregate route | six-layer total position |
| r300 | aggregate → Clay closure + Route B second front from ONE input | 3 Route-B bridges + full-service headline |
| r301 | ONE universal input → ALL SIX layers of supreme capstone extended v2 as direct facts | universal-input flat theorem |
| r302 | framework's TOTAL Millennium position at HEAD as ONE named output structure inhabited via TWO alternative routes | named output structure + 2 route inhabitants |
| **r303** | **position at HEAD is a Subsingleton; two route constructors converge to equal outputs on every universal input** | **Subsingleton instance + two-route-equal theorem; kernel-only** |

Book anchors: Ch 20 § 20.4, Ch 21 § 4.1-4.2 canonical pair + § 6-7
empirical, Ch 34A § 34A.5. Paper `principia_fractalis_alpha_skeleton_
2026-07-13.pdf` § 6 Corollary 6.3.
-/

import PF.PrincipiaFractalisMillenniumPositionAtHEAD_r302

namespace PrincipiaTractalis.PrincipiaFractalisMillenniumPositionUniqueness

open PrincipiaTractalis
open PrincipiaTractalis.PrincipiaFractalisMillenniumPositionAtHEAD
open PrincipiaTractalis.PrincipiaFractalisMillenniumSupremeCapstoneUniversal

/-! ## §1 Subsingleton instance for the named position structure. -/

/-- **`instance : Subsingleton PrincipiaFractalisMillenniumPositionAtHEAD`** —
the framework's TOTAL Millennium position at HEAD is a Subsingleton.

All 11 fields of `PrincipiaFractalisMillenniumPositionAtHEAD` are
`Prop`-typed. By Lean 4's definitional proof irrelevance, any two
inhabitants of a `Prop`-fielded structure with the same underlying
data agree component-wise, hence agree as structure instances. -/
instance : Subsingleton PrincipiaFractalisMillenniumPositionAtHEAD :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-! ## §2 The two route constructors converge to equal outputs. -/

/-- **★★★★★★★★★★★★★★★★★★★★★★★★★★★ (r303) POSITION AT HEAD ROUTE-INESSENTIAL EQUALITY ★★★★★★★★★★★★★★★★★★★★★★★★★★★** —
r302's two route constructors of the framework's Millennium position
at HEAD converge to equal outputs on every universal input.

Given the Subsingleton instance (r303 §1), any two inhabitants of
`PrincipiaFractalisMillenniumPositionAtHEAD` are equal. In particular,
`pf_millennium_position_at_HEAD_via_aggregate_from_universal h` and
`pf_millennium_position_at_HEAD_via_bulletproof_from_universal h`
agree for every universal input `h`.

Framework consequence: for a referee consuming the framework's
referee-facing surface at HEAD, the choice between the aggregate
C'-route and the bulletproof C-route is INESSENTIAL. Both routes
produce equal inhabitants of the same named position. -/
theorem position_via_aggregate_eq_via_bulletproof
    (h : ClayClosureBundleUniversal) :
    pf_millennium_position_at_HEAD_via_aggregate_from_universal h
      = pf_millennium_position_at_HEAD_via_bulletproof_from_universal h :=
  Subsingleton.elim _ _

/-! ## §3 Axiom checks. -/

#print axioms
  PrincipiaTractalis.PrincipiaFractalisMillenniumPositionUniqueness.position_via_aggregate_eq_via_bulletproof

end PrincipiaTractalis.PrincipiaFractalisMillenniumPositionUniqueness
