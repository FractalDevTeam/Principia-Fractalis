/-
# PF.AlgebraicGeometry.MordellWeilRankAgreement17_NamedAnchors

★★★★★ 2026-06-18 — BSD PHASE 1 / TYPED-RESIDUAL CLEANUP ★★★★★

Audit-trail surface for the 17 per-curve `MordellWeilRankIs E_*** n`
typed Props that factor `mordellWeilRankAgreementOn17Curves`.

In `MordellWeilRankAgreement17.lean`, the 17 published-theorem
residuals appear ONLY as inline conjuncts of
`AllSeventeenMordellWeilRanksKnown`. This file lifts each one into
an explicit NAMED declaration with its published-theorem anchor in
the docstring. Purpose: referee-readability of the typed BSD bridge.

HONEST SCOPE
============

This file does NOT discharge any `MordellWeilRankIs E n`. Each Prop
remains a TYPED HYPOTHESIS naming the published Mordell-Weil rank
computation for that curve. Discharging them literally would require
mathlib's missing Mordell-Weil rank infrastructure (`Module.rank ℤ
E.toAffine.Point` over ℚ — mathlib gap G3) PLUS the corresponding
published theorem formalised.

The audit-trail improvement is: each `MordellWeilRankIs E_*** n_***`
hypothesis is now an explicit `abbrev` (so it definitionally
matches the inline form in `AllSeventeenMordellWeilRanksKnown`)
with the named published-theorem anchor in its docstring.

Anchors per rank class
======================

  * Rank-0 CM curves (6 curves):
      - Coates-Wiles 1977 — class-number-1 CM
      - Rubin 1991 — Iwasawa main conjecture for CM
      - Wiles 1995 — modularity
  * Rank-1 Heegner cohort (10 curves):
      - Gross-Zagier 1986 — Heegner-point height formula
      - Kolyvagin 1990 — Euler systems / finiteness of Sha
  * Rank-2 (1 curve, E_389a1):
      - Bhargava-Skinner-Zhang 2014 — average rank
      - Skinner-Urban 2014 — Iwasawa main conjecture (GL₂)
  * Rank-3 (1 curve, E_rank_three = E_5077a1):
      - Classical LMFDB rank computation
      - Higher-rank Kolyvagin-encoded content

Build
=====

ZERO project axioms. Kernel-only `[propext, Classical.choice,
Quot.sound]`. Every declaration in this file builds at HEAD.

Stage 2026-06-18.
-/

import PF.AlgebraicGeometry.MordellWeilRankAgreement17
import PF.AlgebraicGeometry.MordellWeilRankAgreement17_V4Readings

namespace PF.AlgebraicGeometry.MordellWeilRankAgreement17

open PF.AlgebraicGeometry.MordellWeilGroup
open PrincipiaTractalis
open PrincipiaTractalis.BSDGaloisPairConcordance
open PrincipiaTractalis.BSDRankThreeCurveFramework
open PrincipiaTractalis.BSD_MultiCMRankZeroBatch
open PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE53a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE61a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE79a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE83a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE89a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE101a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE102a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE106a1
open PrincipiaTractalis.BSD_Rank2AttemptE389a1
open PF.Referee.BSDCapstoneTypedBridgeV4

/-! ## §1 — Rank-0 CM curves (6 curves)

For each rank-0 curve the named typed Prop asserts the published
Mordell-Weil rank is 0. Anchor: Coates-Wiles 1977 (class-number-1 CM)
+ Rubin 1991 (Iwasawa main for CM) + Wiles 1995 (modularity for the
non-CM case via the BSD G3 sandwich). -/

/-- **Coates-Wiles 1977 / Rubin 1991 anchor** — the named published
Mordell-Weil rank Prop for `E_rank_zero` (LMFDB 27a1, CM by ℤ[ω],
class-number-1). -/
abbrev MordellWeilRankIs_E_rank_zero : Prop :=
  MordellWeilRankIs E_rank_zero 0

/-- **Coates-Wiles 1977 generalised CM anchor** — the named published
Mordell-Weil rank Prop for `E_36a1` (CM tag, L(E,1) ≠ 0). -/
abbrev MordellWeilRankIs_E_36a1 : Prop :=
  MordellWeilRankIs E_36a1 0

/-- **Coates-Wiles 1977 generalised CM anchor** — the named published
Mordell-Weil rank Prop for `E_49a1` (CM tag, L(E,1) ≠ 0). -/
abbrev MordellWeilRankIs_E_49a1 : Prop :=
  MordellWeilRankIs E_49a1 0

/-- **Rubin 1991 / generalised CM anchor** — the named published
Mordell-Weil rank Prop for `E_121b1` (CM tag, L(E,1) ≠ 0). -/
abbrev MordellWeilRankIs_E_121b1 : Prop :=
  MordellWeilRankIs E_121b1 0

/-- **Rubin 1991 / generalised CM anchor** — the named published
Mordell-Weil rank Prop for `E_144a1` (CM tag, L(E,1) ≠ 0). -/
abbrev MordellWeilRankIs_E_144a1 : Prop :=
  MordellWeilRankIs E_144a1 0

/-! ## §2 — Rank-1 generic anchor + Heegner cohort (10 curves)

For each rank-1 curve the named typed Prop asserts the published
Mordell-Weil rank is 1. Anchor: Gross-Zagier 1986 (Heegner-point
height formula) + Kolyvagin 1990 (Euler systems / finiteness of Sha
in the analytic-rank-1 case). -/

/-- **Gross-Zagier 1986 + Kolyvagin 1990 anchor** — the named
published Mordell-Weil rank Prop for the canonical `E_rank_one`. -/
abbrev MordellWeilRankIs_E_rank_one : Prop :=
  MordellWeilRankIs E_rank_one 1

/-- **Gross-Zagier 1986 + Kolyvagin 1990 anchor** — the named
published Mordell-Weil rank Prop for `E_43a1` (LMFDB Cremona 43a1,
Heegner rank-1 curve). -/
abbrev MordellWeilRankIs_E_43a1 : Prop :=
  MordellWeilRankIs PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 1

/-- **Gross-Zagier 1986 + Kolyvagin 1990 anchor** — the named
published Mordell-Weil rank Prop for `E_53a1` (LMFDB Cremona 53a1,
Heegner rank-1 curve). -/
abbrev MordellWeilRankIs_E_53a1 : Prop :=
  MordellWeilRankIs PrincipiaTractalis.BSD_HeegnerRank1ProofE53a1.E_53a1 1

/-- **Gross-Zagier 1986 + Kolyvagin 1990 anchor** — the named
published Mordell-Weil rank Prop for `E_61a1` (LMFDB Cremona 61a1,
Heegner rank-1 curve). -/
abbrev MordellWeilRankIs_E_61a1 : Prop :=
  MordellWeilRankIs PrincipiaTractalis.BSD_HeegnerRank1ProofE61a1.E_61a1 1

/-- **Gross-Zagier 1986 + Kolyvagin 1990 anchor** — the named
published Mordell-Weil rank Prop for `E_79a1` (LMFDB Cremona 79a1,
Heegner rank-1 curve). -/
abbrev MordellWeilRankIs_E_79a1 : Prop :=
  MordellWeilRankIs PrincipiaTractalis.BSD_HeegnerRank1ProofE79a1.E_79a1 1

/-- **Gross-Zagier 1986 + Kolyvagin 1990 anchor** — the named
published Mordell-Weil rank Prop for `E_83a1` (LMFDB Cremona 83a1,
Heegner rank-1 curve). -/
abbrev MordellWeilRankIs_E_83a1 : Prop :=
  MordellWeilRankIs PrincipiaTractalis.BSD_HeegnerRank1ProofE83a1.E_83a1 1

/-- **Gross-Zagier 1986 + Kolyvagin 1990 anchor** — the named
published Mordell-Weil rank Prop for `E_89a1` (LMFDB Cremona 89a1,
Heegner rank-1 curve). -/
abbrev MordellWeilRankIs_E_89a1 : Prop :=
  MordellWeilRankIs PrincipiaTractalis.BSD_HeegnerRank1ProofE89a1.E_89a1 1

/-- **Gross-Zagier 1986 + Kolyvagin 1990 anchor** — the named
published Mordell-Weil rank Prop for `E_101a1` (LMFDB Cremona 101a1,
Heegner rank-1 curve). -/
abbrev MordellWeilRankIs_E_101a1 : Prop :=
  MordellWeilRankIs PrincipiaTractalis.BSD_HeegnerRank1ProofE101a1.E_101a1 1

/-- **Gross-Zagier 1986 + Kolyvagin 1990 anchor** — the named
published Mordell-Weil rank Prop for `E_102a1` (LMFDB Cremona 102a1,
Heegner rank-1 curve). -/
abbrev MordellWeilRankIs_E_102a1 : Prop :=
  MordellWeilRankIs PrincipiaTractalis.BSD_HeegnerRank1ProofE102a1.E_102a1 1

/-- **Gross-Zagier 1986 + Kolyvagin 1990 anchor** — the named
published Mordell-Weil rank Prop for `E_106a1` (LMFDB Cremona 106a1,
Heegner rank-1 curve). -/
abbrev MordellWeilRankIs_E_106a1 : Prop :=
  MordellWeilRankIs PrincipiaTractalis.BSD_HeegnerRank1ProofE106a1.E_106a1 1

/-! ## §3 — Rank-2 anchor (E_389a1)

Anchor: Bhargava-Shankar-Zhang 2014 + Skinner-Urban 2014 (Iwasawa
main conjecture for GL₂). E_389a1 is the canonical lowest-conductor
rank-2 elliptic curve over ℚ. -/

/-- **Bhargava-Shankar-Zhang 2014 + Skinner-Urban 2014 anchor** —
the named published Mordell-Weil rank Prop for `E_389a1` (LMFDB
Cremona 389a1, the canonical conductor-389 rank-2 elliptic curve
over ℚ). -/
abbrev MordellWeilRankIs_E_389a1 : Prop :=
  MordellWeilRankIs PrincipiaTractalis.BSD_Rank2AttemptE389a1.E_389a1 2

/-! ## §4 — Rank-3 anchor (E_rank_three = E_5077a1)

Anchor: classical LMFDB rank computation (descent + 2-descent +
mwrank verification) + higher-rank Kolyvagin-encoded content. -/

/-- **Classical LMFDB rank computation + higher-rank Kolyvagin
anchor** — the named published Mordell-Weil rank Prop for
`E_rank_three` (LMFDB Cremona 5077a1, the canonical lowest-conductor
rank-3 elliptic curve over ℚ). -/
abbrev MordellWeilRankIs_E_rank_three : Prop :=
  MordellWeilRankIs E_rank_three 3

/-! ## §5 — Named-anchor 17-tuple bundle

The same `AllSeventeenMordellWeilRanksKnown` bundle from
`MordellWeilRankAgreement17.lean` §4, but expressed in terms of the
17 named-anchor `MordellWeilRankIs_E_***` abbreviations above. This
form is the AUDIT-TRAIL surface for the BSD typed bridge: each
conjunct cites its published-theorem anchor in its name. -/

/-- **★ NAMED-ANCHOR 17-TUPLE BUNDLE ★** — definitionally equal to
`AllSeventeenMordellWeilRanksKnown` (since each conjunct unfolds to
the same `MordellWeilRankIs E n` Prop), but each named-anchor
abbreviation makes the published-theorem provenance audit-readable.

Composition:
  * 5 rank-0 CM (Coates-Wiles / Rubin / Wiles)
  * 10 rank-1 Heegner (Gross-Zagier / Kolyvagin)
  * 1 rank-2 (BSZ 2014 / Skinner-Urban)
  * 1 rank-3 (classical LMFDB / higher-rank Kolyvagin) -/
abbrev AllSeventeenMordellWeilRanksKnown_namedAnchors : Prop :=
  MordellWeilRankIs_E_rank_zero ∧
  MordellWeilRankIs_E_36a1 ∧
  MordellWeilRankIs_E_49a1 ∧
  MordellWeilRankIs_E_121b1 ∧
  MordellWeilRankIs_E_144a1 ∧
  MordellWeilRankIs_E_rank_one ∧
  MordellWeilRankIs_E_43a1 ∧
  MordellWeilRankIs_E_53a1 ∧
  MordellWeilRankIs_E_61a1 ∧
  MordellWeilRankIs_E_79a1 ∧
  MordellWeilRankIs_E_83a1 ∧
  MordellWeilRankIs_E_89a1 ∧
  MordellWeilRankIs_E_101a1 ∧
  MordellWeilRankIs_E_102a1 ∧
  MordellWeilRankIs_E_106a1 ∧
  MordellWeilRankIs_E_389a1 ∧
  MordellWeilRankIs_E_rank_three

/-- **Audit-trail equivalence** — the named-anchor bundle is the
same Prop as the inline bundle in `MordellWeilRankAgreement17.lean`. -/
theorem allSeventeen_namedAnchors_iff :
    AllSeventeenMordellWeilRanksKnown_namedAnchors ↔
    AllSeventeenMordellWeilRanksKnown :=
  Iff.rfl

/-! ## §6 — Audit-trail capstone

Using the existing axiom-free V4-readings bundle
`allSeventeenV4ReadingsKnown_axiom_free` from
`MordellWeilRankAgreement17_V4Readings.lean`, the 17-curve agreement
holds under just the named-anchor bundle (the V4-readings half is
discharged unconditionally). -/

/-- **★★★ AUDIT-TRAIL CAPSTONE ★★★** — `mordellWeilRankAgreementOn17Curves`
holds under just the named-anchor 17-tuple, with the V4-readings half
discharged axiom-free internally. This is the cleanest referee-
readable form of the typed BSD bridge: ONE named published-theorem
hypothesis bundle, all V4 case-split mechanics already discharged. -/
theorem mordellWeilRankAgreementOn17Curves_under_namedAnchors
    (hMW : AllSeventeenMordellWeilRanksKnown_namedAnchors) :
    mordellWeilRankAgreementOn17Curves :=
  mordellWeilRankAgreementOn17Curves_under_hyps
    (allSeventeen_namedAnchors_iff.mp hMW)
    allSeventeenV4ReadingsKnown_axiom_free

end PF.AlgebraicGeometry.MordellWeilRankAgreement17

-- Axiom checks across the named anchors
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.allSeventeen_namedAnchors_iff
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.mordellWeilRankAgreementOn17Curves_under_namedAnchors
