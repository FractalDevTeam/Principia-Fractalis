/-
# r341 — The BSD anchor, re-rooted in the H₃ exponent datum

★ 2026-10-24 — the missing bridge: BSD's forcing chain was still rooted in a
circular predicate after r340 supplied the non-circular one ★

## The gap this closes

`codex/ALPHA_CHAIN_PER_AXIS_BAR_2026-10-24.md` measured every axis against the
October 1 bar and found exactly one broken link.

`r340` (`PF/NSAlphaFromH3ExponentSum_r340.lean`) built the non-circular NS
realisation predicate

    RealisesNS_forced (a) := 0 < a ∧ 2 * a = 3 * π

and proved `NS_forced : RealisesNS_forced a → a = 3π/2`, grounding the NS anchor
in the H₃ exponent sum `Σ{1,5,9} = 15` rather than in the definition of `α_NS`.

But the BSD axis is forced *through* NS, by

    chain_NS_implies_BSD : RealisesNS aNS → RealisesBSD (aNS / 2)

in `PF/CrossMillenniumImplicationChains.lean`, and that theorem takes the OLD
predicate `RealisesNS (a) := 0 < a ∧ a = α_NS`, which is circular against
`noncomputable def α_NS : ℝ := 3 * Real.pi / 2`. So when r340 landed, nothing
re-pointed the BSD chain at the new root: BSD remained rooted in `a = α_NS`, and
the H₃ work did not reach it.

Of the seven axes, BSD was the only one in that position. P, Hodge, Poincaré and
NS each have a non-circular equation with a proved identification; YM is forced
from P by `chain_P_implies_YM`, and RH from the Poincaré datum by
`alpha_RH_from_poincare_datum`. BSD was the one gap, and it was a missing lemma
rather than missing mathematics.

## What this file does

One bridge lemma and its two consequences. Nothing in `r340` or in
`CrossMillenniumImplicationChains` is modified — no existing statement or proof
is touched, and this file only adds.

## What is and is not claimed

**Claimed.** After this file, `RealisesBSD` is reachable from
`RealisesNS_forced`, so the BSD axis is forced by an equation that does not
mention `α_NS` or `α_BSD`, and the chain from the H₃ exponent datum now covers
BSD as it already covered NS.

**Not claimed.**

1. That `λ_NS = 1/Σ(H₃ exponents)` is derived from the substrate operator. It is
   supplied as a hypothesis — `r340`'s Not-claimed 1, unchanged by this file.
   `PF/H3CoxeterOrigin.lean` states plainly that it does not prove the
   framework's `H_α` operator inherits the H₃ Coxeter structure, and that single
   proposition remains the common open root of both H₃ axes.
2. That `α_BSD = 3π/4` is thereby derived from first principles. The step
   `α_BSD = α_NS / 2` is itself one of the catalogued invariants, read off the
   table per the 2026-10-01 accounting. What improves here is the *rooting* of
   the chain, not the origin of its equations.
3. Anything about the Birch–Swinnerton-Dyer conjecture itself. No property of it
   is consumed, exactly as `r340` records for Navier–Stokes and the O-CIRC audit
   records for Perelman.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-24.
-/

import Mathlib.Tactic
import PF.NSAlphaFromH3ExponentSum_r340
import PF.CrossMillenniumImplicationChains

namespace PrincipiaTractalis
namespace BSDAnchorFromH3ExponentDatum

open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumImplicationChains
open PrincipiaTractalis.NSAlphaFromH3ExponentSum

/-! ## §1 — The bridge -/

/-- **The non-circular NS predicate implies the old one.**

`RealisesNS_forced a` gives `2a = 3π`; since `α_NS` is *defined* as `3π/2`, that
is exactly `a = α_NS`. Positivity carries across unchanged.

This is the lemma whose absence left BSD rooted in a circular predicate. It is
one `linarith` — the mathematics was already there in `r340`. -/
theorem realisesNS_of_forced {a : ℝ} (h : RealisesNS_forced a) :
    RealisesNS a := by
  obtain ⟨hpos, heq⟩ := h
  refine ⟨hpos, ?_⟩
  unfold α_NS
  linarith

/-! ## §2 — BSD, rooted in the H₃ exponent datum -/

/-- **★★ The BSD anchor from the H₃ exponent datum.**

Composing the bridge with `chain_NS_implies_BSD`: any `a` satisfying the
non-circular equation `2a = 3π` yields a BSD-realisation at `a/2`. The
hypothesis mentions neither `α_NS` nor `α_BSD`. -/
theorem BSD_from_H3_exponent_datum {a : ℝ} (h : RealisesNS_forced a) :
    RealisesBSD (a / 2) :=
  chain_NS_implies_BSD (realisesNS_of_forced h)

/-- **Non-vacuity.** The BSD chain's root is satisfiable, so §2 is not
vacuously true. Discharged from `r340`'s own non-vacuity witness. -/
theorem realisesBSD_nonvacuous_from_H3 : ∃ b : ℝ, RealisesBSD b := by
  obtain ⟨a, ha⟩ := RealisesNS_forced_nonvacuous
  exact ⟨a / 2, BSD_from_H3_exponent_datum ha⟩

/-- **The value, pinned.** The BSD realiser obtained from the H₃ datum is
`3π/4 = α_BSD`. Stated so the chain's endpoint is explicit rather than left as
`a / 2`. -/
theorem BSD_value_from_H3_exponent_datum {a : ℝ} (h : RealisesNS_forced a) :
    a / 2 = α_BSD := by
  have ha : a = 3 * Real.pi / 2 := NS_forced h
  rw [ha]
  unfold α_BSD
  ring

/-- **Negative control.** Without positivity the NS equation still forces the
value, so positivity is *not* load-bearing here — unlike the Poincaré axis,
where `(-1)² = 1` makes it essential (`r338.positivity_is_load_bearing`). The
NS equation `2a = 3π` is linear and already has a unique solution. Recorded so
the asymmetry between the two anchors is visible rather than assumed. -/
theorem positivity_not_needed_for_NS_value {a : ℝ} (heq : 2 * a = 3 * Real.pi) :
    a = 3 * Real.pi / 2 := by linarith

end BSDAnchorFromH3ExponentDatum
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.BSDAnchorFromH3ExponentDatum.realisesNS_of_forced
#print axioms PrincipiaTractalis.BSDAnchorFromH3ExponentDatum.BSD_from_H3_exponent_datum
#print axioms PrincipiaTractalis.BSDAnchorFromH3ExponentDatum.realisesBSD_nonvacuous_from_H3
#print axioms PrincipiaTractalis.BSDAnchorFromH3ExponentDatum.BSD_value_from_H3_exponent_datum
#print axioms PrincipiaTractalis.BSDAnchorFromH3ExponentDatum.positivity_not_needed_for_NS_value
