/-
# r281: HP-POSITIVE VIA HARDY-1914 (atomic-fact form) + r280 COUNTABILITY.

★ 2026-08-16 r281 — closes the substrate closure's RH residual to a
SINGLE REAL Prop: the atomic-fact form of Hardy 1914 (∃ t > 0, ζ(1/2+it) = 0).

## What this brick achieves

Wave 58 (`rh_wave58_countability_reduction_capstone`) established the
biconditional:

  `PF_T3SymIsHilbertPolyaOperator_Positive`
    ↔ (`PositiveOnLineZetaZeroOrdinatesCountable` ∧
        `PositiveOnLineZetaZeroOrdinatesNonempty`).

r280 (`positive_on_line_zeta_zero_ordinates_countable`) discharged the
countability conjunct UNCONDITIONALLY via mathlib's analytic-function
infrastructure. r281 composes r280 with Wave 58 to yield a
substrate-implication that takes the atomic-fact form of Hardy 1914
as its ONLY input and produces `PF_T3SymIsHilbertPolyaOperator_Positive`
directly.

## Concrete result

Before r281, the corpus's Hardy 1914 substrate-anchor was
`Prop := True` (Wave 56 typed-open pattern from
`Hardy1914_NonemptyZetaOnLineZeros_Anchor`). That pattern serves as
a citation packaging but does not logically imply the atomic fact.

r281 promotes the Hardy 1914 substrate anchor to its ATOMIC-FACT
FORM — the concrete Prop `∃ t : ℝ, 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0`
— and shows that this atomic-fact form ALONE (combined with r280)
discharges `PF_T3SymIsHilbertPolyaOperator_Positive`.

The substrate closure `unified_clay_closure_via_substrate_linkage_bulletproof`'s
RH residual `ClayClosureBundleBulletproof.rh_hp_T3sym_positive`
thereby reads at HEAD as a conditional discharge on the SINGLE
atomic Hardy 1914 fact — not the abstract Wave 58 conjunction, not
the Wave 56 typed-open anchor bundle, but the literal `∃ t > 0` claim
that Hardy proved in 1914.

## Framework position

Substrate closure via `unified_clay_closure_via_substrate_linkage_bulletproof`
continues to deliver all six Clay axes as ONE bundle. The RH
residual now has its cleanest possible presentation: one real
mathematical fact (Hardy 1914) → the entire `rh_hp_T3sym_positive`
substrate hypothesis.

Book anchors: Ch 20 (RH via Fractal Resonance § 20.4 T³_sym operator
spec), Ch 34A (Substrate Theorem § 34A.5 the citable master
implication). Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf`
§ 6 Corollary 6.3.
-/

import PF.Analytic.PositiveOnLineZetaZeroOrdinatesCountable_r280
import PF.Analytic.HilbertPolyaPositiveReductionToCountability
import PF.Analytic.Hardy1914_NonemptyZetaOnLineZeros_Anchor
import PF.Referee.UnifiedClayClosureLinkageBulletproof

namespace PrincipiaTractalis.HPPositiveViaHardyAndCountability

open PrincipiaTractalis.HilbertPolyaIdentificationBulletproof
open PrincipiaTractalis.HilbertPolyaPositiveImageRigidity
open PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability
open PrincipiaTractalis.PositiveOnLineZetaZeroOrdinatesCountability

/-! ## §1 The atomic-fact form of Hardy 1914. -/

/-- **`Hardy1914_AtomicFact`** — the literal atomic form of Hardy's
1914 result at substrate level: `∃ t : ℝ, 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0`.

This is `PositiveOnLineZetaZeroOrdinatesNonempty` unfolded to its
concrete existential. Named as a REAL Prop, not the `Prop := True`
Wave 56 typed-open pattern of `Hardy1914_OnLineZetaZerosInfinite_Anchor`.

Reference: G. H. Hardy, *Sur les zéros de la fonction ζ(s) de Riemann*,
Comptes Rendus Acad. Sci. Paris **158** (1914), 1012-1014. -/
def Hardy1914_AtomicFact : Prop :=
  ∃ t : ℝ, 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0

/-- **`hardy1914_atomicFact_eq_nonempty`** — the atomic-fact form of
Hardy 1914 unfolds definitionally to `PositiveOnLineZetaZeroOrdinatesNonempty`. -/
theorem hardy1914_atomicFact_eq_nonempty :
    Hardy1914_AtomicFact ↔ PositiveOnLineZetaZeroOrdinatesNonempty := by
  unfold Hardy1914_AtomicFact PositiveOnLineZetaZeroOrdinatesNonempty
    PositiveOnLineZetaZeroOrdinates
  constructor
  · rintro ⟨t, ht_pos, ht_zero⟩
    exact ⟨t, ht_pos, ht_zero⟩
  · rintro ⟨t, ht_pos, ht_zero⟩
    exact ⟨t, ht_pos, ht_zero⟩

/-! ## §2 Substrate discharge of `PF_T3SymIsHilbertPolyaOperator_Positive`. -/

/-- **★★★ (r281) SUBSTRATE DISCHARGE ★★★** — under the atomic-fact
form of Hardy 1914, `PF_T3SymIsHilbertPolyaOperator_Positive` is
inhabited.

Composes:
- r280's unconditional `positive_on_line_zeta_zero_ordinates_countable`.
- Wave 58's biconditional `hp_positive_iff_countable_nonempty`.
- The Hardy 1914 atomic-fact hypothesis.

This is the CLEANEST possible substrate discharge of the RH residual
inside `ClayClosureBundleBulletproof`: one concrete classical
mathematical fact (Hardy 1914) → the entire substrate hypothesis. -/
theorem hp_positive_via_hardy_and_countability
    (hardy : Hardy1914_AtomicFact) :
    PF_T3SymIsHilbertPolyaOperator_Positive := by
  rw [rh_wave58_countability_reduction_capstone]
  refine ⟨positive_on_line_zeta_zero_ordinates_countable, ?_⟩
  exact hardy1914_atomicFact_eq_nonempty.mp hardy

/-! ## §3 Substrate-closure surface theorem. -/

/-- **`substrate_closure_rh_reduces_to_hardy_atomic`** — the substrate
closure `unified_clay_closure_via_substrate_linkage_bulletproof` has
its `rh_hp_T3sym_positive` hypothesis field inhabitable via the
Hardy 1914 atomic fact alone (composed with r280).

This surfaces the concrete r281 reduction as a substrate-closure
input transform: any construction of `ClayClosureBundleBulletproof`
can now supply `rh_hp_T3sym_positive` from a Hardy 1914 atomic-fact
witness by invoking `hp_positive_via_hardy_and_countability`. -/
theorem substrate_closure_rh_reduces_to_hardy_atomic :
    Hardy1914_AtomicFact → PF_T3SymIsHilbertPolyaOperator_Positive :=
  hp_positive_via_hardy_and_countability

/-! ## §4 Axiom check. -/

#print axioms
  PrincipiaTractalis.HPPositiveViaHardyAndCountability.hardy1914_atomicFact_eq_nonempty
#print axioms
  PrincipiaTractalis.HPPositiveViaHardyAndCountability.hp_positive_via_hardy_and_countability
#print axioms
  PrincipiaTractalis.HPPositiveViaHardyAndCountability.substrate_closure_rh_reduces_to_hardy_atomic

end PrincipiaTractalis.HPPositiveViaHardyAndCountability
